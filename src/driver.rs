// SPDX-License-Identifier: Apache-2.0
//! Whole-program analysis (routines, linkages) and module emission.
use crate::arch::target as arch;
use crate::cfg::*;
use crate::ir::*;
use crate::lift::*;
use crate::program::Program;
use crate::structure::*;
use crate::tidy;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

// ------------------------------------------------------------------ driver
/// An analysed program: discovered routines and their inferred linkages.
pub struct Task {
    pub mem: Program,
    pub routines: HashMap<u16, Routine>,
    /// routines in discovery order
    pub rorder: Vec<u16>,
    pub info: HashMap<u16, Info>,
    /// routines treated as hand-written MACRO (no BLISS linkage)
    pub macros: HashSet<u16>,
}

/// called at each call site during the register liveness walk
type CallHook<'a> = &'a mut dyn FnMut(u16, &BTreeSet<i32>);

/// Discover routines from the program's entry points and the calls they make, then infer every
/// routine's linkage: stack parameter count, register parameters, GLOBAL registers, value/NOVALUE.
pub fn analyze(mem: Program) -> Result<Task, String> {
    let mut entries: HashSet<u16> = mem.entries.iter().cloned().collect();
    let mut seen: HashSet<u16> = HashSet::new();
    let mut work: Vec<u16> = entries.iter().cloned().collect();
    work.sort();
    let mut routines: HashMap<u16, Routine> = HashMap::new();
    let mut rorder: Vec<u16> = vec![];
    while let Some(e) = work.pop() {
        if !seen.insert(e) {
            continue;
        }
        let r = match Routine::new(&mem, e, &entries) {
            Ok(r) => r,
            Err(_) => continue,
        };
        for pc in &r.order {
            let i = &r.insns[pc];
            if let Some(t) = i.call_target() {
                // a call from outside the overlay windows reaches whichever overlay is mapped:
                // only targets labelled in this one are ours
                if mem.is_banked(t) && !mem.is_banked(*pc) && !mem.names.contains_key(&t) {
                    continue;
                }
                entries.insert(t);
                if !seen.contains(&t) {
                    work.push(t);
                }
            }
        }
        routines.insert(e, r);
        rorder.push(e);
    }
    let mut info: HashMap<u16, Info> = rorder.iter().map(|&e| (e, Info { nparams: 0, returns: false, regparams: vec![], globals: vec![], gdecl: vec![] })).collect();
    // callees we cannot analyse (e.g. routines in banked windows): argument count from the call sites,
    // the most common number of words pushed right before the JSR (a write to (SP) first counts as one)
    // overlay thunks (JSR R5,dispatcher / inline arguments): the code behind them is in another
    // address space, so like an unanalysable callee their arity comes from the call sites (their
    // own body reads no stack arguments, and the calls would lose theirs)
    let is_thunk = |e: u16| -> bool {
        routines.get(&e).and_then(|r| r.insns.get(&e)).map(|i| i.is_thunk_call(&mem)).unwrap_or(false)
    };
    let mut ext_sites: HashMap<u16, Vec<i32>> = HashMap::new();
    for &e in &rorder {
        let r = &routines[&e];
        for blk in r.blocks.values() {
            for (k, i) in blk.ins.iter().enumerate() {
                let t = match i.call_target() { Some(t) => t, None => continue };
                // every call site counts: an analysable callee ignores the count, a hand-written (MACRO)
                // one, like an unanalysable callee, takes its arity from it
                let mut n = arch::pushed_args(&blk.ins, k);
                // a call that starts its block may have been shared between branches (cross-jumped):
                // its arguments are then pushed at the end of every predecessor block
                if k == 0 && n == 0 {
                    let ps: Vec<i32> = r.blocks.values().filter(|b| b.succ.iter().any(|(x, _)| *x == blk.start))
                        .map(|b| arch::trailing_pushes(&b.ins)).collect();
                    if ps.len() >= 2 && ps.iter().all(|&c| c > 0 && c == ps[0]) { n = ps[0]; }
                }
                ext_sites.entry(t).or_default().push(n);
            }
        }
    }
    let mut site_args: HashMap<u16, i32> = HashMap::new();
    for (t, v) in &ext_sites {
        let mut cnt: BTreeMap<i32, usize> = BTreeMap::new();
        for x in v { *cnt.entry(*x).or_default() += 1; }
        let n = cnt.iter().max_by_key(|(k, c)| (**c, **k)).map(|(k, _)| *k).unwrap_or(0);
        site_args.insert(*t, n);
        if !routines.contains_key(t) {
            info.insert(*t, Info { nparams: n, returns: false, regparams: vec![], globals: vec![], gdecl: vec![] });
        }
    }
    let ext_sites: HashMap<u16, Vec<i32>> = ext_sites.into_iter().filter(|(t, _)| !routines.contains_key(t)).collect();
    let by_name: HashMap<String, u16> = rorder.iter().map(|&e| (routines[&e].name.clone(), e)).collect();
    // register parameters: start from every register a routine reads before writing (optimistic),
    // then drop each one some caller may reach the call without setting (greatest fixpoint).
    let mut cand0: HashMap<u16, Vec<i32>> = HashMap::new();
    for &e in &rorder {
        let mut l = Lifter::new(false);
        match l.lift(&routines[&e], &mem, &info) {
            Ok(()) => {
                cand0.insert(e, l.live_in_regs(&routines[&e]));
                let x = info.get_mut(&e).unwrap();
                x.nparams = x.nparams.max(l.maxparam);
            }
            Err(ex) => eprintln!("! lift failed {}: {}", o6(e), ex),
        }
    }
    // hand-written MACRO (kernel trap stubs, interrupt code): no stack parameters, registers from the callers
    let is_macro = |e: u16| -> bool {
        mem.macros.contains(&e)
            || routines[&e].insns.values().any(|i| i.is_macro_marker())
            || is_thunk(e)
    };
    let macro_set: HashSet<u16> = rorder.iter().cloned().filter(|&e| is_macro(e)).collect();
    for &e in &macro_set {
        let x = info.get_mut(&e).unwrap();
        x.nparams = site_args.get(&e).cloned().unwrap_or(0);
        x.regparams = vec![];
        cand0.insert(e, vec![]);
    }
    let called: HashSet<u16> = {
        let mut c = HashSet::new();
        for &e in &rorder {
            for i in routines[&e].insns.values() {
                if let Some(t) = i.call_target() { c.insert(t); }
            }
        }
        c
    };
    for &e in &rorder {
        if called.contains(&e) {
            info.get_mut(&e).unwrap().regparams = cand0.get(&e).cloned().unwrap_or_default();
        }
    }
    // grow: registers passed through to a callee's register parameters are live-in too
    for _ in 0..20 {
        let mut grew = false;
        for &e in &rorder {
            if !called.contains(&e) || macro_set.contains(&e) { continue; }
            let mut l = Lifter::new(false);
            if l.lift(&routines[&e], &mem, &info).is_err() { continue; }
            let c = l.live_in_regs(&routines[&e]);
            let x = info.get_mut(&e).unwrap();
            for k in c {
                if !x.regparams.contains(&k) { x.regparams.push(k); x.regparams.sort(); grew = true; }
            }
        }
        if !grew { break; }
    }
    for &e in &macro_set {
        if called.contains(&e) {
            info.get_mut(&e).unwrap().regparams = (0..=5).collect();
        }
    }
    for it in 0..20 {
        let mut changed = false;
        let mut lifted: HashMap<u16, Lifter> = HashMap::new();
        for &e in &rorder {
            let mut l = Lifter::new(false);
            if l.lift(&routines[&e], &mem, &info).is_ok() {
                lifted.insert(e, l);
            }
        }
        // forward dataflow per caller: registers that may still hold the entry (garbage) value
        let mut evid: HashMap<u16, BTreeSet<i32>> = HashMap::new();
        for (&caller, l) in &lifted {
            let r = &routines[&caller];
            let all: BTreeSet<i32> = (0..=5).collect();
            let mut inn: HashMap<u16, BTreeSet<i32>> = HashMap::new();
            let mine: BTreeSet<i32> = info.get(&caller).map(|x| x.regparams.iter().cloned().collect()).unwrap_or_default();
            inn.insert(r.entry, all.difference(&mine).cloned().collect());
            let mut work: Vec<u16> = vec![r.entry];
            let transfer = |b: u16, mut u: BTreeSet<i32>, mut at_call: Option<CallHook<'_>>| -> BTreeSet<i32> {
                if let Some(ss) = l.stmts.get(&b) {
                    for st in ss {
                        if let Stmt::Set(_, E::Call(n, _)) | Stmt::Do(E::Call(n, _)) = st {
                            if let (Some(f), Some(&c)) = (at_call.as_mut(), by_name.get(n.as_ref())) {
                                f(c, &u);
                            }
                        }
                        if let Some(Loc::R(k)) = st_def(st) { u.remove(&k); }
                    }
                }
                u
            };
            while let Some(b) = work.pop() {
                let u = transfer(b, inn[&b].clone(), None);
                if let Some(blk) = r.blocks.get(&b) {
                    for (t, _) in &blk.succ {
                        let first = !inn.contains_key(t);
                        let e2 = inn.entry(*t).or_default();
                        let before = e2.len();
                        e2.extend(u.iter().cloned());
                        if (first || e2.len() != before) && !work.contains(t) {
                            work.push(*t);
                        }
                    }
                }
            }
            // for MACRO callees: only registers loaded in the same block since the previous call
            for (&_b, ss) in &l.stmts {
                for (k, st) in ss.iter().enumerate() {
                    if let Stmt::Set(_, E::Call(n, _)) | Stmt::Do(E::Call(n, _)) = st {
                        if let Some(&c) = by_name.get(n.as_ref()) {
                            if macro_set.contains(&c) {
                                let mut set: BTreeSet<i32> = BTreeSet::new();
                                for prev in ss[..k].iter().rev() {
                                    if matches!(prev, Stmt::Set(_, E::Call(..)) | Stmt::Do(E::Call(..))) { break; }
                                    if let Some(Loc::R(r)) = st_def(prev) { set.insert(r); }
                                }
                                let ent = evid.entry(c).or_insert_with(|| all.clone());
                                *ent = ent.intersection(&set).cloned().collect();
                            }
                        }
                    }
                }
            }
            for (&b, u) in inn.clone().iter() {
                let mut f = |c: u16, u: &BTreeSet<i32>| {
                    if macro_set.contains(&c) { return; }
                    let ok: BTreeSet<i32> = all.difference(u).cloned().collect();
                    let ent = evid.entry(c).or_insert_with(|| all.clone());
                    *ent = ent.intersection(&ok).cloned().collect();
                };
                transfer(b, u.clone(), Some(&mut f));
            }
        }
        for &e in &rorder {
            let l = match lifted.get(&e) { Some(l) => l, None => continue };
            let x = info.get_mut(&e).unwrap();
            // shrink only (greatest fixpoint): drop what some caller does not set
            let regs: Vec<i32> = match evid.get(&e) {
                Some(ev) => x.regparams.iter().cloned().filter(|k| ev.contains(k)).collect(),
                None => vec![],
            };
            if l.maxparam > x.nparams && !macro_set.contains(&e) {
                x.nparams = l.maxparam;
                changed = true;
            }
            if regs != x.regparams {
                if std::env::var("BLISSDC_TRACE_REGS").is_ok() {
                    eprintln!("it{} {} {:?} -> {:?}", it, o6(e), x.regparams, regs);
                }
                x.regparams = regs;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    // a register parameter the routine does not save is a linkage GLOBAL register (shared with the
    // caller, may be updated); routines that feed such callees without receiving it declare it
    let saved_of = |e: u16| -> BTreeSet<i32> {
        let r = &routines[&e];
        arch::saved_regs(&r.blocks[&r.entry].ins, &mem)
    };
    if std::env::var("BLISSDC_NOGLOBALS").is_err() {
        // registers every caller loads in the same block since its previous call: real parameters
        let mut local_ev: HashMap<u16, BTreeSet<i32>> = HashMap::new();
        for &caller in &rorder {
            let mut l = Lifter::new(false);
            if l.lift(&routines[&caller], &mem, &info).is_err() { continue; }
            let r = &routines[&caller];
            let mut preds: HashMap<u16, Vec<u16>> = HashMap::new();
            for (&b, blk) in &r.blocks {
                for (t, _) in &blk.succ { preds.entry(*t).or_default().push(b); }
            }
            let scan = |ss: &[Stmt], dead: &mut BTreeSet<i32>| -> BTreeSet<i32> {
                let mut set: BTreeSet<i32> = BTreeSet::new();
                for prev in ss.iter().rev() {
                    if let Stmt::Set(_, E::Call(n2, _)) | Stmt::Do(E::Call(n2, _)) = prev {
                        // an earlier call clobbers R0 and the callee's own register parameters
                        dead.insert(0);
                        if let Some(c2) = by_name.get(n2.as_ref()).and_then(|t| info.get(t)) {
                            dead.extend(c2.regparams.iter().cloned());
                        }
                        if !by_name.contains_key(n2.as_ref()) { dead.extend(0..=5); }
                    }
                    if let Some(Loc::R(r)) = st_def(prev) { if !dead.contains(&r) { set.insert(r); } }
                }
                set
            };
            for (&b, ss) in &l.stmts {
                for (k, st) in ss.iter().enumerate() {
                    if let Stmt::Set(_, E::Call(n, _)) | Stmt::Do(E::Call(n, _)) = st {
                        if let Some(&c) = by_name.get(n.as_ref()) {
                            let mut dead: BTreeSet<i32> = BTreeSet::new();
                            let mut set = scan(&ss[..k], &mut dead);
                            let mut inter: Option<BTreeSet<i32>> = None;
                            for p in preds.get(&b).cloned().unwrap_or_default() {
                                let mut d2 = dead.clone();
                                let ps = l.stmts.get(&p).map(|x| scan(x, &mut d2)).unwrap_or_default();
                                inter = Some(match inter { None => ps, Some(o) => o.intersection(&ps).cloned().collect() });
                            }
                            if let Some(i) = inter { set.extend(i); }
                            if std::env::var("BLISSDC_LEV").map(|x| x == o6(c)).unwrap_or(false) { eprintln!("lev {} at {}: {:?}", o6(c), o6(caller), set); }
                            let ent = local_ev.entry(c).or_insert_with(|| (0..=5).collect());
                            *ent = ent.intersection(&set).cloned().collect();
                        }
                    }
                }
            }
        }
        for &e in &rorder {
            if macro_set.contains(&e) { continue; }
            let sv = saved_of(e);
            let lev = local_ev.get(&e).cloned().unwrap_or_default();
            let x = info.get_mut(&e).unwrap();
            let (g, p): (Vec<i32>, Vec<i32>) = x.regparams.iter().partition(|&&k| k >= 1 && !sv.contains(&k) && !lev.contains(&k));
            x.globals = g;
            x.regparams = p;
        }
        // a caller that receives k as a REGISTER parameter passes it on as one: demote the callee's global
        for _ in 0..10 {
            let mut ch = false;
            for &e in &rorder {
                let mine = info[&e].regparams.clone();
                if mine.is_empty() { continue; }
                let ts: Vec<u16> = routines[&e].insns.values()
                    .filter_map(|i| i.call_target()).collect();
                for t in ts {
                    if let Some(c) = info.get_mut(&t) {
                        for k in &mine {
                            if c.globals.contains(k) {
                                c.globals.retain(|x| x != k);
                                c.regparams.push(*k);
                                c.regparams.sort();
                                ch = true;
                            }
                        }
                    }
                }
            }
            if !ch { break; }
        }
        // Register outputs: a register the routine changes without saving it is handed back to the
        // caller, so it belongs in the routine's linkage (EXTERNAL REGISTER, not saved), not in a
        // local GLOBAL REGISTER declaration, which BLISS saves and restores (the caller then loses
        // the result).  Changed = written in the body, or a global register of a routine it calls.
        for _ in 0..20 {
            let mut ch = false;
            for &e in &rorder {
                // only a routine somebody calls has a caller to hand results to
                if macro_set.contains(&e) || !called.contains(&e) { continue; }
                let sv = saved_of(e);
                let mut cand: BTreeSet<i32> = BTreeSet::new();
                for i in routines[&e].insns.values() {
                    if let Some(t) = i.call_target() {
                        if let Some(c) = info.get(&t) { cand.extend(c.globals.iter().cloned()); }
                        continue;
                    }
                    cand.extend(i.regs_written());
                }
                let x = info.get_mut(&e).unwrap();
                for k in cand {
                    if (1..=5).contains(&k) && !sv.contains(&k) && !x.regparams.contains(&k) && !x.globals.contains(&k) {
                        x.globals.push(k);
                        x.globals.sort();
                        ch = true;
                    }
                }
            }
            if !ch { break; }
        }
        for &e in &rorder {
            if macro_set.contains(&e) { continue; }
            let mut need: BTreeSet<i32> = BTreeSet::new();
            for i in routines[&e].insns.values() {
                if let Some(c) = i.call_target().and_then(|t| info.get(&t)) {
                    need.extend(c.globals.iter().cloned());
                }
            }
            let x = info.get_mut(&e).unwrap();
            x.gdecl = need.into_iter().filter(|k| !x.globals.contains(k) && !x.regparams.contains(k)).collect();
        }
    }
    if std::env::var("BLISSDC_INFO").is_ok() {
        for &e in &rorder {
            let x = &info[&e];
            eprintln!("info {} {} n={} regs={:?} glob={:?} gdecl={:?}", o6(e), routines[&e].name, x.nparams, x.regparams, x.globals, x.gdecl);
        }
    }
    // value-returning routines: R0 used after the call
    let mut lifted: Vec<(u16, Lifter)> = vec![];
    for &e in &rorder {
        let mut l = Lifter::new(false);
        if l.lift(&routines[&e], &mem, &info).is_ok() {
            lifted.push((e, l));
        }
    }
    let mut byname: HashMap<String, Vec<u16>> = HashMap::new();
    for &e in &rorder {
        byname.entry(routines[&e].name.clone()).or_default().push(e);
    }
    for t in ext_sites.keys() {
        byname.entry(mem.name_of(*t)).or_default().push(*t);
    }
    let r0 = Loc::R(0);
    // a routine that loads R0 (not from a call) right before returning, with no use in between, returns it
    for (e, l) in &lifted {
        'blk: for b in &l.order {
            let ss = &l.stmts[b];
            if let Some(k) = ss.iter().position(|s| matches!(s, Stmt::Ret(_))) {
                for s in ss[..k].iter().rev() {
                    let mut u = HashSet::new();
                    st_uses(s, &mut u);
                    if st_def(s) == Some(r0) {
                        if let Stmt::Set(_, x) = s {
                            if !matches!(x, E::Call(..)) && !matches!(x, E::Unk(..)) {
                                info.get_mut(e).unwrap().returns = true;
                                break 'blk;
                            }
                        }
                        break;
                    }
                    if u.contains(&r0) || matches!(s, Stmt::Do(_)) {
                        break;
                    }
                }
            }
        }
    }
    for _ in 0..6 {
        let mut changed = false;
        for (e, l) in &lifted {
            for b in &l.order {
                let ss = &l.stmts[b];
                for (k, s) in ss.iter().enumerate() {
                    let name = match s {
                        Stmt::Set(Place::Loc(Loc::R(0)), E::Call(name, _)) => name,
                        _ => continue,
                    };
                    let mut used = false;
                    let mut broke = false;
                    for s2 in &ss[k + 1..] {
                        if let Stmt::Ret(_) = s2 {
                            used = info[e].returns;
                            broke = true;
                            break;
                        }
                        let mut u = HashSet::new();
                        st_uses(s2, &mut u);
                        if u.contains(&r0) {
                            used = true;
                            broke = true;
                            break;
                        }
                        if st_def(s2) == Some(r0) {
                            broke = true;
                            break;
                        }
                    }
                    if !broke {
                        let mut u = HashSet::new();
                        if let Some(x) = l.bcond.get(b) {
                            locs_in(x, &mut u);
                        }
                        if let Some(x) = l.bcase.get(b) {
                            locs_in(x, &mut u);
                        }
                        if u.contains(&r0) {
                            used = true;
                        }
                    }
                    if used {
                        if let Some(cs) = byname.get(&name.to_string()) {
                            for cc in cs {
                                let x = info.get_mut(cc).unwrap();
                                if !x.returns {
                                    x.returns = true;
                                    changed = true;
                                }
                            }
                        }
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    // user linkage hints win over the analysis
    for (a, h) in &mem.linkages {
        if let Some(x) = info.get_mut(a) {
            if !h.regs.is_empty() || !h.globals.is_empty() {
                x.regparams = h.regs.clone();
                x.globals = h.globals.clone();
                x.gdecl.retain(|k| !h.regs.contains(k) && !h.globals.contains(k));
            }
            if let Some(v) = h.value {
                x.returns = v;
            }
        }
    }
    Ok(Task { mem, routines, rorder, info, macros: macro_set })
}

pub(crate) fn bname(n: &str) -> String {
    n.to_uppercase()
        .chars()
        .map(|ch| if ch.is_ascii_uppercase() || ch.is_ascii_digit() || ch == '_' || ch == '$' { ch } else { '_' })
        .collect()
}

pub(crate) fn wordch(ch: char) -> bool {
    ch.is_alphanumeric() || ch == '_'
}

/// re.sub(r'\b([A-Z][A-Z0-9]*\.[A-Z0-9.$]+)\b', bname)
pub(crate) fn sub_dotted(l: &str) -> String {
    if !l.contains('.') {
        return l.to_string();
    }
    let ch: Vec<char> = l.chars().collect();
    let n = ch.len();
    let mut out = String::with_capacity(l.len());
    let mut i = 0;
    let up = |x: char| x.is_ascii_uppercase() || x.is_ascii_digit();
    while i < n {
        if ch[i].is_ascii_uppercase() && (i == 0 || !wordch(ch[i - 1])) {
            let mut j = i + 1;
            while j < n && up(ch[j]) {
                j += 1;
            }
            if j < n && ch[j] == '.' {
                let mut k = j + 1;
                while k < n && (up(ch[k]) || ch[k] == '.' || ch[k] == '$') {
                    k += 1;
                }
                let mut e = k;
                let mut found = false;
                while e > j + 1 {
                    let a = wordch(ch[e - 1]);
                    let b = e < n && wordch(ch[e]);
                    if a != b {
                        found = true;
                        break;
                    }
                    e -= 1;
                }
                if found {
                    let m: String = ch[i..e].iter().collect();
                    out.push_str(&bname(&m));
                    i = e;
                    continue;
                }
            }
        }
        out.push(ch[i]);
        i += 1;
    }
    out
}

/// re.findall(r'\b([XL]\d+)\b')
pub(crate) fn find_locals(lines: &[String], used: &mut BTreeSet<(char, u64, u64)>) {
    for l in lines {
        for tok in l.split(|ch: char| !wordch(ch)) {
            let mut it = tok.chars();
            if let Some(f) = it.next() {
                let rest = it.as_str();
                let (a, b) = match rest.split_once('_') { Some((a, b)) => (a, b), None => (rest, "") };
                let num = |x: &str| !x.is_empty() && x.chars().all(|c| c.is_ascii_digit());
                if (f == 'X' || f == 'L') && num(a) && (b.is_empty() || num(b)) {
                    if let Ok(v) = a.parse::<u64>() {
                        used.insert((f, v, b.parse::<u64>().unwrap_or(0)));
                    }
                }
            }
        }
    }
}

pub(crate) struct Out {
    lines: Vec<String>,
    ext: BTreeSet<String>,
    vectors: BTreeSet<String>,
    defined: BTreeSet<(String, bool)>,
    failed: Vec<(u16, String)>,
    gvars: BTreeSet<String>,
}

fn module_header(mem: &Program, modname: &str) -> String {
    let mut sw: Vec<String> = vec![];
    if let Some(e) = &mem.environment {
        sw.push(format!("ENVIRONMENT ({})", e));
    }
    if MODULE_O0.with(|m| m.get()) {
        sw.push("OPTLEVEL = 0".into());
    }
    if sw.is_empty() { format!("MODULE {} =", modname) } else { format!("MODULE {} ({}) =", modname, sw.join(", ")) }
}

thread_local! {
    static MODULE_O0: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static KNOB_MAP: std::cell::RefCell<HashMap<String, u32>> = std::cell::RefCell::new(HashMap::new());
    static KNOB_DEFAULT: std::cell::Cell<u32> = const { std::cell::Cell::new(DEFAULT_KNOBS) };
}

pub(crate) fn decompile_one(t: &mut Task, e: u16, o: &mut Out) -> Result<(), String> {
    let r = t.routines.get_mut(&e).ok_or_else(|| format!("KeyError: {}", e))?;
    let kn = KNOB_MAP.with(|m| m.borrow().get(&bname(&r.name)).cloned()).unwrap_or_else(|| KNOB_DEFAULT.with(|d| d.get()));
    KNOBS.with(|k| k.set(kn));
    // knob 11 / 26: undo cross-jumping; lone shared conditional branches are always split
    let mut rcopy = Routine { entry: r.entry, name: r.name.clone(), insns: r.insns.clone(), order: r.order.clone(), blocks: r.blocks.clone() };
    rcopy.dup_tails(if knob(26) { 8 } else if knob(11) { 4 } else { 0 });
    let r: &mut Routine = &mut rcopy;
    let mut l = Lifter::new(true);
    l.bind_regs = true;
    l.lift(r, &t.mem, &t.info)?;
    l.returns = t.info.get(&e).map(|x| x.returns).unwrap_or(false);
    if !l.returns {
        for ss in l.stmts.values_mut() {
            ss.retain(|s| !matches!(s, Stmt::Ret(_)));
        }
    }
    l.cleanup(r)?;
    if std::env::var("BLISSDC_DUMP").map(|x| x == o6(e)).unwrap_or(false) {
        for (b, ss) in &l.stmts {
            eprintln!("{} {:?} cond {:?} succ {:?}", o6(*b), ss, l.bcond.get(b), r.blocks.get(b).map(|x| x.succ.clone()));
        }
    }
    let p = Printer { maxparam: l.maxparam, globals: BTreeSet::new(), externals: BTreeSet::new(), vectors: BTreeSet::new() };
    combine_conditions(r, &mut l)?;
    let r = &*r;
    let mut s = Structurer::new(r, &l, p);
    s.run()?;
    s.out = tidy::tidy(std::mem::take(&mut s.out));
    s.labels = tidy::used_labels(&s.out).into_iter().collect();
    let mut body: Vec<String> = s.out.iter().map(|(ind, t)| format!("{}{}", "    ".repeat(*ind), t)).collect();
    let texts: Vec<String> = s.out.iter().map(|(_, t)| t.clone()).collect();
    let labels: Vec<String> = s.labels.iter().cloned().collect();
    let p = s.p;
    let regs: Vec<i32> = t.info.get(&e).map(|x| x.regparams.clone()).unwrap_or_default();
    let mut params: Vec<String> = regs.iter().map(|k| format!("PR{}", k)).collect();
    let (globs, gdecl) = t.info.get(&e).map(|x| (x.globals.clone(), x.gdecl.clone())).unwrap_or_default();
    let mut regs = regs;
    regs.extend(globs.iter().map(|k| k + 10));
    params.extend((0..l.maxparam).map(|k| format!("A{}", k + 1)));
    let nm = bname(&r.name);
    let attrs = attr_str(&regs, l.returns);
    let hdr = format!(
        "GLOBAL ROUTINE {}{}{} =",
        nm,
        if params.is_empty() { String::new() } else { format!(" ({})", params.join(", ")) },
        attrs
    );
    o.defined.insert((nm, l.returns));
    if READABLE.with(|x| x.get()) {
        if let Some(c) = GSYMS.with(|g| g.borrow().get(&e).map(|x| x.1.clone())) {
            let words: Vec<&str> = c.split_whitespace().collect();
            let mut line = String::from("!");
            for w in words {
                if line.len() + w.len() > 100 { o.lines.push(line); line = String::from("!"); }
                line.push(' ');
                line.push_str(w);
            }
            if line.len() > 1 { o.lines.push(line); }
        }
    }
    o.lines.push(hdr);
    o.lines.push("    BEGIN".into());
    let mut nregdecl = 0;
    for k in &globs {
        o.lines.push(format!("    EXTERNAL REGISTER GR{} = {};", k, k));
        nregdecl += 1;
    }
    for k in &gdecl {
        o.lines.push(format!("    GLOBAL REGISTER GR{} = {};", k, k));
        nregdecl += 1;
    }
    let mut used = BTreeSet::new();
    find_locals(&texts, &mut used);
    // knob 21: the stack locals as one frame vector, F[i] at the ROM's offsets (low address first)
    let mut frame_decl: Option<String> = None;
    if knob(21) {
        // the prologue's local area: after the register saves, SUB #n,SP / TST -(SP) / CMP -(SP),-(SP)
        let (saved, alloc) = arch::frame_layout(&r.blocks[&r.entry].ins, &t.mem);
        let (mut lo, mut hi) = (saved as u64 + 2, (saved + alloc) as u64);
        if knob(22) {   // knob 22: every stack local in the vector, push temporaries included
            let all: Vec<u64> = used.iter().filter(|(c0, _, _)| *c0 == 'L').map(|x| x.1).collect();
            if let (Some(a), Some(b)) = (all.iter().min(), all.iter().max()) { lo = *a; hi = *b; }
        }
        let ls: Vec<u64> = used.iter().filter(|(c0, v, _)| *c0 == 'L' && *v >= lo && *v <= hi).map(|x| x.1).collect();
        let webs = used.iter().any(|(c0, _, w)| *c0 == 'L' && *w > 0);
        if !ls.is_empty() && !webs {
            let (kmax, kmin) = (hi, lo);
            let n = (kmax - kmin) / 2 + 1;
            for line in body.iter_mut() {
                let mut out = String::new();
                let ch: Vec<char> = line.chars().collect();
                let mut i = 0;
                while i < ch.len() {
                    let prev_ok = i == 0 || !(ch[i - 1].is_ascii_alphanumeric() || ch[i - 1] == '_');
                    if ch[i] == 'L' && prev_ok {
                        let mut j = i + 1;
                        while j < ch.len() && ch[j].is_ascii_digit() { j += 1; }
                        let next_ok = j == ch.len() || !(ch[j].is_ascii_alphanumeric() || ch[j] == '_');
                        if j > i + 1 && next_ok {
                            let k: u64 = ch[i + 1..j].iter().collect::<String>().parse().unwrap();
                            if ls.contains(&k) {
                                out.push_str(&format!("F[{}]", (kmax - k) / 2));
                                i = j;
                                continue;
                            }
                        }
                    }
                    out.push(ch[i]);
                    i += 1;
                }
                *line = out;
            }
            used.retain(|(c0, v, _)| !(*c0 == 'L' && ls.contains(v)));
            frame_decl = Some(format!("F : VECTOR[{}]", n));
        }
    }
    let nm_of = |c0: &char, v: &u64, w: &u64| if *w > 0 { format!("{}{}_{}", c0, v, w) } else { format!("{}{}", c0, v) };
    // knob 7: R1..R5 variables live where the ROM kept them (REGISTER Xk = k)
    let pin = knob(7);
    let lo_reg = if knob(17) { 0 } else { 1 };   // knob 17: R0 variables pinned too
    let regd: Vec<String> = used.iter().filter(|(c0, v, _)| pin && *c0 == 'X' && (lo_reg..=5).contains(v))
        .map(|(c0, v, w)| format!("{} = {}", nm_of(c0, v, w), v)).collect();
    let mut locs: Vec<String> = used.iter().filter(|(c0, v, _)| !(pin && *c0 == 'X' && (lo_reg..=5).contains(v)))
        .map(|(c0, v, w)| nm_of(c0, v, w)).collect();
    if knob(20) { locs.reverse(); }   // knob 20: stack locals declared high frame offset first
    if let Some(f) = frame_decl { locs.insert(0, f); }
    if !regd.is_empty() {
        o.lines.push(format!("    REGISTER {};", regd.join(", ")));
        nregdecl += 1;
    }
    if !locs.is_empty() {
        o.lines.push(format!("    LOCAL {};", locs.join(", ")));
    }
    let used: BTreeSet<(char, u64, u64)> = if locs.is_empty() { BTreeSet::new() } else { [('L', 0u64, 0u64)].into_iter().collect() };
    let start = o.lines.len() - nregdecl - if used.is_empty() { 2 } else { 3 };
    if !labels.is_empty() {
        o.lines.push(format!("    LABEL {};", labels.join(", ")));
    }
    o.lines.extend(body);
    o.lines.push("    END;".into());
    o.lines.push(String::new());
    for x in &p.externals {
        o.ext.insert(bname(x));
    }
    for a in &p.globals {
        o.ext.insert(gsym(*a));
        o.gvars.insert(gsym(*a));
    }
    for a in &p.vectors {
        o.vectors.insert(gsym(*a));
    }
    // earlier lines have already been through the substitution (it is idempotent)
    for ln in o.lines[start..].iter_mut() {
        let n = sub_dotted(ln);
        *ln = n;
    }
    Ok(())
}

pub(crate) fn linkage_name(regs: &[i32]) -> String {
    // k < 10: REGISTER = k parameter; k >= 10: GLOBAL register k - 10
    format!("L_{}", regs.iter().map(|k| if *k >= 10 { format!("G{}", k - 10) } else { format!("R{}", k) }).collect::<Vec<_>>().join("_"))
}

pub(crate) fn linkage_decl(r: &[i32]) -> String {
    let ps: Vec<String> = r.iter().filter(|k| **k < 10).map(|k| format!("REGISTER = {}", k)).collect();
    let gs: Vec<String> = r.iter().filter(|k| **k >= 10).map(|k| format!("GR{} = {}", k - 10, k - 10)).collect();
    let mut d = String::from("JSR");
    if !ps.is_empty() { d.push_str(&format!(" ({})", ps.join(", "))); }
    if !gs.is_empty() { d.push_str(&format!(" : GLOBAL ({})", gs.join(", "))); }
    format!("LINKAGE {} = {};", linkage_name(r), d)
}

pub(crate) fn attr_str(regs: &[i32], returns: bool) -> String {
    let mut a: Vec<String> = vec![];
    if !regs.is_empty() {
        a.push(linkage_name(regs));
    }
    if !returns {
        a.push("NOVALUE".into());
    }
    if a.is_empty() { String::new() } else { format!(" : {}", a.join(" ")) }
}

pub(crate) fn build_module(t: &mut Task, want: &[u16], modname: &str) -> String {
    let regs_of: HashMap<String, Vec<i32>> = t.routines.iter()
        .map(|(e, r)| (bname(&r.name), t.info.get(e).map(|x| {
            let mut v = x.regparams.clone();
            v.extend(x.globals.iter().map(|k| k + 10));
            v
        }).unwrap_or_default()))
        .collect();
    // names of routines known not to return a value (for EXTERNAL ROUTINE ... : NOVALUE)
    let novalue: BTreeSet<String> = t.routines.iter()
        .filter(|(e, _)| t.info.get(e).map(|x| !x.returns).unwrap_or(false))
        .map(|(_, r)| bname(&r.name)).collect();
    let want: Vec<u16> = want.to_vec();
    let mut o = Out { lines: vec![], ext: BTreeSet::new(), vectors: BTreeSet::new(), defined: BTreeSet::new(), failed: vec![], gvars: BTreeSet::new() };
    for &e in &want {
        let mark = o.lines.len();
        let defsnap = o.defined.clone();
        if let Err(msg) = decompile_one(t, e, &mut o) {
            o.failed.push((e, msg));
            o.lines.truncate(mark);
            o.defined = defsnap;
        }
    }
    let defnames: BTreeSet<&String> = o.defined.iter().map(|x| &x.0).collect();
    let gl: Vec<&String> =
        o.ext.iter().filter(|x| o.gvars.contains(*x)).collect();
    let rt: Vec<&String> = o.ext.iter().filter(|x| !defnames.contains(x) && !gl.contains(x)).collect();
    let mut src: Vec<String> = vec![
        module_header(&t.mem, modname),
        "BEGIN".into(),
        String::new(),
    ];
    let mut links: BTreeSet<Vec<i32>> = BTreeSet::new();
    for (n, _) in &o.defined {
        if let Some(r) = regs_of.get(n) { if !r.is_empty() { links.insert(r.clone()); } }
    }
    for x in &rt {
        if let Some(r) = regs_of.get(*x) { if !r.is_empty() { links.insert(r.clone()); } }
    }
    for r in &links {
        src.push(linkage_decl(r));
    }
    if !o.defined.is_empty() {
        src.push("FORWARD ROUTINE".into());
        let v: Vec<String> = o.defined.iter()
            .map(|(n, v)| format!("{}{}", n, attr_str(regs_of.get(n).map(|x| x.as_slice()).unwrap_or(&[]), *v))).collect();
        src.push(format!("    {};", v.join(",\n    ")));
    }
    let is_builtin = |x: &str| crate::arch::target::BUILTINS.contains(&x);
    let builtins: Vec<&String> = rt.iter().cloned().filter(|x| is_builtin(x)).collect();
    let rt: Vec<&String> = rt.into_iter().filter(|x| !is_builtin(x)).collect();
    if !builtins.is_empty() {
        src.push(format!("BUILTIN {};", builtins.iter().map(|x| x.as_str()).collect::<Vec<_>>().join(", ")));
    }
    if !rt.is_empty() {
        src.push("EXTERNAL ROUTINE".into());
        let v: Vec<String> = rt.iter()
            .map(|x| format!("{}{}", x, attr_str(regs_of.get(*x).map(|r| r.as_slice()).unwrap_or(&[]), !novalue.contains(*x)))).collect();
        src.push(format!("    {};", v.join(",\n    ")));
    }
    if !gl.is_empty() {
        src.push("EXTERNAL".into());
        let v: Vec<String> =
            gl.iter().map(|g| format!("{}{}", g, if o.vectors.contains(*g) { " : VECTOR" } else { "" })).collect();
        src.push(format!("    {};", v.join(",\n    ")));
    }
    src.push(String::new());
    src.append(&mut o.lines);
    src.push("END".into());
    src.push("ELUDOM".into());
    let mut text = String::new();
    let src: Vec<String> = src.iter().flat_map(|x| x.split('\n').map(|y| y.to_string()).collect::<Vec<_>>()).collect();
    for l in src {
        let mut l: Vec<char> = l.chars().collect();
        while l.len() > 120 {
            let cut = match (40..118).rev().find(|&i| l[i] == ' ') {
                Some(c0) => c0,
                None => break,
            };
            let lead = l.iter().take_while(|ch| ch.is_whitespace()).count();
            let ind = lead + 8;
            // the earlier Python version looped forever when the continuation is not shorter (indent > ~110); stop instead
            if ind + (l.len() - cut - 1) >= l.len() {
                break;
            }
            text.extend(l[..cut].iter());
            text.push('\n');
            let mut nl: Vec<char> = vec![' '; ind];
            nl.extend_from_slice(&l[cut + 1..]);
            l = nl;
        }
        text.extend(l.iter());
        text.push('\n');
    }
    for (e, msg) in &o.failed {
        eprintln!("! {} {}: {}", o6(*e), t.routines[e].name, msg);
    }
    text
}

// ------------------------------------------------------------------ library entry points

/// How routines are written out.
#[derive(Clone, Debug)]
pub struct Options {
    /// natural source: names and comments from the symbols, idiom knobs only
    pub readable: bool,
    /// knob bits for routines not in `knob_map`
    pub knob_default: u32,
    /// per-routine knob bits, keyed by the BLISS routine name as printed (`R001000`)
    pub knob_map: HashMap<String, u32>,
}

/// knobs of `--readable`: idioms on, matching tricks (pinned registers, frame vectors, OPTLEVEL) off
pub const READABLE_KNOBS: u32 = 1 | (1 << 8) | (1 << 9) | (1 << 10) | (1 << 12) | (1 << 14);

impl Default for Options {
    fn default() -> Options {
        Options { readable: false, knob_default: DEFAULT_KNOBS, knob_map: HashMap::new() }
    }
}

impl Options {
    pub fn readable() -> Options {
        Options { readable: true, knob_default: READABLE_KNOBS, knob_map: HashMap::new() }
    }

    /// a knob file: "ROUTINE value" lines (decimal); other lines are ignored
    pub fn load_knob_text(&mut self, txt: &str) {
        for l in txt.lines() {
            let f: Vec<&str> = l.split_whitespace().collect();
            if f.len() == 2 {
                if let Ok(n) = f[1].parse::<u32>() {
                    self.knob_map.insert(f[0].to_string(), n);
                }
            }
        }
    }

    /// `--knobs FILE|N`: a bare number sets the default for every routine
    pub fn set_knobs(&mut self, spec: &str) -> Result<(), String> {
        if let Ok(n) = spec.parse::<u32>() {
            self.knob_default = n;
            return Ok(());
        }
        let txt = std::fs::read_to_string(spec).map_err(|e| format!("{}: {}", spec, e))?;
        self.load_knob_text(&txt);
        Ok(())
    }

    /// install these options for decompilation on the current thread
    pub fn install(&self, mem: &Program) {
        READABLE.with(|r| r.set(self.readable));
        KNOB_DEFAULT.with(|d| d.set(self.knob_default));
        KNOB_MAP.with(|m| *m.borrow_mut() = self.knob_map.clone());
        set_gsyms(&mem.syms);
    }

    pub fn knobs_of(&self, name: &str) -> u32 {
        self.knob_map.get(name).cloned().unwrap_or(self.knob_default)
    }
}

/// BLISS name of a routine (upper case, `.` and other punctuation as `_`)
pub fn routine_bname(t: &Task, e: u16) -> String {
    bname(&t.routines[&e].name)
}

/// Resolve routine selectors (octal address or name, BLISS or listing spelling); empty = every
/// routine in the program's own ranges.  Overlay thunks and `skip` names are dropped.
pub fn select(t: &Task, sel: &[String], skip: &[String]) -> Result<Vec<u16>, String> {
    let mut want: Vec<u16> = vec![];
    for x in sel {
        let a = match u16::from_str_radix(x, 8) {
            Ok(v) => v,
            Err(_) => {
                let bx = bname(x);
                let mut hit: Vec<u16> = t.rorder.iter().cloned().filter(|e| bname(&t.routines[e].name) == bx).collect();
                hit.sort();
                *hit.first().ok_or_else(|| format!("no routine named {}", x))?
            }
        };
        want.push(a);
    }
    if want.is_empty() {
        want = t.rorder.iter().cloned().filter(|e| t.mem.is_own(*e)).collect();
        want.sort();
    }
    for e in &want {
        if !t.routines.contains_key(e) {
            return Err(format!("KeyError: no routine at {}", o6(*e)));
        }
    }
    let skip: HashSet<String> = skip.iter().map(|s| s.to_uppercase()).collect();
    want.retain(|e| !skip.contains(&bname(&t.routines[e].name)));
    // hand-written MACRO-11 (traps, interrupt code, stack switches, thunks) is not BLISS output
    want.retain(|e| !t.macros.contains(e));
    // overlay thunks (JSR R5,dispatcher / inline arguments) are build artefacts, not BLISS code
    want.retain(|e| {
        let r = &t.routines[e];
        match r.insns.get(e) {
            Some(i) => !i.is_thunk_call(&t.mem),
            None => true,
        }
    });
    Ok(want)
}

/// The per-instruction map used for scoring: routine, address, octal words, disassembly.
pub fn map_text(t: &Task, want: &[u16]) -> String {
    let mut txt = String::new();
    for &e in want {
        let r = &t.routines[&e];
        for (pc, i) in &r.insns {
            let ws: Vec<String> = (0..i.nwords).map(|k| format!("{:06o}", t.mem.rw(pc.wrapping_add(2 * k)).unwrap_or(0))).collect();
            let ops: Vec<String> = i.ops.iter().map(|o| arch::fmt_op(o, &t.mem)).collect();
            txt.push_str(&format!("{}\t{:06o}\t{}\t{} {}\n", bname(&r.name), pc, ws.join(" "), i.mn, ops.join(",")));
        }
    }
    txt
}

/// One module with every routine in `want` (names truncated to 6 characters, as BLISS-16 wants).
pub fn decompile_module(t: &mut Task, opts: &Options, want: &[u16], module: &str) -> String {
    opts.install(&t.mem);
    MODULE_O0.with(|m| m.set(false));
    let modname: String = module.chars().take(6).collect();
    build_module(t, want, &modname)
}

/// Modules of at most `n` routines each: (file name, text).  Routines with knob 16 go into their
/// own OPTLEVEL = 0 modules after the others.  Files are `STEM_NN.b16`, modules `XXXXNN`.
pub fn decompile_batch(t: &mut Task, opts: &Options, want: &[u16], n: usize, module: &str, stem: &str) -> Vec<(String, String)> {
    opts.install(&t.mem);
    let (lo, hi): (Vec<u16>, Vec<u16>) = want.iter().partition(|&&e| opts.knobs_of(&routine_bname(t, e)) & (1 << 16) != 0);
    let mut chunks: Vec<(Vec<u16>, bool)> = hi.chunks(n.max(1)).map(|c| (c.to_vec(), false)).collect();
    chunks.extend(lo.chunks(n.max(1)).map(|c| (c.to_vec(), true)));
    let mut out = vec![];
    for (k, (chunk, o0)) in chunks.iter().enumerate() {
        let modname = format!("{}{:02}", module.chars().take(4).collect::<String>(), k + 1);
        MODULE_O0.with(|m| m.set(*o0));
        let text = build_module(t, chunk, &modname);
        out.push((format!("{}_{:02}.b16", stem, k + 1), text));
    }
    MODULE_O0.with(|m| m.set(false));
    out
}
