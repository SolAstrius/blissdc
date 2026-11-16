// SPDX-License-Identifier: Apache-2.0
//! Architecture-independent lifter state and the dataflow cleanup over the lifted statements:
//! copy propagation, dead code, expression folding, def-use webs.  The instruction-level lifting
//! (`Lifter::lift`) lives in the architecture back end.
use crate::ir::*;
use crate::arch::target::Flags;
use crate::cfg::*;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

thread_local! {
    /// per-routine decompilation choices (bit flags), picked by compiling variants against the ROM
    pub static KNOBS: std::cell::Cell<u32> = const { std::cell::Cell::new(DEFAULT_KNOBS) };
}
pub const DEFAULT_KNOBS: u32 = 1 | (1 << 7) | (1 << 8) | (1 << 9) | (1 << 10) | (1 << 12) | (1 << 14) | (1 << 17);
// knob 11: undo cross-jumping (dup_tails)
pub fn knob(bit: u32) -> bool {
    KNOBS.with(|k| k.get() & (1 << bit) != 0)
}
pub fn knobs() -> u32 {
    KNOBS.with(|k| k.get())
}

thread_local! {
    /// --readable: names and comments from the disassembly's symbol file instead of G<octal>
    pub static READABLE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// address -> (BLISS name, comment) for data/RAM/code labels of the task and the kernel
    pub static GSYMS: std::cell::RefCell<HashMap<u16, (String, String)>> = std::cell::RefCell::new(HashMap::new());
}

/// install the readable names/comments of a program for this thread
pub fn set_gsyms(m: &HashMap<u16, (String, String)>) {
    GSYMS.with(|g| *g.borrow_mut() = m.clone());
}

pub fn gsym(a: u16) -> String {
    if READABLE.with(|r| r.get()) {
        if let Some(n) = GSYMS.with(|g| g.borrow().get(&a).map(|x| x.0.clone())) {
            if !n.is_empty() { return n; }
        }
    }
    format!("G{}", o6(a))
}

pub use crate::program::o6;


// ------------------------------------------------------------------ lifting
pub struct Info {
    pub nparams: i32,
    pub returns: bool,
    /// registers carrying parameters (in formal order), empty for the standard stack linkage
    pub regparams: Vec<i32>,
    /// linkage GLOBAL registers (EXTERNAL REGISTER GRk = k inside the routine)
    pub globals: Vec<i32>,
    /// GLOBAL REGISTER GRk = k declared here (the routine sets up a global its callees share)
    pub gdecl: Vec<i32>,
}

#[derive(Default)]
pub struct Lifter {
    /// ea() is evaluating a source operand (ea_src)
    pub ea_is_src: bool,
    /// the instruction being lifted is a byte operation on a register that changes only its low byte
    pub byte_reg: bool,
    pub depth_in: HashMap<u16, i32>,
    pub saved: i32,
    pub maxparam: i32,
    pub stmts: HashMap<u16, Vec<Stmt>>,
    pub order: Vec<u16>,
    pub bcond: HashMap<u16, E>,
    pub bcase: HashMap<u16, E>,
    pub flags_out: HashMap<u16, Flags>,
    pub bcond_pred: HashMap<u16, HashMap<u16, E>>,
    pub returns: bool,
    pub fin: bool,
    pub frame_base: i32,
    pub skip: usize,
    pub live_out_nocond: HashMap<u16, HashSet<Loc>>,
    /// bind register parameters at entry (off while detecting them)
    pub bind_regs: bool,
    /// registers that are linkage globals in this routine: read and written as Q(k + 10)
    pub gregs: HashSet<i32>,
}

pub(crate) fn preds_of(r: &Routine) -> HashMap<u16, Vec<u16>> {
    let mut preds: HashMap<u16, Vec<u16>> = HashMap::new();
    for (&p, blk) in &r.blocks {
        for &(t, _) in &blk.succ {
            preds.entry(t).or_default().push(p);
        }
    }
    preds
}

type Av = BTreeMap<Loc, Loc>;

fn av_update(av: &mut Av, s: &Stmt) {
    if let Stmt::Set(Place::Loc(d), e) = s {
        av.retain(|k, v| k != d && v != d);
        if d.is_rs() {
            if let E::Loc(src) = e {
                // knob 15: a stack parameter copied into R1..R5 stays a register variable (the ROM keeps it there)
                let keep = knob(15) && matches!(d, Loc::R(k) if (1..=5).contains(k)) && matches!(src, Loc::P(_));
                if src.is_p() && !keep {
                    av.insert(*d, *src);
                }
            }
        }
    }
}

fn sub_av(e: &E, av: &Av) -> E {
    let mut e = e.clone();
    for (k, v) in av {
        e = subst(&e, *k, &E::Loc(*v));
    }
    e
}

impl Lifter {
    pub fn new(fin: bool) -> Lifter {
        Lifter { fin, ..Default::default() }
    }


    /// registers read before being written, at routine entry (after the prologue): register parameters
    pub fn live_in_regs(&self, r: &Routine) -> Vec<i32> {
        // hand-written code that switches stacks: no BLISS linkage
        if self.stmts.values().flatten().any(|st| matches!(st, Stmt::Unk(t) if t.starts_with("write to ('sp'"))) {
            return vec![];
        }
        // callee-saved R1..R5 pushed into a slot and later popped back into the same register: a save, not a use
        let mut pushes: HashSet<(Loc, i32)> = HashSet::new();
        let mut pops: HashSet<(Loc, i32)> = HashSet::new();
        for st in self.stmts.values().flatten() {
            if let Stmt::Set(Place::Loc(d), E::Loc(src)) = st {
                match (d, src) {
                    (Loc::S(_), Loc::R(k)) if (1..=5).contains(k) => { pushes.insert((*d, *k)); }
                    (Loc::R(k), Loc::S(_)) if (1..=5).contains(k) => { pops.insert((*src, *k)); }
                    _ => {}
                }
            }
        }
        let saves: HashSet<(Loc, i32)> = pushes.intersection(&pops).cloned().collect();
        let is_save = |st: &Stmt| -> bool {
            if let Stmt::Set(Place::Loc(d), E::Loc(Loc::R(k))) = st {
                return saves.contains(&(*d, *k));
            }
            false
        };
        let mut live_in: HashMap<u16, HashSet<Loc>> = r.blocks.keys().map(|&b| (b, HashSet::new())).collect();
        let mut changed = true;
        while changed {
            changed = false;
            for (&b, blk) in &r.blocks {
                let mut l: HashSet<Loc> = HashSet::new();
                for (t, _) in &blk.succ {
                    if let Some(x) = live_in.get(t) {
                        l.extend(x.iter().cloned());
                    }
                    // a cross-jumped branch whose condition depends on the edge we came by
                    if let Some(c) = self.bcond_pred.get(t).and_then(|per| per.get(&b)) { locs_in(c, &mut l); }
                }
                if let Some(c) = self.bcond.get(&b) { locs_in(c, &mut l); }
                if let Some(c) = self.bcase.get(&b) { locs_in(c, &mut l); }
                if let Some(ss) = self.stmts.get(&b) {
                    for st in ss.iter().rev() {
                        if let Some(d) = st_def(st) { l.remove(&d); }
                        // RETURN R0 is the lifter's guess at a value, not evidence of an input
                        if !is_save(st) && !matches!(st, Stmt::Ret(_)) { st_uses(st, &mut l); }
                    }
                }
                if l != live_in[&b] {
                    live_in.insert(b, l);
                    changed = true;
                }
            }
        }
        if std::env::var("BLISSDC_LIVEDBG").map(|x| x == o6(r.entry)).unwrap_or(false) {
            for b in r.blocks.keys() {
                let mut v: Vec<String> = live_in[b].iter().map(|l| l.name()).collect();
                v.sort();
                eprintln!("{} live {:?} stmts {:?} cond {:?} pred {:?}", o6(*b), v, self.stmts.get(b), self.bcond.get(b), self.bcond_pred.get(b));
            }
        }
        let mut v: Vec<i32> = live_in[&r.entry].iter()
            .filter_map(|l| if let Loc::R(k) = l { if *k <= 5 { Some(*k) } else { None } } else { None })
            .collect();
        v.sort();
        v
    }


    /// Stack slots whose address is taken (E::Frame) are real memory variables: rename S(k) -> M(k)
    /// everywhere so the cleanup no longer treats them as temporaries.
    pub(crate) fn mark_addressed(&mut self) {
        fn frames(e: &E, acc: &mut HashSet<i32>) {
            if let E::Frame(o) = e {
                acc.insert(*o & !1);     // an odd offset addresses the high byte of that word
            }
            for k in e.kids() {
                frames(k, acc);
            }
        }
        let mut offs: HashSet<i32> = HashSet::new();
        for ss in self.stmts.values() {
            for st in ss {
                match st {
                    Stmt::Set(p, e) => {
                        frames(e, &mut offs);
                        if let Place::Mem(a, _) = p {
                            frames(a, &mut offs);
                        }
                    }
                    Stmt::Do(e) | Stmt::Ret(e) => frames(e, &mut offs),
                    _ => {}
                }
            }
        }
        for e in self.bcond.values().chain(self.bcase.values()) {
            frames(e, &mut offs);
        }
        let ks: HashSet<i32> = offs.into_iter().filter(|o| *o < 2).map(|o| -o).collect();
        if ks.is_empty() {
            return;
        }
        fn ren_e(e: &E, ks: &HashSet<i32>) -> E {
            let mut out = e.clone();
            for &k in ks {
                out = subst(&out, Loc::S(k), &E::Loc(Loc::M(k)));
            }
            out
        }
        let ren_l = |l: &Loc| -> Loc {
            if let Loc::S(k) = l {
                if ks.contains(k) {
                    return Loc::M(*k);
                }
            }
            *l
        };
        for ss in self.stmts.values_mut() {
            for st in ss.iter_mut() {
                *st = match &*st {
                    Stmt::Set(Place::Loc(l), e) => Stmt::Set(Place::Loc(ren_l(l)), ren_e(e, &ks)),
                    Stmt::Set(Place::Mem(a, b), e) => Stmt::Set(Place::Mem(ren_e(a, &ks), *b), ren_e(e, &ks)),
                    Stmt::Do(e) => Stmt::Do(ren_e(e, &ks)),
                    Stmt::Ret(e) => Stmt::Ret(ren_e(e, &ks)),
                    Stmt::Post(l, n) => Stmt::Post(ren_l(l), *n),
                    other => other.clone(),
                };
            }
        }
        for v in self.bcond.values_mut().chain(self.bcase.values_mut()) {
            *v = ren_e(v, &ks);
        }
        for per in self.bcond_pred.values_mut() {
            for v in per.values_mut() {
                *v = ren_e(v, &ks);
            }
        }
    }


    pub(crate) fn st(&self, b: u16) -> Result<&Vec<Stmt>, String> {
        self.stmts.get(&b).ok_or_else(|| format!("KeyError: {}", b))
    }

    // ---------------------------------------------------------------- dataflow cleanup

    pub(crate) fn copyprop(&mut self, r: &Routine) -> Result<(), String> {
        let preds = preds_of(r);
        let mut inn: HashMap<u16, Option<Av>> = r.blocks.keys().map(|&b| (b, None)).collect();
        inn.insert(r.entry, Some(Av::new()));
        let mut outm: HashMap<u16, Av> = HashMap::new();
        let mut changed = true;
        while changed {
            changed = false;
            for &b in r.blocks.keys() {
                let i: Av = if b == r.entry {
                    Av::new()
                } else {
                    let ps: Vec<&Av> =
                        preds.get(&b).map(|v| v.iter().filter_map(|p| outm.get(p)).collect()).unwrap_or_default();
                    if ps.is_empty() {
                        continue;
                    }
                    let mut i = ps[0].clone();
                    for o in &ps[1..] {
                        i.retain(|k, v| o.get(k) == Some(v));
                    }
                    i
                };
                let mut o = i.clone();
                for s in self.st(b)? {
                    av_update(&mut o, s);
                }
                if inn[&b].as_ref() != Some(&i) || outm.get(&b) != Some(&o) {
                    inn.insert(b, Some(i));
                    outm.insert(b, o);
                    changed = true;
                }
            }
        }
        for &b in r.blocks.keys() {
            let mut av: Av = inn[&b].clone().unwrap_or_default();
            let mut new = vec![];
            for s in self.st(b)?.clone() {
                let s = if av.is_empty() {
                    s
                } else {
                    match s {
                        Stmt::Set(tgt, e) => {
                            let e = sub_av(&e, &av);
                            let tgt = match tgt {
                                Place::Mem(a, by) => Place::Mem(sub_av(&a, &av), by),
                                t => t,
                            };
                            Stmt::Set(tgt, e)
                        }
                        Stmt::Do(e) => Stmt::Do(sub_av(&e, &av)),
                        Stmt::Ret(e) => Stmt::Ret(sub_av(&e, &av)),
                        s => s,
                    }
                };
                av_update(&mut av, &s);
                new.push(s);
            }
            self.stmts.insert(b, new);
            if let Some(e) = self.bcond.get(&b) {
                let e = sub_av(e, &av);
                self.bcond.insert(b, e);
            }
            if let Some(e) = self.bcase.get(&b) {
                let e = sub_av(e, &av);
                self.bcase.insert(b, e);
            }
        }
        for per in self.bcond_pred.values_mut() {
            for (p, e) in per.iter_mut() {
                if let Some(o) = outm.get(p) {
                    *e = sub_av(e, o);
                }
            }
        }
        Ok(())
    }


    /// Give every def-use web of a register / stack temporary its own name, so BLISS allocates each
    /// one separately (the original locals were not tied to the register the compiler later chose).
    /// A statement that reads and redefines the same name (X = .X + 1) keeps one web.
    pub fn split_webs(&mut self, r: &Routine) {
        // knob bits 0..5: split webs of R0..R5; bit 6: split stack temporaries
        let regs_mask: u32 = knobs() & 0o77;
        let split_s = knob(6);
        let splittable = |l: &Loc| matches!(l, Loc::R(k) if *k <= 5 && regs_mask & (1 << *k) != 0) || (split_s && matches!(l, Loc::S(_)));
        // def ids: 0.. per statement def; entry pseudo-defs get ids too
        let mut defs: Vec<Loc> = vec![];
        let mut def_at: HashMap<(u16, usize), usize> = HashMap::new();
        let blocks: Vec<u16> = r.blocks.keys().cloned().collect();
        for &b in &blocks {
            if let Some(ss) = self.stmts.get(&b) {
                for (i, st) in ss.iter().enumerate() {
                    if let Some(d) = st_def(st) {
                        if splittable(&d) {
                            def_at.insert((b, i), defs.len());
                            defs.push(d);
                        }
                    }
                }
            }
        }
        let mut entry_def: HashMap<Loc, usize> = HashMap::new();
        let mut all_locs: HashSet<Loc> = HashSet::new();
        for ss in self.stmts.values() {
            for st in ss {
                st_uses(st, &mut all_locs);
                if let Some(d) = st_def(st) { all_locs.insert(d); }
            }
        }
        for e in self.bcond.values().chain(self.bcase.values()) { locs_in(e, &mut all_locs); }
        for per in self.bcond_pred.values() { for e in per.values() { locs_in(e, &mut all_locs); } }
        let mut locs: Vec<Loc> = all_locs.into_iter().filter(|l| splittable(l)).collect();
        locs.sort();
        for l in &locs {
            entry_def.insert(*l, defs.len());
            defs.push(*l);
        }
        let mut parent: Vec<usize> = (0..defs.len()).collect();
        fn find(p: &mut [usize], x: usize) -> usize {
            let mut x = x;
            while p[x] != x { p[x] = p[p[x]]; x = p[x]; }
            x
        }
        fn union(p: &mut [usize], a: usize, b: usize) {
            let (a, b) = (find(p, a), find(p, b));
            if a != b { p[a.max(b)] = a.min(b); }
        }
        type Rd = HashMap<Loc, BTreeSet<usize>>;
        let transfer = |b: u16, mut rd: Rd, stmts: &HashMap<u16, Vec<Stmt>>| -> Rd {
            if let Some(ss) = stmts.get(&b) {
                for (i, _st) in ss.iter().enumerate() {
                    if let Some(&id) = def_at.get(&(b, i)) {
                        let mut set = BTreeSet::new();
                        set.insert(id);
                        rd.insert(defs[id], set);
                    }
                }
            }
            rd
        };
        let mut inn: HashMap<u16, Rd> = HashMap::new();
        let mut e0: Rd = HashMap::new();
        for l in &locs { e0.insert(*l, [entry_def[l]].into_iter().collect()); }
        inn.insert(r.entry, e0);
        let mut work = vec![r.entry];
        while let Some(b) = work.pop() {
            let out = transfer(b, inn[&b].clone(), &self.stmts);
            if let Some(blk) = r.blocks.get(&b) {
                for (t, _) in &blk.succ {
                    let first = !inn.contains_key(t);
                    let tin = inn.entry(*t).or_default();
                    let mut ch = first;
                    for (l, ds) in &out {
                        let x = tin.entry(*l).or_default();
                        let n = x.len();
                        x.extend(ds.iter().cloned());
                        if x.len() != n { ch = true; }
                    }
                    if ch && !work.contains(t) { work.push(*t); }
                }
            }
        }
        // unions: every use joins the defs reaching it
        let mut use_web: HashMap<(u16, usize, Loc), usize> = HashMap::new();
        for &b in &blocks {
            let mut rd = match inn.get(&b) { Some(x) => x.clone(), None => continue };
            let join = |rd: &Rd, l: &Loc, parent: &mut Vec<usize>| -> Option<usize> {
                let ds = rd.get(l)?;
                let mut it = ds.iter();
                let f = *it.next()?;
                for &d in it { union(parent, f, d); }
                Some(f)
            };

            let n = self.stmts.get(&b).map(|x| x.len()).unwrap_or(0);
            for i in 0..n {
                let st = self.stmts[&b][i].clone();
                let mut u = HashSet::new();
                st_uses(&st, &mut u);
                for l in u.iter().filter(|l| splittable(l)) {
                    if let Some(f) = join(&rd, l, &mut parent) { use_web.insert((b, i, *l), f); }
                }
                if let Some(&id) = def_at.get(&(b, i)) {
                    let d = defs[id];
                    if u.contains(&d) {
                        if let Some(&f) = use_web.get(&(b, i, d)) { union(&mut parent, f, id); }
                    }
                    rd.insert(d, [id].into_iter().collect());
                }
            }
            let mut u = HashSet::new();
            if let Some(e) = self.bcond.get(&b) { locs_in(e, &mut u); }
            if let Some(e) = self.bcase.get(&b) { locs_in(e, &mut u); }
            for l in u.iter().filter(|l| splittable(l)) {
                if let Some(f) = join(&rd, l, &mut parent) { use_web.insert((b, usize::MAX, *l), f); }
            }
            for (t, _) in &r.blocks[&b].succ {
                if let Some(e) = self.bcond_pred.get(t).and_then(|per| per.get(&b)) {
                    let mut u = HashSet::new();
                    locs_in(e, &mut u);
                    for l in u.iter().filter(|l| splittable(l)) {
                        if let Some(f) = join(&rd, l, &mut parent) { use_web.insert((*t, usize::MAX - 1 - b as usize, *l), f); }
                    }
                }
            }
        }
        // names: per original loc, the web holding the entry def (or the first one met) keeps the name
        let mut name_of: HashMap<usize, Loc> = HashMap::new();
        let mut count: HashMap<Loc, i32> = HashMap::new();
        for l in &locs {
            let root = find(&mut parent, entry_def[l]);
            name_of.insert(root, *l);
            count.insert(*l, 1);
        }
        let mut order: Vec<usize> = def_at.values().cloned().collect();
        order.sort();
        let mut webname = |id: usize, parent: &mut Vec<usize>, name_of: &mut HashMap<usize, Loc>| -> Loc {
            let root = find(parent, id);
            if let Some(n) = name_of.get(&root) { return *n; }
            let base = defs[id];
            let w = count.entry(base).or_insert(0);
            let n = match base { Loc::R(k) => Loc::R(k + 8 * *w), Loc::S(k) => Loc::S(k + 1000 * *w), x => x };
            *w += 1;
            name_of.insert(root, n);
            n
        };
        for id in order { webname(id, &mut parent, &mut name_of); }
        let ren = |e: &E, b: u16, i: usize, parent: &mut Vec<usize>, name_of: &mut HashMap<usize, Loc>| -> E {
            let mut u = HashSet::new();
            locs_in(e, &mut u);
            let mut e = e.clone();
            for l in u.iter().filter(|l| splittable(l)) {
                if let Some(&f) = use_web.get(&(b, i, *l)) {
                    let root = find(parent, f);
                    if let Some(n) = name_of.get(&root) {
                        if n != l { e = subst(&e, *l, &E::Loc(*n)); }
                    }
                }
            }
            e
        };
        for &b in &blocks {
            let n = self.stmts.get(&b).map(|x| x.len()).unwrap_or(0);
            for i in 0..n {
                let st = self.stmts[&b][i].clone();
                let new = match &st {
                    Stmt::Set(pl, e) => {
                        let pl2 = match pl {
                            Place::Mem(a, by) => Place::Mem(ren(a, b, i, &mut parent, &mut name_of), *by),
                            Place::Loc(d) => match def_at.get(&(b, i)) {
                                Some(&id) => Place::Loc(webname(id, &mut parent, &mut name_of)),
                                None => Place::Loc(*d),
                            },
                        };
                        Stmt::Set(pl2, ren(e, b, i, &mut parent, &mut name_of))
                    }
                    Stmt::Do(e) => Stmt::Do(ren(e, b, i, &mut parent, &mut name_of)),
                    Stmt::Ret(e) => Stmt::Ret(ren(e, b, i, &mut parent, &mut name_of)),
                    x => x.clone(),
                };
                self.stmts.get_mut(&b).unwrap()[i] = new;
            }
            if let Some(e) = self.bcond.get(&b).cloned() {
                let e = ren(&e, b, usize::MAX, &mut parent, &mut name_of);
                self.bcond.insert(b, e);
            }
            if let Some(e) = self.bcase.get(&b).cloned() {
                let e = ren(&e, b, usize::MAX, &mut parent, &mut name_of);
                self.bcase.insert(b, e);
            }
            if let Some(per) = self.bcond_pred.get(&b).cloned() {
                let per2 = per.into_iter().map(|(p, e)| (p, ren(&e, b, usize::MAX - 1 - p as usize, &mut parent, &mut name_of))).collect();
                self.bcond_pred.insert(b, per2);
            }
        }
    }


    pub fn cleanup(&mut self, r: &Routine) -> Result<(), String> {
        self.copyprop(r)?;
        for _ in 0..4 {
            // what the branch conditions read, again each round: simplify_block folds statements
            // (a call, a copied temporary) into a condition, and their variables stay live there
            let mut cond_uses: HashMap<u16, HashSet<Loc>> = HashMap::new();
            for &b in r.blocks.keys() {
                let mut u = HashSet::new();
                if let Some(e) = self.bcond.get(&b) {
                    locs_in(e, &mut u);
                }
                if let Some(e) = self.bcase.get(&b) {
                    locs_in(e, &mut u);
                }
                // per-predecessor conditions of a successor are used on the edge out of this block
                for (t, _) in &r.blocks[&b].succ {
                    if let Some(e) = self.bcond_pred.get(t).and_then(|per| per.get(&b)) {
                        locs_in(e, &mut u);
                    }
                }
                cond_uses.insert(b, u);
            }
            let mut live_in: HashMap<u16, HashSet<Loc>> = r.blocks.keys().map(|&b| (b, HashSet::new())).collect();
            let mut changed = true;
            while changed {
                changed = false;
                for (&b, blk) in &r.blocks {
                    let mut l: HashSet<Loc> = HashSet::new();
                    for (t, _) in &blk.succ {
                        l.extend(live_in[t].iter().cloned());
                    }
                    l.extend(cond_uses[&b].iter().cloned());
                    for s in self.st(b)?.iter().rev() {
                        if let Some(d) = st_def(s) {
                            l.remove(&d);
                        }
                        st_uses(s, &mut l);
                    }
                    if l != live_in[&b] {
                        live_in.insert(b, l);
                        changed = true;
                    }
                }
            }
            self.live_out_nocond = HashMap::new();
            for (&b, blk) in &r.blocks {
                let mut lo: HashSet<Loc> = HashSet::new();
                for (t, _) in &blk.succ {
                    lo.extend(live_in[t].iter().cloned());
                }
                self.live_out_nocond.insert(b, lo.clone());
                lo.extend(cond_uses[&b].iter().cloned());
                let ss = self.simplify_block(b, &lo)?;
                self.stmts.insert(b, ss);
            }
        }
        // BIC #m,M / BIS V,M on the same memory place: one field-store expression
        for ss in self.stmts.values_mut() {
            let mut i = 0;
            while i + 1 < ss.len() {
                let merged = match (&ss[i], &ss[i + 1]) {
                    (Stmt::Set(p1 @ Place::Mem(a1, b1), E::Op("AND", k, m)), Stmt::Set(p2, E::Op("OR", k2, v)))
                        if p1 == p2 && matches!(**m, E::C(_)) && **k == E::Fetch(Rc::new(a1.clone()), *b1)
                            && **k2 == E::Fetch(Rc::new(a1.clone()), *b1) =>
                    {
                        Some(Stmt::Set(p1.clone(), op("OR", E::Op("AND", k.clone(), m.clone()), (**v).clone())))
                    }
                    _ => None,
                };
                if let Some(n) = merged {
                    ss[i] = n;
                    ss.remove(i + 1);
                }
                i += 1;
            }
        }
        if std::env::var("BLISSDC_NOWEBS").is_err() {
            self.split_webs(r);
        }
        Ok(())
    }


    pub(crate) fn simplify_block(&mut self, b: u16, live_out: &HashSet<Loc>) -> Result<Vec<Stmt>, String> {
        let ss = self.st(b)?.clone();
        let mut res = vec![];
        let mut live = live_out.clone();
        for s in ss.iter().rev() {
            let d = st_def(s);
            if let (Some(d), Stmt::Set(_, e)) = (d, s) {
                if d.is_rs() && !live.contains(&d) {
                    if has_call(e) {
                        let n = Stmt::Do(e.clone());
                        st_uses(&n, &mut live);
                        res.push(n);
                    }
                    continue;
                }
            }
            if let Some(d) = d {
                live.remove(&d);
            }
            st_uses(s, &mut live);
            res.push(s.clone());
        }
        res.reverse();
        let mut ss = res;
        'outer: loop {
            for i in 0..ss.len() {
                let (d, e) = match &ss[i] {
                    Stmt::Set(Place::Loc(d), e) if d.is_rs() => (*d, e.clone()),
                    _ => continue,
                };
                // knobs 18/19: keep register temporaries as statements (pinned, so the compiler
                // computes them where the ROM did) — 18: R1..R5, 19: R0
                if self.fin && ((knob(18) && matches!(d, Loc::R(k) if (1..=5).contains(&k)))
                    || (knob(19) && d == Loc::R(0))) {
                    continue;
                }
                let mut uses: Vec<(usize, usize)> = vec![];
                let mut j = i + 1;
                let mut redefined = false;
                while j < ss.len() {
                    let n = match &ss[j] {
                        Stmt::Set(pl, e2) => {
                            count_loc(e2, d) + if let Place::Mem(a, _) = pl { count_loc(a, d) } else { 0 }
                        }
                        Stmt::Do(e2) | Stmt::Ret(e2) => count_loc(e2, d),
                        _ => 0,
                    };
                    if n > 0 {
                        uses.push((j, n));
                    }
                    if st_def(&ss[j]) == Some(d) {
                        redefined = true;
                        break;
                    }
                    j += 1;
                }
                let mut end_use = 0;
                if !redefined {
                    if self.live_out_nocond.get(&b).map(|s| s.contains(&d)).unwrap_or(false) {
                        continue;
                    }
                    end_use = self.bcond.get(&b).map(|x| count_loc(x, d)).unwrap_or(0)
                        + self.bcase.get(&b).map(|x| count_loc(x, d)).unwrap_or(0);
                }
                let total: usize = uses.iter().map(|u| u.1).sum::<usize>() + end_use;
                if total != 1 {
                    continue;
                }
                if depth(&e) > 24 {
                    continue;
                }
                let k = if uses.is_empty() { ss.len() } else { uses[0].0 };
                let mut ok = true;
                let mut reads = HashSet::new();
                locs_in(&e, &mut reads);
                let (mr, hc) = (is_mem_read(&e), has_call(&e));
                for s in &ss[i + 1..k] {
                    if let Some(dd) = st_def(s) {
                        if reads.contains(&dd) {
                            ok = false;
                        }
                    }
                    if mr && st_store(s) {
                        ok = false;
                    }
                    if hc && (st_store(s) || matches!(s, Stmt::Do(_))) {
                        ok = false;
                    }
                }
                if !ok {
                    continue;
                }
                if !uses.is_empty() {
                    let new = match &ss[k] {
                        Stmt::Set(tgt, e2) => {
                            let tgt = match tgt {
                                Place::Mem(a, by) => Place::Mem(subst(a, d, &e), *by),
                                t => t.clone(),
                            };
                            Stmt::Set(tgt, subst(e2, d, &e))
                        }
                        Stmt::Do(e2) => Stmt::Do(subst(e2, d, &e)),
                        Stmt::Ret(e2) => Stmt::Ret(subst(e2, d, &e)),
                        s => s.clone(),
                    };
                    ss[k] = new;
                } else {
                    if let Some(x) = self.bcond.get(&b) {
                        let x = subst(x, d, &e);
                        self.bcond.insert(b, x);
                    }
                    if let Some(x) = self.bcase.get(&b) {
                        let x = subst(x, d, &e);
                        self.bcase.insert(b, x);
                    }
                }
                ss.remove(i);
                continue 'outer;
            }
            break;
        }
        Ok(ss)
    }
}
