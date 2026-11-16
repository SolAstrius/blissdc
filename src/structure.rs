// SPDX-License-Identifier: Apache-2.0
//! Structuring (CFG -> BEGIN/IF/CASE/loops) and expression printing.
use crate::ir::*;
use crate::cfg::*;
use crate::lift::*;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

// ------------------------------------------------------------------ printing
pub(crate) fn prec_of(s: &str) -> i32 {
    match s {
        "OR" | "XOR" => 1,
        "AND" => 2,
        "+" | "-" => 4,
        "*" => 5,
        "^" => 6,
        _ => 3,
    }
}

pub(crate) fn contiguous(m: u16) -> Option<(i32, i32)> {
    if m == 0 {
        return None;
    }
    let p = m.trailing_zeros();
    let hi = (m >> p) as u32;
    let s = 32 - hi.leading_zeros();
    if hi == (1u32 << s) - 1 { Some((p as i32, s as i32)) } else { None }
}

pub(crate) fn shift_of(e: &E) -> (E, i32, Option<i32>) {
    let mut e = e.clone();
    let mut k = 0;
    let mut ksw: Option<i32> = None;
    loop {
        let next = match &e {
            E::Op("^", a, b) if matches!(**b, E::C(_)) => {
                if let E::C(v) = **b {
                    k += sgn(v);
                }
                (**a).clone()
            }
            E::Swab(a) if ksw.is_none() => {
                ksw = Some(k);
                (**a).clone()
            }
            _ => break,
        };
        e = next;
    }
    (e, k, ksw)
}

/// (base shifted) AND mask -> (base, pos, size, scale)
pub(crate) fn field_read(e: &E) -> Option<(E, i32, i32, i32)> {
    let (inner, mask) = match e {
        E::Op("AND", a, b) => match **b {
            E::C(m) => (a, m),
            _ => return None,
        },
        _ => return None,
    };
    let (p, s) = contiguous(mask)?;
    let (base, k, ksw) = shift_of(inner);
    match ksw {
        None => {
            if k == 0 {
                return if p == 0 && s == 16 { None } else { Some((base, p, s, 0)) };
            }
            if k < 0 {
                return Some((base, p - k, s, p));
            }
            if k > 0 && p >= k {
                return Some((base, p - k, s, p));
            }
            None
        }
        Some(after) => {
            let before = k - after;
            if before != 0 {
                return None;
            }
            if after >= 0 && p - after >= 8 {
                return Some((base, p - after - 8, s, p));
            }
            if after <= 0 && p - after + s <= 8 {
                return Some((base, p - after + 8, s, p));
            }
            None
        }
    }
}

pub(crate) struct Printer {
    pub(crate) maxparam: i32,
    pub(crate) globals: BTreeSet<u16>,
    pub(crate) externals: BTreeSet<String>,
    pub(crate) vectors: BTreeSet<u16>,
}

impl Printer {
    fn pname(&self, l: Loc) -> String {
        match l {
            Loc::P(k) => format!("A{}", self.maxparam - k),
            Loc::S(k) | Loc::M(k) if k >= 1000 => format!("L{}_{}", k % 1000, k / 1000),
            Loc::S(k) | Loc::M(k) => format!("L{}", k),
            Loc::Q(k) if k >= 10 => format!("GR{}", k - 10),
            Loc::Q(k) => format!("PR{}", k),
            Loc::R(k) if k >= 8 => format!("X{}_{}", k % 8, k / 8),
            Loc::R(k) => format!("X{}", k),
        }
    }

    fn gname(&mut self, a: u16) -> String {
        self.globals.insert(a);
        gsym(a)
    }

    fn e(&mut self, x: &E, prec: i32) -> String {
        match x {
            E::C(v) => {
                let s = sgn(*v);
                if -1000 < s && s < 1000 { format!("{}", s) } else { format!("%O'{:o}'", v) }
            }
            E::Loc(l) => format!(".{}", self.pname(*l)),
            // address of a frame slot: in BLISS the bare name is the address
            E::Frame(o) => {
                // an odd offset is the high byte of the word below it: (slot + 1)
                let (w, hi) = (*o & !1, *o & 1 != 0);
                let nm = if w >= 2 { self.pname(Loc::P((w - 2) / 2)) } else { self.pname(Loc::M(-w)) };
                if hi { format!("({} + 1)", nm) } else { nm }
            }
            E::G(a) => self.gname(*a),
            // mask kept in place (no shift): a plain AND, not a field extraction
            E::Op("AND", a, m) if matches!(**m, E::C(_)) && matches!(field_read(x), Some((_, p, _, 0)) if p > 0)
                && !matches!(**a, E::Op("^", ..) | E::Swab(_)) => {
                let s = format!("{} AND {}", self.e(a, 3), self.e(m, 3));
                if prec > 2 { format!("({})", s) } else { s }
            }
            E::Op("AND", ..) if field_read(x).is_some() => {
                let (base, pos, size, scale) = field_read(x).unwrap();
                let s = match &base {
                    E::Loc(l) => format!(".{}<{},{}>", self.pname(*l), pos, size),
                    E::Fetch(a, false) => format!(".{}<{},{}>", self.addr(a), pos, size),
                    E::Fetch(a, true) if pos + size <= 8 => format!(".{}<{},{}>", self.addr(a), pos, size),
                    _ => format!("(({} ^ {}) AND {})", self.e(&base, 6), -pos, (1i64 << size) - 1),
                };
                if scale != 0 {
                    let s = format!("{} * {}", s, 1i64 << scale);
                    return if prec > 5 { format!("({})", s) } else { s };
                }
                s
            }
            E::Fetch(a, byte) => {
                if !*byte {
                    if let Some(v) = self.vec(a) {
                        return v;
                    }
                }
                if *byte {
                    // a byte of a stack word: a field of that local (BLISS compiles .L<0,8> / .L<8,8>
                    // to BISB (SP) / BISB 1(SP))
                    if let Some((nm, pos)) = self.frame_byte(a) {
                        return format!(".{}<{},8>", nm, pos);
                    }
                }
                let s = format!(".{}", self.addr(a));
                if *byte { s + "<0,8>" } else { s }
            }
            // MOVB load: sign-extended byte
            E::Ext8(a) => match &**a {
                E::Fetch(ad, true) if self.frame_byte(ad).is_some() => {
                    let (nm, pos) = self.frame_byte(ad).unwrap();
                    format!(".{}<{},8,1>", nm, pos)
                }
                E::Fetch(ad, true) => format!(".{}<0,8,1>", self.addr(ad)),
                // MOVB R1,R0: the register's low byte, sign-extended
                E::Loc(l) => format!(".{}<0,8,1>", self.pname(*l)),
                // CLRB R0 / SWAB R0 / MOVB R0,R0 (with or without the CLRB): the high byte, sign-extended
                E::Swab(x) if matches!(hi_word(x), E::Loc(_) | E::Fetch(_, false)) => match hi_word(x) {
                    E::Loc(l) => format!(".{}<8,8,1>", self.pname(*l)),
                    E::Fetch(ad, _) => format!(".{}<8,8,1>", self.addr(ad)),
                    _ => unreachable!(),
                },
                E::Fetch(..) => self.e(a, prec),
                // any other value: the low byte, less 256 when bit 7 is set
                _ => {
                    let x = self.e(a, 9);
                    let s = format!("({} AND 255) - (({} AND 128) ^ 1)", x, x);
                    if prec > 0 { format!("({})", s) } else { s }
                }
            },
            // (0 AND m) OR x, 0 OR x: the cleared word with a byte merged in
            E::Op("OR", a, b) if matches!(**a, E::C(0)) || matches!(&**a, E::Op("AND", z, _) if matches!(**z, E::C(0))) => self.e(b, prec),
            E::Call(n, args) => {
                self.externals.insert(n.to_string());
                let a: Vec<String> = args.iter().map(|a| self.e(a, 0)).collect();
                format!("{} ({})", n, a.join(", "))
            }
            // SWAB: the two bytes exchanged (x ^ 8 alone is a left shift: the low byte would be 0)
            E::Swab(a) if matches!(**a, E::C(_)) => {
                let v = match **a { E::C(v) => v, _ => 0 };
                self.e(&E::C(v.rotate_left(8)), prec)
            }
            E::Swab(a) => {
                let x = self.e(a, 6);
                format!("(({} ^ 8) OR ({} ^ -8))", x, x)
            }
            E::Rel("LOW", a, _) => self.e(a, prec.max(4)),
            E::Rel("NLOW", a, _) => {
                let s = format!("NOT {}", self.e(a, 7));
                if prec > 3 { format!("({})", s) } else { s }
            }
            E::Rel(r, a, b) => {
                // readable: printable constants in comparisons as characters
                if READABLE.with(|x| x.get()) {
                    if let E::C(v) = **b {
                        if (0x21..0x7f).contains(&v) {
                            let ch = v as u8 as char;
                            let lit = if ch == '\'' { String::from("%C''''") } else { format!("%C'{}'", ch) };
                            let s = format!("{} {} {}", self.e(a, 4), r, lit);
                            return if prec > 3 { format!("({})", s) } else { s };
                        }
                    }
                }
                let s = format!("{} {} {}", self.e(a, 4), r, self.e(b, 4));
                if prec > 3 { format!("({})", s) } else { s }
            }
            E::Un(s, a) => {
                if *s == "NOT" {
                    format!("NOT {}", self.e(a, 7))
                } else {
                    format!("-{}", self.e(a, 7))
                }
            }
            E::Op(o, a, b) => {
                let p = prec_of(o);
                let s = format!("{} {} {}", self.e(a, p), o, self.e(b, p + 1));
                if prec > p { format!("({})", s) } else { s }
            }
            _ => {
                let s = pyrepr(x).replace('%', "").replace(")%", ") %");
                let s: String = s.chars().take(60).collect();
                format!("0 %( ?? {} )%", s)
            }
        }
    }

    /// a = (i ^ 1) + base -> BASE[i]
    fn vec(&mut self, a: &E) -> Option<String> {
        if let E::Op("+", l, r) = a {
            let base = match **r {
                E::C(v) | E::G(v) => v,
                _ => return None,
            };
            if let E::Op("^", idx, sh) = &**l {
                if **sh == E::C(1) {
                    self.vectors.insert(base);
                    return Some(format!(".{}[{}]", self.gname(base), self.e(idx, 0)));
                }
            }
        }
        None
    }

    fn cond(&mut self, cnd: &E, prec: i32) -> String {
        match cnd {
            E::And(a, b) => {
                let s = format!("{} AND {}", self.cond(a, 2), self.cond(b, 2));
                if prec > 2 { format!("({})", s) } else { s }
            }
            E::Or(a, b) => {
                let s = format!("{} OR {}", self.cond(a, 1), self.cond(b, 1));
                if prec > 1 { format!("({})", s) } else { s }
            }
            E::Not(a) => format!("NOT ({})", self.cond(a, 0)),
            _ => self.e(cnd, if prec != 0 { prec.max(3) } else { 0 }),
        }
    }

    fn addr(&mut self, a: &E) -> String {
        if let Some(v) = self.vec(a) {
            return v[1..].to_string();
        }
        match a {
            E::G(v) => self.gname(*v),
            E::Loc(l) => format!("(.{})", self.pname(*l)),
            _ => format!("({})", self.e(a, 0)),
        }
    }

    /// a byte address inside a stack word: (that local's name, bit position 0 or 8)
    fn frame_byte(&mut self, a: &E) -> Option<(String, i32)> {
        let o = match a {
            E::Frame(o) => *o,
            E::Op("+", f, k) => match (&**f, &**k) { (E::Frame(o), E::C(1)) => *o + 1, _ => return None },
            _ => return None,
        };
        let w = o & !1;
        let nm = if w >= 2 { self.pname(Loc::P((w - 2) / 2)) } else { self.pname(Loc::M(-w)) };
        Some((nm, 8 * (o & 1)))
    }

    fn place(&mut self, p: &Place) -> String {
        match p {
            Place::Loc(l) => self.pname(*l),
            Place::Mem(a, true) if self.frame_byte(a).is_some() => {
                let (nm, pos) = self.frame_byte(a).unwrap();
                format!("{}<{},8>", nm, pos)
            }
            Place::Mem(a, byte) => {
                let s = self.addr(a);
                if *byte { s + "<0,8>" } else { s }
            }
        }
    }
}

// ------------------------------------------------------------------ structuring
pub(crate) const EXIT: u32 = 0x10000;

pub(crate) fn postdoms(blocks: &BTreeMap<u16, Block>, back: &HashSet<(u16, u16)>) -> HashMap<u16, u32> {
    let keys: Vec<u16> = blocks.keys().cloned().collect();
    let n = keys.len();
    let idx: HashMap<u16, usize> = keys.iter().enumerate().map(|(i, &k)| (k, i)).collect();
    let words = (n + 1).div_ceil(64);
    let succ: Vec<Vec<usize>> = keys
        .iter()
        .map(|k| {
            // back edges go to the virtual exit: joins inside loop bodies become visible
            let mut s: Vec<usize> = blocks[k].succ.iter()
                .map(|(t, _)| if back.contains(&(*k, *t)) { n } else { idx[t] }).collect();
            s.dedup();
            if s.is_empty() { vec![n] } else { s }
        })
        .collect();
    let mut full = vec![!0u64; words];
    let extra = words * 64 - (n + 1);
    if extra > 0 {
        full[words - 1] >>= extra;
    }
    let mut pd: Vec<Vec<u64>> = vec![full; n + 1];
    pd[n] = vec![0u64; words];
    pd[n][n / 64] |= 1 << (n % 64);
    let mut changed = true;
    while changed {
        changed = false;
        for i in 0..n {
            let mut new = pd[succ[i][0]].clone();
            for &t in &succ[i][1..] {
                for w in 0..words {
                    new[w] &= pd[t][w];
                }
            }
            new[i / 64] |= 1 << (i % 64);
            if new != pd[i] {
                pd[i] = new;
                changed = true;
            }
        }
    }
    let mut ipd = HashMap::new();
    for i in 0..n {
        let mut cands = pd[i].clone();
        cands[i / 64] &= !(1 << (i % 64));
        for cnd in 0..=n {
            if cands[cnd / 64] >> (cnd % 64) & 1 == 0 {
                continue;
            }
            if (0..words).all(|w| cands[w] & !pd[cnd][w] == 0) {
                ipd.insert(keys[i], if cnd == n { EXIT } else { keys[cnd] as u32 });
                break;
            }
        }
    }
    ipd
}

pub(crate) fn bad_cond(e: Option<&E>) -> bool {
    match e {
        None => true,
        Some(e) => is_unk(e, "?cc") || is_unk(e, "perpred") || is_unk(e, "?"),
    }
}

pub(crate) fn succ_kind(b: &Block, k: Kind) -> Result<u16, String> {
    b.succ.iter().find(|(_, kk)| *kk == k).map(|(t, _)| *t).ok_or_else(|| "IndexError: list index out of range".to_string())
}

/// Merge short-circuit branch pairs.
pub(crate) fn combine_conditions(r: &mut Routine, l: &mut Lifter) -> Result<(), String> {
    loop {
        let mut changed = false;
        let mut preds: HashMap<u16, BTreeSet<u16>> = HashMap::new();
        for (&p, blk) in &r.blocks {
            for &(t, _) in &blk.succ {
                preds.entry(t).or_default().insert(p);
            }
        }
        let keys: Vec<u16> = r.blocks.keys().cloned().collect();
        for a in keys {
            let ablk = &r.blocks[&a];
            if ablk.term != Term::Cond || bad_cond(l.bcond.get(&a)) {
                continue;
            }
            let ta = succ_kind(ablk, Kind::T)?;
            let fa = succ_kind(ablk, Kind::F)?;
            let ca = l.bcond[&a].clone();
            for (bb, x, z) in [(ta, ca.clone(), fa), (fa, negate(&ca), ta)] {
                if bb == a || !r.blocks.contains_key(&bb) {
                    continue;
                }
                let bblk = &r.blocks[&bb];
                let only_a = preds.get(&bb).map(|s| s.len() == 1 && s.contains(&a)).unwrap_or(false);
                if bblk.term != Term::Cond || l.stmts.get(&bb).map(|s| !s.is_empty()).unwrap_or(false) || !only_a {
                    continue;
                }
                if bad_cond(l.bcond.get(&bb)) {
                    continue;
                }
                let cb = l.bcond[&bb].clone();
                let tb = succ_kind(bblk, Kind::T)?;
                let fb = succ_kind(bblk, Kind::F)?;
                if (z != tb && z != fb) || tb == fb {
                    continue;
                }
                let y = if tb == z { cb } else { negate(&cb) };
                let w = if tb == z { fb } else { tb };
                l.bcond.insert(a, negate(&E::And(Rc::new(x), Rc::new(negate(&y)))));
                r.blocks.get_mut(&a).unwrap().succ = vec![(z, Kind::T), (w, Kind::F)];
                r.blocks.remove(&bb);
                changed = true;
                break;
            }
            if changed {
                break;
            }
        }
        if !changed {
            return Ok(());
        }
    }
}

#[derive(Clone)]
pub(crate) struct LoopCtx {
    head: u16,
    body: Rc<HashSet<u16>>,
    follow: Option<u16>,
    id: usize,
}

pub(crate) const MAX_DEPTH: usize = 300_000;

pub(crate) struct Structurer<'a> {
    r: &'a Routine,
    l: &'a Lifter,
    pub(crate) p: Printer,
    ipd: HashMap<u16, u32>,
    loopheads: HashMap<u16, Rc<HashSet<u16>>>,
    pub(crate) out: Vec<(usize, String)>,
    prev: Option<u16>,
    rd: usize,
    trace: Vec<(char, u16, u16)>,
    lstack: Vec<Rc<LoopCtx>>,
    /// blocks emitted after an enclosing labelled block (knob 23): reaching one = LEAVE that label
    exits: Vec<(u16, String)>,
    in_merge: HashSet<u16>,
    back: HashSet<(u16, u16)>,
    open_all: Vec<u16>,
    next_id: usize,
    pub labels: BTreeSet<String>,
    pub unstructured: bool,
}

pub(crate) fn stmt_repr(s: &str) -> String {
    if s.contains('\'') && !s.contains('"') {
        format!("('?', \"{}\")", s)
    } else {
        format!("('?', '{}')", s)
    }
}

impl<'a> Structurer<'a> {
    pub(crate) fn new(r: &'a Routine, l: &'a Lifter, p: Printer) -> Structurer<'a> {
        let mut s = Structurer {
            r, l, p, ipd: HashMap::new(), loopheads: HashMap::new(), back: HashSet::new(), out: vec![], prev: None, rd: 0, trace: vec![],
            lstack: vec![], exits: vec![], in_merge: HashSet::new(), open_all: vec![], next_id: 1, labels: BTreeSet::new(), unstructured: false,
        };
        s.find_loops();
        s.ipd = postdoms(&r.blocks, &s.back);
        s
    }

    fn find_loops(&mut self) {
        let blocks = &self.r.blocks;
        // reverse postorder from entry
        let mut order: Vec<u16> = vec![];
        let mut seen: HashSet<u16> = HashSet::new();
        let mut st: Vec<(u16, usize)> = vec![(self.r.entry, 0)];
        seen.insert(self.r.entry);
        while let Some(&(n, i)) = st.last() {
            let succ = &blocks[&n].succ;
            if i < succ.len() {
                st.last_mut().unwrap().1 += 1;
                let t = succ[i].0;
                if blocks.contains_key(&t) && seen.insert(t) {
                    st.push((t, 0));
                }
            } else {
                order.push(n);
                st.pop();
            }
        }
        order.reverse();
        let idx: HashMap<u16, usize> = order.iter().enumerate().map(|(i, &n)| (n, i)).collect();
        let mut preds: HashMap<u16, BTreeSet<u16>> = HashMap::new();
        for (&b, blk) in blocks {
            for &(t, _) in &blk.succ {
                preds.entry(t).or_default().insert(b);
            }
        }
        // Cooper-Harvey-Kennedy immediate dominators
        let mut idom: HashMap<u16, u16> = HashMap::new();
        idom.insert(self.r.entry, self.r.entry);
        let mut changed = true;
        while changed {
            changed = false;
            for &n in order.iter().skip(1) {
                let mut new: Option<u16> = None;
                for &p in preds.get(&n).map(|x| x.iter().cloned().collect::<Vec<_>>()).unwrap_or_default().iter() {
                    if !idom.contains_key(&p) {
                        continue;
                    }
                    new = Some(match new {
                        None => p,
                        Some(mut a) => {
                            let mut b = p;
                            while a != b {
                                while idx[&a] > idx[&b] { a = idom[&a]; }
                                while idx[&b] > idx[&a] { b = idom[&b]; }
                            }
                            a
                        }
                    });
                }
                if let Some(d) = new {
                    if idom.get(&n) != Some(&d) {
                        idom.insert(n, d);
                        changed = true;
                    }
                }
            }
        }
        let dominates = |h: u16, mut n: u16| -> bool {
            loop {
                if n == h { return true; }
                match idom.get(&n) {
                    Some(&d) if d != n => n = d,
                    _ => return false,
                }
            }
        };
        let mut back: Vec<(u16, u16)> = vec![];
        for &n in &order {
            for &(t, _) in &blocks[&n].succ {
                if idx.contains_key(&t) && dominates(t, n) {
                    back.push((n, t));
                }
            }
        }
        // irreducible cycles (a loop entered in two places, e.g. a branch cross-jumped into its test):
        // a retreating edge of the depth-first order that no dominator explains still closes a loop
        let backset: HashSet<(u16, u16)> = back.iter().cloned().collect();
        for &n in &order {
            for &(t, _) in &blocks[&n].succ {
                if let (Some(&it), Some(&inn)) = (idx.get(&t), idx.get(&n)) {
                    if it <= inn && !backset.contains(&(n, t)) {
                        back.push((n, t));
                    }
                }
            }
        }
        let mut heads: HashMap<u16, HashSet<u16>> = HashMap::new();
        self.back = back.iter().cloned().collect();
        for (n, h) in back {
            let mut body: HashSet<u16> = HashSet::new();
            body.insert(h);
            let mut st = vec![n];
            let hi = idx[&h];
            while let Some(x) = st.pop() {
                if body.insert(x) {
                    if let Some(ps) = preds.get(&x) {
                        // the loop body lies after its header in depth-first order
                        st.extend(ps.iter().cloned().filter(|p| idx.get(p).map(|&i| i >= hi).unwrap_or(false)));
                    }
                }
            }
            heads.entry(h).or_default().extend(body);
        }
        self.loopheads = heads.into_iter().map(|(k, v)| (k, Rc::new(v))).collect();
    }

    /// lone BIC #m / BIS #m on a memory place: one field store per run of bits (the compiler merges
    /// them back into one BICB/BISB, as the ROM has it)
    fn mem_bit_stores(&self, pl: &Place, e: &E) -> Option<Vec<(i32, i32, i64)>> {
        let (addr, byte) = match pl { Place::Mem(a, b) => (a, *b), _ => return None };
        if !byte { return None; }   // words: .P AND m already compiles to a direct BIC
        let width = if byte { 8 } else { 16 };
        let wm: u32 = (1u32 << width) - 1;
        let (bits, set) = match e {
            E::Op("AND", k, m) if **k == E::Fetch(Rc::new(addr.clone()), byte) => match **m { E::C(v) => (!(v as u32) & wm, false), _ => return None },
            E::Op("OR", k, m) if **k == E::Fetch(Rc::new(addr.clone()), byte) => match **m { E::C(v) => ((v as u32) & wm, true), _ => return None },
            _ => return None,
        };
        if bits == 0 { return None; }
        let mut runs = vec![];
        let mut p = 0;
        while p < width {
            if bits & (1 << p) != 0 {
                let mut q = p;
                while q < width && bits & (1 << q) != 0 { q += 1; }
                let s = q - p;
                if knob(27) {   // knob 27: whole runs; default one field per bit
                    runs.push((p, s, if set { (1i64 << s) - 1 } else { 0 }));
                } else {
                    for b in p..q { runs.push((b, 1, if set { 1 } else { 0 })); }
                }
                p = q;
            } else { p += 1; }
        }
        Some(runs)
    }

    /// P = (.P AND NOT mask) OR value-in-mask  ->  P<pos,size> = value  (memory places)
    fn mem_field_store(&self, pl: &Place, e: &E) -> Option<(i32, i32, E)> {
        let (addr, byte) = match pl { Place::Mem(a, b) => (a, *b), _ => return None };
        let width_mask: u16 = if byte { 0o377 } else { 0o177777 };
        // lone BIC #m / BIS #m on the place: P<p,s> = 0, P<p,1> = 1
        match e {
            E::Op("AND", k, m) if matches!(**m, E::C(_)) && **k == E::Fetch(Rc::new(addr.clone()), byte) => {
                if let E::C(mv) = **m {
                    let cm = contiguous(!mv & width_mask)?;
                    return Some((cm.0, cm.1, c(0)));
                }
            }
            E::Op("OR", k, m) if matches!(**m, E::C(_)) && **k == E::Fetch(Rc::new(addr.clone()), byte) => {
                if let E::C(mv) = **m {
                    let cm = contiguous(mv & width_mask)?;
                    if cm.1 == 1 { return Some((cm.0, 1, c(1))); }
                    return None;
                }
            }
            _ => {}
        }
        let (a, b) = match e {
            E::Op("OR", a, b) => (a, b),
            _ => return None,
        };
        for (keep, ins) in [(a, b), (b, a)] {
            if let E::Op("AND", kl, km) = &**keep {
                if let (E::Fetch(fa, fb), E::C(m)) = (&**kl, &**km) {
                    if **fa != *addr || *fb != byte { continue; }
                    let width = if byte { 8 } else { 16 };
                    let inv = !*m & if byte { 0o377 } else { 0o177777 };
                    let cm = contiguous(inv)?;
                    if cm.0 + cm.1 > width { return None; }
                    if let Some((base, pos, size, scale)) = field_read(ins) {
                        if (scale, size) == cm {
                            let val = if pos == 0 { base } else { op("AND", op("^", base, c(-pos)), c(((1i64 << size) - 1) as i32)) };
                            return Some((cm.0, cm.1, val));
                        }
                    }
                }
            }
        }
        None
    }

    fn field_store(&self, e: &E) -> Option<(Loc, i32, i32, E)> {
        let (a, b) = match e {
            E::Op("OR", a, b) => (a, b),
            _ => return None,
        };
        for (keep, ins) in [(a, b), (b, a)] {
            if let E::Op("AND", kl, km) = &**keep {
                if let (E::Loc(loc), E::C(m)) = (&**kl, &**km) {
                    let cm = contiguous(!*m);
                    let f = field_read(ins);
                    if let (Some(cm), Some((base, pos, size, scale))) = (cm, f) {
                        if (scale, size) == cm {
                            let val = if pos == 0 {
                                base
                            } else {
                                op("AND", op("^", base, c(-pos)), c(((1i64 << size) - 1) as i32))
                            };
                            return Some((*loc, cm.0, cm.1, val));
                        }
                    }
                }
            }
        }
        None
    }

    fn emit(&mut self, ind: usize, s: String) {
        self.out.push((ind, s));
    }

    fn stmts(&mut self, bpc: u16, ind: usize) {
        let l = self.l;
        let ss = match l.stmts.get(&bpc) {
            Some(s) => s,
            None => return,
        };
        for s in ss {
            match s {
                Stmt::Set(pl, e) => {
                    // a byte store of a swapped word takes its low byte: the word's high byte
                    if let (Place::Mem(_, true), E::Swab(x)) = (pl, e) {
                        if !matches!(**x, E::C(_)) {
                            let t = format!("{} = ({} ^ -8);", self.p.place(pl), self.p.e(x, 6));
                            self.emit(ind, t);
                            continue;
                        }
                    }
                    if let Some(runs) = self.mem_bit_stores(pl, e) {
                        let a = match pl { Place::Mem(a, _) => a.clone(), _ => unreachable!() };
                        for (pos, size, v) in runs {
                            let t = format!("{}<{},{}> = {};", self.p.addr(&a), pos, size, v);
                            self.emit(ind, t);
                        }
                        continue;
                    }
                    if let Some((pos, size, val)) = self.mem_field_store(pl, e) {
                        let a = match pl { Place::Mem(a, _) => a.clone(), _ => unreachable!() };
                        let t = format!("{}<{},{}> = {};", self.p.addr(&a), pos, size, self.p.e(&val, 0));
                        self.emit(ind, t);
                        continue;
                    }
                    if let E::Op(..) = e {
                        if let Some((loc, pos, size, val)) = self.field_store(e) {
                            let t = format!("{}<{},{}> = {};", self.p.pname(loc), pos, size, self.p.e(&val, 0));
                            self.emit(ind, t);
                            if *pl != Place::Loc(loc) {
                                let t = format!("{} = .{};", self.p.place(pl), self.p.pname(loc));
                                self.emit(ind, t);
                            }
                            continue;
                        }
                    }
                    let t = format!("{} = {};", self.p.place(pl), self.p.e(e, 0));
                    self.emit(ind, t);
                }
                Stmt::Tail(n) => self.emit(ind, format!("RETURN {} ();", n)),
                Stmt::Do(e) => {
                    let t = format!("{};", self.p.e(e, 0));
                    self.emit(ind, t);
                }
                Stmt::Ret(_) => {}
                Stmt::Unk(t) => self.emit(ind, format!("! ?? {}", stmt_repr(t))),
                Stmt::Post(..) => {}
            }
        }
    }

    /// Innermost frames of the runaway seq/block recursion: kind:block/loop-head.
    fn rec_err(&self) -> String {
        let t: Vec<String> = self.trace[self.trace.len().saturating_sub(16)..]
            .iter()
            .map(|(k, n, h)| format!("{}:{}/{}", k, o6(*n), o6(*h)))
            .collect();
        format!("RecursionError: maximum recursion depth exceeded; innermost frames (seq|block:node/loophead) {}", t.join(" "))
    }

    pub(crate) fn run(&mut self) -> Result<(), String> {
        self.seq(Some(self.r.entry), None, 1, None, None)
    }

    fn blk(&self, n: u16) -> Result<&'a Block, String> {
        self.r.blocks.get(&n).ok_or_else(|| format!("KeyError: {}", n))
    }

    fn seq(&mut self, n: Option<u16>, stop: Option<u16>, ind: usize, lp: Option<&LoopCtx>, prev: Option<u16>)
           -> Result<(), String> {
        self.rd += 1;
        self.trace.push(('s', n.unwrap_or(0), lp.map(|x| x.head).unwrap_or(0)));
        if self.rd > MAX_DEPTH {
            return Err(self.rec_err());
        }
        let r = self.seq_inner(n, stop, ind, lp, prev);
        self.rd -= 1;
        self.trace.pop();
        r
    }

    fn seq_inner(&mut self, mut n: Option<u16>, stop: Option<u16>, ind: usize, _lp: Option<&LoopCtx>, prev: Option<u16>)
                 -> Result<(), String> {
        let mut guard = 0;
        self.prev = prev;
        while let Some(nn) = n {
            if n == stop || guard >= 2000 {
                break;
            }
            guard += 1;
            // a shared block emitted after an enclosing labelled block: jump there = LEAVE it
            if let Some((_, lab)) = self.exits.iter().rev().find(|(b, _)| *b == nn) {
                let lab = lab.clone();
                self.labels.insert(lab.clone());
                self.emit(ind, format!("LEAVE {};", lab));
                return Ok(());
            }
            // back to the header of an open loop: next iteration of that loop
            if let Some(k) = self.lstack.iter().rposition(|c| c.head == nn) {
                let id = self.lstack[k].id;
                let lab = format!("NEXT{}", id);
                self.labels.insert(lab.clone());
                self.emit(ind, format!("LEAVE {};", lab));
                return Ok(());
            }
            if let Some(inner) = self.lstack.last().cloned() {
                if !inner.body.contains(&nn) {
                    // exit to the follow of some enclosing loop
                    if let Some(k) = self.lstack.iter().rposition(|c| c.follow == Some(nn)) {
                        let lab = format!("LOOP{}", self.lstack[k].id);
                        self.labels.insert(lab.clone());
                        self.emit(ind, format!("LEAVE {};", lab));
                        return Ok(());
                    }
                    // continue inside an enclosing loop's body: inline that code in its context
                    let m = self.lstack.iter().rposition(|c| c.body.contains(&nn));
                    let cut = m.map(|m| m + 1).unwrap_or(0);
                    let saved = self.lstack.split_off(cut);
                    let pv = self.prev;
                    let follow0 = if cut == 0 { saved.first().and_then(|c| c.follow) } else { None };
                    let res = self.seq(Some(nn), follow0, ind, None, pv);
                    let outer_id = saved.first().map(|c| c.id);
                    self.lstack.extend(saved);
                    res?;
                    if cut == 0 {
                        if let Some(id) = outer_id {
                            let lab = format!("LOOP{}", id);
                            self.labels.insert(lab.clone());
                            self.emit(ind, format!("LEAVE {};", lab));
                        }
                    }
                    return Ok(());
                }
            }
            if self.loopheads.contains_key(&nn) {
                if self.open_all.contains(&nn) {
                    // header open further up but hidden by inlining: not expressible without GOTO
                    self.unstructured = true;
                    self.emit(ind, format!("! ?? GOTO {:06o} (irreducible flow)", nn));
                    return Ok(());
                }
                let body = self.loopheads[&nn].clone();
                let mut exits: BTreeSet<u16> = BTreeSet::new();
                for &b in body.iter() {
                    for &(t, _) in &self.blk(b)?.succ {
                        if !body.contains(&t) {
                            exits.insert(t);
                        }
                    }
                }
                let mut follow: Option<u16> = match self.ipd.get(&nn) {
                    Some(&f) if f != EXIT => Some(f as u16),
                    _ => None,
                };
                if follow.map(|f| !exits.contains(&f)).unwrap_or(true) {
                    follow = exits.iter().next().cloned();
                }
                // the code after the loop is entered by one exit edge and only returns: it was
                // written inside the loop at that exit (BLISS placed it there)
                if knob(10) && self.lstack.is_empty() {
                    if let Some(f) = follow {
                        let mut edges = 0;
                        for &b in body.iter() {
                            // one edge per predecessor block (a CASE table may list the same target twice)
                            if self.blk(b)?.succ.iter().any(|&(t, _)| t == f) { edges += 1; }
                        }
                        let mut seen: HashSet<u16> = HashSet::new();
                        let mut stack = vec![f];
                        let mut terminal = true;
                        let mut outside_preds = false;
                        while let Some(x) = stack.pop() {
                            if !seen.insert(x) { continue; }
                            if body.contains(&x) || self.loopheads.contains_key(&x) || seen.len() > 60 { terminal = false; break; }
                            let xb = self.blk(x)?;
                            for &(t, _) in &xb.succ { stack.push(t); }
                        }
                        for (&b, blk) in &self.r.blocks {
                            if !body.contains(&b) && !seen.contains(&b) && blk.succ.iter().any(|(t, _)| *t == f) { outside_preds = true; }
                        }
                        if terminal && edges == 1 && !outside_preds {
                            follow = None;
                        }
                    }
                }
                let id = self.next_id;
                self.next_id += 1;
                let ctx = Rc::new(LoopCtx { head: nn, body, follow, id });
                let _start = self.out.len();
                self.emit(ind, format!("LOOP{}: BEGIN", id));
                self.emit(ind, "WHILE 1 DO".into());
                self.emit(ind + 1, format!("NEXT{}: BEGIN", id));
                self.lstack.push(ctx.clone());
                self.open_all.push(nn);
                let pv = self.prev;
                let r1 = self.block(nn, ind + 2, Some(&ctx), None, pv);
                let r2 = match r1 {
                    Ok(cnt) => self.seq(cnt, None, ind + 2, Some(&ctx), Some(nn)),
                    Err(e) => Err(e),
                };
                self.open_all.pop();
                self.lstack.pop();
                r2?;
                self.emit(ind + 1, "END;".into());
                self.emit(ind, format!("END;  ! LOOP{}", id));
                n = follow;
                self.prev = None;
                continue;
            }
            let pv = self.prev;
            let lp = self.lstack.last().cloned();
            n = self.block(nn, ind, lp.as_deref(), stop, pv)?;
            self.prev = Some(nn);
        }
        Ok(())
    }

    fn join(&self, n: u16, lp: Option<&LoopCtx>) -> Option<u16> {
        let mut j = match self.ipd.get(&n) {
            Some(&f) if f != EXIT => Some(f as u16),
            _ => None,
        };
        if let (Some(lc), Some(jj)) = (lp, j) {
            if !lc.body.contains(&jj) || jj == lc.head {
                j = None;
            }
        }
        // several returns: no post-dominator, but the arms may still meet; the first block all of
        // them reach (that some path takes) is the join (knob 14)
        if j.is_none() && knob(14) {
            let succ: Vec<u16> = match self.r.blocks.get(&n) { Some(b) => b.succ.iter().map(|x| x.0).collect(), None => return None };
            if succ.len() < 2 { return None; }
            let reach = |s0: u16| -> HashSet<u16> {
                let mut seen = HashSet::new();
                let mut st = vec![s0];
                while let Some(x) = st.pop() {
                    if let Some(lc) = lp { if x == lc.head || !lc.body.contains(&x) { continue; } }
                    if x == n || !seen.insert(x) { continue; }
                    if let Some(b) = self.r.blocks.get(&x) {
                        for (t, _) in &b.succ { if !self.back.contains(&(x, *t)) { st.push(*t); } }
                    }
                }
                seen
            };
            let sets: Vec<HashSet<u16>> = succ.iter().map(|&x| reach(x)).collect();
            let common: Vec<u16> = sets[0].iter().filter(|x| sets[1..].iter().all(|s| s.contains(x))).cloned().collect();
            // minimal: not reachable from another common block
            let mut best: Option<u16> = None;
            for &c in &common {
                let rc = reach(c);
                if common.iter().any(|&d| d != c && reach(d).contains(&c) && !rc.contains(&d)) { continue; }
                if best.map(|b| c < b).unwrap_or(true) { best = Some(c); }
            }
            j = best;
        }
        j
    }

    fn block(&mut self, n: u16, ind: usize, lp: Option<&LoopCtx>, _stop: Option<u16>, prev: Option<u16>)
             -> Result<Option<u16>, String> {
        self.rd += 1;
        self.trace.push(('b', n, lp.map(|x| x.head).unwrap_or(0)));
        if self.rd > MAX_DEPTH {
            return Err(self.rec_err());
        }
        let r = self.block_inner(n, ind, lp, prev);
        self.rd -= 1;
        self.trace.pop();
        r
    }

    /// knob 23: blocks of a branch's region that several paths reach before its join
    fn merge_points(&self, n: u16, j: Option<u16>, lp: Option<&LoopCtx>) -> Vec<u16> {
        let succ: Vec<u16> = match self.r.blocks.get(&n) { Some(b) => b.succ.iter().map(|x| x.0).collect(), None => return vec![] };
        let mut region: Vec<u16> = vec![];
        let mut seen: HashSet<u16> = HashSet::new();
        let mut st: Vec<u16> = succ.clone();
        while let Some(x) = st.pop() {
            if Some(x) == j || x == n || self.exits.iter().any(|(b, _)| *b == x) { continue; }
            if let Some(lc) = lp { if x == lc.head || !lc.body.contains(&x) { continue; } }
            if self.loopheads.contains_key(&x) { continue; }
            if !seen.insert(x) { continue; }
            region.push(x);
            if let Some(b) = self.r.blocks.get(&x) {
                for (t, _) in &b.succ { if !self.back.contains(&(x, *t)) { st.push(*t); } }
            }
        }
        let mut preds: HashMap<u16, usize> = HashMap::new();
        for &x in region.iter().chain(std::iter::once(&n)) {
            if let Some(b) = self.r.blocks.get(&x) {
                for (t, _) in &b.succ {
                    if seen.contains(t) && !self.back.contains(&(x, *t)) { *preds.entry(*t).or_default() += 1; }
                }
            }
        }
        let mut m: Vec<u16> = region.into_iter().filter(|x| preds.get(x).cloned().unwrap_or(0) >= 2 && !succ.contains(x)).collect();
        // topological order inside the region (no back edges): by reachability, then address
        m.sort();
        let reach_from = |a: u16, b0: u16| -> bool {
            let mut sn = HashSet::new();
            let mut st = vec![a];
            while let Some(x) = st.pop() {
                if x == b0 { return true; }
                if Some(x) == j || !sn.insert(x) { continue; }
                if let Some(b) = self.r.blocks.get(&x) {
                    for (t, _) in &b.succ { if !self.back.contains(&(x, *t)) && seen.contains(t) { st.push(*t); } }
                }
            }
            false
        };
        let mut out: Vec<u16> = vec![];
        let mut rest = m;
        while !rest.is_empty() {
            let k = (0..rest.len()).find(|&i| !rest.iter().any(|&o| o != rest[i] && reach_from(o, rest[i]))).unwrap_or(0);
            out.push(rest.remove(k));
        }
        out
    }

    fn block_inner(&mut self, n: u16, ind: usize, lp: Option<&LoopCtx>, prev: Option<u16>)
                   -> Result<Option<u16>, String> {
        let b0 = self.blk(n)?;
        if knob(23) && matches!(b0.term, Term::Cond | Term::Case) && !self.in_merge.contains(&n) {
            let j = self.join(n, lp);
            let ms = self.merge_points(n, j, lp);
            if !ms.is_empty() && ms.len() <= 12 {
                // LOOPj: BEGIN LOOPm_k: BEGIN ... LOOPm_1: BEGIN <branch> END; m_1 ... END; m_k END; (j follows)
                let mut labs: Vec<String> = vec![];
                let jl = j.map(|_| { let id = self.next_id; self.next_id += 1; format!("LOOP{}", id) });
                let base_exits = self.exits.len();
                if let (Some(jj), Some(l)) = (j, jl.clone()) {
                    self.emit(ind, format!("{}: BEGIN", l));
                    self.exits.push((jj, l));
                }
                for &m in ms.iter().rev() {
                    let id = self.next_id; self.next_id += 1;
                    let l = format!("LOOP{}", id);
                    self.emit(ind, format!("{}: BEGIN", l));
                    labs.push(l.clone());
                    self.exits.push((m, l));
                }
                self.in_merge.insert(n);
                let r = self.block_inner(n, ind, lp, prev);
                self.in_merge.remove(&n);
                let after = r?;
                if let Some(a) = after { self.seq(Some(a), None, ind, lp, Some(n))?; }
                // close the innermost label, emit its block, and so on outwards
                for &m in ms.iter() {
                    let (_, l) = self.exits.pop().unwrap();
                    self.emit(ind, format!("END;  ! {}", l));
                    self.seq(Some(m), None, ind, lp, None)?;
                }
                if let Some(l) = jl {
                    self.exits.pop();
                    self.emit(ind, format!("END;  ! {}", l));
                }
                self.exits.truncate(base_exits);
                let _ = labs;
                return Ok(j);
            }
        }
        let b = self.blk(n)?;
        let l = self.l;
        self.prev = prev;
        self.stmts(n, ind);
        match b.term {
            Term::Ret => {
                let rv = l.stmts.get(&n).and_then(|ss| {
                    ss.iter().rev().find_map(|s| if let Stmt::Ret(e) = s { Some(e) } else { None })
                });
                match rv {
                    Some(e) if l.returns => {
                        let t = format!("RETURN {};", self.p.e(e, 0));
                        self.emit(ind, t);
                    }
                    _ => self.emit(ind, "RETURN;".into()),
                }
                Ok(None)
            }
            Term::Tail => Ok(None),
            Term::Jmp | Term::Fall => Ok(b.succ.first().map(|x| x.0)),
            Term::Cond => {
                let mut cnd = l.bcond.get(&n).cloned().unwrap_or_else(|| unk("?cc"));
                if is_unk(&cnd, "perpred") {
                    let per = l.bcond_pred.get(&n).ok_or_else(|| format!("KeyError: {}", n))?;
                    cnd = prev.and_then(|p| per.get(&p)).cloned().unwrap_or_else(|| unk("?cc"));
                }
                let mut tt = b.succ.iter().find(|x| x.1 == Kind::T).map(|x| x.0);
                let mut ff = b.succ.iter().find(|x| x.1 == Kind::F).map(|x| x.0);
                // long branch: Bcc NEAR / JMP FAR / NEAR: ... is "B!cc FAR" with NEAR as the fall-through
                if let (Some(f), Some(t)) = (ff, tt) {
                    if let Ok(fb) = self.blk(f) {
                        let empty = l.stmts.get(&f).map(|x| x.is_empty()).unwrap_or(true);
                        if fb.term == Term::Jmp && fb.ins.len() == 1 && fb.ins[0].is_jump() && empty
                            && t == f.wrapping_add(2 * fb.ins[0].nwords) {
                            if let Some(x) = fb.succ.first().map(|x| x.0) {
                                cnd = negate(&cnd);
                                tt = Some(x);
                                ff = Some(t);
                            }
                        }
                    }
                }
                let j = self.join(n, lp);
                let (cc, first, second) = if ff == j {
                    (cnd, tt, None)
                } else if tt == j {
                    (negate(&cnd), ff, None)
                } else {
                    (negate(&cnd), ff, tt)
                };
                let t = format!("IF {}", self.p.cond(&cc, 0));
                self.emit(ind, t);
                self.emit(ind, "THEN".into());
                self.emit(ind + 1, "BEGIN".into());
                self.seq(first, j, ind + 2, lp, Some(n))?;
                self.emit(ind + 1, "END".into());
                // THEN arm ends in RETURN: no ELSE, the other arm follows the IF (BLISS lays it out so)
                let then_returns = self.out.len() >= 2 && self.out[self.out.len() - 2].1.starts_with("RETURN");
                if second.is_some() && then_returns && knob(8) {
                    self.out.last_mut().unwrap().1.push(';');
                    self.seq(second, j, ind, lp, Some(n))?;
                    return Ok(j);
                }
                if second.is_some() {
                    self.emit(ind, "ELSE".into());
                    self.emit(ind + 1, "BEGIN".into());
                    self.seq(second, j, ind + 2, lp, Some(n))?;
                    self.emit(ind + 1, "END".into());
                }
                self.out.last_mut().unwrap().1.push(';');
                Ok(j)
            }
            Term::Case => {
                let idx = l.bcase.get(&n);
                let cs = b.case.as_ref().unwrap();
                let j = self.join(n, lp);
                let idx = idx.ok_or_else(|| "TypeError: 'NoneType' object is not subscriptable".to_string())?;
                // ASL Rn before the dispatch: idx = X ^ 1 -> X;  X = Y + k -> CASE Y FROM -k
                let mut x: E = idx.clone();
                let mut halved = false;
                if let E::Op("^", a, b) = &x {
                    if **b == E::C(1) {
                        x = (**a).clone();
                        halved = true;
                    }
                }
                let mut lo: i64 = 0;
                if halved {
                    if let E::Op("+", a, b) = &x {
                        if let E::C(k) = **b {
                            lo = -(sgn(k) as i64);
                            x = (**a).clone();
                        }
                    }
                }
                // knob 23: code several arms (not all) share before the join: CASE inside a labelled
                // block, the shared code after TES, the other arms LEAVE the block
                let mut shared: Option<u16> = None;
                if knob(24) {
                    let arms: Vec<u16> = { let mut v: Vec<u16> = cs.3.clone(); v.sort(); v.dedup(); v };
                    let reach = |s0: u16, avoid: Option<u16>| -> HashSet<u16> {
                        let mut seen = HashSet::new();
                        let mut st = vec![s0];
                        while let Some(x) = st.pop() {
                            if Some(x) == j || Some(x) == avoid || x == n { continue; }
                            if let Some(lc) = lp { if x == lc.head || !lc.body.contains(&x) { continue; } }
                            if !seen.insert(x) { continue; }
                            if let Some(b) = self.r.blocks.get(&x) {
                                for (t, _) in &b.succ { if !self.back.contains(&(x, *t)) { st.push(*t); } }
                            }
                        }
                        seen
                    };
                    let reaches_j = |s0: u16, avoid: u16| -> bool {
                        let mut seen = HashSet::new();
                        let mut st = vec![s0];
                        while let Some(x) = st.pop() {
                            if x == avoid || x == n { continue; }
                            if Some(x) == j { return true; }
                            if let Some(lc) = lp { if x == lc.head || !lc.body.contains(&x) { continue; } }
                            if !seen.insert(x) { continue; }
                            if let Some(b) = self.r.blocks.get(&x) {
                                for (t, _) in &b.succ { if !self.back.contains(&(x, *t)) { st.push(*t); } }
                            }
                        }
                        false
                    };
                    let sets: Vec<HashSet<u16>> = arms.iter().map(|&a| reach(a, None)).collect();
                    let mut best: Option<(usize, u16)> = None;
                    let mut cands: Vec<u16> = sets.iter().flatten().cloned().collect();
                    cands.sort(); cands.dedup();
                    for c in cands {
                        if arms.contains(&c) || self.loopheads.contains_key(&c) { continue; }
                        let users: Vec<usize> = (0..arms.len()).filter(|&k| sets[k].contains(&c)).collect();
                        if users.len() < 2 || users.len() == arms.len() { continue; }
                        // every path of a user arm to the join goes through c
                        if users.iter().any(|&k| reaches_j(arms[k], c)) { continue; }
                        // c is the first shared block: no other candidate shared by the same arms reaches c
                        let score = users.len();
                        if best.map(|(bs, bc)| score > bs || (score == bs && c < bc)).unwrap_or(true) { best = Some((score, c)); }
                    }
                    shared = best.map(|x| x.1);
                    // the earliest block of that shared region: not reachable from another one the same arms share
                    if let Some(c) = shared {
                        let users: Vec<u16> = arms.iter().cloned().filter(|&a| reach(a, None).contains(&c)).collect();
                        let mut first = c;
                        for d in reach(users[0], None) {
                            if d != c && users.iter().all(|&a| reach(a, None).contains(&d)) && reach(d, None).contains(&first)
                                && !users.iter().any(|&a| reaches_j(a, d)) {
                                first = d;
                            }
                        }
                        shared = Some(first);
                    }
                }
                let blk_id = if shared.is_some() { let id = self.next_id; self.next_id += 1; Some(id) } else { None };
                if let Some(id) = blk_id {
                    self.emit(ind, format!("LOOP{}: BEGIN", id));
                    self.labels.insert(format!("LOOP{}", id));
                }
                let cnt = cs.1 as i64;
                let t = if halved {
                    format!("CASE {} FROM {} TO {} OF", self.p.e(&x, 0), lo, lo + cnt - 1)
                } else {
                    format!("CASE ({}) / 2 FROM 0 TO {} OF", self.p.e(idx, 0), cnt - 1)
                };
                self.emit(ind, t);
                self.emit(ind, "SET".into());
                let mut seen: Vec<(u16, Vec<usize>)> = vec![];
                for (k, &t) in cs.3.iter().enumerate() {
                    match seen.iter_mut().find(|x| x.0 == t) {
                        Some(x) => x.1.push(k),
                        None => seen.push((t, vec![k])),
                    }
                }
                // arms in the order their code sits in the ROM: BLISS lays them out in source order
                if knob(9) {
                    seen.sort_by_key(|x| x.0);
                }
                for (t, ks) in seen {
                    let lab: Vec<String> = ks.iter().map(|k| (*k as i64 + lo).to_string()).collect();
                    self.emit(ind, format!("[{}]:", lab.join(",")));
                    self.emit(ind + 1, "BEGIN".into());
                    match (shared, blk_id) {
                        (Some(sh), Some(id)) => {
                            // arm through the shared code: stop there; other arms skip it
                            let mut seen2 = HashSet::new();
                            let mut st = vec![t];
                            let mut uses = false;
                            while let Some(x) = st.pop() {
                                if x == sh { uses = true; break; }
                                if Some(x) == j || x == n || !seen2.insert(x) { continue; }
                                if let Some(lc) = lp { if x == lc.head || !lc.body.contains(&x) { continue; } }
                                if let Some(b) = self.r.blocks.get(&x) {
                                    for (tt, _) in &b.succ { if !self.back.contains(&(x, *tt)) { st.push(*tt); } }
                                }
                            }
                            if uses {
                                self.seq(Some(t), Some(sh), ind + 2, lp, Some(n))?;
                            } else {
                                self.seq(Some(t), j, ind + 2, lp, Some(n))?;
                                self.emit(ind + 2, format!("LEAVE LOOP{};", id));
                            }
                        }
                        _ => self.seq(Some(t), j, ind + 2, lp, Some(n))?,
                    }
                    self.emit(ind + 1, "END;".into());
                }
                self.emit(ind, "TES;".into());
                if let (Some(sh), Some(id)) = (shared, blk_id) {
                    self.seq(Some(sh), j, ind, lp, None)?;
                    self.emit(ind, format!("END;  ! LOOP{}", id));
                }
                Ok(j)
            }
        }
    }
}


/// the word under a SWAB that CLRB cleared the low byte of first (x AND 177400), or the word itself
fn hi_word(x: &E) -> &E {
    match x {
        E::Op("AND", y, m) if matches!(**m, E::C(k) if k as u16 == 0o177400) => y,
        y => y,
    }
}
