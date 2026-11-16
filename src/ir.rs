// SPDX-License-Identifier: Apache-2.0
// Expressions, statements and the helpers over them.
use std::collections::HashSet;
use std::rc::Rc;

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Loc {
    R(i32),
    P(i32),
    S(i32),
    /// a stack slot whose address is taken: a real memory variable
    M(i32),
    /// a parameter passed in register k (LINKAGE ... = JSR (REGISTER = k))
    Q(i32),
}

impl Loc {
    pub fn name(&self) -> String {
        match self {
            Loc::R(n) => format!("R{}", n),
            Loc::P(n) => format!("P{}", n),
            Loc::S(n) => format!("S{}", n),
            Loc::M(n) => format!("M{}", n),
            Loc::Q(n) => format!("Q{}", n),
        }
    }
    /// memory-like: parameters and addressed locals
    pub fn is_p(&self) -> bool {
        matches!(self, Loc::P(_) | Loc::M(_) | Loc::Q(_))
    }
    pub fn is_rs(&self) -> bool {
        !self.is_p()
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum E {
    C(u16),
    /// address of the frame slot at this offset (ret address = 0)
    Frame(i32),
    Loc(Loc),
    G(u16),
    Fetch(Rc<E>, bool),
    Op(&'static str, Rc<E>, Rc<E>),
    Un(&'static str, Rc<E>),
    Call(Rc<str>, Vec<E>),
    Ext8(Rc<E>),
    Swab(Rc<E>),
    Rel(&'static str, Rc<E>, Rc<E>),
    And(Rc<E>, Rc<E>),
    Or(Rc<E>, Rc<E>),
    Not(Rc<E>),
    Unk(String, Vec<E>),
    Pending(&'static str),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Place {
    Loc(Loc),
    Mem(E, bool),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Stmt {
    Set(Place, E),
    Do(E),
    Ret(E),
    Tail(String),
    Unk(String),
    Post(Loc, u16),
}

pub fn c(v: i32) -> E {
    E::C(v as u16)
}
pub fn sgn(v: u16) -> i32 {
    v as i16 as i32
}
pub fn op(s: &'static str, a: E, b: E) -> E {
    E::Op(s, Rc::new(a), Rc::new(b))
}
pub fn unk(s: &str) -> E {
    E::Unk(s.to_string(), vec![])
}
pub fn is_unk(e: &E, tag: &str) -> bool {
    matches!(e, E::Unk(t, v) if t == tag && v.is_empty())
}

pub fn add(a: E, b: E) -> E {
    if let (E::C(x), E::C(y)) = (&a, &b) {
        return E::C(x.wrapping_add(*y));
    }
    if let (E::Frame(o), E::C(c)) | (E::C(c), E::Frame(o)) = (&a, &b) {
        return E::Frame(o + sgn(*c));
    }
    if let E::C(0) = b {
        return a;
    }
    if let E::C(0) = a {
        return b;
    }
    if let (E::Op("+", l, r), E::C(y)) = (&a, &b) {
        if let E::C(x) = **r {
            return add((**l).clone(), E::C(x.wrapping_add(*y)));
        }
    }
    op("+", a, b)
}

pub fn sub(a: E, b: E) -> E {
    if let E::C(y) = b {
        return add(a, E::C(y.wrapping_neg()));
    }
    op("-", a, b)
}

impl E {
    pub fn kids(&self) -> Vec<&E> {
        match self {
            E::C(_) | E::Frame(_) | E::Loc(_) | E::G(_) | E::Pending(_) => vec![],
            E::Fetch(a, _) | E::Un(_, a) | E::Ext8(a) | E::Swab(a) | E::Not(a) => vec![a],
            E::Op(_, a, b) | E::Rel(_, a, b) | E::And(a, b) | E::Or(a, b) => vec![a, b],
            E::Call(_, v) | E::Unk(_, v) => v.iter().collect(),
        }
    }
}

pub fn locs_in(e: &E, acc: &mut HashSet<Loc>) {
    if let E::Loc(l) = e {
        acc.insert(*l);
        return;
    }
    for k in e.kids() {
        locs_in(k, acc);
    }
}

pub fn count_loc(e: &E, name: Loc) -> usize {
    if let E::Loc(l) = e {
        return (*l == name) as usize;
    }
    e.kids().into_iter().map(|k| count_loc(k, name)).sum()
}

pub fn subst(e: &E, name: Loc, v: &E) -> E {
    let r = |x: &Rc<E>| Rc::new(subst(x, name, v));
    match e {
        E::Loc(l) => {
            if *l == name {
                v.clone()
            } else {
                e.clone()
            }
        }
        E::C(_) | E::Frame(_) | E::G(_) | E::Pending(_) => e.clone(),
        E::Fetch(a, b) => E::Fetch(r(a), *b),
        E::Un(s, a) => E::Un(s, r(a)),
        E::Ext8(a) => E::Ext8(r(a)),
        E::Swab(a) => E::Swab(r(a)),
        E::Not(a) => E::Not(r(a)),
        E::Op("+", a, b) => add((*r(a)).clone(), (*r(b)).clone()),
        E::Op(s, a, b) => E::Op(s, r(a), r(b)),
        E::Rel(s, a, b) => E::Rel(s, r(a), r(b)),
        E::And(a, b) => E::And(r(a), r(b)),
        E::Or(a, b) => E::Or(r(a), r(b)),
        E::Call(n, a) => E::Call(n.clone(), a.iter().map(|x| subst(x, name, v)).collect()),
        E::Unk(n, a) => E::Unk(n.clone(), a.iter().map(|x| subst(x, name, v)).collect()),
    }
}

pub fn depth(e: &E) -> usize {
    1 + e.kids().into_iter().map(depth).max().unwrap_or(0)
}

pub fn has_call(e: &E) -> bool {
    if let E::Call(..) = e {
        return true;
    }
    e.kids().into_iter().any(has_call)
}

pub fn is_mem_read(e: &E) -> bool {
    match e {
        E::Fetch(..) | E::Call(..) => true,
        E::Loc(l) => l.is_p(),
        _ => e.kids().into_iter().any(is_mem_read),
    }
}

pub fn st_uses(s: &Stmt, u: &mut HashSet<Loc>) {
    match s {
        Stmt::Set(p, e) => {
            locs_in(e, u);
            if let Place::Mem(a, _) = p {
                locs_in(a, u);
            }
        }
        Stmt::Do(e) | Stmt::Ret(e) => locs_in(e, u),
        _ => {}
    }
}

pub fn st_def(s: &Stmt) -> Option<Loc> {
    if let Stmt::Set(Place::Loc(l), _) = s {
        Some(*l)
    } else {
        None
    }
}

pub fn st_store(s: &Stmt) -> bool {
    match s {
        Stmt::Set(Place::Mem(..), _) => true,
        Stmt::Set(Place::Loc(l), e) => l.is_p() || has_call(e),
        Stmt::Do(_) | Stmt::Tail(_) => true,
        _ => false,
    }
}

pub fn neg_rel(r: &str) -> &'static str {
    match r {
        "EQL" => "NEQ", "NEQ" => "EQL", "LSS" => "GEQ", "GEQ" => "LSS", "GTR" => "LEQ", "LEQ" => "GTR",
        "GTRU" => "LEQU", "LEQU" => "GTRU", "GEQU" => "LSSU", "LSSU" => "GEQU",
        "LOW" => "NLOW", "NLOW" => "LOW",
        _ => "???",
    }
}

pub fn negate(e: &E) -> E {
    match e {
        E::Rel(r, a, b) => E::Rel(neg_rel(r), a.clone(), b.clone()),
        E::And(a, b) => E::Or(Rc::new(negate(a)), Rc::new(negate(b))),
        E::Or(a, b) => E::And(Rc::new(negate(a)), Rc::new(negate(b))),
        E::Not(a) => (**a).clone(),
        _ => E::Not(Rc::new(e.clone())),
    }
}

fn pb(b: bool) -> &'static str {
    if b { "True" } else { "False" }
}

/// Python repr() of the tuple form of an expression (the format of an earlier Python version), for the
/// "?? ..." fallback text.
pub fn pyrepr(e: &E) -> String {
    let list = |v: &Vec<E>| v.iter().map(pyrepr).collect::<Vec<_>>().join(", ");
    match e {
        E::C(v) => format!("('c', {})", v),
        E::Frame(o) => format!("('frame', {})", o),
        E::Loc(l) => format!("('loc', '{}')", l.name()),
        E::G(a) => format!("('g', {})", a),
        E::Fetch(a, b) => format!("('fetch', {}, {})", pyrepr(a), pb(*b)),
        E::Op(s, a, b) => format!("('op', '{}', {}, {})", s, pyrepr(a), pyrepr(b)),
        E::Un(s, a) => format!("('un', '{}', {})", s, pyrepr(a)),
        E::Call(n, v) => format!("('call', '{}', [{}])", n, list(v)),
        E::Ext8(a) => format!("('ext8', {})", pyrepr(a)),
        E::Swab(a) => format!("('swab', {})", pyrepr(a)),
        E::Rel(s, a, b) => format!("('rel', '{}', {}, {})", s, pyrepr(a), pyrepr(b)),
        E::And(a, b) => format!("('and', {}, {})", pyrepr(a), pyrepr(b)),
        E::Or(a, b) => format!("('or', {}, {})", pyrepr(a), pyrepr(b)),
        E::Not(a) => format!("('not', {})", pyrepr(a)),
        E::Unk(t, v) => {
            if v.is_empty() {
                format!("('{}',)", t)
            } else {
                format!("('{}', {})", t, list(v))
            }
        }
        E::Pending(m) => format!("('pending', '{}')", m),
    }
}
