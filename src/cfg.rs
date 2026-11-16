// SPDX-License-Identifier: Apache-2.0
//! Routine discovery and control-flow graphs.
use crate::arch::target::*;
use crate::program::Program;
use std::collections::{BTreeMap, HashSet};
use std::rc::Rc;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kind {
    T,
    F,
    J,
    Case,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Term {
    Ret,
    Jmp,
    Cond,
    Case,
    Fall,
    Tail,
}

#[derive(Clone)]
pub struct Block {
    pub start: u16,
    pub ins: Vec<Insn>,
    pub succ: Vec<(u16, Kind)>,
    pub term: Term,
    pub case: Option<Rc<CaseInfo>>,
}

pub struct Routine {
    pub entry: u16,
    pub name: String,
    pub insns: BTreeMap<u16, Insn>,
    pub order: Vec<u16>,
    pub blocks: BTreeMap<u16, Block>,
}

impl Routine {
    pub fn new(mem: &Program, entry: u16, entries: &HashSet<u16>) -> Result<Routine, String> {
        let mut insns: BTreeMap<u16, Insn> = BTreeMap::new();
        let mut order = vec![];
        let mut work = vec![entry];
        let mut leaders: HashSet<u16> = HashSet::new();
        leaders.insert(entry);
        while let Some(mut pc) = work.pop() {
            while !insns.contains_key(&pc) {
                let mut i = mem.dec(pc)?;
                let mut brk = false;
                let nxt = pc.wrapping_add(2 * i.nwords);
                let case = i.case_table(mem);
                if i.is_hard_stop() {
                    i.stop = true;
                    brk = true;
                } else if let Some((tab, n, base)) = case {
                    let mut ts = vec![];
                    for k in 0..n {
                        let w = mem.rw(tab.wrapping_add(2 * k as u16)).ok_or("TypeError: case table outside image")?;
                        ts.push(base.wrapping_add(w));
                    }
                    for &t in &ts {
                        leaders.insert(t);
                        work.push(t);
                    }
                    i.case = Some(Rc::new((tab, n, base, ts)));
                    brk = true;
                } else if i.is_return() {
                    brk = true;
                } else if i.is_jump() && !i.targets.is_empty() {
                    let t = i.targets[0];
                    if entries.contains(&t) && t != entry {
                        i.tail = true;
                    } else {
                        leaders.insert(t);
                        work.push(t);
                    }
                    brk = true;
                } else if i.is_branch() {
                    leaders.insert(i.targets[0]);
                    work.push(i.targets[0]);
                    brk = true;
                } else {
                    if i.cond && !i.targets.is_empty() {
                        leaders.insert(i.targets[0]);
                        work.push(i.targets[0]);
                        leaders.insert(nxt);
                    }
                    if i.stop {
                        brk = true;
                    }
                }
                insns.insert(pc, i);
                order.push(pc);
                if brk {
                    break;
                }
                pc = nxt;
            }
        }
        let mut r = Routine { entry, name: mem.name_of(entry), insns, order, blocks: BTreeMap::new() };
        r.build_blocks(&leaders);
        Ok(r)
    }

    fn build_blocks(&mut self, leaders: &HashSet<u16>) {
        let mut blocks: BTreeMap<u16, Block> = BTreeMap::new();
        let mut cur = 0u16;
        for (&pc, i) in &self.insns {
            if leaders.contains(&pc) || blocks.is_empty() {
                blocks.insert(pc, Block { start: pc, ins: vec![], succ: vec![], term: Term::Fall, case: None });
                cur = pc;
            }
            blocks.get_mut(&cur).unwrap().ins.push(i.clone());
        }
        for b in blocks.values_mut() {
            let last = b.ins.last().unwrap().clone();
            let nxt = last.pc.wrapping_add(2 * last.nwords);
            if let Some(cs) = &last.case {
                b.term = Term::Case;
                b.case = Some(cs.clone());
                b.succ = cs.3.iter().map(|&t| (t, Kind::Case)).collect();
            } else if last.is_return() {
                b.term = Term::Ret;
            } else if last.is_jump() {
                if last.tail || last.targets.is_empty() {
                    b.term = Term::Tail;
                } else {
                    b.term = Term::Jmp;
                    b.succ = vec![(last.targets[0], Kind::J)];
                }
            } else if last.is_branch() {
                b.term = Term::Jmp;
                b.succ = vec![(last.targets[0], Kind::J)];
            } else if last.is_cond_branch() {
                b.term = Term::Cond;
                b.succ = vec![(last.targets[0], Kind::T), (nxt, Kind::F)];
            } else if last.stop {
                b.term = Term::Ret;
            } else {
                b.term = Term::Fall;
                b.succ = vec![(nxt, Kind::F)];
            }
        }
        let keys: HashSet<u16> = blocks.keys().cloned().collect();
        for b in blocks.values_mut() {
            b.succ.retain(|(t, _)| keys.contains(t));
        }
        self.blocks = blocks;
    }

    /// Undo cross-jumping: a small block reached from several places (no cycle through it) gets a
    /// private copy per extra predecessor, keyed by an odd (never a real) address.
    pub fn dup_tails(&mut self, max_ins: usize) {
        let keys: Vec<u16> = self.blocks.keys().cloned().collect();
        let mut next_odd: u16 = 1;
        for j in keys {
            if j == self.entry { continue; }
            let blk = self.blocks[&j].clone();
            // a lone conditional branch testing flags its predecessors set (a cross-jumped Bcc):
            // one copy per predecessor, so each copy's condition is that predecessor's comparison
            let lone_bcc = blk.term == Term::Cond && blk.ins.len() == 1 && blk.ins[0].cond;
            if max_ins == 0 && !lone_bcc { continue; }
            if !lone_bcc && (blk.ins.len() > max_ins || !matches!(blk.term, Term::Jmp | Term::Ret | Term::Fall)) { continue; }
            let preds: Vec<u16> = self.blocks.iter().filter(|(_, b)| b.succ.iter().any(|(t, _)| *t == j)).map(|(k, _)| *k).collect();
            if preds.len() < 2 { continue; }
            if preds.iter().any(|p| self.blocks[p].term == Term::Case) { continue; }
            // no cycle through j
            let mut seen: HashSet<u16> = HashSet::new();
            let mut st: Vec<u16> = blk.succ.iter().map(|x| x.0).collect();
            let mut cyc = false;
            while let Some(x) = st.pop() {
                if x == j { cyc = true; break; }
                if !seen.insert(x) { continue; }
                if let Some(b) = self.blocks.get(&x) { st.extend(b.succ.iter().map(|y| y.0)); }
            }
            if cyc { continue; }
            for p in preds.into_iter().skip(1) {
                while self.blocks.contains_key(&next_odd) { next_odd += 2; }
                let mut copy = Block { start: next_odd, ins: blk.ins.clone(), succ: blk.succ.clone(), term: blk.term, case: None };
                if copy.term == Term::Fall {
                    copy.term = Term::Jmp;
                    copy.succ = copy.succ.iter().map(|(t, _)| (*t, Kind::J)).collect();
                }
                let k = next_odd;
                next_odd += 2;
                if let Some(pb) = self.blocks.get_mut(&p) {
                    for s in pb.succ.iter_mut() { if s.0 == j { s.0 = k; } }
                }
                self.blocks.insert(k, copy);
            }
        }
    }
}
