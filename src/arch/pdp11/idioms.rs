// SPDX-License-Identifier: Apache-2.0
//! PDP-11 / BLISS-16 code idioms the architecture-independent passes ask about: control flow of an
//! instruction, the CASE dispatch, register-save helpers, argument pushes, the prologue's local
//! allocation, hand-written MACRO markers, overlay thunks.
use super::*;
use crate::program::Program;
use std::collections::BTreeSet;

impl Insn {
    /// JSR PC,target: a routine call
    pub fn is_call(&self) -> bool {
        self.mn == "JSR" && self.ops[0].reg == 7
    }

    pub fn call_target(&self) -> Option<u16> {
        if self.is_call() { self.targets.first().cloned() } else { None }
    }

    /// any JSR (also coroutine and inline-argument calls such as JSR R5,X)
    pub fn is_jsr(&self) -> bool {
        self.mn == "JSR"
    }

    pub fn is_return(&self) -> bool {
        self.ret || self.mn == "RTS"
    }

    pub fn is_jump(&self) -> bool {
        self.mn == "JMP"
    }

    pub fn is_branch(&self) -> bool {
        self.mn == "BR"
    }

    pub fn is_cond_branch(&self) -> bool {
        self.cond && (br_rel(&self.mn).is_some() || self.mn == "SOB")
    }

    /// ends the walk: undecodable, a trap/halt or an interrupt return (IOT is a kernel call and returns)
    pub fn is_hard_stop(&self) -> bool {
        let special = !self.valid || self.mn.starts_with(".WORD")
            || matches!(self.mn.as_str(), "HALT" | "IOT" | "EMT" | "TRAP" | "RTI" | "RTT");
        special && self.mn != "IOT"
    }

    /// instructions BLISS-16 never emits: the routine is hand-written MACRO (MTPS/MFPS are builtins)
    pub fn is_macro_marker(&self) -> bool {
        matches!(self.mn.as_str(), "IOT" | "RTI" | "RTT" | "EMT" | "TRAP")
            // BLISS only adjusts SP (ADD/SUB, pushes and pops); loading it is a stack switch
            || (self.mn == "MOV" && self.ops.len() == 2 && self.ops[1].mode == 0 && self.ops[1].reg == 6)
    }

    /// general registers (R0-R5) this instruction changes, not counting calls and returns
    pub fn regs_written(&self) -> Vec<i32> {
        let mut v = vec![];
        if matches!(self.mn.as_str(), "CMP" | "CMPB" | "BIT" | "BITB" | "TST" | "TSTB" | "JSR" | "RTS" | "JMP") {
            return v;
        }
        if let Some(d) = self.ops.last() {
            if matches!(d.mode, 0 | 2 | 4) && d.reg <= 5 { v.push(d.reg as i32); }
        }
        if self.ops.len() == 2 && matches!(self.ops[0].mode, 2 | 4) && self.ops[0].reg <= 5 {
            v.push(self.ops[0].reg as i32);
        }
        v
    }

    /// BLISS-16's CASE dispatch `ADD tbl(Rn),PC` at an address with a known case table
    pub fn case_table(&self, mem: &Program) -> Option<(u16, usize, u16)> {
        if self.mn == "ADD" && self.ops[1].mode == 0 && self.ops[1].reg == 7 {
            mem.cases.get(&self.pc).cloned()
        } else {
            None
        }
    }

    /// MOV Rk,-(SP) with k in 1..5: a register save in a prologue
    fn is_reg_push(&self) -> bool {
        self.mn == "MOV" && self.ops[0].mode == 0 && (1..=5).contains(&self.ops[0].reg) && self.ops[1].mode == 4 && self.ops[1].reg == 6
    }

    /// JSR R5,dispatcher as the first instruction: an overlay thunk with inline arguments
    pub fn is_thunk_call(&self, mem: &Program) -> bool {
        self.mn == "JSR" && self.ops[0].reg == 5 && self.targets.first().map(|x| mem.thunks.contains(x)).unwrap_or(false)
    }
}

/// operations the compiler provides as builtins; calls to them are declared `BUILTIN`, not
/// `EXTERNAL ROUTINE`
pub const BUILTINS: &[&str] = &["MTPS", "MFPS"];

/// Registers a routine's prologue saves: `JSR R1,$SAVn` (R1..Rn) or individual pushes.
pub fn saved_regs(entry: &[Insn], mem: &Program) -> BTreeSet<i32> {
    let mut set = BTreeSet::new();
    for (k, i) in entry.iter().enumerate() {
        if k == 0 && i.mn == "JSR" && i.ops[0].reg == 1 {
            if let Some(&n) = i.targets.first().and_then(|t| mem.saves.get(t)) {
                for j in 1..=n {
                    set.insert(j);
                }
                break;
            }
        }
        if i.is_reg_push() {
            set.insert(i.ops[0].reg as i32);
        } else {
            break;
        }
    }
    set
}

/// Words pushed as arguments before the call at `ins[k]` (since the previous call in the block);
/// a store into (SP) before any push reuses the slot an earlier call left and counts as one.
pub fn pushed_args(ins: &[Insn], k: usize) -> i32 {
    let mut n = 0;
    let mut earliest_fill = false;
    for j in ins[..k].iter().rev() {
        if j.mn == "JSR" {
            break;
        }
        let d = match j.ops.last() {
            Some(d) => d,
            None => continue,
        };
        if d.reg == 6 && d.mode == 4 {
            n += 1;
            earliest_fill = false;
            continue;
        }
        if d.reg == 6 && d.mode == 1 && j.ops.len() == 2 && !matches!(j.mn.as_str(), "CMP" | "CMPB" | "BIT" | "BITB") {
            earliest_fill = true;
        }
    }
    if earliest_fill {
        n += 1;
    }
    n
}

/// The prologue's frame: bytes of register saves (return address included) and of locals
/// allocated after them (SUB #n,SP / TST -(SP) / CMP -(SP),-(SP), then CLR/TST -(SP) pushes).
pub fn frame_layout(ins: &[Insn], mem: &Program) -> (i64, i64) {
    let mut k0 = 0usize;
    let mut saved = 0i64;
    if let Some(i) = ins.first() {
        if i.mn == "JSR" && i.ops[0].reg == 1 {
            if let Some(&d) = mem.saves.get(i.targets.first().unwrap_or(&0)) {
                saved = 2 * d as i64 + 2;
                k0 = 1;
            }
        }
    }
    while k0 < ins.len() && ins[k0].mn == "MOV" && ins[k0].ops[0].mode == 0 && ins[k0].ops[1].mode == 4 && ins[k0].ops[1].reg == 6 {
        saved += 2;
        k0 += 1;
    }
    let alloc: i64 = match ins.get(k0) {
        Some(i) if i.mn == "SUB" && i.ops[0].mode == 2 && i.ops[0].reg == 7 && i.ops[1].mode == 0 && i.ops[1].reg == 6 => i.ops[0].x as i64,
        Some(i) if i.mn == "TST" && i.ops[0].mode == 4 && i.ops[0].reg == 6 => 2,
        Some(i) if i.mn == "CMP" && i.ops[0].mode == 4 && i.ops[0].reg == 6 && i.ops[1].mode == 4 && i.ops[1].reg == 6 => 4,
        _ => 0,
    };
    let mut alloc = alloc;
    let mut k1 = k0 + if alloc > 0 { 1 } else { 0 };
    while k1 < ins.len() && matches!(ins[k1].mn.as_str(), "CLR" | "TST") && ins[k1].ops[0].mode == 4 && ins[k1].ops[0].reg == 6 {
        alloc += 2;
        k1 += 1;
    }
    (saved, alloc)
}

/// Words a block pushes at its very end (before a closing BR / JMP): the arguments of a call
/// the compiler shared between branches (MOV #1,-(SP) / BR CALL).  A MOVB into (SP) fills the
/// word the push before it made.
pub fn trailing_pushes(ins: &[Insn]) -> i32 {
    let mut ins = ins;
    if let Some(l) = ins.last() {
        if l.mn == "BR" || l.mn == "JMP" {
            ins = &ins[..ins.len() - 1];
        }
    }
    let mut c = 0;
    for j in ins.iter().rev() {
        match j.ops.last() {
            Some(d) if d.reg == 6 && d.mode == 4 && j.ops.len() <= 2 => c += 1,
            Some(d) if d.reg == 6 && d.mode == 1 && j.ops.len() == 2 && j.mn == "MOVB" => {}
            _ => break,
        }
    }
    c
}
