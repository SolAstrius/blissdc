// SPDX-License-Identifier: Apache-2.0
//! PDP-11 disassembly text.
use super::{Insn, Opnd};
use crate::program::{o6, Program};

/// operand in listing syntax, addresses by name (R<octal> when unnamed)
pub fn fmt_op(o: &Opnd, mem: &Program) -> String {
    let r = ["R0", "R1", "R2", "R3", "R4", "R5", "SP", "PC"][o.reg as usize & 7];
    if o.mode < 0 {
        return match o.addr { Some(a) => mem.name_of(a), None => format!("{:o}", o.x) };
    }
    if o.reg == 7 {
        match o.mode {
            2 => return format!("#{:o}", o.x),
            3 => return format!("@#{}", mem.name_of(o.x)),
            6 => return mem.name_of(o.addr.unwrap_or(0)),
            7 => return format!("@{}", mem.name_of(o.addr.unwrap_or(0))),
            _ => {}
        }
    }
    match o.mode {
        0 => r.to_string(),
        1 => format!("({})", r),
        2 => format!("({})+", r),
        3 => format!("@({})+", r),
        4 => format!("-({})", r),
        5 => format!("@-({})", r),
        6 => format!("{:o}({})", o.x, r),
        7 => format!("@{:o}({})", o.x, r),
        _ => format!("?{}", o.mode),
    }
}



/// one listing line: address, octal words, mnemonic and operands
pub fn disasm_line(mem: &Program, i: &Insn) -> String {
    let ws: Vec<String> = (0..i.nwords).map(|k| format!("{:06o}", mem.rw(i.pc.wrapping_add(2 * k)).unwrap_or(0))).collect();
    let ops: Vec<String> = i.ops.iter().map(|o| fmt_op(o, mem)).collect();
    format!("{}  {:<20}  {:<6} {}\n", o6(i.pc), ws.join(" "), i.mn, ops.join(","))
}
