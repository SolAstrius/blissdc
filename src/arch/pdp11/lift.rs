// SPDX-License-Identifier: Apache-2.0
//! PDP-11 instruction lifting: addressing modes to places, instructions to statements, condition
//! codes to relations, the BLISS-16 prologue (JSR R1,$SAVn or individual pushes) to the frame base.
use super::*;
use crate::cfg::*;
use crate::ir::*;
use crate::lift::*;
use crate::program::Program;
use std::collections::{HashMap, HashSet, VecDeque};
use std::rc::Rc;

/// branch mnemonic -> BLISS relation (LSS0/GEQ0: sign of the result)
pub fn br_rel(mn: &str) -> Option<&'static str> {
    Some(match mn {
        "BEQ" => "EQL", "BNE" => "NEQ", "BLT" => "LSS", "BGE" => "GEQ", "BGT" => "GTR", "BLE" => "LEQ",
        "BHI" => "GTRU", "BLOS" => "LEQU", "BCC" => "GEQU", "BCS" => "LSSU", "BMI" => "LSS0", "BPL" => "GEQ0",
        _ => return None,
    })
}

pub(crate) enum Ea {
    Imm(E),
    Mem(E, bool),
    Loc(Loc),
    Sp(i32),
}

#[derive(Clone)]
pub enum Flags {
    In,
    Bad,
    Cmp(E, E),
    Tst(E),
    Bit(E, E),
    /// carry = low bit of the value (ROR before BCC/BCS: BLISS's truth test IF .X)
    Low(E),
}

fn cmp_expr(fl: &Flags, mn: &str) -> E {
    let mut rel = br_rel(mn).unwrap();
    let (mut a, mut b, is_cmp) = match fl {
        Flags::Cmp(a, b) => (a.clone(), b.clone(), true),
        Flags::Tst(a) => (a.clone(), c(0), false),
        Flags::Bit(a, b) => (op("AND", a.clone(), b.clone()), c(0), false),
        Flags::Low(a) if mn == "BCS" => return E::Rel("LOW", Rc::new(a.clone()), Rc::new(c(0))),
        Flags::Low(a) if mn == "BCC" => return E::Rel("NLOW", Rc::new(a.clone()), Rc::new(c(0))),
        _ => return unk("?cc"),
    };
    if rel == "LSS0" || rel == "GEQ0" {
        rel = if rel == "LSS0" { "LSS" } else { "GEQ" };
        if is_cmp {
            a = sub(a, b);
            b = c(0);
        }
    }
    E::Rel(rel, Rc::new(a), Rc::new(b))
}

fn val(p: &Ea) -> E {
    match p {
        Ea::Loc(l) => E::Loc(*l),
        Ea::Imm(e) => e.clone(),
        Ea::Mem(a, b) => E::Fetch(Rc::new(a.clone()), *b),
        Ea::Sp(d) => E::Frame(*d),
    }
}

fn fix_post(out: Vec<Stmt>) -> Vec<Stmt> {
    let mut res = vec![];
    let mut pend: Vec<(Loc, u16)> = vec![];
    for s in out {
        if let Stmt::Post(l, k) = s {
            pend.push((l, k));
            continue;
        }
        res.push(s);
        for (l, k) in pend.drain(..) {
            res.push(Stmt::Set(Place::Loc(l), add(E::Loc(l), E::C(k))));
        }
    }
    for (l, k) in pend {
        res.push(Stmt::Set(Place::Loc(l), add(E::Loc(l), E::C(k))));
    }
    res
}

impl Lifter {
    pub(crate) fn slot(&mut self, off: i32) -> Loc {
        if off >= 2 {
            let k = (off - 2) / 2;
            self.maxparam = self.maxparam.max(k + 1);
            return Loc::P(k);
        }
        Loc::S(-off)
    }


    pub(crate) fn analyze_prologue(&mut self, r: &Routine, mem: &Program) {
        let ins = &r.blocks[&r.entry].ins;
        let mut d = 0;
        let mut i0 = 0;
        if !ins.is_empty() && ins[0].mn == "JSR" && ins[0].ops[0].reg == 1 && !ins[0].targets.is_empty() {
            if let Some(&n) = mem.saves.get(&ins[0].targets[0]) {
                self.saved = n;
                d = -(2 * n + 2);
                i0 = 1;
            }
        }
        if self.saved == 0 {
            while i0 < ins.len() && ins[i0].mn == "MOV" && ins[i0].ops[0].mode == 0
                && (1..=5).contains(&ins[i0].ops[0].reg) && ins[i0].ops[1].mode == 4 && ins[i0].ops[1].reg == 6
            {
                d -= 2;
                self.saved += 1;
                i0 += 1;
            }
        }
        self.frame_base = d;
        self.skip = i0;
    }


    /// a source operand: only read (byte reads of stack words become fields of the local, see ea)
    pub(crate) fn ea_src(&mut self, out: &mut Vec<Stmt>, o: &Opnd, depth: &mut i32, byte: bool) -> Result<Ea, String> {
        self.ea_is_src = true;
        let r = self.ea(out, o, depth, byte);
        self.ea_is_src = false;
        r
    }

    pub(crate) fn ea(&mut self, out: &mut Vec<Stmt>, o: &Opnd, depth: &mut i32, byte: bool) -> Result<Ea, String> {
        let (m, rn) = (o.mode, o.reg);
        if rn == 6 && byte && (m == 1 || m == 6) && self.ea_is_src {
            // A byte read of a local stack word (`MOV R0,-(SP)` then `BISB (SP),R1` / `BISB 1(SP),R0`):
            // a byte fetch through the slot's address, the high byte as address + 1, so the word and
            // its bytes stay one variable; printed as .L<0,8> / .L<8,8>.  A separate slot per odd
            // offset was never assigned (the word store went to the even one).  Parameters keep their
            // slots; byte stores (argument pushes such as CLR -(SP) / MOVB x,(SP)) are not touched.
            let off = *depth + if m == 6 { sgn(o.x) } else { 0 };
            if off < 2 {
                let base = off & !1;
                let a = if off & 1 != 0 { E::Op("+", Rc::new(E::Frame(base)), Rc::new(E::C(1))) } else { E::Frame(base) };
                return Ok(Ea::Mem(a, true));
            }
        }
        if rn == 7 {
            match m {
                2 => return Ok(Ea::Imm(E::C(o.x))),
                1 => return Ok(Ea::Imm(E::C(if byte { o.x & 0o377 } else { o.x }))),
                3 => return Ok(Ea::Mem(E::G(o.x), byte)),
                6 => return Ok(Ea::Mem(E::G(o.addr.unwrap_or(0)), byte)),
                7 => return Ok(Ea::Mem(E::Fetch(Rc::new(E::G(o.addr.unwrap_or(0))), false), byte)),
                _ => return Ok(Ea::Mem(unk(&format!("?pcmode{}", m)), byte)),
            }
        }
        if rn == 6 {
            return Ok(match m {
                0 => Ea::Sp(*depth),
                1 => Ea::Loc(self.slot(*depth)),
                2 => {
                    let n = self.slot(*depth);
                    *depth += 2;
                    Ea::Loc(n)
                }
                4 => {
                    *depth -= 2;
                    Ea::Loc(self.slot(*depth))
                }
                6 => Ea::Loc(self.slot(*depth + sgn(o.x))),
                7 => Ea::Mem(E::Loc(self.slot(*depth + sgn(o.x))), byte),
                _ => return Err(format!("ValueError: SP mode {}", m)),
            });
        }
        if rn > 7 {
            return Err("TypeError: operand without register".into());
        }
        let rl = if self.gregs.contains(&(rn as i32)) { Loc::Q(rn as i32 + 10) } else { Loc::R(rn as i32) };
        let reg = E::Loc(rl);
        let step = if byte && rn < 6 { 1 } else { 2 };
        Ok(match m {
            0 => Ea::Loc(rl),
            1 => Ea::Mem(reg, byte),
            2 => {
                out.push(Stmt::Post(rl, step as u16));
                Ea::Mem(reg, byte)
            }
            3 => {
                out.push(Stmt::Post(rl, 2));
                Ea::Mem(E::Fetch(Rc::new(reg), false), byte)
            }
            4 => {
                out.push(Stmt::Set(Place::Loc(rl), add(reg.clone(), c(-step))));
                Ea::Mem(reg, byte)
            }
            5 => {
                out.push(Stmt::Set(Place::Loc(rl), add(reg.clone(), c(-2))));
                Ea::Mem(E::Fetch(Rc::new(reg), false), byte)
            }
            6 => Ea::Mem(add(reg, E::C(o.x)), byte),
            7 => Ea::Mem(E::Fetch(Rc::new(add(reg, E::C(o.x))), false), byte),
            _ => return Err("TypeError: bad operand mode".into()),
        })
    }


    pub fn lift(&mut self, r: &Routine, mem: &Program, info: &HashMap<u16, Info>) -> Result<(), String> {
        self.analyze_prologue(r, mem);
        self.depth_in.insert(r.entry, self.frame_base);
        let mut work: VecDeque<u16> = VecDeque::new();
        work.push_back(r.entry);
        let mut done: HashSet<u16> = HashSet::new();
        while let Some(bpc) = work.pop_front() {
            if !done.insert(bpc) {
                continue;
            }
            let b = &r.blocks[&bpc];
            let mut out = vec![];
            let mut flags = Flags::In;
            let mut depth = self.depth_in[&bpc];
            let ins = if bpc == r.entry { &b.ins[self.skip.min(b.ins.len())..] } else { &b.ins[..] };
            if bpc == r.entry && self.bind_regs {
                if let Some(me) = info.get(&r.entry) {
                    self.gregs = me.globals.iter().chain(me.gdecl.iter()).cloned().collect();
                }
                if let Some(me) = info.get(&r.entry) {
                    for &k in &me.regparams {
                        out.push(Stmt::Set(Place::Loc(Loc::R(k)), E::Loc(Loc::Q(k))));
                    }
                }
            }
            for i in ins {
                self.step(&mut out, &mut flags, i, &mut depth, b.start, mem, info)?;
            }
            self.stmts.insert(bpc, fix_post(out));
            self.order.push(bpc);
            self.flags_out.insert(bpc, flags);
            for &(t, _) in &b.succ {
                self.depth_in.entry(t).or_insert(depth);
                work.push_back(t);
            }
        }
        let preds = preds_of(r);
        let keys: Vec<u16> = self.bcond.keys().cloned().collect();
        for bpc in keys {
            let mn = match &self.bcond[&bpc] {
                E::Pending(mn) => *mn,
                _ => continue,
            };
            let mut per: Vec<(u16, E)> = vec![];
            for &p in preds.get(&bpc).map(|v| v.as_slice()).unwrap_or(&[]) {
                let v = match self.flags_out.get(&p) {
                    Some(f) => cmp_expr(f, mn),
                    None => unk("?cc"),
                };
                if !per.iter().any(|(q, _)| *q == p) {
                    per.push((p, v));
                }
            }
            if !per.is_empty() && per.iter().all(|(_, v)| *v == per[0].1) {
                self.bcond.insert(bpc, per[0].1.clone());
            } else {
                self.bcond.insert(bpc, unk("perpred"));
                self.bcond_pred.insert(bpc, per.into_iter().collect());
            }
        }
        self.mark_addressed();
        Ok(())
    }


    pub(crate) fn emit_set(&mut self, out: &mut Vec<Stmt>, flags: &mut Flags, d: Ea, e: E) {
        match d {
            Ea::Sp(_) => {
                out.push(Stmt::Unk("write to ('sp',)".into()));
                *flags = Flags::Bad;
            }
            Ea::Imm(x) => {
                out.push(Stmt::Unk(format!("write to ('imm', {})", pyrepr(&x))));
                *flags = Flags::Bad;
            }
            Ea::Loc(l) => {
                // CLRB R0 / INCB R0 / BISB R1,R0: the register's high byte stays
                let e = if std::mem::take(&mut self.byte_reg) && matches!(l, Loc::R(_) | Loc::Q(_)) {
                    match e {
                        E::C(k) if k & 0o377 == 0 => op("AND", E::Loc(l), c(0o177400u16 as i32)),
                        E::C(k) => op("OR", op("AND", E::Loc(l), c(0o177400u16 as i32)), c((k & 0o377) as i32)),
                        e => op("OR", op("AND", E::Loc(l), c(0o177400u16 as i32)), op("AND", e, c(0o377))),
                    }
                } else { e };
                out.push(Stmt::Set(Place::Loc(l), e));
                *flags = Flags::Tst(E::Loc(l));
            }
            Ea::Mem(a, b) => {
                *flags = Flags::Tst(E::Fetch(Rc::new(a.clone()), b));
                out.push(Stmt::Set(Place::Mem(a, b), e));
            }
        }
    }


    pub(crate) fn emit_pre(&mut self, out: &mut Vec<Stmt>, flags: &mut Flags, pre: Vec<Stmt>, d: Ea, e: E) {
        let (posts, sets): (Vec<Stmt>, Vec<Stmt>) = pre.into_iter().partition(|x| matches!(x, Stmt::Post(..)));
        out.extend(sets);
        self.emit_set(out, flags, d, e);
        out.extend(posts);
    }


    #[allow(clippy::too_many_arguments)]
    pub(crate) fn step(&mut self, out: &mut Vec<Stmt>, flags: &mut Flags, i: &Insn, depth: &mut i32, bstart: u16, mem: &Program,
            info: &HashMap<u16, Info>) -> Result<(), String> {
        let mn = i.mn.as_str();
        let byte = mn.ends_with('B') && mn != "SWAB" && mn != "SUB";
        let ops = &i.ops;
        // BISB / BICB from memory or an immediate leave the high byte alone as a word operation would;
        // from a register, and CLRB / INCB / COMB ..., the register's high byte must be kept explicitly
        self.byte_reg = byte && ops.last().map(|o| o.mode == 0 && o.reg < 6).unwrap_or(false)
            && (matches!(mn, "CLRB" | "INCB" | "DECB" | "NEGB" | "COMB" | "ASLB" | "ASRB" | "ROLB" | "RORB" | "ADCB" | "SBCB")
                || (matches!(mn, "BISB" | "BICB") && ops[0].mode == 0));
        if mn == "MOV" || mn == "MOVB" {
            let mut pre = vec![];
            let s = self.ea_src(&mut pre, &ops[0], depth, byte)?;
            let mut sv = val(&s);
            if byte && (matches!(s, Ea::Mem(..)) || (ops[0].mode == 0 && ops[0].reg < 6)) {
                sv = E::Ext8(Rc::new(sv));
            }
            let d = self.ea(&mut pre, &ops[1], depth, byte)?;
            if byte && matches!(d, Ea::Mem(..)) {
                if let E::Ext8(inner) = &sv {
                    sv = (**inner).clone();
                }
            }
            // MOVB into a stack slot replaces only its low byte (CLR -(SP) / MOVB X,(SP): zero-extended X)
            if byte && ops[1].reg == 6 {
                if let Ea::Loc(l) = &d {
                    let lo = match &sv { E::Ext8(inner) => (**inner).clone(), x => op("AND", x.clone(), c(0o377)) };
                    sv = op("OR", op("AND", E::Loc(*l), c(0o177400u16 as i32)), lo);
                }
            }
            self.emit_pre(out, flags, pre, d, sv);
            return Ok(());
        }
        if mn == "CLR" || mn == "CLRB" {
            let mut pre = vec![];
            let d = self.ea(&mut pre, &ops[0], depth, byte)?;
            self.emit_pre(out, flags, pre, d, c(0));
            return Ok(());
        }
        if mn == "TST" || mn == "TSTB" {
            if ops[0].reg == 6 && (ops[0].mode == 2 || ops[0].mode == 4) {
                *depth += if ops[0].mode == 2 { 2 } else { -2 };
                if ops[0].mode == 4 {
                    self.slot(*depth);
                }
                return Ok(());
            }
            let mut pre = vec![];
            let s = self.ea_src(&mut pre, &ops[0], depth, byte)?;
            out.extend(pre);
            *flags = Flags::Tst(val(&s));
            return Ok(());
        }
        if matches!(mn, "CMP" | "CMPB" | "BIT" | "BITB") {
            if mn == "CMP" && ops[0].mode == 2 && ops[0].reg == 6 && ops[1].mode == 2 && ops[1].reg == 6 {
                *depth += 4;
                return Ok(());
            }
            let mut pre = vec![];
            let a = val(&self.ea_src(&mut pre, &ops[0], depth, byte)?);
            let bb = val(&self.ea_src(&mut pre, &ops[1], depth, byte)?);
            out.extend(pre);
            *flags = if mn.starts_with("CMP") { Flags::Cmp(a, bb) } else { Flags::Bit(a, bb) };
            return Ok(());
        }
        if i.case.is_some() {
            // ADD tbl(Rn),PC: the index is the source register
            self.bcase.insert(bstart, E::Loc(Loc::R(ops[0].reg as i32)));
            return Ok(());
        }
        if (mn == "ADD" || mn == "SUB") && ops[1].mode == 0 && ops[1].reg == 6 && ops[0].mode == 2 && ops[0].reg == 7 {
            *depth += if mn == "ADD" { sgn(ops[0].x) } else { -sgn(ops[0].x) };
            return Ok(());
        }
        if matches!(mn, "ADD" | "SUB" | "BIS" | "BIC" | "BISB" | "BICB" | "XOR") {
            let mut pre = vec![];
            let s = val(&self.ea_src(&mut pre, &ops[0], depth, byte)?);
            let d = self.ea(&mut pre, &ops[1], depth, byte)?;
            let mut dv = val(&d);
            // ADD SP,x where x was just set to a constant k: x = address of frame slot (sp + k)
            if mn == "ADD" && matches!(s, E::Frame(_)) {
                if let Ea::Loc(dl) = &d {
                    for st in out.iter().rev() {
                        match st {
                            Stmt::Set(Place::Loc(l), E::C(k)) if l == dl => {
                                dv = E::C(*k);
                                break;
                            }
                            Stmt::Set(Place::Loc(l), _) if l == dl => break,
                            _ => {}
                        }
                    }
                }
            }
            let e = if mn == "ADD" {
                add(dv, s)
            } else if mn == "SUB" {
                sub(dv, s)
            } else if mn.starts_with("BIS") {
                op("OR", dv, s)
            } else if mn.starts_with("BIC") {
                let m = if let E::C(v) = s { E::C(!v) } else { E::Un("NOT", Rc::new(s)) };
                op("AND", dv, m)
            } else {
                op("XOR", dv, s)
            };
            self.emit_pre(out, flags, pre, d, e);
            return Ok(());
        }
        if mn == "ROR" && ops[0].mode == 0 {
            // the BLISS truth test: the register is a dead temporary, only the carry matters
            let rl = if self.gregs.contains(&(ops[0].reg as i32)) { Loc::Q(ops[0].reg as i32 + 10) } else { Loc::R(ops[0].reg as i32) };
            *flags = Flags::Low(E::Loc(rl));
            return Ok(());
        }
        // MTPS / MFPS: BLISS-16 builtins (processor priority)
        if mn == "MTPS" || mn == "MFPS" {
            let mut pre = vec![];
            let d = self.ea(&mut pre, &ops[0], depth, true)?;
            if mn == "MTPS" {
                out.extend(pre);
                out.push(Stmt::Do(E::Call(Rc::from("MTPS"), vec![val(&d)])));
            } else {
                self.emit_pre(out, flags, pre, d, E::Call(Rc::from("MFPS"), vec![]));
            }
            *flags = Flags::Bad;
            return Ok(());
        }
        if mn == "SOB" {
            let rl = if self.gregs.contains(&(ops[0].reg as i32)) { Loc::Q(ops[0].reg as i32 + 10) } else { Loc::R(ops[0].reg as i32) };
            out.push(Stmt::Set(Place::Loc(rl), add(E::Loc(rl), c(-1))));
            self.bcond.insert(bstart, E::Rel("NEQ", Rc::new(E::Loc(rl)), Rc::new(c(0))));
            *flags = Flags::Bad;
            return Ok(());
        }
        if matches!(mn, "INC" | "DEC" | "NEG" | "COM" | "ASL" | "ASR" | "SWAB" | "INCB" | "DECB" | "COMB" | "NEGB"
            | "ASLB" | "ASRB" | "ROL" | "ROR" | "ADC" | "SBC" | "SXT")
        {
            let mut pre = vec![];
            let d = self.ea(&mut pre, &ops[0], depth, byte)?;
            let dv = val(&d);
            let key = if mn != "SWAB" { mn.trim_end_matches('B') } else { mn };
            let e = match key {
                "INC" => add(dv, c(1)),
                "DEC" => add(dv, c(-1)),
                "NEG" => E::Un("-", Rc::new(dv)),
                "COM" => E::Un("NOT", Rc::new(dv)),
                "ASL" => op("^", dv, c(1)),
                "ASR" => op("^", dv, c(-1)),
                "SWAB" => E::Swab(Rc::new(dv)),
                _ => E::Unk(format!("?{}", mn), vec![dv]),
            };
            self.emit_pre(out, flags, pre, d, e);
            return Ok(());
        }
        if mn == "JSR" {
            if ops[0].reg == 7 && !i.targets.is_empty() {
                let t = i.targets[0];
                let callee = info.get(&t);
                let mut nargs = callee.map(|x| x.nparams).unwrap_or(0);
                // arguments are words pushed below the saved registers; a call made with fewer
                // (BLISS does not check) must not pick up the register save area
                while nargs > 0 && *depth + 2 * (nargs - 1) >= self.frame_base && self.frame_base < 0 {
                    nargs -= 1;
                }
                let mut nm = mem.name_of(t);
                if self.fin && READABLE.with(|r| r.get()) && nm.starts_with('R') {
                    nm = match mem.ovl_name(t, i.pc) {
                        Some(o) => o.replace(".", "_"),
                        None if mem.is_banked(t) => format!("OV_{}", o6(t)),
                        None => nm,
                    };
                }
                let name: Rc<str> = Rc::from(nm.as_str());
                let mut args: Vec<E> = (0..nargs).map(|k| E::Loc(self.slot(*depth + 2 * k))).collect();
                args.reverse();
                if let Some(c) = callee {
                    let mut regs: Vec<E> = c.regparams.iter().map(|&k| E::Loc(Loc::R(k))).collect();
                    regs.extend(args);
                    args = regs;
                }
                let call = E::Call(name, args);
                if callee.map(|x| !x.returns).unwrap_or(false) && self.fin {
                    out.push(Stmt::Do(call));
                    out.push(Stmt::Set(Place::Loc(Loc::R(0)), unk("?clobbered")));
                } else {
                    out.push(Stmt::Set(Place::Loc(Loc::R(0)), call));
                }
                *flags = Flags::Bad;
                return Ok(());
            }
            out.push(Stmt::Unk(format!("JSR R{}", ops[0].reg)));
            return Ok(());
        }
        if br_rel(mn).is_some() {
            let cnd = match flags {
                Flags::In => E::Pending(br_rel_key(mn)),
                Flags::Bad => unk("?cc"),
                f => cmp_expr(f, mn),
            };
            self.bcond.insert(bstart, cnd);
            return Ok(());
        }
        if mn == "BR" || (mn == "JMP" && !i.targets.is_empty() && !i.tail) {
            return Ok(());
        }
        if mn == "RTS" {
            out.push(Stmt::Ret(E::Loc(Loc::R(0))));
            return Ok(());
        }
        if mn == "JMP" {
            out.push(Stmt::Tail(match i.targets.first() {
                Some(&t) => mem.name_of(t),
                None => "?".to_string(),
            }));
            return Ok(());
        }
        out.push(Stmt::Unk(mn.to_string()));
        Ok(())
    }

}

fn br_rel_key(mn: &str) -> &'static str {
    match mn {
        "BEQ" => "BEQ", "BNE" => "BNE", "BLT" => "BLT", "BGE" => "BGE", "BGT" => "BGT", "BLE" => "BLE",
        "BHI" => "BHI", "BLOS" => "BLOS", "BCC" => "BCC", "BCS" => "BCS", "BMI" => "BMI", _ => "BPL",
    }
}
