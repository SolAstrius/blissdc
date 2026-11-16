// SPDX-License-Identifier: Apache-2.0
// PDP-11 / T-11 instruction decoder.
use std::rc::Rc;

#[derive(Clone, Debug)]
pub struct Opnd {
    pub mode: i8,
    pub reg: u8,
    pub x: u16,
    pub addr: Option<u16>,
}

pub type CaseInfo = (u16, usize, u16, Vec<u16>);

#[derive(Clone, Debug)]
pub struct Insn {
    pub pc: u16,
    pub nwords: u16,
    pub mn: String,
    pub ops: Vec<Opnd>,
    pub targets: Vec<u16>,
    pub ret: bool,
    pub stop: bool,
    pub cond: bool,
    pub valid: bool,
    pub case: Option<Rc<CaseInfo>>,
    pub tail: bool,
}

fn op(mode: i8, reg: u8) -> Opnd {
    Opnd { mode, reg, x: 0, addr: None }
}

fn operand(rw: &dyn Fn(u16) -> Option<u16>, pos: &mut u16, nw: &mut u16, mode: u16, reg: u16) -> Result<Opnd, String> {
    let mut o = op(mode as i8, reg as u8);
    let fetch = |pos: &mut u16, nw: &mut u16| -> Result<u16, String> {
        let x = rw(*pos).ok_or_else(|| "TypeError: operand word outside image".to_string())?;
        *pos = pos.wrapping_add(2);
        *nw += 1;
        Ok(x)
    };
    if reg == 7 {
        match mode {
            2 => o.x = fetch(pos, nw)?,
            // (PC): the operand is the next word of the instruction stream (a BLISS-16 peephole that
            // reuses the following index word as a constant)
            1 => o.x = rw(*pos).ok_or_else(|| "TypeError: operand word outside image".to_string())?,
            3 => {
                o.x = fetch(pos, nw)?;
                o.addr = Some(o.x);
            }
            6 | 7 => {
                o.x = fetch(pos, nw)?;
                o.addr = Some(pos.wrapping_add(o.x));
            }
            _ => {}
        }
    } else if mode == 6 || mode == 7 {
        o.x = fetch(pos, nw)?;
    }
    Ok(o)
}

fn double(o: u16) -> &'static str {
    match o {
        0o01 => "MOV", 0o02 => "CMP", 0o03 => "BIT", 0o04 => "BIC", 0o05 => "BIS", 0o06 => "ADD",
        0o11 => "MOVB", 0o12 => "CMPB", 0o13 => "BITB", 0o14 => "BICB", 0o15 => "BISB", 0o16 => "SUB",
        _ => "",
    }
}

fn single(k: u16) -> Option<&'static str> {
    Some(match k {
        0o0050 => "CLR", 0o0051 => "COM", 0o0052 => "INC", 0o0053 => "DEC", 0o0054 => "NEG", 0o0055 => "ADC",
        0o0056 => "SBC", 0o0057 => "TST", 0o0060 => "ROR", 0o0061 => "ROL", 0o0062 => "ASR", 0o0063 => "ASL",
        0o0067 => "SXT",
        0o1050 => "CLRB", 0o1051 => "COMB", 0o1052 => "INCB", 0o1053 => "DECB", 0o1054 => "NEGB", 0o1055 => "ADCB",
        0o1056 => "SBCB", 0o1057 => "TSTB", 0o1060 => "RORB", 0o1061 => "ROLB", 0o1062 => "ASRB", 0o1063 => "ASLB",
        0o1064 => "MTPS", 0o1067 => "MFPS",
        _ => return None,
    })
}

fn branch(k: u16) -> Option<&'static str> {
    Some(match k {
        0o0004 => "BR", 0o0010 => "BNE", 0o0014 => "BEQ", 0o0020 => "BGE", 0o0024 => "BLT", 0o0030 => "BGT",
        0o0034 => "BLE", 0o1000 => "BPL", 0o1004 => "BMI", 0o1010 => "BHI", 0o1014 => "BLOS", 0o1020 => "BVC",
        0o1024 => "BVS", 0o1030 => "BCC", 0o1034 => "BCS",
        _ => return None,
    })
}

pub fn decode(rw: &dyn Fn(u16) -> Option<u16>, pc: u16) -> Result<Insn, String> {
    let w = rw(pc).ok_or_else(|| "TypeError: opcode outside image".to_string())?;
    let mut ins = Insn {
        pc, nwords: 1, mn: String::new(), ops: vec![], targets: vec![], ret: false, stop: false, cond: false,
        valid: true, case: None, tail: false,
    };
    let mut pos = pc.wrapping_add(2);
    let mut nw = 1u16;
    let o = w >> 12;
    if (1..=6).contains(&o) || (0o11..=0o16).contains(&o) {
        let mn = double(o);
        let s = operand(rw, &mut pos, &mut nw, (w >> 9) & 7, (w >> 6) & 7)?;
        let d = operand(rw, &mut pos, &mut nw, (w >> 3) & 7, w & 7)?;
        let ro = matches!(mn, "CMP" | "CMPB" | "BIT" | "BITB");
        if d.mode == 0 && d.reg == 7 && !ro {
            ins.stop = true;
        }
        ins.mn = mn.to_string();
        ins.ops = vec![s, d];
    } else if (w & 0o177000) == 0o074000 {
        let r = (w >> 6) & 7;
        let d = operand(rw, &mut pos, &mut nw, (w >> 3) & 7, w & 7)?;
        ins.mn = "XOR".into();
        ins.ops = vec![op(0, r as u8), d];
    } else if (w & 0o177000) == 0o077000 {
        let r = (w >> 6) & 7;
        let off = w & 0o77;
        let t = pc.wrapping_add(2).wrapping_sub(2 * off);
        ins.mn = "SOB".into();
        ins.ops = vec![op(0, r as u8), Opnd { mode: -1, reg: 255, x: 0, addr: Some(t) }];
        ins.targets = vec![t];
        ins.cond = true;
    } else if (w & 0o177000) == 0o004000 {
        let r = (w >> 6) & 7;
        let d = operand(rw, &mut pos, &mut nw, (w >> 3) & 7, w & 7)?;
        ins.mn = "JSR".into();
        if d.mode == 0 {
            ins.valid = false;
        } else if d.reg == 7 && matches!(d.mode, 1 | 3 | 6) {
            if let Some(a) = d.addr {
                ins.targets = vec![a];
            }
        }
        ins.ops = vec![op(0, r as u8), d];
    } else if (w & 0o177700) == 0o000100 {
        let d = operand(rw, &mut pos, &mut nw, (w >> 3) & 7, w & 7)?;
        ins.mn = "JMP".into();
        ins.stop = true;
        if d.mode == 0 {
            ins.valid = false;
        } else if d.reg == 7 && (d.mode == 6 || d.mode == 3) {
            if let Some(a) = d.addr {
                ins.targets = vec![a];
            }
        }
        ins.ops = vec![d];
    } else if (w & 0o177770) == 0o000200 {
        ins.mn = "RTS".into();
        ins.ops = vec![op(0, (w & 7) as u8)];
        ins.ret = true;
        ins.stop = true;
    } else if (w & 0o177740) == 0o000240 {
        if w == 0o240 {
            ins.mn = "NOP".into();
        } else if w == 0o257 {
            ins.mn = "CCC".into();
        } else if w == 0o277 {
            ins.mn = "SCC".into();
        } else {
            let pre = if w & 0o20 != 0 { "SE" } else { "CL" };
            let mut f = vec![];
            for (b, n) in [(8, "N"), (4, "Z"), (2, "V"), (1, "C")] {
                if w & b != 0 {
                    f.push(format!("{}{}", pre, n));
                }
            }
            ins.mn = f.join("!");
        }
    } else if (w & 0o177400) == 0o104000 {
        ins.mn = "EMT".into();
        ins.ops = vec![Opnd { mode: -2, reg: 255, x: w & 0o377, addr: None }];
    } else if (w & 0o177400) == 0o104400 {
        ins.mn = "TRAP".into();
        ins.ops = vec![Opnd { mode: -2, reg: 255, x: w & 0o377, addr: None }];
    } else if w <= 6 {
        ins.mn = ["HALT", "WAIT", "RTI", "BPT", "IOT", "RESET", "RTT"][w as usize].into();
        if w == 0 || w == 2 || w == 6 {
            ins.stop = true;
            if w != 0 {
                ins.ret = true;
            }
        }
    }
    if ins.mn.is_empty() {
        let hi = w & 0o177400;
        let bkey = hi >> 6;
        if hi != 0 && branch(bkey).is_some() {
            ins.mn = branch(bkey).unwrap().into();
            let off = (w & 0xFF) as u8 as i8 as i32;
            let t = (pc as i32 + 2 + 2 * off) as u16;
            ins.ops = vec![Opnd { mode: -1, reg: 255, x: 0, addr: Some(t) }];
            ins.targets = vec![t];
            if ins.mn == "BR" {
                ins.stop = true;
            } else {
                ins.cond = true;
            }
        } else if let Some(m) = single(w >> 6) {
            ins.mn = m.into();
            let d = operand(rw, &mut pos, &mut nw, (w >> 3) & 7, w & 7)?;
            ins.ops = vec![d];
        } else if (w & 0o177700) == 0o000300 {
            ins.mn = "SWAB".into();
            let d = operand(rw, &mut pos, &mut nw, (w >> 3) & 7, w & 7)?;
            ins.ops = vec![d];
        }
    }
    if ins.mn.is_empty() {
        ins.valid = false;
        ins.mn = ".WORD".into();
        nw = 1;
    }
    ins.nwords = nw;
    Ok(ins)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dec(words: &[u16], pc: u16) -> Insn {
        let w = words.to_vec();
        decode(&move |a: u16| w.get(((a.wrapping_sub(pc)) / 2) as usize).cloned(), pc).unwrap()
    }

    #[test]
    fn double_operand() {
        let i = dec(&[0o010146], 0o1000);
        assert_eq!(i.mn, "MOV");
        assert_eq!((i.ops[0].mode, i.ops[0].reg), (0, 1));
        assert_eq!((i.ops[1].mode, i.ops[1].reg), (4, 6));
        assert_eq!(i.nwords, 1);
        // MOV 4(SP),R0
        let i = dec(&[0o016600, 4], 0o1000);
        assert_eq!((i.mn.as_str(), i.ops[0].mode, i.ops[0].reg, i.ops[0].x, i.nwords), ("MOV", 6, 6, 4, 2));
        // SUB is not a byte op
        assert_eq!(dec(&[0o162705, 0o60], 0).mn, "SUB");
        assert_eq!(dec(&[0o110001], 0).mn, "MOVB");
        // MOV to PC stops the walk; CMP with PC does not
        assert!(dec(&[0o010007], 0).stop);
        assert!(!dec(&[0o020007], 0).stop);
    }

    #[test]
    fn pc_modes() {
        // MOV #123,R1
        let i = dec(&[0o012701, 0o123], 0o2000);
        assert_eq!((i.ops[0].mode, i.ops[0].x, i.nwords), (2, 0o123, 2));
        // JSR PC,X(PC): target relative to the updated PC
        let i = dec(&[0o004767, 0o770], 0o1004);
        assert_eq!(i.mn, "JSR");
        assert_eq!(i.targets, vec![0o2000]);
        // JMP @#addr
        let i = dec(&[0o000137, 0o4000], 0o1000);
        assert!(i.stop);
        assert_eq!(i.targets, vec![0o4000]);
        // MOVB (PC),R0: the next word is a constant, not consumed
        let i = dec(&[0o111700, 0o42], 0o1000);
        assert_eq!((i.ops[0].x, i.nwords), (0o42, 1));
    }

    #[test]
    fn branches() {
        // BNE .+6
        let i = dec(&[0o001002], 0o1000);
        assert_eq!((i.mn.as_str(), i.cond), ("BNE", true));
        assert_eq!(i.targets, vec![0o1006]);
        // BR .-2 (offset -2)
        let i = dec(&[0o000776], 0o1000);
        assert_eq!((i.mn.as_str(), i.stop), ("BR", true));
        assert_eq!(i.targets, vec![0o776]);
        // SOB R1,.-2
        let i = dec(&[0o077102], 0o1006);
        assert_eq!(i.mn, "SOB");
        assert_eq!(i.targets, vec![0o1004]);
        // RTS PC
        let i = dec(&[0o000207], 0);
        assert!(i.ret && i.stop);
    }

    #[test]
    fn misc() {
        assert_eq!(dec(&[0o104401], 0).mn, "TRAP");
        assert_eq!(dec(&[0o000004], 0).mn, "IOT");
        assert_eq!(dec(&[0o000241], 0).mn, "CLC");
        assert_eq!(dec(&[0o000300 | 0o01], 0).mn, "SWAB");
        let i = dec(&[0o007000], 0);
        assert!(!i.valid);
        assert_eq!(i.mn, ".WORD");
        // operand word outside the image
        let w = [0o012700u16];
        assert!(decode(&|a: u16| if a == 0 { Some(w[0]) } else { None }, 0).is_err());
    }
}
