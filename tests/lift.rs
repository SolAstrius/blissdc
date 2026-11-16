// SPDX-License-Identifier: Apache-2.0
//! Lifting small hand-assembled BLISS-16 style routines.
use blissdc::driver::{self, Options};
use blissdc::program::Program;

/// words at octal addresses -> a program with those routines as entries
fn program(code: &[(u16, &[u16])], entries: &[u16]) -> Program {
    let mut img = vec![0u8; 0o10000];
    for (a, ws) in code {
        for (k, w) in ws.iter().enumerate() {
            let p = *a as usize + 2 * k;
            img[p] = (*w & 0xFF) as u8;
            img[p + 1] = (*w >> 8) as u8;
        }
    }
    let mut p = Program::new();
    p.add_bytes("test", img, 0);
    p.entries = entries.iter().cloned().collect();
    p.module = Some("TEST".into());
    p
}

fn decompile(p: Program, opts: Options) -> String {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(move || {
            let mut t = driver::analyze(p).unwrap();
            let want = driver::select(&t, &[], &[]).unwrap();
            driver::decompile_module(&mut t, &opts, &want, "TEST")
        })
        .unwrap()
        .join()
        .unwrap()
}

#[test]
fn stack_parameters_and_value() {
    // MOV 4(SP),R0 / ADD 2(SP),R0 / RTS PC
    let p = program(&[(0o1000, &[0o016600, 4, 0o066600, 2, 0o000207])], &[0o1000]);
    let s = decompile(p, Options::readable());
    assert!(s.starts_with("MODULE TEST =\n"), "{}", s);
    assert!(s.contains("GLOBAL ROUTINE R001000 (A1, A2) ="), "{}", s);
    assert!(s.contains(".A1 + .A2"), "{}", s);
    assert!(!s.contains("NOVALUE"), "{}", s);
}

#[test]
fn if_then_else() {
    // TST 2(SP) / BNE 1$ / MOV #1,R0 / RTS PC / 1$: MOV #2,R0 / RTS PC
    let p = program(&[(0o1000, &[0o005766, 2, 0o001003, 0o012700, 1, 0o000207, 0o012700, 2, 0o000207])], &[0o1000]);
    let s = decompile(p, Options::readable());
    assert!(s.contains("IF .A1 EQL 0"), "{}", s);
    assert!(s.contains("RETURN 1"), "{}", s);
    assert!(s.contains("RETURN 2"), "{}", s);
}

#[test]
fn sob_loop_is_decr() {
    // CLR R0 / MOV 2(SP),R1 / 1$: INC R0 / SOB R1,1$ / RTS PC
    let p = program(&[(0o1000, &[0o005000, 0o016601, 2, 0o005200, 0o077102, 0o000207])], &[0o1000]);
    // without knob 10 the loop's exit (RETURN) stays after the loop
    let mut o = Options::readable();
    o.knob_default &= !(1 << 10);
    let s = decompile(p, o);
    assert!(s.contains("DECR X1 FROM .A1 TO 1 DO"), "{}", s);
}

#[test]
fn register_parameter_linkage() {
    // caller: MOV #5,R0 / JSR PC,2000 / RTS PC     callee: ASL R0 / RTS PC
    let p = program(&[(0o1000, &[0o012700, 5, 0o004767, 0o770, 0o000207]), (0o2000, &[0o006300, 0o000207])], &[0o1000]);
    let s = decompile(p, Options::default());
    assert!(s.contains("LINKAGE L_R0 = JSR (REGISTER = 0);"), "{}", s);
    assert!(s.contains("GLOBAL ROUTINE R002000 (PR0) : L_R0"), "{}", s);
    assert!(s.contains("R002000 (5)"), "{}", s);
}

#[test]
fn case_dispatch_from_symbols() {
    // MOV 2(SP),R0 / ASL R0 / ADD 1100(R0),PC / 1$: MOV #10,R0 / RTS PC / 2$: MOV #20,R0 / RTS PC
    // table at 1100: offsets of 1$ and 2$ from 1012 (the PC after the ADD)
    let code: &[(u16, &[u16])] = &[
        (0o1000, &[0o016600, 2, 0o006300, 0o066007, 0o1100, 0o012700, 0o10, 0o000207, 0o012700, 0o20, 0o000207]),
        (0o1100, &[0, 0o6]),
    ];
    let mut p = program(code, &[0o1000]);
    p.parse("case 001006 001100 2. 001012\n", std::path::Path::new(".")).unwrap();
    let s = decompile(p, Options::readable());
    assert!(s.contains("CASE .A1 FROM 0 TO 1 OF"), "{}", s);
}

#[test]
fn save_helper_prologue() {
    // 1000: JSR R1,$SAV2 (at 3000) / MOV 6(SP)... : with $SAV2 the frame base moves by 6 bytes, so the
    // first stack argument is at 10(SP) after the saves
    let code: &[(u16, &[u16])] = &[
        (0o1000, &[0o004167, 0o1774, 0o016602, 0o10, 0o010200, 0o000207]),
        (0o3000, &[0o000207]),
    ];
    let mut p = program(code, &[0o1000]);
    p.parse("save 003000 2\nlabel 003000 $SAV2\n", std::path::Path::new(".")).unwrap();
    let s = decompile(p, Options::readable());
    assert!(s.contains("GLOBAL ROUTINE R001000 (A1) ="), "{}", s);
}

// ---- regressions found by booting a rebuilt VT240 ROM (the match score could not see them)

#[test]
fn swab_then_byte_store_keeps_the_high_byte() {
    // MOV 2(SP),R0 / SWAB R0 / MOVB R0,@#1200 / RTS PC: the stored byte is A1's high byte.
    // (x ^ 8) is a left shift in BLISS: its low byte would be 0.
    let p = program(&[(0o1000, &[0o016600, 2, 0o000300, 0o110037, 0o1200, 0o000207])], &[0o1000]);
    let s = decompile(p, Options::readable());
    assert!(s.contains("^ -8"), "{}", s);
    assert!(!s.contains("(.A1 ^ 8)"), "{}", s);
}

#[test]
fn bytes_of_a_stack_word_are_fields_of_one_local() {
    // MOV 2(SP),-(SP) / CLR R0 / BISB 1(SP),R0 / TST (SP)+ / RTS PC: R0 = high byte of the pushed word.
    // The odd offset used to become a second local that was never assigned.
    let p = program(&[(0o1000, &[0o016646, 2, 0o005000, 0o156600, 1, 0o005726, 0o000207])], &[0o1000]);
    let s = decompile(p, Options::readable());
    assert!(s.contains("<8,8>"), "{}", s);
    assert!(!s.contains("L1"), "{}", s);
}

#[test]
fn unsaved_register_is_an_output() {
    // caller: JSR PC,2000 / MOV R1,R0 / RTS PC     callee: MOV #7,R1 / RTS PC
    // The callee hands R1 back: it must be in its linkage (EXTERNAL REGISTER), not a local GLOBAL
    // REGISTER, which BLISS would save and restore.
    let p = program(&[(0o1000, &[0o004767, 0o774, 0o010100, 0o000207]), (0o2000, &[0o012701, 7, 0o000207])], &[0o1000]);
    let s = decompile(p, Options::default());
    let callee = &s[s.find("ROUTINE R002000").expect("callee")..];
    assert!(callee.contains("EXTERNAL REGISTER GR1 = 1;"), "{}", s);
}

#[test]
fn thunk_takes_its_arguments_from_the_call_sites() {
    // caller: MOV #5,-(SP) / JSR PC,2000 / TST (SP)+ / RTS PC
    // thunk:  JSR R5,3000 / .WORD 1 / .WORD 4000      dispatcher at 3000
    let code: &[(u16, &[u16])] = &[
        (0o1000, &[0o012746, 5, 0o004767, 0o770, 0o005726, 0o000207]),
        (0o2000, &[0o004567, 0o774, 1, 0o4000]),
        (0o3000, &[0o000207]),
    ];
    let mut p = program(code, &[0o1000]);
    p.parse("thunk 003000\n", std::path::Path::new(".")).unwrap();
    let s = decompile(p, Options::default());
    assert!(s.contains("R002000 (5)"), "{}", s);
}

#[test]
fn local_read_only_in_a_folded_condition_keeps_its_stores() {
    // MOV 2(SP),-(SP) / 1$: MOV (SP),-(SP) / JSR PC,3000 / TST (SP)+ / TST R0 / BEQ 2$ /
    // MOV 6(SP),(SP) / BR 1$ / 2$: TST (SP)+ / RTS PC      3000: MOV 2(SP),R0 / RTS PC
    // The local (A1, then A2) is read only by the call that ends up folded into the loop's IF;
    // its stores must not be dropped as dead.
    let p = program(
        &[
            (0o1000, &[
                0o016646, 2, 0o011646, 0o004767, 0o1766, 0o005726, 0o005700, 0o001403, 0o016616, 6, 0o000767,
                0o005726, 0o000207,
            ]),
            (0o3000, &[0o016600, 2, 0o000207]),
        ],
        &[0o1000],
    );
    let s = decompile(p, Options::readable());
    assert!(s.contains("= .A1;") && s.contains("= .A2;"), "{}", s);
}

#[test]
fn high_byte_sign_extended() {
    // MOV 2(SP),R0 / CLRB R0 / SWAB R0 / MOVB R0,R0 / RTS PC: CLRB clears only the low byte
    let p = program(&[(0o1000, &[0o016600, 2, 0o105000, 0o000300, 0o110000, 0o000207])], &[0o1000]);
    let s = decompile(p, Options::readable());
    assert!(s.contains(".A1<8,8,1>"), "{}", s);
    assert!(!s.contains("RETURN 0"), "{}", s);
}

#[test]
fn shared_call_takes_arguments_pushed_by_its_predecessors() {
    // TST 2(SP) / BEQ 1$ / MOV #1,-(SP) / BR 2$ / 1$: CLR -(SP) / 2$: JSR PC,20000 / TST (SP)+ / RTS PC
    let p = program(
        &[(0o1000, &[0o005766, 2, 0o001403, 0o012746, 1, 0o000401, 0o005046, 0o004767, 0o16756, 0o005726, 0o000207])],
        &[0o1000],
    );
    let s = decompile(p, Options::readable());
    assert!(!s.contains("R020000 ()"), "{}", s);
    assert!(s.contains("R020000 (."), "{}", s);
}

#[test]
fn shared_conditional_branch_tests_each_predecessors_flags() {
    // TST 2(SP) / BNE 1$ / CMP 4(SP),#5 / BR 2$ / 1$: CMP 4(SP),#7 / 2$: BNE 3$ / MOV #1,R0 / RTS PC
    // 3$: CLR R0 / RTS PC
    let p = program(
        &[(0o1000, &[
            0o005766, 2, 0o001004, 0o026627, 4, 5, 0o000403, 0o026627, 4, 7, 0o001003, 0o012700, 1, 0o000207,
            0o005000, 0o000207,
        ])],
        &[0o1000],
    );
    let s = decompile(p, Options::readable());
    assert!(!s.contains("?cc"), "{}", s);
    assert!(s.contains(" 5") && s.contains(" 7"), "{}", s);
}

#[test]
fn empty_countdown_loop_stays_a_loop() {
    // MOV #13,R3 / 1$: MOV #100000,R0 / 2$: SOB R0,2$ / SOB R3,1$ / CLR @#1200 / RTS PC: a delay
    // (the VT240's).  As DECR ... DO 0 BLISS-16 sees the inner loop has no effect and deletes it.
    let p = program(&[(0o1000, &[0o012703, 0o13, 0o012700, 0o100000, 0o077001, 0o077304, 0o005037, 0o1200, 0o000207])], &[0o1000]);
    let s = decompile(p, Options::readable());
    assert!(!s.contains("DO 0;"), "{}", s);
}
