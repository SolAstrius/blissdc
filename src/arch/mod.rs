// SPDX-License-Identifier: Apache-2.0
//! Architecture back ends.
//!
//! Everything that depends on the instruction set lives under `arch::<isa>`; the rest of the crate
//! (CFG, dataflow cleanup, structuring, printing, module emission, scoring) reaches it only through
//! `arch::target`.  A back end provides:
//!
//! - the decoder: `decode`, `Insn` (with the control-flow fields `targets`, `ret`, `stop`, `cond`,
//!   `case`, `tail`) and `Opnd`;
//! - control-flow predicates on `Insn`: `is_call`/`call_target`, `is_jsr`, `is_return`, `is_jump`,
//!   `is_branch`, `is_cond_branch`, `is_hard_stop`;
//! - the compiler's idioms: `Insn::case_table` (CASE dispatch), `saved_regs` and `frame_layout`
//!   (register-save helpers and the prologue), `pushed_args` (argument count at a call site),
//!   `Insn::is_macro_marker` (instructions the compiler never emits), `Insn::is_thunk_call`;
//! - the lifter: `impl Lifter { fn lift(..) }` turning blocks into `ir::Stmt`s with condition
//!   expressions (`Lifter::bcond`, `bcase`), stack slots as `Loc::P`/`Loc::S`, registers as `Loc::R`;
//! - disassembly text: `fmt_op`, `disasm_line`.
//!
//! Only `pdp11` exists.  A VAX (BLISS-32) or PDP-10 (BLISS-36) back end would add a module with the
//! same names and switch `target`; the IR's 16-bit addresses (`u16`) would have to widen first.
pub mod pdp11;
pub use pdp11 as target;
