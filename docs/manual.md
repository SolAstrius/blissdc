# blissdc manual

## BLISS-16

BLISS is DEC's system implementation language (Wulf et al., CMU, 1970). BLISS-16 is the PDP-11
member of DEC's Common BLISS family (BLISS-16, -32 for the VAX, -36 for the PDP-10). It was a
cross-compiler hosted on TOPS-10/20 and VMS, used inside DEC for PDP-11 systems software such as
the DECnet MCB and RSX components, and for firmware such as the VT240's.

Features the decompiler has to recover from its code:

- expression language: every name is an address and `.X` fetches; assignments, `IF`, `CASE`,
  `SELECT`, loops (`WHILE`, `UNTIL`, `DO … UNTIL`, `INCR`, `DECR`), labelled blocks left with `LEAVE`;
- field references `.X<pos,size,sign>`, vectors `X[i]`;
- `LINKAGE`s that pass parameters in registers (`JSR (REGISTER = 0)`) and share `GLOBAL` registers
  between caller and callee (`EXTERNAL REGISTER GR2 = 2`);
- `REGISTER` and `LOCAL` variables, value-returning and `NOVALUE` routines;
- builtins such as `MTPS`/`MFPS` (processor priority);
- the code generator's idioms: `JSR R1,$SAVn` register-save helpers (or individual pushes),
  `ADD tbl(Rn),PC` CASE dispatch through a table of PC-relative offsets, caller-pops argument
  cleanup (`ADD #n,SP`, `CMP (SP)+,(SP)+`, `TST (SP)+`), `ROR R`/`BCC` as the truth test, `SOB`
  for `DECR`, `BICB`/`BISB` for one-bit field stores, `CLRB`/`SWAB`/`MOVB` for a sign-extended
  high byte, cross-jumping of common tails (including calls whose arguments the branches push).

## How it works

1. **Program.** A 16-bit address space assembled from image files (whole files at an address, or
   windows of files for mapped/banked systems), plus what is known from outside: entry points, names,
   case tables, register-save helpers, hints. See [Project files](#project-files).
2. **Routine discovery.** From the entry points, routines are walked instruction by instruction
   (branches, `JMP`, case tables) and every `JSR PC` target becomes another routine. A `JMP` to
   another routine's entry is a tail call. Each routine becomes a CFG of basic blocks.
3. **Linkage inference.** Each routine is lifted to a simple IR (assignments to registers `R0..R5`,
   frame slots, memory; conditions from the condition codes). Stack parameters come from the frame
   offsets read above the return address. Register parameters start as every register read before
   written and shrink to those every caller sets (greatest fixpoint over the call graph). A register
   parameter the callee does not save, and that some caller only passes through, becomes a linkage
   `GLOBAL` register. A routine returns a value if some caller uses `R0` after the call or it loads
   `R0` right before returning. Routines containing `IOT`, `EMT`, `TRAP`, `RTI` or `RTT` are
   hand-written MACRO: no stack parameters of their own, registers taken from the callers.
4. **Lifting and cleanup.** Per routine: copy propagation, dead code elimination, folding single-use
   temporaries into expressions, splitting registers and stack temporaries into separate variables per
   def-use web, `BIC`/`BIS` pairs and single `BIC`/`BIS` on memory into field stores.
5. **Structuring.** Loops from dominator back edges and from the remaining retreating edges of the
   depth-first order (irreducible flow, e.g. a branch cross-jumped into a loop test), post-dominators
   for `IF` joins, short-circuit conditions, `CASE` from dispatch tables, labelled blocks with `LEAVE`
   where the flow is not structured.
6. **Printing.** Fields, vectors, address-of-local, `INCR`/`DECR`/`UNTIL` forms, then a text pass
   that removes redundant `BEGIN`/`END` and dead `LEAVE`s, and hoists `IF c THEN LEAVE … ELSE body`
   into `IF c THEN LEAVE …; body`. Each module gets `LINKAGE`, `FORWARD ROUTINE`, `BUILTIN`,
   `EXTERNAL ROUTINE` and `EXTERNAL` declarations.

Where several BLISS sources compile to the same structure but to different code, the choice is a
**knob**: a bit in a per-routine word (see [Knobs](#knobs)). `blissdc search` compiles the variants and
keeps, per routine, the bits whose code is closer to the original.

## Building

```
cargo build --release        # target/release/blissdc
cargo test --release
```

Rust stable; the only dependency is clap.

## Usage

Every command that reads a program takes the same input options: `-p FILE` (project file,
repeatable), `--image FILE@ADDR`, `--entry ADDR[=NAME]`, `--own RANGE`, `--banked RANGE`. They can
be mixed; command-line entries and names come after the project files. Numbers are octal unless
written `0x…` (hex) or with a trailing `.` (decimal). A range is `LO-HI` (HI exclusive, up to
`200000`) or `LO+LEN`.

```
$ blissdc --help
Decompile PDP-11 code produced by DEC's BLISS-16 compiler back to BLISS source

Usage: blissdc <COMMAND>

Commands:
  disasm     Disassemble routines or an address range
  routines   List discovered routines and their inferred linkages
  decompile  Decompile routines to BLISS-16 source
  map        Write the per-instruction map used by `score`
  score      Score compiled BLISS-16 listings against the original code
  compile    Run the external BLISS-16 compiler on .b16 files
  search     Search knob bits per routine by compiling variants and scoring them
  project    Write the input (project files, images, options) as one project file
  help       Print this message or the help of the given subcommand(s)
```

The examples below use `examples/demo`, a small hand-assembled image whose listing is in
`demo.proj`.

### A raw image

Only an image and an entry point are needed:

```
$ blissdc routines --image examples/demo/demo.bin@0 --entry 1000=MAIN
addr    name                     insns words  arg regs           globals    declares   kind
001000  MAIN                         7    11  0   -              -          -          novalue
001100  R001100                      2     2  0   R0             -          -          value
001200  R001200                      3     5  1   -              -          -          value
```

`R001200` stops after three instructions: its `ADD tbl(R0),PC` dispatch is followed only when the
case table is given, which the project file does.

### A project file

```
$ blissdc routines -p examples/demo/demo.proj
addr    name                     insns words  arg regs           globals    declares   kind
001000  MAIN                         7    11  0   -              -          -          novalue
001100  DOUBLE                       2     2  0   R0             -          -          value
001200  PICK                         7    11  1   -              -          -          value
001400  FIRST                        4     6  1   -              -          -          value
001500  SETPRI                       2     3  0   -              -          -          novalue

$ blissdc disasm -p examples/demo/demo.proj FIRST
; 001400 FIRST
001400  004167 001374         JSR    R1,$SAV2
001404  016602 000010         MOV    10(SP),R2
001410  010200                MOV    R2,R0
001412  000207                RTS    PC

$ blissdc decompile -p examples/demo/demo.proj --readable MAIN FIRST
MODULE DEMO =
BEGIN

LINKAGE L_R0 = JSR (REGISTER = 0);
FORWARD ROUTINE
    FIRST,
    MAIN : NOVALUE;
EXTERNAL ROUTINE
    DOUBLE : L_R0,
    PICK;
EXTERNAL
    RESULT;

GLOBAL ROUTINE MAIN : NOVALUE =
    BEGIN
    RESULT = PICK (DOUBLE (3));
    RETURN;
    END;

GLOBAL ROUTINE FIRST (A1) =
    BEGIN
    RETURN .A1;
    END;

END
ELUDOM
```

Routines are named from the labels, else `R<octal address>`; globals `G<octal>` (or their symbol
name with `--readable`). Parameters are `A1..An` (stack, in BLISS order), `PRk` (register `k`),
`GRk` (linkage global); locals `Xk`/`Xk_n` (from register `k`) and `Lk`/`Lk_n` (frame offset `k`).

`disasm --range 1000-1100` disassembles linearly instead of by routine. `routines --all` also lists
routines outside the `own` ranges.

### decompile

```
blissdc decompile [INPUT] [ROUTINE...] [--readable | --match] [--knobs FILE|N]
                  [--batch N] [-o FILE] [-x NAME]... [--map FILE] [--module NAME] [--environment SW]
```

- `ROUTINE`: octal address or name; default every routine whose entry is in an `own` range
  (all mapped memory when no `own` range is given). Overlay thunks are left out.
- `--match` (default): source meant to recompile to the original code. Default knobs 153473.
- `--readable`: names and comments from the `sym`/`comment` lines, printable characters in
  comparisons as `%C'x'`, calls into banked windows named per call site (`banklabel`, else
  `OV_<addr>`), knobs 22273 (idioms on, pinning/frame-vector/OPTLEVEL tricks off). `--knobs` is
  ignored.
- `--knobs FILE` (lines `ROUTINE value`, value decimal, routine as printed, e.g. `PICK`) or
  `--knobs N` (one decimal value for every routine).
- `--batch N`: modules of at most N routines in `STEM_01.b16`, `STEM_02.b16`, … (stem from `-o`,
  default the module name). BLISS-16 runs out of dynamic memory on large modules; 25 works. Routines
  with knob 16 go into separate `OPTLEVEL = 0` modules after the others.
- `--module`: module name (first 6 characters; 4 plus a number with `--batch`).
- `--environment`: `ENVIRONMENT (…)` switch, e.g. `T11`; the default is none. It changes code
  generation (the T-11 has no EIS: without the right switch the compiler emits `ASH`).

Routines that fail to structure are reported on stderr as `! ADDR NAME: message` and left out.

### project

`blissdc project [INPUT] -o FILE` writes everything the input options and project files describe as
one project file, in a fixed order with absolute image paths. It is the form an importer's output
or a set of files plus command-line additions can be saved in.

### map, score

```
blissdc map [INPUT] [ROUTINE...] -o task.map
blissdc score task.map M_01.LST M_02.LST ...
blissdc score task.map M_*.LST --routine PICK
```

The map has one line per original instruction: routine, address, octal words, disassembly.
`score` reads BLISS-16 listings (`PC<TAB>WORDS<TAB>TEXT` lines; sections start at the routine's
`NAME::` label), aligns each routine's instructions with the original by first word (the same
algorithm as Python's `difflib.SequenceMatcher`), and counts an aligned pair as exact when every
word agrees. Relocated words (marked `G`, `V`, `'`, …) are wildcards; `JSR PC` compares the target
name, since displacements depend on how routines are packed into modules.

The report has one line per routine (`NAME rom N mine N exact N  P%`), then the totals, here for the
VT240 PARSER task:

```
TOTAL routines 119 (compiled 119), ROM instructions 4369, exact 3667 (83.9%), strict 75.2% (exact / larger of ROM and ours)
fully exact routines: 52
```

The percentage is exact over the original's instruction count; the strict figure divides by the
larger of the original's and the compiled count, so extra instructions count against the match.
`--routine NAME` prints the original and the compiled code side by side: `=` exact, `~` aligned but
different, `|` not aligned.

### Plugging in a compiler: compile, search

blissdc does not include a BLISS-16 compiler. The only known BLISS-16 is the TOPS-20 hosted
cross-compiler (`BLIS16.EXE`, Bliss-16 3(552)) from DEC's DECnet-20 source tapes, which runs under
a PDP-10 emulator (KLH10 or SIMH) with TOPS-20. Wrap that in a command that

- takes the path of a `.b16` source as its last argument,
- leaves the listing `FILE.LST` (any case) in the same directory (compile with `/LIST`),
- prints the compiler's messages (`? ERR…`/`% ERR…` lines count as errors, `% WARN…` as warnings).

The command runs through `sh -c` with the source's directory as working directory; its output is
saved as `FILE.out`. Give it as `--compiler CMD` or in `BLISSDC_COMPILER`.

```
blissdc compile --compiler b16 m_01.b16 m_02.b16
blissdc search -p task.proj --compiler b16 --knobs knobs.txt --bits 7,17,10+25 --batch 25 --work var
```

`search` is per-routine coordinate descent: it builds everything with the current knobs (decompile in
batches, compile, score), then for each flip in `--bits` (a bit, or several joined by `+` and flipped
together) builds again with it applied to every routine and keeps it for the routines whose strict
score (exact over the larger of the original's and the compiled instruction count) went up. The knob
file is rewritten; the best build is left in `WORK/best`. Routines missing from the knob file start
from `--default` (153473).

## Project files

Plain text, one directive per line, `#` at the start of a line is a comment. Addresses octal (`0x`
hex, trailing `.` decimal). Relative paths are relative to the file they appear in. Several files
can be given; later directives add to earlier ones (for names, the first one given wins).

| Directive | Meaning |
|---|---|
| `include PATH` | read another project file here |
| `image PATH ADDR` | map the whole file at virtual ADDR |
| `file NAME PATH` | declare an image file for `map` |
| `map VADDR LEN NAME OFFSET` | map LEN bytes at VADDR from file NAME at OFFSET (banked/mapped systems; later maps win) |
| `own RANGE` | routines here are the ones decompiled by default |
| `banked RANGE` | contents depend on the mapped overlay: a call from outside into it is followed only if the target is labelled; unresolved calls print as `OV_<addr>` with `--readable` |
| `nocode RANGE` | data: routine discovery never decodes here |
| `entry ADDR [NAME]` | routine entry point |
| `label ADDR NAME` | name of a code address (routines, call and jump targets) |
| `sym ADDR NAME [; comment]` | name of a data address for `--readable` (`-` for none) and a comment printed above a routine at ADDR |
| `comment ADDR TEXT` | comment only |
| `case ADDR TABLE COUNT BASE` | the `ADD TABLE(Rn),PC` at ADDR dispatches through COUNT word offsets at TABLE, relative to BASE (the address after the ADD) |
| `save ADDR N` | ADDR is a register-save helper: `JSR R1,ADDR` saves R1..RN (BLISS-16's `$SAVn`) |
| `macro ADDR` | the routine at ADDR is hand-written MACRO (no BLISS linkage), in addition to the automatic detection |
| `linkage ADDR WORD...` | fix a routine's linkage: `R0`..`R5` register parameters, `G1`..`G5` global registers, `VALUE`/`NOVALUE` |
| `banklabel ADDR NAME [local] [CALLER...]` | a routine in a banked window, used to name calls to ADDR made from the listed CALLER addresses (`local`: never used as the only candidate) |
| `thunk ADDR` | ADDR is an overlay dispatcher: a routine whose first instruction is `JSR R5,ADDR` is a linker thunk (its inline arguments select the overlay and target) and is not decompiled |
| `module NAME` | module name and default output stem |
| `environment SW` | `ENVIRONMENT (SW)` of generated modules |

Example (`examples/demo/demo.proj`):

```
module DEMO
image demo.bin 0
own 1000-3000
include names.proj
entry 1000 MAIN
entry 1400
entry 1500
case 1206 1300 2. 1212
nocode 1300-1304
save 3000 2
```

### Mapped and overlaid systems

A system with memory management or overlays is described with one project file per address space
the code runs in. For a task of a mapped system: a `file` for the image, one `map` line per window
(physical page → virtual address), `own` over the task's windows, entry points as an explicit list.
For an overlay of that task: the same maps with the overlay window(s) pointing at the overlay's pages,
`own` over those windows only, `banked` over them in every variant, the overlay's routines as
entries, and labels of the other overlays (with the call sites that reach them, from the listing's
cross references) as `banklabel`s. Linker thunks of the form `JSR R5,DISPATCHER` / `.WORD id` /
`.WORD target` are marked with `thunk DISPATCHER`; the targets with this overlay's id go in as
entries. Kernel or library routines and data shared by all variants can go in a common file read with
`include`.

The VT240 was handled this way: a separate importer reads its task header chain, overlay table,
listing labels and symbol files, and writes one project file per task and overlay. Neither it nor
any VT240 material is part of this repository.

## Knobs

Bit flags per routine, given as decimal numbers. Default (`--match`) is bits 0, 7, 8, 9, 10, 12, 14,
17 = 153473; `--readable` uses 0, 8, 9, 10, 12, 14 = 22273.

| Bit | Effect |
|---|---|
| 0–5 | split each def-use web of R0 (bit 0) … R5 (bit 5) into its own variable |
| 6 | split webs of stack temporaries too |
| 7 | pin R1..R5 variables to the registers the original used (`REGISTER X1 = 1`) |
| 8 | an `IF` whose THEN arm ends in `RETURN` has no ELSE; the other arm follows the IF |
| 9 | `CASE` arms in the order of their code in the binary (= source order) |
| 10 | code after a loop reached from one block of the loop and only returning is written inside the loop at that exit |
| 11 | undo cross-jumping: small shared tails (≤ 4 instructions) duplicated per predecessor (a shared lone conditional branch is always split, whatever the knobs: its condition depends on which predecessor set the flags) |
| 12 | `DECR X FROM n TO 1` for count-down `DO … UNTIL` loops |
| 13 | `INCR X FROM a TO b` for count-up `DO … UNTIL` loops |
| 14 | when RETURNs leave an IF without a post-dominator, its arms join at the first block all of them reach |
| 15 | a stack parameter copied into R1..R5 stays a register variable (no copy propagation) |
| 16 | put the routine in a separate `OPTLEVEL = 0` module (with `--batch`) |
| 17 | with 7, pin R0 variables too. BLISS-16 also uses R0 as its scratch and value register, and a pinned R0 variable can be miscompiled (a VT240 routine lost a whole `IF`). Trust it only where the routine recompiles byte-identical; for code that will run, clear it everywhere else |
| 18 | keep R1..R5 temporaries as statements instead of folding them into their use |
| 19 | the same for R0 |
| 20 | declare stack locals high frame offset first |
| 21 | stack locals as one `LOCAL F : VECTOR[n]` at the original frame offsets (bounded by the prologue's allocation) |
| 22 | with 21, every stack slot in the vector, push temporaries included |
| 23 | code that several paths of a branch reach before its join goes after nested labelled blocks, reached by `LEAVE` |
| 24 | code shared by some (not all) CASE arms goes after `TES` in a labelled block; the other arms `LEAVE` it |
| 25 | `X = a; UNTIL .X GEQ b DO BEGIN …; X = .X + 1 END` as `INCR X FROM a TO b - 1` |
| 26 | as 11, with tails up to 8 instructions |
| 27 | memory bit stores as one field per run of bits (default: one field per bit) |

The score measures how much of the original code the recompiled routine reproduces, not whether it
behaves the same. A routine that is not byte-identical can still be wrong in ways the score cannot
see; booting a rebuilt VT240 ROM found output registers that were saved and restored, bytes of a stack
word split into two variables, a byte swap printed as a shift, and the R0 pinning above. All are fixed
and covered by `tests/lift.rs`, but run rebuilt code before trusting a near-match.

Environment variables for debugging (address in octal where one is given): `BLISSDC_INFO`
(print inferred linkages), `BLISSDC_DUMP=ADDR` (lifted statements of one routine),
`BLISSDC_LIVEDBG=ADDR`, `BLISSDC_LEV=ADDR`, `BLISSDC_TRACE_REGS`, `BLISSDC_NOWEBS`,
`BLISSDC_NOGLOBALS`.

## Library

The crate is also a library (`blissdc::program::Program`, `blissdc::driver::{analyze, select,
decompile_module, decompile_batch, map_text}`, `blissdc::score`, `blissdc::search`). An importer for
a system's own listing formats builds a `Program` (all fields are public) and saves it with
`Program::to_text`. Knobs and the readable flag are per-thread state installed by
`driver::Options::install`; the structurer recurses deeply, so run it on a thread with a large stack
(the binary uses 1 GB).

The instruction set is behind `arch::target` (now `arch::pdp11`): the decoder, the instruction
lifter, and the BLISS-16 idioms (prologue and save helpers, CASE dispatch, argument pushes, MACRO
markers, builtins, thunks). CFG, dataflow, structuring and printing do not look at opcodes. A
BLISS-32 (VAX) or BLISS-36 (PDP-10) back end would add a module with the same interface; the IR's
16-bit addresses would have to widen first.

`cargo test` runs the decoder and lifting tests and the `examples/demo` project. Set
`BLISSDC_TEST_PROJECTS` to project files (separated by `:`) to also check that each one survives
`to_text` and parsing unchanged and decompiles the same either way.

## Limits

- PDP-11 only, 16-bit virtual addresses. The decoder covers the T-11 instruction set: EIS (`MUL`,
  `DIV`, `ASH`, `ASHC`), FIS and FPU instructions decode as `.WORD` and stop the routine.
- Entry points are not found by scanning: give them (`entry`), they are followed through `JSR PC`
  calls only. Calls through registers or memory (`JSR PC,@X`, `JSR PC,(R1)`) are not followed.
- CASE tables are not detected; give each one (`case`). Register-save helpers likewise (`save`).
- `JSR R5` with inline arguments (other than thunks), coroutine calls and stack switching are lifted
  as unknown statements (`?? …`), as are a few rare instructions.
- Names in output are made BLISS-safe (upper case, punctuation as `_`). PDP-11 object modules keep
  global names to 6 characters (RAD50), so long distinct names can collide when linked.
- The score assumes the listing format of Bliss-16 3(552).
- Matching is never complete: a different compiler version (the VT240 was built with an earlier
  one) strength-reduces, CSEs and lays out code differently in places.
