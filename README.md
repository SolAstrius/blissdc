# blissdc

Decompiles PDP-11 machine code produced by DEC's BLISS-16 compiler back to BLISS source that
BLISS-16 compiles again, ideally to the same instructions.

It was written for the DEC VT240 terminal's T-11 firmware. On the VT240 PARSER task, the output
recompiled with BLISS-16 3(552) reproduces 83.9% of the original instructions exactly (3667 of
4369). Nothing in the tool is specific to the VT240.

## Build

```
cargo build --release        # target/release/blissdc
```

## Use

A program is described by a project file: images, entry points, names, case tables, register-save
helpers. `examples/demo` is a small hand-assembled one.

```
$ blissdc decompile -p examples/demo/demo.proj --readable MAIN FIRST
...
GLOBAL ROUTINE MAIN : NOVALUE =
    BEGIN
    RESULT = PICK (DOUBLE (3));
    RETURN;
    END;

GLOBAL ROUTINE FIRST (A1) =
    BEGIN
    RETURN .A1;
    END;
...
```

`blissdc --help` lists the other commands: `disasm`, `routines`, `map`, `score`, `compile`,
`search`, `project`.

## Recompiling

blissdc does not include a compiler. The only known BLISS-16 is `BLIS16.EXE` from DEC's DECnet-20
source tapes, which runs under TOPS-20 on a PDP-10 emulator. Wrap it in a command that takes a `.b16`
path and leaves `FILE.LST` next to it, then:

```
blissdc compile --compiler b16 m_01.b16
blissdc search -p task.proj --compiler b16 --knobs knobs.txt
```

`search` tries alternative code shapes per routine and keeps those whose recompiled code is closer
to the original. A close score doesn't prove the code behaves the same: run rebuilt code before
trusting it.

Project file directives, knobs, internals and limits are in [docs/manual.md](docs/manual.md).

## License

Apache-2.0, see `LICENSE` and `NOTICE`.
