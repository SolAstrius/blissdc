// SPDX-License-Identifier: Apache-2.0
use blissdc::arch::pdp11;
use blissdc::driver::{self, Options, Task};
use blissdc::program::{o6, parse_addr, parse_range, Program};
use blissdc::{score, search};
use clap::{Args, Parser, Subcommand};
use std::path::{Path, PathBuf};

#[derive(Parser)]
#[command(name = "blissdc", version, about = "Decompile PDP-11 code produced by DEC's BLISS-16 compiler back to BLISS source")]
struct Cli {
    #[command(subcommand)]
    cmd: Cmd,
}

/// Where the program comes from: project files and/or raw images.
#[derive(Args, Clone)]
struct Input {
    /// project/symbol file (repeatable; see README for the format)
    #[arg(short = 'p', long = "project", value_name = "FILE")]
    projects: Vec<PathBuf>,
    /// raw binary mapped at a virtual address (octal; 0x hex; trailing '.' decimal), e.g. rom.bin@020000
    #[arg(long = "image", value_name = "FILE@ADDR")]
    images: Vec<String>,
    /// routine entry point, optionally named: ADDR or ADDR=NAME (repeatable)
    #[arg(long = "entry", value_name = "ADDR[=NAME]")]
    entries: Vec<String>,
    /// address range whose routines are decompiled by default: LO-HI or LO+LEN (repeatable)
    #[arg(long = "own", value_name = "RANGE")]
    own: Vec<String>,
    /// banked/overlay address range (repeatable)
    #[arg(long = "banked", value_name = "RANGE")]
    banked: Vec<String>,
}

#[derive(Args)]
struct DecompileArgs {
    #[command(flatten)]
    input: Input,
    /// routines to decompile (octal address or name); default: every routine in the own ranges
    routines: Vec<String>,
    /// natural source: symbol names and comments, idiom knobs only (ignores --knobs)
    #[arg(long, conflicts_with = "match_mode")]
    readable: bool,
    /// source meant to recompile to the same code (the default)
    #[arg(long = "match")]
    match_mode: bool,
    /// knob file ("ROUTINE value" lines) or a number used for every routine
    #[arg(long, value_name = "FILE|N")]
    knobs: Option<String>,
    /// write modules of at most N routines each: STEM_01.b16, STEM_02.b16, ...
    #[arg(long, value_name = "N")]
    batch: Option<usize>,
    /// output file (with --batch: the stem, STEM.b16)
    #[arg(short = 'o', value_name = "FILE")]
    out: Option<PathBuf>,
    /// skip a routine by name (repeatable)
    #[arg(short = 'x', value_name = "NAME")]
    skip: Vec<String>,
    /// also write the instruction map (as `blissdc map`)
    #[arg(long, value_name = "FILE")]
    map: Option<PathBuf>,
    /// MODULE name [default: the project's module, else the first image's file name]
    #[arg(long, value_name = "NAME")]
    module: Option<String>,
    /// ENVIRONMENT switch of the module, e.g. T11 or EIS (overrides the project)
    #[arg(long, value_name = "SW")]
    environment: Option<String>,
}

#[derive(Subcommand)]
enum Cmd {
    /// Disassemble routines or an address range
    Disasm {
        #[command(flatten)]
        input: Input,
        /// routines (octal address or name)
        routines: Vec<String>,
        /// linear disassembly of LO-HI instead of routines
        #[arg(long, value_name = "RANGE")]
        range: Option<String>,
    },
    /// List discovered routines and their inferred linkages
    Routines {
        #[command(flatten)]
        input: Input,
        /// include routines outside the own ranges (kernel, library)
        #[arg(long)]
        all: bool,
    },
    /// Decompile routines to BLISS-16 source
    Decompile(DecompileArgs),
    /// Write the per-instruction map used by `score`
    Map {
        #[command(flatten)]
        input: Input,
        /// routines (octal address or name); default: every routine in the own ranges
        routines: Vec<String>,
        /// skip a routine by name (repeatable)
        #[arg(short = 'x', value_name = "NAME")]
        skip: Vec<String>,
        /// output file [default: stdout]
        #[arg(short = 'o', value_name = "FILE")]
        out: Option<PathBuf>,
    },
    /// Score compiled BLISS-16 listings against the original code
    Score {
        /// map file from `blissdc map`
        map: PathBuf,
        /// compiled listings (.LST)
        #[arg(required = true)]
        lsts: Vec<PathBuf>,
        /// show one routine side by side instead (= exact, ~ aligned but different, | unaligned)
        #[arg(long, value_name = "NAME")]
        routine: Option<String>,
    },
    /// Run the external BLISS-16 compiler on .b16 files
    Compile {
        /// command taking FILE.b16 as its last argument and leaving FILE.LST next to it
        #[arg(long, value_name = "CMD", env = "BLISSDC_COMPILER")]
        compiler: String,
        #[arg(required = true)]
        files: Vec<PathBuf>,
    },
    /// Search knob bits per routine by compiling variants and scoring them
    Search {
        #[command(flatten)]
        input: Input,
        /// compiler command, as for `compile`
        #[arg(long, value_name = "CMD", env = "BLISSDC_COMPILER")]
        compiler: String,
        /// knob file to start from and to update
        #[arg(long, value_name = "FILE")]
        knobs: PathBuf,
        /// knob bits to try, in order; `a+b` flips several together (e.g. 7,8,10+25)
        #[arg(long, value_delimiter = ',', required = true)]
        bits: Vec<String>,
        /// default knobs for routines missing from the file
        #[arg(long, default_value_t = blissdc::lift::DEFAULT_KNOBS)]
        default: u32,
        #[arg(long, default_value_t = 25)]
        batch: usize,
        /// work directory (builds in WORK/best and WORK/trial)
        #[arg(long, value_name = "DIR")]
        work: PathBuf,
        /// routines to include (octal address or name); default: every routine in the own ranges
        routines: Vec<String>,
        /// skip a routine by name (repeatable)
        #[arg(short = 'x', value_name = "NAME")]
        skip: Vec<String>,
    },
    /// Write the input (project files, images, options) as one project file
    Project {
        #[command(flatten)]
        input: Input,
        /// output file [default: stdout]
        #[arg(short = 'o', value_name = "FILE")]
        out: Option<PathBuf>,
    },
}

fn load_program(inp: &Input) -> Result<Program, String> {
    let mut p = Program::new();
    for f in &inp.projects {
        p.load_file(f)?;
    }
    for s in &inp.images {
        let (f, a) = s.rsplit_once('@').ok_or_else(|| format!("--image {}: expected FILE@ADDR", s))?;
        p.add_image(Path::new(f), parse_addr(a)?)?;
        if p.module.is_none() {
            let stem = Path::new(f).file_stem().map(|x| x.to_string_lossy().to_uppercase()).unwrap_or_default();
            let m: String = stem.chars().filter(|c| c.is_ascii_alphanumeric()).collect();
            if !m.is_empty() {
                p.module = Some(m);
            }
        }
    }
    for e in &inp.entries {
        let (a, n) = match e.split_once('=') { Some((a, n)) => (a, Some(n)), None => (e.as_str(), None) };
        let a = parse_addr(a)?;
        p.entries.insert(a);
        if let Some(n) = n {
            p.names.insert(a, n.to_string());
        }
    }
    for r in &inp.own {
        p.own.push(parse_range(r)?);
    }
    for r in &inp.banked {
        p.banked.push(parse_range(r)?);
    }
    if p.segments.is_empty() {
        return Err("no memory: give --image FILE@ADDR, or a project file with 'image'/'map'".into());
    }
    if p.entries.is_empty() {
        return Err("no entry points: give --entry ADDR or 'entry' lines in a project file".into());
    }
    Ok(p)
}

fn analyze(inp: &Input) -> Result<Task, String> {
    driver::analyze(load_program(inp)?)
}

fn write_out(out: &Option<PathBuf>, text: &str) -> Result<(), String> {
    match out {
        Some(f) => std::fs::write(f, text).map_err(|e| format!("{}: {}", f.display(), e)),
        None => {
            emit(text);
            Ok(())
        }
    }
}

/// write to stdout; a closed pipe (`| head`) ends the program quietly
fn emit(text: &str) {
    use std::io::Write;
    let mut o = std::io::stdout().lock();
    if o.write_all(text.as_bytes()).and_then(|_| o.flush()).is_err() {
        std::process::exit(0);
    }
}

fn routine_insns(t: &Task, e: u16) -> String {
    let r = &t.routines[&e];
    let mut s = String::new();
    s += &format!("; {} {}\n", o6(e), r.name);
    for (pc, i) in &r.insns {
        if r.blocks.contains_key(pc) && *pc != e {
            s += &format!("{}:\n", t.mem.names.get(pc).cloned().unwrap_or_else(|| format!("L{}", o6(*pc))));
        }
        s += &pdp11::disasm_line(&t.mem, i);
    }
    s
}

fn run(cli: Cli) -> Result<(), String> {
    match cli.cmd {
        Cmd::Disasm { input, routines, range } => {
            if let Some(r) = range {
                let p = load_program(&input)?;
                let (lo, hi) = parse_range(&r)?;
                let mut pc = lo as u32;
                let mut s = String::new();
                while pc < hi {
                    let a = pc as u16;
                    if let Some(n) = p.names.get(&a) {
                        s += &format!("{}:\n", n);
                    }
                    match p.dec(a) {
                        Ok(i) => {
                            s += &pdp11::disasm_line(&p, &i);
                            pc += 2 * i.nwords as u32;
                        }
                        Err(_) => {
                            s += &format!("{}  ??????\n", o6(a));
                            pc += 2;
                        }
                    }
                }
                emit(&s);
                return Ok(());
            }
            let t = analyze(&input)?;
            let want = driver::select(&t, &routines, &[])?;
            for e in want {
                emit(&format!("{}\n", routine_insns(&t, e)));
            }
        }
        Cmd::Routines { input, all } => {
            let t = analyze(&input)?;
            let mut v: Vec<u16> = t.rorder.iter().cloned().filter(|e| all || t.mem.is_own(*e)).collect();
            v.sort();
            let mut out = format!("{:<7} {:<24} {:>5} {:>5}  {:<3} {:<14} {:<10} {:<10} {}\n", "addr", "name", "insns", "words", "arg",
                "regs", "globals", "declares", "kind");
            for e in v {
                let r = &t.routines[&e];
                let x = &t.info[&e];
                let words: u32 = r.insns.values().map(|i| i.nwords as u32).sum();
                let regs = |v: &[i32], p: &str| -> String {
                    if v.is_empty() { "-".into() } else { v.iter().map(|k| format!("{}{}", p, k)).collect::<Vec<_>>().join(",") }
                };
                let thunk = r.insns.get(&e).map(|i| i.is_thunk_call(&t.mem)).unwrap_or(false);
                let kind = if thunk { "thunk" } else if t.macros.contains(&e) { "MACRO" } else if x.returns { "value" } else { "novalue" };
                out += &format!("{:<7} {:<24} {:>5} {:>5}  {:<3} {:<14} {:<10} {:<10} {}\n", o6(e), r.name, r.insns.len(), words,
                    x.nparams, regs(&x.regparams, "R"), regs(&x.globals, "G"), regs(&x.gdecl, "G"), kind);
            }
            emit(&out);
        }
        Cmd::Decompile(a) => {
            let mut prog = load_program(&a.input)?;
            if let Some(e) = &a.environment {
                prog.environment = if e.is_empty() { None } else { Some(e.clone()) };
            }
            let module = a.module.clone().or_else(|| prog.module.clone()).unwrap_or_else(|| "BLISDC".into());
            let mut t = driver::analyze(prog)?;
            let mut opts = if a.readable { Options::readable() } else { Options::default() };
            if let Some(k) = &a.knobs {
                if a.readable {
                    eprintln!("note: --knobs is ignored with --readable");
                } else {
                    opts.set_knobs(k)?;
                }
            }
            let want = driver::select(&t, &a.routines, &a.skip)?;
            if let Some(m) = &a.map {
                std::fs::write(m, driver::map_text(&t, &want)).map_err(|e| format!("{}: {}", m.display(), e))?;
            }
            if let Some(n) = a.batch {
                let base = a.out.clone().map(|p| p.to_string_lossy().to_string())
                    .unwrap_or_else(|| format!("{}.b16", module.to_lowercase().replace('/', "_")));
                let stem = base.trim_end_matches(".b16").to_string();
                for (f, text) in driver::decompile_batch(&mut t, &opts, &want, n, &module, &stem) {
                    std::fs::write(&f, text).map_err(|e| format!("{}: {}", f, e))?;
                }
            } else {
                let text = driver::decompile_module(&mut t, &opts, &want, &module);
                match &a.out {
                    Some(f) => std::fs::write(f, text).map_err(|e| format!("{}: {}", f.display(), e))?,
                    None => emit(&format!("{}\n", text)),
                }
            }
        }
        Cmd::Map { input, routines, skip, out } => {
            let t = analyze(&input)?;
            let want = driver::select(&t, &routines, &skip)?;
            write_out(&out, &driver::map_text(&t, &want))?;
        }
        Cmd::Score { map, lsts, routine } => {
            let m = score::read_map(&map.to_string_lossy())?;
            let ls: Vec<String> = lsts.iter().map(|p| p.to_string_lossy().to_string()).collect();
            match routine {
                Some(n) => emit(&score::side_by_side(&m, &n, &ls)?),
                None => {
                    let secs = score::lst_sections(&ls)?;
                    emit(&score::score_report(&score::score_rows(&m, &secs)));
                }
            }
        }
        Cmd::Compile { compiler, files } => {
            let mut bad = 0;
            for f in &files {
                let r = search::compile(&compiler, f)?;
                println!("{}  warn {}  err {}  {}", f.display(), r.warnings, r.errors,
                    r.listing.map(|l| l.display().to_string()).unwrap_or_else(|| "(no listing)".into()));
                bad += r.errors;
            }
            if bad > 0 {
                return Err(format!("{} errors", bad));
            }
        }
        Cmd::Search { input, compiler, knobs, bits, default, batch, work, routines, skip } => {
            let prog = load_program(&input)?;
            let module = prog.module.clone().unwrap_or_else(|| "BLISDC".into());
            let mut t = driver::analyze(prog)?;
            let want = driver::select(&t, &routines, &skip)?;
            let cfg = search::SearchConfig { compiler: &compiler, batch, module, stem: "m".into(), want };
            let knobs = std::env::current_dir().map(|d| d.join(&knobs)).unwrap_or(knobs);
            let work = std::env::current_dir().map(|d| d.join(&work)).unwrap_or(work);
            let flips = bits.iter().map(|b| search::parse_flip(b)).collect::<Result<Vec<u32>, String>>()?;
            search::search(&mut t, &cfg, &knobs, &flips, default, &work, &mut |l| println!("{}", l))?;
        }
        Cmd::Project { input, out } => {
            let p = load_program(&input)?;
            write_out(&out, &p.to_text())?;
        }
    }
    Ok(())
}

fn main() {
    let cli = Cli::parse();
    // deep recursion in the structurer: run on a big stack
    let h = std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || match run(cli) {
            Ok(()) => 0,
            Err(e) => {
                eprintln!("blissdc: {}", e);
                1
            }
        })
        .expect("thread");
    std::process::exit(h.join().unwrap_or(101));
}
