// SPDX-License-Identifier: Apache-2.0
//! Project files: the example in examples/demo, the command line, and (optionally) larger projects
//! given in BLISSDC_TEST_PROJECTS (paths separated by ':'), which are skipped when unset.
use blissdc::driver::{self, Options};
use blissdc::program::Program;
use std::path::{Path, PathBuf};
use std::process::Command;

fn demo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/demo/demo.proj")
}

fn big_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new().stack_size(1 << 30).spawn(f).unwrap().join().unwrap()
}

fn decompile(p: Program, opts: Options) -> String {
    big_stack(move || {
        let module = p.module.clone().unwrap_or_default();
        let mut t = driver::analyze(p).unwrap();
        let want = driver::select(&t, &[], &[]).unwrap();
        driver::decompile_module(&mut t, &opts, &want, &module)
    })
}

#[test]
fn demo_project() {
    let mut p = Program::new();
    p.load_file(&demo()).unwrap();
    assert_eq!(p.names.get(&0o1200).map(|s| s.as_str()), Some("PICK")); // from the included file
    let s = decompile(p, Options::readable());
    assert!(s.starts_with("MODULE DEMO =\n"), "{}", s);
    assert!(s.contains("LINKAGE L_R0 = JSR (REGISTER = 0);"), "{}", s);
    assert!(s.contains("RESULT = PICK (DOUBLE (3));"), "{}", s);
    assert!(s.contains("! selects a constant by index\nGLOBAL ROUTINE PICK (A1) ="), "{}", s);
    assert!(s.contains("CASE .A1 FROM 0 TO 1 OF"), "{}", s);
    assert!(s.contains("GLOBAL ROUTINE FIRST (A1) ="), "{}", s);
    assert!(s.contains("BUILTIN MTPS;"), "{}", s);
    assert!(s.contains("MTPS (224);"), "{}", s);
    assert!(!s.contains("EXTERNAL ROUTINE"), "{}", s);
}

#[test]
fn to_text_round_trip() {
    let mut p = Program::new();
    p.load_file(&demo()).unwrap();
    let text = p.to_text();
    let mut q = Program::new();
    q.parse(&text, Path::new("/")).unwrap();
    assert_eq!(q.to_text(), text);
    assert_eq!(decompile(p, Options::default()), decompile(q, Options::default()));
}

#[test]
fn command_line() {
    let bin = env!("CARGO_BIN_EXE_blissdc");
    let img = format!("{}@0", demo().with_file_name("demo.bin").display());
    let out = Command::new(bin).args(["routines", "--image", &img, "--entry", "1000=MAIN"]).output().unwrap();
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    let s = String::from_utf8_lossy(&out.stdout);
    assert!(s.contains("001000  MAIN"), "{}", s);
    assert!(s.contains("001100  R001100"), "{}", s);
    let out = Command::new(bin).args(["project", "-p"]).arg(demo()).output().unwrap();
    assert!(out.status.success());
    assert!(String::from_utf8_lossy(&out.stdout).contains("label 001200 PICK\n"));
}

/// any project: the text format carries everything (written, parsed back, same output)
#[test]
fn external_projects() {
    let list = match std::env::var("BLISSDC_TEST_PROJECTS") {
        Ok(v) if !v.is_empty() => v,
        _ => {
            eprintln!("skipping: BLISSDC_TEST_PROJECTS not set");
            return;
        }
    };
    for f in list.split(':') {
        let mut p = Program::new();
        p.load_file(Path::new(f)).unwrap();
        let text = p.to_text();
        let mut q = Program::new();
        q.parse(&text, Path::new("/")).unwrap();
        assert_eq!(q.to_text(), text, "{}", f);
        for o in [Options::default(), Options::readable()] {
            assert_eq!(decompile(p.clone(), o.clone()), decompile(q.clone(), o), "{}", f);
        }
    }
}
