// SPDX-License-Identifier: Apache-2.0
//! The external compiler hook and the per-routine knob search built on it.
//!
//! blissdc does not contain a BLISS-16 compiler.  `--compiler CMD` names a command that is run as
//! `sh -c 'CMD "$1"' blissdc FILE.b16`, with the directory of FILE.b16 as the working directory, and
//! must leave the listing `FILE.LST` (any case) next to the source.  Its output is saved as
//! `FILE.out`; lines starting with `? ERR` / `% ERR` count as errors, `% WARN` as warnings.

use crate::driver::{self, Options, Task};
use crate::score;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

pub struct CompileResult {
    pub source: PathBuf,
    pub listing: Option<PathBuf>,
    pub errors: usize,
    pub warnings: usize,
}

fn count_prefixed(out: &str, pre: &[&str]) -> usize {
    out.lines()
        .filter(|l| {
            pre.iter().any(|p| {
                // "? ERR", "?ERR", "% ERR", "%  WARN": marker, optional blanks, keyword
                let (m, kw) = p.split_at(1);
                l.strip_prefix(m).map(|r| r.trim_start_matches(' ').starts_with(kw.trim())).unwrap_or(false)
            })
        })
        .count()
}

/// Run the compiler on one source file.
pub fn compile(cmd: &str, src: &Path) -> Result<CompileResult, String> {
    let src = std::fs::canonicalize(src).map_err(|e| format!("{}: {}", src.display(), e))?;
    let dir = src.parent().unwrap_or(Path::new(".")).to_path_buf();
    let stem = src.file_stem().map(|s| s.to_string_lossy().to_uppercase()).unwrap_or_default();
    let find_lst = || -> Option<PathBuf> {
        std::fs::read_dir(&dir).ok().and_then(|rd| {
            rd.filter_map(|e| e.ok()).map(|e| e.path()).find(|p| {
                p.extension().map(|x| x.eq_ignore_ascii_case("lst")).unwrap_or(false)
                    && p.file_stem().map(|s| s.to_string_lossy().to_uppercase() == stem).unwrap_or(false)
            })
        })
    };
    // a listing left from an earlier run must not pass for this one
    if let Some(old) = find_lst() {
        let _ = std::fs::remove_file(old);
    }
    // the command runs in the source's directory: a relative program path is taken from here
    let cmd = match cmd.split_once(char::is_whitespace) {
        Some((prog, rest)) if prog.contains('/') && !prog.starts_with('/') => {
            format!("{} {}", std::env::current_dir().map(|d| d.join(prog).display().to_string()).unwrap_or(prog.into()), rest)
        }
        None if cmd.contains('/') && !cmd.starts_with('/') => {
            std::env::current_dir().map(|d| d.join(cmd).display().to_string()).unwrap_or(cmd.into())
        }
        _ => cmd.to_string(),
    };
    let out = Command::new("sh")
        .arg("-c")
        .arg(format!("{} \"$1\"", cmd))
        .arg("blissdc")
        .arg(&src)
        .current_dir(&dir)
        .output()
        .map_err(|e| format!("{}: {}", cmd, e))?;
    let mut text = String::from_utf8_lossy(&out.stdout).to_string();
    text.push_str(&String::from_utf8_lossy(&out.stderr));
    let _ = std::fs::write(src.with_extension("out"), &text);
    let listing = find_lst();
    Ok(CompileResult {
        source: src,
        listing,
        errors: count_prefixed(&text, &["? ERR", "% ERR"]),
        warnings: count_prefixed(&text, &["% WARN"]),
    })
}

/// One build: decompile into `dir` in batches, write the map, compile every module, score.
pub struct Build {
    /// per routine: exact instructions over the larger of the ROM's and ours (extra code counts against)
    pub scores: BTreeMap<String, f64>,
    pub errors: usize,
    pub total_line: String,
    pub report: String,
}

pub struct SearchConfig<'a> {
    pub compiler: &'a str,
    pub batch: usize,
    pub module: String,
    pub stem: String,
    pub want: Vec<u16>,
}

pub fn build(t: &mut Task, cfg: &SearchConfig, opts: &Options, dir: &Path) -> Result<Build, String> {
    std::fs::create_dir_all(dir).map_err(|e| format!("{}: {}", dir.display(), e))?;
    for e in std::fs::read_dir(dir).map_err(|e| e.to_string())?.flatten() {
        if e.path().is_file() {
            let _ = std::fs::remove_file(e.path());
        }
    }
    let files = driver::decompile_batch(t, opts, &cfg.want, cfg.batch, &cfg.module, &cfg.stem);
    let mut srcs = vec![];
    for (f, text) in files {
        let p = dir.join(&f);
        std::fs::write(&p, text).map_err(|e| format!("{}: {}", p.display(), e))?;
        srcs.push(p);
    }
    let mapf = dir.join("task.map");
    std::fs::write(&mapf, driver::map_text(t, &cfg.want)).map_err(|e| e.to_string())?;
    srcs.sort();
    let mut errors = 0;
    let mut lsts = vec![];
    for s in &srcs {
        let r = compile(cfg.compiler, s)?;
        errors += r.errors;
        if let Some(l) = r.listing {
            lsts.push(l.to_string_lossy().to_string());
        }
    }
    lsts.sort();
    let map = score::read_map(&mapf.to_string_lossy())?;
    let secs = score::lst_sections(&lsts)?;
    let rows = score::score_rows(&map, &secs);
    let report = score::score_report(&rows);
    let lines: Vec<&str> = report.lines().collect();
    let total_line = lines.get(lines.len().saturating_sub(2)).unwrap_or(&"").to_string();
    let scores = rows.iter().map(|r| (r.name.clone(), r.exact as f64 / r.rom.max(r.mine).max(1) as f64)).collect();
    Ok(Build { scores, errors, total_line, report })
}

pub fn write_knobs(kn: &BTreeMap<String, u32>, path: &Path) -> Result<(), String> {
    let mut s = String::new();
    for (n, v) in kn {
        s += &format!("{} {}\n", n, v);
    }
    std::fs::write(path, s).map_err(|e| format!("{}: {}", path.display(), e))
}

/// A flip as given on the command line: a bit number or several joined by `+` (`10+25`), as a mask.
pub fn parse_flip(s: &str) -> Result<u32, String> {
    let mut m = 0u32;
    for b in s.split('+') {
        let k: u32 = b.trim().parse().map_err(|_| format!("bad knob bit '{}'", b))?;
        if k >= 32 {
            return Err(format!("knob bit {} out of range", k));
        }
        m |= 1 << k;
    }
    Ok(m)
}

/// Per-routine coordinate descent over knob flips: for each flip (a mask of one or more bits), build
/// everything with it applied to every routine and keep it where a routine's score (exact over the
/// larger of the ROM's and our instruction count) went up.  Reads and rewrites `knob_file`; the best
/// build is left in `work/best`.
pub fn search(t: &mut Task, cfg: &SearchConfig, knob_file: &Path, flips: &[u32], default: u32, work: &Path,
              log: &mut dyn FnMut(&str)) -> Result<(), String> {
    let mut kn: BTreeMap<String, u32> = BTreeMap::new();
    if let Ok(txt) = std::fs::read_to_string(knob_file) {
        for l in txt.lines() {
            let f: Vec<&str> = l.split_whitespace().collect();
            if f.len() == 2 {
                if let Ok(v) = f[1].parse() {
                    kn.insert(f[0].to_string(), v);
                }
            }
        }
    }
    let opts_of = |m: &BTreeMap<String, u32>| -> Options {
        Options { knob_map: m.iter().map(|(k, v)| (k.clone(), *v)).collect(), ..Options::default() }
    };
    let b0 = build(t, cfg, &opts_of(&kn), &work.join("best"))?;
    log(&format!("base {} err {}", b0.total_line, b0.errors));
    let mut base = b0.scores;
    for &b in flips {
        let trial: BTreeMap<String, u32> =
            base.keys().map(|n| (n.clone(), kn.get(n).cloned().unwrap_or(default) ^ b)).collect();
        let tb = build(t, cfg, &opts_of(&trial), &work.join("trial"))?;
        let mut gained = 0.0;
        for (n, &v) in &tb.scores {
            let old = base.get(n).cloned().unwrap_or(0.0);
            if v > old {
                if let Some(&k) = trial.get(n) {
                    gained += v - old;
                    kn.insert(n.clone(), k);
                    base.insert(n.clone(), v);
                }
            }
        }
        log(&format!("flip {:o} trial {} err {} gain {:.2}", b, tb.total_line, tb.errors, gained));
    }
    write_knobs(&kn, knob_file)?;
    let best = build(t, cfg, &opts_of(&kn), &work.join("best"))?;
    log(&format!("best {} err {}", best.total_line, best.errors));
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::parse_flip;

    #[test]
    fn flips() {
        assert_eq!(parse_flip("7"), Ok(1 << 7));
        assert_eq!(parse_flip("10+25"), Ok((1 << 10) | (1 << 25)));
        assert!(parse_flip("x").is_err());
        assert!(parse_flip("32").is_err());
    }
}
