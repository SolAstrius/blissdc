// SPDX-License-Identifier: Apache-2.0
//! The input program: a 16-bit address space assembled from raw image files, plus everything known
//! about it from outside the code (entry points, names, case tables, idiom helpers, hints).
//!
//! A `Program` is built from project files (see [`Program::parse`] and the README for the format),
//! from command-line options, or by code (an importer for a particular system's listings).
//! [`Program::to_text`] writes the same plain-text format back, so a program assembled by an importer
//! or from several files can be saved as one file, edited and reused.

use crate::arch::pdp11::{decode, Insn};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::path::{Path, PathBuf};

/// One mapping of `len` bytes of virtual memory at `vaddr` to `offset` in image file `file`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Segment {
    pub vaddr: u16,
    pub len: u32,
    pub file: usize,
    pub offset: usize,
}

/// A raw image file and the short name the project file refers to it by.
#[derive(Clone, Debug)]
pub struct ImageFile {
    pub name: String,
    pub path: PathBuf,
    pub data: Vec<u8>,
}

/// A routine reached through a banked (overlaid) window, named per calling site.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BankLabel {
    pub name: String,
    /// a local label (not a routine): only used when a caller lists it
    pub local: bool,
    /// call sites known to reach this label (from the listing's cross references)
    pub callers: Vec<u16>,
}

/// User-given linkage of one routine; overrides what the analysis infers.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct LinkageHint {
    /// registers carrying parameters (LINKAGE ... REGISTER = k)
    pub regs: Vec<i32>,
    /// linkage GLOBAL registers
    pub globals: Vec<i32>,
    /// Some(true) value-returning, Some(false) NOVALUE, None: inferred
    pub value: Option<bool>,
}

#[derive(Clone, Debug, Default)]
pub struct Program {
    pub files: Vec<ImageFile>,
    pub segments: Vec<Segment>,
    /// address ranges [lo, hi) whose routines are decompiled by default
    pub own: Vec<(u16, u32)>,
    /// address ranges [lo, hi) whose contents depend on which overlay/bank is mapped
    pub banked: Vec<(u16, u32)>,
    /// address ranges [lo, hi) that hold data: routine discovery never decodes there
    pub nocode: Vec<(u16, u32)>,
    /// routine entry points (discovery starts here and follows calls)
    pub entries: BTreeSet<u16>,
    /// code labels: routine and call-target names
    pub names: HashMap<u16, String>,
    /// data/global names (`--readable`) and comments
    pub syms: HashMap<u16, (String, String)>,
    /// case dispatch at the key address: (table, entries, base the offsets are relative to)
    pub cases: HashMap<u16, (u16, usize, u16)>,
    /// register-save helpers: JSR R1,addr saves R1..Rn
    pub saves: HashMap<u16, i32>,
    /// routines that are hand-written MACRO (no BLISS linkage)
    pub macros: HashSet<u16>,
    pub linkages: BTreeMap<u16, LinkageHint>,
    pub bank_labels: HashMap<u16, Vec<BankLabel>>,
    /// thunk dispatchers: a routine whose first instruction is JSR R5 to one of these is not decompiled
    pub thunks: HashSet<u16>,
    /// MODULE name (also the default output file stem)
    pub module: Option<String>,
    /// ENVIRONMENT (...) switch of the generated modules, e.g. T11 or EIS
    pub environment: Option<String>,
}

pub fn o6(v: u16) -> String {
    format!("{:06o}", v)
}

/// A number in the project-file syntax: octal by default, `0x` hex, trailing `.` decimal.
pub fn parse_num(s: &str) -> Result<u64, String> {
    let s = s.trim();
    let r = if let Some(h) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        u64::from_str_radix(h, 16)
    } else if let Some(d) = s.strip_suffix('.') {
        d.parse::<u64>()
    } else {
        u64::from_str_radix(s, 8)
    };
    r.map_err(|_| format!("bad number '{}' (octal, 0x hex, or decimal with a trailing '.')", s))
}

pub fn parse_addr(s: &str) -> Result<u16, String> {
    let v = parse_num(s)?;
    if v > 0xFFFF {
        return Err(format!("address {} out of range", s));
    }
    Ok(v as u16)
}

/// `LO-HI` (HI exclusive; may be 200000 for the top of memory) or `LO+LEN`.
pub fn parse_range(s: &str) -> Result<(u16, u32), String> {
    if let Some((a, l)) = s.split_once('+') {
        let lo = parse_addr(a)?;
        let n = parse_num(l)?;
        return Ok((lo, (lo as u64 + n).min(0x10000) as u32));
    }
    let (a, b) = s.split_once('-').ok_or_else(|| format!("bad range '{}' (LO-HI or LO+LEN)", s))?;
    let lo = parse_addr(a)?;
    let hi = parse_num(b)?;
    if hi > 0x10000 || hi < lo as u64 {
        return Err(format!("bad range '{}'", s));
    }
    Ok((lo, hi as u32))
}

fn in_ranges(r: &[(u16, u32)], a: u16) -> bool {
    r.iter().any(|&(lo, hi)| a >= lo && (a as u32) < hi)
}

impl Program {
    pub fn new() -> Program {
        Program::default()
    }

    // ------------------------------------------------------------ memory
    pub fn add_file(&mut self, name: &str, path: &Path) -> Result<usize, String> {
        if let Some(i) = self.files.iter().position(|f| f.name == name) {
            return Ok(i);
        }
        let data = std::fs::read(path).map_err(|e| format!("{}: {}", path.display(), e))?;
        self.files.push(ImageFile { name: name.to_string(), path: path.to_path_buf(), data });
        Ok(self.files.len() - 1)
    }

    /// map bytes held in memory at `vaddr` (for tests and embedding)
    pub fn add_bytes(&mut self, name: &str, data: Vec<u8>, vaddr: u16) {
        let len = (data.len() as u32).min(0x10000 - vaddr as u32);
        self.files.push(ImageFile { name: name.to_string(), path: PathBuf::new(), data });
        self.segments.push(Segment { vaddr, len, file: self.files.len() - 1, offset: 0 });
    }

    /// map a whole file at `vaddr` (the `--image FILE@ADDR` option)
    pub fn add_image(&mut self, path: &Path, vaddr: u16) -> Result<(), String> {
        let name = format!("img{}", self.files.len());
        let f = self.add_file(&name, path)?;
        let len = (self.files[f].data.len() as u32).min(0x10000 - vaddr as u32);
        self.segments.push(Segment { vaddr, len, file: f, offset: 0 });
        Ok(())
    }

    /// file and byte offset of a virtual address (later segments override earlier ones)
    pub fn v2p(&self, v: u16) -> Option<(usize, usize)> {
        for s in self.segments.iter().rev() {
            if v >= s.vaddr && (v as u32) < s.vaddr as u32 + s.len {
                return Some((s.file, s.offset + (v - s.vaddr) as usize));
            }
        }
        None
    }

    pub fn mapped(&self, v: u16) -> bool {
        self.v2p(v).is_some()
    }

    /// little-endian word at a virtual address; the second byte is the next byte of the same file
    pub fn rw(&self, v: u16) -> Option<u16> {
        let (f, p) = self.v2p(v)?;
        let d = &self.files[f].data;
        if p + 1 >= d.len() {
            return None;
        }
        Some(d[p] as u16 | ((d[p + 1] as u16) << 8))
    }

    pub fn rb(&self, v: u16) -> Option<u8> {
        let (f, p) = self.v2p(v)?;
        self.files[f].data.get(p).cloned()
    }

    pub fn dec(&self, pc: u16) -> Result<Insn, String> {
        if in_ranges(&self.nocode, pc) {
            return Err(format!("TypeError: {} is in a nocode range", o6(pc)));
        }
        decode(&|a| self.rw(a), pc)
    }

    pub fn is_own(&self, a: u16) -> bool {
        if self.own.is_empty() {
            return self.mapped(a);
        }
        in_ranges(&self.own, a)
    }

    pub fn is_banked(&self, a: u16) -> bool {
        in_ranges(&self.banked, a)
    }

    // ------------------------------------------------------------ names
    pub fn name_of(&self, a: u16) -> String {
        self.names.get(&a).cloned().unwrap_or_else(|| format!("R{}", o6(a)))
    }

    /// the banked routine a call at `caller` reaches: the label whose cross references list the
    /// caller, else the only routine label at that address
    pub fn ovl_name(&self, a: u16, caller: u16) -> Option<String> {
        let v = self.bank_labels.get(&a)?;
        if let Some(x) = v.iter().find(|b| b.callers.contains(&caller)) {
            return Some(x.name.clone());
        }
        if v.len() == 1 && !v[0].local {
            return Some(v[0].name.clone());
        }
        None
    }

    pub fn find_name(&self, n: &str) -> Option<u16> {
        let mut v: Vec<u16> = self.names.iter().filter(|(_, x)| x.as_str() == n).map(|(a, _)| *a).collect();
        v.sort();
        v.first().cloned()
    }

    // ------------------------------------------------------------ text format
    /// Parse a project/symbol file and merge it into this program.  `base` resolves relative paths.
    pub fn parse(&mut self, text: &str, base: &Path) -> Result<(), String> {
        self.parse_nested(text, base, 0)
    }

    fn parse_nested(&mut self, text: &str, base: &Path, depth: usize) -> Result<(), String> {
        for (ln, raw) in text.lines().enumerate() {
            let err = |m: String| format!("line {}: {}", ln + 1, m);
            // '#' at the start of a line is a comment; in sym lines a ';' starts the comment text
            let line = raw.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            let (head, rest) = match line.split_once(char::is_whitespace) {
                Some((h, r)) => (h, r.trim()),
                None => (line, ""),
            };
            let f: Vec<&str> = rest.split_whitespace().collect();
            let need = |n: usize| -> Result<(), String> {
                if f.len() < n { Err(err(format!("'{}' needs {} arguments", head, n))) } else { Ok(()) }
            };
            match head {
                "file" => {
                    need(2)?;
                    let p = base.join(rest[f[0].len()..].trim());
                    self.add_file(f[0], &p).map_err(err)?;
                }
                "include" => {
                    // include PATH: another project file, its relative paths resolved against its own directory
                    need(1)?;
                    let p = base.join(rest);
                    if depth >= 16 {
                        return Err(err(format!("include nested too deeply at {}", p.display())));
                    }
                    let txt = std::fs::read_to_string(&p).map_err(|e| err(format!("{}: {}", p.display(), e)))?;
                    let b = p.parent().map(|x| x.to_path_buf()).unwrap_or_default();
                    self.parse_nested(&txt, &b, depth + 1).map_err(|e| err(format!("{}: {}", p.display(), e)))?;
                }
                "image" => {
                    // image PATH ADDR
                    need(2)?;
                    let a = parse_addr(f[f.len() - 1]).map_err(err)?;
                    let pstr = rest[..rest.len() - f[f.len() - 1].len()].trim();
                    self.add_image(&base.join(pstr), a).map_err(err)?;
                }
                "map" => {
                    // map VADDR LEN FILE OFFSET
                    need(4)?;
                    let vaddr = parse_addr(f[0]).map_err(err)?;
                    let len = parse_num(f[1]).map_err(err)? as u32;
                    let file = self.files.iter().position(|x| x.name == f[2])
                        .ok_or_else(|| err(format!("unknown file '{}' (declare it with 'file')", f[2])))?;
                    let offset = parse_num(f[3]).map_err(err)? as usize;
                    self.segments.push(Segment { vaddr, len, file, offset });
                }
                "own" | "banked" | "nocode" => {
                    need(1)?;
                    let r = parse_range(f[0]).map_err(err)?;
                    match head {
                        "own" => self.own.push(r),
                        "banked" => self.banked.push(r),
                        _ => self.nocode.push(r),
                    }
                }
                "entry" => {
                    need(1)?;
                    let a = parse_addr(f[0]).map_err(err)?;
                    self.entries.insert(a);
                    if let Some(n) = f.get(1) {
                        self.names.entry(a).or_insert_with(|| n.to_string());
                    }
                }
                "label" => {
                    need(2)?;
                    let a = parse_addr(f[0]).map_err(err)?;
                    self.names.entry(a).or_insert_with(|| f[1].to_string());
                }
                "sym" => {
                    // sym ADDR NAME [; comment]   (NAME '-' for a comment only)
                    need(1)?;
                    let a = parse_addr(f[0]).map_err(err)?;
                    let (body, cmt) = match rest.split_once(';') { Some((b, c)) => (b, c.trim()), None => (rest, "") };
                    let bf: Vec<&str> = body.split_whitespace().collect();
                    let name = match bf.get(1) { Some(&"-") | None => "", Some(n) => n };
                    let e = self.syms.entry(a).or_insert((String::new(), String::new()));
                    if e.0.is_empty() { e.0 = name.to_string(); }
                    if e.1.is_empty() { e.1 = cmt.to_string(); }
                }
                "comment" => {
                    need(1)?;
                    let a = parse_addr(f[0]).map_err(err)?;
                    let text = rest[f[0].len()..].trim();
                    let e = self.syms.entry(a).or_insert((String::new(), String::new()));
                    if e.1.is_empty() { e.1 = text.to_string(); }
                }
                "case" => {
                    // case AT TABLE COUNT BASE
                    need(4)?;
                    let at = parse_addr(f[0]).map_err(err)?;
                    let tab = parse_addr(f[1]).map_err(err)?;
                    let n = parse_num(f[2]).map_err(err)? as usize;
                    let b = parse_addr(f[3]).map_err(err)?;
                    self.cases.insert(at, (tab, n, b));
                }
                "save" => {
                    need(2)?;
                    let a = parse_addr(f[0]).map_err(err)?;
                    let n = parse_num(f[1]).map_err(err)? as i32;
                    if !(1..=5).contains(&n) {
                        return Err(err("save count must be 1..5".into()));
                    }
                    self.saves.insert(a, n);
                }
                "macro" => {
                    need(1)?;
                    self.macros.insert(parse_addr(f[0]).map_err(err)?);
                }
                "thunk" => {
                    need(1)?;
                    self.thunks.insert(parse_addr(f[0]).map_err(err)?);
                }
                "linkage" => {
                    need(1)?;
                    let a = parse_addr(f[0]).map_err(err)?;
                    let mut h = LinkageHint::default();
                    for w in &f[1..] {
                        let u = w.to_ascii_uppercase();
                        match u.as_str() {
                            "NOVALUE" => h.value = Some(false),
                            "VALUE" => h.value = Some(true),
                            _ => {
                                let (kind, num) = u.split_at(1);
                                let k: i32 = num.parse().map_err(|_| err(format!("bad linkage word '{}'", w)))?;
                                match kind {
                                    "R" if (0..=5).contains(&k) => h.regs.push(k),
                                    "G" if (1..=5).contains(&k) => h.globals.push(k),
                                    _ => return Err(err(format!("bad linkage word '{}' (R0-R5, G1-G5, VALUE, NOVALUE)", w))),
                                }
                            }
                        }
                    }
                    h.regs.sort();
                    h.globals.sort();
                    self.linkages.insert(a, h);
                }
                "banklabel" => {
                    // banklabel ADDR NAME [local] [CALLER...]
                    need(2)?;
                    let a = parse_addr(f[0]).map_err(err)?;
                    let mut bl = BankLabel { name: f[1].to_string(), local: false, callers: vec![] };
                    for w in &f[2..] {
                        if *w == "local" { bl.local = true; } else { bl.callers.push(parse_addr(w).map_err(err)?); }
                    }
                    self.bank_labels.entry(a).or_default().push(bl);
                }
                "module" => {
                    need(1)?;
                    self.module = Some(f[0].to_string());
                }
                "environment" => {
                    self.environment = Some(rest.to_string());
                }
                _ => return Err(err(format!("unknown directive '{}'", head))),
            }
        }
        Ok(())
    }

    pub fn load_file(&mut self, path: &Path) -> Result<(), String> {
        let txt = std::fs::read_to_string(path).map_err(|e| format!("{}: {}", path.display(), e))?;
        let base = path.parent().map(|p| p.to_path_buf()).unwrap_or_default();
        self.parse(&txt, &base).map_err(|e| format!("{}: {}", path.display(), e))
    }

    /// The program as a project file (absolute image paths).
    pub fn to_text(&self) -> String {
        let mut s = String::new();
        let rng = |(lo, hi): &(u16, u32)| format!("{}-{:06o}", o6(*lo), hi);
        if let Some(m) = &self.module { s += &format!("module {}\n", m); }
        if let Some(e) = &self.environment { s += &format!("environment {}\n", e); }
        for f in &self.files {
            let p = std::fs::canonicalize(&f.path).unwrap_or_else(|_| f.path.clone());
            s += &format!("file {} {}\n", f.name, p.display());
        }
        for g in &self.segments {
            s += &format!("map {} {:06o} {} 0x{:x}\n", o6(g.vaddr), g.len, self.files[g.file].name, g.offset);
        }
        for r in &self.own { s += &format!("own {}\n", rng(r)); }
        for r in &self.banked { s += &format!("banked {}\n", rng(r)); }
        for r in &self.nocode { s += &format!("nocode {}\n", rng(r)); }
        for e in &self.entries { s += &format!("entry {}\n", o6(*e)); }
        let mut v: Vec<_> = self.names.iter().collect();
        v.sort();
        for (a, n) in v { s += &format!("label {} {}\n", o6(*a), n); }
        let mut v: Vec<_> = self.saves.iter().collect();
        v.sort();
        for (a, n) in v { s += &format!("save {} {}\n", o6(*a), n); }
        let mut v: Vec<_> = self.thunks.iter().collect();
        v.sort();
        for a in v { s += &format!("thunk {}\n", o6(*a)); }
        let mut v: Vec<_> = self.macros.iter().collect();
        v.sort();
        for a in v { s += &format!("macro {}\n", o6(*a)); }
        let mut v: Vec<_> = self.cases.iter().collect();
        v.sort();
        for (a, (t, n, b)) in v { s += &format!("case {} {} {}. {}\n", o6(*a), o6(*t), n, o6(*b)); }
        for (a, h) in &self.linkages {
            let mut w: Vec<String> = h.regs.iter().map(|k| format!("R{}", k)).collect();
            w.extend(h.globals.iter().map(|k| format!("G{}", k)));
            if let Some(v) = h.value { w.push(if v { "VALUE".into() } else { "NOVALUE".into() }); }
            s += &format!("linkage {} {}\n", o6(*a), w.join(" "));
        }
        let mut v: Vec<_> = self.bank_labels.iter().collect();
        v.sort_by_key(|x| *x.0);
        for (a, ls) in v {
            for l in ls {
                let mut w = vec![o6(*a), l.name.clone()];
                if l.local { w.push("local".into()); }
                w.extend(l.callers.iter().map(|c| o6(*c)));
                s += &format!("banklabel {}\n", w.join(" "));
            }
        }
        let mut v: Vec<_> = self.syms.iter().collect();
        v.sort_by_key(|x| *x.0);
        for (a, (n, c)) in v {
            let n = if n.is_empty() { "-" } else { n.as_str() };
            if c.is_empty() { s += &format!("sym {} {}\n", o6(*a), n); } else { s += &format!("sym {} {} ; {}\n", o6(*a), n, c); }
        }
        s
    }
}
