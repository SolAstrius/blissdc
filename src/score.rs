// SPDX-License-Identifier: Apache-2.0
//! Scoring compiled BLISS-16 listings against the original binary.
//!
//! The map (from `blissdc map`) has one line per original instruction: routine, address, octal words,
//! disassembly.  A BLISS-16 `.LST` file has, per instruction, `PC<TAB>WORDS<TAB>TEXT`, where a word
//! may carry a relocation mark (`G`, `V`, `'`, ...); routine sections start at the `NAME::` label.
//! Instructions are aligned per routine by their first word (Python difflib's `SequenceMatcher`,
//! ported here exactly so the numbers agree with the original `score.py`), and an aligned pair counts
//! as exact when all words agree, relocated words being wildcards; `JSR PC` compares the target name,
//! since the displacement depends on how routines are packed into modules.

use std::collections::HashMap;

// ------------------------------------------------------------------ difflib
/// `difflib.SequenceMatcher(None, a, b, autojunk=False)` over interned symbols.
pub struct SequenceMatcher<'a> {
    a: &'a [u32],
    b: &'a [u32],
    b2j: HashMap<u32, Vec<usize>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tag {
    Equal,
    Replace,
    Delete,
    Insert,
}

impl<'a> SequenceMatcher<'a> {
    pub fn new(a: &'a [u32], b: &'a [u32]) -> SequenceMatcher<'a> {
        let mut b2j: HashMap<u32, Vec<usize>> = HashMap::new();
        for (j, x) in b.iter().enumerate() {
            b2j.entry(*x).or_default().push(j);
        }
        SequenceMatcher { a, b, b2j }
    }

    fn find_longest_match(&self, alo: usize, ahi: usize, blo: usize, bhi: usize) -> (usize, usize, usize) {
        let (a, b) = (self.a, self.b);
        let (mut besti, mut bestj, mut bestsize) = (alo, blo, 0usize);
        let mut j2len: HashMap<usize, usize> = HashMap::new();
        for (i, ai) in a.iter().enumerate().take(ahi).skip(alo) {
            let mut newj2len: HashMap<usize, usize> = HashMap::new();
            if let Some(js) = self.b2j.get(ai) {
                for &j in js {
                    if j < blo {
                        continue;
                    }
                    if j >= bhi {
                        break;
                    }
                    let k = if j > 0 { j2len.get(&(j - 1)).cloned().unwrap_or(0) } else { 0 } + 1;
                    newj2len.insert(j, k);
                    if k > bestsize {
                        besti = i + 1 - k;
                        bestj = j + 1 - k;
                        bestsize = k;
                    }
                }
            }
            j2len = newj2len;
        }
        // no junk: the extensions difflib does around junk elements are no-ops, but keep them exact
        while besti > alo && bestj > blo && a[besti - 1] == b[bestj - 1] {
            besti -= 1;
            bestj -= 1;
            bestsize += 1;
        }
        while besti + bestsize < ahi && bestj + bestsize < bhi && a[besti + bestsize] == b[bestj + bestsize] {
            bestsize += 1;
        }
        (besti, bestj, bestsize)
    }

    pub fn matching_blocks(&self) -> Vec<(usize, usize, usize)> {
        let (la, lb) = (self.a.len(), self.b.len());
        let mut queue = vec![(0, la, 0, lb)];
        let mut mb = vec![];
        while let Some((alo, ahi, blo, bhi)) = queue.pop() {
            let (i, j, k) = self.find_longest_match(alo, ahi, blo, bhi);
            if k > 0 {
                mb.push((i, j, k));
                if alo < i && blo < j {
                    queue.push((alo, i, blo, j));
                }
                if i + k < ahi && j + k < bhi {
                    queue.push((i + k, ahi, j + k, bhi));
                }
            }
        }
        mb.sort();
        let (mut i1, mut j1, mut k1) = (0, 0, 0);
        let mut out = vec![];
        for (i2, j2, k2) in mb {
            if i1 + k1 == i2 && j1 + k1 == j2 {
                k1 += k2;
            } else {
                if k1 > 0 {
                    out.push((i1, j1, k1));
                }
                i1 = i2;
                j1 = j2;
                k1 = k2;
            }
        }
        if k1 > 0 {
            out.push((i1, j1, k1));
        }
        out.push((la, lb, 0));
        out
    }

    pub fn opcodes(&self) -> Vec<(Tag, usize, usize, usize, usize)> {
        let (mut i, mut j) = (0, 0);
        let mut ans = vec![];
        for (ai, bj, size) in self.matching_blocks() {
            let tag = if i < ai && j < bj {
                Some(Tag::Replace)
            } else if i < ai {
                Some(Tag::Delete)
            } else if j < bj {
                Some(Tag::Insert)
            } else {
                None
            };
            if let Some(t) = tag {
                ans.push((t, i, ai, j, bj));
            }
            i = ai + size;
            j = bj + size;
            if size > 0 {
                ans.push((Tag::Equal, ai, i, bj, j));
            }
        }
        ans
    }
}

// ------------------------------------------------------------------ Python string helpers
/// Python's str.isspace() for Latin-1 text
fn py_space(c: char) -> bool {
    matches!(c, ' ' | '\t' | '\n' | '\r' | '\x0b' | '\x0c' | '\x1c' | '\x1d' | '\x1e' | '\x1f' | '\u{85}' | '\u{a0}')
}

fn py_strip(s: &str) -> &str {
    s.trim_matches(py_space)
}

/// re.sub(r'\s+', ' ', s)
fn squash(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut sp = false;
    for c in s.chars() {
        if py_space(c) {
            if !sp {
                out.push(' ');
            }
            sp = true;
        } else {
            out.push(c);
            sp = false;
        }
    }
    out
}

/// re.sub(r'^\S+:\s*', '', s): drop a leading label
fn strip_label(s: &str) -> String {
    let ch: Vec<char> = s.chars().collect();
    let end = ch.iter().position(|c| py_space(*c)).unwrap_or(ch.len());
    match ch[..end].iter().rposition(|c| *c == ':') {
        Some(k) if k >= 1 => {
            let mut i = k + 1;
            while i < ch.len() && py_space(ch[i]) {
                i += 1;
            }
            ch[i..].iter().collect()
        }
        _ => s.to_string(),
    }
}

/// Latin-1 text, lines split the way Python's universal newlines do
pub fn read_latin1_lines(path: &str) -> Result<Vec<String>, String> {
    let b = std::fs::read(path).map_err(|e| format!("{}: {}", path, e))?;
    let s: String = b.iter().map(|&c| c as char).collect();
    let s = s.replace("\r\n", "\n").replace('\r', "\n");
    let mut v: Vec<String> = s.split('\n').map(|x| x.to_string()).collect();
    if v.last().map(|x| x.is_empty()).unwrap_or(false) {
        v.pop();
    }
    Ok(v)
}

// ------------------------------------------------------------------ listings
/// one listing instruction: words (with relocation marks), text (field 3 after the second tab)
pub struct LstLine {
    pub words: Vec<String>,
    pub text: String,
}

/// `^(\d{6})\t((?:\d{6}[ A-Z']? *)+)\t(.*)`: (words, rest)
fn lst_insn(l: &str) -> Option<(Vec<String>, String)> {
    let b: Vec<char> = l.chars().collect();
    if b.len() < 8 || !b[..6].iter().all(|c| c.is_ascii_digit()) || b[6] != '\t' {
        return None;
    }
    let tab2 = b[7..].iter().position(|c| *c == '\t')? + 7;
    let f = &b[7..tab2];
    let mut ws = vec![];
    let mut p = 0;
    loop {
        if p + 6 > f.len() || !f[p..p + 6].iter().all(|c| c.is_ascii_digit()) {
            return None;
        }
        let mut w: String = f[p..p + 6].iter().collect();
        p += 6;
        if p < f.len() && (f[p] == ' ' || f[p] == '\'' || f[p].is_ascii_uppercase()) {
            if f[p] != ' ' {
                w.push(f[p]);
            }
            p += 1;
        }
        while p < f.len() && f[p] == ' ' {
            p += 1;
        }
        ws.push(w);
        if p == f.len() {
            break;
        }
    }
    Some((ws, b[tab2 + 1..].iter().collect()))
}

/// `\t([A-Z$.][A-Z0-9$.]*)::` anywhere in the line
fn section_label(l: &str) -> Option<String> {
    let b: Vec<char> = l.chars().collect();
    for i in 0..b.len() {
        if b[i] != '\t' || i + 1 >= b.len() {
            continue;
        }
        let c0 = b[i + 1];
        if !(c0.is_ascii_uppercase() || c0 == '$' || c0 == '.') {
            continue;
        }
        let mut j = i + 2;
        while j < b.len() && (b[j].is_ascii_uppercase() || b[j].is_ascii_digit() || b[j] == '$' || b[j] == '.') {
            j += 1;
        }
        if j + 1 < b.len() && b[j] == ':' && b[j + 1] == ':' {
            return Some(b[i + 1..j].iter().collect());
        }
    }
    None
}

/// `^\t{5,}([A-Z$.].*)`
fn continuation(l: &str) -> Option<&str> {
    let n = l.chars().take_while(|c| *c == '\t').count();
    if n < 5 {
        return None;
    }
    let rest = &l[n..];
    let c0 = rest.chars().next()?;
    if c0.is_ascii_uppercase() || c0 == '$' || c0 == '.' { Some(rest) } else { None }
}

fn before_semi(s: &str) -> &str {
    s.split(';').next().unwrap_or("")
}

/// Routine sections of compiled listings, keyed by routine name (`.` as `_`), in first-seen order.
pub fn lst_sections(files: &[String]) -> Result<Vec<(String, Vec<LstLine>)>, String> {
    let mut secs: Vec<(String, Vec<LstLine>)> = vec![];
    let mut idx: HashMap<String, usize> = HashMap::new();
    for fname in files {
        let mut cur: Option<String> = None;
        for l in read_latin1_lines(fname)? {
            let m = lst_insn(&l);
            if m.is_some() {
                if let Some(g) = section_label(&l) {
                    let name = g.replace('.', "_");
                    match idx.get(&name) {
                        Some(&k) => secs[k].1.clear(),
                        None => {
                            idx.insert(name.clone(), secs.len());
                            secs.push((name.clone(), vec![]));
                        }
                    }
                    cur = Some(name);
                }
            }
            if let (Some((ws, rest)), Some(c)) = (&m, &cur) {
                let txt = squash(&strip_label(py_strip(before_semi(rest))));
                secs[idx[c]].1.push(LstLine { words: ws.clone(), text: txt });
                continue;
            }
            if let (Some(rest), Some(c)) = (continuation(&l), &cur) {
                let v = &mut secs[idx[c]].1;
                if let Some(last) = v.last_mut() {
                    if last.text.is_empty() {
                        last.text = squash(py_strip(before_semi(rest)));
                    }
                }
            }
        }
    }
    Ok(secs)
}

// ------------------------------------------------------------------ map
pub struct MapLine {
    pub words: Vec<String>,
    pub text: String,
}

/// routine -> original instructions, in first-seen order
pub fn read_map(path: &str) -> Result<Vec<(String, Vec<MapLine>)>, String> {
    let txt = std::fs::read_to_string(path).map_err(|e| format!("{}: {}", path, e))?;
    let mut v: Vec<(String, Vec<MapLine>)> = vec![];
    let mut idx: HashMap<String, usize> = HashMap::new();
    for l in txt.lines() {
        let f: Vec<&str> = l.split('\t').collect();
        if f.len() < 3 {
            continue;
        }
        let k = *idx.entry(f[0].to_string()).or_insert_with(|| {
            v.push((f[0].to_string(), vec![]));
            v.len() - 1
        });
        v[k].1.push(MapLine {
            words: f[2].split_whitespace().map(|x| x.to_string()).collect(),
            text: f.get(3).map(|x| x.to_string()).unwrap_or_default(),
        });
    }
    Ok(v)
}

// ------------------------------------------------------------------ comparison
fn key(ws: &[String]) -> Vec<&str> {
    ws.iter()
        .map(|w| {
            let last = w.chars().last();
            if last.map(|c| c.is_alphabetic()).unwrap_or(false) || w.ends_with('\'') { "?" } else { w.as_str() }
        })
        .collect()
}

fn norm_target(t: &str) -> String {
    py_strip(t).replace('.', "_").to_uppercase()
}

fn last_operand(t: &str) -> &str {
    t.rsplit(',').next().unwrap_or("")
}

fn eq_score(rw: &[String], rt: &str, mw: &[String], mt: &str) -> bool {
    let (a, b) = (key(rw), key(mw));
    if a.len() != b.len() {
        return false;
    }
    if a[0] == "004767" && b[0] == "004767" {
        return norm_target(last_operand(rt)) == norm_target(last_operand(mt));
    }
    a.iter().zip(b.iter()).all(|(x, y)| *x == "?" || *y == "?" || x == y)
}

fn first6(ws: &[String]) -> String {
    ws.first().map(|w| w.chars().take(6).collect()).unwrap_or_default()
}

struct Interner(HashMap<String, u32>);
impl Interner {
    fn id(&mut self, s: String) -> u32 {
        let n = self.0.len() as u32;
        *self.0.entry(s).or_insert(n)
    }
}

pub struct Row {
    pub name: String,
    pub rom: usize,
    pub mine: usize,
    pub exact: usize,
}

/// per-routine exact counts, in map order
pub fn score_rows(map: &[(String, Vec<MapLine>)], secs: &[(String, Vec<LstLine>)]) -> Vec<Row> {
    let empty: Vec<LstLine> = vec![];
    let by: HashMap<&str, &Vec<LstLine>> = secs.iter().map(|(n, v)| (n.as_str(), v)).collect();
    let mut rows = vec![];
    for (name, rk) in map {
        let mk = by.get(name.as_str()).cloned().unwrap_or(&empty);
        let mut it = Interner(HashMap::new());
        let a: Vec<u32> = rk.iter().map(|x| it.id(first6(&x.words))).collect();
        let b: Vec<u32> = mk.iter().map(|x| it.id(first6(&x.words))).collect();
        let sm = SequenceMatcher::new(&a, &b);
        let mut exact = 0;
        for (tag, a1, a2, b1, _) in sm.opcodes() {
            if tag != Tag::Equal {
                continue;
            }
            for (i, j) in (a1..a2).zip(b1..) {
                if eq_score(&rk[i].words, &rk[i].text, &mk[j].words, &mk[j].text) {
                    exact += 1;
                }
            }
        }
        rows.push(Row { name: name.clone(), rom: rk.len(), mine: mk.len(), exact });
    }
    rows
}

/// the report score.py prints
pub fn score_report(rows: &[Row]) -> String {
    let mut s = String::new();
    let mut v: Vec<&Row> = rows.iter().collect();
    v.sort_by(|x, y| {
        let fx = -(x.exact as f64) / (x.rom.max(1) as f64);
        let fy = -(y.exact as f64) / (y.rom.max(1) as f64);
        fx.partial_cmp(&fy).unwrap()
    });
    for r in v {
        s += &format!("{:<24} rom {:4} mine {:4} exact {:4}  {:5.1}%\n", r.name, r.rom, r.mine, r.exact,
            100.0 * r.exact as f64 / r.rom.max(1) as f64);
    }
    let tot: usize = rows.iter().map(|r| r.rom).sum();
    let ex: usize = rows.iter().map(|r| r.exact).sum();
    // strict: extra instructions of ours count against the match
    let big: usize = rows.iter().map(|r| r.rom.max(r.mine)).sum();
    s += &format!("TOTAL routines {} (compiled {}), ROM instructions {}, exact {} ({:.1}%), strict {:.1}% (exact / larger of ROM and ours)\n",
        rows.len(), rows.iter().filter(|r| r.mine > 0).count(), tot, ex, 100.0 * ex as f64 / tot.max(1) as f64,
        100.0 * ex as f64 / big.max(1) as f64);
    s += &format!("fully exact routines: {}\n", rows.iter().filter(|r| r.exact == r.rom).count());
    s
}

// ------------------------------------------------------------------ side by side (sbs.py)
/// The listing's instructions of routine `name` for the side-by-side view (label kept in the text).
fn sbs_mine(files: &[String], name: &str) -> Result<Vec<LstLine>, String> {
    let mut mine: Vec<LstLine> = vec![];
    let mut cur: Option<String> = None;
    for fname in files {
        for l in read_latin1_lines(fname)? {
            let m = lst_insn(&l);
            if m.is_some() {
                if let Some(g) = section_label(&l) {
                    cur = Some(g.replace('.', "_"));
                }
            }
            if let Some((ws, rest)) = &m {
                if cur.as_deref() == Some(name) {
                    mine.push(LstLine { words: ws.clone(), text: py_strip(&squash(before_semi(rest))).to_string() });
                    continue;
                }
            }
            if let Some(rest) = continuation(&l) {
                if cur.as_deref() == Some(name) {
                    if let Some(last) = mine.last_mut() {
                        if last.text.ends_with("::") {
                            last.text = format!("{} {}", last.text, squash(py_strip(before_semi(rest))));
                        }
                    }
                }
            }
        }
    }
    Ok(mine)
}

fn eq_sbs(rw: &[String], rt: &str, mw: &[String], mt: &str) -> bool {
    let (a, b) = (key(rw), key(mw));
    let nt = |t: &str| -> String { norm_target(last_operand(&strip_label(t))) };
    if a.len() == b.len() && a[0] == "004767" && b[0] == "004767" {
        return nt(rt) == nt(mt);
    }
    a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| *x == "?" || *y == "?" || x == y)
}

/// original vs compiled for one routine, aligned like the score: `=` exact, `~` aligned but
/// different, `|` unaligned
pub fn side_by_side(map: &[(String, Vec<MapLine>)], name: &str, lsts: &[String]) -> Result<String, String> {
    let rom: Vec<&MapLine> = map.iter().filter(|(n, _)| n == name).flat_map(|(_, v)| v.iter()).collect();
    let mine = sbs_mine(lsts, name)?;
    let mut it = Interner(HashMap::new());
    let a: Vec<u32> = rom.iter().map(|x| it.id(first6(&x.words))).collect();
    let b: Vec<u32> = mine.iter().map(|x| it.id(first6(&x.words))).collect();
    let sm = SequenceMatcher::new(&a, &b);
    let mut s = String::new();
    for (tag, a1, a2, b1, b2) in sm.opcodes() {
        let n = (a2 - a1).max(b2 - b1);
        for k in 0..n {
            let r = if a1 + k < a2 { Some(rom[a1 + k]) } else { None };
            let m = if b1 + k < b2 { Some(&mine[b1 + k]) } else { None };
            let mark = if tag == Tag::Equal {
                let (r, m) = (r.unwrap(), m.unwrap());
                if eq_sbs(&r.words, &r.text, &m.words, &m.text) { "=" } else { "~" }
            } else {
                "|"
            };
            s += &format!("{:<34} {} {}\n", r.map(|x| x.text.as_str()).unwrap_or(""), mark, m.map(|x| x.text.as_str()).unwrap_or(""));
        }
    }
    Ok(s)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ops(a: &str, b: &str) -> Vec<(Tag, usize, usize, usize, usize)> {
        let a: Vec<u32> = a.bytes().map(|c| c as u32).collect();
        let b: Vec<u32> = b.bytes().map(|c| c as u32).collect();
        SequenceMatcher::new(&a, &b).opcodes()
    }

    #[test]
    fn difflib_matches_python() {
        // difflib.SequenceMatcher(None, "qabxcd", "abycdf", autojunk=False).get_opcodes()
        assert_eq!(ops("qabxcd", "abycdf"), vec![
            (Tag::Delete, 0, 1, 0, 0), (Tag::Equal, 1, 3, 0, 2), (Tag::Replace, 3, 4, 2, 3),
            (Tag::Equal, 4, 6, 3, 5), (Tag::Insert, 6, 6, 5, 6)]);
        assert_eq!(ops("abc", "abc"), vec![(Tag::Equal, 0, 3, 0, 3)]);
        assert_eq!(ops("", "ab"), vec![(Tag::Insert, 0, 0, 0, 2)]);
    }

    #[test]
    fn listing_line() {
        let (ws, rest) = lst_insn("000012\t004767 000000G\t\tJSR\tPC,FOO").unwrap();
        assert_eq!(ws, vec!["004767", "000000G"]);
        assert_eq!(rest, "\tJSR\tPC,FOO");
        assert!(lst_insn("000012\t00476\tX").is_none());
        assert_eq!(section_label("000000\t010146\tFOO.BA::\tMOV R1,-(SP)").as_deref(), Some("FOO.BA"));
        assert_eq!(strip_label("1$:  MOV R1,R2"), "MOV R1,R2");
        assert_eq!(strip_label("MOV R1,R2"), "MOV R1,R2");
    }
}
