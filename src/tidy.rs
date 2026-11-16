// SPDX-License-Identifier: Apache-2.0
//! Post-pass over emitted BLISS lines: drop BEGIN/END around single statements, flatten ELSE IF
//! chains, drop a trailing LEAVE NEXTn and unused loop labels.  Purely cosmetic: the compiled code
//! is the same.

#[derive(Clone, Debug)]
struct N {
    ind: usize,
    text: String,
    kids: Vec<N>,
}

fn parse(lines: &[(usize, String)]) -> Vec<N> {
    // stack of (ind, path) — build by recursion over a slice
    fn build(lines: &[(usize, String)], i: &mut usize, level: usize) -> Vec<N> {
        let mut out = vec![];
        while *i < lines.len() {
            let (ind, ref t) = lines[*i];
            if ind < level {
                break;
            }
            *i += 1;
            let mut n = N { ind, text: t.clone(), kids: vec![] };
            if *i < lines.len() && lines[*i].0 > ind {
                n.kids = build(lines, i, ind + 1);
            }
            out.push(n);
        }
        out
    }
    let mut i = 0;
    let lvl = lines.iter().map(|x| x.0).min().unwrap_or(0);
    build(lines, &mut i, lvl)
}

fn render(v: &[N], out: &mut Vec<(usize, String)>) {
    for n in v {
        out.push((n.ind, n.text.clone()));
        render(&n.kids, out);
    }
}

fn shift(n: &mut N, d: isize) {
    n.ind = (n.ind as isize + d).max(0) as usize;
    for k in n.kids.iter_mut() {
        shift(k, d);
    }
}

/// statement groups among siblings: IF+THEN(+ELSE), CASE..TES;, or single nodes
fn groups(v: &[N]) -> Vec<(usize, usize)> {
    let mut g = vec![];
    let mut i = 0;
    while i < v.len() {
        let t = v[i].text.as_str();
        let mut j = i + 1;
        if t.starts_with("IF ") {
            while j < v.len() && (v[j].text == "THEN" || v[j].text == "ELSE" || v[j].text.starts_with("THEN ")
                || v[j].text.starts_with("ELSE ")) {
                j += 1;
            }
        } else if t.starts_with("CASE ") {
            while j < v.len() && !v[j - 1].text.starts_with("TES") {
                j += 1;
            }
        }
        g.push((i, j));
        i = j;
    }
    g
}

fn is_simple(n: &N) -> bool {
    n.kids.is_empty() && !n.text.starts_with("IF ") && !n.text.starts_with("CASE ") && !n.text.starts_with('!')
        && n.text.ends_with(';')
}

/// branch keyword node (THEN/ELSE) whose kids are [BEGIN{body}, END[;]]: the body if so
fn branch_body(k: &N) -> Option<(&Vec<N>, bool)> {
    if k.kids.len() == 2 && k.kids[0].text == "BEGIN" && k.kids[1].text.starts_with("END") {
        Some((&k.kids[0].kids, k.kids[1].text.ends_with(';')))
    } else {
        None
    }
}

fn tidy_list(v: Vec<N>) -> Vec<N> {
    // first tidy all children
    let mut v: Vec<N> = v
        .into_iter()
        .map(|mut n| {
            n.kids = tidy_list(std::mem::take(&mut n.kids));
            n
        })
        .collect();
    // ELSE IF flattening (repeat until stable)
    loop {
        let mut changed = false;
        let mut i = 0;
        while i < v.len() {
            if v[i].text == "ELSE" {
                if let Some((body, semi)) = branch_body(&v[i]) {
                    let gs = groups(body);
                    if semi && gs.len() == 1 && body[0].text.starts_with("IF ") {
                        let mut inner: Vec<N> = body.clone();
                        let ind = v[i].ind;
                        for n in inner.iter_mut() {
                            let d = ind as isize - n.ind as isize;
                            shift(n, d);
                        }
                        inner[0].text = format!("ELSE {}", inner[0].text);
                        v.splice(i..i + 1, inner);
                        changed = true;
                    }
                }
            }
            i += 1;
        }
        if !changed {
            break;
        }
    }
    // single-statement branches: THEN/ELSE + BEGIN + one simple statement + END
    for n in v.iter_mut() {
        let kw = n.text.clone();
        if kw != "THEN" && kw != "ELSE" {
            continue;
        }
        if let Some((body, semi)) = branch_body(n) {
            let one_line_if = body.len() == 1 && body[0].kids.is_empty() && body[0].text.starts_with("IF ")
                && body[0].text.ends_with(';') && semi;
            if body.len() == 1 && (is_simple(&body[0]) || one_line_if) {
                let mut s = body[0].text.clone();
                if !semi {
                    s.pop(); // statement before ELSE takes no ';'
                }
                n.text = format!("{} {}", kw, s);
                n.kids.clear();
            } else if body.is_empty() {
                n.text = format!("{} {}", kw, if semi { "0;" } else { "0" });
                n.kids.clear();
            }
        }
    }
    // IF c THEN LEAVE x ELSE BEGIN body END;  ->  IF c THEN LEAVE x; body   (also RETURN)
    let mut i = 0;
    while i + 2 < v.len() {
        let t1 = v[i + 1].text.clone();
        let hoist = v[i].text.starts_with("IF ") && v[i].kids.is_empty() && v[i + 1].kids.is_empty()
            && (t1.starts_with("THEN LEAVE ") || t1.starts_with("THEN RETURN")) && !t1.ends_with(';')
            && v[i + 2].text == "ELSE";
        if hoist {
            if let Some((body, semi)) = branch_body(&v[i + 2]) {
                if semi {
                    let ind = v[i].ind;
                    let mut inner: Vec<N> = body.clone();
                    for n in inner.iter_mut() { let d = ind as isize - n.ind as isize; shift(n, d); }
                    v[i + 1].text.push(';');
                    v.splice(i + 2..i + 3, inner);
                }
            }
        }
        i += 1;
    }
    // join a short IF onto one line:  IF c THEN s [ELSE s];
    let gs = groups(&v);
    let mut out: Vec<N> = vec![];
    for (a, b) in gs {
        let grp = &v[a..b];
        if grp[0].text.starts_with("IF ") || grp[0].text.starts_with("ELSE IF ") {
            let all_inline = grp[1..].iter().all(|n| n.kids.is_empty() && (n.text.starts_with("THEN ") || n.text.starts_with("ELSE ")));
            if all_inline && grp[0].kids.is_empty() {
                let line = grp.iter().map(|n| n.text.as_str()).collect::<Vec<_>>().join(" ");
                if line.len() + grp[0].ind * 4 <= 100 {
                    out.push(N { ind: grp[0].ind, text: line, kids: vec![] });
                    continue;
                }
            }
        }
        out.extend(grp.iter().cloned());
    }
    // trailing LEAVE NEXTn at the end of its own loop body
    for n in out.iter_mut() {
        if n.text.contains("WHILE ") {
            if let Some(b) = n.kids.first_mut() {
                if let Some(lab) = b.text.strip_suffix(": BEGIN") {
                    let leave = format!("LEAVE {};", lab);
                    if b.kids.last().map(|x| x.text == leave).unwrap_or(false) {
                        b.kids.pop();
                    }
                }
            }
        }
    }
    out
}

fn mentions(v: &[N], lab: &str) -> usize {
    let pat = format!("LEAVE {}", lab);
    let mut c = 0;
    for n in v {
        let t = &n.text;
        let mut from = 0;
        while let Some(p) = t[from..].find(&pat) {
            let after = t[from + p + pat.len()..].chars().next();
            if !after.map(|ch| ch.is_ascii_alphanumeric()).unwrap_or(false) {
                c += 1;
            }
            from += p + pat.len();
        }
        c += mentions(&n.kids, lab);
    }
    c
}

/// "IF c THEN LEAVE LOOPn[;]" / "... ELSE LEAVE NEXTn;" as one line or as an IF/THEN(/ELSE) group -> c
fn exit_test(grp: &[N], lp: &str, nx: &str) -> Option<String> {
    let joined: String = grp.iter().map(|n| n.text.clone()).collect::<Vec<_>>().join(" ");
    if grp.iter().any(|n| !n.kids.is_empty()) {
        return None;
    }
    let body = joined.strip_prefix("IF ")?;
    for tail in [format!(" THEN LEAVE {};", lp), format!(" THEN LEAVE {} ELSE LEAVE {};", lp, nx)] {
        if let Some(c) = body.strip_suffix(tail.as_str()) {
            return Some(c.to_string());
        }
    }
    None
}

/// LOOPn: BEGIN / WHILE 1 DO NEXTn: BEGIN body END; / END;  ->  UNTIL c DO body  |  DO body UNTIL c
fn loop_forms(v: Vec<N>) -> Vec<N> {
    let mut v: Vec<N> = v.into_iter().map(|mut n| { n.kids = loop_forms(std::mem::take(&mut n.kids)); n }).collect();
    let mut i = 0;
    while i + 2 < v.len() {
        let lp = match v[i].text.strip_suffix(": BEGIN") { Some(l) if l.starts_with("LOOP") => l.to_string(), _ => { i += 1; continue; } };
        if v[i + 1].text != "WHILE 1 DO" || v[i + 2].text != format!("END;  ! {}", lp) || v[i + 1].kids.len() != 2 {
            i += 1;
            continue;
        }
        let nx = format!("NEXT{}", &lp[4..]);
        let bl = &v[i + 1].kids[0];
        if bl.text != format!("{}: BEGIN", nx) && bl.text != "BEGIN" {
            i += 1;
            continue;
        }
        let body = bl.kids.clone();
        let gs = groups(&body);
        let ind = v[i].ind;
        let total_lp = mentions(&body, &lp);
        let total_nx = mentions(&body, &nx);
        let mut repl: Option<Vec<N>> = None;
        // exit test first: UNTIL c DO rest
        if let Some(&(a, b)) = gs.first() {
            if let Some(c) = exit_test(&body[a..b], &lp, &nx) {
                let rest: Vec<N> = body[b..].to_vec();
                let own_nx = if body[a..b].iter().any(|n| n.text.contains(&format!("LEAVE {}", nx))) { 1 } else { 0 };
                if total_lp == 1 && total_nx == own_nx && !rest.is_empty() && own_nx == 0 {
                    let mut blk = N { ind: ind + 1, text: "BEGIN".into(), kids: rest };
                    for k in blk.kids.iter_mut() { let d = (ind + 2) as isize - k.ind as isize; shift(k, d); }
                    repl = Some(vec![N { ind, text: format!("UNTIL {} DO", c), kids: vec![blk, N { ind: ind + 1, text: "END;".into(), kids: vec![] }] }]);
                }
            }
        }
        // exit test last: DO body UNTIL c
        if repl.is_none() {
            if let Some(&(a, b)) = gs.last() {
                if let Some(c) = exit_test(&body[a..b], &lp, &nx) {
                    let own_nx = if body[a..b].iter().any(|n| n.text.contains(&format!("LEAVE {}", nx))) { 1 } else { 0 };
                    if total_lp == 1 && total_nx == own_nx && a > 0 {
                        let mut blk = N { ind: ind + 1, text: "BEGIN".into(), kids: body[..a].to_vec() };
                        for k in blk.kids.iter_mut() { let d = (ind + 2) as isize - k.ind as isize; shift(k, d); }
                        repl = Some(vec![
                            N { ind, text: "DO".into(), kids: vec![blk, N { ind: ind + 1, text: "END".into(), kids: vec![] }] },
                            N { ind, text: format!("UNTIL {};", c), kids: vec![] },
                        ]);
                    }
                }
            }
        }
        match repl {
            Some(r) => { let n = r.len(); v.splice(i..i + 3, r); i += n; }
            None => i += 3,
        }
    }
    v
}

/// LEAVE right after RETURN in the same block is never reached (the compiler drops it too)
fn drop_after_return(v: Vec<N>) -> Vec<N> {
    let v: Vec<N> = v.into_iter().map(|mut n| { n.kids = drop_after_return(std::mem::take(&mut n.kids)); n }).collect();
    let mut out: Vec<N> = vec![];
    for n in v {
        if n.text.starts_with("LEAVE ") && n.kids.is_empty() {
            if let Some(p) = out.last() {
                if p.text.starts_with("RETURN") && p.kids.is_empty() { continue; }
            }
        }
        out.push(n);
    }
    out
}

fn all_text(v: &[N], acc: &mut String) {
    for n in v {
        acc.push_str(&n.text);
        acc.push('\n');
        all_text(&n.kids, acc);
    }
}

fn mentions_var(text: &str, x: &str) -> bool {
    let pat = format!(".{}", x);
    let mut from = 0;
    while let Some(p) = text[from..].find(&pat) {
        let after = text[from + p + pat.len()..].chars().next();
        if !after.map(|c| c.is_ascii_alphanumeric() || c == '_').unwrap_or(false) {
            return true;
        }
        from += p + pat.len();
    }
    false
}

/// X = a; DO body; X = .X + 1 UNTIL .X GTR b  ->  INCR X FROM a TO b DO body   (knob 13)
/// X = n; DO body; X = .X + -1 UNTIL .X EQL 0 ->  DECR X FROM n TO 1 DO body   (knob 12)
fn counted_loops(v: Vec<N>, incr: bool, decr: bool) -> Vec<N> {
    let mut v: Vec<N> = v.into_iter().map(|mut n| { n.kids = counted_loops(std::mem::take(&mut n.kids), incr, decr); n }).collect();
    // knob 25: X = a; UNTIL .X GEQ b DO BEGIN body; X = .X + 1 END  ->  INCR X FROM a TO b - 1 DO body
    if crate::lift::knob(25) {
        let mut i = 1;
        while i < v.len() {
            let t = v[i].text.clone();
            let ok_shape = t.starts_with("UNTIL .") && t.ends_with(" DO") && v[i].kids.len() == 2 && v[i].kids[0].text == "BEGIN";
            let (x, init) = match v[i - 1].text.split_once(" = ") {
                Some((x, a)) if v[i - 1].kids.is_empty() && !x.contains(' ') && a.ends_with(';') => (x.to_string(), a.trim_end_matches(';').to_string()),
                _ => (String::new(), String::new()),
            };
            if !ok_shape || x.is_empty() { i += 1; continue; }
            let cond = &t["UNTIL ".len()..t.len() - 3];
            let hi = if let Some(b) = cond.strip_prefix(&format!(".{} GEQ ", x)) {
                Some(format!("{} - 1", b))
            } else { cond.strip_prefix(&format!(".{} GTR ", x)).map(|b| b.to_string()) };
            let body = &v[i].kids[0].kids;
            let last_ok = body.last().map(|l| l.kids.is_empty() && l.text == format!("{} = .{} + 1;", x, x)).unwrap_or(false);
            let mut rest = String::new();
            all_text(&v[i + 1..], &mut rest);
            let mut inner = String::new();
            all_text(&body[..body.len().saturating_sub(1)], &mut inner);
            let hi = match hi { Some(h) if last_ok && !mentions_var(&rest, &x) && !inner.contains(&format!("{} =", x)) && !mentions_var(&h, &x) => h, _ => { i += 1; continue; } };
            // an empty counting loop is a delay: as INCR ... DO 0 the compiler deletes it
            if body.len() == 1 { i += 1; continue; }
            let ind = v[i - 1].ind;
            let mut kids: Vec<N> = body[..body.len() - 1].to_vec();
            for k in kids.iter_mut() { let d = (ind + 2) as isize - k.ind as isize; shift(k, d); }
            let node = if kids.is_empty() {
                N { ind, text: format!("INCR {} FROM {} TO {} DO 0;", x, init, hi), kids: vec![] }
            } else {
                N { ind, text: format!("INCR {} FROM {} TO {} DO", x, init, hi),
                    kids: vec![N { ind: ind + 1, text: "BEGIN".into(), kids }, N { ind: ind + 1, text: "END;".into(), kids: vec![] }] }
            };
            v.splice(i - 1..i + 1, vec![node]);
        }
    }
    let mut i = 1;
    while i + 1 < v.len() {
        if v[i].text != "DO" || v[i].kids.len() != 2 || v[i].kids[0].text != "BEGIN" {
            i += 1;
            continue;
        }
        let body = &v[i].kids[0].kids;
        let last = match body.last() { Some(l) if l.kids.is_empty() => l.text.clone(), _ => { i += 1; continue; } };
        let (x, init) = match v[i - 1].text.split_once(" = ") {
            Some((x, a)) if v[i - 1].kids.is_empty() && !x.contains(' ') && a.ends_with(';') => (x.to_string(), a.trim_end_matches(';').to_string()),
            _ => { i += 1; continue; }
        };
        let until = v[i + 1].text.clone();
        let form = if decr && last == format!("{} = .{} + -1;", x, x) && until == format!("UNTIL .{} EQL 0;", x) {
            Some(format!("DECR {} FROM {} TO 1 DO", x, init))
        } else if incr && last == format!("{} = .{} + 1;", x, x) && until.starts_with(&format!("UNTIL .{} GTR ", x)) {
            let b = until[format!("UNTIL .{} GTR ", x).len()..].trim_end_matches(';').to_string();
            Some(format!("INCR {} FROM {} TO {} DO", x, init, b))
        } else {
            None
        };
        let form = match form { Some(f) => f, None => { i += 1; continue; } };
        // an empty counting loop is a delay (MOV #n,R0 / SOB R0,.): as DECR ... DO 0 the compiler
        // sees it has no effect and deletes it
        if body.len() == 1 { i += 1; continue; }
        // the index must not be read after the loop (it is the loop's own variable)
        let mut rest = String::new();
        all_text(&v[i + 2..], &mut rest);
        if mentions_var(&rest, &x) {
            i += 1;
            continue;
        }
        let ind = v[i - 1].ind;
        let mut kids: Vec<N> = body[..body.len() - 1].to_vec();
        let node = if kids.is_empty() {
            N { ind, text: format!("{} 0;", form), kids: vec![] }
        } else {
            for k in kids.iter_mut() { let d = (ind + 2) as isize - k.ind as isize; shift(k, d); }
            N { ind, text: form, kids: vec![N { ind: ind + 1, text: "BEGIN".into(), kids }, N { ind: ind + 1, text: "END;".into(), kids: vec![] }] }
        };
        v.splice(i - 1..i + 2, vec![node]);
    }
    v
}

pub fn tidy(lines: Vec<(usize, String)>) -> Vec<(usize, String)> {
    if lines.is_empty() {
        return lines;
    }
    let tree = drop_after_return(loop_forms(tidy_list(parse(&lines))));
    let tree = counted_loops(tree, crate::lift::knob(13), crate::lift::knob(12));
    let mut out = vec![];
    render(&tree, &mut out);
    // unused labels: LOOPn wraps "LOOPn: BEGIN ... END;  ! LOOPn" (drop both lines), NEXTn just loses its prefix
    let text: String = out.iter().map(|x| x.1.as_str()).collect::<Vec<_>>().join("\n");
    let used = |lab: &str| -> bool {
        let pat = format!("LEAVE {}", lab);
        let mut from = 0;
        while let Some(p) = text[from..].find(&pat) {
            let after = text[from + p + pat.len()..].chars().next();
            if !after.map(|c| c.is_ascii_alphanumeric()).unwrap_or(false) {
                return true;
            }
            from += p + pat.len();
        }
        false
    };
    let mut res: Vec<(usize, String)> = vec![];
    for (ind, l) in out.into_iter() {
        if let Some(lab) = l.strip_suffix(": BEGIN") {
            if lab.starts_with("LOOP") && !used(lab) {
                continue;
            }
            if lab.starts_with("NEXT") && !used(lab) {
                res.push((ind, "BEGIN".into()));
                continue;
            }
        }
        if let Some(lab) = l.strip_prefix("END;  ! ") {
            if !used(lab) {
                continue;
            }
        }
        res.push((ind, l));
    }
    res
}

pub fn used_labels(lines: &[(usize, String)]) -> Vec<String> {
    let mut v: Vec<String> = vec![];
    for (_, l) in lines {
        for pre in ["LOOP", "NEXT"] {
            if l.starts_with(pre) {
                if let Some(p) = l.find(": ") {
                    v.push(l[..p].to_string());
                }
            }
        }
    }
    v.sort();
    v.dedup();
    v
}
