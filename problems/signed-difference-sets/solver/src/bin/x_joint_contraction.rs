//! Exploration (D15x): joint contraction. Coset sums Y1 on H1 = G/K1 and Y2 on H2 = G/K2 of one SDS contract to the same
//! vector on H12 = G/(K1 + K2). Pair test: V12 = vectors on H12; T1 = those with a lift to H1; kill if no z ∈ T1 lifts to
//! H2. Only K1 ∩ K2 = 0, K1 + K2 ≠ G (otherwise a vector on the proper quotient G/(K1 ∩ K2) passes it, or H12 = 1).
//! Modes add Ma's constraints (C21's step) on every Ma quotient H = C_{p^j} × K of G a searched quotient maps onto:
//! `div`: p | W on H/P (C33/C34); `ma`: also Y_H(x) ≡ Y_H(x + u) mod p^b (u ∈ P). In `div`/`ma` every proper quotient J
//! is also searched alone with those constraints (`single`). `plain` with `singles` = E8's test (agreement check).
//! Usage: `x_joint_contraction <instances.csv> <plain|div|ma> <max_nodes> <threads> <out> [<id file>] [singles]
//! [noval]`. Validates on every `exists` row first unless `noval` (none may be killed).
//! Line: id key v mode `KILL pair|single …` | `open …` (`pass`/`cut` counts) | `skip …`.

use signed_difference_sets::instances::{read, Instance};
use signed_difference_sets::{is_sds, Group};
use std::collections::{HashMap, HashSet};
use std::io::Write;
use std::sync::{Arc, Mutex};

const MAX_SUBGROUPS: usize = 4000;
const MAX_SIDE: usize = 64;
const MAX_V12: usize = 300_000;
const MAX_PAIRS: usize = 2500;

#[derive(Clone, Copy, PartialEq, Debug)]
enum Mode {
    Plain,
    Div,
    Ma,
    /// G = Z_p × Z_p: all p + 1 quotients at once (`tomography`).
    Tomo,
}

type Bits = Vec<u64>;

fn bits_new(n: usize) -> Bits {
    vec![0; n.div_ceil(64)]
}
fn has(b: &Bits, i: usize) -> bool {
    (b[i / 64] >> (i % 64)) & 1 == 1
}
fn put(b: &mut Bits, i: usize) {
    b[i / 64] |= 1 << (i % 64);
}
fn subset(a: &Bits, b: &Bits) -> bool {
    a.iter().zip(b).all(|(x, y)| x & !y == 0)
}
fn size(b: &Bits) -> usize {
    b.iter().map(|w| w.count_ones() as usize).sum()
}
fn elems(b: &Bits, n: usize) -> Vec<usize> {
    (0..n).filter(|&i| has(b, i)).collect()
}
fn meet(a: &Bits, b: &Bits) -> Bits {
    a.iter().zip(b).map(|(x, y)| x & y).collect()
}

fn cyclic(g: &Group, x: usize) -> Bits {
    let mut b = bits_new(g.order);
    let mut y = 0;
    loop {
        put(&mut b, y);
        y = g.add[y][x];
        if y == 0 {
            return b;
        }
    }
}

fn join(g: &Group, a: &Bits, b: &Bits) -> Bits {
    let (ea, eb) = (elems(a, g.order), elems(b, g.order));
    let mut out = bits_new(g.order);
    for &x in &ea {
        for &y in &eb {
            put(&mut out, g.add[x][y]);
        }
    }
    out
}

/// Every subgroup of G (trivial and G included), or None past the cap.
fn subgroups(g: &Group) -> Option<Vec<Bits>> {
    let mut cyc: Vec<Bits> = Vec::new();
    let mut seen: HashSet<Bits> = HashSet::new();
    for x in 0..g.order {
        let c = cyclic(g, x);
        if seen.insert(c.clone()) {
            cyc.push(c);
        }
    }
    let mut all = cyc.clone();
    let mut i = 0;
    while i < all.len() {
        let s = all[i].clone();
        for c in &cyc {
            if subset(c, &s) {
                continue;
            }
            let t = join(g, &s, c);
            if seen.insert(t.clone()) {
                all.push(t);
                if all.len() > MAX_SUBGROUPS {
                    return None;
                }
            }
        }
        i += 1;
    }
    Some(all)
}

/// The quotient J = G/L: labels of G's elements, a representative per coset, J's tables; c = |L|.
struct Quo {
    m: usize,
    c: i64,
    label: Vec<usize>,
    rep: Vec<usize>,
    add: Vec<Vec<usize>>,
    sub: Vec<Vec<usize>>,
    l: Bits,
}

fn quotient(g: &Group, l: &Bits) -> Quo {
    let le = elems(l, g.order);
    let mut label = vec![usize::MAX; g.order];
    let mut rep = Vec::new();
    for x in 0..g.order {
        if label[x] == usize::MAX {
            let id = rep.len();
            rep.push(x);
            for &y in &le {
                label[g.add[x][y]] = id;
            }
        }
    }
    let m = rep.len();
    let add = (0..m).map(|i| (0..m).map(|j| label[g.add[rep[i]][rep[j]]]).collect()).collect();
    let sub = (0..m).map(|i| (0..m).map(|j| label[g.sub[rep[i]][rep[j]]]).collect()).collect();
    Quo { m, c: le.len() as i64, label, rep, add, sub, l: l.clone() }
}

fn order_of(q: &Quo, x: usize) -> usize {
    let (mut y, mut t) = (x, 1);
    while y != 0 {
        y = q.add[y][x];
        t += 1;
    }
    t
}

fn gcd(a: i64, b: i64) -> i64 {
    if b == 0 { a.abs() } else { gcd(b, a % b) }
}

fn vp(mut x: i64, p: i64) -> u32 {
    let mut c = 0;
    while x != 0 && x % p == 0 {
        x /= p;
        c += 1;
    }
    c
}

fn primes_of(mut n: i64) -> Vec<i64> {
    let (mut out, mut d) = (Vec::new(), 2);
    n = n.abs();
    while d * d <= n {
        if n % d == 0 {
            out.push(d);
            while n % d == 0 {
                n /= d;
            }
        }
        d += 1;
    }
    if n > 1 {
        out.push(n);
    }
    out
}

/// p^i ≡ −1 (mod m) for some i ≥ 1 (m ≤ 2: always).
fn self_conjugate(p: i64, m: i64) -> bool {
    if m <= 2 {
        return true;
    }
    let mut x = p % m;
    for _ in 0..m {
        if (x + 1) % m == 0 {
            return true;
        }
        x = x * p % m;
    }
    false
}

/// A Ma quotient H = G/M ≅ C_{p^j} × K (j ≥ 1, p ∤ |K|, K self-conjugate mod p), p^(2b) ∣ n, b ≥ 1;
/// u generates P ≤ H of order p; M' ⊇ M is the kernel of G → H/P.
struct MaQ {
    p: i64,
    pb: i64,
    h: Quo,
    u: usize,
    w: Quo,
}

fn ma_quotients(g: &Group, subs: &[Bits], n: i64) -> Vec<MaQ> {
    let mut out = Vec::new();
    for p in primes_of(n) {
        let b = vp(n, p) / 2;
        if b == 0 || g.order as i64 % p != 0 {
            continue;
        }
        for m in subs {
            if size(m) == g.order {
                continue;
            }
            let h = quotient(g, m);
            if h.m as i64 % p != 0 {
                continue;
            }
            let ords: Vec<usize> = (0..h.m).map(|x| order_of(&h, x)).collect();
            if ords.iter().filter(|&&o| o as i64 == p).count() as i64 != p - 1 {
                continue;
            }
            let e = ords.iter().filter(|&&o| o as i64 % p != 0).fold(1i64, |a, &o| a / gcd(a, o as i64) * o as i64);
            if !self_conjugate(p, e) {
                continue;
            }
            let u = (0..h.m).find(|&x| ords[x] as i64 == p).unwrap();
            let mut mp = bits_new(g.order);
            let mut y = 0;
            loop {
                for x in 0..g.order {
                    if h.label[x] == y {
                        put(&mut mp, x);
                    }
                }
                y = h.add[y][u];
                if y == 0 {
                    break;
                }
            }
            let w = quotient(g, &mp);
            out.push(MaQ { p, pb: p.pow(b), h, u, w });
        }
    }
    out
}

/// Σ_{plus} Y − Σ_{minus} Y ≡ 0 (mod modulus), indices in the searched quotient.
#[derive(Clone, PartialEq, Eq, Hash)]
struct Con {
    plus: Vec<usize>,
    minus: Vec<usize>,
    modulus: i64,
}

fn fibres(j: &Quo, h: &Quo) -> Vec<Vec<usize>> {
    let mut f = vec![Vec::new(); h.m];
    for x in 0..j.m {
        f[h.label[j.rep[x]]].push(x);
    }
    f
}

fn constraints(j: &Quo, mas: &[MaQ], mode: Mode) -> Vec<Con> {
    let mut out: Vec<Con> = Vec::new();
    let mut seen = HashSet::new();
    let mut push = |c: Con, out: &mut Vec<Con>| {
        if seen.insert(c.clone()) {
            out.push(c);
        }
    };
    for ma in mas {
        if mode == Mode::Ma && subset(&j.l, &ma.h.l) {
            let f = fibres(j, &ma.h);
            for x in 0..ma.h.m {
                let y = ma.h.add[x][ma.u];
                push(Con { plus: f[x].clone(), minus: f[y].clone(), modulus: ma.pb }, &mut out);
            }
        }
        if mode != Mode::Plain && subset(&j.l, &ma.w.l) {
            let f = fibres(j, &ma.w);
            for x in 0..ma.w.m {
                push(Con { plus: f[x].clone(), minus: vec![], modulus: ma.p }, &mut out);
            }
        }
    }
    out
}

/// Vectors on H12 as a trie (one level per H12 element); `alive` counts unfound leaves below a node.
struct Trie {
    child: Vec<HashMap<i64, usize>>,
    alive: Vec<u32>,
}

impl Trie {
    fn build(vs: &[Vec<i64>]) -> Trie {
        let mut t = Trie { child: vec![HashMap::new()], alive: vec![0] };
        let mut seen = HashSet::new();
        for v in vs {
            if !seen.insert(v.clone()) {
                continue;
            }
            let mut node = 0;
            t.alive[0] += 1;
            for &x in v {
                let next = match t.child[node].get(&x) {
                    Some(&c) => c,
                    None => {
                        t.child.push(HashMap::new());
                        t.alive.push(0);
                        let c = t.child.len() - 1;
                        t.child[node].insert(x, c);
                        c
                    }
                };
                t.alive[next] += 1;
                node = next;
            }
        }
        t
    }
}

#[derive(Clone, Copy, PartialEq)]
enum Want {
    First,
    All,
}

struct Spec<'a> {
    j: &'a Quo,
    k: i64,
    square: i64,
    target: i64,
    sum: i64,
    cons: &'a [Con],
    /// J → H12 labels and |H12|: search fibre by fibre against the trie.
    fib: Option<(&'a [usize], usize)>,
}

struct Out {
    vecs: Vec<Vec<i64>>,
    cut: bool,
    nodes: u64,
}

struct St<'a, 'b> {
    sp: &'a Spec<'a>,
    c: i64,
    order: Vec<usize>,
    pos: Vec<usize>,
    cons_at: Vec<Vec<usize>>,
    fibre_of: Vec<usize>,
    fibre_last: Vec<usize>,
    trie: Option<&'b mut Trie>,
    tpath: Vec<usize>,
    y: Vec<i64>,
    partial: Vec<i64>,
    a1: Vec<i64>,
    n2: Vec<i64>,
    nodes: u64,
    max_nodes: u64,
    max_vecs: usize,
    want: Want,
    vecs: Vec<Vec<i64>>,
    cut: bool,
}

fn isqrt(x: i64) -> i64 {
    if x <= 0 {
        return 0;
    }
    let mut r = (x as f64).sqrt() as i64;
    while r * r > x {
        r -= 1;
    }
    while (r + 1) * (r + 1) <= x {
        r += 1;
    }
    r
}

fn search(sp: &Spec, trie: Option<&mut Trie>, want: Want, max_nodes: u64, max_vecs: usize) -> Out {
    let m = sp.j.m;
    let mut order: Vec<usize> = (0..m).collect();
    let mut fibre_of = vec![0; m];
    let mut fibre_last = Vec::new();
    if let Some((lab, m12)) = sp.fib {
        order.sort_by_key(|&x| (lab[x], x));
        fibre_last = vec![0; m12];
        for (d, &x) in order.iter().enumerate() {
            fibre_of[d] = lab[x];
            fibre_last[lab[x]] = d;
        }
    }
    let mut pos = vec![0; m];
    for (d, &x) in order.iter().enumerate() {
        pos[x] = d;
    }
    let mut cons_at = vec![Vec::new(); m];
    for (i, c) in sp.cons.iter().enumerate() {
        let last = c.plus.iter().chain(&c.minus).map(|&x| pos[x]).max().unwrap_or(0);
        cons_at[last].push(i);
    }
    let mut st = St {
        sp,
        c: sp.j.c,
        order,
        pos,
        cons_at,
        fibre_of,
        fibre_last,
        trie,
        tpath: vec![0],
        y: vec![0; m],
        partial: vec![0; m],
        a1: vec![0; m],
        n2: vec![m as i64; m],
        nodes: 0,
        max_nodes,
        max_vecs,
        want,
        vecs: Vec::new(),
        cut: false,
    };
    st.go(0, 0, 0, 0, 0);
    Out { vecs: st.vecs, cut: st.cut, nodes: st.nodes }
}

impl St<'_, '_> {
    /// Assign (dir 1) or unassign (−1) element e at depth d with value x.
    fn touch(&mut self, e: usize, d: usize, x: i64, dir: i64) {
        let j = self.sp.j;
        for g in 1..j.m {
            let f = j.add[e][g];
            if self.pos[f] < d {
                self.partial[g] += dir * x * self.y[f];
                self.a1[g] -= dir * self.y[f].abs();
            } else {
                self.n2[g] -= dir;
                self.a1[g] += dir * x.abs();
            }
            let b = j.sub[e][g];
            if self.pos[b] < d {
                self.partial[g] += dir * self.y[b] * x;
                self.a1[g] -= dir * self.y[b].abs();
            } else {
                self.n2[g] -= dir;
                self.a1[g] += dir * x.abs();
            }
        }
    }

    fn cons_ok(&self, d: usize) -> bool {
        self.cons_at[d].iter().all(|&i| {
            let c = &self.sp.cons[i];
            let s: i64 = c.plus.iter().map(|&x| self.y[x]).sum::<i64>() - c.minus.iter().map(|&x| self.y[x]).sum::<i64>();
            s % c.modulus == 0
        })
    }

    /// Returns true to stop the whole search.
    fn go(&mut self, d: usize, sum: i64, sq: i64, abs: i64, fsum: i64) -> bool {
        self.nodes += 1;
        if self.nodes > self.max_nodes {
            self.cut = true;
            return true;
        }
        let sp = self.sp;
        let m = sp.j.m;
        if d == m {
            if sum != sp.sum || sq != sp.square || abs > sp.k || (sp.k - abs) % 2 != 0 {
                return false;
            }
            if (1..m).any(|g| self.partial[g] != sp.target) {
                return false;
            }
            if let Some(t) = self.trie.as_deref_mut() {
                // Record z (the trie path) and retire it.
                let mut z = Vec::new();
                let mut node = 0;
                for &nd in &self.tpath[1..] {
                    let key = *t.child[node].iter().find(|&(_, &c)| c == nd).unwrap().0;
                    z.push(key);
                    node = nd;
                }
                for &nd in &self.tpath {
                    t.alive[nd] -= 1;
                }
                self.vecs.push(z);
            } else {
                self.vecs.push(self.y.clone());
            }
            if self.want == Want::First {
                return true;
            }
            if self.vecs.len() >= self.max_vecs {
                self.cut = true;
                return true;
            }
            return false;
        }
        let rem = (m - d) as i64;
        let left_sq = sp.square - sq;
        let left_sum = sp.sum - sum;
        if left_sq < 0 || left_sum * left_sum > rem * left_sq || left_sum.abs() > rem * self.c {
            return false;
        }
        let lim = self.c.min(isqrt(left_sq));
        let e = self.order[d];
        let fib = sp.fib.is_some();
        for x in -lim..=lim {
            let after_sq = left_sq - x * x;
            if after_sq < 0 {
                continue;
            }
            let mut pushed = false;
            if fib {
                let f = self.fibre_of[d];
                let fs = fsum + x;
                let rf = (self.fibre_last[f] - d) as i64;
                let t = self.trie.as_deref().unwrap();
                let cur = *self.tpath.last().unwrap();
                if rf == 0 {
                    match t.child[cur].get(&fs) {
                        Some(&nd) if t.alive[nd] > 0 => {
                            self.tpath.push(nd);
                            pushed = true;
                        }
                        _ => continue,
                    }
                } else {
                    let ok = t.child[cur].iter().any(|(&tv, &nd)| {
                        t.alive[nd] > 0 && (tv - fs).abs() <= self.c * rf && (tv - fs) * (tv - fs) <= rf * after_sq
                    });
                    if !ok {
                        continue;
                    }
                }
            }
            self.y[e] = x;
            self.touch(e, d, x, 1);
            let mr = self.c.min(isqrt(after_sq));
            let mut ok = self.cons_ok(d);
            if ok {
                ok = (1..m).all(|g| (sp.target - self.partial[g]).abs() <= mr * self.a1[g] + mr * mr * self.n2[g]);
            }
            let mut stop = false;
            if ok {
                let nfs = if fib && self.fibre_last[self.fibre_of[d]] == d { 0 } else { fsum + x };
                stop = self.go(d + 1, sum + x, sq + x * x, abs + x.abs(), nfs);
            }
            self.touch(e, d, x, -1);
            self.y[e] = 0;
            if pushed {
                self.tpath.pop();
            }
            if stop {
                return true;
            }
        }
        false
    }
}

/// G = Z_p × Z_p, lines K_i (i = 0..=p), π_i : G → Z_p with kernel K_i. Every x ≠ 0 lies on one line, so
/// Σ_i Y_i(π_i x) = p D(x) + s for the coset sums Y_i; conversely, vectors Y_i meeting the contraction demands with
/// Σ_i Y_i(π_i x) − s ∈ {−p, 0, p} everywhere give an SDS (every nontrivial character factors through one π_i).
/// Meet in the middle over the lines; Y_0, Y_1 up to translation ((π_0, π_1) is onto Z_p²); key: the sum mod p.
fn tomography(inst: &Instance, max_combos: u64) -> (bool, String) {
    let sh = &inst.shape;
    if sh.len() != 2 || sh[0] != sh[1] || primes_of(sh[0] as i64) != vec![sh[0] as i64] {
        return (false, "skip shape".into());
    }
    let p = sh[0];
    let (v, k, lam) = (inst.v as i64, inst.k as i64, inst.lam);
    let total = k + lam * (v - 1);
    let s = isqrt(total);
    if s * s != total {
        return (false, "skip square".into());
    }
    let gp = Group::new(&[p]);
    let mut zero = bits_new(p);
    put(&mut zero, 0);
    let mut q = quotient(&gp, &zero);
    q.c = p as i64;
    let spec = Spec { j: &q, k, square: k + lam * (p as i64 - 1), target: lam * p as i64, sum: s, cons: &[], fib: None };
    let vs = search(&spec, None, Want::All, max_combos, MAX_V12);
    if vs.cut {
        return (false, "open tomo Vcut".into());
    }
    let vecs = vs.vecs;
    if vecs.is_empty() {
        return (true, "KILL tomo V=0".into());
    }
    let reps: Vec<Vec<i64>> = vecs
        .iter()
        .filter(|y| (1..p).all(|t| { let r: Vec<i64> = (0..p).map(|x| y[(x + t) % p]).collect(); **y <= r }))
        .cloned()
        .collect();
    // π for direction (a, b): (x, y) ↦ b x − a y.
    let dirs: Vec<(usize, usize)> = (0..p).map(|i| (1, i)).chain(std::iter::once((0, 1))).collect();
    let proj: Vec<Vec<usize>> = dirs
        .iter()
        .map(|&(a, b)| (0..p * p).map(|e| (b * (e / p) + (p - a) * (e % p)) % p).collect())
        .collect();
    let h = (p + 1) / 2;
    let choices = |i: usize| if i < 2 { &reps } else { &vecs };
    let na: u64 = (0..h).map(|i| choices(i).len() as u64).product();
    let nb: u64 = (h..=p).map(|i| choices(i).len() as u64).product();
    if na > max_combos || nb > max_combos {
        return (false, format!("open tomo V={} reps={} A={na} B={nb} over cap", vecs.len(), reps.len()));
    }
    // Side A: every tuple's sum, keyed by the sum mod p.
    let n = p * p;
    let mut store: Vec<i16> = Vec::new();
    let mut table: HashMap<Vec<u8>, Vec<u32>> = HashMap::new();
    let mut idx = vec![0usize; p + 1];
    let mut acc = vec![0i16; n];
    fn tuples(lines: &[usize], choices: &dyn Fn(usize) -> usize, idx: &mut Vec<usize>, f: &mut dyn FnMut(&[usize])) {
        fn rec(d: usize, lines: &[usize], choices: &dyn Fn(usize) -> usize, idx: &mut Vec<usize>, f: &mut dyn FnMut(&[usize])) {
            if d == lines.len() {
                f(idx);
                return;
            }
            for c in 0..choices(lines[d]) {
                idx[lines[d]] = c;
                rec(d + 1, lines, choices, idx, f);
            }
        }
        rec(0, lines, choices, idx, f);
    }
    let count = |i: usize| choices(i).len();
    let la: Vec<usize> = (0..h).collect();
    let lb: Vec<usize> = (h..=p).collect();
    tuples(&la, &count, &mut idx, &mut |ix: &[usize]| {
        acc.iter_mut().for_each(|a| *a = 0);
        for &i in &la {
            let y = &choices(i)[ix[i]];
            for e in 0..n {
                acc[e] += y[proj[i][e]] as i16;
            }
        }
        let key: Vec<u8> = acc.iter().map(|&a| a.rem_euclid(p as i16) as u8).collect();
        table.entry(key).or_default().push((store.len() / n) as u32);
        store.extend_from_slice(&acc);
    });
    let (pi, si) = (p as i16, s as i16);
    let mut matches = 0u64;
    let mut found: Option<Vec<i8>> = None;
    tuples(&lb, &count, &mut idx, &mut |ix: &[usize]| {
        if found.is_some() {
            return;
        }
        acc.iter_mut().for_each(|a| *a = 0);
        for &i in &lb {
            let y = &choices(i)[ix[i]];
            for e in 0..n {
                acc[e] += y[proj[i][e]] as i16;
            }
        }
        let key: Vec<u8> = acc.iter().map(|&b| (si - b).rem_euclid(pi) as u8).collect();
        if let Some(list) = table.get(&key) {
            for &a in list {
                matches += 1;
                let sa = &store[a as usize * n..(a as usize + 1) * n];
                if (0..n).all(|e| { let d = sa[e] + acc[e] - si; d == 0 || d == pi || d == -pi }) {
                    found = Some((0..n).map(|e| ((sa[e] + acc[e] - si) / pi) as i8).collect());
                    return;
                }
            }
        }
    });
    let info = format!("V={} reps={} A={na} B={nb} keymatches={matches}", vecs.len(), reps.len());
    match found {
        Some(d) => {
            let g = Group::new(&[p, p]);
            assert!(is_sds(&g, inst.k, lam, &d), "tomography built a non-SDS");
            (false, format!("open tomo FOUND (checked SDS) {info} D={:?}", d))
        }
        None => (true, format!("KILL tomo {info}")),
    }
}

struct Row<'a> {
    id: &'a str,
    g: &'a Group,
    k: i64,
    lam: i64,
    s: i64,
    mas: Vec<MaQ>,
    mode: Mode,
    max_nodes: u64,
}

impl Row<'_> {
    fn spec<'a>(&self, j: &'a Quo, cons: &'a [Con], fib: Option<(&'a [usize], usize)>) -> Spec<'a> {
        Spec { j, k: self.k, square: self.k + self.lam * (j.c - 1), target: self.lam * j.c, sum: self.s, cons, fib }
    }
}

enum Verdict {
    Kill(String),
    Pass,
    Cut(String),
}

/// Pair test on (K1, K2), K1 ∩ K2 = 0, K1 + K2 ≠ G.
fn pair(row: &Row, k1: &Bits, k2: &Bits) -> (Verdict, String) {
    let g = row.g;
    let k12 = join(g, k1, k2);
    let (h12, mut ha, mut hb) = (quotient(g, &k12), quotient(g, k1), quotient(g, k2));
    if ha.m > hb.m {
        std::mem::swap(&mut ha, &mut hb);
    }
    let desc = format!("{}|{}>{}", ha.m, hb.m, h12.m);
    let c12 = constraints(&h12, &row.mas, row.mode);
    let v12 = search(&row.spec(&h12, &c12, None), None, Want::All, row.max_nodes, MAX_V12);
    if v12.cut {
        return (Verdict::Cut(format!("{desc}:V12cut")), desc);
    }
    if v12.vecs.is_empty() {
        return (Verdict::Kill(format!("{desc} V12=0 nodes={}", v12.nodes)), desc);
    }
    let lab_a: Vec<usize> = (0..ha.m).map(|x| h12.label[ha.rep[x]]).collect();
    let ca = constraints(&ha, &row.mas, row.mode);
    let mut trie = Trie::build(&v12.vecs);
    let ta = search(&row.spec(&ha, &ca, Some((&lab_a, h12.m))), Some(&mut trie), Want::All, row.max_nodes, usize::MAX);
    if ta.vecs.is_empty() && !ta.cut {
        return (Verdict::Kill(format!("{desc} V12={} T1=0 nodes={}", v12.vecs.len(), v12.nodes + ta.nodes)), desc);
    }
    let lab_b: Vec<usize> = (0..hb.m).map(|x| h12.label[hb.rep[x]]).collect();
    let cb = constraints(&hb, &row.mas, row.mode);
    if std::env::var("D15X_DEBUG").is_ok() {
        // Full T2 too, for the independent check (`check.py`): kernels as G indices, set sizes.
        let mut t12 = Trie::build(&v12.vecs);
        let tb_all = search(&row.spec(&hb, &cb, Some((&lab_b, h12.m))), Some(&mut t12), Want::All, row.max_nodes, usize::MAX);
        let s1: HashSet<Vec<i64>> = ta.vecs.iter().cloned().collect();
        let both = tb_all.vecs.iter().filter(|z| s1.contains(*z)).count();
        let (ka, kb) = if quotient(g, k1).m == ha.m { (k1, k2) } else { (k2, k1) };
        eprintln!("PAIR {} {:?} Ka={:?} Kb={:?} V12={} T1={} T2={} meet={} cut={}", row.id, row.mode,
            elems(ka, g.order), elems(kb, g.order), v12.vecs.len(), ta.vecs.len(), tb_all.vecs.len(), both,
            ta.cut || tb_all.cut);
    }
    let mut trie2 = Trie::build(&ta.vecs);
    let tb = search(&row.spec(&hb, &cb, Some((&lab_b, h12.m))), Some(&mut trie2), Want::First, row.max_nodes, 1);
    let info = format!("{desc} V12={} T1={}{} nodes={}", v12.vecs.len(), ta.vecs.len(), if ta.cut { "+" } else { "" },
        v12.nodes + ta.nodes + tb.nodes);
    if !tb.vecs.is_empty() {
        (Verdict::Pass, info)
    } else if ta.cut || tb.cut {
        (Verdict::Cut(info), desc)
    } else {
        (Verdict::Kill(info), desc)
    }
}

fn run(inst: &Instance, mode: Mode, max_nodes: u64, singles: bool) -> (bool, String) {
    if mode == Mode::Tomo {
        return tomography(inst, max_nodes);
    }
    let (v, k, lam) = (inst.v as i64, inst.k as i64, inst.lam);
    let total = k + lam * (v - 1);
    let s = isqrt(total);
    if s * s != total {
        return (false, "skip square".into());
    }
    let g = Group::new(&inst.shape);
    let Some(subs) = subgroups(&g) else { return (false, "skip lattice".into()) };
    let zero = { let mut b = bits_new(g.order); put(&mut b, 0); b };
    let mas = ma_quotients(&g, &subs, k - lam);
    let row = Row { id: &inst.id, g: &g, k, lam, s, mas, mode, max_nodes };
    let mut notes = Vec::new();
    let (mut pass, mut cut, mut nsingle) = (0, 0, 0);
    // Singles: every proper quotient J with constraints (all J in plain mode with `singles`).
    if mode != Mode::Plain || singles {
        let mut js: Vec<&Bits> =
            subs.iter().filter(|l| *l != &zero && size(l) < g.order && g.order / size(l) <= MAX_SIDE).collect();
        js.sort_by_key(|l| g.order / size(l));
        for l in js {
            let j = quotient(&g, l);
            let cons = constraints(&j, &row.mas, mode);
            if cons.is_empty() && mode != Mode::Plain {
                continue;
            }
            nsingle += 1;
            let out = search(&row.spec(&j, &cons, None), None, Want::First, max_nodes, 1);
            if out.vecs.is_empty() && !out.cut {
                return (true, format!("KILL single J={} c={} cons={} nodes={}", j.m, j.c, cons.len(), out.nodes));
            }
            if out.cut {
                cut += 1;
                notes.push(format!("s{}:cut", j.m));
            } else {
                pass += 1;
            }
        }
    }
    // Pairs with K1 ∩ K2 = 0, K1 + K2 ≠ G, both sides ≤ MAX_SIDE, cheapest first.
    let nontriv: Vec<&Bits> = subs.iter().filter(|l| *l != &zero && size(l) < g.order).collect();
    let mut pairs = Vec::new();
    for (a, ka) in nontriv.iter().enumerate() {
        for kb in &nontriv[a + 1..] {
            if meet(ka, kb) != zero {
                continue;
            }
            let (sa, sb) = (size(ka), size(kb));
            if sa * sb >= g.order || g.order / sa > MAX_SIDE || g.order / sb > MAX_SIDE {
                continue;
            }
            pairs.push((g.order / sa + g.order / sb, *ka, *kb));
        }
    }
    pairs.sort_by_key(|p| p.0);
    let npairs = pairs.len();
    pairs.truncate(MAX_PAIRS);
    for (_, ka, kb) in pairs {
        match pair(&row, ka, kb) {
            (Verdict::Kill(info), _) => return (true, format!("KILL pair {info}")),
            (Verdict::Pass, _) => pass += 1,
            (Verdict::Cut(info), _) => {
                cut += 1;
                if notes.len() < 12 {
                    notes.push(info);
                }
            }
        }
    }
    (false, format!("open singles={nsingle} pairs={npairs} pass={pass} cut={cut} {}", notes.join(" ")))
}

fn parallel(todo: Vec<Instance>, mode: Mode, threads: usize, max_nodes: u64, singles: bool, out: Option<&str>) -> Vec<String> {
    let queue = Arc::new(Mutex::new(todo.into_iter().rev().collect::<Vec<_>>()));
    let kills = Arc::new(Mutex::new(Vec::new()));
    let file = out.map(|p| Arc::new(Mutex::new(std::fs::OpenOptions::new().create(true).append(true).open(p).unwrap())));
    let workers: Vec<_> = (0..threads)
        .map(|_| {
            let (queue, kills, file) = (Arc::clone(&queue), Arc::clone(&kills), file.clone());
            std::thread::spawn(move || loop {
                let next = queue.lock().unwrap().pop();
                let Some(inst) = next else { break };
                let t = std::time::Instant::now();
                let (killed, text) = run(&inst, mode, max_nodes, singles);
                let line = format!("{} {} {} {:?} {text} t={:.1?}", inst.id, inst.key, inst.v, mode, t.elapsed());
                if let Some(f) = &file {
                    let mut f = f.lock().unwrap();
                    writeln!(f, "{line}").unwrap();
                    f.flush().unwrap();
                }
                if killed {
                    kills.lock().unwrap().push(line);
                }
            })
        })
        .collect();
    for w in workers {
        w.join().unwrap();
    }
    Arc::try_unwrap(kills).unwrap().into_inner().unwrap()
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mode = match args[1].as_str() {
        "plain" => Mode::Plain,
        "div" => Mode::Div,
        "ma" => Mode::Ma,
        "tomo" => Mode::Tomo,
        m => panic!("unknown mode {m}"),
    };
    let max_nodes: u64 = args[2].parse().unwrap();
    let threads: usize = args[3].parse().unwrap();
    let out = &args[4];
    let rest: Vec<&String> = args[5..].iter().collect();
    let singles = rest.iter().any(|a| *a == "singles");
    let noval = rest.iter().any(|a| *a == "noval");
    let idfile = rest.iter().find(|a| **a != "singles" && **a != "noval");
    let all = read(&args[0]);
    if !noval {
        let t = std::time::Instant::now();
        let exists: Vec<Instance> = read(&args[0]).into_iter().filter(|i| i.status == "exists").collect();
        let n = exists.len();
        let vout = format!("{out}.validation");
        let wrong = parallel(exists, mode, threads, max_nodes, singles, Some(&vout));
        assert!(wrong.is_empty(), "kills an Instance that exists: {wrong:?}");
        eprintln!("validation passed: {n} existing Instances survive ({:.1?}), log {vout}", t.elapsed());
    }
    let wanted: Option<HashSet<String>> =
        idfile.map(|p| std::fs::read_to_string(p).unwrap().lines().map(|l| l.trim().to_string()).collect());
    let done: HashSet<String> = std::fs::read_to_string(out)
        .unwrap_or_default()
        .lines()
        .filter_map(|l| l.split(' ').next().map(str::to_string))
        .collect();
    let todo: Vec<Instance> = all
        .into_iter()
        .filter(|i| match &wanted {
            Some(w) => w.contains(&i.id),
            None => i.status == "open",
        })
        .filter(|i| !done.contains(&i.id))
        .collect();
    eprintln!("{} to do, {} already done", todo.len(), done.len());
    let t = std::time::Instant::now();
    parallel(todo, mode, threads, max_nodes, singles, Some(out));
    eprintln!("pass done in {:.1?}", t.elapsed());
}
