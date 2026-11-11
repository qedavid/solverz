//! Exploration (tomo3): hyperplane tomography on a quotient Q = Z_p^r of G (r ≤ the p-rank), box c = v/p^r.
//! Blocks: the (p^r − 1)/(p − 1) hyperplanes f (quotients Z_p, fibres v/p), each a vector y_f in V (C3/C4 demands).
//! p^{r−1} Y(x) = Σ_f y_f(f·x) − ((p^{r−1} − 1)/(p − 1)) s. DFS over the blocks in a static order; on every pencil
//! (2-dim flat, a Z_p² quotient) the moments M_n (n = 1..p − 2) must lie on one binary form of degree n and Σ y(0) ≡ s
//! (as in `x_tomography`), which forces the moments of later members; every completed flat of dimension d (a Z_p^d
//! quotient) must be integral with |Y_S| ≤ v/p^d, Σ|Y_S| ≤ k, parity. Translation: the r unit hyperplanes take
//! translate representatives. Leaves: Y on Q integral, in the box, Σ|Y| ≤ k with parity (sum, autocorrelation asserted).
//! Usage: x_tomo_flat <instances.csv> <ids file: id p [r]> <threads> <max_vec_nodes> <max_nodes> <out> [all] [orbit] [r=]
//! Line: id key p r c s U0 V reps vnodes blocks flats nodes rejects(d = 2..r) leaves integral valid miss verdict secs.

use signed_difference_sets::contraction::Demand;
use signed_difference_sets::instances::{read, Instance};
use std::collections::HashSet;
use std::io::Write;
use std::sync::{Arc, Mutex};
use std::time::Instant;

type Range = (u32, u32);

/// Prune V's search by the Fourier bound too.
const FOURIER: bool = true;

/// Node cap of the engine cross-check (first vector only).
const ENGINE_CAP: u64 = 20_000_000;

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

fn is_prime(n: usize) -> bool {
    n > 1 && (2..n).take_while(|d| d * d <= n).all(|d| n % d != 0)
}

fn md(x: i64, p: u64) -> u64 {
    x.rem_euclid(p as i64) as u64
}

fn inv_mod(a: u64, p: u64) -> u64 {
    let (mut r, mut b, mut e) = (1u64, a % p, p - 2);
    while e > 0 {
        if e & 1 == 1 {
            r = r * b % p;
        }
        b = b * b % p;
        e >>= 1;
    }
    r
}

/// Inverse of a square matrix mod p (None if singular).
fn mat_inv(m: &[Vec<u64>], p: u64) -> Option<Vec<Vec<u64>>> {
    let n = m.len();
    let mut a: Vec<Vec<u64>> = m.iter().map(|r| r.clone()).collect();
    let mut b: Vec<Vec<u64>> = (0..n).map(|i| (0..n).map(|j| (i == j) as u64).collect()).collect();
    for c in 0..n {
        let piv = (c..n).find(|&r| a[r][c] % p != 0)?;
        a.swap(c, piv);
        b.swap(c, piv);
        let iv = inv_mod(a[c][c], p);
        for j in 0..n {
            a[c][j] = a[c][j] * iv % p;
            b[c][j] = b[c][j] * iv % p;
        }
        for r in 0..n {
            if r != c && a[r][c] != 0 {
                let f = a[r][c];
                for j in 0..n {
                    a[r][j] = (a[r][j] + p * p - f * a[c][j] % p) % p;
                    b[r][j] = (b[r][j] + p * p - f * b[c][j] % p) % p;
                }
            }
        }
    }
    Some(b)
}

// ---------------------------------------------------------------------------------------------------------------
// V: all vectors on Z_p meeting the demands.

struct VecEnum<'a> {
    p: usize,
    k: i64,
    dem: &'a Demand,
    a: Vec<i64>,
    partial: Vec<i64>,
    a1: Vec<i64>,
    n2: Vec<i64>,
    nodes: u64,
    max_nodes: u64,
    cut: bool,
    out: Vec<Vec<i16>>,
    /// Fourier bound: fre/fim[d][j] = Σ_{t<d} a_t ζ^{jt} (j = 1..=(p−1)/2), cos/sin tables, √(k − λ).
    fre: Vec<Vec<f64>>,
    fim: Vec<Vec<f64>>,
    cs: Vec<Vec<f64>>,
    sn: Vec<Vec<f64>>,
    root_n: f64,
}

impl VecEnum<'_> {
    /// After setting a_d = x: every |Y(ζ^j)|² = n, so the rest R (positions > d) needs |R_j| ≥ ||P_j| − √n|, and
    /// Σ_{j≠0} |R_j|² = p Σ R² − (Σ R)² (Parseval).
    fn fourier_ok(&mut self, d: usize, x: i64, after: i64, left_sum: i64) -> bool {
        let p = self.p;
        let mut lhs = 0.0;
        for j in 1..=(p - 1) / 2 {
            let re = self.fre[d][j] + x as f64 * self.cs[j][d];
            let im = self.fim[d][j] + x as f64 * self.sn[j][d];
            self.fre[d + 1][j] = re;
            self.fim[d + 1][j] = im;
            let gap = (re * re + im * im).sqrt() - self.root_n;
            lhs += 2.0 * gap * gap;
        }
        let rhs = (p as i64 * after - left_sum * left_sum) as f64;
        lhs <= rhs + 1e-6 * (1.0 + rhs.abs())
    }

    fn touch(&mut self, d: usize, x: i64, dir: i64) {
        let p = self.p;
        for g in 1..=(p - 1) / 2 {
            for f in [(d + g) % p, (d + p - g) % p] {
                if f < d {
                    self.partial[g] += dir * x * self.a[f];
                    self.a1[g] -= dir * self.a[f].abs();
                } else {
                    self.n2[g] -= dir;
                    self.a1[g] += dir * x.abs();
                }
            }
        }
    }

    /// Positions 0..d assigned; a₀ of the largest absolute value (translation).
    fn go(&mut self, d: usize, sum: i64, sq: i64, abs: i64) {
        self.nodes += 1;
        if self.nodes > self.max_nodes {
            self.cut = true;
            return;
        }
        let p = self.p;
        let (c, square, s, target) = (self.dem.c, self.dem.square, self.dem.sum, self.dem.target);
        if d == p {
            if sum == s
                && sq == square
                && abs <= self.k
                && (self.k - abs) % 2 == 0
                && (1..=(p - 1) / 2).all(|g| self.partial[g] == target)
            {
                self.out.push(self.a.iter().map(|&x| x as i16).collect());
            }
            return;
        }
        let rem = (p - d) as i64;
        let left_sq = square - sq;
        let left_sum = s - sum;
        if left_sq < 0 || left_sum * left_sum > rem * left_sq || left_sum.abs() > rem * c {
            return;
        }
        if d == p - 2 && d > 0 {
            // The last two are fixed by the sum and the square sum: x + y = L, x² + y² = R.
            let disc = 2 * left_sq - left_sum * left_sum;
            let r = isqrt(disc);
            if disc < 0 || r * r != disc || (left_sum + r) % 2 != 0 {
                return;
            }
            let (x, y) = ((left_sum + r) / 2, (left_sum - r) / 2);
            let top = self.a[0].abs().min(c);
            let cands: Vec<(i64, i64)> = if r == 0 { vec![(x, y)] } else { vec![(x, y), (y, x)] };
            for (x, y) in cands {
                if x.abs() > top || y.abs() > top {
                    continue;
                }
                self.a[d] = x;
                self.touch(d, x, 1);
                self.a[d + 1] = y;
                self.touch(d + 1, y, 1);
                self.go(p, sum + x + y, sq + x * x + y * y, abs + x.abs() + y.abs());
                self.touch(d + 1, y, -1);
                self.a[d + 1] = 0;
                self.touch(d, x, -1);
                self.a[d] = 0;
            }
            return;
        }
        let lim = if d == 0 { c } else { self.a[0].abs() }.min(isqrt(left_sq));
        for x in -lim..=lim {
            let after = left_sq - x * x;
            self.a[d] = x;
            self.touch(d, x, 1);
            let m = c.min(isqrt(after)).min(self.a[0].abs().max(x.abs()));
            let ok = (1..=(p - 1) / 2).all(|g| {
                (target - self.partial[g]).abs() <= m * self.a1[g] + (m * m * self.n2[g]).min(after)
            }) && (!FOURIER || self.fourier_ok(d, x, after, left_sum - x));
            if ok {
                self.go(d + 1, sum + x, sq + x * x, abs + x.abs());
            }
            self.touch(d, x, -1);
            self.a[d] = 0;
            if self.cut {
                return;
            }
        }
    }
}

/// Every vector (all translates); None when the node cap is hit.
fn vectors(p: usize, k: usize, dem: &Demand, max_nodes: u64) -> (Option<Vec<Vec<i16>>>, u64) {
    let h = (p - 1) / 2 + 1;
    let mut e = VecEnum {
        p,
        k: k as i64,
        dem,
        a: vec![0; p],
        partial: vec![0; h],
        a1: vec![0; h],
        n2: vec![p as i64; h],
        nodes: 0,
        max_nodes,
        cut: false,
        out: Vec::new(),
        fre: vec![vec![0.0; h]; p + 1],
        fim: vec![vec![0.0; h]; p + 1],
        cs: (0..h).map(|j| (0..p).map(|t| (2.0 * std::f64::consts::PI * (j * t % p) as f64 / p as f64).cos()).collect()).collect(),
        sn: (0..h).map(|j| (0..p).map(|t| (2.0 * std::f64::consts::PI * (j * t % p) as f64 / p as f64).sin()).collect()).collect(),
        root_n: ((k as i64 - dem.target / dem.c) as f64).max(0.0).sqrt(),
    };
    // n2[g] counts pairs with no assigned end: p pairs (t, t + g) per shift.
    e.go(0, 0, 0, 0);
    if e.cut {
        return (None, e.nodes);
    }
    let mut set: HashSet<Vec<i16>> = HashSet::new();
    for y in &e.out {
        for t in 0..p {
            set.insert((0..p).map(|x| y[(x + t) % p]).collect());
        }
    }
    let mut all: Vec<Vec<i16>> = set.into_iter().collect();
    all.sort();
    (Some(all), e.nodes)
}

// ---------------------------------------------------------------------------------------------------------------
// V by multipliers: α = Y(ζ) has α ᾱ = n = k − λ. U0 = ∩ ⟨q mod p⟩ over the primes q | n, q ≠ p, with −1 ∉ ⟨q⟩, fixes
// every prime ideal dividing (α) (a self-conjugate q enters (α) as q^{e/2}), so σ_c(α) = ±ζ^j α (Kronecker); when
// p ∤ s the sign is + and Y(c⁻¹t) = Y(t − j). A translate of Y is then constant on {0} and on the U0-cosets.

fn prime_factors(mut n: u64) -> Vec<u64> {
    let mut out = Vec::new();
    let mut d = 2;
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

/// U0 as a membership table on 0..p.
fn multiplier_group(p: u64, n: u64) -> Vec<bool> {
    let mut u: Vec<bool> = (0..p).map(|x| x != 0).collect();
    for q in prime_factors(n) {
        if q % p == 0 {
            continue;
        }
        let mut h = vec![false; p as usize];
        let mut x = 1;
        loop {
            h[x as usize] = true;
            x = x * q % p;
            if x == 1 {
                break;
            }
        }
        if h[(p - 1) as usize] {
            continue;
        }
        for i in 0..p as usize {
            u[i] = u[i] && h[i];
        }
    }
    u
}

struct OrbitEnum<'a> {
    p: usize,
    k: i64,
    dem: &'a Demand,
    orbits: Vec<Vec<usize>>,
    y: Vec<i64>,
    nodes: u64,
    max_nodes: u64,
    cut: bool,
    out: Vec<Vec<i16>>,
}

impl OrbitEnum<'_> {
    fn go(&mut self, i: usize, sum: i64, sq: i64, abs: i64) {
        self.nodes += 1;
        if self.nodes > self.max_nodes {
            self.cut = true;
            return;
        }
        let (c, square, s) = (self.dem.c, self.dem.square, self.dem.sum);
        let left_sq = square - sq;
        let left_sum = s - sum;
        let wrest: i64 = self.orbits[i..].iter().map(|o| o.len() as i64).sum();
        if left_sq < 0 || left_sum * left_sum > wrest * left_sq || left_sum.abs() > wrest * c {
            return;
        }
        if i == self.orbits.len() {
            if left_sq != 0 || left_sum != 0 || abs > self.k || (self.k - abs) % 2 != 0 {
                return;
            }
            let p = self.p;
            let mut a = vec![0i64; p];
            for (o, &v) in self.orbits.iter().zip(&self.y) {
                for &t in o {
                    a[t] = v;
                }
            }
            if (1..=(p - 1) / 2).all(|g| (0..p).map(|t| a[t] * a[(t + g) % p]).sum::<i64>() == self.dem.target) {
                self.out.push(a.iter().map(|&x| x as i16).collect());
            }
            return;
        }
        let w = self.orbits[i].len() as i64;
        let lim = c.min(isqrt(left_sq / w));
        for x in -lim..=lim {
            self.y[i] = x;
            self.go(i + 1, sum + w * x, sq + w * x * x, abs + w * x.abs());
            if self.cut {
                return;
            }
        }
        self.y[i] = 0;
    }
}

/// V from the U0-invariant vectors (all translates); None when U0 = 1, p | s, or the cap is hit. Returns |U0| too.
fn vectors_orbit(p: usize, k: usize, lam: i64, dem: &Demand, max_nodes: u64) -> (Option<Vec<Vec<i16>>>, u64, usize) {
    let pp = p as u64;
    let n = k as i64 - lam;
    if n <= 0 || dem.sum.rem_euclid(p as i64) == 0 {
        return (None, 0, 1);
    }
    let u = multiplier_group(pp, n as u64);
    let e = u.iter().filter(|&&b| b).count();
    if e == 1 {
        return (None, 0, 1);
    }
    let mut seen = vec![false; p];
    let mut orbits = vec![vec![0usize]];
    seen[0] = true;
    for t in 1..p {
        if !seen[t] {
            let o: Vec<usize> = (1..p).filter(|&c| u[c]).map(|c| c * t % p).collect();
            o.iter().for_each(|&x| seen[x] = true);
            orbits.push(o);
        }
    }
    let m = orbits.len();
    let mut st = OrbitEnum { p, k: k as i64, dem, orbits, y: vec![0; m], nodes: 0, max_nodes, cut: false, out: Vec::new() };
    st.go(0, 0, 0, 0);
    if st.cut {
        return (None, st.nodes, e);
    }
    let mut set: HashSet<Vec<i16>> = HashSet::new();
    for y in &st.out {
        for t in 0..p {
            set.insert((0..p).map(|x| y[(x + t) % p]).collect());
        }
    }
    let mut all: Vec<Vec<i16>> = set.into_iter().collect();
    all.sort();
    (Some(all), st.nodes, e)
}

// ---------------------------------------------------------------------------------------------------------------
// Flats: a d-dimensional subspace S of the dual F_p^r (basis b_1..b_d) is the quotient Q/S^⊥ ≅ Z_p^d; its members are
// the hyperplanes f ∈ S (normalized), at coordinates c ∈ P^{d−1} (f·x = λ f'(x), f = Σ c_j b_j, f' normalized).
// p^{d−1} Y_S(ξ) = Σ_{f'} y_{f'}(λ⁻¹ c·ξ) − h'_d s, h'_d = (p^{d−1} − 1)/(p − 1), ξ ∈ F_p^d.

struct Flat {
    d: usize,
    /// (block, c coordinates, λ⁻¹) per member.
    members: Vec<(usize, Vec<u64>, u64)>,
    /// Depth (static order) at which the last member is assigned.
    done_at: usize,
}

fn normalize(v: &[u64], p: u64) -> (Vec<u64>, u64) {
    let i = v.iter().position(|&x| x != 0).unwrap();
    let lam = v[i];
    let il = inv_mod(lam, p);
    (v.iter().map(|&x| x * il % p).collect(), lam)
}

fn idx_of(v: &[u64], p: u64) -> usize {
    v.iter().fold(0usize, |a, &x| a * p as usize + x as usize)
}

/// Every flat of dimension d (2 ≤ d ≤ r), as member lists with coordinates.
fn flats(r: usize, p: u64, hyp_index: &[usize], max_d: usize) -> Vec<Flat> {
    let mut out = Vec::new();
    let mut seen: HashSet<Vec<usize>> = HashSet::new();
    // Bases in reduced echelon form over F_p^r, enumerated by choosing pivot columns and free entries.
    for d in 2..=max_d.min(r) {
        let mut piv = vec![0usize; d];
        fn next_comb(c: &mut [usize], n: usize) -> bool {
            let k = c.len();
            for i in (0..k).rev() {
                if c[i] < n - k + i {
                    c[i] += 1;
                    for j in i + 1..k {
                        c[j] = c[j - 1] + 1;
                    }
                    return true;
                }
            }
            false
        }
        for i in 0..d {
            piv[i] = i;
        }
        loop {
            // free positions: (row i, column j) with j > piv[i] and j not a pivot.
            let free: Vec<(usize, usize)> =
                (0..d).flat_map(|i| (piv[i] + 1..r).filter(|j| !piv.contains(j)).map(move |j| (i, j))).collect();
            let total = (p as usize).pow(free.len() as u32);
            for code in 0..total {
                let mut basis = vec![vec![0u64; r]; d];
                for i in 0..d {
                    basis[i][piv[i]] = 1;
                }
                let mut x = code;
                for &(i, j) in &free {
                    basis[i][j] = (x % p as usize) as u64;
                    x /= p as usize;
                }
                let mut members = Vec::new();
                for ci in 1..(p as usize).pow(d as u32) {
                    let mut c = vec![0u64; d];
                    let mut y = ci;
                    for j in (0..d).rev() {
                        c[j] = (y % p as usize) as u64;
                        y /= p as usize;
                    }
                    if c[c.iter().position(|&t| t != 0).unwrap()] != 1 {
                        continue;
                    }
                    let f: Vec<u64> = (0..r).map(|col| (0..d).map(|j| c[j] * basis[j][col]).sum::<u64>() % p).collect();
                    let (fn_, lam) = normalize(&f, p);
                    members.push((hyp_index[idx_of(&fn_, p)], c, inv_mod(lam, p)));
                }
                let mut key: Vec<usize> = members.iter().map(|m| m.0).collect();
                key.sort();
                if seen.insert(key) {
                    out.push(Flat { d, members, done_at: 0 });
                }
            }
            if !next_comb(&mut piv, r) {
                break;
            }
        }
    }
    out
}

struct Search<'a> {
    p: usize,
    pp: u64,
    r: usize,
    s: i64,
    k: i64,
    lam: i64,
    v: usize,
    vecs: &'a [Vec<i16>],
    keys: &'a [Vec<u8>],
    reps: Vec<bool>,
    order: Vec<usize>,
    pos_of: Vec<usize>,
    flats: &'a [Flat],
    /// Per block: (pencil index, member index) for the pencils containing it.
    pencils_of: Vec<Vec<(usize, usize)>>,
    /// Per pencil and n: info members (indices into members, the first n + 1 in order) and, for each member, the
    /// evaluation coefficients on the info values (None for info members).
    interp: Vec<Vec<(Vec<usize>, Vec<Option<Vec<u64>>>)>>,
    /// Flats completed at each depth.
    complete_at: Vec<Vec<usize>>,
    assign: Vec<usize>,
    hyps: Vec<Vec<u64>>,
    all: bool,
    nodes: u64,
    max_nodes: u64,
    cut: bool,
    leaves: u64,
    integral: u64,
    valid: u64,
    flat_rejects: Vec<u64>,
    theory_miss: u64,
    found: Option<Vec<i64>>,
}

impl Search<'_> {
    fn stop(&self) -> bool {
        self.cut || (!self.all && self.found.is_some())
    }

    /// Value of y on the coordinate of block b at a point with coordinates `coord` in F_p (block's own coordinate).
    fn moment_val(&self, b: usize, n: usize, lam_inv: u64) -> u64 {
        // member at coordinate c: f = λ f', value λ^n M_n(y_{f'}); stored as λ⁻¹, so multiply by (λ⁻¹)^{−n}.
        let m = if n == 0 { 0 } else { self.keys[self.assign[b]][n - 1] as u64 };
        let l = inv_mod(lam_inv, self.pp);
        let mut lp = 1u64;
        for _ in 0..n {
            lp = lp * l % self.pp;
        }
        m * lp % self.pp
    }

    /// Quotient vector of a completed flat, or None (non-integral counts as a theory miss when d = 2).
    fn flat_vector(&self, fi: usize) -> Option<Vec<i64>> {
        let f = &self.flats[fi];
        let (p, pp, d) = (self.p, self.pp, f.d);
        let npts = p.pow(d as u32);
        let hd: i64 = (p.pow(d as u32 - 1) as i64 - 1) / (p as i64 - 1);
        let den = p.pow(d as u32 - 1) as i64;
        let mut out = vec![0i64; npts];
        for xi in 0..npts {
            let mut coord = vec![0u64; d];
            let mut y = xi;
            for j in (0..d).rev() {
                coord[j] = (y % p) as u64;
                y /= p;
            }
            let mut tot = -hd * self.s;
            for (b, c, li) in &f.members {
                let t = (c.iter().zip(&coord).map(|(a, b)| a * b).sum::<u64>() % pp) * li % pp;
                tot += self.vecs[self.assign[*b]][t as usize] as i64;
            }
            if tot % den != 0 {
                return None;
            }
            out[xi] = tot / den;
        }
        Some(out)
    }

    fn check_flat(&mut self, fi: usize) -> bool {
        let d = self.flats[fi].d;
        let Some(y) = self.flat_vector(fi) else {
            if d == 2 {
                self.theory_miss += 1;
            }
            self.flat_rejects[d] += 1;
            return false;
        };
        let box_ = (self.v / self.p.pow(d as u32)) as i64;
        let abs: i64 = y.iter().map(|x| x.abs()).sum();
        if y.iter().any(|x| x.abs() > box_) || abs > self.k || (self.k - abs) % 2 != 0 {
            self.flat_rejects[d] += 1;
            return false;
        }
        true
    }

    fn go(&mut self, depth: usize) {
        if self.stop() {
            return;
        }
        self.nodes += 1;
        if self.nodes > self.max_nodes {
            self.cut = true;
            return;
        }
        if depth == self.order.len() {
            self.leaf();
            return;
        }
        let b = self.order[depth];
        let p = self.p;
        let pp = self.pp;
        // Forced key entries: (column, value).
        let mut forced: Vec<(usize, u8)> = Vec::new();
        for &(pi, mi) in &self.pencils_of[b] {
            let fl = &self.flats[pi];
            let assigned = fl.members.iter().filter(|m| self.pos_of[m.0] < depth).count();
            for n in 1..=p - 2 {
                if assigned < n + 1 {
                    break;
                }
                let (info, coefs) = &self.interp[pi][n];
                let Some(co) = &coefs[mi] else { continue };
                let mut val = 0u64;
                for (s, &ii) in info.iter().enumerate() {
                    let (bb, _, li) = &fl.members[ii];
                    val = (val + co[s] * self.moment_val(*bb, n, *li)) % pp;
                }
                // value at this member = λ^n M_n(y) ⇒ M_n = val · λ^{−n} = val · (λ⁻¹)^n.
                let li = fl.members[mi].2;
                let mut lp = 1u64;
                for _ in 0..n {
                    lp = lp * li % pp;
                }
                forced.push((n - 1, (val * lp % pp) as u8));
            }
            if assigned == p {
                let mut need = md(self.s, pp);
                for m in &fl.members {
                    if m.0 != b {
                        need = (need + pp - md(self.vecs[self.assign[m.0]][0] as i64, pp)) % pp;
                    }
                }
                forced.push((p - 2, need as u8));
            }
        }
        let only_reps = depth < self.r;
        for vi in 0..self.vecs.len() {
            if only_reps && !self.reps[vi] {
                continue;
            }
            let key = &self.keys[vi];
            if forced.iter().any(|&(c, v)| key[c] != v) {
                continue;
            }
            self.assign[b] = vi;
            let mut ok = true;
            for fi in self.complete_at[depth].clone() {
                if self.flats[fi].d < self.r && !self.check_flat(fi) {
                    ok = false;
                    break;
                }
            }
            if ok {
                self.go(depth + 1);
            }
            if self.stop() {
                return;
            }
        }
        self.assign[b] = usize::MAX;
    }

    fn leaf(&mut self) {
        self.leaves += 1;
        let (p, pp, r) = (self.p, self.pp, self.r);
        let n = p.pow(r as u32);
        let den = p.pow(r as u32 - 1) as i64;
        let hr: i64 = (den - 1) / (p as i64 - 1);
        let mut y = vec![0i64; n];
        for xi in 0..n {
            let mut x = vec![0u64; r];
            let mut t = xi;
            for j in (0..r).rev() {
                x[j] = (t % p) as u64;
                t /= p;
            }
            let mut tot = -hr * self.s;
            for (bi, h) in self.hyps.iter().enumerate() {
                let c = h.iter().zip(&x).map(|(a, b)| a * b).sum::<u64>() % pp;
                tot += self.vecs[self.assign[bi]][c as usize] as i64;
            }
            if tot % den != 0 {
                return;
            }
            y[xi] = tot / den;
        }
        self.integral += 1;
        let cq = (self.v / n) as i64;
        let abs: i64 = y.iter().map(|x| x.abs()).sum();
        if y.iter().any(|x| x.abs() > cq) || abs > self.k || (self.k - abs) % 2 != 0 {
            return;
        }
        // Theory: sum and autocorrelation follow; assert.
        assert_eq!(y.iter().sum::<i64>(), self.s, "theory: sum");
        for g in 1..n {
            let mut ac = 0i64;
            for xi in 0..n {
                let (mut a, mut b, mut z, mut place) = (xi, g, 0usize, 1usize);
                for _ in 0..r {
                    z += ((a % p + b % p) % p) * place;
                    place *= p;
                    a /= p;
                    b /= p;
                }
                ac += y[xi] * y[z];
            }
            assert_eq!(ac, self.lam * cq, "theory: autocorrelation");
        }
        self.valid += 1;
        if self.found.is_none() {
            self.found = Some(y);
        }
    }
}

struct Opts {
    max_vec_nodes: u64,
    max_nodes: u64,
    all: bool,
    orbit: bool,
    rank: Option<usize>,
}

fn p_rank(shape: &[usize], p: usize) -> usize {
    shape.iter().filter(|&&m| m % p == 0).count()
}

fn run(inst: &Instance, p: usize, r: usize, o: &Opts) -> String {
    let head = format!("{} {} p={p} r={r}", inst.id, inst.key);
    if !is_prime(p) || p_rank(&inst.shape, p) < r || r < 2 || p.pow(r as u32) > 2000 {
        return format!("{head} skip shape");
    }
    let pp = p as u64;
    let Some(dem) = Demand::new(inst.v, inst.k, inst.lam, p) else {
        return format!("{head} skip square");
    };
    let s = dem.sum;
    let cq = inst.v / p.pow(r as u32);
    let t0 = Instant::now();
    let (vo, onodes, ue) =
        if o.orbit { vectors_orbit(p, inst.k, inst.lam, &dem, o.max_vec_nodes) } else { (None, 0, 1) };
    let (vs, vnodes) = match vo {
        Some(v) => (Some(v), onodes),
        None => vectors(p, inst.k, &dem, o.max_vec_nodes),
    };
    let Some(vecs) = vs else {
        return format!("{head} c={cq} s={s} CUT V vnodes={vnodes} {:.1}s", t0.elapsed().as_secs_f64());
    };
    if vecs.is_empty() {
        return format!("{head} c={cq} s={s} V=0 KILL V=0 {:.2}s", t0.elapsed().as_secs_f64());
    }
    let keys: Vec<Vec<u8>> = vecs
        .iter()
        .map(|y| {
            let mut k: Vec<u8> = (1..=p - 2)
                .map(|n| {
                    (0..p)
                        .map(|t| {
                            let mut tn = 1u64;
                            for _ in 0..n {
                                tn = tn * t as u64 % pp;
                            }
                            md(y[t] as i64, pp) * tn % pp
                        })
                        .sum::<u64>()
                        % pp
                })
                .map(|x| x as u8)
                .collect();
            k.push(md(y[0] as i64, pp) as u8);
            k
        })
        .collect();
    let reps: Vec<bool> = vecs
        .iter()
        .map(|y| (1..p).all(|t| { let z: Vec<i16> = (0..p).map(|x| y[(x + t) % p]).collect(); *y <= z }))
        .collect();
    // Hyperplanes: normalized nonzero vectors of F_p^r.
    let mut hyps: Vec<Vec<u64>> = Vec::new();
    let mut hyp_index = vec![usize::MAX; p.pow(r as u32)];
    for code in 1..p.pow(r as u32) {
        let mut v = vec![0u64; r];
        let mut y = code;
        for j in (0..r).rev() {
            v[j] = (y % p) as u64;
            y /= p;
        }
        if v[v.iter().position(|&t| t != 0).unwrap()] == 1 {
            hyp_index[code] = hyps.len();
            hyps.push(v);
        }
    }
    let nb = hyps.len();
    let mut fl = flats(r, pp, &hyp_index, r);
    // Static order: unit vectors first, then greedily the block completing the most pencil incidences.
    let mut order: Vec<usize> = (0..r).map(|j| hyp_index[p.pow((r - 1 - j) as u32)]).collect();
    let mut in_order = vec![false; nb];
    order.iter().for_each(|&b| in_order[b] = true);
    let pencil_ids: Vec<usize> = (0..fl.len()).filter(|&i| fl[i].d == 2).collect();
    let mut pencils_of_b: Vec<Vec<usize>> = vec![Vec::new(); nb];
    for &pi in &pencil_ids {
        for m in &fl[pi].members {
            pencils_of_b[m.0].push(pi);
        }
    }
    while order.len() < nb {
        let best = (0..nb)
            .filter(|&b| !in_order[b])
            .max_by_key(|&b| {
                let sc: usize = pencils_of_b[b]
                    .iter()
                    .map(|&pi| {
                        let a = fl[pi].members.iter().filter(|m| in_order[m.0]).count();
                        a * a
                    })
                    .sum();
                (sc, usize::MAX - b)
            })
            .unwrap();
        in_order[best] = true;
        order.push(best);
    }
    let mut pos_of = vec![0usize; nb];
    for (i, &b) in order.iter().enumerate() {
        pos_of[b] = i;
    }
    let mut complete_at: Vec<Vec<usize>> = vec![Vec::new(); nb];
    for (i, f) in fl.iter_mut().enumerate() {
        f.done_at = f.members.iter().map(|m| pos_of[m.0]).max().unwrap();
        complete_at[f.done_at].push(i);
    }
    // Pencil interpolation tables.
    let mut pencils_of: Vec<Vec<(usize, usize)>> = vec![Vec::new(); nb];
    let mut interp: Vec<Vec<(Vec<usize>, Vec<Option<Vec<u64>>>)>> = vec![Vec::new(); fl.len()];
    for &pi in &pencil_ids {
        let f = &fl[pi];
        for (mi, m) in f.members.iter().enumerate() {
            pencils_of[m.0].push((pi, mi));
        }
        let mut by_pos: Vec<usize> = (0..f.members.len()).collect();
        by_pos.sort_by_key(|&mi| pos_of[f.members[mi].0]);
        let mono = |n: usize, a: usize, c: &[u64]| -> u64 {
            let mut x = 1u64;
            for _ in 0..n - a {
                x = x * c[0] % pp;
            }
            for _ in 0..a {
                x = x * c[1] % pp;
            }
            x
        };
        let mut tab = vec![(Vec::new(), Vec::new())];
        for n in 1..=p - 2 {
            let info: Vec<usize> = by_pos[..n + 1].to_vec();
            let m: Vec<Vec<u64>> = info.iter().map(|&mi| (0..=n).map(|a| mono(n, a, &f.members[mi].1)).collect()).collect();
            let minv = mat_inv(&m, pp).expect("info set singular");
            let coefs: Vec<Option<Vec<u64>>> = (0..f.members.len())
                .map(|mi| {
                    if info.contains(&mi) {
                        None
                    } else {
                        let row: Vec<u64> = (0..=n).map(|a| mono(n, a, &f.members[mi].1)).collect();
                        Some((0..=n).map(|s| (0..=n).map(|a| row[a] * minv[a][s] % pp).sum::<u64>() % pp).collect())
                    }
                })
                .collect();
            tab.push((info, coefs));
        }
        interp[pi] = tab;
    }
    let nflats: Vec<usize> = (2..=r).map(|d| fl.iter().filter(|f| f.d == d).count()).collect();
    let mut st = Search {
        p,
        pp,
        r,
        s,
        k: inst.k as i64,
        lam: inst.lam,
        v: inst.v,
        vecs: &vecs,
        keys: &keys,
        reps,
        order,
        pos_of,
        flats: &fl,
        pencils_of,
        interp,
        complete_at,
        assign: vec![usize::MAX; nb],
        hyps,
        all: o.all,
        nodes: 0,
        max_nodes: o.max_nodes,
        cut: false,
        leaves: 0,
        integral: 0,
        valid: 0,
        flat_rejects: vec![0; r + 1],
        theory_miss: 0,
        found: None,
    };
    st.go(0);
    let verdict = if st.cut {
        "CUT".to_string()
    } else if let Some(y) = &st.found {
        format!("FOUND Y={}", y.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","))
    } else if st.integral == 0 {
        "KILL int".to_string()
    } else {
        "KILL box".to_string()
    };
    format!(
        "{head} c={cq} s={s} U0={ue} V={} reps={} vnodes={vnodes} blocks={nb} flats={:?} nodes={} rejects={:?} leaves={} integral={} valid={} miss={} {verdict} {:.2}s",
        vecs.len(),
        st.reps.iter().filter(|&&b| b).count(),
        nflats,
        st.nodes,
        &st.flat_rejects[2..],
        st.leaves,
        st.integral,
        st.valid,
        st.theory_miss,
        t0.elapsed().as_secs_f64()
    )
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a.len() < 7 {
        eprintln!("usage: x_tomo_flat <instances.csv> <ids file: id p [r]> <threads> <max_vec_nodes> <max_nodes> <out> [all] [orbit]");
        std::process::exit(2);
    }
    let insts = read(&a[1]);
    let threads: usize = a[3].parse().unwrap();
    let flag = |f: &str| a[7..].iter().any(|x| x == f);
    let o = Arc::new(Opts {
        max_vec_nodes: a[4].parse::<f64>().unwrap() as u64,
        max_nodes: a[5].parse::<f64>().unwrap() as u64,
        all: flag("all"),
        orbit: flag("orbit"),
        rank: a[7..].iter().find_map(|x| x.strip_prefix("r=")).map(|x| x.parse().unwrap()),
    });
    let mut todo: Vec<(usize, usize, usize)> = Vec::new();
    for l in std::fs::read_to_string(&a[2]).unwrap().lines() {
        let f: Vec<&str> = l.split_whitespace().collect();
        if f.len() < 2 {
            continue;
        }
        let Some(ix) = insts.iter().position(|i| i.id == f[0]) else { continue };
        let p: usize = f[1].parse().unwrap();
        let r = f.get(2).and_then(|x| x.parse().ok()).or(o.rank).unwrap_or_else(|| p_rank(&insts[ix].shape, p));
        todo.push((ix, p, r));
    }
    let insts = Arc::new(insts);
    let queue = Arc::new(Mutex::new(todo.into_iter().rev().collect::<Vec<_>>()));
    let out = Arc::new(Mutex::new(std::fs::OpenOptions::new().create(true).append(true).open(&a[6]).unwrap()));
    let hs: Vec<_> = (0..threads)
        .map(|_| {
            let (queue, out, o, insts) = (queue.clone(), out.clone(), o.clone(), insts.clone());
            std::thread::spawn(move || loop {
                let Some((ix, p, r)) = queue.lock().unwrap().pop() else { break };
                let line = run(&insts[ix], p, r, &o);
                println!("{line}");
                let mut f = out.lock().unwrap();
                writeln!(f, "{line}").unwrap();
                f.flush().unwrap();
            })
        })
        .collect();
    for h in hs {
        h.join().unwrap();
    }
}
