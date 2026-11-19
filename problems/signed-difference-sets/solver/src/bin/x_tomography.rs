//! Exploration (I23): line tomography on G = Z_p × Z_p, p prime. Every x ≠ 0 lies on exactly one line K_i (i ∈ P¹),
//! so the coset sums Y_i on G/K_i ≅ Z_p (coordinate ℓ_i(x) = u_i x₁ + w_i x₂) give Σ_i Y_i(ℓ_i x) = p D(x) + s.
//! D is integral iff for every n = 1..p−2 the moments M_n(Y_i) = Σ_t Y_i(t) tⁿ mod p are the values at the points
//! (u_i, w_i) of one binary form h_n of degree n (h_n(u, w) = Σ_x D(x)(u x₁ + w x₂)ⁿ), and Σ_i Y_i(0) ≡ s (mod p).
//! Valid Y_i with integral D whose values are in {0, ±1} give an SDS (each nontrivial character factors through one
//! line), so the search decides the row.
//! Search: when p ∤ s, h_1 = 0 by translation; `gl`: h_3 one per GL(2, p) orbit when h_1 = h_2 = 0. Then each h_n in
//! turn among the codewords whose value at every line is the moment of a vector still allowed there (information set:
//! the n + 1 lines with the fewest values); last Y_i(0), then each leaf rebuilds D (asserted integral) and checks it.
//! V: every vector on Z_p meeting the engine's `Demand` (C3) with Σ a = +s, Σ|a| ≤ k, k − Σ|a| even.
//! Usage: x_tomography <instances.csv> <ids file> <threads> <max_vec_nodes> <max_nodes> <out> [stats] [all] [gl]
//! [witness=<file>] [orbit] [vcheck] [vfile=<file>] [part=i/m]
//! `stats`: V only. `all`: count every leaf instead of stopping at the first SDS. `witness`: V := the contractions
//! of that SDS (`a b ±` lines), closed under translation and scaling; tests the search (must be FOUND). `orbit`: V
//! from the vectors constant on the cosets of the multiplier group U0 (see `vectors_orbit`) when |U0| > 1 and p ∤ s;
//! `vcheck`: V both ways, asserted equal. `vfile`: V read from a file (`scratch/tomo/vlat.py`: lattice enumeration
//! for n prime ≡ 1 mod p), with `vcheck` asserted equal to the DFS V. The ids file then holds one row. `part=i/m`: only every m-th accepted
//! codeword of the second level, from the i-th (split one row over processes; a kill needs all m parts).
//! Line: id key p s V V0 vnodes levels(n:enumerated/accepted) leaves integral sds verdict seconds.

use signed_difference_sets::contraction::{search as engine_search, Demand};
use signed_difference_sets::instances::{read, Instance};
use signed_difference_sets::{is_sds, Group};
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
    out: Vec<Vec<i8>>,
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
                self.out.push(self.a.iter().map(|&x| x as i8).collect());
            }
            return;
        }
        let rem = (p - d) as i64;
        let left_sq = square - sq;
        let left_sum = s - sum;
        if left_sq < 0 || left_sum * left_sum > rem * left_sq || left_sum.abs() > rem * c {
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
fn vectors(p: usize, k: usize, dem: &Demand, max_nodes: u64) -> (Option<Vec<Vec<i8>>>, u64) {
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
    let mut set: HashSet<Vec<i8>> = HashSet::new();
    for y in &e.out {
        for t in 0..p {
            set.insert((0..p).map(|x| y[(x + t) % p]).collect());
        }
    }
    let mut all: Vec<Vec<i8>> = set.into_iter().collect();
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
    out: Vec<Vec<i8>>,
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
                self.out.push(a.iter().map(|&x| x as i8).collect());
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
fn vectors_orbit(p: usize, k: usize, lam: i64, dem: &Demand, max_nodes: u64) -> (Option<Vec<Vec<i8>>>, u64, usize) {
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
    let mut set: HashSet<Vec<i8>> = HashSet::new();
    for y in &st.out {
        for t in 0..p {
            set.insert((0..p).map(|x| y[(x + t) % p]).collect());
        }
    }
    let mut all: Vec<Vec<i8>> = set.into_iter().collect();
    all.sort();
    (Some(all), st.nodes, e)
}

// ---------------------------------------------------------------------------------------------------------------
// Binary forms of degree n: coefficients c_a of u^{n−a} w^a, a = 0..=n; GL(2, p) orbits of cubics.

/// Orbit representative flags of binary cubic forms (index Σ c_a p^a) under all invertible substitutions.
fn cubic_reps(p: u64) -> Vec<bool> {
    let n = (p * p * p * p) as usize;
    let mut parent: Vec<usize> = (0..n).collect();
    fn find(par: &mut [usize], mut x: usize) -> usize {
        while par[x] != x {
            par[x] = par[par[x]];
            x = par[x];
        }
        x
    }
    let gamma = (2..p).find(|&g| (1..p - 1).all(|e| {
        let mut r = 1;
        for _ in 0..e {
            r = r * g % p;
        }
        r != 1
    })).unwrap_or(1);
    // Substitution (u, w) ↦ (a u + b w, c u + d w): expand Σ c_e (a u + b w)^{3−e} (c u + d w)^e.
    let subst = |co: &[u64; 4], m: [u64; 4]| -> [u64; 4] {
        let [a, b, c, d] = m;
        let mut out = [0u64; 4];
        for e in 0..4 {
            // (a u + b w)^{3−e} (c u + d w)^e as a polynomial in w (u-degree implied).
            let mut poly = vec![1u64];
            for _ in 0..3 - e {
                let mut np = vec![0u64; poly.len() + 1];
                for (i, &q) in poly.iter().enumerate() {
                    np[i] = (np[i] + q * a) % p;
                    np[i + 1] = (np[i + 1] + q * b) % p;
                }
                poly = np;
            }
            for _ in 0..e {
                let mut np = vec![0u64; poly.len() + 1];
                for (i, &q) in poly.iter().enumerate() {
                    np[i] = (np[i] + q * c) % p;
                    np[i + 1] = (np[i + 1] + q * d) % p;
                }
                poly = np;
            }
            for i in 0..4 {
                out[i] = (out[i] + co[e] * poly[i]) % p;
            }
        }
        out
    };
    let gens = [[1, 0, 1, 1], [0, 1, 1, 0], [gamma, 0, 0, 1]];
    for idx in 0..n {
        let mut co = [0u64; 4];
        let mut x = idx as u64;
        for c in co.iter_mut() {
            *c = x % p;
            x /= p;
        }
        for g in gens {
            let o = subst(&co, g);
            let j = (o[0] + p * (o[1] + p * (o[2] + p * o[3]))) as usize;
            let (ri, rj) = (find(&mut parent, idx), find(&mut parent, j));
            if ri != rj {
                let (lo, hi) = if ri < rj { (ri, rj) } else { (rj, ri) };
                parent[hi] = lo;
            }
        }
    }
    (0..n).map(|i| find(&mut parent, i) == i).collect()
}

// ---------------------------------------------------------------------------------------------------------------
// The search.

struct Tomo<'a> {
    p: usize,
    pp: u64,
    s: i64,
    k: usize,
    lam: i64,
    g: &'a Group,
    vecs: Vec<Vec<i8>>,
    /// key[n − 1] = M_n (n = 1..=p−2), key[p − 2] = Y(0) mod p.
    keys: Vec<Vec<u8>>,
    pts: Vec<(u64, u64)>,
    proj: Vec<Vec<usize>>,
    /// Form degrees enumerated, in order.
    levels: Vec<usize>,
    gl: Option<Vec<bool>>,
    all: bool,
    max_nodes: u64,
    nodes: u64,
    enumerated: Vec<u64>,
    accepted: Vec<u64>,
    leaves: u64,
    integral: u64,
    sds: u64,
    found: Option<Vec<i8>>,
    cut: bool,
    /// Current forms h_n (coefficients), for `gl`.
    forms: Vec<Vec<u64>>,
    /// `part=i/m`: only the accepted codewords of the second level with index ≡ i (mod m).
    part: Option<(u64, u64)>,
}

impl Tomo<'_> {
    fn stop(&self) -> bool {
        self.cut || (!self.all && self.found.is_some())
    }

    /// Sub-ranges of `r` by key[col] (the range shares key[..col]).
    fn groups(&self, r: Range, col: usize) -> Vec<(u8, Range)> {
        let mut out = Vec::new();
        let (mut lo, hi) = (r.0 as usize, r.1 as usize);
        while lo < hi {
            let v = self.keys[lo][col];
            let end = lo + self.keys[lo..hi].partition_point(|k| k[col] <= v);
            out.push((v, (lo as u32, end as u32)));
            lo = end;
        }
        out
    }

    /// Value at line point (u, w) of the monomial u^{n−a} w^a.
    fn mono(&self, n: usize, a: usize, i: usize) -> u64 {
        let (u, w) = self.pts[i];
        let mut r = 1u64;
        for _ in 0..n - a {
            r = r * u % self.pp;
        }
        for _ in 0..a {
            r = r * w % self.pp;
        }
        r
    }

    fn level(&mut self, li: usize, ranges: &[Range]) {
        if self.stop() {
            return;
        }
        if li == self.levels.len() {
            self.last(ranges);
            return;
        }
        let n = self.levels[li];
        let p = self.p;
        let pp = self.pp;
        let lines = p + 1;
        let groups: Vec<Vec<(u8, Range)>> = ranges.iter().map(|&r| self.groups(r, n - 1)).collect();
        if groups.iter().any(|g| g.is_empty()) {
            return;
        }
        let mut order: Vec<usize> = (0..lines).collect();
        order.sort_by_key(|&i| (groups[i].len(), i));
        let info: Vec<usize> = order[..n + 1].to_vec();
        let rest: Vec<usize> = order[n + 1..].to_vec();
        // Lagrange: h = Σ_s val_s L_s; E[j][s] = L_s(point j); C[a][s] = coefficient a of L_s.
        let m: Vec<Vec<u64>> = info.iter().map(|&i| (0..=n).map(|a| self.mono(n, a, i)).collect()).collect();
        let minv = mat_inv(&m, pp).expect("information set is singular");
        // coefficients = minv · vals, so C[a][s] = minv[a][s].
        let ev: Vec<Vec<u64>> = rest
            .iter()
            .map(|&j| {
                let row: Vec<u64> = (0..=n).map(|a| self.mono(n, a, j)).collect();
                (0..=n).map(|s| (0..=n).map(|a| row[a] * minv[a][s] % pp).sum::<u64>() % pp).collect()
            })
            .collect();
        let masks: Vec<u32> = rest.iter().map(|&j| groups[j].iter().fold(0u32, |m, &(v, _)| m | 1 << v)).collect();
        let mut pick = vec![0usize; n + 1];
        let mut acc = vec![vec![0u64; rest.len()]; n + 2];
        self.tuples(li, 0, &info, &rest, &groups, &ev, &masks, &minv, &mut pick, &mut acc);
    }

    #[allow(clippy::too_many_arguments)]
    fn tuples(
        &mut self,
        li: usize,
        pos: usize,
        info: &[usize],
        rest: &[usize],
        groups: &[Vec<(u8, Range)>],
        ev: &[Vec<u64>],
        masks: &[u32],
        minv: &[Vec<u64>],
        pick: &mut Vec<usize>,
        acc: &mut Vec<Vec<u64>>,
    ) {
        if self.stop() {
            return;
        }
        let pp = self.pp;
        if pos == info.len() {
            self.nodes += 1;
            self.enumerated[li] += 1;
            if self.nodes > self.max_nodes {
                self.cut = true;
                return;
            }
            let a = &acc[pos];
            if !rest.iter().enumerate().all(|(r, _)| masks[r] >> a[r] & 1 == 1) {
                return;
            }
            let n = self.levels[li];
            let vals: Vec<u64> = (0..info.len()).map(|s| groups[info[s]][pick[s]].0 as u64).collect();
            let coef: Vec<u64> =
                (0..=n).map(|c| (0..=n).map(|s| minv[c][s] * vals[s] % pp).sum::<u64>() % pp).collect();
            if n == 3 {
                if let Some(reps) = &self.gl {
                    let flat = |f: &Vec<u64>| f.iter().all(|&c| c == 0);
                    if self.forms.len() >= 2 && flat(&self.forms[0]) && flat(&self.forms[1]) {
                        let idx = (coef[0] + pp * (coef[1] + pp * (coef[2] + pp * coef[3]))) as usize;
                        if !reps[idx] {
                            return;
                        }
                    }
                }
            }
            self.accepted[li] += 1;
            if li == 1 {
                if let Some((i, m)) = self.part {
                    if (self.accepted[li] - 1) % m != i {
                        return;
                    }
                }
            }
            let mut next = vec![(0u32, 0u32); self.p + 1];
            for (s, &i) in info.iter().enumerate() {
                next[i] = groups[i][pick[s]].1;
            }
            for (r, &j) in rest.iter().enumerate() {
                let v = a[r] as u8;
                next[j] = groups[j].iter().find(|g| g.0 == v).unwrap().1;
            }
            self.forms.push(coef);
            self.level(li + 1, &next);
            self.forms.pop();
            return;
        }
        let i = info[pos];
        for gi in 0..groups[i].len() {
            pick[pos] = gi;
            let v = groups[i][gi].0 as u64;
            for r in 0..rest.len() {
                acc[pos + 1][r] = (acc[pos][r] + v * ev[r][pos]) % pp;
            }
            self.tuples(li, pos + 1, info, rest, groups, ev, masks, minv, pick, acc);
            if self.stop() {
                return;
            }
        }
    }

    /// All moments fixed: choose Y_i(0) mod p with Σ ≡ s, then every vector, then check D.
    fn last(&mut self, ranges: &[Range]) {
        let p = self.p;
        let pp = self.pp;
        let col = p - 2;
        let groups: Vec<Vec<(u8, Range)>> = ranges.iter().map(|&r| self.groups(r, col)).collect();
        // reach[i]: residues Σ_{j ≥ i} r_j can take.
        let rot = |m: u32, v: u64| -> u32 {
            let mut o = 0u32;
            for r in 0..p {
                if m >> r & 1 == 1 {
                    o |= 1 << ((r as u64 + v) % pp);
                }
            }
            o
        };
        let mut reach = vec![0u32; p + 2];
        reach[p + 1] = 1;
        for i in (0..=p).rev() {
            let mut m = 0;
            for &(v, _) in &groups[i] {
                m |= rot(reach[i + 1], v as u64);
            }
            reach[i] = m;
        }
        let target = md(self.s, pp);
        if reach[0] >> target & 1 == 0 {
            return;
        }
        let mut choice = vec![0u32; p + 1];
        self.leaf_rec(0, target, &groups, &reach, &mut choice);
    }

    fn leaf_rec(&mut self, i: usize, need: u64, groups: &[Vec<(u8, Range)>], reach: &[u32], choice: &mut Vec<u32>) {
        if self.stop() {
            return;
        }
        let p = self.p;
        let pp = self.pp;
        if i == p + 1 {
            self.leaf(choice);
            return;
        }
        for &(v, (lo, hi)) in &groups[i] {
            let left = (need + pp - v as u64) % pp;
            if reach[i + 1] >> left & 1 == 0 {
                continue;
            }
            for x in lo..hi {
                self.nodes += 1;
                if self.nodes > self.max_nodes {
                    self.cut = true;
                    return;
                }
                choice[i] = x;
                self.leaf_rec(i + 1, left, groups, reach, choice);
                if self.stop() {
                    return;
                }
            }
        }
    }

    fn leaf(&mut self, choice: &[u32]) {
        self.leaves += 1;
        let p = self.p;
        let v = p * p;
        let mut d = vec![0i8; v];
        let mut unit = true;
        for e in 0..v {
            let tot: i64 = (0..=p).map(|i| self.vecs[choice[i] as usize][self.proj[i][e]] as i64).sum::<i64>() - self.s;
            assert!(tot % p as i64 == 0, "theory: a leaf with a non-integral D");
            let x = tot / p as i64;
            if x.abs() > 1 {
                unit = false;
            }
            d[e] = x.clamp(-1, 1) as i8;
        }
        self.integral += 1;
        if unit {
            assert!(is_sds(self.g, self.k, self.lam, &d), "theory: D in {{0, ±1}} with valid lines but not an SDS");
            self.sds += 1;
            if self.found.is_none() {
                self.found = Some(d);
            }
        }
    }
}

struct Opts {
    max_vec_nodes: u64,
    max_nodes: u64,
    stats: bool,
    all: bool,
    gl: bool,
    /// V := the contractions of this known SDS, closed under translation and scaling (tests the search).
    witness: Option<String>,
    /// V from the U0-invariant vectors when |U0| > 1 (`orbit`); `vcheck`: also the plain DFS, asserted equal.
    orbit: bool,
    vcheck: bool,
    /// V from a file (one vector per line, all translates), e.g. `vlat.py`'s; with `vcheck` asserted = DFS V.
    vfile: Option<String>,
    part: Option<(u64, u64)>,
}

/// D from a file of `a b ±` lines (a header line first); coordinates (a, b) ↦ index a·p + b.
fn read_witness(path: &str, p: usize) -> Vec<i8> {
    let mut d = vec![0i8; p * p];
    for line in std::fs::read_to_string(path).unwrap().lines().skip(1) {
        let f: Vec<&str> = line.split_whitespace().collect();
        if f.len() == 3 {
            let (a, b): (usize, usize) = (f[0].parse().unwrap(), f[1].parse().unwrap());
            d[a * p + b] = if f[2] == "+" { 1 } else { -1 };
        }
    }
    d
}

/// The p + 1 contractions of `d`, each checked against the demands, closed under t ↦ c t + τ.
fn witness_vectors(d: &[i8], p: usize, k: usize, dem: &Demand) -> Vec<Vec<i8>> {
    let pp = p as u64;
    let mut set: HashSet<Vec<i8>> = HashSet::new();
    let pts: Vec<(u64, u64)> = (0..pp).map(|i| (1, i)).chain(std::iter::once((0, 1))).collect();
    for &(u, w) in &pts {
        let mut y = vec![0i64; p];
        for e in 0..p * p {
            y[((u * (e / p) as u64 + w * (e % p) as u64) % pp) as usize] += d[e] as i64;
        }
        let abs: i64 = y.iter().map(|x| x.abs()).sum();
        assert!(y.iter().all(|x| x.abs() <= dem.c), "witness: box");
        assert_eq!(y.iter().sum::<i64>(), dem.sum, "witness: sum");
        assert_eq!(y.iter().map(|x| x * x).sum::<i64>(), dem.square, "witness: square");
        assert!(abs <= k as i64 && (k as i64 - abs) % 2 == 0, "witness: support");
        assert!((1..p).all(|g| (0..p).map(|t| y[t] * y[(t + g) % p]).sum::<i64>() == dem.target), "witness: autocorrelation");
        for c in 1..p {
            for tau in 0..p {
                let mut z = vec![0i8; p];
                for t in 0..p {
                    z[(c * t + tau) % p] = y[t] as i8;
                }
                set.insert(z);
            }
        }
    }
    let mut all: Vec<Vec<i8>> = set.into_iter().collect();
    all.sort();
    all
}

fn run(inst: &Instance, o: &Opts, reps_cache: &Mutex<Vec<(usize, Arc<Vec<bool>>)>>) -> String {
    let sh = &inst.shape;
    let head = format!("{} {}", inst.id, inst.key);
    if sh.len() != 2 || sh[0] != sh[1] || !is_prime(sh[0]) || sh[0] < 3 || sh[0] > 31 {
        return format!("{head} skip shape");
    }
    let p = sh[0];
    let pp = p as u64;
    let Some(dem) = Demand::new(inst.v, inst.k, inst.lam, p) else {
        return format!("{head} skip square");
    };
    let s = dem.sum;
    let t0 = Instant::now();
    let mut ue = 1usize;
    let (vs, vnodes) = match (&o.witness, &o.vfile) {
        (None, Some(path)) => {
            let mut vf: Vec<Vec<i8>> = std::fs::read_to_string(path)
                .unwrap()
                .lines()
                .filter(|l| !l.trim().is_empty())
                .map(|l| l.split_whitespace().map(|x| x.parse::<i8>().unwrap()).collect())
                .collect();
            vf.sort();
            vf.dedup();
            assert!(vf.iter().all(|y| y.len() == p), "{head}: vfile vector length");
            if o.vcheck {
                let (vd, _) = vectors(p, inst.k, &dem, o.max_vec_nodes);
                let vd = vd.expect("vcheck: DFS cut");
                assert!(vd == vf, "{head}: vfile V ({}) ≠ DFS V ({})", vf.len(), vd.len());
            }
            (Some(vf), 0)
        }
        _ => match &o.witness {
        Some(path) => {
            let g = Group::new(&[p, p]);
            let mut d = read_witness(path, p);
            assert!(is_sds(&g, inst.k, inst.lam, &d), "witness is not an SDS");
            if d.iter().map(|&x| x as i64).sum::<i64>() != s {
                d.iter_mut().for_each(|x| *x = -*x);
            }
            (Some(witness_vectors(&d, p, inst.k, &dem)), 0)
        }
        None => {
            let (vo, onodes, e) =
                if o.orbit || o.vcheck { vectors_orbit(p, inst.k, inst.lam, &dem, o.max_vec_nodes) } else { (None, 0, 1) };
            ue = e;
            match vo {
                Some(vo) if !o.vcheck => (Some(vo), onodes),
                Some(vo) => {
                    let (vd, dn) = vectors(p, inst.k, &dem, o.max_vec_nodes);
                    if let Some(vd) = &vd {
                        assert!(*vd == vo, "{head}: orbit V ({}) ≠ DFS V ({})", vo.len(), vd.len());
                    }
                    (vd, dn)
                }
                None => vectors(p, inst.k, &dem, o.max_vec_nodes),
            }
        }
    },
    };
    let Some(vecs) = vs else {
        return format!("{head} p={p} s={s} CUT V vnodes={vnodes} {:.1}s", t0.elapsed().as_secs_f64());
    };
    // Engine cross-check: its first vector is in V; it finds none iff V is empty.
    let eng = if o.witness.is_some() { None } else { Some(engine_search(&Group::new(&[p]), inst.k, &dem, o.max_vec_nodes.min(ENGINE_CAP))) };
    if let Some(eng) = eng.filter(|e| !e.cut) {
        match &eng.found {
            Some(y) => {
                let y8: Vec<i8> = y.iter().map(|&x| x as i8).collect();
                assert!(vecs.binary_search(&y8).is_ok(), "{head}: engine vector not in V");
            }
            None => assert!(vecs.is_empty(), "{head}: engine finds no vector, V nonempty"),
        }
    }
    if vecs.is_empty() {
        return format!("{head} p={p} s={s} V=0 vnodes={vnodes} KILL V=0 {:.2}s", t0.elapsed().as_secs_f64());
    }
    // Moment keys.
    let pw: Vec<Vec<u64>> = (0..pp).map(|t| (0..pp).map(|n| {
        let mut r = 1u64;
        for _ in 0..n {
            r = r * t % pp;
        }
        r
    }).collect()).collect();
    let key_of = |y: &[i8]| -> Vec<u8> {
        let mut k: Vec<u8> = (1..=p - 2)
            .map(|n| (0..p).map(|t| md(y[t] as i64, pp) * pw[t][n] % pp).sum::<u64>() % pp)
            .map(|x| x as u8)
            .collect();
        k.push(md(y[0] as i64, pp) as u8);
        k
    };
    let mut pairs: Vec<(Vec<u8>, Vec<i8>)> = vecs.into_iter().map(|y| (key_of(&y), y)).collect();
    pairs.sort();
    let (keys, vecs): (Vec<Vec<u8>>, Vec<Vec<i8>>) = pairs.into_iter().unzip();
    let smod = md(s, pp);
    let preset = smod != 0;
    let v0 = if preset { keys.iter().filter(|k| k[0] == 0).count() } else { keys.len() };
    let vinfo = format!("p={p} s={s} U0={ue} V={} V0={v0} vnodes={vnodes}", vecs.len());
    if o.stats {
        return format!("{head} {vinfo} {:.2}s", t0.elapsed().as_secs_f64());
    }
    let pts: Vec<(u64, u64)> = (0..pp).map(|i| (1, i)).chain(std::iter::once((0, 1))).collect();
    let proj: Vec<Vec<usize>> =
        pts.iter().map(|&(u, w)| (0..p * p).map(|e| ((u * (e / p) as u64 + w * (e % p) as u64) % pp) as usize).collect()).collect();
    let g = Group::new(&[p, p]);
    let gl = if o.gl && preset {
        let mut c = reps_cache.lock().unwrap();
        let r = match c.iter().find(|(q, _)| *q == p) {
            Some((_, r)) => r.clone(),
            None => {
                let r = Arc::new(cubic_reps(pp));
                c.push((p, r.clone()));
                r
            }
        };
        Some((*r).clone())
    } else {
        None
    };
    let levels: Vec<usize> = if preset { (2..=p - 2).collect() } else { (1..=p - 2).collect() };
    let nl = levels.len();
    let mut t = Tomo {
        p,
        pp,
        s,
        k: inst.k,
        lam: inst.lam,
        g: &g,
        vecs,
        keys,
        pts,
        proj,
        levels,
        gl,
        all: o.all,
        max_nodes: o.max_nodes,
        nodes: 0,
        enumerated: vec![0; nl],
        accepted: vec![0; nl],
        leaves: 0,
        integral: 0,
        sds: 0,
        found: None,
        cut: false,
        forms: if preset { vec![vec![0, 0]] } else { Vec::new() },
        part: o.part,
    };
    let start: Range = if preset {
        let lo = 0;
        let hi = t.keys.partition_point(|k| k[0] <= 0);
        (lo as u32, hi as u32)
    } else {
        (0, t.keys.len() as u32)
    };
    if start.0 == start.1 {
        return format!("{head} {vinfo} KILL V0=0 {:.2}s", t0.elapsed().as_secs_f64());
    }
    let ranges = vec![start; p + 1];
    t.level(0, &ranges);
    let lv: Vec<String> =
        t.levels.iter().enumerate().filter(|&(i, _)| t.enumerated[i] > 0).map(|(i, n)| format!("{n}:{}/{}", t.enumerated[i], t.accepted[i])).collect();
    let verdict = if t.cut {
        "CUT".to_string()
    } else if let Some(d) = &t.found {
        assert!(is_sds(&g, inst.k, inst.lam, d));
        format!("FOUND (checked SDS) D={}", d.iter().map(|x| match x { 1 => '+', -1 => '-', _ => '0' }).collect::<String>())
    } else if t.integral == 0 {
        "KILL int".to_string()
    } else {
        "KILL sds".to_string()
    };
    format!(
        "{head} {vinfo} gl={} nodes={} levels=[{}] leaves={} integral={} sds={} {verdict} {:.2}s",
        t.gl.is_some(),
        t.nodes,
        lv.join(" "),
        t.leaves,
        t.integral,
        t.sds,
        t0.elapsed().as_secs_f64()
    )
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a.len() < 7 {
        eprintln!("usage: x_tomography <instances.csv> <ids file> <threads> <max_vec_nodes> <max_nodes> <out> [stats] [all] [gl]");
        std::process::exit(2);
    }
    let insts = read(&a[1]);
    let ids: Vec<String> = std::fs::read_to_string(&a[2])
        .unwrap()
        .lines()
        .filter_map(|l| l.split_whitespace().next().map(String::from))
        .collect();
    let threads: usize = a[3].parse().unwrap();
    let flag = |f: &str| a[7..].iter().any(|x| x == f);
    let o = Arc::new(Opts {
        max_vec_nodes: a[4].parse::<f64>().unwrap() as u64,
        max_nodes: a[5].parse::<f64>().unwrap() as u64,
        stats: flag("stats"),
        all: flag("all"),
        gl: flag("gl"),
        orbit: flag("orbit"),
        part: a[7..].iter().find_map(|x| x.strip_prefix("part=")).map(|x| {
            let (i, m) = x.split_once('/').unwrap();
            (i.parse().unwrap(), m.parse().unwrap())
        }),
        vfile: a[7..].iter().find_map(|x| x.strip_prefix("vfile=").map(String::from)),
        vcheck: flag("vcheck"),
        witness: a[7..].iter().find_map(|x| x.strip_prefix("witness=").map(String::from)),
    });
    let insts = Arc::new(insts);
    let todo: Vec<usize> = ids.iter().filter_map(|id| insts.iter().position(|i| &i.id == id)).collect();
    let queue = Arc::new(Mutex::new(todo.into_iter().rev().collect::<Vec<usize>>()));
    let out = Arc::new(Mutex::new(std::fs::OpenOptions::new().create(true).append(true).open(&a[6]).unwrap()));
    let cache = Arc::new(Mutex::new(Vec::new()));
    let hs: Vec<_> = (0..threads)
        .map(|_| {
            let (queue, out, o, cache, insts) = (queue.clone(), out.clone(), o.clone(), cache.clone(), insts.clone());
            std::thread::spawn(move || loop {
                let Some(ix) = queue.lock().unwrap().pop() else { break };
                let line = run(&insts[ix], &o, &cache);
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
