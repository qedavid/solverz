//! Exploration (tomo3): tomography on a quotient Q_a = Z_{p^a} × Z_p of G, level by level. On Q_l the p cyclic
//! quotients Q_l/K_j ≅ Z_{p^l} (K_j = ⟨(j p^{l−1}, 1)⟩) and U on Q_l/P_0 = Q_{l−1} (P_0 = ⟨(p^{l−1}, 0)⟩) give
//! p D(x) = Σ_j Y_j(t − j p^{l−1} u) − Z(t mod p^{l−1}) + U(t mod p^{l−1}, u), Z the contraction of U (and of every Y_j)
//! to Z_{p^{l−1}} (incidence count over Q_l[p]). Level 1 is the line identity on Z_p². Per level: every valid U (up to
//! translation), Y_0..Y_{p−2} from V_l with contraction Z, Y_{p−1} looked up by the residues it must have; D integral,
//! |D| ≤ v/p^{l+1}, Σ|D| ≤ k with parity (autocorrelation and sum asserted). No D at some level: KILL (C3 on Q_l).
//! Usage: x_tomo_cyc <instances.csv> <ids file: id p a> <threads> <max_vec_nodes> <out> [max_out=]
//! Line: id key p a s [per level: U reps, |V_l|, nodes, integral, valid reps] verdict seconds.

use signed_difference_sets::contraction::Demand;
use signed_difference_sets::Group;
use signed_difference_sets::instances::{read, Instance};
use std::collections::{HashMap, HashSet};
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

// ---------------------------------------------------------------------------------------------------------------
// V on a block H = Z_p × Z_m (index t·m + k): every vector meeting the demands, all translates.

struct VecEnumG<'a> {
    h: &'a Group,
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
    /// Fourier bound: fre/fim[d][u] = Σ_{x<d} a_x χ_u(x) for every character u ≠ 0; cs/sn[u][x]; √(k − λ).
    fre: Vec<Vec<f64>>,
    fim: Vec<Vec<f64>>,
    cs: Vec<Vec<f64>>,
    sn: Vec<Vec<f64>>,
    root_n: f64,
}

impl VecEnumG<'_> {
    /// After a_d = x: |R_u| ≥ ||P_u| − √n| for every u ≠ 0, and Σ_{u≠0} |R_u|² = N Σ R² − (Σ R)² (Parseval).
    fn fourier_ok(&mut self, d: usize, x: i64, after: i64, left_sum: i64) -> bool {
        let n = self.h.order;
        let mut lhs = 0.0;
        for u in 1..n {
            let re = self.fre[d][u] + x as f64 * self.cs[u][d];
            let im = self.fim[d][u] + x as f64 * self.sn[u][d];
            self.fre[d + 1][u] = re;
            self.fim[d + 1][u] = im;
            let gap = (re * re + im * im).sqrt() - self.root_n;
            lhs += gap * gap;
        }
        let rhs = (n as i64 * after - left_sum * left_sum) as f64;
        lhs <= rhs + 1e-6 * (1.0 + rhs.abs())
    }

    /// Assign position d := x (dir = 1) or undo it (dir = −1); positions < d are assigned.
    fn touch(&mut self, d: usize, x: i64, dir: i64) {
        let n = self.h.order;
        for g in 1..n {
            // Terms x₀ = d (other end d + g) and x₀ = d − g (other end d − g).
            for o in [self.h.add[d][g], self.h.sub[d][g]] {
                if o < d {
                    self.partial[g] += dir * x * self.a[o];
                    self.a1[g] -= dir * self.a[o].abs();
                } else {
                    self.n2[g] -= dir;
                    self.a1[g] += dir * x.abs();
                }
            }
        }
    }

    fn go(&mut self, d: usize, sum: i64, sq: i64, abs: i64) {
        self.nodes += 1;
        if self.nodes > self.max_nodes {
            self.cut = true;
            return;
        }
        let n = self.h.order;
        let (c, square, s, target) = (self.dem.c, self.dem.square, self.dem.sum, self.dem.target);
        if d == n {
            if sum == s && sq == square && abs <= self.k && (self.k - abs) % 2 == 0 && (1..n).all(|g| self.partial[g] == target) {
                self.out.push(self.a.iter().map(|&x| x as i16).collect());
            }
            return;
        }
        let rem = (n - d) as i64;
        let left_sq = square - sq;
        let left_sum = s - sum;
        if left_sq < 0 || left_sum * left_sum > rem * left_sq || left_sum.abs() > rem * c {
            return;
        }
        if d == n - 2 && d > 0 {
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
                self.go(n, sum + x + y, sq + x * x + y * y, abs + x.abs() + y.abs());
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
            let mm = c.min(isqrt(after)).min(self.a[0].abs().max(x.abs()));
            let ok = (1..n).all(|g| (target - self.partial[g]).abs() <= mm * self.a1[g] + (mm * mm * self.n2[g]).min(after))
                && self.fourier_ok(d, x, after, left_sum - x);
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

fn vectors_group(h: &Group, k: usize, dem: &Demand, max_nodes: u64) -> (Option<Vec<Vec<i16>>>, u64) {
    let n = h.order;
    let mut e = VecEnumG {
        h,
        k: k as i64,
        dem,
        a: vec![0; n],
        partial: vec![0; n],
        a1: vec![0; n],
        n2: vec![n as i64; n],
        nodes: 0,
        max_nodes,
        cut: false,
        out: Vec::new(),
        fre: vec![vec![0.0; n]; n + 1],
        fim: vec![vec![0.0; n]; n + 1],
        cs: Vec::new(),
        sn: Vec::new(),
        root_n: ((k as i64 - dem.target / dem.c) as f64).max(0.0).sqrt(),
    };
    // Characters of ∏ Z_{m_i}: χ_u(x) = exp(2πi Σ u_i x_i / m_i).
    let phase = |u: usize, x: usize| -> f64 {
        let (cu, cx) = (h.coords(u), h.coords(x));
        cu.iter().zip(&cx).zip(&h.shape).map(|((a, b), m)| (a * b % m) as f64 / *m as f64).sum::<f64>()
    };
    e.cs = (0..n).map(|u| (0..n).map(|x| (2.0 * std::f64::consts::PI * phase(u, x)).cos()).collect()).collect();
    e.sn = (0..n).map(|u| (0..n).map(|x| (2.0 * std::f64::consts::PI * phase(u, x)).sin()).collect()).collect();
    e.go(0, 0, 0, 0);
    if e.cut {
        return (None, e.nodes);
    }
    let mut set: HashSet<Vec<i16>> = HashSet::new();
    for y in &e.out {
        for t in 0..n {
            set.insert((0..n).map(|x| y[h.add[x][t]]).collect());
        }
    }
    let mut all: Vec<Vec<i16>> = set.into_iter().collect();
    all.sort();
    (Some(all), e.nodes)
}

// ---------------------------------------------------------------------------------------------------------------
// Level l: Q_l = Z_{p^l} × Z_p (index t·p + u), P_0 = ⟨(p^{l−1}, 0)⟩, Q[p] = ⟨P_0, (0, 1)⟩, K_j = ⟨(j p^{l−1}, 1)⟩.
// π_j(t, u) = t − j p^{l−1} u mod p^l. Incidence: Σ_j Y_j(π_j x) = p D(x) + Z(t mod p^{l−1}) − U(t mod p^{l−1}, u),
// U the vector on Q/P_0 = Q_{l−1}, Z its contraction to Q/Q[p] = Z_{p^{l−1}} (shared by every Y_j).

fn translates_q(y: &[i16], pl: usize, p: usize) -> Vec<Vec<i16>> {
    let mut out = Vec::new();
    for t0 in 0..pl {
        for u0 in 0..p {
            out.push((0..pl * p).map(|i| y[((i / p + t0) % pl) * p + (i % p + u0) % p]).collect());
        }
    }
    out
}

fn rep_of(y: &[i16], pl: usize, p: usize) -> Vec<i16> {
    translates_q(y, pl, p).into_iter().min().unwrap()
}

struct Level {
    l: usize,
    ureps: usize,
    vl: usize,
    nodes: u64,
    integral: u64,
    valid: usize,
}

/// All valid vectors on Q_l (as translate representatives) from the representatives on Q_{l−1}; None when capped.
#[allow(clippy::too_many_arguments)]
fn level(
    p: usize,
    l: usize,
    v: usize,
    k: usize,
    lam: i64,
    s: i64,
    ureps: &[Vec<i16>],
    max_vec_nodes: u64,
    max_out: usize,
    stats: &mut Vec<Level>,
) -> Option<Vec<Vec<i16>>> {
    let pl = p.pow(l as u32);
    let pl1 = pl / p;
    let dem = Demand::new(v, k, lam, pl)?;
    let (vl, _) = vectors_group(&Group::new(&[pl]), k, &dem, max_vec_nodes);
    let vl = vl?;
    // Group V_l by contraction to Z_{p^{l−1}}; inside, by residues mod p.
    let mut by_z: HashMap<Vec<i64>, Vec<usize>> = HashMap::new();
    for (i, y) in vl.iter().enumerate() {
        let z: Vec<i64> = (0..pl1).map(|t| (0..p).map(|i2| y[t + i2 * pl1] as i64).sum()).collect();
        by_z.entry(z).or_default().push(i);
    }
    let box_ = (v / (pl * p)) as i64;
    let (kk, pi) = (k as i64, p as i64);
    let mut found: HashSet<Vec<i16>> = HashSet::new();
    let mut st = Level { l, ureps: ureps.len(), vl: vl.len(), nodes: 0, integral: 0, valid: 0 };
    for u in ureps {
        let z: Vec<i64> = (0..pl1).map(|t| (0..p).map(|uu| u[t * p + uu] as i64).sum()).collect();
        let Some(cands) = by_z.get(&z) else { continue };
        let mut by_res: HashMap<Vec<u8>, Vec<usize>> = HashMap::new();
        for &c in cands {
            by_res.entry(vl[c].iter().map(|&x| (x as i64).rem_euclid(pi) as u8).collect()).or_default().push(c);
        }
        // DFS over j = 0..p−2, the last block forced mod p.
        let mut pick = vec![0usize; p];
        let mut stack = vec![0usize; p - 1];
        let mut depth = 0usize;
        if p == 1 {
            continue;
        }
        loop {
            if depth == p - 1 {
                st.nodes += 1;
                // Residue the last block must have at τ = π_{p−1}(x).
                let mut need: Vec<Option<u8>> = vec![None; pl];
                let mut ok = true;
                'x: for t in 0..pl {
                    for uu in 0..p {
                        let mut tot = z[t % pl1] - u[(t % pl1) * p + uu] as i64;
                        for j in 0..p - 1 {
                            tot -= vl[pick[j]][(t + pl - (j * pl1 * uu) % pl) % pl] as i64;
                        }
                        let r = tot.rem_euclid(pi) as u8;
                        let tau = (t + pl - ((p - 1) * pl1 * uu) % pl) % pl;
                        match need[tau] {
                            None => need[tau] = Some(r),
                            Some(q) if q != r => {
                                ok = false;
                                break 'x;
                            }
                            _ => {}
                        }
                    }
                }
                if ok {
                    let key: Vec<u8> = need.iter().map(|x| x.unwrap()).collect();
                    for &c in by_res.get(&key).map(|x| x.as_slice()).unwrap_or(&[]) {
                        pick[p - 1] = c;
                        let mut d = vec![0i64; pl * p];
                        for t in 0..pl {
                            for uu in 0..p {
                                let mut tot = -z[t % pl1] + u[(t % pl1) * p + uu] as i64;
                                for j in 0..p {
                                    tot += vl[pick[j]][(t + pl - (j * pl1 * uu) % pl) % pl] as i64;
                                }
                                assert!(tot % pi == 0, "theory: residue forcing");
                                d[t * p + uu] = tot / pi;
                            }
                        }
                        st.integral += 1;
                        let abs: i64 = d.iter().map(|x| x.abs()).sum();
                        if d.iter().all(|x| x.abs() <= box_) && abs <= kk && (kk - abs) % 2 == 0 {
                            let g = Group::new(&[pl, p]);
                            for gg in 1..pl * p {
                                let ac: i64 = (0..pl * p).map(|x| d[x] * d[g.add[x][gg]]).sum();
                                assert_eq!(ac, lam * box_, "theory: autocorrelation");
                            }
                            assert_eq!(d.iter().sum::<i64>(), s, "theory: sum");
                            let d16: Vec<i16> = d.iter().map(|&x| x as i16).collect();
                            found.insert(rep_of(&d16, pl, p));
                            if found.len() > max_out {
                                stats.push(st);
                                return None;
                            }
                        }
                    }
                }
                depth -= 1;
                stack[depth] += 1;
                continue;
            }
            if stack[depth] >= cands.len() {
                if depth == 0 {
                    break;
                }
                stack[depth] = 0;
                depth -= 1;
                stack[depth] += 1;
                continue;
            }
            pick[depth] = cands[stack[depth]];
            depth += 1;
            if depth < p - 1 {
                stack[depth] = 0;
            }
        }
    }
    st.valid = found.len();
    stats.push(st);
    let mut out: Vec<Vec<i16>> = found.into_iter().collect();
    out.sort();
    Some(out)
}

fn run(inst: &Instance, p: usize, a: usize, max_vec_nodes: u64, max_out: usize) -> String {
    let head = format!("{} {} p={p} a={a}", inst.id, inst.key);
    let mut es: Vec<usize> = inst
        .shape
        .iter()
        .map(|&m| {
            let (mut m, mut e) = (m, 0);
            while m % p == 0 {
                m /= p;
                e += 1;
            }
            e
        })
        .filter(|&e| e > 0)
        .collect();
    es.sort_unstable_by(|x, y| y.cmp(x));
    if !is_prime(p) || es.len() < 2 || es[0] < a || a < 1 {
        return format!("{head} skip shape");
    }
    let t0 = Instant::now();
    let Some(dem) = Demand::new(inst.v, inst.k, inst.lam, p) else {
        return format!("{head} skip square");
    };
    let s = dem.sum;
    let (u0, _) = vectors_group(&Group::new(&[p]), inst.k, &dem, max_vec_nodes);
    let Some(u0) = u0 else { return format!("{head} CUT V0") };
    let mut reps: Vec<Vec<i16>> = u0.iter().map(|y| rep_of(y, 1, p)).collect();
    reps.sort();
    reps.dedup();
    let mut stats = Vec::new();
    let mut verdict = String::new();
    for l in 1..=a {
        match level(p, l, inst.v, inst.k, inst.lam, s, &reps, max_vec_nodes, max_out, &mut stats) {
            None => {
                verdict = format!("CUT at l={l}");
                break;
            }
            Some(next) => {
                if next.is_empty() {
                    verdict = format!("KILL at l={l} (Z_{} x Z_{p})", p.pow(l as u32));
                    break;
                }
                reps = next;
            }
        }
    }
    if verdict.is_empty() {
        verdict = format!("FOUND {} reps", reps.len());
    }
    let lv: Vec<String> = stats
        .iter()
        .map(|st| format!("l{}:U={},V={},nodes={},int={},valid={}", st.l, st.ureps, st.vl, st.nodes, st.integral, st.valid))
        .collect();
    format!("{head} s={s} [{}] {verdict} {:.2}s", lv.join(" "), t0.elapsed().as_secs_f64())
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a.len() < 6 {
        eprintln!("usage: x_tomo_cyc <instances.csv> <ids file: id p a> <threads> <max_vec_nodes> <out> [max_out=]");
        std::process::exit(2);
    }
    let insts = read(&a[1]);
    let threads: usize = a[3].parse().unwrap();
    let max_vec_nodes = a[4].parse::<f64>().unwrap() as u64;
    let max_out: usize = a[6..].iter().find_map(|x| x.strip_prefix("max_out=")).map(|x| x.parse().unwrap()).unwrap_or(200_000);
    let mut todo: Vec<(usize, usize, usize)> = Vec::new();
    for l in std::fs::read_to_string(&a[2]).unwrap().lines() {
        let f: Vec<&str> = l.split_whitespace().collect();
        if f.len() < 3 {
            continue;
        }
        let Some(ix) = insts.iter().position(|i| i.id == f[0]) else { continue };
        todo.push((ix, f[1].parse().unwrap(), f[2].parse().unwrap()));
    }
    let insts = Arc::new(insts);
    let queue = Arc::new(Mutex::new(todo.into_iter().rev().collect::<Vec<_>>()));
    let out = Arc::new(Mutex::new(std::fs::OpenOptions::new().create(true).append(true).open(&a[5]).unwrap()));
    let hs: Vec<_> = (0..threads)
        .map(|_| {
            let (queue, out, insts) = (queue.clone(), out.clone(), insts.clone());
            std::thread::spawn(move || loop {
                let Some((ix, p, aa)) = queue.lock().unwrap().pop() else { break };
                let line = run(&insts[ix], p, aa, max_vec_nodes, max_out);
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
