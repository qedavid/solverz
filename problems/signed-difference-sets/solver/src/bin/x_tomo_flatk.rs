//! Exploration (tomo3): tomography on a quotient Q = Z_p^r × Z_m of G (m | exp of the p′-part, p ∤ m), box
//! c = v/(p^r m). Blocks: the hyperplanes f, each a vector y_f on Z_p × Z_m (index t·m + k, fibres v/(pm)) meeting
//! C3/C4. p^{r−1} Y(x, k) = Σ_f y_f(f·x, k) − ((p^{r−1} − 1)/(p − 1)) Y_K(k), Y_K the contraction to Z_m (all blocks
//! share it). Integrality mod p holds slice by slice (fixed k): on every pencil the moments of slice k lie on one binary
//! form and Σ y(0, k) ≡ Y_K(k), as in `x_tomo_flat` (m = 1). Every completed flat of dimension d must be integral, in its
//! box v/(p^d m), Σ| | ≤ k with parity. Translation: block e₁ up to Z_p × Z_m shifts, e₂..e_r up to Z_p shifts.
//! V by a DFS on the group Z_p × Z_m (every shift's autocorrelation; `vcheck`: equal to the Z_p DFS when m = 1).
//! Usage: x_tomo_flatk <instances.csv> <ids file: id p r m> <threads> <max_vec_nodes> <max_nodes> <out> [all] [vcheck]
//! Line: id key p r m c s V kclasses reps vnodes nodes rejects(d = 2..r) leaves integral valid miss verdict secs.

use signed_difference_sets::contraction::Demand;
use signed_difference_sets::Group;
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
// The search on Q = Z_p^r × Z_m; blocks y_f on Z_p × Z_m (index t·m + k).

struct Search<'a> {
    p: usize,
    pp: u64,
    r: usize,
    m: usize,
    k: i64,
    lam: i64,
    v: usize,
    vecs: &'a [Vec<i16>],
    /// keys[vi][k·(p − 1) + n − 1] = M_n of slice k (n = 1..p − 2); [k·(p − 1) + p − 2] = y(0, k) mod p.
    keys: &'a [Vec<u8>],
    /// Class of the contraction to Z_m (equal classes ⇔ equal contractions) and the contraction itself.
    kclass: Vec<usize>,
    kvec: Vec<Vec<i64>>,
    rep_full: Vec<bool>,
    rep_t: Vec<bool>,
    order: Vec<usize>,
    pos_of: Vec<usize>,
    flats: &'a [Flat],
    pencils_of: Vec<Vec<(usize, usize)>>,
    interp: Vec<Vec<(Vec<usize>, Vec<Option<Vec<u64>>>)>>,
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

fn pw(x: u64, e: usize, p: u64) -> u64 {
    let mut r = 1u64;
    for _ in 0..e {
        r = r * x % p;
    }
    r
}

impl Search<'_> {
    fn stop(&self) -> bool {
        self.cut || (!self.all && self.found.is_some())
    }

    fn yk(&self) -> &Vec<i64> {
        &self.kvec[self.assign[self.order[0]]]
    }

    /// Quotient vector of a completed flat on F_p^d × Z_m (index ξ·m + k), or None if not integral.
    fn flat_vector(&self, fi: usize) -> Option<Vec<i64>> {
        let f = &self.flats[fi];
        let (p, pp, d, m) = (self.p, self.pp, f.d, self.m);
        let npts = p.pow(d as u32);
        let hd: i64 = (p.pow(d as u32 - 1) as i64 - 1) / (p as i64 - 1);
        let den = p.pow(d as u32 - 1) as i64;
        let yk = self.yk();
        let mut out = vec![0i64; npts * m];
        for xi in 0..npts {
            let mut coord = vec![0u64; d];
            let mut y = xi;
            for j in (0..d).rev() {
                coord[j] = (y % p) as u64;
                y /= p;
            }
            let ts: Vec<usize> = f
                .members
                .iter()
                .map(|(_, c, li)| ((c.iter().zip(&coord).map(|(a, b)| a * b).sum::<u64>() % pp) * li % pp) as usize)
                .collect();
            for kk in 0..m {
                let mut tot = -hd * yk[kk];
                for ((b, _, _), &t) in f.members.iter().zip(&ts) {
                    tot += self.vecs[self.assign[*b]][t * m + kk] as i64;
                }
                if tot % den != 0 {
                    return None;
                }
                out[xi * m + kk] = tot / den;
            }
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
        let box_ = (self.v / (self.p.pow(d as u32) * self.m)) as i64;
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
        let (p, pp, m) = (self.p, self.pp, self.m);
        let w = p - 1;
        let mut forced: Vec<(usize, u8)> = Vec::new();
        for &(pi, mi) in &self.pencils_of[b] {
            let fl = &self.flats[pi];
            let assigned = fl.members.iter().filter(|mm| self.pos_of[mm.0] < depth).count();
            for n in 1..=p - 2 {
                if assigned < n + 1 {
                    break;
                }
                let (info, coefs) = &self.interp[pi][n];
                let Some(co) = &coefs[mi] else { continue };
                let lin = pw(fl.members[mi].2, n, pp);
                for kk in 0..m {
                    let mut val = 0u64;
                    for (s, &ii) in info.iter().enumerate() {
                        let (bb, _, li) = &fl.members[ii];
                        let mom = self.keys[self.assign[*bb]][kk * w + n - 1] as u64;
                        // value at a member = λ^n M_n, λ = (λ⁻¹)⁻¹.
                        let lam = inv_mod(*li, pp);
                        val = (val + co[s] * (mom * pw(lam, n, pp) % pp)) % pp;
                    }
                    forced.push((kk * w + n - 1, (val * lin % pp) as u8));
                }
            }
            if assigned == p {
                let yk = self.yk();
                for kk in 0..m {
                    let mut need = md(yk[kk], pp);
                    for mm in &fl.members {
                        if mm.0 != b {
                            need = (need + pp - md(self.vecs[self.assign[mm.0]][kk] as i64, pp)) % pp;
                        }
                    }
                    forced.push((kk * w + p - 2, need as u8));
                }
            }
        }
        let kc = if depth == 0 { usize::MAX } else { self.kclass[self.assign[self.order[0]]] };
        for vi in 0..self.vecs.len() {
            if depth == 0 && !self.rep_full[vi] {
                continue;
            }
            if depth > 0 && depth < self.r && !self.rep_t[vi] {
                continue;
            }
            if depth > 0 && self.kclass[vi] != kc {
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
        let (p, pp, r, m) = (self.p, self.pp, self.r, self.m);
        let nq = p.pow(r as u32);
        let den = p.pow(r as u32 - 1) as i64;
        let hr: i64 = (den - 1) / (p as i64 - 1);
        let yk = self.yk().clone();
        let mut y = vec![0i64; nq * m];
        for xi in 0..nq {
            let mut x = vec![0u64; r];
            let mut t = xi;
            for j in (0..r).rev() {
                x[j] = (t % p) as u64;
                t /= p;
            }
            for kk in 0..m {
                let mut tot = -hr * yk[kk];
                for (bi, h) in self.hyps.iter().enumerate() {
                    let c = (h.iter().zip(&x).map(|(a, b)| a * b).sum::<u64>() % pp) as usize;
                    tot += self.vecs[self.assign[bi]][c * m + kk] as i64;
                }
                if tot % den != 0 {
                    return;
                }
                y[xi * m + kk] = tot / den;
            }
        }
        self.integral += 1;
        let cq = (self.v / (nq * m)) as i64;
        let abs: i64 = y.iter().map(|x| x.abs()).sum();
        if y.iter().any(|x| x.abs() > cq) || abs > self.k || (self.k - abs) % 2 != 0 {
            return;
        }
        let mut shape = vec![p; r];
        shape.push(m);
        let g = Group::new(&shape);
        for gg in 1..g.order {
            let ac: i64 = (0..g.order).map(|x| y[x] * y[g.add[x][gg]]).sum();
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
    vcheck: bool,
}

/// Largest cyclic factor's order of the p′-part divisible by m (m | exp of the p′-part).
fn has_cyclic_quotient(shape: &[usize], p: usize, m: usize) -> bool {
    let mut mm = m;
    let mut q = 2;
    while mm > 1 {
        if mm % q == 0 {
            let mut e = 1;
            while mm % q == 0 {
                mm /= q;
                e *= q;
            }
            if q == p || !shape.iter().any(|&x| x % e == 0) {
                return false;
            }
        }
        q += 1;
    }
    true
}

fn run(inst: &Instance, p: usize, r: usize, m: usize, o: &Opts) -> String {
    let head = format!("{} {} p={p} r={r} m={m}", inst.id, inst.key);
    let rank = inst.shape.iter().filter(|&&x| x % p == 0).count();
    if !is_prime(p) || rank < r || r < 2 || p.pow(r as u32) * m > 4000 || !has_cyclic_quotient(&inst.shape, p, m) {
        return format!("{head} skip shape");
    }
    let pp = p as u64;
    let Some(dem) = Demand::new(inst.v, inst.k, inst.lam, p * m) else {
        return format!("{head} skip square");
    };
    let cq = inst.v / (p.pow(r as u32) * m);
    let t0 = Instant::now();
    let hgrp = Group::new(&[p, m]);
    let (vs, vnodes) = vectors_group(&hgrp, inst.k, &dem, o.max_vec_nodes);
    let Some(vecs) = vs else {
        return format!("{head} c={cq} CUT V vnodes={vnodes} {:.1}s", t0.elapsed().as_secs_f64());
    };
    if o.vcheck && m == 1 {
        let (vd, _) = vectors(p, inst.k, &dem, o.max_vec_nodes);
        assert!(vd.as_ref() == Some(&vecs), "{head}: generic V ≠ Z_p V");
    }
    if vecs.is_empty() {
        return format!("{head} c={cq} V=0 KILL V=0 {:.2}s", t0.elapsed().as_secs_f64());
    }
    let w = p - 1;
    let keys: Vec<Vec<u8>> = vecs
        .iter()
        .map(|y| {
            let mut key = vec![0u8; m * w];
            for kk in 0..m {
                for n in 1..=p - 2 {
                    key[kk * w + n - 1] =
                        ((0..p).map(|t| md(y[t * m + kk] as i64, pp) * pw(t as u64, n, pp) % pp).sum::<u64>() % pp) as u8;
                }
                key[kk * w + p - 2] = md(y[kk] as i64, pp) as u8;
            }
            key
        })
        .collect();
    let kvec: Vec<Vec<i64>> = vecs.iter().map(|y| (0..m).map(|kk| (0..p).map(|t| y[t * m + kk] as i64).sum()).collect()).collect();
    let mut classes: Vec<Vec<i64>> = kvec.clone();
    classes.sort();
    classes.dedup();
    let kclass: Vec<usize> = kvec.iter().map(|kv| classes.binary_search(kv).unwrap()).collect();
    let shift = |y: &Vec<i16>, g: usize| -> Vec<i16> { (0..p * m).map(|x| y[hgrp.add[x][g]]).collect() };
    let rep_full: Vec<bool> = vecs.iter().map(|y| (1..p * m).all(|g| *y <= shift(y, g))).collect();
    let rep_t: Vec<bool> = vecs.iter().map(|y| (1..p).all(|t| *y <= shift(y, t * m))).collect();
    // Hyperplanes, flats, order, interpolation: as in x_tomo_flat.
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
    let mut order: Vec<usize> = (0..r).map(|j| hyp_index[p.pow((r - 1 - j) as u32)]).collect();
    let mut in_order = vec![false; nb];
    order.iter().for_each(|&b| in_order[b] = true);
    let pencil_ids: Vec<usize> = (0..fl.len()).filter(|&i| fl[i].d == 2).collect();
    let mut pencils_of_b: Vec<Vec<usize>> = vec![Vec::new(); nb];
    for &pi in &pencil_ids {
        for mm in &fl[pi].members {
            pencils_of_b[mm.0].push(pi);
        }
    }
    while order.len() < nb {
        let best = (0..nb)
            .filter(|&b| !in_order[b])
            .max_by_key(|&b| {
                let sc: usize = pencils_of_b[b]
                    .iter()
                    .map(|&pi| {
                        let a = fl[pi].members.iter().filter(|mm| in_order[mm.0]).count();
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
        f.done_at = f.members.iter().map(|mm| pos_of[mm.0]).max().unwrap();
        complete_at[f.done_at].push(i);
    }
    let mut pencils_of: Vec<Vec<(usize, usize)>> = vec![Vec::new(); nb];
    let mut interp: Vec<Vec<(Vec<usize>, Vec<Option<Vec<u64>>>)>> = vec![Vec::new(); fl.len()];
    for &pi in &pencil_ids {
        let f = &fl[pi];
        for (mi, mm) in f.members.iter().enumerate() {
            pencils_of[mm.0].push((pi, mi));
        }
        let mut by_pos: Vec<usize> = (0..f.members.len()).collect();
        by_pos.sort_by_key(|&mi| pos_of[f.members[mi].0]);
        let mono = |n: usize, a: usize, c: &[u64]| -> u64 { pw(c[0], n - a, pp) * pw(c[1], a, pp) % pp };
        let mut tab = vec![(Vec::new(), Vec::new())];
        for n in 1..=p - 2 {
            let info: Vec<usize> = by_pos[..n + 1].to_vec();
            let mat: Vec<Vec<u64>> = info.iter().map(|&mi| (0..=n).map(|a| mono(n, a, &f.members[mi].1)).collect()).collect();
            let minv = mat_inv(&mat, pp).expect("info set singular");
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
    let mut st = Search {
        p,
        pp,
        r,
        m,
        k: inst.k as i64,
        lam: inst.lam,
        v: inst.v,
        vecs: &vecs,
        keys: &keys,
        kclass,
        kvec,
        rep_full,
        rep_t,
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
        "{head} c={cq} s={} V={} kclasses={} reps={} vnodes={vnodes} nodes={} rejects={:?} leaves={} integral={} valid={} miss={} {verdict} {:.2}s",
        dem.sum,
        vecs.len(),
        classes.len(),
        st.rep_full.iter().filter(|&&b| b).count(),
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
        eprintln!("usage: x_tomo_flatk <instances.csv> <ids file: id p r m> <threads> <max_vec_nodes> <max_nodes> <out> [all] [vcheck]");
        std::process::exit(2);
    }
    let insts = read(&a[1]);
    let threads: usize = a[3].parse().unwrap();
    let flag = |f: &str| a[7..].iter().any(|x| x == f);
    let o = Arc::new(Opts {
        max_vec_nodes: a[4].parse::<f64>().unwrap() as u64,
        max_nodes: a[5].parse::<f64>().unwrap() as u64,
        all: flag("all"),
        vcheck: flag("vcheck"),
    });
    let mut todo: Vec<(usize, usize, usize, usize)> = Vec::new();
    for l in std::fs::read_to_string(&a[2]).unwrap().lines() {
        let f: Vec<usize> = l.split_whitespace().skip(1).filter_map(|x| x.parse().ok()).collect();
        let Some(id) = l.split_whitespace().next() else { continue };
        let Some(ix) = insts.iter().position(|i| i.id == id) else { continue };
        if f.len() >= 3 {
            todo.push((ix, f[0], f[1], f[2]));
        }
    }
    let insts = Arc::new(insts);
    let queue = Arc::new(Mutex::new(todo.into_iter().rev().collect::<Vec<_>>()));
    let out = Arc::new(Mutex::new(std::fs::OpenOptions::new().create(true).append(true).open(&a[6]).unwrap()));
    let hs: Vec<_> = (0..threads)
        .map(|_| {
            let (queue, out, o, insts) = (queue.clone(), out.clone(), o.clone(), insts.clone());
            std::thread::spawn(move || loop {
                let Some((ix, p, r, m)) = queue.lock().unwrap().pop() else { break };
                let line = run(&insts[ix], p, r, m, &o);
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
