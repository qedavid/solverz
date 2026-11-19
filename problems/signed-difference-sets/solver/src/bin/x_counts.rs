//! Exploration (C7 with integer counts over every quotient): for each quotient H of G (fibres c = v/|H|) the coset sums
//! take values in [−c, c] (in Turyn's residue class a = s/|H| mod M when C5's modulus M > 1); their counts must meet
//! |H| values, sum ±s, square sum k + λ(c − 1), absolute sum ≤ k with k − Σ|x| even (C4), and room for the k nonzero
//! elements: Σ maxMarked(x) ≥ k with maxMarked(x) = c or c − 1 (same parity as x) (C7). No counts: no SDS.
//! Usage: `x_counts <instances.csv> <threads> <out>`: validates on every `exists` row first. Line: id key v `KILL H M` | `open`.

use signed_difference_sets::contraction::quotients;
use signed_difference_sets::instances::{read, Instance};
use std::io::Write;
use std::sync::{Arc, Mutex};

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

fn gcd(a: i64, b: i64) -> i64 {
    if b == 0 { a.abs() } else { gcd(b, a % b) }
}

fn self_conjugate(q: i64, m: i64) -> bool {
    if m == 1 {
        return true;
    }
    let mut x = q % m;
    for _ in 0..m {
        if (x + 1) % m == 0 {
            return true;
        }
        x = x * q % m;
    }
    false
}

fn inverse(a: i64, m: i64) -> Option<i64> {
    let a = a.rem_euclid(m);
    (1..m.max(2)).find(|&x| (a * x) % m == 1 % m)
}

/// Counts m_a of each absolute value a ∈ allowed (with signs) meeting the moments; `marked(a)` per value.
struct Ctx {
    c: i64,
    n: i64,
    q: i64,
    s: i64,
    k: i64,
    vals: Vec<i64>, // allowed absolute values a ≥ 1, descending; 0 allowed iff zero_ok
    zero_ok: bool,
    signs_ok: Vec<(bool, bool)>, // for each a: +a allowed, −a allowed
}

impl Ctx {
    fn marked(&self, a: i64) -> i64 {
        if (self.c - a) % 2 == 0 { self.c } else { self.c - 1 }
    }
    fn rec(&self, i: usize, n: i64, q: i64, abs: i64, mk: i64, ms: &mut Vec<(usize, i64)>) -> bool {
        if i == self.vals.len() {
            if q != 0 || n < 0 || (!self.zero_ok && n != 0) {
                return false;
            }
            let mk = mk + n * self.marked(0);
            if abs > self.k || (self.k - abs) % 2 != 0 || mk < self.k {
                return false;
            }
            // signs: reachable sums
            let mut reach: std::collections::HashSet<i64> = [0].into_iter().collect();
            for &(j, m) in ms.iter() {
                let a = self.vals[j];
                let (pos, neg) = self.signs_ok[j];
                let mut next = std::collections::HashSet::new();
                for &x in &reach {
                    for plus in 0..=m {
                        let minus = m - plus;
                        if (plus > 0 && !pos) || (minus > 0 && !neg) {
                            continue;
                        }
                        next.insert(x + a * (plus - minus));
                    }
                }
                reach = next;
            }
            return reach.contains(&self.s) || reach.contains(&-self.s);
        }
        let a = self.vals[i];
        let mut m = 0;
        while m * a * a <= q && m <= n {
            if m > 0 {
                ms.push((i, m));
            }
            let ok = self.rec(i + 1, n - m, q - m * a * a, abs + m * a, mk + m * self.marked(a), ms);
            if m > 0 {
                ms.pop();
            }
            if ok {
                return true;
            }
            m += 1;
        }
        false
    }
}

fn feasible(c: i64, n: i64, q: i64, s: i64, k: i64, modulus: i64, res: i64) -> bool {
    // values x in [−c, c] with x ≡ res (mod modulus), or x ≡ −res for the negated vector (sum −s): try both
    for (r, ss) in [(res, s), ((-res).rem_euclid(modulus.max(1)), -s)] {
        let ok_val = |x: i64| modulus <= 1 || (x - r).rem_euclid(modulus) == 0;
        let mut vals = Vec::new();
        let mut signs = Vec::new();
        for a in (1..=c).rev() {
            let (p, m) = (ok_val(a), ok_val(-a));
            if p || m {
                vals.push(a);
                signs.push((p, m));
            }
        }
        let ctx = Ctx { c, n, q, s: ss, k, vals, zero_ok: ok_val(0), signs_ok: signs };
        // only sum ss (not −ss) is meaningful once the residue fixes the sign
        let ctx2 = Ctx { s: ss, ..ctx };
        if ctx2.rec(0, n, q, 0, 0, &mut Vec::new()) {
            return true;
        }
    }
    false
}

fn run(inst: &Instance) -> (bool, String) {
    let (v, k, lam) = (inst.v as i64, inst.k as i64, inst.lam);
    let n = k - lam;
    let total = k + lam * (v - 1);
    let s = (total as f64).sqrt().round() as i64;
    if n <= 0 || s * s != total {
        return (false, "skip".into());
    }
    for quo in quotients(&inst.shape) {
        let h = quo.divisors.iter().product::<usize>() as i64;
        if h <= 1 || v % h != 0 {
            continue;
        }
        let c = v / h;
        let q = k + lam * (c - 1);
        let expo = quo.invariants.iter().fold(1i64, |a, &x| a / gcd(a, x as i64) * x as i64);
        let mut modulus = 1i64;
        for p in primes_of(n) {
            let j = vp(n, p) / 2;
            if j > 0 && h % p != 0 && self_conjugate(p, expo) {
                modulus *= p.pow(j);
            }
        }
        let res = if modulus > 1 { inverse(h, modulus).map(|i| (s * i).rem_euclid(modulus)).unwrap_or(0) } else { 0 };
        if !feasible(c, h, q, s, k, modulus, res) {
            let name = format!("{:?}", quo.invariants).replace(' ', "");
            return (true, format!("KILL {name} {modulus}"));
        }
    }
    (false, "open".into())
}

fn parallel(todo: Vec<Instance>, threads: usize, out: Option<&str>) -> Vec<String> {
    let queue = Arc::new(Mutex::new(todo.into_iter().rev().collect::<Vec<_>>()));
    let kills = Arc::new(Mutex::new(Vec::new()));
    let file = out.map(|p| Arc::new(Mutex::new(std::fs::File::create(p).unwrap())));
    let workers: Vec<_> = (0..threads)
        .map(|_| {
            let (queue, kills, file) = (Arc::clone(&queue), Arc::clone(&kills), file.clone());
            std::thread::spawn(move || loop {
                let next = queue.lock().unwrap().pop();
                let Some(inst) = next else { break };
                let (killed, text) = run(&inst);
                let line = format!("{} {} {} {text}", inst.id, inst.key, inst.v);
                if let Some(f) = &file {
                    let mut f = f.lock().unwrap();
                    writeln!(f, "{line}").unwrap();
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
    let threads: usize = args[1].parse().unwrap();
    let t = std::time::Instant::now();
    let exists: Vec<Instance> = read(&args[0]).into_iter().filter(|i| i.status == "exists").collect();
    let n_exists = exists.len();
    let wrong = parallel(exists, threads, None);
    assert!(wrong.is_empty(), "kills an Instance that exists: {wrong:?}");
    eprintln!("validation passed: {n_exists} existing Instances survive ({:.1?})", t.elapsed());
    let todo: Vec<Instance> = read(&args[0]).into_iter().filter(|i| i.status == "open").collect();
    let t = std::time::Instant::now();
    let kills = parallel(todo, threads, Some(&args[2]));
    eprintln!("{} kills in {:.1?}", kills.len(), t.elapsed());
}
