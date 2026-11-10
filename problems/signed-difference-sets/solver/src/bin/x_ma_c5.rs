//! Exploration (I22, C34 iterated, with C5): as x_ma_iterated, and on H' the values of Z also lie in Turyn's residue
//! class mod M = ∏ q^(j_q) over primes q ≠ p of k − λ with q ∤ |H'| and q self-conjugate mod exp H' (Z ≡ s/(p^l |H'|) mod M).
//! Original note: on a Ma quotient H = ZMod(p^j) × K (p^b ∣ k − λ, b ≥ 1, p^i = −1 on K), Ma's step at
//! every level ZMod(p^t) × K makes the coset sums on ZMod(p^(j−l)) × K divisible by p^l for l ≤ b. Search Z = W/p^l there
//! (fibres p^l c): |Z| ≤ c, ΣZ² = (k + λ(p^l c − 1))/p^(2l), autocorrelation λc/p^l, ΣZ = s/p^l, Σ|Z| ≤ k/p^l (≡ k mod 2
//! for odd p). l = 1 is x_ma_divided.
//! Usage: `x_ma_c5 <instances.csv> <max_nodes> <threads> <out> [<id file>]`: validates on every `exists` row first
//! (none may be killed), then runs the id file's rows or every open one. Line: id key v `KILL p j H' nodes|arith` | `open …`.

use signed_difference_sets::contraction::Demand;
use signed_difference_sets::instances::{read, Instance};
use signed_difference_sets::Group;
use std::collections::HashSet;
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
    if b == 0 { a } else { gcd(b, a % b) }
}

/// p^i ≡ −1 (mod m) for some i ≥ 1 (m = 1 always).
fn self_conjugate(p: i64, m: i64) -> bool {
    if m == 1 {
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

fn divisors(n: i64) -> Vec<i64> {
    (1..=n).filter(|d| n % d == 0).collect()
}

/// Every divisor tuple d (dₜ ∣ oₜ).
fn tuples(o: &[i64]) -> Vec<Vec<i64>> {
    let mut out = vec![vec![]];
    for &x in o {
        out = out.into_iter().flat_map(|t| divisors(x).into_iter().map(move |d| [t.clone(), vec![d]].concat())).collect();
    }
    out
}

fn inverse(a: i64, m: i64) -> Option<i64> {
    let a = a.rem_euclid(m);
    (1..m.max(2)).find(|&x| (a * x) % m == 1 % m)
}

/// E5's search (as `contraction::search`) with every value ≡ `res` (mod `modulus`).
struct St<'a> {
    h: &'a Group,
    k: i64,
    dem: &'a Demand,
    modulus: i64,
    res: i64,
    a: Vec<i64>,
    nodes: u64,
    max_nodes: u64,
    found: bool,
}

impl St<'_> {
    fn go(&mut self, i: usize, sum: i64, sq: i64, abs: i64, top: i64) -> bool {
        self.nodes += 1;
        if self.nodes > self.max_nodes {
            return true;
        }
        let n = self.h.order;
        let (c, square, s) = (self.dem.c, self.dem.square, self.dem.sum);
        if i == n {
            if sum != s || sq != square || abs > self.k || (self.k - abs) % 2 != 0 {
                return false;
            }
            let ok = (1..n).all(|g| (0..n).map(|x| self.a[x] * self.a[self.h.add[x][g]]).sum::<i64>() == self.dem.target);
            if ok {
                self.found = true;
            }
            return ok;
        }
        let rem = (n - i) as i64;
        let left_sq = square - sq;
        let left_sum = s - sum;
        if left_sq < 0 || left_sum * left_sum > rem * left_sq || left_sum.abs() > rem * c {
            return false;
        }
        let lim = if i == 0 { c } else { top };
        for x in -lim..=lim {
            if x * x > left_sq || (x - self.res).rem_euclid(self.modulus) != 0 {
                continue;
            }
            self.a[i] = x;
            let t = if i == 0 { x.abs() } else { top };
            if self.go(i + 1, sum + x, sq + x * x, abs + x.abs(), t) {
                return true;
            }
        }
        self.a[i] = 0;
        false
    }
}

/// Search with the largest |value| first (translation), sum +s (negation is the residue −a with sum −s: both run).
fn search(h: &Group, k: usize, dem: &Demand, modulus: i64, res: i64, max_nodes: u64) -> (bool, bool, u64) {
    let mut total = 0;
    let mut cut = false;
    for (sum, r) in [(dem.sum, res), (-dem.sum, -res)] {
        let d = Demand { c: dem.c, square: dem.square, target: dem.target, sum };
        let mut st = St { h, k: k as i64, dem: &d, modulus, res: r, a: vec![0; h.order], nodes: 0, max_nodes, found: false };
        st.go(0, 0, 0, 0, 0);
        total += st.nodes;
        cut |= st.nodes > max_nodes;
        if st.found {
            return (true, cut, total);
        }
    }
    (false, cut, total)
}

fn run(inst: &Instance, max_nodes: u64) -> (bool, String) {
    let (v, k, lam) = (inst.v as i64, inst.k as i64, inst.lam);
    let n = k - lam;
    let total = k + lam * (v - 1);
    let s = (total as f64).sqrt().round() as i64;
    if n <= 0 || s * s != total {
        return (false, "skip".into());
    }
    let ms: Vec<i64> = inst.shape.iter().map(|&m| m as i64).collect();
    let mut notes = Vec::new();
    let mut seen = HashSet::new();
    for p in primes_of(n) {
        if vp(n, p) / 2 == 0 {
            continue;
        }
        let odd: Vec<i64> = ms.iter().map(|&m| m / p.pow(vp(m, p))).collect();
        for (si, &m) in ms.iter().enumerate() {
            for j in 1..=vp(m, p) {
                for d in tuples(&odd) {
                    let l = d.iter().fold(1, |a, &x| a / gcd(a, x) * x);
                    if !self_conjugate(p, l) {
                        continue;
                    }
                    let b = vp(n, p) / 2;
                    let c = v / (p.pow(j) * d.iter().product::<i64>());
                    for lv in 1..=b.min(j) {
                        let mut e = d.clone();
                        e[si] *= p.pow(j - lv);
                        if !seen.insert((p, lv, e.clone())) {
                            continue;
                        }
                        let (pl, num) = (p.pow(lv), k + lam * (p.pow(lv) * c - 1));
                        let name = format!("{e:?}").replace(' ', "");
                        if num % (pl * pl) != 0 || (lam * c) % pl != 0 || s % pl != 0 {
                            return (true, format!("KILL {p} {j} {lv} {name} arith"));
                        }
                        let dem = Demand { c, square: num / (pl * pl), target: lam * c / pl, sum: s / pl };
                        let group = Group::new(&e.iter().map(|&x| x as usize).collect::<Vec<_>>());
                        let bounds: Vec<i64> = if p == 2 { vec![k / pl, k / pl - 1] } else {
                            let kk = k / pl;
                            vec![if (kk - k) % 2 == 0 { kk } else { kk - 1 }]
                        };
                        let h1: i64 = e.iter().product();
                        let expo = e.iter().fold(1i64, |a, &x| a / gcd(a, x) * x);
                        let mut modulus = 1i64;
                        for q in primes_of(n) {
                            let jq = vp(n, q) / 2;
                            if q != p && jq > 0 && h1 % q != 0 && self_conjugate(q, expo) {
                                modulus *= q.pow(jq);
                            }
                        }
                        let res = if modulus > 1 {
                            match inverse(pl * h1, modulus) { Some(inv) => (s * inv).rem_euclid(modulus), None => 0 }
                        } else { 0 };
                        let (mut found, mut cut, mut nodes) = (false, false, 0);
                        for kk in bounds.into_iter().filter(|&x| x >= 0) {
                            let (f, c2, nd) = search(&group, kk as usize, &dem, modulus, res, max_nodes);
                            nodes += nd;
                            cut |= c2;
                            found |= f;
                        }
                        if found {
                            notes.push(format!("{p}:{lv}:{name}:found"));
                        } else if cut {
                            notes.push(format!("{p}:{lv}:{name}:cut"));
                        } else {
                            return (true, format!("KILL {p} {j} {lv} {name} {nodes}"));
                        }
                    }
                }
            }
        }
    }
    (false, format!("open {}", notes.join(" ")))
}

fn parallel(todo: Vec<Instance>, threads: usize, max_nodes: u64, out: Option<&str>) -> Vec<String> {
    let queue = Arc::new(Mutex::new(todo.into_iter().rev().collect::<Vec<_>>()));
    let kills = Arc::new(Mutex::new(Vec::new()));
    let file = out.map(|p| {
        Arc::new(Mutex::new(std::fs::OpenOptions::new().create(true).append(true).open(p).unwrap()))
    });
    let workers: Vec<_> = (0..threads)
        .map(|_| {
            let (queue, kills, file) = (Arc::clone(&queue), Arc::clone(&kills), file.clone());
            std::thread::spawn(move || loop {
                let next = queue.lock().unwrap().pop();
                let Some(inst) = next else { break };
                let (killed, text) = run(&inst, max_nodes);
                let line = format!("{} {} {} {text}", inst.id, inst.key, inst.v);
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
    let max_nodes: u64 = args[1].parse().unwrap();
    let threads: usize = args[2].parse().unwrap();
    let out = &args[3];
    let all = read(&args[0]);
    let t = std::time::Instant::now();
    let exists: Vec<Instance> = read(&args[0]).into_iter().filter(|i| i.status == "exists").collect();
    let n_exists = exists.len();
    let wrong = parallel(exists, threads, max_nodes, None);
    assert!(wrong.is_empty(), "kills an Instance that exists: {wrong:?}");
    eprintln!("validation passed: {n_exists} existing Instances survive ({:.1?})", t.elapsed());
    let wanted: Option<HashSet<String>> = args
        .get(4)
        .map(|p| std::fs::read_to_string(p).unwrap().lines().map(|l| l.trim().to_string()).collect());
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
    parallel(todo, threads, max_nodes, Some(out));
    eprintln!("pass done in {:.1?}", t.elapsed());
}
