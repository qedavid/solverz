//! Exploration (I22, C33's step): on a Ma quotient H = ZMod(p^j) × K (p^b ∣ k − λ, b ≥ 1, p^i = −1 on K) the coset sums
//! W on H' = H/P = ZMod(p^(j−1)) × K are all divisible by p. Search Z = W/p on H' (fibres p c of W): |Z| ≤ c,
//! ΣZ² = (k + λ(p c − 1))/p², autocorrelation λc/p, ΣZ = s/p, Σ|Z| ≤ k/p (≡ k mod 2 for odd p).
//! Usage: `x_ma_divided <instances.csv> <max_nodes> <threads> <out> [<id file>]`: validates on every `exists` row first
//! (none may be killed), then runs the id file's rows or every open one. Line: id key v `KILL p j H' nodes|arith` | `open …`.

use signed_difference_sets::contraction::{search, Demand};
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
                    let mut e = d.clone();
                    e[si] *= p.pow(j - 1);
                    let h1: i64 = e.iter().product();
                    if v % (p * h1) != 0 || !seen.insert((p, e.clone())) {
                        continue;
                    }
                    let c = v / (p * h1);
                    let num = k + lam * (p * c - 1);
                    let name = format!("{e:?}").replace(' ', "");
                    if num % (p * p) != 0 || (lam * c) % p != 0 || s % p != 0 {
                        return (true, format!("KILL {p} {j} {name} arith"));
                    }
                    let dem = Demand { c, square: num / (p * p), target: lam * c / p, sum: s / p };
                    let group = Group::new(&e.iter().map(|&x| x as usize).collect::<Vec<_>>());
                    let bounds: Vec<i64> = if p == 2 { vec![k / 2, k / 2 - 1] } else {
                        let kk = k / p;
                        vec![if (kk - k) % 2 == 0 { kk } else { kk - 1 }]
                    };
                    let (mut found, mut cut, mut nodes) = (false, false, 0);
                    for kk in bounds.into_iter().filter(|&x| x >= 0) {
                        let out = search(&group, kk as usize, &dem, max_nodes);
                        nodes += out.nodes;
                        cut |= out.cut;
                        found |= out.found.is_some();
                    }
                    if found {
                        notes.push(format!("{p}:{name}:found"));
                    } else if cut {
                        notes.push(format!("{p}:{name}:cut"));
                    } else {
                        return (true, format!("KILL {p} {j} {name} {nodes}"));
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
