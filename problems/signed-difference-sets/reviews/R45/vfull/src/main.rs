//! Refuter (C40): every Y in Z^p with |Y_i| <= p, sum s, sum of squares Q = k + lam (p - 1),
//! every cyclic shift autocorrelation lam p, sum |Y| <= k, k - sum |Y| even. Plain DFS over
//! all coordinates (no translation normalisation), sum and Cauchy-Schwarz pruning only.
//! Usage: vfull p k lam s  -> prints each vector, then the count.
use std::env;

struct Ctx { p: usize, k: i64, lam: i64, s: i64, q: i64, y: Vec<i64>, out: Vec<Vec<i64>>, nodes: u64 }

fn leaf(c: &Ctx) -> bool {
    let p = c.p;
    let a: i64 = c.y.iter().map(|v| v.abs()).sum();
    if a > c.k || (c.k - a) % 2 != 0 { return false; }
    for g in 1..p {
        let mut t = 0;
        for x in 0..p { t += c.y[x] * c.y[(x + g) % p]; }
        if t != c.lam * p as i64 { return false; }
    }
    true
}

fn dfs(c: &mut Ctx, i: usize, sum: i64, sq: i64) {
    c.nodes += 1;
    let rem = (c.p - i) as i64;
    let r = c.q - sq;
    let d = c.s - sum;
    if r < 0 || d * d > rem * r || d.abs() > rem * c.p as i64 { return; }
    if rem == 0 {
        if d == 0 && r == 0 && leaf(c) { c.out.push(c.y.clone()); }
        return;
    }
    let lim = (c.p as i64).min((r as f64).sqrt() as i64 + 1);
    for x in -lim..=lim {
        if x * x > r { continue; }
        c.y[i] = x;
        dfs(c, i + 1, sum + x, sq + x * x);
    }
    c.y[i] = 0;
}

fn main() {
    let a: Vec<i64> = env::args().skip(1).map(|s| s.parse().unwrap()).collect();
    let (p, k, lam, s) = (a[0] as usize, a[1], a[2], a[3]);
    let q = k + lam * (p as i64 - 1);
    let mut c = Ctx { p, k, lam, s, q, y: vec![0; p], out: vec![], nodes: 0 };
    dfs(&mut c, 0, 0, 0);
    for v in &c.out { println!("{:?}", v); }
    println!("count {} nodes {}", c.out.len(), c.nodes);
}
