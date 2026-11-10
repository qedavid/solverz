// Independent vector search for C38's rows (own code, not derived from goRes/noVectorRes).
// Finds every Z on H' = prod Z_m with |Z| <= c, sum Z = s, sum Z^2 = Q, sum_y Z(y)Z(y+g) = t (g != 0),
// optionally all Z(y) = a (mod M) for a fixed class a. Prune: for every shift g, the completed pairs'
// sum of (Z(y) - Z(y+g))^2 never exceeds 2(Q - t) (it equals it at the end); remaining sum / square sum
// reachable (Cauchy-Schwarz and box bounds). No normalisation (translation, negation) is used.
// usage: vsearch m1,m2,.. c Q t s M cap   (M = 0: no residue class)
use std::env;
struct S { n: usize, add: Vec<usize>, vals: Vec<i64>, q: i64, t: i64, s: i64, dmax: i64,
           z: Vec<i64>, d: Vec<i64>, negt: Vec<usize>, nodes: u64, cap: u64, sols: u64, first: Option<Vec<i64>>, maxabs: i64, maxsq: i64 }
impl S {
    fn rec(&mut self, pos: usize, sum: i64, sq: i64) {
        self.nodes += 1;
        if self.nodes > self.cap { return; }
        let n = self.n;
        if pos == n {
            if sum != self.s || sq != self.q { return; }
            for g in 1..n { if self.d[g] != self.dmax { return; } }
            // full autocorrelation check, independently of the prune
            for g in 1..n {
                let mut a = 0; for y in 0..n { a += self.z[y] * self.z[self.add[y * n + g]]; }
                if a != self.t { panic!("prune/recheck mismatch"); }
            }
            self.sols += 1;
            if self.first.is_none() { self.first = Some(self.z.clone()); }
            return;
        }
        let m = (n - pos) as i64;
        let vals = self.vals.clone();
        for &x in &vals {
            let (s2, q2) = (sum + x, sq + x * x);
            let (rs, rq) = (self.s - s2, self.q - q2);
            let rm = m - 1;
            if rq < 0 { continue; }
            if rm == 0 { if rs != 0 || rq != 0 { continue; } }
            else {
                if rs.abs() > rm * self.maxabs || rq > rm * self.maxsq || rs * rs > rm * rq { continue; }
            }
            self.z[pos] = x;
            // pairs completed now: (y, y+g) with max(y, y+g) = pos, both <= pos
            let mut ok = true; let mut touched: Vec<(usize, i64)> = Vec::new();
            for g in 1..n {
                let mut inc = 0;
                let yp = self.add[pos * n + g];           // pair (pos, pos+g)
                if yp < pos { let df = x - self.z[yp]; inc += df * df; }
                // pair (y, pos) with y + g = pos, y = pos - g
                let ym = self.add[pos * n + self.neg(g)];
                if ym < pos { let df = x - self.z[ym]; inc += df * df; }
                if inc > 0 { self.d[g] += inc; touched.push((g, inc)); if self.d[g] > self.dmax { ok = false; break; } }
            }
            if ok { self.rec(pos + 1, s2, q2); }
            for (g, inc) in touched { self.d[g] -= inc; }
            if self.nodes > self.cap { return; }
        }
    }
    fn neg(&self, g: usize) -> usize { self.negt[g] }
}
fn main() {
    let a: Vec<String> = env::args().collect();
    let ms: Vec<usize> = a[1].split(',').map(|x| x.parse().unwrap()).collect();
    let c: i64 = a[2].parse().unwrap(); let q: i64 = a[3].parse().unwrap();
    let t: i64 = a[4].parse().unwrap(); let s: i64 = a[5].parse().unwrap();
    let mm: i64 = a[6].parse().unwrap(); let cap: u64 = a[7].parse().unwrap();
    let n: usize = ms.iter().product();
    // mixed radix, first factor most significant
    let dec = |mut x: usize| { let mut v = vec![0; ms.len()]; for i in (0..ms.len()).rev() { v[i] = x % ms[i]; x /= ms[i]; } v };
    let enc = |v: &Vec<usize>| { let mut x = 0; for i in 0..ms.len() { x = x * ms[i] + v[i]; } x };
    let mut add = vec![0; n * n];
    for x in 0..n { for y in 0..n { let (u, w) = (dec(x), dec(y));
        let r: Vec<usize> = (0..ms.len()).map(|i| (u[i] + w[i]) % ms[i]).collect(); add[x * n + y] = enc(&r); } }
    let classes: Vec<Option<i64>> = if mm == 0 { vec![None] } else { (0..mm).map(Some).collect() };
    let mut total_nodes = 0u64; let mut total_sols = 0u64; let mut capped = false;
    for sign in [1i64, -1] {
        for cl in &classes {
            let vals: Vec<i64> = (-c..=c).filter(|x| match cl { None => true, Some(r) => (x - r).rem_euclid(mm) == 0 }).collect();
            let maxabs = vals.iter().map(|x| x.abs()).max().unwrap_or(0);
            let mut st = S { n, add: add.clone(), vals, q, t, s: sign * s, dmax: 2 * (q - t), z: vec![0; n], d: vec![0; n], negt: (0..n).map(|g| (0..n).find(|&h| add[g * n + h] == 0).unwrap()).collect(),
                             nodes: 0, cap, sols: 0, first: None, maxabs, maxsq: maxabs * maxabs };
            st.rec(0, 0, 0);
            total_nodes += st.nodes; total_sols += st.sols; if st.nodes > cap { capped = true; }
            if let Some(f) = &st.first { println!("sol sign={} class={:?} z={:?} abs={}", sign, cl, f, f.iter().map(|x| x.abs()).sum::<i64>()); }
        }
    }
    println!("RESULT nodes={} sols={} capped={}", total_nodes, total_sols, capped);
}
