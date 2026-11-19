// C37(a) on small groups G = C2 x K: every SDS (D(0) = +1 wlog) with 4 | k - lam is checked for
// parity D(0,y) = D(1,y) mod 2, Z = (D0+D1)/2 SDS ((k+lam)/4, lam/2), T = (D0-D1)/2 SDS ((k-lam)/4, 0),
// disjoint supports. Groups given as cyclic dims, with the split map to (u, y in K).
fn main() {
    // (name, dims of G, |K|, split: element index -> (u, y))
    let groups: Vec<(&str, Vec<usize>)> = vec![
        ("C6", vec![6]), ("C10", vec![10]), ("C14 (control: 2 not self-conj mod 7)", vec![14]),
        ("C18", vec![18]), ("C2xC3xC3", vec![2, 3, 3]), ("C3xC6", vec![3, 6]),
    ];
    for (name, dims) in groups {
        let n: usize = dims.iter().product();
        let dec = |mut i: usize| -> Vec<usize> { let mut v = vec![0; dims.len()];
            for j in (0..dims.len()).rev() { v[j] = i % dims[j]; i /= dims[j]; } v };
        let enc = |v: &[usize]| -> usize { let mut i = 0; for j in 0..dims.len() { i = i * dims[j] + v[j]; } i };
        let mut add = vec![vec![0usize; n]; n];
        for x in 0..n { for y in 0..n { let (a, b) = (dec(x), dec(y));
            let s: Vec<usize> = (0..dims.len()).map(|j| (a[j] + b[j]) % dims[j]).collect(); add[x][y] = enc(&s); } }
        // split: G -> (u, y). For one cyclic factor C_{2m}: u = b mod 2, y = b mod m.
        // For [2,3,3]: u = a, y = (b, c). For [3,6]: u = b mod 2, y = (a, b mod 3).
        let m = n / 2;
        let split = |x: usize| -> (usize, usize) { let v = dec(x);
            if dims.len() == 1 { (v[0] % 2, v[0] % m) }
            else if dims[0] == 2 { (v[0], v[1] * 3 + v[2]) }
            else { (v[1] % 2, v[0] * 3 + v[1] % 3) } };
        // K's addition via the split (check it is a bijection)
        let mut inv = vec![usize::MAX; n];
        for x in 0..n { let (u, y) = split(x); assert!(inv[u * m + y] == usize::MAX); inv[u * m + y] = x; }
        let kadd = |y1: usize, y2: usize| -> usize { let x = add[inv[y1]][inv[y2]]; split(x).1 };
        let mut f = vec![0i32; n]; f[0] = 1;
        let mut digits = vec![0u8; n]; // positions 1..n
        let (mut total, mut four, mut bad) = (0u64, 0u64, 0u64);
        let mut seen = std::collections::BTreeMap::new();
        loop {
            // odometer over positions 1..n with values 0, 1, -1
            let mut i = 1;
            while i < n { digits[i] += 1; if digits[i] == 3 { digits[i] = 0; f[i] = 0; i += 1; } else { f[i] = if digits[i] == 1 { 1 } else { -1 }; break; } }
            if i == n { break; }
            let c = |g: usize, f: &[i32]| -> i32 { let mut s = 0; for x in 0..n { s += f[x] * f[add[x][g]]; } s };
            let lam = c(1, &f);
            let mut ok = true;
            for g in 2..n { if c(g, &f) != lam { ok = false; break; } }
            if !ok { continue; }
            total += 1;
            let k = f.iter().filter(|&&v| v != 0).count() as i32;
            *seen.entry((k, lam)).or_insert(0u64) += 1;
            if (k - lam) % 4 != 0 { continue; }
            four += 1;
            let mut d0 = vec![0i32; m]; let mut d1 = vec![0i32; m];
            for x in 0..n { let (u, y) = split(x); if u == 0 { d0[y] = f[x] } else { d1[y] = f[x] } }
            let par = (0..m).all(|y| (d0[y] - d1[y]) % 2 == 0);
            let mut good = par && lam % 2 == 0;
            if good {
                let z: Vec<i32> = (0..m).map(|y| (d0[y] + d1[y]) / 2).collect();
                let t: Vec<i32> = (0..m).map(|y| (d0[y] - d1[y]) / 2).collect();
                let kc = |h: &[i32], g: usize| -> i32 { (0..m).map(|y| h[y] * h[kadd(y, g)]).sum() };
                let wz = z.iter().filter(|&&v| v != 0).count() as i32;
                let wt = t.iter().filter(|&&v| v != 0).count() as i32;
                good = 4 * wz == k + lam && 4 * wt == k - lam
                    && (1..m).all(|g| 2 * kc(&z, g) == lam && kc(&t, g) == 0)
                    && (0..m).all(|y| z[y] == 0 || t[y] == 0);
            }
            if !good { bad += 1; if bad <= 3 { println!("  {}: FAILS halving: k={} lam={} D={:?}", name, k, lam, f); } }
        }
        println!("{}: SDS with D(0)=+1: {}, params {:?}; with 4 | k-lam: {}, halving fails: {}", name, total, seen, four, bad);
    }
}
