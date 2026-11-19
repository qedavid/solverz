// Independent check of C37 (refuter). Own indexing, no covers, no slices.
// K = Z3 x Z9, index i = 9a + b. Z: support-first (0 in S, Z(0) = -1), parity filter, then signs.
// T: every signed weight-tw function on Z's zeros (no normalisation of T).
use std::time::Instant;

struct Grp { n: usize, add: Vec<Vec<usize>>, neg: Vec<usize> }

fn grp(dims: &[usize]) -> Grp {
    let n: usize = dims.iter().product();
    let dec = |mut i: usize| -> Vec<usize> {
        let mut v = vec![0; dims.len()];
        for j in (0..dims.len()).rev() { v[j] = i % dims[j]; i /= dims[j]; }
        v
    };
    let enc = |v: &[usize]| -> usize { let mut i = 0; for j in 0..dims.len() { i = i * dims[j] + v[j]; } i };
    let mut add = vec![vec![0; n]; n];
    let mut neg = vec![0; n];
    for x in 0..n { for y in 0..n {
        let (a, b) = (dec(x), dec(y));
        let s: Vec<usize> = (0..dims.len()).map(|j| (a[j] + b[j]) % dims[j]).collect();
        add[x][y] = enc(&s);
    }
        let a = dec(x);
        let s: Vec<usize> = (0..dims.len()).map(|j| (dims[j] - a[j]) % dims[j]).collect();
        neg[x] = enc(&s);
    }
    Grp { n, add, neg }
}

// corr(g) = sum_x f(x) f(x+g)
fn corr(g: &Grp, f: &[i32], s: usize) -> i32 { (0..g.n).map(|x| f[x] * f[g.add[x][s]]).sum() }

// Some((k, lam)) if f is an SDS
fn is_sds(g: &Grp, f: &[i32]) -> Option<(usize, i32)> {
    let k = f.iter().filter(|&&v| v != 0).count();
    let lam = corr(g, f, 1);
    for s in 1..g.n { if corr(g, f, s) != lam { return None; } }
    Some((k, lam))
}

// {y : y + s in mask}
fn sh(g: &Grp, mask: u64, s: usize) -> u64 {
    let mut r = 0u64; let mut m = mask;
    while m != 0 { let x = m.trailing_zeros() as usize; m &= m - 1; r |= 1u64 << g.add[x][g.neg[s]]; }
    r
}

fn next_comb(v: u64) -> u64 { let t = v | (v - 1); (t + 1) | (((!t & (t + 1)) - 1) >> (v.trailing_zeros() + 1)) }

// All Z: K -> {-1,0,1}, |supp| = kz, corr = lz off 0, sum = sz > 0, Z(0) = -1.
fn all_z(g: &Grp, kz: usize, lz: i32, sz: i32) -> Vec<Vec<i32>> {
    let n = g.n; let m = ((kz as i32 - sz) / 2) as usize; assert!(m >= 1);
    let mut out = vec![];
    let r = kz - 1; // other support elements among 1..n
    let mut c: u64 = (1u64 << r) - 1;
    let lim = 1u64 << (n - 1);
    let mut cnt_par = 0u64;
    while c < lim {
        let s = (c << 1) | 1;
        let mut ok = true;
        for t in 1..n { if (((s & sh(g, s, t)).count_ones() as i32 - lz) & 1) != 0 { ok = false; break; } }
        if ok {
            cnt_par += 1;
            // choose m-1 further minus among the r other support elements
            let elems: Vec<usize> = (1..n).filter(|&x| (s >> x) & 1 == 1).collect();
            let mut sel: u64 = if m == 1 { 0 } else { (1u64 << (m - 1)) - 1 };
            loop {
                let mut f = vec![0i32; n];
                for &x in &elems { f[x] = 1; }
                f[0] = -1;
                for (j, &x) in elems.iter().enumerate() { if (sel >> j) & 1 == 1 { f[x] = -1; } }
                let mut good = true;
                for t in 1..n { if corr(g, &f, t) != lz { good = false; break; } }
                if good { out.push(f); }
                if m == 1 { break; }
                sel = next_comb(sel);
                if sel >= (1u64 << r) { break; }
            }
        }
        c = next_comb(c);
    }
    eprintln!("  supports passing parity: {}", cnt_par);
    out
}

// All T on the zeros of z with weight tw and corr 0 off 0 (both signs, no normalisation).
fn all_t(g: &Grp, z: &[i32], tw: usize) -> Vec<Vec<i32>> {
    let n = g.n;
    let rz: Vec<usize> = (0..n).filter(|&x| z[x] == 0).collect();
    let mut out = vec![];
    if rz.len() < tw { return out; }
    let mut c: u64 = (1u64 << tw) - 1;
    while c < (1u64 << rz.len()) {
        let mut s = 0u64;
        for (j, &x) in rz.iter().enumerate() { if (c >> j) & 1 == 1 { s |= 1u64 << x; } }
        let mut ok = true;
        for t in 1..n { if (s & sh(g, s, t)).count_ones() & 1 != 0 { ok = false; break; } }
        if ok {
            let el: Vec<usize> = (0..n).filter(|&x| (s >> x) & 1 == 1).collect();
            for sg in 0u64..(1u64 << tw) {
                let mut f = vec![0i32; n];
                for (j, &x) in el.iter().enumerate() { f[x] = if (sg >> j) & 1 == 1 { -1 } else { 1 }; }
                let mut good = true;
                for t in 1..n { if corr(g, &f, t) != 0 { good = false; break; } }
                if good { out.push(f); }
            }
        }
        c = next_comb(c);
    }
    out
}

// D on Z3 x Z18 from (Z, T) on K: (a, b) -> u = b mod 2, y = (a, b mod 9).
fn double(z: &[i32], t: &[i32]) -> Vec<i32> {
    let mut d = vec![0i32; 54];
    for a in 0..3 { for b in 0..18 {
        let y = 9 * a + b % 9;
        d[18 * a + b] = if b % 2 == 0 { z[y] + t[y] } else { z[y] - t[y] };
    } }
    d
}

fn run_row(name: &str, kz: usize, lz: i32, sz: i32, tw: usize, k: usize, lam: i32) {
    let kk = grp(&[3, 9]);
    let g54 = grp(&[3, 18]);
    let t0 = Instant::now();
    let zs = all_z(&kk, kz, lz, sz);
    eprintln!("{}: {} normalised Z (27,{},{}) with Z(0)=-1, sum {} [{:.1}s]", name, zs.len(), kz, lz, sz, t0.elapsed().as_secs_f64());
    { use std::io::Write; let mut fh = std::fs::File::create(format!("zs{}.txt", name)).unwrap();
      for z in &zs { writeln!(fh, "{}", z.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(" ")).unwrap(); } }
    let mut pairs = 0usize; let mut zwith = 0usize; let mut bad_d = 0usize;
    for z in &zs {
        let ts = all_t(&kk, z, tw);
        if !ts.is_empty() { zwith += 1; }
        for t in &ts {
            pairs += 1;
            let d = double(z, t);
            match is_sds(&g54, &d) { Some((k2, l2)) if k2 == k && l2 == lam => {}, _ => bad_d += 1 }
            if pairs == 1 { eprintln!("  first pair: Z={:?}\n              T={:?}", z, t); }
        }
    }
    eprintln!("{}: pairs (Z normalised, T any) = {}, Z with some T = {}, doubled D failing SDS({},{},{}) = {} [{:.1}s]",
        name, pairs, zwith, 54, k, lam, bad_d, t0.elapsed().as_secs_f64());
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let what = if args.len() > 1 { args[1].as_str() } else { "both" };
    if what == "n464" || what == "both" { run_row("N464", 14, 5, 12, 9, 46, 10); }
    if what == "n449" || what == "both" { run_row("N449", 10, 1, 6, 9, 38, 2); }
    if what == "tall" {
        // every T on K with weight 9, sum 3, corr 0 off 0 (no translation normalisation)
        use std::io::Write;
        let kk = grp(&[3, 9]);
        let mut fh = std::fs::File::create("tall.txt").unwrap();
        let mut c: u64 = (1u64 << 9) - 1; let mut cnt = 0usize;
        while c < (1u64 << 27) {
            let mut ok = true;
            for t in 1..27 { if (c & sh(&kk, c, t)).count_ones() & 1 != 0 { ok = false; break; } }
            if ok {
                let el: Vec<usize> = (0..27).filter(|&x| (c >> x) & 1 == 1).collect();
                let mut sel: u64 = 7;
                while sel < 512 {
                    let mut f = vec![0i32; 27];
                    for (j, &x) in el.iter().enumerate() { f[x] = if (sel >> j) & 1 == 1 { -1 } else { 1 }; }
                    if (1..27).all(|t| corr(&kk, &f, t) == 0) { cnt += 1;
                        writeln!(fh, "{}", f.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(" ")).unwrap(); }
                    sel = next_comb(sel);
                }
            }
            c = next_comb(c);
        }
        eprintln!("T (27,9,0) with sum 3: {}", cnt);
    }
}
