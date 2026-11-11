//! Exploration (tomo3): the engine's exact search (`contraction::search`, E8's) on one quotient H of a row, with a large
//! node cap: an independent check of the tomography verdicts (KILL ⇒ the engine must exhaust without a vector).
//! Usage: x_quot_check <instances.csv> <file: id m1,m2,…> <threads> <max_nodes> <out>
//! Line: id key H nodes FOUND <vector> | NONE | CUT.

use signed_difference_sets::contraction::{search, Demand};
use signed_difference_sets::instances::read;
use signed_difference_sets::Group;
use std::io::Write;
use std::sync::{Arc, Mutex};

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let insts = Arc::new(read(&a[1]));
    let threads: usize = a[3].parse().unwrap();
    let max_nodes = a[4].parse::<f64>().unwrap() as u64;
    let todo: Vec<(String, Vec<usize>)> = std::fs::read_to_string(&a[2])
        .unwrap()
        .lines()
        .filter_map(|l| {
            let f: Vec<&str> = l.split_whitespace().collect();
            (f.len() == 2).then(|| (f[0].to_string(), f[1].split(',').map(|x| x.parse().unwrap()).collect()))
        })
        .collect();
    let queue = Arc::new(Mutex::new(todo.into_iter().rev().collect::<Vec<_>>()));
    let out = Arc::new(Mutex::new(std::fs::OpenOptions::new().create(true).append(true).open(&a[5]).unwrap()));
    let hs: Vec<_> = (0..threads)
        .map(|_| {
            let (queue, out, insts) = (queue.clone(), out.clone(), insts.clone());
            std::thread::spawn(move || loop {
                let Some((id, shape)) = queue.lock().unwrap().pop() else { break };
                let inst = insts.iter().find(|i| i.id == id).unwrap();
                let h = Group::new(&shape);
                let line = match Demand::new(inst.v, inst.k, inst.lam, h.order) {
                    None => format!("{id} {} {shape:?} skip", inst.key),
                    Some(dem) => {
                        let r = search(&h, inst.k, &dem, max_nodes);
                        let verdict = if r.cut {
                            "CUT".to_string()
                        } else if let Some(y) = r.found {
                            format!("FOUND {y:?}")
                        } else {
                            "NONE".to_string()
                        };
                        format!("{id} {} {shape:?} nodes={} {verdict}", inst.key, r.nodes)
                    }
                };
                println!("{line}");
                writeln!(out.lock().unwrap(), "{line}").unwrap();
            })
        })
        .collect();
    for h in hs {
        h.join().unwrap();
    }
}
