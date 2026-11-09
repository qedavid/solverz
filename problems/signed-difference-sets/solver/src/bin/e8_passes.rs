//! E8 (exploration): E5's contraction search over every open Instance, one pass per node cap.
//! Usage: `e8_passes <instances.csv> <max_nodes> <threads> <out> [<id file>]`: Instances in
//! the id file (one id per line) or every open one; ids already in <out> are skipped, each
//! result is appended to <out> as it comes. Line: id key v `KILL d H nodes` | `open …`
//! (quotients `found`/`cut`). Validates first: no existing Instance is killed, N32 dies at C5.

use signed_difference_sets::contraction::{quotients, search, Demand};
use signed_difference_sets::instances::{read, Instance};
use signed_difference_sets::Group;
use std::collections::HashSet;
use std::io::Write;
use std::sync::{Arc, Mutex};

fn run(inst: &Instance, max_nodes: u64) -> (bool, String) {
    let mut notes = Vec::new();
    for quo in quotients(&inst.shape) {
        let group = Group::new(&quo.divisors);
        let dem = Demand::new(inst.v, inst.k, inst.lam, group.order).expect("F1 holds");
        let out = search(&group, inst.k, &dem, max_nodes);
        let name = format!("{:?}", quo.invariants).replace(' ', "");
        let divisors = format!("{:?}", quo.divisors).replace(' ', "");
        if out.cut {
            notes.push(format!("{name}:cut"));
        } else if out.found.is_none() {
            return (true, format!("KILL {divisors} {name} {}", out.nodes));
        } else {
            notes.push(format!("{name}:found"));
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
    assert!(wrong.is_empty(), "contraction kills an Instance that exists: {wrong:?}");
    let n32 = all.iter().find(|i| i.id == "N32").unwrap();
    assert!(run(n32, max_nodes).1.starts_with("KILL [1,5] [5]"), "N32 not killed at C5");
    eprintln!("validation passed: {n_exists} existing Instances survive, N32 dies at C5 ({:.1?})", t.elapsed());
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
