//! The thread pool. It implements `run_all` for the verified core under contract K1. See spec section 10.7.
//!
//! Contract K1 is `ParallelAll n f out`: for each job index `i < n`, `out[i] = f i`. The pool runs each job exactly once. A worker takes the next job from a shared counter, so a fast worker takes more jobs. The results go into a slot array indexed by job, so the order in which the workers finish does not change the output.
//!
//! The pool does not use `unsafe` code. It uses scoped threads of `std` and one atomic counter.

#![forbid(unsafe_code)]

use std::sync::atomic::{AtomicUsize, Ordering};

/// Runs `job(state, k)` for each job `k` in `order`, on at most `threads` threads with a stack of `stack` bytes each. Each thread makes its state once with `init`. The result has the value of job `k` at position `k`.
///
/// `order` must have each number of `0..order.len()` exactly once. The workers take the jobs in this order, so the caller can put long jobs first. The function panics if `order` is not such a list, or if a job panics.
pub fn run_all<S, R, I, F>(threads: usize, stack: usize, order: &[usize], init: I, job: F) -> Vec<R>
where
    R: Send,
    I: Fn() -> S + Sync,
    F: Fn(&mut S, usize) -> R + Sync,
{
    let n = order.len();
    check_order(order);
    let threads = threads.clamp(1, n.max(1));
    let next = AtomicUsize::new(0);
    let mut parts: Vec<Vec<(usize, R)>> = Vec::with_capacity(threads);
    std::thread::scope(|s| {
        let mut handles = Vec::with_capacity(threads);
        for t in 0..threads {
            let b = std::thread::Builder::new()
                .name(format!("rulean-worker-{t}"))
                .stack_size(stack);
            let h = b
                .spawn_scoped(s, || worker(&next, order, &init, &job))
                .expect("the pool cannot start a thread");
            handles.push(h);
        }
        for h in handles {
            match h.join() {
                Ok(p) => parts.push(p),
                Err(e) => std::panic::resume_unwind(e),
            }
        }
    });
    let mut slots: Vec<Option<R>> = (0..n).map(|_| None).collect();
    for p in parts {
        for (k, r) in p {
            assert!(slots[k].is_none(), "job {k} ran twice");
            slots[k] = Some(r);
        }
    }
    slots
        .into_iter()
        .enumerate()
        .map(|(k, r)| r.unwrap_or_else(|| panic!("job {k} did not run")))
        .collect()
}

/// One worker: it takes jobs from the counter until no job is left.
fn worker<S, R, I, F>(next: &AtomicUsize, order: &[usize], init: &I, job: &F) -> Vec<(usize, R)>
where
    I: Fn() -> S,
    F: Fn(&mut S, usize) -> R,
{
    let mut out = Vec::new();
    let mut i = next.fetch_add(1, Ordering::Relaxed);
    if i >= order.len() {
        return out;
    }
    let mut state = init();
    while i < order.len() {
        let k = order[i];
        out.push((k, job(&mut state, k)));
        i = next.fetch_add(1, Ordering::Relaxed);
    }
    out
}

/// Panics if `order` does not have each number of `0..order.len()` exactly once.
fn check_order(order: &[usize]) {
    let mut seen = vec![false; order.len()];
    for &k in order {
        assert!(k < order.len(), "job {k} is out of range");
        assert!(!seen[k], "job {k} is twice in the order");
        seen[k] = true;
    }
}

/// The order of jobs with the largest cost first ("longest processing time first", spec 08.3.3). Jobs with the same cost keep their input order.
pub fn largest_first(costs: &[u64]) -> Vec<usize> {
    let mut order: Vec<usize> = (0..costs.len()).collect();
    order.sort_by(|a, b| costs[*b].cmp(&costs[*a]).then(a.cmp(b)));
    order
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::AtomicU64;

    #[test]
    fn each_job_runs_once_and_in_its_slot() {
        for threads in [1, 2, 3, 8, 50] {
            let order = largest_first(&[5, 1, 9, 9, 0, 3, 7]);
            let inits = AtomicU64::new(0);
            let out = run_all(
                threads,
                1 << 20,
                &order,
                || {
                    inits.fetch_add(1, Ordering::Relaxed);
                    0u64
                },
                |count: &mut u64, k| {
                    *count += 1;
                    k * 10
                },
            );
            assert_eq!(out, vec![0, 10, 20, 30, 40, 50, 60]);
            assert!(inits.load(Ordering::Relaxed) as usize <= threads.min(7));
        }
    }

    #[test]
    fn no_job_gives_no_result() {
        let out: Vec<u8> = run_all(4, 1 << 20, &[], || (), |_, _| 1u8);
        assert!(out.is_empty());
    }

    #[test]
    fn largest_first_keeps_ties_in_input_order() {
        assert_eq!(largest_first(&[5, 1, 9, 9, 0]), vec![2, 3, 0, 1, 4]);
        assert_eq!(largest_first(&[]), Vec::<usize>::new());
    }

    #[test]
    #[should_panic(expected = "twice")]
    fn a_bad_order_panics() {
        let _ = run_all(2, 1 << 20, &[0, 0], || (), |_, k| k);
    }
}
