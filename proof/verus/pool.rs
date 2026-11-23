//! The Verus proof of contract K1 for `rulean-pool` (spec 10.7).
//!
//! Contract K1 is `ParallelAll n f out`: for each job index `k < n`, `out[k] = f k`. This file is a model of `crates/rulean-pool/src/lib.rs`. Each function of the model has the same steps as the function of the same name in the crate, with these changes:
//!
//! - A panic of the crate is the result `None` of the model.
//! - `Job::run` is the closure `job`, and `Job::init` is the closure `init`. The contract of `run` says that the result of job `k` is `f(k)`, for each state. This is the part of K1 that the checker must give: the session state of a worker must not change a result (spec 08.4).
//! - `Counter::fetch_add` is the shared atomic counter. Its contract is empty, so the proof holds for each value that the counter can give, and thus for each schedule of the threads.
//! - The model runs the workers one after the other. The workers share only the counter and `job`, and the proof does not use a property of the counter. So the order of the workers does not change the proof.
//!
//! The proof shows safety: if `run_all` returns `Some(out)`, then `out` has `n` values and `out[k] == f(k)` for each `k < n`. It does not show that `run_all` returns `Some`. This needs the atomic counter to give each index once, and the test `each_job_runs_once_and_in_its_slot` and review cover it. The loop of `worker` has no `decreases` clause for the same reason.
//!
//! Run it with `verus proof/verus/pool.rs`. The CI job `verus` runs it with the Verus release of `.github/workflows/ci.yml`.

use vstd::prelude::*;

verus! {

/// The jobs of one call of `run_all`. `f` is the result of each job in the sequential twin.
pub trait Job {
    type S;
    type R;
    spec fn f(k: usize) -> Self::R;
    fn init(&self) -> Self::S;
    fn run(&self, s: &mut Self::S, k: usize) -> (r: Self::R)
        ensures r == Self::f(k);
}

/// The shared counter. The proof does not use a property of it.
pub trait Counter {
    fn fetch_add(&self) -> usize;
}

/// Each pair `(k, r)` of the output of a worker has a job index `k < n` and the result `r == f(k)`.
pub open spec fn good_part<J: Job>(p: Seq<(usize, J::R)>, n: nat) -> bool {
    forall|j: int| 0 <= j < p.len() ==> ((#[trigger] p[j]).0 as nat) < n && p[j].1 == J::f(p[j].0)
}

#[verifier::exec_allows_no_decreases_clause]
fn worker<J: Job, C: Counter>(next: &C, order: &Vec<usize>, job: &J) -> (out: Vec<(usize, J::R)>)
    requires forall|i: int| 0 <= i < order.len() ==> order[i] < order.len(),
    ensures good_part::<J>(out@, order.len() as nat),
{
    let mut out: Vec<(usize, J::R)> = Vec::new();
    let mut i = next.fetch_add();
    if i >= order.len() {
        return out;
    }
    let mut state = job.init();
    while i < order.len()
        invariant
            forall|i: int| 0 <= i < order.len() ==> order[i] < order.len(),
            good_part::<J>(out@, order.len() as nat),
    {
        let k = order[i];
        let r = job.run(&mut state, k);
        out.push((k, r));
        i = next.fetch_add();
    }
    out
}

fn check_order(order: &Vec<usize>) -> (ok: bool)
    ensures ok ==> forall|i: int| 0 <= i < order.len() ==> order[i] < order.len(),
{
    let n = order.len();
    let mut seen: Vec<bool> = Vec::new();
    let mut j: usize = 0;
    while j < n
        invariant seen.len() == j, j <= n,
        decreases n - j,
    {
        seen.push(false);
        j = j + 1;
    }
    let mut i: usize = 0;
    while i < n
        invariant
            n == order.len(), seen.len() == n, i <= n,
            forall|a: int| 0 <= a < i ==> order[a] < n,
        decreases n - i,
    {
        let k = order[i];
        if k >= n || seen[k] {
            return false;
        }
        seen.set(k, true);
        i = i + 1;
    }
    true
}

fn assemble<J: Job>(n: usize, parts: Vec<Vec<(usize, J::R)>>) -> (res: Option<Vec<J::R>>)
    requires forall|p: int| 0 <= p < parts.len() ==> good_part::<J>(#[trigger] parts[p]@, n as nat),
    ensures res matches Some(out) ==> out.len() == n && forall|k: int| 0 <= k < n ==> out[k] == J::f(k as usize),
{
    let mut parts = parts;
    let mut slots: Vec<Option<J::R>> = Vec::new();
    let mut j: usize = 0;
    while j < n
        invariant slots.len() == j, j <= n, forall|k: int| 0 <= k < j ==> slots[k] is None,
        decreases n - j,
    {
        slots.push(None);
        j = j + 1;
    }
    while parts.len() > 0
        invariant
            slots.len() == n,
            forall|p: int| 0 <= p < parts.len() ==> good_part::<J>(#[trigger] parts[p]@, n as nat),
            forall|k: int| 0 <= k < n ==> ((#[trigger] slots[k]) matches Some(r) ==> r == J::f(k as usize)),
        decreases parts.len(),
    {
        let mut part = parts.pop().unwrap();
        assert(good_part::<J>(part@, n as nat));
        while part.len() > 0
            invariant
                slots.len() == n,
                good_part::<J>(part@, n as nat),
                forall|k: int| 0 <= k < n ==> ((#[trigger] slots[k]) matches Some(r) ==> r == J::f(k as usize)),
            decreases part.len(),
        {
            let ghost before = part@;
            let (k, r) = part.pop().unwrap();
            assert(before[before.len() - 1] == (k, r));
            if slots[k].is_some() {
                return None;
            }
            slots.set(k, Some(r));
        }
    }
    // The crate takes the results out with `into_iter`. The model takes them out of the slots from the last slot to the first, and then puts them in order again.
    let mut rev: Vec<J::R> = Vec::new();
    while slots.len() > 0
        invariant
            slots.len() + rev.len() == n,
            forall|k: int| 0 <= k < slots.len() ==> ((#[trigger] slots[k]) matches Some(r) ==> r == J::f(k as usize)),
            forall|j: int| 0 <= j < rev.len() ==> rev[j] == J::f((n - 1 - j) as usize),
        decreases slots.len(),
    {
        let ghost m = slots.len() - 1;
        match slots.pop().unwrap() {
            Some(r) => {
                assert(r == J::f(m as usize));
                rev.push(r);
            }
            None => return None,
        }
    }
    let mut out: Vec<J::R> = Vec::new();
    while rev.len() > 0
        invariant
            out.len() + rev.len() == n,
            forall|j: int| 0 <= j < rev.len() ==> rev[j] == J::f((n - 1 - j) as usize),
            forall|k: int| 0 <= k < out.len() ==> out[k] == J::f(k as usize),
        decreases rev.len(),
    {
        let ghost m = rev.len() - 1;
        let r = rev.pop().unwrap();
        assert(r == J::f((n - 1 - m) as usize));
        out.push(r);
    }
    Some(out)
}

pub fn run_all<J: Job, C: Counter>(threads: usize, order: &Vec<usize>, job: &J, next: &C) -> (res: Option<Vec<J::R>>)
    ensures res matches Some(out) ==> out.len() == order.len() && forall|k: int| 0 <= k < order.len() ==> out[k] == J::f(k as usize),
{
    if !check_order(order) {
        return None;
    }
    let n = order.len();
    // `threads.clamp(1, n.max(1))` of the crate.
    let hi = if n == 0 { 1 } else { n };
    let threads = if threads < 1 { 1 } else if threads > hi { hi } else { threads };
    let mut parts: Vec<Vec<(usize, J::R)>> = Vec::new();
    let mut t: usize = 0;
    while t < threads
        invariant
            forall|i: int| 0 <= i < order.len() ==> order[i] < order.len(),
            n == order.len(),
            forall|p: int| 0 <= p < parts.len() ==> good_part::<J>(#[trigger] parts[p]@, n as nat),
        decreases threads - t,
    {
        let p = worker(next, order, job);
        parts.push(p);
        t = t + 1;
    }
    assemble::<J>(n, parts)
}

fn main() {}

} // verus!
