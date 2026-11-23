//! The two-stage scheduler of spec 08.3.
//!
//! The **add stage** runs in input order on one checker. It adds each axiom, definition, theorem and opaque constant to the environment without a check, so a later declaration can use its type and its value. It checks an inductive or a quotient declaration fully, because that check makes the constants that it adds, such as the recursors.
//!
//! The **check stage** runs the checks that the add stage did not do. The checks are put into jobs of consecutive declarations. A worker runs a job with a locked copy of the environment. Each check sees only the constants before its declaration (the cut of 08.3.2), so it sees the environment of a sequential run.
//!
//! **Determinism.** The job list does not depend on the thread count, and the merge takes the results in job order (spec 08.3.4 and contract K1). Each worker keeps its session from one job to the next, because a new session for each job made the check stage about two times slower on the Init export. A session entry is a true judgment, and the stamp rule lets a check use only the entries that were made at or below its cut. So the verdict, the first rejected declaration and the counts of declarations do not depend on the thread count or on the order in which the workers take the jobs. The counts of the session and of engine F depend on this order. A check that stops at a resource limit, such as the depth bound, can also depend on it, as it can depend on `--session`.

use alloc::vec::Vec;
use rulean_format::Decl;
use rulean_store::ids::KIND_COUNT;
use rulean_store::{Expr, ExprId, Store, Tier};

use crate::conv::FStats;
use crate::env::{ConstInfo, ConstKind, Env};
use crate::session::SessionStats;
use crate::tc::{Checker, Fault};

/// The number of jobs that the check stage aims at. A fixed number keeps the job list the same for each thread count.
pub const JOB_COUNT: u64 = 256;

/// One check of the check stage.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Step {
    /// The position of the declaration in the input.
    pub decl: u32,
    /// The number of constants before the declaration: the cut of the check.
    pub cut: u32,
    /// The extensions that primitive pinning turned off before the declaration (spec 05.8).
    pub pin_off: u32,
    /// The estimated cost: the number of distinct nodes of the type and the value.
    pub cost: u64,
}

/// What the add stage did with one declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Staged {
    /// The declaration is checked and added.
    Done,
    /// The declaration is added, and the check stage must check it with this cut and these pin bits.
    Later(u32, u32),
    /// The declaration is rejected.
    Failed(Fault),
}

/// The result of the add stage.
#[derive(Clone, Debug, Default)]
pub struct Plan {
    /// The checks of the check stage, in input order.
    pub steps: Vec<Step>,
    /// Job `k` has the steps `starts[k]..starts[k + 1]`. The last item is the number of steps.
    pub starts: Vec<u32>,
    /// The estimated cost of each job.
    pub costs: Vec<u64>,
    /// The number of declarations that the add stage looked at. If `failed` is set, it is the position of the rejected declaration.
    pub staged: u32,
    /// The fault of the declaration that the add stage rejected.
    pub failed: Option<Fault>,
    /// The number of constants after each declaration of the add stage.
    pub ends: Vec<u32>,
}

impl Plan {
    /// The number of jobs.
    pub fn jobs(&self) -> usize {
        if self.starts.len() == 0 {
            0
        } else {
            self.starts.len() - 1
        }
    }
}

/// The result of one job.
#[derive(Clone, Copy, Debug, Default)]
pub struct JobResult {
    /// The position of the first rejected declaration of the job, and its fault. The term of the fault is a term of the store of the worker.
    pub failed: Option<(u32, Fault)>,
    /// The counts of engine F in the job.
    pub f_stats: FStats,
    /// The counts of the session in the job.
    pub s_stats: SessionStats,
    /// The number of entries in the session of the worker at the end of the job.
    pub s_entries: u64,
    /// True if an array of the store of the worker was full. Then the result is not valid, and the run must stop.
    pub full: bool,
}

/// The merge of the results of all jobs.
#[derive(Clone, Copy, Debug, Default)]
pub struct Outcome {
    /// The number of declarations before the first rejected declaration, or the number of all declarations.
    pub accepted: u32,
    /// The first rejected declaration in input order, and its fault.
    pub failed: Option<(u32, Fault)>,
    pub f_stats: FStats,
    pub s_stats: SessionStats,
    /// The largest session of a worker at the end of a job.
    pub s_entries: u64,
    /// True if the store of a worker was full.
    pub full: bool,
}

/// A mark for each frozen expression node, for the cost estimate.
struct Marks {
    /// The position of the first node of each kind in `seen`.
    off: Vec<usize>,
    seen: Vec<u32>,
    stack: Vec<ExprId>,
}

impl Marks {
    fn new(st: &Store) -> Marks {
        let mut off = Vec::with_capacity(KIND_COUNT);
        let mut n = 0;
        let mut k = 0;
        while k < KIND_COUNT {
            off.push(n);
            n += st.kind_count(k);
            k += 1;
        }
        let mut seen = Vec::with_capacity(n);
        let mut i = 0;
        while i < n {
            seen.push(0);
            i += 1;
        }
        Marks {
            off,
            seen,
            stack: Vec::new(),
        }
    }

    /// Marks `e` with `stamp` and gives true if it had another mark. A scratch node is never marked.
    fn visit(&mut self, e: ExprId, stamp: u32) -> bool {
        if e.tier() == Tier::Scratch {
            false
        } else {
            let i = self.off[e.kind() as usize] + e.index();
            if i < self.seen.len() && self.seen[i] != stamp {
                self.seen[i] = stamp;
                true
            } else {
                false
            }
        }
    }

    /// The number of nodes of `e` that have no mark `stamp` yet. The call marks them.
    fn size(&mut self, st: &Store, e: ExprId, stamp: u32) -> u64 {
        let mut n = 0;
        self.stack.truncate(0);
        if self.visit(e, stamp) {
            self.stack.push(e);
        }
        while self.stack.len() != 0 {
            let x = self.stack[self.stack.len() - 1];
            self.stack.pop();
            n += 1;
            match st.node(x) {
                Expr::App(f, a) => {
                    self.push(f, stamp);
                    self.push(a, stamp);
                }
                Expr::Lam(b) | Expr::Pi(b) => {
                    self.push(b.dom, stamp);
                    self.push(b.body, stamp);
                }
                Expr::Let(l) => {
                    self.push(l.ty, stamp);
                    self.push(l.value, stamp);
                    self.push(l.body, stamp);
                }
                Expr::Proj(p) => self.push(p.expr, stamp),
                Expr::FVar(_, t) => self.push(t, stamp),
                _ => {}
            }
        }
        n
    }

    fn push(&mut self, e: ExprId, stamp: u32) {
        if self.visit(e, stamp) {
            self.stack.push(e);
        }
    }
}

/// The type and the value of a declaration that the check stage checks.
fn decl_terms(d: &Decl) -> (ExprId, Option<ExprId>) {
    match d {
        Decl::Axiom(a) => (a.ty, None),
        Decl::Defn(x) => (x.ty, Some(x.value)),
        Decl::Thm(t) => (t.ty, Some(t.value)),
        Decl::Opaque(o) => (o.ty, Some(o.value)),
        Decl::Quot(q) => (q.ty, None),
        Decl::Induct(_) | Decl::Mutual(_) => (ExprId(0), None),
    }
}

/// Puts the steps into jobs of consecutive steps with about the same cost.
fn group(plan: &mut Plan) {
    let mut total: u64 = 0;
    let mut i = 0;
    while i < plan.steps.len() {
        total += plan.steps[i].cost;
        i += 1;
    }
    let budget = total / JOB_COUNT + 1;
    plan.starts.truncate(0);
    plan.costs.truncate(0);
    let mut acc: u64 = 0;
    let mut j = 0;
    while j < plan.steps.len() {
        if acc == 0 {
            plan.starts.push(j as u32);
        }
        acc += plan.steps[j].cost;
        if acc >= budget {
            plan.costs.push(acc);
            acc = 0;
        }
        j += 1;
    }
    if acc > 0 {
        plan.costs.push(acc);
    }
    plan.starts.push(plan.steps.len() as u32);
}

impl Checker {
    /// The add stage for one declaration (spec 08.3.1).
    pub fn stage_decl(&mut self, d: &Decl) -> Staged {
        match d {
            Decl::Quot(_) | Decl::Induct(_) | Decl::Mutual(_) => match self.add_decl(d) {
                Some(f) => Staged::Failed(f),
                None => Staged::Done,
            },
            _ => self.stage_const(d),
        }
    }

    /// Adds an axiom, a definition, a theorem or an opaque constant without a check. Only the name is checked, because a later declaration with the same name must see this constant.
    fn stage_const(&mut self, d: &Decl) -> Staged {
        let cut = self.env.len() as u32;
        let pin_off = self.pin_off;
        let (ty, _) = decl_terms(d);
        self.fault = None;
        self.check_name(d.name(), ty);
        match self.fault() {
            Some(f) => Staged::Failed(f),
            None => {
                let c = match d {
                    Decl::Axiom(a) => (a.lparams.clone(), a.safety, ConstKind::Axiom),
                    Decl::Defn(x) => (
                        x.lparams.clone(),
                        x.safety,
                        ConstKind::Defn {
                            value: x.value,
                            hints: x.hints,
                        },
                    ),
                    Decl::Thm(t) => (
                        t.lparams.clone(),
                        rulean_format::Safety::Safe,
                        ConstKind::Thm { value: t.value },
                    ),
                    Decl::Opaque(o) => (
                        o.lparams.clone(),
                        o.safety,
                        ConstKind::Opaque { value: o.value },
                    ),
                    _ => (Vec::new(), rulean_format::Safety::Safe, ConstKind::Axiom),
                };
                self.env.add(ConstInfo {
                    name: d.name(),
                    lparams: c.0,
                    ty,
                    safety: c.1,
                    kind: c.2,
                });
                self.check_pins();
                Staged::Later(cut, pin_off)
            }
        }
    }

    /// Runs the add stage on all declarations and makes the jobs of the check stage. The add stage stops at the first rejected declaration.
    pub fn plan(&mut self, ds: &[Decl]) -> Plan {
        let mut plan = Plan::default();
        let mut i = 0;
        let mut going = true;
        while going && i < ds.len() {
            match self.stage_decl(&ds[i]) {
                Staged::Done => {}
                Staged::Later(cut, pin_off) => plan.steps.push(Step {
                    decl: i as u32,
                    cut,
                    pin_off,
                    cost: 0,
                }),
                Staged::Failed(f) => {
                    plan.failed = Some(f);
                    going = false;
                }
            }
            if going {
                plan.ends.push(self.env.len() as u32);
                i += 1;
            }
        }
        plan.staged = i as u32;
        let mut marks = Marks::new(&self.st);
        let mut k = 0;
        while k < plan.steps.len() {
            let (ty, value) = decl_terms(&ds[plan.steps[k].decl as usize]);
            let stamp = k as u32 + 1;
            let mut cost = 1 + marks.size(&self.st, ty, stamp);
            if let Some(v) = value {
                cost += marks.size(&self.st, v, stamp);
            }
            plan.steps[k].cost = cost;
            k += 1;
        }
        group(&mut plan);
        plan
    }

    /// A checker for a worker of the check stage. `st` and `env` are copies of the store and the environment of `main` after the add stage.
    pub fn worker(st: Store, env: Env, main: &Checker) -> Checker {
        let mut c = Checker::new(st);
        c.env = env;
        c.env.lock();
        c.flags = main.flags;
        c.engine = main.engine;
        c.confirm_all = main.confirm_all;
        c.trust_primitives = main.trust_primitives;
        c.max_depth = main.max_depth;
        c.set_max_memory(main.max_memory);
        c.sess = main.sess.fresh();
        c.pin_off = 0;
        // The add stage compared the primitives. A worker takes the pin bits of each step from the plan.
        c.pin_done = u32::MAX;
        c
    }

    /// Runs job `k` of the plan, and stops at the first rejected declaration of the job. The session of the worker stays from one job to the next. The stamp rule (spec 08.4) lets a check use only the entries with a stamp at or below its cut, so an entry of a later job is not used.
    pub fn run_job(&mut self, plan: &Plan, ds: &[Decl], k: usize) -> JobResult {
        self.f_stats = FStats::default();
        self.sess.stats = SessionStats::default();
        let mut r = JobResult::default();
        let mut i = plan.starts[k] as usize;
        let end = plan.starts[k + 1] as usize;
        while i < end {
            let s = plan.steps[i];
            if s.pin_off != self.pin_off {
                // The extensions change, so the old judgments of the session are not valid.
                self.pin_off = s.pin_off;
                self.sess.clear();
            }
            self.env.set_cut(s.cut);
            match self.add_decl(&ds[s.decl as usize]) {
                Some(f) => {
                    r.failed = Some((s.decl, f));
                    i = end;
                }
                None => i += 1,
            }
        }
        r.f_stats = self.f_stats;
        r.s_stats = self.sess.stats;
        r.s_entries = self.sess.len() as u64;
        r.full = self.st.is_full();
        r
    }
}

/// Adds the counts of `b` to `a`.
fn add_f(a: &mut FStats, b: &FStats) {
    a.queries += b.queries;
    a.equal += b.equal;
    a.fallback += b.fallback;
    a.confirmed += b.confirmed;
    a.disagree += b.disagree;
    a.faults += b.faults;
    a.infer += b.infer;
    a.infer_ok += b.infer_ok;
}

/// Adds the counts of `b` to `a`.
fn add_s(a: &mut SessionStats, b: &SessionStats) {
    a.hits += b.hits;
    a.stores += b.stores;
    a.drops += b.drops;
    a.evictions += b.evictions;
    a.promoted += b.promoted;
}

/// The larger of two counts.
fn max_u64(a: u64, b: u64) -> u64 {
    if a < b { b } else { a }
}

/// `a` if it is a failure, or else `b`.
fn first_failure(a: Option<(u32, Fault)>, b: Option<(u32, Fault)>) -> Option<(u32, Fault)> {
    match a {
        Some(x) => Some(x),
        None => b,
    }
}

/// True if `a` or `b` is true.
fn either(a: bool, b: bool) -> bool {
    a || b
}

/// Merges the results of the jobs, in job order, with the result of the add stage. `n` is the number of declarations.
pub fn merge(plan: &Plan, results: &[JobResult], n: u32) -> Outcome {
    let mut o = Outcome::default();
    let mut k = 0;
    while k < results.len() {
        let r = &results[k];
        add_f(&mut o.f_stats, &r.f_stats);
        add_s(&mut o.s_stats, &r.s_stats);
        o.s_entries = max_u64(o.s_entries, r.s_entries);
        o.full = either(o.full, r.full);
        o.failed = first_failure(o.failed, r.failed);
        k += 1;
    }
    let staged = match plan.failed {
        Some(f) => Some((plan.staged, f)),
        None => None,
    };
    o.failed = match (o.failed, staged) {
        (Some(a), Some(b)) => {
            if a.0 < b.0 {
                Some(a)
            } else {
                Some(b)
            }
        }
        (Some(a), None) => Some(a),
        (None, b) => b,
    };
    o.accepted = match o.failed {
        Some((i, _)) => i,
        None => n,
    };
    o
}
