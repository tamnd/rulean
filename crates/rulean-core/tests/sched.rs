//! Tests of the two-stage scheduler of spec 08.3. Each test compares the scheduler with the sequential loop of `add_decl`. The verdict, the first rejected declaration and its error kind must be the same, for each order of the jobs.

use rulean_core::sched::{self, JobResult, Plan};
use rulean_core::tc::{Checker, ErrorKind};
use rulean_format::{Axiom, Decl, Defn, Hints, Safety, Thm};
use rulean_store::{BinderInfo, ExprId, NameId, Store};

struct T {
    st: Store,
}

impl T {
    fn name(&mut self, s: &str) -> NameId {
        let mut n = self.st.anon();
        for part in s.split('.') {
            n = self.st.name_str_bytes(n, part.as_bytes());
        }
        n
    }
    fn sort(&mut self, k: u32) -> ExprId {
        let mut l = self.st.level_zero();
        for _ in 0..k {
            l = self.st.level_succ(l);
        }
        self.st.mk_sort(l)
    }
    fn k(&mut self, s: &str) -> ExprId {
        let n = self.name(s);
        let ls = self.st.level_list_empty();
        self.st.mk_const(n, ls)
    }
    fn axiom(&mut self, name: &str, ty: ExprId) -> Decl {
        Decl::Axiom(Axiom {
            name: self.name(name),
            lparams: Vec::new(),
            ty,
            safety: Safety::Safe,
        })
    }
    fn defn(&mut self, name: &str, ty: ExprId, value: ExprId) -> Decl {
        let name = self.name(name);
        Decl::Defn(Defn {
            name,
            lparams: Vec::new(),
            ty,
            value,
            hints: Hints::Regular(1),
            safety: Safety::Safe,
            all: vec![name],
        })
    }
    fn thm(&mut self, name: &str, ty: ExprId, value: ExprId) -> Decl {
        Decl::Thm(Thm {
            name: self.name(name),
            lparams: Vec::new(),
            ty,
            value,
            all: Vec::new(),
        })
    }
}

/// A list of declarations: `Nat`, `Nat.zero`, `id`, `P`, `p`, and `n` definitions that use them. `bad` is called with the index of each definition and can give a wrong value for it.
fn decls(n: usize, bad: &dyn Fn(&mut T, usize) -> Option<Decl>) -> (Store, Vec<Decl>) {
    let mut t = T { st: Store::new() };
    let mut ds = Vec::new();
    let s1 = t.sort(1);
    ds.push(t.axiom("Nat", s1));
    let nat = t.k("Nat");
    ds.push(t.axiom("Nat.zero", nat));
    let x = t.name("x");
    let b0 = t.st.mk_bvar(0);
    let arrow = t.st.mk_pi(x, BinderInfo::Default, nat, nat);
    let lam = t.st.mk_lam(x, BinderInfo::Default, nat, b0);
    ds.push(t.defn("id", arrow, lam));
    let prop = t.sort(0);
    ds.push(t.axiom("P", prop));
    let p_ty = t.k("P");
    ds.push(t.axiom("p", p_ty));
    for i in 0..n {
        match bad(&mut t, i) {
            Some(d) => ds.push(d),
            None => {
                let prev = if i == 0 {
                    t.k("Nat.zero")
                } else {
                    t.k(&format!("d{}", i - 1))
                };
                let id = t.k("id");
                let v = t.st.mk_app(id, prev);
                ds.push(t.defn(&format!("d{i}"), nat, v));
                if i % 7 == 0 {
                    let p = t.k("p");
                    ds.push(t.thm(&format!("t{i}"), p_ty, p));
                }
            }
        }
    }
    (t.st, ds)
}

/// The position of the first rejected declaration and its kind, or the number of declarations.
fn sequential(st: &Store, ds: &[Decl]) -> (u32, Option<ErrorKind>) {
    let mut c = Checker::new(st.clone());
    for (i, d) in ds.iter().enumerate() {
        if let Some(f) = c.add_decl(d) {
            return (i as u32, Some(f.kind));
        }
    }
    (ds.len() as u32, None)
}

/// Runs the scheduler. The jobs run in `order`. If `fresh` is true, each job gets a new worker.
fn parallel(st: &Store, ds: &[Decl], order: &[usize], fresh: bool) -> (u32, Option<ErrorKind>) {
    let mut main = Checker::new(st.clone());
    let plan: Plan = main.plan(ds);
    let mut results = vec![JobResult::default(); plan.jobs()];
    let mut w = Checker::worker(main.st.clone(), main.env.clone(), &main);
    for &k in order {
        if fresh {
            w = Checker::worker(main.st.clone(), main.env.clone(), &main);
        }
        results[k] = w.run_job(&plan, ds, k);
    }
    let o = sched::merge(&plan, &results, ds.len() as u32);
    (o.accepted, o.failed.map(|(_, f)| f.kind))
}

/// Compares the scheduler with the sequential loop for three job orders.
fn same(st: &Store, ds: &[Decl]) -> (u32, Option<ErrorKind>) {
    let want = sequential(st, ds);
    let mut main = Checker::new(st.clone());
    let jobs = main.plan(ds).jobs();
    let forward: Vec<usize> = (0..jobs).collect();
    let backward: Vec<usize> = (0..jobs).rev().collect();
    let mut mixed: Vec<usize> = (0..jobs).filter(|k| k % 2 == 1).collect();
    mixed.extend((0..jobs).filter(|k| k % 2 == 0));
    for order in [&forward, &backward, &mixed] {
        assert_eq!(parallel(st, ds, order, false), want, "order {order:?}");
        assert_eq!(parallel(st, ds, order, true), want, "order {order:?}");
    }
    want
}

#[test]
fn a_good_list_is_accepted_in_full() {
    let (st, ds) = decls(600, &|_, _| None);
    let mut main = Checker::new(st.clone());
    assert!(main.plan(&ds).jobs() > 100);
    assert_eq!(same(&st, &ds), (ds.len() as u32, None));
}

#[test]
fn the_first_bad_value_is_rejected() {
    let (st, ds) = decls(600, &|t, i| {
        if i == 300 || i == 500 {
            let nat = t.k("Nat");
            let p = t.k("p");
            Some(t.defn(&format!("d{i}"), nat, p))
        } else {
            None
        }
    });
    let got = same(&st, &ds);
    assert!(got.0 < ds.len() as u32);
    assert_eq!(got.1, Some(ErrorKind::DefTypeMismatch));
}

#[test]
fn a_check_does_not_see_a_later_constant() {
    // d200 refers to d201, which comes after it. A sequential run rejects d200. A worker has all constants, so the cut must hide d201.
    let (st, ds) = decls(600, &|t, i| {
        if i == 200 {
            let nat = t.k("Nat");
            let next = t.k("d201");
            Some(t.defn("d200", nat, next))
        } else {
            None
        }
    });
    let got = same(&st, &ds);
    assert!(got.0 < ds.len() as u32);
    assert!(got.1.is_some());
}

#[test]
fn a_duplicate_name_stops_the_add_stage() {
    let (st, ds) = decls(400, &|t, i| {
        if i == 100 {
            let nat = t.k("Nat");
            Some(t.axiom("d50", nat))
        } else {
            None
        }
    });
    let mut main = Checker::new(st.clone());
    let plan = main.plan(&ds);
    assert!(plan.failed.is_some());
    let got = same(&st, &ds);
    assert_eq!(got.0, plan.staged);
    assert_eq!(got.1, Some(ErrorKind::AlreadyDeclared));
}
