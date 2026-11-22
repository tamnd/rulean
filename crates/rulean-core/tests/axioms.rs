//! Tests of the axiom sets of the module `axioms` (spec 09.4). Each test builds a small environment by hand.

use rulean_core::axioms::Axioms;
use rulean_core::env::{ConstInfo, ConstKind, CtorInfo, Env, InductInfo, RecInfo};
use rulean_format::{Hints, Safety};
use rulean_store::{BinderInfo, ExprId, NameId, Store};

struct T {
    st: Store,
    env: Env,
}

impl T {
    fn name(&mut self, s: &str) -> NameId {
        let mut n = self.st.anon();
        for part in s.split('.') {
            n = self.st.name_str_bytes(n, part.as_bytes());
        }
        n
    }
    fn k(&mut self, s: &str) -> ExprId {
        let n = self.name(s);
        let ls = self.st.level_list_empty();
        self.st.mk_const(n, ls)
    }
    fn add(&mut self, name: &str, ty: ExprId, kind: ConstKind) {
        let name = self.name(name);
        self.env.add(ConstInfo {
            name,
            lparams: Vec::new(),
            ty,
            safety: Safety::Safe,
            kind,
        });
    }
    fn names(&mut self, xs: &[&str]) -> Vec<NameId> {
        let mut v: Vec<NameId> = xs.iter().map(|x| self.name(x)).collect();
        v.sort_by_key(|n| n.0);
        v
    }
}

#[test]
fn sets_follow_print_axioms() {
    let mut t = T {
        st: Store::new(),
        env: Env::default(),
    };
    let mut ax = Axioms::new();
    let l0 = t.st.level_zero();
    let prop = t.st.mk_sort(l0);
    let l1 = t.st.level_succ(l0);
    let ty1 = t.st.mk_sort(l1);
    t.add("P", prop, ConstKind::Axiom);
    let p = t.k("P");
    t.add("h", p, ConstKind::Axiom);
    ax.update(&t.st, &t.env);
    let want = t.names(&["P"]);
    assert_eq!(ax.of_slot(1), &want[..]);
    // An axiom gives only itself. Its type is not visited.
    let want = t.names(&["h"]);
    assert_eq!(ax.of_slot(2), &want[..]);

    // An inductive group: `I : Type` with `I.mk : P -> I` and `I.rec`. The type of `I` has no axiom, so the set of `I` comes from its constructor, which is new in the same update.
    let ind = t.name("I");
    let mk = t.name("I.mk");
    let i = t.k("I");
    let x = t.name("x");
    let mk_ty = t.st.mk_pi(x, BinderInfo::Default, p, i);
    t.add(
        "I",
        ty1,
        ConstKind::Induct(InductInfo {
            nparams: 0,
            nindices: 0,
            all: vec![ind],
            ctors: vec![mk],
            nnested: 0,
            is_rec: false,
            is_reflexive: false,
        }),
    );
    t.add(
        "I.mk",
        mk_ty,
        ConstKind::Ctor(CtorInfo {
            induct: ind,
            cidx: 0,
            nparams: 0,
            nfields: 1,
        }),
    );
    t.add(
        "I.rec",
        i,
        ConstKind::Rec(RecInfo {
            all: vec![ind],
            nparams: 0,
            nindices: 0,
            nmotives: 1,
            nminors: 1,
            rules: Vec::new(),
            k: false,
        }),
    );
    ax.update(&t.st, &t.env);
    let want = t.names(&["P"]);
    for s in 3..=5 {
        assert_eq!(ax.of_slot(s), &want[..], "slot {s}");
    }

    // A definition and a theorem that use the constants above.
    let h = t.k("h");
    t.add(
        "d",
        ty1,
        ConstKind::Defn {
            value: i,
            hints: Hints::Regular(1),
        },
    );
    t.add("thm", p, ConstKind::Thm { value: h });
    t.add("free", prop, ConstKind::Thm { value: p });
    ax.update(&t.st, &t.env);
    let (d, thm, free, none) = (t.name("d"), t.name("thm"), t.name("free"), t.name("none"));
    let want = t.names(&["P"]);
    assert_eq!(ax.of_const(&t.env, d), &want[..]);
    assert_eq!(ax.of_const(&t.env, free), &want[..]);
    let want = t.names(&["P", "h"]);
    assert_eq!(ax.of_const(&t.env, thm), &want[..]);
    assert_eq!(ax.all(), want);
    assert!(ax.of_const(&t.env, none).is_empty());
}
