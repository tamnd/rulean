//! Compares the declarations that the olean reader gives with the declarations of an NDJSON export of the same modules. Usage: `olean_compare EXPORT DIR MODULE...`.
//!
//! The two readers write into one store, so two equal terms have the same handle. lean4export shares terms that are equal up to the names and the kinds of the binders, as `BEq Expr` of Lean does, so the export can give a binder the name of another term. The comparison is thus up to binder names and binder kinds, which the kernel does not use.

use std::collections::BTreeMap;

use rulean_format::Decl;
use rulean_store::{BinderInfo, Expr, ExprId, NameId, Store};

/// The terms with each binder name anonymous and each binder kind default.
struct Canon {
    memo: BTreeMap<ExprId, ExprId>,
}

impl Canon {
    fn expr(&mut self, st: &mut Store, root: ExprId) -> ExprId {
        let mut stack = vec![(root, false)];
        while let Some((e, ready)) = stack.pop() {
            if self.memo.contains_key(&e) {
                continue;
            }
            let node = st.node(e);
            let kids: Vec<ExprId> = match node {
                Expr::App(f, a) => vec![f, a],
                Expr::Lam(b) | Expr::Pi(b) => vec![b.dom, b.body],
                Expr::Let(l) => vec![l.ty, l.value, l.body],
                Expr::Proj(p) => vec![p.expr],
                Expr::FVar(_, t) => vec![t],
                _ => vec![],
            };
            if !ready {
                stack.push((e, true));
                stack.extend(kids.into_iter().map(|k| (k, false)));
                continue;
            }
            let m = |k: ExprId| self.memo[&k];
            let anon = NameId(0);
            let out = match node {
                Expr::App(f, a) => {
                    let (f, a) = (m(f), m(a));
                    st.mk_app(f, a)
                }
                Expr::Lam(b) => {
                    let (d, x) = (m(b.dom), m(b.body));
                    st.mk_lam(anon, BinderInfo::Default, d, x)
                }
                Expr::Pi(b) => {
                    let (d, x) = (m(b.dom), m(b.body));
                    st.mk_pi(anon, BinderInfo::Default, d, x)
                }
                Expr::Let(l) => {
                    let (t, v, x) = (m(l.ty), m(l.value), m(l.body));
                    st.mk_let(anon, t, v, x)
                }
                Expr::Proj(p) => {
                    let x = m(p.expr);
                    st.mk_proj(p.struct_name, p.index, x)
                }
                Expr::FVar(i, t) => {
                    let t = m(t);
                    st.mk_fvar(i, t)
                }
                _ => e,
            };
            self.memo.insert(e, out);
        }
        self.memo[&root]
    }

    fn decl(&mut self, st: &mut Store, d: &Decl) -> Decl {
        let mut d = d.clone();
        match &mut d {
            Decl::Axiom(x) => x.ty = self.expr(st, x.ty),
            Decl::Quot(x) => x.ty = self.expr(st, x.ty),
            Decl::Defn(x) => {
                x.ty = self.expr(st, x.ty);
                x.value = self.expr(st, x.value);
            }
            Decl::Thm(x) => {
                x.ty = self.expr(st, x.ty);
                x.value = self.expr(st, x.value);
            }
            Decl::Opaque(x) => {
                x.ty = self.expr(st, x.ty);
                x.value = self.expr(st, x.value);
            }
            Decl::Mutual(ds) => {
                for x in ds {
                    x.ty = self.expr(st, x.ty);
                    x.value = self.expr(st, x.value);
                }
            }
            Decl::Induct(b) => {
                // The checker finds a recursor by its name, so the order of the recursors does not matter.
                b.recs.sort_by_key(|r| r.name);
                for t in &mut b.types {
                    t.ty = self.expr(st, t.ty);
                }
                for c in &mut b.ctors {
                    c.ty = self.expr(st, c.ty);
                }
                for r in &mut b.recs {
                    r.ty = self.expr(st, r.ty);
                    for x in &mut r.rules {
                        x.rhs = self.expr(st, x.rhs);
                    }
                }
            }
        }
        d
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() < 3 {
        eprintln!("usage: olean_compare EXPORT DIR MODULE...");
        std::process::exit(64);
    }
    let mut st = Store::new();
    let bytes = std::fs::read(&args[0]).expect("read the export");
    let export = rulean_format::ndjson::parse_export(&mut st, &bytes).expect("parse the export");
    let search = vec![std::path::PathBuf::from(&args[1])];
    let loaded = match rulean_olean::load(&mut st, &args[2..], &search) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("error ({:?}): {e}", e.kind);
            std::process::exit(1);
        }
    };
    let mut c = Canon {
        memo: BTreeMap::new(),
    };
    let mut a = BTreeMap::new();
    for d in &export.decls {
        a.insert(d.name(), c.decl(&mut st, d));
    }
    let mut b = BTreeMap::new();
    for d in &loaded.decls {
        b.insert(d.name(), c.decl(&mut st, d));
    }
    let text = |n: NameId| String::from_utf8_lossy(&st.name_text(n)).into_owned();
    let mut missing = 0;
    let mut differ = 0;
    for (n, d) in &a {
        match b.get(n) {
            None => {
                missing += 1;
                if missing <= 5 {
                    println!("only in the export: {}", text(*n));
                }
            }
            Some(e) if e != d => {
                differ += 1;
                if differ <= 5 {
                    println!("differ: {}\n  export: {:?}\n  olean:  {:?}", text(*n), d, e);
                    if let (Decl::Induct(x), Decl::Induct(y)) = (d, e) {
                        let rn = |b: &rulean_format::Induct| {
                            b.recs.iter().map(|r| text(r.name)).collect::<Vec<_>>()
                        };
                        println!("  recs: {:?} {:?}", rn(x), rn(y));
                        println!(
                            "  same types {} ctors {}",
                            x.types == y.types,
                            x.ctors == y.ctors
                        );
                    }
                }
            }
            Some(_) => {}
        }
    }
    let extra: Vec<_> = b.keys().filter(|n| !a.contains_key(n)).collect();
    let mut kinds: BTreeMap<String, usize> = BTreeMap::new();
    for n in &extra {
        let k = match b[*n] {
            Decl::Axiom(ref x) => format!("axiom {:?}", x.safety),
            Decl::Defn(ref x) => format!("defn {:?}", x.safety),
            Decl::Opaque(ref x) => format!("opaque {:?}", x.safety),
            Decl::Thm(_) => "thm".into(),
            Decl::Quot(_) => "quot".into(),
            Decl::Induct(_) => "induct".into(),
            Decl::Mutual(ref ds) => format!("mutual {:?} of {}", ds[0].safety, ds.len()),
        };
        let e = kinds.entry(k.clone()).or_default();
        *e += 1;
        if *e <= 3 {
            println!("only in the oleans: {k} {}", text(**n));
        }
    }
    println!("kinds only in the oleans: {kinds:?}");
    println!(
        "export {} declarations, oleans {} declarations: {} only in the export, {} only in the oleans, {} differ",
        a.len(),
        b.len(),
        missing,
        extra.len(),
        differ
    );
    if missing + differ > 0 {
        std::process::exit(1);
    }
}
