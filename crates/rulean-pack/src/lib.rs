//! Writes `.rlb` files (spec 07.2) from the store and the declarations that a parse gives.
//!
//! The encoder is not trusted. The checker checks what the decoder of `rulean-format` reads, so a wrong encoder can cause a reject but not a wrong accept (spec 10.5).
//!
//! The layout constants are in `rulean_format::rlb`. The encoder writes the tables in this order: STRINGS, NAMES, LEVELS, NATS, EXPRS, DECLS. It writes all strings, names, levels and numbers of the store, and the expressions that the declarations use, children first.

use std::collections::HashMap;

use rulean_format::crc::crc32c;
use rulean_format::rlb::*;
use rulean_format::{Decl, Defn, Hints, InductType, QuotKind, Rec, Safety};
use rulean_store::{BinderInfo, Expr, ExprId, Level, Literal, Name, NameId, Raw, Store, Tier};

/// The facts of the source export that go into the header.
#[derive(Clone, Debug, Default)]
pub struct Source {
    pub lean_version: Vec<u8>,
    pub githash: Vec<u8>,
    pub sha256: [u8; 32],
}

/// Counts of the written file.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Counts {
    pub strings: usize,
    pub names: usize,
    pub levels: usize,
    pub nats: usize,
    pub exprs: usize,
    pub decls: usize,
}

struct Body {
    kind: u32,
    count: u64,
    bytes: Vec<u8>,
}

fn put32(out: &mut Vec<u8>, x: u32) {
    out.extend_from_slice(&x.to_le_bytes());
}

fn put64(out: &mut Vec<u8>, x: u64) {
    out.extend_from_slice(&x.to_le_bytes());
}

fn pad8(out: &mut Vec<u8>) {
    while !out.len().is_multiple_of(8) {
        out.push(0);
    }
}

fn padded_field(out: &mut Vec<u8>, text: &[u8], size: usize, what: &str) -> Result<(), String> {
    if text.len() > size {
        return Err(format!("the {what} has more than {size} bytes"));
    }
    if text.contains(&0) {
        return Err(format!("the {what} has a zero byte"));
    }
    out.extend_from_slice(text);
    out.resize(out.len() + size - text.len(), 0);
    Ok(())
}

/// Encodes the declarations `decls`, whose handles refer to the frozen tier of `store`.
pub fn encode(store: &Store, decls: &[Decl], src: &Source) -> Result<(Vec<u8>, Counts), String> {
    let mut e = Encoder {
        store,
        index: HashMap::new(),
        exprs: Vec::new(),
        count: 0,
    };
    for d in decls {
        e.decl_exprs(d)?;
    }
    let strings = e.strings();
    let names = e.names();
    let levels = e.levels()?;
    let nats = e.nats();
    let exprs = Body {
        kind: SEC_EXPRS,
        count: e.count,
        bytes: std::mem::take(&mut e.exprs),
    };
    let mut db = Vec::new();
    for d in decls {
        e.decl(&mut db, d);
    }
    let decls_body = Body {
        kind: SEC_DECLS,
        count: decls.len() as u64,
        bytes: db,
    };
    let counts = Counts {
        strings: strings.count as usize,
        names: names.count as usize,
        levels: levels.count as usize,
        nats: nats.count as usize,
        exprs: exprs.count as usize,
        decls: decls.len(),
    };
    let bodies = [strings, names, levels, nats, exprs, decls_body];
    let mut out = Vec::new();
    out.extend_from_slice(&MAGIC);
    put32(&mut out, VERSION);
    put32(&mut out, 0);
    padded_field(
        &mut out,
        &src.lean_version,
        LEAN_VERSION_BYTES,
        "Lean version",
    )?;
    padded_field(&mut out, &src.githash, GITHASH_BYTES, "Lean githash")?;
    put32(&mut out, 0);
    put32(&mut out, bodies.len() as u32);
    out.extend_from_slice(&src.sha256);
    debug_assert_eq!(out.len(), HEADER_BYTES);
    let mut offset = (HEADER_BYTES + bodies.len() * DIR_BYTES) as u64;
    for b in &bodies {
        put32(&mut out, b.kind);
        put64(&mut out, offset);
        put64(&mut out, b.bytes.len() as u64);
        put64(&mut out, b.count);
        put32(&mut out, crc32c(&b.bytes, 0, b.bytes.len()));
        offset += (b.bytes.len() as u64).next_multiple_of(8);
    }
    for b in &bodies {
        out.extend_from_slice(&b.bytes);
        pad8(&mut out);
    }
    Ok((out, counts))
}

struct Encoder<'a> {
    store: &'a Store,
    /// The file index of each expression that is written.
    index: HashMap<Raw, u32>,
    exprs: Vec<u8>,
    count: u64,
}

fn binder_code(i: BinderInfo) -> u32 {
    match i {
        BinderInfo::Default => 0,
        BinderInfo::Implicit => 1,
        BinderInfo::StrictImplicit => 2,
        BinderInfo::InstImplicit => 3,
    }
}

fn safety_code(s: Safety) -> u32 {
    match s {
        Safety::Safe => 0,
        Safety::Unsafe => 1,
        Safety::Partial => 2,
    }
}

impl Encoder<'_> {
    fn strings(&self) -> Body {
        let s = self.store;
        let n = s.str_count();
        let mut out = Vec::new();
        for i in 0..n {
            put32(
                &mut out,
                s.str_bytes(rulean_store::StrId(i as u32)).len() as u32,
            );
        }
        for i in 0..n {
            out.extend_from_slice(s.str_bytes(rulean_store::StrId(i as u32)));
        }
        Body {
            kind: SEC_STRINGS,
            count: n as u64,
            bytes: out,
        }
    }

    fn names(&self) -> Body {
        let s = self.store;
        let n = s.name_count();
        let mut out = Vec::new();
        for i in 1..n {
            match s.name(NameId(i as u32)) {
                Name::Str(pre, x) => {
                    out.extend_from_slice(&[N_STR, 0, 0, 0]);
                    put32(&mut out, pre.0);
                    put64(&mut out, x.0 as u64);
                }
                Name::Num(pre, x) => {
                    out.extend_from_slice(&[N_NUM, 0, 0, 0]);
                    put32(&mut out, pre.0);
                    put64(&mut out, x);
                }
                Name::Anon => unreachable!("the store has one anonymous name, at index 0"),
            }
        }
        Body {
            kind: SEC_NAMES,
            count: (n - 1) as u64,
            bytes: out,
        }
    }

    fn levels(&self) -> Result<Body, String> {
        let s = self.store;
        let n = s.level_count();
        let mut out = Vec::new();
        for i in 1..n {
            let (tag, a, b) = match s.level(rulean_store::LevelId(i as u32)) {
                Level::Succ(a) => (L_SUCC, a.0, 0),
                Level::Max(a, b) => (L_MAX, a.0, b.0),
                Level::IMax(a, b) => (L_IMAX, a.0, b.0),
                Level::Param(p) => (L_PARAM, p.0, 0),
                Level::Zero => return Err("the store has two zero levels".to_owned()),
            };
            out.extend_from_slice(&[tag, 0, 0, 0]);
            put32(&mut out, a);
            put32(&mut out, b);
        }
        Ok(Body {
            kind: SEC_LEVELS,
            count: (n - 1) as u64,
            bytes: out,
        })
    }

    fn nats(&self) -> Body {
        let s = self.store;
        let n = s.nat_count();
        let mut out = Vec::new();
        for i in 0..n {
            let v = s.nat(rulean_store::NatId(i as u32));
            let k = v.limb_count();
            put32(&mut out, k as u32);
            put32(&mut out, 0);
            for j in 0..k {
                put64(&mut out, v.limb(j));
            }
        }
        Body {
            kind: SEC_NATS,
            count: n as u64,
            bytes: out,
        }
    }

    fn decl_exprs(&mut self, d: &Decl) -> Result<(), String> {
        match d {
            Decl::Axiom(x) => self.visit(x.ty),
            Decl::Defn(x) => {
                self.visit(x.ty)?;
                self.visit(x.value)
            }
            Decl::Thm(x) => {
                self.visit(x.ty)?;
                self.visit(x.value)
            }
            Decl::Opaque(x) => {
                self.visit(x.ty)?;
                self.visit(x.value)
            }
            Decl::Quot(x) => self.visit(x.ty),
            Decl::Mutual(ds) => {
                for x in ds {
                    self.visit(x.ty)?;
                    self.visit(x.value)?;
                }
                Ok(())
            }
            Decl::Induct(x) => {
                for t in &x.types {
                    self.visit(t.ty)?;
                }
                for c in &x.ctors {
                    self.visit(c.ty)?;
                }
                for r in &x.recs {
                    self.visit(r.ty)?;
                    for rule in &r.rules {
                        self.visit(rule.rhs)?;
                    }
                }
                Ok(())
            }
        }
    }

    /// Writes `root` and the expressions below it that are not written yet, children first. The walk uses a stack, so a deep term does not use the call stack.
    fn visit(&mut self, root: ExprId) -> Result<(), String> {
        let mut stack: Vec<(ExprId, bool)> = vec![(root, false)];
        while let Some((e, ready)) = stack.pop() {
            if self.index.contains_key(&e.0) {
                continue;
            }
            if e.tier() != Tier::Frozen {
                return Err("a declaration refers to a scratch term".to_owned());
            }
            let node = self.store.node(e);
            if ready {
                self.write(e, node)?;
                continue;
            }
            stack.push((e, true));
            match node {
                Expr::App(f, a) => {
                    stack.push((a, false));
                    stack.push((f, false));
                }
                Expr::Lam(b) | Expr::Pi(b) => {
                    stack.push((b.body, false));
                    stack.push((b.dom, false));
                }
                Expr::Let(l) => {
                    stack.push((l.body, false));
                    stack.push((l.value, false));
                    stack.push((l.ty, false));
                }
                Expr::Proj(p) => stack.push((p.expr, false)),
                Expr::FVar(..) => return Err("a declaration has a free variable".to_owned()),
                _ => {}
            }
        }
        Ok(())
    }

    fn at(&self, e: ExprId) -> u32 {
        self.index[&e.0]
    }

    fn write(&mut self, e: ExprId, node: Expr) -> Result<(), String> {
        let mut w: Vec<u32> = Vec::with_capacity(5);
        match node {
            Expr::BVar(i) => w.extend([E_BVAR, i]),
            Expr::Sort(l) => w.extend([E_SORT, l.0]),
            Expr::Const(c, ls) => {
                let items = self.store.level_list_items(ls);
                w.extend([E_CONST, c.0, items.len() as u32]);
                w.extend(items.iter().map(|l| l.0));
            }
            Expr::App(f, a) => w.extend([E_APP, self.at(f), self.at(a)]),
            Expr::Lam(b) | Expr::Pi(b) => {
                let tag = if matches!(node, Expr::Lam(_)) {
                    E_LAM
                } else {
                    E_PI
                };
                w.extend([
                    tag | (binder_code(b.info) << 8),
                    b.name.0,
                    self.at(b.dom),
                    self.at(b.body),
                ]);
            }
            Expr::Let(l) => w.extend([
                E_LET,
                l.name.0,
                self.at(l.ty),
                self.at(l.value),
                self.at(l.body),
            ]),
            Expr::Lit(Literal::Nat(n)) => w.extend([E_NAT, n.0]),
            Expr::Lit(Literal::Str(s)) => w.extend([E_STR, s.0]),
            Expr::Proj(p) => w.extend([E_PROJ, p.struct_name.0, p.index, self.at(p.expr)]),
            Expr::FVar(..) => return Err("a declaration has a free variable".to_owned()),
        }
        for x in w {
            put32(&mut self.exprs, x);
        }
        let i = u32::try_from(self.count).map_err(|_| "too many expressions".to_owned())?;
        self.index.insert(e.0, i);
        self.count += 1;
        Ok(())
    }

    fn names_list(out: &mut Vec<u8>, xs: &[NameId]) {
        put32(out, xs.len() as u32);
        for x in xs {
            put32(out, x.0);
        }
    }

    fn decl(&self, out: &mut Vec<u8>, d: &Decl) {
        match d {
            Decl::Axiom(x) => {
                put32(out, D_AXIOM);
                put32(out, x.name.0);
                Self::names_list(out, &x.lparams);
                put32(out, self.at(x.ty));
                put32(out, safety_code(x.safety));
            }
            Decl::Defn(x) => {
                put32(out, D_DEFN);
                self.defn(out, x);
            }
            Decl::Mutual(ds) => {
                put32(out, D_MUTUAL);
                put32(out, ds.len() as u32);
                for x in ds {
                    self.defn(out, x);
                }
            }
            Decl::Thm(x) => {
                put32(out, D_THM);
                put32(out, x.name.0);
                Self::names_list(out, &x.lparams);
                put32(out, self.at(x.ty));
                put32(out, self.at(x.value));
                Self::names_list(out, &x.all);
            }
            Decl::Opaque(x) => {
                put32(out, D_OPAQUE);
                put32(out, x.name.0);
                Self::names_list(out, &x.lparams);
                put32(out, self.at(x.ty));
                put32(out, self.at(x.value));
                put32(out, safety_code(x.safety));
                Self::names_list(out, &x.all);
            }
            Decl::Quot(x) => {
                put32(out, D_QUOT);
                put32(out, x.name.0);
                Self::names_list(out, &x.lparams);
                put32(out, self.at(x.ty));
                put32(
                    out,
                    match x.kind {
                        QuotKind::Type => 0,
                        QuotKind::Ctor => 1,
                        QuotKind::Lift => 2,
                        QuotKind::Ind => 3,
                    },
                );
            }
            Decl::Induct(x) => {
                put32(out, D_INDUCT);
                put32(out, x.types.len() as u32);
                put32(out, x.ctors.len() as u32);
                put32(out, x.recs.len() as u32);
                for t in &x.types {
                    self.induct_type(out, t);
                }
                for c in &x.ctors {
                    put32(out, c.name.0);
                    Self::names_list(out, &c.lparams);
                    put32(out, self.at(c.ty));
                    put32(out, c.induct.0);
                    put32(out, c.cidx);
                    put32(out, c.num_params);
                    put32(out, c.num_fields);
                    put32(out, safety_code(c.safety));
                }
                for r in &x.recs {
                    self.recursor(out, r);
                }
            }
        }
    }

    /// The fields of a definition, after its tag.
    fn defn(&self, out: &mut Vec<u8>, x: &Defn) {
        put32(out, x.name.0);
        Self::names_list(out, &x.lparams);
        put32(out, self.at(x.ty));
        put32(out, self.at(x.value));
        match x.hints {
            Hints::Opaque => put32(out, 0),
            Hints::Abbrev => put32(out, 1),
            Hints::Regular(h) => {
                put32(out, 2);
                put32(out, h);
            }
        }
        put32(out, safety_code(x.safety));
        Self::names_list(out, &x.all);
    }

    fn induct_type(&self, out: &mut Vec<u8>, t: &InductType) {
        put32(out, t.name.0);
        Self::names_list(out, &t.lparams);
        put32(out, self.at(t.ty));
        put32(out, t.num_params);
        put32(out, t.num_indices);
        Self::names_list(out, &t.all);
        Self::names_list(out, &t.ctors);
        put32(out, t.num_nested);
        put32(out, t.is_rec as u32);
        put32(out, t.is_reflexive as u32);
        put32(out, safety_code(t.safety));
    }

    fn recursor(&self, out: &mut Vec<u8>, r: &Rec) {
        put32(out, r.name.0);
        Self::names_list(out, &r.lparams);
        put32(out, self.at(r.ty));
        Self::names_list(out, &r.all);
        put32(out, r.num_params);
        put32(out, r.num_indices);
        put32(out, r.num_motives);
        put32(out, r.num_minors);
        put32(out, r.k as u32);
        put32(out, r.rules.len() as u32);
        for rule in &r.rules {
            put32(out, rule.ctor.0);
            put32(out, rule.nfields);
            put32(out, self.at(rule.rhs));
        }
        put32(out, safety_code(r.safety));
    }
}
