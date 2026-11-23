//! The loader: module search, the import closure and the order of the declarations (spec 07.3.4).

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use rulean_core::sha256::Hasher;
use rulean_format::{Decl, Defn, Induct, InductType, Rec, Safety};
use rulean_store::{Expr, ExprId, Level, Name, NameId, Store};

use crate::decode::{Decoder, Item};
use crate::region::{Part, Region};
use crate::{Error, Fault, FaultKind};

/// The file name extensions of the parts of a module, in load order.
const PARTS: [&str; 3] = ["olean", "olean.server", "olean.private"];

/// The result of `load`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Loaded {
    /// The declarations of all modules, in an order where each declaration comes after the declarations that it uses.
    pub decls: Vec<Decl>,
    /// The Lean version in the headers, for example `4.36.0`.
    pub lean_version: Vec<u8>,
    /// The Lean commit in the headers.
    pub githash: Vec<u8>,
    /// The olean format version.
    pub version: u8,
    /// The modules in load order.
    pub modules: Vec<String>,
    /// The files that the loader read.
    pub files: Vec<PathBuf>,
    /// The number of objects in the files.
    pub objects: usize,
    /// The SHA-256 digest of all the bytes of `files`, in the order of `files`. These are the bytes that the loader decoded (contract K2, spec 10.7).
    pub sha256: [u8; 32],
}

/// The SHA-256 digest of all the bytes of `files`, in order. A caller reads the files again after the run with this function and compares the result with `Loaded::sha256`.
pub fn digest(files: &[PathBuf]) -> std::io::Result<[u8; 32]> {
    let mut h = Hasher::new();
    for f in files {
        h.update(&std::fs::read(f)?);
    }
    Ok(h.finish())
}

/// An error without a file.
fn plain(kind: FaultKind, msg: impl Into<String>) -> Error {
    Error {
        kind,
        file: None,
        offset: 0,
        msg: msg.into(),
    }
}

/// The path of the `.olean` file of `module` below `dir`. Each component of the module name must be a plain file name, so a name cannot point outside `dir`.
pub fn module_path(dir: &Path, module: &str) -> Option<PathBuf> {
    let mut p = dir.to_path_buf();
    for c in module.split('.') {
        let plain = !c.is_empty()
            && c != ".."
            && !c.contains(['/', '\\', '\0', ':'])
            && !c.starts_with('«');
        if !plain {
            return None;
        }
        p.push(c);
    }
    p.set_extension("olean");
    Some(p)
}

/// The text of a module name of the store. A name with a number component is not a module name.
fn module_text(st: &Store, n: NameId) -> Option<String> {
    let mut parts = Vec::new();
    let mut cur = n;
    loop {
        match st.name(cur) {
            Name::Anon => break,
            Name::Str(pre, s) => {
                parts.push(String::from_utf8(st.str_bytes(s).to_vec()).ok()?);
                cur = pre;
            }
            Name::Num(..) => return None,
        }
    }
    parts.reverse();
    if parts.is_empty() {
        None
    } else {
        Some(parts.join("."))
    }
}

/// One decoded module.
#[derive(Debug)]
pub struct Module {
    /// The imports, in the order of the file.
    pub imports: Vec<String>,
    /// The declarations, in an order where each declaration comes after the declarations of the module that it uses.
    pub decls: Vec<Decl>,
}

/// Reads and decodes the module `m` from the directories `search`, but not its imports. The declarations can refer to constants of the imports, so the checker cannot take them alone.
pub fn read_module(st: &mut Store, search: &[PathBuf], m: &str) -> Result<Module, Error> {
    let mut l = Loader::new(st, search);
    l.module(m)
}

/// Decodes one module from the bytes of its parts, in the order `.olean`, `.olean.server`, `.olean.private`. `None` is a part that does not exist. The module has the same checks as a module that `read_module` reads from files. An error gives the part as the file `mem.olean`, `mem.olean.server` or `mem.olean.private`. The fuzz targets use this function (spec 11.5.1).
pub fn decode_parts(st: &mut Store, parts: [Option<Vec<u8>>; 3]) -> Result<Module, Error> {
    let mut l = Loader::new(st, &[]);
    let files = part_files(Path::new("mem"));
    let mut mem = BTreeMap::new();
    for (f, b) in files.iter().zip(parts) {
        if let Some(b) = b {
            mem.insert(f.clone(), b);
        }
    }
    l.mem = Some(mem);
    l.module_files(&files)
}

/// The files of the parts of the module with the base path `base`, in load order.
fn part_files(base: &Path) -> Vec<PathBuf> {
    PARTS.iter().map(|x| base.with_extension(x)).collect()
}

/// The state of the loader.
struct Loader<'a> {
    st: &'a mut Store,
    search: &'a [PathBuf],
    /// The bytes of each file, for `decode_parts`. `None` reads the files from the file system.
    mem: Option<BTreeMap<PathBuf, Vec<u8>>>,
    out: Loaded,
    first: bool,
    hash: Hasher,
    /// The first position of `out.decls` that `load` must sort again after a replacement.
    resort: Option<usize>,
}

/// Loads the modules `roots` and their import closure from the directories `search`. The first directory that has the `.olean` file of a module wins.
pub fn load(st: &mut Store, roots: &[String], search: &[PathBuf]) -> Result<Loaded, Error> {
    let mut l = Loader::new(st, search);
    // A depth-first walk of the import graph with an explicit stack. A module is emitted after all of its imports.
    let mut state: BTreeMap<String, u8> = BTreeMap::new();
    let mut decoded: BTreeMap<String, Module> = BTreeMap::new();
    let mut index: BTreeMap<NameId, usize> = BTreeMap::new();
    for r in roots {
        let mut stack: Vec<(String, usize)> = vec![(r.clone(), 0)];
        while let Some((m, next)) = stack.pop() {
            if next == 0 {
                match state.get(&m) {
                    Some(2) => continue,
                    Some(_) => {
                        return Err(plain(
                            FaultKind::Malformed,
                            format!("the imports of {m} have a cycle"),
                        ));
                    }
                    None => {}
                }
                state.insert(m.clone(), 1);
                let md = l.module(&m)?;
                decoded.insert(m.clone(), md);
            }
            let imports = &decoded[&m].imports;
            if next < imports.len() {
                let dep = imports[next].clone();
                stack.push((m, next + 1));
                if state.get(&dep) != Some(&2) {
                    stack.push((dep, 0));
                }
                continue;
            }
            state.insert(m.clone(), 2);
            if let Some(md) = decoded.remove(&m) {
                for d in md.decls {
                    l.add(&m, d, &mut index)?;
                }
            }
            l.out.modules.push(m);
        }
    }
    if let Some(from) = l.resort {
        let decls = std::mem::take(&mut l.out.decls);
        l.out.decls = resort(l.st, decls, from, &index)?;
    }
    l.out.sha256 = l.hash.finish();
    Ok(l.out)
}

impl<'a> Loader<'a> {
    fn new(st: &'a mut Store, search: &'a [PathBuf]) -> Loader<'a> {
        Loader {
            st,
            search,
            mem: None,
            out: Loaded {
                decls: Vec::new(),
                lean_version: Vec::new(),
                githash: Vec::new(),
                version: 0,
                modules: Vec::new(),
                files: Vec::new(),
                objects: 0,
                sha256: [0; 32],
            },
            first: true,
            hash: Hasher::new(),
            resort: None,
        }
    }

    /// Adds a declaration of module `m`. Each name must occur once, with one exception. Lean can make the same auxiliary theorem in two modules, for example an equation lemma. The import of Lean (`finalizeImport`) accepts a second constant when one of the two constants subsumes the other (`subsumes`). When the new constant subsumes the old constant, the new constant replaces the old constant, so the last copy wins. The loader does the same. The new constant goes to the position of the old constant. If its value uses a declaration that comes after this position, `load` sorts the declarations from this position again (`resort`).
    fn add(&mut self, m: &str, d: Decl, index: &mut BTreeMap<NameId, usize>) -> Result<(), Error> {
        let mut names = members(&d);
        names.sort();
        let clash = names.iter().find_map(|n| index.get(n).map(|&i| (*n, i)));
        let Some((n, i)) = clash else {
            for n in names {
                index.insert(n, self.out.decls.len());
            }
            self.out.decls.push(d);
            return Ok(());
        };
        let text = String::from_utf8_lossy(&self.st.name_text(n)).into_owned();
        if self.subsumes(&d, &self.out.decls[i], index) {
            if uses(self.st, &d, index, i).iter().any(|&u| u > i) {
                self.resort = Some(self.resort.map_or(i, |r| r.min(i)));
            }
            self.out.decls[i] = d;
            return Ok(());
        }
        if self.subsumes(&self.out.decls[i], &d, index) {
            return Ok(());
        }
        Err(plain(
            FaultKind::Malformed,
            format!(
                "the module {m} declares {text} again, and neither constant subsumes the other"
            ),
        ))
    }

    /// The `subsumesInfo` test of the import of Lean: `a` can replace `b`. The two constants must have the same name, level parameters and type. Then a theorem subsumes a theorem with the same `all` list, and a theorem subsumes a safe axiom when its `all` list is the name. An axiom subsumes an axiom with the same safety when the type is a proposition by the test `prop_cheap`. The values are not compared.
    fn subsumes(&self, a: &Decl, b: &Decl, index: &BTreeMap<NameId, usize>) -> bool {
        match (a, b) {
            (Decl::Thm(x), Decl::Thm(y)) => {
                x.name == y.name && x.lparams == y.lparams && x.ty == y.ty && x.all == y.all
            }
            (Decl::Thm(x), Decl::Axiom(y)) => {
                x.name == y.name
                    && x.lparams == y.lparams
                    && x.ty == y.ty
                    && x.all == [y.name]
                    && y.safety == Safety::Safe
            }
            (Decl::Axiom(x), Decl::Axiom(y)) => {
                x.name == y.name
                    && x.lparams == y.lparams
                    && x.ty == y.ty
                    && x.safety == y.safety
                    && self.prop_cheap(x.ty, index)
            }
            _ => false,
        }
    }

    /// The `isPropCheap` test of the import of Lean. The type `ty` must have the form `(xs : As) -> p ys`, where `p` is a constant with a type `(zs : Bs) -> Prop` and `ys` and `zs` have the same length. The test does not instantiate the bound variables.
    fn prop_cheap(&self, ty: ExprId, index: &BTreeMap<NameId, usize>) -> bool {
        let mut e = ty;
        while let Expr::Pi(b) = self.st.node(e) {
            e = b.body;
        }
        let mut args = 0usize;
        while let Expr::App(f, _) = self.st.node(e) {
            e = f;
            args += 1;
        }
        let Expr::Const(n, _) = self.st.node(e) else {
            return false;
        };
        let Some(mut p) = index.get(&n).and_then(|&i| type_of(&self.out.decls[i], n)) else {
            return false;
        };
        for _ in 0..args {
            let Expr::Pi(b) = self.st.node(p) else {
                return false;
            };
            p = b.body;
        }
        matches!(self.st.node(p), Expr::Sort(l) if self.st.level(l) == Level::Zero)
    }

    /// The base path of the files of `m`.
    fn find(&self, m: &str) -> Result<PathBuf, Error> {
        for d in self.search {
            match module_path(d, m) {
                Some(p) if p.is_file() => return Ok(p),
                Some(_) => {}
                None => {
                    return Err(plain(
                        FaultKind::Malformed,
                        format!("{m} is not a valid module name"),
                    ));
                }
            }
        }
        Err(plain(
            FaultKind::Missing,
            format!("the module {m} is not on the search path"),
        ))
    }

    /// Reads one part and checks that its Lean version is the same as the version of the first part.
    fn part(&mut self, p: &Path) -> Result<Part, Error> {
        let read = match &self.mem {
            Some(m) => m
                .get(p)
                .cloned()
                .ok_or_else(|| std::io::Error::from(std::io::ErrorKind::NotFound)),
            None => std::fs::read(p),
        };
        let bytes = read.map_err(|e| Error {
            kind: FaultKind::Io,
            file: Some(p.to_path_buf()),
            offset: 0,
            msg: format!("cannot read the file: {e}"),
        })?;
        self.hash.update(&bytes);
        let part = Part::new(bytes).map_err(|f| at_file(p, f))?;
        let h = &part.header;
        if self.first {
            self.first = false;
            self.out.lean_version = h.lean_version.clone();
            self.out.githash = h.githash.clone();
            self.out.version = h.version;
        } else if h.lean_version != self.out.lean_version || h.githash != self.out.githash {
            return Err(Error {
                kind: FaultKind::Malformed,
                file: Some(p.to_path_buf()),
                offset: 7,
                msg: format!(
                    "the file is from Lean {}, but the first file is from Lean {}",
                    String::from_utf8_lossy(&h.lean_version),
                    String::from_utf8_lossy(&self.out.lean_version)
                ),
            });
        }
        self.out.files.push(p.to_path_buf());
        self.out.objects += part.objects;
        Ok(part)
    }

    /// True if the file `p` exists.
    fn exists(&self, p: &Path) -> bool {
        match &self.mem {
            Some(m) => m.contains_key(p),
            None => p.is_file(),
        }
    }

    /// Reads and decodes the module `m`.
    fn module(&mut self, m: &str) -> Result<Module, Error> {
        let base = self.find(m)?;
        self.module_files(&part_files(&base))
    }

    /// Reads and decodes the module with the part files `files`.
    fn module_files(&mut self, files: &[PathBuf]) -> Result<Module, Error> {
        let mut rg = Region::default();
        let first = self.part(&files[0])?;
        rg.push(first).map_err(|f| at_file(&files[0], f))?;
        // Read the public part first. For a module of the module system, also read the other parts.
        let public = {
            let mut d = Decoder::new(&rg, self.st);
            d.module_data(0).map_err(|f| at_part(files, f, 0))?
        };
        if !public.is_module {
            let imports = self.imports(&public.imports, &files[0])?;
            let decls = order(self.st, public.constants).map_err(|f| at_part(files, f, 0))?;
            return Ok(Module { imports, decls });
        }
        for f in &files[1..] {
            if self.exists(f) {
                let p = self.part(f)?;
                rg.push(p).map_err(|e| at_file(f, e))?;
            }
        }
        let last = rg.parts.len() - 1;
        if !self.exists(&files[2]) {
            return Err(Error {
                kind: FaultKind::Missing,
                file: Some(files[2].clone()),
                offset: 0,
                msg: "the module uses the module system, but its private part is missing, so its proofs cannot be checked".into(),
            });
        }
        let (public, private) = {
            let mut d = Decoder::new(&rg, self.st);
            let public = d.module_data(0).map_err(|f| at_part(files, f, 0))?;
            let private = d.module_data(last).map_err(|f| at_part(files, f, last))?;
            (public, private)
        };
        let last_file = &rg_file(files, &rg, last);
        if private.imports != public.imports || !private.is_module {
            return Err(Error {
                kind: FaultKind::Malformed,
                file: Some(last_file.clone()),
                offset: 0,
                msg: "the private part does not agree with the public part on the imports".into(),
            });
        }
        same_public(self.st, &public.constants, &private.constants).map_err(|msg| Error {
            kind: FaultKind::Malformed,
            file: Some(last_file.clone()),
            offset: 0,
            msg,
        })?;
        let imports = self.imports(&public.imports, &files[0])?;
        let decls = order(self.st, private.constants).map_err(|f| at_part(files, f, last))?;
        Ok(Module { imports, decls })
    }

    fn imports(&self, ns: &[NameId], file: &Path) -> Result<Vec<String>, Error> {
        ns.iter()
            .map(|&n| {
                module_text(self.st, n).ok_or_else(|| Error {
                    kind: FaultKind::Malformed,
                    file: Some(file.to_path_buf()),
                    offset: 0,
                    msg: "an import is not a module name".into(),
                })
            })
            .collect()
    }
}

/// The file of part `i` of the region. The parts that exist are pushed in the order of `files`.
fn rg_file(files: &[PathBuf], rg: &Region, i: usize) -> PathBuf {
    if rg.parts.len() == files.len() {
        files[i].clone()
    } else if i == 0 {
        files[0].clone()
    } else {
        files[2].clone()
    }
}

fn at_file(p: &Path, f: Fault) -> Error {
    Error {
        kind: f.kind,
        file: Some(p.to_path_buf()),
        offset: f.offset,
        msg: f.msg,
    }
}

/// The error of a fault in the region. The part of the fault, if it has one, selects the file.
fn at_part(files: &[PathBuf], f: Fault, part: usize) -> Error {
    let i = f.part.unwrap_or(part).min(files.len() - 1);
    at_file(&files[i], f)
}

/// Checks the rule of spec 07.3.4: each constant of the public part is also in the private part. Where the public part has an axiom and the private part has a theorem, a definition or an opaque constant, the two must have the same name, level parameters and type. All other constants must be the same.
fn same_public(st: &Store, public: &[Item], private: &[Item]) -> Result<(), String> {
    let by_name: BTreeMap<NameId, &Item> = private.iter().map(|i| (i.name(), i)).collect();
    for p in public {
        let text = || String::from_utf8_lossy(&st.name_text(p.name())).into_owned();
        let Some(q) = by_name.get(&p.name()) else {
            return Err(format!(
                "the constant {} is in the public part but not in the private part",
                text()
            ));
        };
        if p == *q {
            continue;
        }
        let ok = match (p, q) {
            (Item::Decl(Decl::Axiom(a)), Item::Decl(d)) => {
                let (lp, ty) = match d {
                    Decl::Thm(t) => (&t.lparams, t.ty),
                    Decl::Defn(t) => (&t.lparams, t.ty),
                    Decl::Opaque(t) => (&t.lparams, t.ty),
                    _ => {
                        return Err(format!(
                            "the public and the private forms of {} do not agree",
                            text()
                        ));
                    }
                };
                *lp == a.lparams && ty == a.ty
            }
            _ => false,
        };
        if !ok {
            return Err(format!(
                "the public and the private forms of {} do not agree",
                text()
            ));
        }
    }
    Ok(())
}

/// Puts the inductive types, the constructors and the recursors of `items` into blocks, and orders the declarations so that each one comes after the declarations of the module that it uses.
fn order(st: &Store, items: Vec<Item>) -> Result<Vec<Decl>, Fault> {
    let units = blocks(st, items)?;
    let mut owner: BTreeMap<NameId, usize> = BTreeMap::new();
    for (i, d) in units.iter().enumerate() {
        for n in members(d) {
            owner.insert(n, i);
        }
    }
    // A depth-first walk with an explicit stack. A use of a declaration that is on the stack is a cycle. The walk does not follow it, and the checker rejects the declaration that comes first.
    let mut state = vec![0u8; units.len()];
    let mut seq = Vec::with_capacity(units.len());
    for start in 0..units.len() {
        if state[start] != 0 {
            continue;
        }
        state[start] = 1;
        let mut stack = vec![(start, uses(st, &units[start], &owner, start), 0usize)];
        while let Some((u, deps, next)) = stack.pop() {
            if next < deps.len() {
                let v = deps[next];
                stack.push((u, deps, next + 1));
                if state[v] == 0 {
                    state[v] = 1;
                    let dv = uses(st, &units[v], &owner, v);
                    stack.push((v, dv, 0));
                }
                continue;
            }
            state[u] = 2;
            seq.push(u);
        }
    }
    let mut slots: Vec<Option<Decl>> = units.into_iter().map(Some).collect();
    Ok(seq.into_iter().filter_map(|i| slots[i].take()).collect())
}

/// The names that a declaration adds.
fn members(d: &Decl) -> Vec<NameId> {
    match d {
        Decl::Induct(b) => b
            .types
            .iter()
            .map(|t| t.name)
            .chain(b.ctors.iter().map(|c| c.name))
            .chain(b.recs.iter().map(|r| r.name))
            .collect(),
        Decl::Mutual(ds) => ds.iter().map(|x| x.name).collect(),
        _ => vec![d.name()],
    }
}

/// Sorts the declarations from position `from` again, so that each declaration comes after the declarations that it uses. The sort is stable: a declaration moves only to come after a declaration that it uses. `index` gives the position of each name. A cycle is malformed.
fn resort(
    st: &Store,
    mut decls: Vec<Decl>,
    from: usize,
    index: &BTreeMap<NameId, usize>,
) -> Result<Vec<Decl>, Error> {
    let n = decls.len();
    // 0: not seen, 1: on the stack, 2: emitted.
    let mut state = vec![0u8; n];
    let mut seq = Vec::with_capacity(n - from);
    for root in from..n {
        if state[root] != 0 {
            continue;
        }
        state[root] = 1;
        let deps = |k: usize| -> Vec<usize> {
            uses(st, &decls[k], index, k)
                .into_iter()
                .filter(|&u| u >= from)
                .collect()
        };
        let mut stack: Vec<(usize, Vec<usize>, usize)> = vec![(root, deps(root), 0)];
        while let Some((k, ds, next)) = stack.last_mut() {
            if *next < ds.len() {
                let u = ds[*next];
                *next += 1;
                match state[u] {
                    0 => {
                        state[u] = 1;
                        let du = deps(u);
                        stack.push((u, du, 0));
                    }
                    1 => {
                        return Err(plain(
                            FaultKind::Malformed,
                            format!(
                                "the declarations {} and {} use each other",
                                String::from_utf8_lossy(&st.name_text(decls[*k].name())),
                                String::from_utf8_lossy(&st.name_text(decls[u].name()))
                            ),
                        ));
                    }
                    _ => {}
                }
                continue;
            }
            state[*k] = 2;
            seq.push(*k);
            stack.pop();
        }
    }
    let mut tail: Vec<Option<Decl>> = decls.drain(from..).map(Some).collect();
    for k in seq {
        if let Some(d) = tail[k - from].take() {
            decls.push(d);
        }
    }
    Ok(decls)
}

/// The type of the constant `n` of declaration `d`.
fn type_of(d: &Decl, n: NameId) -> Option<ExprId> {
    match d {
        Decl::Axiom(x) => (x.name == n).then_some(x.ty),
        Decl::Defn(x) => (x.name == n).then_some(x.ty),
        Decl::Thm(x) => (x.name == n).then_some(x.ty),
        Decl::Opaque(x) => (x.name == n).then_some(x.ty),
        Decl::Quot(x) => (x.name == n).then_some(x.ty),
        Decl::Mutual(ds) => ds.iter().find(|x| x.name == n).map(|x| x.ty),
        Decl::Induct(b) => b
            .types
            .iter()
            .find(|t| t.name == n)
            .map(|t| t.ty)
            .or_else(|| b.ctors.iter().find(|c| c.name == n).map(|c| c.ty))
            .or_else(|| b.recs.iter().find(|r| r.name == n).map(|r| r.ty)),
    }
}

/// The expressions of a declaration.
fn exprs(d: &Decl) -> Vec<ExprId> {
    match d {
        Decl::Axiom(x) => vec![x.ty],
        Decl::Defn(x) => vec![x.ty, x.value],
        Decl::Thm(x) => vec![x.ty, x.value],
        Decl::Opaque(x) => vec![x.ty, x.value],
        Decl::Quot(x) => vec![x.ty],
        Decl::Mutual(ds) => ds.iter().flat_map(|x| [x.ty, x.value]).collect(),
        Decl::Induct(b) => {
            let mut v: Vec<ExprId> = b.types.iter().map(|t| t.ty).collect();
            v.extend(b.ctors.iter().map(|c| c.ty));
            for r in &b.recs {
                v.push(r.ty);
                v.extend(r.rules.iter().map(|x| x.rhs));
            }
            v
        }
    }
}

/// The other declarations of the module that declaration `me` uses, in order of first use.
fn uses(st: &Store, d: &Decl, owner: &BTreeMap<NameId, usize>, me: usize) -> Vec<usize> {
    let mut seen: BTreeSet<ExprId> = BTreeSet::new();
    let mut found: BTreeSet<usize> = BTreeSet::new();
    let mut out = Vec::new();
    let mut stack = exprs(d);
    while let Some(e) = stack.pop() {
        if !seen.insert(e) {
            continue;
        }
        match st.node(e) {
            Expr::Const(n, _) => {
                if let Some(&u) = owner.get(&n)
                    && u != me
                    && found.insert(u)
                {
                    out.push(u);
                }
            }
            Expr::App(f, a) => {
                stack.push(a);
                stack.push(f);
            }
            Expr::Lam(b) | Expr::Pi(b) => {
                stack.push(b.body);
                stack.push(b.dom);
            }
            Expr::Let(l) => {
                stack.push(l.body);
                stack.push(l.value);
                stack.push(l.ty);
            }
            Expr::Proj(p) => {
                stack.push(p.expr);
                // A projection uses its structure type.
                if let Some(&u) = owner.get(&p.struct_name)
                    && u != me
                    && found.insert(u)
                {
                    out.push(u);
                }
            }
            Expr::FVar(_, t) => stack.push(t),
            Expr::BVar(_) | Expr::Sort(_) | Expr::Lit(_) => {}
        }
    }
    out
}

/// A position in the declarations of a module.
enum Slot {
    Decl(Decl),
    /// The inductive block with this first type.
    Induct(NameId),
    /// The block of unsafe or partial definitions with this `all` list.
    Mutual(Vec<NameId>),
}

/// Makes one `Decl` for each inductive block, at the position of the first type of the block. Each type, constructor and recursor must be in exactly one block.
///
/// An unsafe or a partial definition goes into a mutual block with the other definitions of its `all` list, at the position of the first of them. Lean adds a recursive unsafe or partial definition with `mutualDefnDecl`, and the kernel then adds all the headers before it checks the values. The olean does not keep the declaration form, so the loader uses the mutual form for each unsafe or partial definition. For a block with one definition, `add_mutual` accepts each definition that `add_definition` accepts, and also a definition that refers to itself.
fn blocks(st: &Store, items: Vec<Item>) -> Result<Vec<Decl>, Fault> {
    let text = |n: NameId| String::from_utf8_lossy(&st.name_text(n)).into_owned();
    let bad = |msg: String| Fault::new(FaultKind::Malformed, 0, msg);
    let mut types: BTreeMap<NameId, InductType> = BTreeMap::new();
    let mut ctors = BTreeMap::new();
    let mut recs: BTreeMap<NameId, Vec<Rec>> = BTreeMap::new();
    let mut heads = Vec::new();
    let mut mutual: BTreeMap<Vec<NameId>, Vec<Defn>> = BTreeMap::new();
    // The position of each declaration and each block in the module.
    let mut seq: Vec<Slot> = Vec::new();
    for it in items {
        match it {
            Item::Decl(Decl::Defn(d)) if d.safety != Safety::Safe => {
                if !d.all.contains(&d.name) {
                    return Err(bad(format!(
                        "the definition {} is not in its own `all` list",
                        text(d.name)
                    )));
                }
                let key = d.all.clone();
                if !mutual.contains_key(&key) {
                    seq.push(Slot::Mutual(key.clone()));
                }
                mutual.entry(key).or_default().push(d);
            }
            Item::Decl(d) => seq.push(Slot::Decl(d)),
            Item::Type(t) => {
                if t.all.is_empty() {
                    return Err(bad(format!(
                        "the inductive type {} has an empty `all` list",
                        text(t.name)
                    )));
                }
                if t.all[0] == t.name {
                    heads.push(t.name);
                    seq.push(Slot::Induct(t.name));
                }
                types.insert(t.name, t);
            }
            Item::Ctor(c) => {
                ctors.insert(c.name, c);
            }
            Item::Rec(r) => {
                let key = match r.all.first() {
                    Some(&k) => k,
                    None => {
                        return Err(bad(format!(
                            "the recursor {} has an empty `all` list",
                            text(r.name)
                        )));
                    }
                };
                recs.entry(key).or_default().push(r);
            }
        }
    }
    let mut made: BTreeMap<NameId, Induct> = BTreeMap::new();
    for h in heads {
        let all = types[&h].all.clone();
        let mut b = Induct {
            types: Vec::new(),
            ctors: Vec::new(),
            recs: Vec::new(),
        };
        for n in &all {
            let t = types.remove(n).ok_or_else(|| {
                bad(format!(
                    "the inductive type {} of the block of {} is missing",
                    text(*n),
                    text(h)
                ))
            })?;
            if t.all != all {
                return Err(bad(format!(
                    "the inductive type {} does not agree with its block on `all`",
                    text(*n)
                )));
            }
            for c in &t.ctors {
                let x = ctors.remove(c).ok_or_else(|| {
                    bad(format!(
                        "the constructor {} of {} is missing",
                        text(*c),
                        text(*n)
                    ))
                })?;
                b.ctors.push(x);
            }
            b.types.push(t);
        }
        for r in recs.remove(&h).unwrap_or_default() {
            if r.all != all {
                return Err(bad(format!(
                    "the recursor {} does not agree with its block on `all`",
                    text(r.name)
                )));
            }
            b.recs.push(r);
        }
        made.insert(h, b);
    }
    if let Some(n) = types.keys().next() {
        return Err(bad(format!(
            "the inductive type {} is not in the block of its first type",
            text(*n)
        )));
    }
    if let Some(n) = ctors.keys().next() {
        return Err(bad(format!(
            "the constructor {} is not a constructor of an inductive type of the module",
            text(*n)
        )));
    }
    if let Some(rs) = recs.values().next() {
        return Err(bad(format!(
            "the recursor {} has no inductive block in the module",
            text(rs[0].name)
        )));
    }
    let mut out = Vec::with_capacity(seq.len());
    for x in seq {
        match x {
            Slot::Decl(d) => out.push(d),
            Slot::Induct(h) => out.extend(made.remove(&h).map(Decl::Induct)),
            Slot::Mutual(all) => {
                let mut ds = mutual.remove(&all).unwrap_or_default();
                // The members follow the order of `all`, and each name of `all` must be a member once.
                ds.sort_by_key(|d| all.iter().position(|n| *n == d.name));
                let names: Vec<NameId> = ds.iter().map(|d| d.name).collect();
                if names != all {
                    return Err(bad(format!(
                        "the definitions of the mutual block of {} do not agree with its `all` list",
                        text(all[0])
                    )));
                }
                out.push(Decl::Mutual(ds));
            }
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rulean_format::{Axiom, Ctor, Thm};
    use rulean_store::LevelListId;

    fn name(st: &mut Store, s: &str) -> NameId {
        st.name_str_bytes(NameId(0), s.as_bytes())
    }

    /// `Sort 0`, and the constant `n` with no levels.
    fn prop(st: &mut Store) -> ExprId {
        let z = st.level_zero();
        st.mk_sort(z)
    }

    fn cnst(st: &mut Store, n: NameId) -> ExprId {
        st.mk_const(n, LevelListId(0))
    }

    fn axiom(n: NameId, ty: ExprId) -> Decl {
        Decl::Axiom(Axiom {
            name: n,
            lparams: vec![],
            ty,
            safety: Safety::Safe,
        })
    }

    #[test]
    fn a_declaration_comes_after_the_declarations_that_it_uses() {
        let mut st = Store::new();
        let (a, b, c) = (name(&mut st, "a"), name(&mut st, "b"), name(&mut st, "c"));
        let p = prop(&mut st);
        let ta = cnst(&mut st, a);
        let tb = cnst(&mut st, b);
        let items = vec![
            Item::Decl(axiom(c, tb)),
            Item::Decl(axiom(b, ta)),
            Item::Decl(axiom(a, p)),
        ];
        let got: Vec<NameId> = order(&st, items)
            .expect("order")
            .iter()
            .map(|d| d.name())
            .collect();
        assert_eq!(got, vec![a, b, c]);
    }

    fn ind(st: &mut Store) -> (Vec<Item>, NameId) {
        let t = name(st, "T");
        let k = st.name_str_bytes(t, b"mk");
        let r = st.name_str_bytes(t, b"rec");
        let ty = prop(st);
        let tk = cnst(st, t);
        let ty_t = InductType {
            name: t,
            lparams: vec![],
            ty,
            num_params: 0,
            num_indices: 0,
            all: vec![t],
            ctors: vec![k],
            num_nested: 0,
            is_rec: false,
            is_reflexive: false,
            safety: Safety::Safe,
        };
        let ctor = Ctor {
            name: k,
            lparams: vec![],
            ty: tk,
            induct: t,
            cidx: 0,
            num_params: 0,
            num_fields: 0,
            safety: Safety::Safe,
        };
        let rec = Rec {
            name: r,
            lparams: vec![],
            ty,
            all: vec![t],
            num_params: 0,
            num_indices: 0,
            num_motives: 1,
            num_minors: 1,
            k: true,
            rules: vec![],
            safety: Safety::Safe,
        };
        (vec![Item::Rec(rec), Item::Ctor(ctor), Item::Type(ty_t)], k)
    }

    fn partial(n: NameId, all: &[NameId], ty: ExprId, value: ExprId) -> Item {
        Item::Decl(Decl::Defn(Defn {
            name: n,
            lparams: vec![],
            ty,
            value,
            hints: rulean_format::Hints::Opaque,
            safety: Safety::Partial,
            all: all.to_vec(),
        }))
    }

    #[test]
    fn partial_definitions_of_one_block_make_one_mutual_declaration() {
        let mut st = Store::new();
        let (f, g, h) = (name(&mut st, "f"), name(&mut st, "g"), name(&mut st, "h"));
        let p = prop(&mut st);
        let tf = cnst(&mut st, f);
        let tg = cnst(&mut st, g);
        let items = vec![
            partial(g, &[f, g], p, tf),
            Item::Decl(axiom(h, p)),
            partial(f, &[f, g], p, tg),
        ];
        let ds = blocks(&st, items).expect("blocks");
        assert_eq!(ds.len(), 2);
        let Decl::Mutual(m) = &ds[0] else {
            panic!("not a mutual block")
        };
        let names: Vec<NameId> = m.iter().map(|d| d.name).collect();
        assert_eq!(names, vec![f, g]);
        assert_eq!(ds[1].name(), h);
        // A safe definition stays a definition.
        let mut safe = partial(h, &[h], p, p);
        if let Item::Decl(Decl::Defn(d)) = &mut safe {
            d.safety = Safety::Safe;
        }
        let ds = blocks(&st, vec![safe]).expect("blocks");
        assert!(matches!(ds[0], Decl::Defn(_)));
    }

    #[test]
    fn a_mutual_block_with_a_missing_definition_is_malformed() {
        let mut st = Store::new();
        let (f, g) = (name(&mut st, "f"), name(&mut st, "g"));
        let p = prop(&mut st);
        let e = blocks(&st, vec![partial(f, &[f, g], p, p)]).expect_err("g is missing");
        assert_eq!(e.kind, FaultKind::Malformed);
        let e = blocks(&st, vec![partial(f, &[g], p, p)]).expect_err("f is not in its block");
        assert_eq!(e.kind, FaultKind::Malformed);
        let two = vec![partial(f, &[f], p, p), partial(f, &[f], p, p)];
        let e = blocks(&st, two).expect_err("f is in its block two times");
        assert_eq!(e.kind, FaultKind::Malformed);
    }

    #[test]
    fn an_inductive_block_has_its_types_constructors_and_recursors() {
        let mut st = Store::new();
        let (items, _) = ind(&mut st);
        let ds = blocks(&st, items).expect("blocks");
        assert_eq!(ds.len(), 1);
        let Decl::Induct(b) = &ds[0] else {
            panic!("not a block")
        };
        assert_eq!((b.types.len(), b.ctors.len(), b.recs.len()), (1, 1, 1));
    }

    #[test]
    fn a_constructor_without_its_type_is_malformed() {
        let mut st = Store::new();
        let (mut items, _) = ind(&mut st);
        items.retain(|i| matches!(i, Item::Ctor(_)));
        let e = blocks(&st, items).expect_err("a lone constructor");
        assert_eq!(e.kind, FaultKind::Malformed);
    }

    #[test]
    fn a_missing_constructor_is_malformed() {
        let mut st = Store::new();
        let (mut items, _) = ind(&mut st);
        items.retain(|i| !matches!(i, Item::Ctor(_)));
        assert!(blocks(&st, items).is_err());
    }

    fn thm(n: NameId, ty: ExprId, value: ExprId) -> Decl {
        Decl::Thm(Thm {
            name: n,
            lparams: vec![],
            ty,
            value,
            all: vec![n],
        })
    }

    #[test]
    fn a_public_axiom_can_hide_a_private_theorem() {
        let mut st = Store::new();
        let (a, h) = (name(&mut st, "a"), name(&mut st, "h"));
        let p = prop(&mut st);
        let ta = cnst(&mut st, a);
        let public = vec![Item::Decl(axiom(a, p)), Item::Decl(axiom(h, ta))];
        let private = vec![Item::Decl(axiom(a, p)), Item::Decl(thm(h, ta, ta))];
        assert_eq!(same_public(&st, &public, &private), Ok(()));
        let other = vec![Item::Decl(axiom(a, p)), Item::Decl(thm(h, p, ta))];
        assert!(same_public(&st, &public, &other).is_err());
        let short = vec![Item::Decl(axiom(a, p))];
        assert!(same_public(&st, &public, &short).is_err());
        let changed = vec![Item::Decl(axiom(a, ta)), Item::Decl(thm(h, ta, ta))];
        assert!(same_public(&st, &public, &changed).is_err());
    }

    fn loader<'a>(st: &'a mut Store) -> Loader<'a> {
        Loader {
            st,
            search: &[],
            mem: None,
            out: Loaded {
                decls: Vec::new(),
                lean_version: Vec::new(),
                githash: Vec::new(),
                version: 0,
                modules: Vec::new(),
                files: Vec::new(),
                objects: 0,
                sha256: [0; 32],
            },
            first: true,
            hash: Hasher::new(),
            resort: None,
        }
    }

    #[test]
    fn a_later_theorem_with_the_same_statement_replaces_the_first() {
        let mut st = Store::new();
        let (a, h, q) = (name(&mut st, "a"), name(&mut st, "h"), name(&mut st, "q"));
        let p = prop(&mut st);
        let ta = cnst(&mut st, a);
        let tq = cnst(&mut st, q);
        let mut l = loader(&mut st);
        let mut index = BTreeMap::new();
        l.add("A", axiom(q, p), &mut index).expect("q");
        l.add("A", thm(h, tq, ta), &mut index).expect("first");
        l.add("B", thm(h, tq, tq), &mut index)
            .expect("same statement");
        assert_eq!(l.out.decls.len(), 2);
        assert_eq!(l.out.decls[1], thm(h, tq, tq));
        let e = l
            .add("E", thm(h, p, tq), &mut index)
            .expect_err("different statement");
        assert_eq!(e.kind, FaultKind::Malformed);
        // An axiom with a type `q`, where `q : Prop`, can occur two times, and a theorem replaces it.
        l.add("A", axiom(a, tq), &mut index).expect("axiom");
        l.add("C", axiom(a, tq), &mut index).expect("equal axiom");
        l.add("D", thm(a, tq, tq), &mut index).expect("theorem");
        assert_eq!(l.out.decls[2], thm(a, tq, tq));
        // The axiom does not replace the theorem, and the theorem stays.
        l.add("F", axiom(a, tq), &mut index)
            .expect("axiom after theorem");
        assert_eq!(l.out.decls[2], thm(a, tq, tq));
        assert_eq!(l.out.decls.len(), 3);
        // The type of `q` is not a proposition, so `q` cannot occur two times.
        let e = l
            .add("G", axiom(q, p), &mut index)
            .expect_err("axiom of type Prop");
        assert_eq!(e.kind, FaultKind::Malformed);
    }

    #[test]
    fn a_replacement_that_uses_a_later_declaration_moves_after_it() {
        let mut st = Store::new();
        let (h, q, z, w) = (
            name(&mut st, "h"),
            name(&mut st, "q"),
            name(&mut st, "z"),
            name(&mut st, "w"),
        );
        let p = prop(&mut st);
        let tq = cnst(&mut st, q);
        let tz = cnst(&mut st, z);
        let th = cnst(&mut st, h);
        let mut l = loader(&mut st);
        let mut index = BTreeMap::new();
        l.add("A", axiom(q, p), &mut index).expect("q");
        l.add("A", thm(h, tq, tq), &mut index).expect("first");
        l.add("A", thm(w, tq, th), &mut index).expect("w uses h");
        l.add("B", axiom(z, tq), &mut index).expect("z");
        l.add("B", thm(h, tq, tz), &mut index).expect("uses z");
        assert_eq!(l.resort, Some(1));
        let st = &*l.st;
        let decls = resort(st, l.out.decls, 1, &index).expect("sort");
        let order: Vec<NameId> = decls.iter().map(Decl::name).collect();
        assert_eq!(order, vec![q, z, h, w]);
        assert_eq!(decls[2], thm(h, tq, tz));
    }

    #[test]
    fn a_cycle_after_a_replacement_is_malformed() {
        let mut st = Store::new();
        let (h, q, z) = (name(&mut st, "h"), name(&mut st, "q"), name(&mut st, "z"));
        let p = prop(&mut st);
        let tq = cnst(&mut st, q);
        let tz = cnst(&mut st, z);
        let th = cnst(&mut st, h);
        let mut l = loader(&mut st);
        let mut index = BTreeMap::new();
        l.add("A", axiom(q, p), &mut index).expect("q");
        l.add("A", thm(h, tq, tq), &mut index).expect("first");
        l.add("B", thm(z, tq, th), &mut index).expect("z uses h");
        l.add("B", thm(h, tq, tz), &mut index).expect("h uses z");
        let st = &*l.st;
        let e = resort(st, l.out.decls, 1, &index).expect_err("cycle");
        assert_eq!(e.kind, FaultKind::Malformed);
    }

    #[test]
    fn a_missing_module_is_reported() {
        let mut st = Store::new();
        let dir = std::env::temp_dir().join("rulean-olean-no-such-dir");
        let e = load(&mut st, &["No.Such.Module".to_owned()], &[dir]).expect_err("missing");
        assert_eq!(e.kind, FaultKind::Missing);
    }

    #[test]
    fn module_paths_stay_below_the_directory() {
        let d = Path::new("/lib");
        assert_eq!(
            module_path(d, "Init.Prelude"),
            Some(PathBuf::from("/lib/Init/Prelude.olean"))
        );
        assert_eq!(module_path(d, "Init..Prelude"), None);
        assert_eq!(module_path(d, "Init.../x"), None);
        assert_eq!(module_path(d, "a/b"), None);
        assert_eq!(module_path(d, ""), None);
    }
}
