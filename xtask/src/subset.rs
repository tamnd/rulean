//! The Aeneas subset lint of spec section 10.6.
//!
//! The lint reads the source of each core crate with `syn` and reports the forms that Charon and Aeneas do not translate, or translate badly. It works on syntax only. It does not know types, so a few rules are close approximations. The extraction job is the final check.
//!
//! Code under `#[cfg(test)]` and `#[test]` functions is not extracted, so the lint skips it.

use std::path::{Path, PathBuf};

use syn::spanned::Spanned;
use syn::visit::{self, Visit};

use crate::metadata::{self, Layer};

/// The largest function, in lines (spec 10.6, findings F12).
pub const MAX_FN_LINES: usize = 300;

/// The longest `if` / `else if` chain, in branches (spec 10.6, finding F19).
pub const MAX_ELSE_IF: usize = 4;

/// Types with interior mutability or shared ownership.
const SHARED: &[&str] = &[
    "Cell",
    "RefCell",
    "UnsafeCell",
    "OnceCell",
    "Rc",
    "Arc",
    "Weak",
    "Mutex",
    "RwLock",
];

/// Collection types of `std` and `alloc` other than `Vec`.
const COLLECTIONS: &[&str] = &[
    "HashMap",
    "HashSet",
    "BTreeMap",
    "BTreeSet",
    "VecDeque",
    "BinaryHeap",
    "LinkedList",
];

/// `Vec` and slice methods outside the modelled set (push, pop, index, len, with_capacity, truncate). The lint cannot see the receiver type, so it reports these names on any receiver.
const VEC_METHODS: &[&str] = &[
    "insert",
    "remove",
    "swap_remove",
    "drain",
    "retain",
    "retain_mut",
    "dedup",
    "dedup_by",
    "dedup_by_key",
    "append",
    "split_off",
    "extend",
    "extend_from_slice",
    "resize",
    "resize_with",
    "splice",
    "sort",
    "sort_by",
    "sort_by_key",
    "sort_unstable",
    "sort_unstable_by",
    "sort_unstable_by_key",
];

/// One break of the subset.
#[derive(Debug, PartialEq, Eq)]
pub struct Finding {
    pub file: PathBuf,
    pub line: usize,
    pub rule: &'static str,
    pub message: String,
}

impl std::fmt::Display for Finding {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}:{}: [{}] {}",
            self.file.display(),
            self.line,
            self.rule,
            self.message
        )
    }
}

pub fn run() -> Result<(), Vec<String>> {
    let members = metadata::members()?;
    let mut problems = Vec::new();
    let mut files = 0;
    for m in members.iter().filter(|m| m.layer == Some(Layer::Core)) {
        let Some(root) = &m.lib_root else {
            problems.push(format!("{}: no library root", m.name));
            continue;
        };
        match std::fs::read_to_string(root) {
            Ok(text) if has_forbid_unsafe(&text) => {}
            Ok(_) => problems.push(format!(
                "{}: [S1] a core crate must declare #![forbid(unsafe_code)]",
                root.display()
            )),
            Err(e) => problems.push(format!("{}: {e}", root.display())),
        }
        let dir = root.parent().map(Path::to_path_buf).unwrap_or_default();
        for file in rust_files(&dir) {
            files += 1;
            match std::fs::read_to_string(&file) {
                Ok(text) => match lint_source(&file, &text) {
                    Ok(found) => problems.extend(found.iter().map(ToString::to_string)),
                    Err(e) => problems.push(format!("{}: cannot parse: {e}", file.display())),
                },
                Err(e) => problems.push(format!("{}: {e}", file.display())),
            }
        }
    }
    if problems.is_empty() {
        println!("subset: {files} files of the core crates are in the Aeneas subset");
        Ok(())
    } else {
        Err(problems)
    }
}

fn has_forbid_unsafe(text: &str) -> bool {
    text.lines().any(|l| l.trim() == "#![forbid(unsafe_code)]")
}

fn rust_files(dir: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&d) else {
            continue;
        };
        for e in entries.filter_map(Result::ok) {
            let p = e.path();
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().is_some_and(|x| x == "rs") {
                out.push(p);
            }
        }
    }
    out.sort();
    out
}

/// Lints one source file. The path is only used in the findings.
pub fn lint_source(file: &Path, text: &str) -> Result<Vec<Finding>, syn::Error> {
    let ast = syn::parse_file(text)?;
    let mut v = Lint {
        file: file.to_path_buf(),
        found: Vec::new(),
        loop_depth: 0,
    };
    v.visit_file(&ast);
    Ok(v.found)
}

struct Lint {
    file: PathBuf,
    found: Vec<Finding>,
    loop_depth: usize,
}

impl Lint {
    fn report(&mut self, span: proc_macro2::Span, rule: &'static str, message: impl Into<String>) {
        self.found.push(Finding {
            file: self.file.clone(),
            line: span.start().line,
            rule,
            message: message.into(),
        });
    }

    fn check_fn_length(&mut self, span: proc_macro2::Span, name: &syn::Ident) {
        let lines = span.end().line.saturating_sub(span.start().line) + 1;
        if lines > MAX_FN_LINES {
            self.report(
                span,
                "S12",
                format!("function `{name}` has {lines} lines, more than {MAX_FN_LINES}"),
            );
        }
    }

    /// A path segment or a `use` item that names a banned type or module.
    fn check_name(&mut self, ident: &syn::Ident) {
        let name = ident.to_string();
        if SHARED.contains(&name.as_str()) {
            self.report(
                ident.span(),
                "S5",
                format!("`{name}`: no interior mutability or shared ownership"),
            );
        } else if COLLECTIONS.contains(&name.as_str()) || name == "collections" {
            self.report(
                ident.span(),
                "S6",
                format!("`{name}`: use `rulean_store::Table`"),
            );
        }
    }

    fn with_loop(&mut self, f: impl FnOnce(&mut Self)) {
        self.loop_depth += 1;
        f(self);
        self.loop_depth -= 1;
    }

    /// Field types of a struct or an enum variant: no reference (F18) and no `&'static str` (F7).
    fn check_fields(&mut self, fields: &syn::Fields) {
        for field in fields {
            if let syn::Type::Reference(r) = &field.ty {
                if is_static_str(r) {
                    self.report(
                        r.span(),
                        "S14",
                        "`&'static str` in a data type; use bytes or an index",
                    );
                } else {
                    self.report(
                        r.span(),
                        "S11",
                        "a reference in a data type; pass it as a parameter",
                    );
                }
            }
        }
    }
}

fn is_test_only(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|a| {
        let path = a.path();
        if path.is_ident("test") {
            return true;
        }
        if path.is_ident("cfg") {
            let mut test = false;
            let _ = a.parse_nested_meta(|meta| {
                if meta.path.is_ident("test") {
                    test = true;
                }
                Ok(())
            });
            return test;
        }
        false
    })
}

fn is_static_str(r: &syn::TypeReference) -> bool {
    let static_lt = r.lifetime.as_ref().is_some_and(|l| l.ident == "static");
    let is_str = matches!(&*r.elem, syn::Type::Path(p) if p.path.is_ident("str"));
    static_lt && is_str
}

fn else_if_len(e: &syn::ExprIf) -> usize {
    let mut n = 1;
    let mut cur = e;
    while let Some((_, els)) = &cur.else_branch {
        match &**els {
            syn::Expr::If(next) => {
                n += 1;
                cur = next;
            }
            _ => break,
        }
    }
    n
}

impl<'ast> Visit<'ast> for Lint {
    fn visit_item_mod(&mut self, i: &'ast syn::ItemMod) {
        if !is_test_only(&i.attrs) {
            visit::visit_item_mod(self, i);
        }
    }

    fn visit_item_fn(&mut self, i: &'ast syn::ItemFn) {
        if is_test_only(&i.attrs) {
            return;
        }
        if i.sig.unsafety.is_some() {
            self.report(i.sig.span(), "S1", "an `unsafe fn`");
        }
        self.check_fn_length(i.span(), &i.sig.ident);
        visit::visit_item_fn(self, i);
    }

    fn visit_impl_item_fn(&mut self, i: &'ast syn::ImplItemFn) {
        if is_test_only(&i.attrs) {
            return;
        }
        if i.sig.unsafety.is_some() {
            self.report(i.sig.span(), "S1", "an `unsafe fn`");
        }
        self.check_fn_length(i.span(), &i.sig.ident);
        visit::visit_impl_item_fn(self, i);
    }

    fn visit_item_impl(&mut self, i: &'ast syn::ItemImpl) {
        if is_test_only(&i.attrs) {
            return;
        }
        if i.unsafety.is_some() {
            self.report(i.span(), "S1", "an `unsafe impl`");
        }
        visit::visit_item_impl(self, i);
    }

    fn visit_item_trait(&mut self, i: &'ast syn::ItemTrait) {
        if i.unsafety.is_some() {
            self.report(i.span(), "S1", "an `unsafe trait`");
        }
        visit::visit_item_trait(self, i);
    }

    fn visit_item_struct(&mut self, i: &'ast syn::ItemStruct) {
        if is_test_only(&i.attrs) {
            return;
        }
        self.check_fields(&i.fields);
        visit::visit_item_struct(self, i);
    }

    fn visit_item_enum(&mut self, i: &'ast syn::ItemEnum) {
        if is_test_only(&i.attrs) {
            return;
        }
        for v in &i.variants {
            self.check_fields(&v.fields);
        }
        visit::visit_item_enum(self, i);
    }

    fn visit_expr_unsafe(&mut self, i: &'ast syn::ExprUnsafe) {
        self.report(i.span(), "S1", "an `unsafe` block");
        visit::visit_expr_unsafe(self, i);
    }

    fn visit_expr_closure(&mut self, i: &'ast syn::ExprClosure) {
        self.report(i.span(), "S2", "a closure; use an enum and a `match`");
        visit::visit_expr_closure(self, i);
    }

    fn visit_type_trait_object(&mut self, i: &'ast syn::TypeTraitObject) {
        self.report(i.span(), "S3", "a `dyn` trait object");
        visit::visit_type_trait_object(self, i);
    }

    fn visit_type_bare_fn(&mut self, i: &'ast syn::TypeBareFn) {
        self.report(i.span(), "S4", "a function pointer type");
        visit::visit_type_bare_fn(self, i);
    }

    fn visit_path(&mut self, i: &'ast syn::Path) {
        for seg in &i.segments {
            self.check_name(&seg.ident);
        }
        visit::visit_path(self, i);
    }

    fn visit_use_path(&mut self, i: &'ast syn::UsePath) {
        self.check_name(&i.ident);
        visit::visit_use_path(self, i);
    }

    fn visit_use_name(&mut self, i: &'ast syn::UseName) {
        self.check_name(&i.ident);
        visit::visit_use_name(self, i);
    }

    fn visit_use_rename(&mut self, i: &'ast syn::UseRename) {
        self.check_name(&i.ident);
        visit::visit_use_rename(self, i);
    }

    fn visit_expr_method_call(&mut self, i: &'ast syn::ExprMethodCall) {
        let name = i.method.to_string();
        if VEC_METHODS.contains(&name.as_str()) {
            self.report(
                i.method.span(),
                "S7",
                format!("`.{name}()` is outside the modelled `Vec` methods"),
            );
        }
        visit::visit_expr_method_call(self, i);
    }

    fn visit_expr_try(&mut self, i: &'ast syn::ExprTry) {
        self.report(
            i.question_token.span,
            "S8",
            "the `?` operator; use an explicit `match`",
        );
        visit::visit_expr_try(self, i);
    }

    fn visit_expr_while(&mut self, i: &'ast syn::ExprWhile) {
        self.visit_expr(&i.cond);
        self.with_loop(|v| v.visit_block(&i.body));
    }

    fn visit_expr_loop(&mut self, i: &'ast syn::ExprLoop) {
        self.with_loop(|v| v.visit_block(&i.body));
    }

    fn visit_expr_for_loop(&mut self, i: &'ast syn::ExprForLoop) {
        self.visit_expr(&i.expr);
        self.with_loop(|v| v.visit_block(&i.body));
    }

    fn visit_expr_return(&mut self, i: &'ast syn::ExprReturn) {
        if self.loop_depth > 0 {
            self.report(
                i.span(),
                "S9",
                "a `return` inside a loop; move the loop into its own function",
            );
        }
        visit::visit_expr_return(self, i);
    }

    fn visit_expr_break(&mut self, i: &'ast syn::ExprBreak) {
        if i.label.is_some() {
            self.report(i.span(), "S9", "a `break` to a labelled loop");
        }
        visit::visit_expr_break(self, i);
    }

    fn visit_expr_continue(&mut self, i: &'ast syn::ExprContinue) {
        if i.label.is_some() {
            self.report(i.span(), "S9", "a `continue` to a labelled loop");
        }
        visit::visit_expr_continue(self, i);
    }

    fn visit_expr_if(&mut self, i: &'ast syn::ExprIf) {
        let n = else_if_len(i);
        if n > MAX_ELSE_IF {
            self.report(
                i.span(),
                "S13",
                format!("an `else if` chain of {n} branches; use a `match`"),
            );
        }
        // Visit the condition and the branches, but count a chain only once, from its head.
        self.visit_expr(&i.cond);
        self.visit_block(&i.then_branch);
        let mut els = i.else_branch.as_ref().map(|(_, e)| &**e);
        while let Some(e) = els {
            match e {
                syn::Expr::If(next) => {
                    self.visit_expr(&next.cond);
                    self.visit_block(&next.then_branch);
                    els = next.else_branch.as_ref().map(|(_, e)| &**e);
                }
                other => {
                    self.visit_expr(other);
                    els = None;
                }
            }
        }
    }

    fn visit_type_path(&mut self, i: &'ast syn::TypePath) {
        for seg in &i.path.segments {
            if let syn::PathArguments::AngleBracketed(args) = &seg.arguments {
                for a in &args.args {
                    if let syn::GenericArgument::Type(syn::Type::Reference(r)) = a {
                        self.report(
                            r.span(),
                            "S10",
                            format!("a borrow inside `{}<..>`", seg.ident),
                        );
                    }
                }
            }
        }
        visit::visit_type_path(self, i);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rules(src: &str) -> Vec<&'static str> {
        lint_source(Path::new("t.rs"), src)
            .expect("parse")
            .into_iter()
            .map(|f| f.rule)
            .collect()
    }

    #[test]
    fn clean_code_passes() {
        let src = r#"
            pub struct Store { nodes: Vec<u32> }
            pub enum Kind { App, Lam }
            impl Store {
                pub fn push(&mut self, n: u32) -> usize { self.nodes.push(n); self.nodes.len() }
                pub fn get(&self, i: usize) -> Option<u32> {
                    if i < self.nodes.len() { Some(self.nodes[i]) } else { None }
                }
            }
            pub fn sum(xs: &[u32]) -> u64 {
                let mut i = 0; let mut s = 0u64;
                while i < xs.len() { s += xs[i] as u64; i += 1; }
                s
            }
        "#;
        assert_eq!(rules(src), Vec::<&str>::new());
    }

    #[test]
    fn each_rule_fires() {
        let cases: &[(&str, &str)] = &[
            ("fn f() { unsafe { } }", "S1"),
            ("unsafe fn f() {}", "S1"),
            ("fn f() { let g = |x: u8| x; }", "S2"),
            ("fn f(x: &dyn Fn()) {}", "S3"),
            ("fn f(x: fn(u8) -> u8) {}", "S4"),
            ("fn f(x: Rc<u8>) {}", "S5"),
            ("fn f(x: RefCell<u8>) {}", "S5"),
            ("use alloc::collections::BTreeMap;", "S6"),
            ("use alloc::collections::{BTreeMap as M};", "S6"),
            ("fn f(x: HashMap<u8, u8>) {}", "S6"),
            ("fn f(v: &mut Vec<u8>) { v.insert(0, 1); }", "S7"),
            (
                "fn f(x: Option<u8>) -> Option<u8> { let y = x?; Some(y) }",
                "S8",
            ),
            ("fn f() -> u8 { loop { return 1; } }", "S9"),
            ("fn f() { 'a: loop { loop { break 'a; } } }", "S9"),
            ("fn f(x: Option<&u8>) {}", "S10"),
            ("struct R<'a> { bytes: &'a [u8] }", "S11"),
            ("enum E { S(&'static str) }", "S14"),
            (
                "fn f(t: u8) -> u8 { if t == 0 { 0 } else if t == 1 { 1 } else if t == 2 { 2 } else if t == 3 { 3 } else if t == 4 { 4 } else { 5 } }",
                "S13",
            ),
        ];
        for (src, rule) in cases {
            let mut found = rules(src);
            found.dedup();
            assert_eq!(found, vec![*rule], "{src}");
        }
    }

    #[test]
    fn a_short_else_if_chain_passes() {
        let src = "fn f(t: u8) -> u8 { if t == 0 { 0 } else if t == 1 { 1 } else if t == 2 { 2 } else { 3 } }";
        assert!(rules(src).is_empty());
    }

    #[test]
    fn a_return_outside_a_loop_passes() {
        assert!(rules("fn f(x: u8) -> u8 { if x == 0 { return 1; } x }").is_empty());
    }

    #[test]
    fn a_long_function_fires() {
        let body = "    let _x = 0;\n".repeat(MAX_FN_LINES);
        let src = format!("fn f() {{\n{body}}}\n");
        assert_eq!(rules(&src), vec!["S12"]);
    }

    #[test]
    fn test_code_is_skipped() {
        let src = r#"
            #[cfg(test)]
            mod tests { fn f() { let g = |x: u8| x; } }
            #[test]
            fn t() { let v: Vec<u8> = Vec::new(); let _ = v.iter().map(|x| x + 1); }
        "#;
        assert!(rules(src).is_empty());
    }

    #[test]
    fn findings_have_line_numbers() {
        let src = "fn f() {}\n\nfn g() { let h = |x: u8| x; }\n";
        let found = lint_source(Path::new("t.rs"), src).expect("parse");
        assert_eq!(found.len(), 1);
        assert_eq!(found[0].line, 3);
    }
}
