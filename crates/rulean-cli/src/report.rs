//! The result of `rulean check` and its two output forms: one line of text and the JSON report of spec 09.4.
//!
//! The JSON text is written by hand, so the CLI has no JSON dependency. The schema is in `docs/report.schema.json`. Fields are only added, and a change of a field changes the schema version.

use rulean_core::conv::{Engine, FStats};

use crate::exit::Code;

/// The schema version of the report.
pub const SCHEMA: &str = "rulean-report/1";

/// The facts of one `check` run.
#[derive(Debug, Default)]
pub struct Report {
    pub code: Code,
    pub input_path: String,
    pub sha256: String,
    pub format_version: String,
    pub lean_version: String,
    pub profile: Option<&'static str>,
    pub declarations: usize,
    pub accepted: usize,
    pub rejected: usize,
    pub failed_decl: Option<String>,
    pub error: Option<String>,
    pub quarantine: Vec<String>,
    pub pin_mismatch: Vec<String>,
    pub deviations: Vec<&'static str>,
    pub wall_ms: u128,
    pub engine: Engine,
    pub confirm_all: bool,
    pub f_stats: FStats,
}

/// The one line of text for standard output.
pub fn text(r: &Report) -> String {
    let w = r.code.word();
    let p = &r.input_path;
    let mut s = match &r.error {
        Some(e) => format!("{w}: {p}: {e}"),
        None => format!(
            "{w}: {p}: {} declarations, {} in quarantine, {} ms",
            r.accepted,
            r.quarantine.len(),
            r.wall_ms
        ),
    };
    if !r.pin_mismatch.is_empty() {
        s.push_str(&format!("\npin mismatch: {}", r.pin_mismatch.join(", ")));
    }
    s
}

/// The JSON report.
pub fn json(r: &Report) -> String {
    let mut s = String::new();
    s.push_str("{\n");
    s.push_str(&format!("  \"schema\": {},\n", quote(SCHEMA)));
    s.push_str(&format!(
        "  \"tool\": {{ \"rulean\": {}, \"build\": \"unverified\" }},\n",
        quote(env!("CARGO_PKG_VERSION"))
    ));
    let format = if r.format_version.is_empty() {
        "ndjson".to_owned()
    } else {
        format!("ndjson-{}", r.format_version)
    };
    s.push_str(&format!(
        "  \"input\": {{ \"path\": {}, \"format\": {}, \"sha256\": {}, \"lean_version\": {}, \"profile\": {} }},\n",
        quote(&r.input_path),
        quote(&format),
        quote(&r.sha256),
        quote(&r.lean_version),
        match r.profile {
            Some(p) => quote(p),
            None => "null".to_owned(),
        }
    ));
    s.push_str(&format!("  \"verdict\": {},\n", quote(r.code.word())));
    s.push_str(&format!("  \"exit_code\": {},\n", r.code.value()));
    s.push_str(&format!(
        "  \"error\": {},\n",
        match &r.error {
            Some(e) => quote(e),
            None => "null".to_owned(),
        }
    ));
    s.push_str(&format!(
        "  \"failed_decl\": {},\n",
        match &r.failed_decl {
            Some(e) => quote(e),
            None => "null".to_owned(),
        }
    ));
    s.push_str(&format!(
        "  \"summary\": {{ \"declarations\": {}, \"accepted\": {}, \"rejected\": {}, \"quarantine\": {}, \"deviations\": {}, \"wall_ms\": {} }},\n",
        r.declarations,
        r.accepted,
        r.rejected,
        r.quarantine.len(),
        list(&r.deviations),
        r.wall_ms
    ));
    s.push_str(&format!("  \"quarantine\": {},\n", list(&r.quarantine)));
    s.push_str(&format!("  \"pin_mismatch\": {},\n", list(&r.pin_mismatch)));
    let f = &r.f_stats;
    s.push_str(&format!(
        "  \"engine\": {{ \"engine\": {}, \"confirm\": {}, \"f_queries\": {}, \"f_equal\": {}, \"f_fallback\": {}, \"f_faults\": {}, \"r_confirmed\": {}, \"r_disagree\": {} }}\n",
        quote(match r.engine {
            Engine::F => "F",
            Engine::R => "R",
        }),
        quote(if r.confirm_all { "all" } else { "default" }),
        f.queries,
        f.equal,
        f.fallback,
        f.faults,
        f.confirmed,
        f.disagree
    ));
    s.push('}');
    s
}

/// A JSON array of strings.
fn list<T: AsRef<str>>(xs: &[T]) -> String {
    let mut s = String::from("[");
    for (i, x) in xs.iter().enumerate() {
        if i > 0 {
            s.push_str(", ");
        }
        s.push_str(&quote(x.as_ref()));
    }
    s.push(']');
    s
}

/// A JSON string with the escapes of RFC 8259.
pub fn quote(t: &str) -> String {
    let mut s = String::with_capacity(t.len() + 2);
    s.push('"');
    for c in t.chars() {
        match c {
            '"' => s.push_str("\\\""),
            '\\' => s.push_str("\\\\"),
            '\n' => s.push_str("\\n"),
            '\r' => s.push_str("\\r"),
            '\t' => s.push_str("\\t"),
            c if (c as u32) < 0x20 => s.push_str(&format!("\\u{:04x}", c as u32)),
            c => s.push(c),
        }
    }
    s.push('"');
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn quote_escapes() {
        assert_eq!(quote("a\"b\\c\nd\u{1}"), "\"a\\\"b\\\\c\\nd\\u0001\"");
    }

    #[test]
    fn json_has_the_fields_of_the_schema() {
        let r = Report {
            code: Code::Reject,
            input_path: "x.ndjson".to_owned(),
            profile: Some("v4.35"),
            error: Some("B: TypeExpected".to_owned()),
            quarantine: vec!["U".to_owned()],
            deviations: vec!["D1"],
            ..Report::default()
        };
        let j = json(&r);
        for f in [
            "\"schema\": \"rulean-report/1\"",
            "\"verdict\": \"reject\"",
            "\"exit_code\": 1",
            "\"profile\": \"v4.35\"",
            "\"quarantine\": [\"U\"]",
            "\"deviations\": [\"D1\"]",
            "\"failed_decl\": null",
        ] {
            assert!(j.contains(f), "{f} is not in {j}");
        }
    }

    #[test]
    fn text_names_the_verdict() {
        let r = Report {
            code: Code::Accept,
            input_path: "x".to_owned(),
            accepted: 3,
            ..Report::default()
        };
        assert_eq!(text(&r), "accept: x: 3 declarations, 0 in quarantine, 0 ms");
    }
}
