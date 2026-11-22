//! The rule trace of `rulean explain` (spec 09.2).
//!
//! When `Checker::trace_on` is true, the checker writes one event for each rule that it applies: delta, iota, the quotient rules, the `Nat` extension, the type-directed rules of definitional equality, and the answer of each engine F query. The trace keeps at most `MAX_EVENTS` events, and it counts all events. When `trace_on` is false, the checker writes nothing.

use alloc::vec::Vec;
use rulean_store::{Expr, ExprId, NameId};

use crate::expr;
use crate::tc::Checker;

/// The largest number of events in a trace. After that, the trace counts the events but does not keep them.
pub const MAX_EVENTS: usize = 100_000;

/// A rule of the trace.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rule {
    /// A definition or a theorem was unfolded. The name is the constant.
    Delta,
    /// A recursor stepped by the rule of a constructor. The name is the recursor.
    Iota,
    /// `Quot.lift` or `Quot.ind` stepped. The name is the quotient constant.
    Quot,
    /// The `Nat` extension computed a literal. The name is the operation.
    Nat,
    /// Proof irrelevance gave "equal".
    ProofIrrel,
    /// Function eta gave "equal".
    EtaFn,
    /// Structure eta gave "equal".
    EtaStruct,
    /// The unit-like rule gave "equal".
    UnitLike,
    /// The string literal expansion gave the answer.
    StringLit,
    /// Engine F found an equality, and it is the answer.
    FEqual,
    /// Engine F found an equality, and engine R confirmed it.
    FConfirmed,
    /// Engine F found an equality, and engine R did not confirm it.
    FDisagree,
    /// Engine F did not find an equality, or it stopped with a fault, so engine R decided the query.
    FFallback,
}

/// The number of rules.
pub const RULES: usize = 13;

impl Rule {
    /// The index of the rule in the counts.
    pub fn index(self) -> usize {
        match self {
            Rule::Delta => 0,
            Rule::Iota => 1,
            Rule::Quot => 2,
            Rule::Nat => 3,
            Rule::ProofIrrel => 4,
            Rule::EtaFn => 5,
            Rule::EtaStruct => 6,
            Rule::UnitLike => 7,
            Rule::StringLit => 8,
            Rule::FEqual => 9,
            Rule::FConfirmed => 10,
            Rule::FDisagree => 11,
            Rule::FFallback => 12,
        }
    }

    /// The rule of an index, for the counts.
    pub fn of_index(i: usize) -> Rule {
        match i {
            0 => Rule::Delta,
            1 => Rule::Iota,
            2 => Rule::Quot,
            3 => Rule::Nat,
            4 => Rule::ProofIrrel,
            5 => Rule::EtaFn,
            6 => Rule::EtaStruct,
            7 => Rule::UnitLike,
            8 => Rule::StringLit,
            9 => Rule::FEqual,
            10 => Rule::FConfirmed,
            11 => Rule::FDisagree,
            _ => Rule::FFallback,
        }
    }

    /// The name of the rule in the text of `rulean explain`.
    pub fn word(self) -> &'static str {
        match self {
            Rule::Delta => "delta",
            Rule::Iota => "iota",
            Rule::Quot => "quot",
            Rule::Nat => "nat",
            Rule::ProofIrrel => "proof-irrelevance",
            Rule::EtaFn => "function-eta",
            Rule::EtaStruct => "structure-eta",
            Rule::UnitLike => "unit-like",
            Rule::StringLit => "string-literal",
            Rule::FEqual => "engine-f-equal",
            Rule::FConfirmed => "engine-f-confirmed",
            Rule::FDisagree => "engine-f-disagree",
            Rule::FFallback => "engine-f-fallback",
        }
    }
}

/// One event of the trace: the rule, the constant if the rule has one (else the anonymous name), and the depth of the checker.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Event {
    pub rule: Rule,
    pub name: NameId,
    pub depth: u32,
}

/// The trace of a check.
#[derive(Clone, Debug, Default)]
pub struct Trace {
    pub events: Vec<Event>,
    /// The number of events of each rule, also after `MAX_EVENTS`.
    pub counts: Vec<u64>,
}

impl Trace {
    /// An empty trace.
    pub fn new() -> Trace {
        let mut counts: Vec<u64> = Vec::with_capacity(RULES);
        let mut i = 0;
        while i < RULES {
            counts.push(0);
            i += 1;
        }
        Trace {
            events: Vec::new(),
            counts,
        }
    }
}

impl Checker {
    /// Writes an event if the trace is on.
    pub(crate) fn note(&mut self, rule: Rule, name: NameId) {
        if !self.trace_on {
            return;
        }
        let i = rule.index();
        if i < self.trace.counts.len() {
            self.trace.counts[i] += 1;
        }
        if self.trace.events.len() < MAX_EVENTS {
            let depth = self.depth;
            self.trace.events.push(Event { rule, name, depth });
        }
    }

    /// `note` with the head constant of an application, or the anonymous name.
    pub(crate) fn note_head(&mut self, rule: Rule, e: ExprId) {
        if !self.trace_on {
            return;
        }
        let f = expr::app_fn(&self.st, e);
        let n = match self.st.node(f) {
            Expr::Const(n, _) => n,
            _ => self.st.anon(),
        };
        self.note(rule, n);
    }
}
