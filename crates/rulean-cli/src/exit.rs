//! Exit codes, as in section 09.3 of the specification.
//!
//! The Arena reads 0 as accept, 1 as reject and 2 as decline. The codes above 2 are more specific, and every Arena-style caller reads them as "not accepted".

use std::process::ExitCode;

/// The exit code of a `rulean` run.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Code {
    /// Every declaration was accepted.
    Accept,
    /// At least one declaration was rejected.
    #[allow(dead_code, reason = "used from milestone M2")]
    Reject,
    /// rulean does not support this input.
    Decline,
    /// A resource limit was reached and no declaration was rejected.
    #[allow(dead_code, reason = "used from milestone M1")]
    Resource,
    /// The input is malformed.
    #[allow(dead_code, reason = "used from milestone M1")]
    Input,
    /// Every declaration was accepted, but a theorem uses an axiom outside the allowed list.
    #[allow(dead_code, reason = "used from milestone M2")]
    AxiomPolicy,
    /// The command line is wrong.
    Usage,
}

impl Code {
    /// The numeric value of the code.
    pub const fn value(self) -> u8 {
        match self {
            Code::Accept => 0,
            Code::Reject => 1,
            Code::Decline => 2,
            Code::Resource => 3,
            Code::Input => 4,
            Code::AxiomPolicy => 5,
            Code::Usage => 64,
        }
    }
}

impl From<Code> for ExitCode {
    fn from(code: Code) -> Self {
        ExitCode::from(code.value())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn values_match_the_specification() {
        let table = [
            (Code::Accept, 0),
            (Code::Reject, 1),
            (Code::Decline, 2),
            (Code::Resource, 3),
            (Code::Input, 4),
            (Code::AxiomPolicy, 5),
            (Code::Usage, 64),
        ];
        for (code, value) in table {
            assert_eq!(code.value(), value, "{code:?}");
        }
    }
}
