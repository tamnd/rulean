//! Semantics profiles (spec 05.2).
//!
//! A profile is a set of flags. The checker tests the flags, never a version string. This version of rulean has only the `v4.35` profile, which is the baseline, so every flag is off.

/// A semantics profile.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Profile {
    /// Lean v4.35.0, v4.36.0 and the v4.36.x releases.
    V4_35,
}

/// The flags of a profile. A flag is on when the profile has the behaviour of the newer kernel.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Flags {
    /// Proof irrelevance before the other rules of definitional equality (lean4#15103).
    pub proof_irrel_first: bool,
    /// No `whnf` of a major premise in `Prop` (lean4#15371).
    pub no_whnf_prop_major: bool,
    /// Eta for a subsingleton major premise (lean4#15371).
    pub eta_subsingleton_major: bool,
    /// Eta for a partial constructor application (lean4#15373).
    pub eta_partial_ctor: bool,
    /// 64-bit counts (lean4#16279).
    pub count_64: bool,
    /// The loose bound variable check of the inductive types (lean4#16512).
    pub inductive_loose_bvar_check: bool,
}

/// The number of profiles.
pub const PROFILE_COUNT: usize = 1;

/// All profiles, in release order.
pub const PROFILES: [Profile; PROFILE_COUNT] = [Profile::V4_35];

impl Profile {
    /// The identifier of the profile, for `--profile` and the report.
    pub fn id(self) -> &'static str {
        match self {
            Profile::V4_35 => "v4.35",
        }
    }

    /// The flags of the profile.
    pub fn flags(self) -> Flags {
        match self {
            Profile::V4_35 => Flags {
                proof_irrel_first: false,
                no_whnf_prop_major: false,
                eta_subsingleton_major: false,
                eta_partial_ctor: false,
                count_64: false,
                inductive_loose_bvar_check: false,
            },
        }
    }
}

/// True if `v` starts with the bytes of `p`.
fn starts_with(v: &[u8], p: &[u8]) -> bool {
    if v.len() < p.len() {
        return false;
    }
    let mut i = 0;
    while i < p.len() && v[i] == p[i] {
        i += 1;
    }
    i == p.len()
}

/// True if `v` is `p`, or `p` and then a dot or a dash and more bytes.
fn is_release_of(v: &[u8], p: &[u8]) -> bool {
    if !starts_with(v, p) {
        return false;
    }
    if v.len() == p.len() {
        return true;
    }
    v[p.len()] == b'.' || v[p.len()] == b'-'
}

/// The profile of a `lean.version` string, such as `4.36.0`. A version with no profile gives `None`, and the checker declines the input (spec 05.2).
pub fn of_lean_version(v: &[u8]) -> Option<Profile> {
    if is_release_of(v, b"4.35") || is_release_of(v, b"4.36") {
        Some(Profile::V4_35)
    } else {
        None
    }
}

/// The profile with the identifier `id`, for `--profile`.
pub fn of_id(id: &[u8]) -> Option<Profile> {
    let mut i = 0;
    let mut r = None;
    while i < PROFILE_COUNT {
        let p = PROFILES[i];
        let b = p.id().as_bytes();
        if b.len() == id.len() && starts_with(id, b) {
            r = Some(p);
        }
        i += 1;
    }
    r
}
