//! The mirror of the kernel environment (spec 09.6.3).
//!
//! The checker keeps its own copy of the constants of a Lean environment. Lean has added these constants already, so the mirror adds them without a check, as the official kernel does with the constants of an import. The checker then checks each new declaration against the mirror.

use rulean_core::tc::Checker;

use crate::Fault;
use crate::conv::Converter;
use crate::heap::Heap;

/// Converts the `ConstantInfo` objects at the addresses `cis` and adds the constants to the environment of `chk` without a check. If `quot_init` is true, the environment marks the quotient constants as initialized, as the field `quotInit` of the Lean environment does.
///
/// The add is all or nothing. If one conversion fails, the call gives the fault and the environment does not change. The store can keep the terms of the constants before the fault, but the environment does not refer to them.
///
/// After the add, the checker compares the targets of the primitive extensions that it has now with their references (`check_pins`), as it does after a declaration. Thus a mirrored `Nat.add` that is not the reference turns its extension off.
pub fn add_constants<H: Heap>(
    chk: &mut Checker,
    h: &H,
    cis: &[u64],
    quot_init: bool,
) -> Result<usize, Fault> {
    let mut out = Vec::with_capacity(cis.len());
    {
        let mut c = Converter::new(h, &mut chk.st);
        for &ci in cis {
            out.push(c.constant(ci)?);
        }
    }
    let n = out.len();
    for k in out {
        chk.env.add(k);
    }
    if quot_init {
        chk.env.mark_quot_initialized();
    }
    chk.check_pins();
    Ok(n)
}
