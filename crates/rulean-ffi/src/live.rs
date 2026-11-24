//! The memory of the process as a heap of Lean objects. This is the only module of the crate with `unsafe` code (spec 12).

#![allow(unsafe_code)]

use crate::heap::Heap;

/// Reads the objects of the Lean runtime in the memory of the process.
#[derive(Debug)]
pub struct LiveHeap {
    _private: (),
}

impl LiveHeap {
    /// A reader of the memory of the process.
    ///
    /// # Safety
    ///
    /// The caller gives the conversion the address of a Lean object that stays alive while the `LiveHeap` exists. The objects that it points to must have the layout of the Lean runtime of v4.36.0. The conversion reads only the bytes that the header of an object or the size field of a string or a big number gives, so all reads are then in live objects.
    pub unsafe fn new() -> LiveHeap {
        LiveHeap { _private: () }
    }
}

impl Heap for LiveHeap {
    fn read(&self, addr: u64, out: &mut [u8]) -> bool {
        let Ok(a) = usize::try_from(addr) else {
            return false;
        };
        if a == 0 || a.checked_add(out.len()).is_none() {
            return false;
        }
        let src = core::ptr::with_exposed_provenance::<u8>(a);
        // SAFETY: the contract of `LiveHeap::new` makes the `out.len()` bytes at `addr` part of a live Lean object. `out` is a different allocation, so the two ranges do not overlap.
        unsafe {
            core::ptr::copy_nonoverlapping(src, out.as_mut_ptr(), out.len());
        }
        true
    }
}
