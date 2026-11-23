//! The bench harness. It runs a checker on each test of a corpus and records the instructions, the wall time, the CPU time and the peak memory. The results are in the format of the Lean Kernel Arena, so that they can be compared with the Arena numbers. See spec section 08.7.

pub mod compare;
pub mod gate;
pub mod measure;
pub mod record;
pub mod suite;
pub mod work;
