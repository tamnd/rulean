//! The file header of an `.olean` file (spec 07.3.2).

use crate::{Fault, FaultKind};

/// The first bytes of each `.olean` file.
pub const MAGIC: &[u8; 5] = b"olean";

/// The size of the fixed header: the magic, the version, the flags, the Lean version, the commit and the base address.
pub const HEADER_BYTES: usize = 88;

/// Flag bit 0: the big numbers use the GMP encoding.
pub const FLAG_GMP: u8 = 1;

/// The format versions that this reader supports.
pub const VERSIONS: &[u8] = &[2, 3, 4];

/// The header of one `.olean` file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Header {
    /// The format version.
    pub version: u8,
    /// True if the big numbers use the GMP encoding.
    pub gmp: bool,
    /// The Lean version, for example `4.36.0`.
    pub lean_version: Vec<u8>,
    /// The commit of Lean that wrote the file.
    pub githash: Vec<u8>,
    /// The address that the writer used for the first byte of the file.
    pub base: u64,
}

/// Reads the header of `b`. An unknown version or an unknown flag is a decline.
pub fn read(b: &[u8]) -> Result<Header, Fault> {
    if b.len() < HEADER_BYTES || &b[..5] != MAGIC {
        return Err(Fault::new(
            FaultKind::Malformed,
            0,
            "the file does not start with the olean magic",
        ));
    }
    let version = b[5];
    if !VERSIONS.contains(&version) {
        return Err(Fault::new(
            FaultKind::Decline,
            5,
            format!(
                "olean format version {version} is not supported, this reader supports versions 2, 3 and 4"
            ),
        ));
    }
    let flags = b[6];
    if flags & !FLAG_GMP != 0 {
        return Err(Fault::new(
            FaultKind::Decline,
            6,
            format!("the olean flags {flags:#x} are not known"),
        ));
    }
    if flags & FLAG_GMP == 0 {
        return Err(Fault::new(
            FaultKind::Decline,
            6,
            "the file uses the native big number encoding, this reader supports only the GMP encoding",
        ));
    }
    let lean_version = text(&b[7..40], 7)?;
    let githash = text(&b[40..80], 40)?;
    let mut w = [0u8; 8];
    w.copy_from_slice(&b[80..88]);
    let base = u64::from_le_bytes(w);
    if base % 8 != 0 {
        return Err(Fault::new(
            FaultKind::Malformed,
            80,
            "the base address is not a multiple of 8",
        ));
    }
    Ok(Header {
        version,
        gmp: true,
        lean_version,
        githash,
        base,
    })
}

/// The text of a fixed field: the bytes before the first zero byte. Each byte must be printable ASCII, and after the first zero byte all bytes must be zero.
fn text(f: &[u8], at: usize) -> Result<Vec<u8>, Fault> {
    let n = f.iter().position(|&c| c == 0).unwrap_or(f.len());
    let good = f[..n].iter().all(|&c| (0x21..0x7f).contains(&c)) && f[n..].iter().all(|&c| c == 0);
    if !good {
        return Err(Fault::new(
            FaultKind::Malformed,
            at as u64,
            "a text field of the header is not printable ASCII",
        ));
    }
    Ok(f[..n].to_vec())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample() -> Vec<u8> {
        let mut b = vec![0u8; HEADER_BYTES];
        b[..5].copy_from_slice(MAGIC);
        b[5] = 2;
        b[6] = FLAG_GMP;
        b[7..13].copy_from_slice(b"4.36.0");
        b[40..44].copy_from_slice(b"611c");
        b[80..88].copy_from_slice(&0x31fc_9d50_0000u64.to_le_bytes());
        b
    }

    #[test]
    fn a_good_header_is_read() {
        let h = read(&sample()).expect("header");
        assert_eq!(h.version, 2);
        assert_eq!(h.lean_version, b"4.36.0");
        assert_eq!(h.githash, b"611c");
        assert_eq!(h.base, 0x31fc_9d50_0000);
    }

    #[test]
    fn an_unknown_version_is_a_decline() {
        let mut b = sample();
        b[5] = 9;
        assert_eq!(read(&b).expect_err("version").kind, FaultKind::Decline);
        b[5] = 1;
        assert_eq!(read(&b).expect_err("version").kind, FaultKind::Decline);
        for v in [3, 4] {
            b[5] = v;
            assert_eq!(read(&b).expect("known version").version, v);
        }
    }

    #[test]
    fn native_numbers_are_a_decline() {
        let mut b = sample();
        b[6] = 0;
        assert_eq!(read(&b).expect_err("flags").kind, FaultKind::Decline);
    }

    #[test]
    fn a_bad_magic_is_malformed() {
        let mut b = sample();
        b[0] = b'x';
        assert_eq!(read(&b).expect_err("magic").kind, FaultKind::Malformed);
        assert_eq!(
            read(&b[..10]).expect_err("short").kind,
            FaultKind::Malformed
        );
    }

    #[test]
    fn a_bad_text_field_is_malformed() {
        let mut b = sample();
        b[20] = b'x';
        assert_eq!(read(&b).expect_err("text").kind, FaultKind::Malformed);
    }
}
