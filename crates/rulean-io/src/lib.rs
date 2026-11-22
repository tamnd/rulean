//! File input for the verified core under contract K2 (spec 10.7).
//!
//! The contract is `ReadsAs path bytes`: the bytes that the core gets are the content of the file at open time. Review discharges the contract, with two checks at run time:
//!
//! 1. `open` opens the file read-only, and the reader gives the bytes of the file in the order of the file, in blocks of `READ_BYTES`. The caller hashes each byte that it gives to the core, so the SHA-256 digest in the report is the digest of the bytes that were checked.
//! 2. After the run, `confirm` reads the file again and computes its digest. If the two digests are not the same, the file changed during the run, and the caller must not report the verdict.
//!
//! Standard input and a file that is not a regular file, for example a pipe, cannot be read again. For these inputs `confirm` gives `Confirm::NotAFile`, and only check 1 applies.
//!
//! This crate does not map the file into memory. A mapping needs `unsafe` code (spec 12), and the block reader is fast enough for the parser of spec 07.

use std::fs::{File, OpenOptions};
use std::io::{BufRead, BufReader, Read};
use std::path::{Path, PathBuf};

use rulean_core::sha256::Hasher;

/// The size of a read block.
pub const READ_BYTES: usize = 1 << 20;

/// The path that means standard input.
pub const STDIN: &str = "-";

/// Where the input comes from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Source {
    /// Standard input.
    Stdin,
    /// A regular file. `confirm` can read it again.
    File(PathBuf),
    /// A file that is not a regular file, for example a pipe or a device.
    Other(PathBuf),
}

/// An open input.
pub struct Input {
    /// The reader. It gives the bytes of the input in order.
    pub reader: Box<dyn BufRead + Send>,
    /// Where the bytes come from.
    pub source: Source,
}

impl std::fmt::Debug for Input {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Input")
            .field("source", &self.source)
            .finish_non_exhaustive()
    }
}

/// The result of `confirm`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Confirm {
    /// The file has the same digest as at the start.
    Same,
    /// The file has a different digest. The value is the new digest.
    Changed([u8; 32]),
    /// The input cannot be read again.
    NotAFile,
}

/// Opens the input read-only. The path `-` is standard input.
pub fn open(path: &str) -> std::io::Result<Input> {
    if path == STDIN {
        return Ok(Input {
            reader: Box::new(BufReader::with_capacity(READ_BYTES, std::io::stdin())),
            source: Source::Stdin,
        });
    }
    let f = open_file(Path::new(path))?;
    let regular = f.metadata()?.is_file();
    let p = PathBuf::from(path);
    let source = if regular {
        Source::File(p)
    } else {
        Source::Other(p)
    };
    Ok(Input {
        reader: Box::new(BufReader::with_capacity(READ_BYTES, f)),
        source,
    })
}

/// Opens a file for reading only. The handle cannot write to the file.
fn open_file(path: &Path) -> std::io::Result<File> {
    OpenOptions::new().read(true).open(path)
}

/// The SHA-256 digest of all bytes of `r`.
pub fn digest<R: Read>(mut r: R) -> std::io::Result<[u8; 32]> {
    let mut h = Hasher::new();
    let mut buf = vec![0u8; READ_BYTES];
    loop {
        let n = r.read(&mut buf)?;
        if n == 0 {
            return Ok(h.finish());
        }
        h.update(&buf[..n]);
    }
}

/// Reads the input again after the run and compares its digest with `start`, the digest of the bytes that the core got.
pub fn confirm(source: &Source, start: &[u8; 32]) -> std::io::Result<Confirm> {
    match source {
        Source::Stdin | Source::Other(_) => Ok(Confirm::NotAFile),
        Source::File(p) => {
            let end = digest(open_file(p)?)?;
            if &end == start {
                Ok(Confirm::Same)
            } else {
                Ok(Confirm::Changed(end))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    /// A file in the temporary directory with a name for this test only.
    fn temp(name: &str, bytes: &[u8]) -> PathBuf {
        let p = std::env::temp_dir().join(format!("rulean-io-{}-{name}", std::process::id()));
        let mut f = File::create(&p).expect("create");
        f.write_all(bytes).expect("write");
        p
    }

    fn read_all(mut i: Input) -> Vec<u8> {
        let mut out = Vec::new();
        i.reader.read_to_end(&mut out).expect("read");
        out
    }

    #[test]
    fn the_reader_gives_the_file_content() {
        let bytes: Vec<u8> = (0..3 * READ_BYTES + 17).map(|i| (i % 251) as u8).collect();
        let p = temp("content", &bytes);
        let i = open(p.to_str().expect("utf-8")).expect("open");
        assert_eq!(i.source, Source::File(p.clone()));
        assert_eq!(read_all(i), bytes);
        std::fs::remove_file(p).expect("remove");
    }

    #[test]
    fn an_unchanged_file_is_confirmed() {
        let p = temp("same", b"abc\n");
        let i = open(p.to_str().expect("utf-8")).expect("open");
        let source = i.source.clone();
        let d = digest(&read_all(i)[..]).expect("digest");
        assert_eq!(confirm(&source, &d).expect("confirm"), Confirm::Same);
        std::fs::remove_file(p).expect("remove");
    }

    #[test]
    fn a_changed_file_is_found() {
        let p = temp("changed", b"abc\n");
        let i = open(p.to_str().expect("utf-8")).expect("open");
        let source = i.source.clone();
        let d = digest(&read_all(i)[..]).expect("digest");
        std::fs::write(&p, b"abd\n").expect("write");
        let want = digest(&b"abd\n"[..]).expect("digest");
        assert_eq!(
            confirm(&source, &d).expect("confirm"),
            Confirm::Changed(want)
        );
        std::fs::remove_file(p).expect("remove");
    }

    #[test]
    fn a_removed_file_is_an_error() {
        let p = temp("removed", b"abc\n");
        let i = open(p.to_str().expect("utf-8")).expect("open");
        let source = i.source.clone();
        let d = digest(&read_all(i)[..]).expect("digest");
        std::fs::remove_file(&p).expect("remove");
        assert!(confirm(&source, &d).is_err());
    }

    #[test]
    fn standard_input_is_not_read_again() {
        assert_eq!(
            confirm(&Source::Stdin, &[0; 32]).expect("confirm"),
            Confirm::NotAFile
        );
    }

    #[test]
    fn the_digest_is_sha_256() {
        let d = digest(&b"abc"[..]).expect("digest");
        assert_eq!(d[..4], [0xba, 0x78, 0x16, 0xbf]);
    }

    #[test]
    fn a_missing_file_is_an_error() {
        assert!(open("/no/such/rulean/input").is_err());
    }
}
