//! The resource limits `--max-memory` and `--timeout` (spec 05.11, 12.3).
//!
//! The memory limit is a budget in bytes for the store, the caches, the value arena and the session of the checker. The measure counts the arrays and tables, without the allocator overhead, so the resident memory of the process is larger than the measure. The time limit is a deadline for the checker thread. At the deadline, the main thread stops the process with the resource code.

use std::sync::mpsc;
use std::time::Duration;

use crate::check::STACK_BYTES;

/// The value of `--max-memory none`: no budget.
pub const NO_LIMIT: usize = usize::MAX;

/// The largest `--timeout`: 10^7 seconds, about 115 days.
const MAX_SECONDS: f64 = 1.0e7;

/// Reads the value of `--max-memory`: a number of bytes with an optional unit `K`, `M`, `G` or `T` (powers of 1024), or `none`.
pub fn parse_size(v: &str) -> Result<usize, String> {
    if v == "none" {
        return Ok(NO_LIMIT);
    }
    let bad = || format!("`--max-memory` needs a size such as 512M or 8G, or `none`, not `{v}`");
    let (digits, shift) = match v.as_bytes().last() {
        Some(b'K' | b'k') => (&v[..v.len() - 1], 10),
        Some(b'M' | b'm') => (&v[..v.len() - 1], 20),
        Some(b'G' | b'g') => (&v[..v.len() - 1], 30),
        Some(b'T' | b't') => (&v[..v.len() - 1], 40),
        _ => (v, 0),
    };
    if digits.is_empty() || !digits.bytes().all(|c| c.is_ascii_digit()) {
        return Err(bad());
    }
    let n: u64 = digits.parse().map_err(|_| bad())?;
    let bytes = n.checked_mul(1u64 << shift).ok_or_else(bad)?;
    if bytes == 0 {
        return Err(bad());
    }
    Ok(usize::try_from(bytes).unwrap_or(NO_LIMIT - 1))
}

/// Reads the value of `--timeout`: a number of seconds, with an optional unit `s`, `m` or `h`. A decimal point is allowed.
pub fn parse_duration(v: &str) -> Result<Duration, String> {
    let bad = || format!("`--timeout` needs a time such as 90, 90s, 30m or 2h, not `{v}`");
    let (num, unit) = match v.as_bytes().last() {
        Some(b's') => (&v[..v.len() - 1], 1.0),
        Some(b'm') => (&v[..v.len() - 1], 60.0),
        Some(b'h') => (&v[..v.len() - 1], 3600.0),
        _ => (v, 1.0),
    };
    if num.is_empty() || !num.bytes().all(|c| c.is_ascii_digit() || c == b'.') {
        return Err(bad());
    }
    let n: f64 = num.parse().map_err(|_| bad())?;
    let secs = n * unit;
    if !(secs > 0.0 && secs <= MAX_SECONDS) {
        return Err(bad());
    }
    Ok(Duration::from_secs_f64(secs))
}

/// The default memory budget: 0.8 times the physical memory (spec 05.11). If rulean cannot find the physical memory, there is no budget.
pub fn default_max_memory() -> usize {
    match physical_memory() {
        Some(b) => usize::try_from(b / 5 * 4).unwrap_or(NO_LIMIT - 1),
        None => NO_LIMIT,
    }
}

/// The physical memory in bytes. On Linux, the value is `MemTotal` of `/proc/meminfo`. On macOS, the value is `hw.memsize` of `sysctl`. On other systems, the value is not known.
fn physical_memory() -> Option<u64> {
    if let Ok(s) = std::fs::read_to_string("/proc/meminfo") {
        return meminfo_total(&s);
    }
    if cfg!(target_os = "macos") {
        let out = std::process::Command::new("/usr/sbin/sysctl")
            .args(["-n", "hw.memsize"])
            .output()
            .ok()?;
        if out.status.success() {
            return String::from_utf8_lossy(&out.stdout).trim().parse().ok();
        }
    }
    None
}

/// The `MemTotal` line of `/proc/meminfo` in bytes.
fn meminfo_total(s: &str) -> Option<u64> {
    let line = s.lines().find(|l| l.starts_with("MemTotal:"))?;
    let mut words = line["MemTotal:".len()..].split_whitespace();
    let n: u64 = words.next()?.parse().ok()?;
    match words.next() {
        Some("kB") => n.checked_mul(1024),
        None => Some(n),
        Some(_) => None,
    }
}

/// The result of a run on the checker thread with a deadline.
pub enum Limited<T> {
    /// The thread gave a result.
    Done(T),
    /// The deadline came first. The thread continues until the process stops.
    Timeout,
    /// The thread stopped without a result.
    Stopped,
    /// The thread could not start.
    NoThread(std::io::Error),
}

/// Runs `f` on a new thread with the stack of the checker and waits for the result until `timeout`. With no timeout, the wait has no limit.
pub fn run_limited<T, F>(timeout: Option<Duration>, f: F) -> Limited<T>
where
    T: Send + 'static,
    F: FnOnce() -> T + Send + 'static,
{
    let (tx, rx) = mpsc::channel();
    let h = std::thread::Builder::new()
        .stack_size(STACK_BYTES)
        .spawn(move || {
            // The receiver is gone only after a timeout, and then the result is not used.
            let _ = tx.send(f());
        });
    let h = match h {
        Ok(h) => h,
        Err(e) => return Limited::NoThread(e),
    };
    let got = match timeout {
        Some(t) => match rx.recv_timeout(t) {
            Ok(v) => Some(v),
            Err(mpsc::RecvTimeoutError::Timeout) => return Limited::Timeout,
            Err(mpsc::RecvTimeoutError::Disconnected) => None,
        },
        None => rx.recv().ok(),
    };
    match got {
        Some(v) => {
            // The thread sent its result, so it ends now.
            let _ = h.join();
            Limited::Done(v)
        }
        None => Limited::Stopped,
    }
}

/// The text of a timeout for messages and the report.
pub fn timeout_text(t: Duration) -> String {
    format!(
        "the run is longer than the time limit of `--timeout` ({} s)",
        t.as_secs_f64()
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sizes() {
        assert_eq!(parse_size("1024"), Ok(1024));
        assert_eq!(parse_size("2K"), Ok(2048));
        assert_eq!(parse_size("512M"), Ok(512 << 20));
        assert_eq!(parse_size("8G"), Ok(8 << 30));
        assert_eq!(parse_size("1t"), Ok(1 << 40));
        assert_eq!(parse_size("none"), Ok(NO_LIMIT));
        for bad in [
            "",
            "0",
            "0G",
            "G",
            "1.5G",
            "-1",
            "8GB",
            "x",
            "99999999999999999999T",
        ] {
            assert!(parse_size(bad).is_err(), "{bad}");
        }
    }

    #[test]
    fn durations() {
        assert_eq!(parse_duration("90"), Ok(Duration::from_secs(90)));
        assert_eq!(parse_duration("90s"), Ok(Duration::from_secs(90)));
        assert_eq!(parse_duration("30m"), Ok(Duration::from_secs(1800)));
        assert_eq!(parse_duration("2h"), Ok(Duration::from_secs(7200)));
        assert_eq!(parse_duration("0.5"), Ok(Duration::from_millis(500)));
        for bad in [
            "", "0", "0s", "s", "-1", "1e3", "inf", "NaN", "1d", "99999999",
        ] {
            assert!(parse_duration(bad).is_err(), "{bad}");
        }
    }

    #[test]
    fn meminfo() {
        let s = "MemTotal:       16384 kB\nMemFree:         1024 kB\n";
        assert_eq!(meminfo_total(s), Some(16384 * 1024));
        assert_eq!(meminfo_total("MemFree: 1 kB\n"), None);
        assert_eq!(meminfo_total("MemTotal: x kB\n"), None);
    }

    #[test]
    fn default_budget_is_below_the_physical_memory() {
        let b = default_max_memory();
        if let Some(p) = physical_memory() {
            assert!((b as u64) < p);
            assert!(b > 0);
        }
    }

    #[test]
    fn deadline() {
        match run_limited(Some(Duration::from_secs(60)), || 7) {
            Limited::Done(v) => assert_eq!(v, 7),
            _ => panic!("no result"),
        }
        let (tx, rx) = mpsc::channel::<()>();
        // The thread waits until the test ends, so the deadline comes first.
        match run_limited(Some(Duration::from_millis(20)), move || rx.recv().is_ok()) {
            Limited::Timeout => {}
            _ => panic!("no timeout"),
        }
        drop(tx);
        match run_limited(None, || 3) {
            Limited::Done(v) => assert_eq!(v, 3),
            _ => panic!("no result"),
        }
    }
}
