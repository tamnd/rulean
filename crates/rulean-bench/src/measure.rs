//! Run one command and measure it.
//!
//! The measure of spec 08.7.1 is the count of user-space instructions over all threads, as `perf stat -e instructions:u` gives it. The harness can use four counters:
//!
//! - `perf`: `perf stat -e instructions:u`. This is the measure of the Arena. It needs Linux and a CPU that exposes its counters. GitHub-hosted runners do not expose them.
//! - `cachegrind`: the `I refs` of valgrind cachegrind. It counts the same instructions on each run and needs no hardware counter, but the run is about 50 times slower. The harness runs the command a second time for it, so that the wall time and the memory are not those of valgrind.
//! - `rusage`: the `instructions retired` of `/usr/bin/time -l` on macOS. It includes the instructions of the system calls, so it is not the same measure as the Arena.
//! - `none`: no count.
//!
//! The wall time comes from the harness. The CPU time and the peak memory come from `/usr/bin/time` when it exists.

use std::io::{self, Read};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, ExitStatus, Stdio};
use std::sync::mpsc;
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

/// The instruction counter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Counter {
    /// `perf stat -e instructions:u`.
    Perf,
    /// The `I refs` of valgrind cachegrind.
    Cachegrind,
    /// The `instructions retired` of `/usr/bin/time -l` on macOS.
    Rusage,
    /// No count.
    None,
}

impl Counter {
    /// The name of the counter on the command line and in the results.
    pub fn as_str(self) -> &'static str {
        match self {
            Counter::Perf => "perf",
            Counter::Cachegrind => "cachegrind",
            Counter::Rusage => "rusage",
            Counter::None => "none",
        }
    }

    /// Read a counter name. `auto` selects the best counter of this machine.
    pub fn parse(text: &str) -> Option<Counter> {
        match text {
            "auto" => Some(Counter::detect()),
            "perf" => Some(Counter::Perf),
            "cachegrind" => Some(Counter::Cachegrind),
            "rusage" => Some(Counter::Rusage),
            "none" => Some(Counter::None),
            _ => None,
        }
    }

    /// The best counter of this machine: `perf` if it gives a count, then `cachegrind`, then `rusage` on macOS.
    pub fn detect() -> Counter {
        if cfg!(target_os = "macos") {
            return Counter::Rusage;
        }
        if cfg!(target_os = "linux") {
            if perf_works() {
                return Counter::Perf;
            }
            if tool_exists("valgrind") {
                return Counter::Cachegrind;
            }
        }
        Counter::None
    }
}

fn perf_works() -> bool {
    let out = Command::new("perf")
        .args(["stat", "-x", ",", "-e", "instructions:u", "--", "true"])
        .output();
    match out {
        Ok(out) if out.status.success() => {
            parse_perf(&String::from_utf8_lossy(&out.stderr)).is_some()
        }
        _ => false,
    }
}

fn tool_exists(name: &str) -> bool {
    Command::new(name)
        .arg("--version")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok_and(|s| s.success())
}

/// The limits of one run.
#[derive(Debug, Clone, Copy)]
pub struct Limits {
    /// Stop the command after this time.
    pub timeout: Option<Duration>,
    /// Keep at most this many bytes of the standard output and of the standard error.
    pub output_cap: usize,
}

/// The measures of one run.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Sample {
    /// The exit code. A process that a signal stopped gets 128 plus the signal number, as in a shell.
    pub exit_code: i32,
    /// The harness stopped the command at the timeout.
    pub timed_out: bool,
    /// The wall time in seconds.
    pub wall_time: f64,
    /// The user and system CPU time in seconds, or 0 if it is not known.
    pub cpu_time: f64,
    /// The peak resident set size in bytes, or 0 if it is not known.
    pub max_rss: u64,
    /// The instruction count, if the counter gave one.
    pub instructions: Option<u64>,
    /// The start of the standard output.
    pub stdout: String,
    /// The start of the standard error.
    pub stderr: String,
}

/// Run `argv` once and measure it. The environment variable `IN` is set to `input`, as the Arena does.
pub fn measure(
    argv: &[String],
    input: &Path,
    counter: Counter,
    limits: &Limits,
) -> io::Result<Sample> {
    let work = scratch_dir()?;
    let result = measure_in(argv, input, counter, limits, &work);
    let _ = std::fs::remove_dir_all(&work);
    result
}

fn measure_in(
    argv: &[String],
    input: &Path,
    counter: Counter,
    limits: &Limits,
    work: &Path,
) -> io::Result<Sample> {
    let time_file = work.join("time.txt");
    let perf_file = work.join("perf.txt");
    let wrapper = TimeWrapper::detect();
    let mut full = Vec::new();
    if counter == Counter::Perf {
        full.extend(["perf", "stat", "-x", ",", "-e", "instructions:u", "-o"].map(String::from));
        full.push(path_arg(&perf_file));
        full.push("--".into());
    }
    full.extend(wrapper.prefix(&time_file));
    full.extend_from_slice(argv);

    let run = run_bounded(&full, input, limits)?;
    let mut sample = Sample {
        exit_code: run.exit_code,
        timed_out: run.timed_out,
        wall_time: run.wall_time,
        stdout: run.stdout,
        stderr: run.stderr,
        ..Sample::default()
    };
    if let Ok(text) = std::fs::read_to_string(&time_file) {
        let usage = wrapper.parse(&text);
        sample.cpu_time = usage.cpu_time;
        sample.max_rss = usage.max_rss;
        if counter == Counter::Rusage {
            sample.instructions = usage.instructions;
        }
    }
    if counter == Counter::Perf {
        sample.instructions = std::fs::read_to_string(&perf_file)
            .ok()
            .as_deref()
            .and_then(parse_perf);
    }
    if counter == Counter::Cachegrind && !sample.timed_out {
        sample.instructions = cachegrind(argv, input, limits, work)?;
    }
    Ok(sample)
}

fn cachegrind(
    argv: &[String],
    input: &Path,
    limits: &Limits,
    work: &Path,
) -> io::Result<Option<u64>> {
    let log = work.join("cachegrind.%p.log");
    let mut full: Vec<String> = [
        "valgrind",
        "--tool=cachegrind",
        "--cache-sim=no",
        "--cachegrind-out-file=/dev/null",
        "--trace-children=yes",
    ]
    .map(String::from)
    .into();
    full.push(format!("--log-file={}", log.display()));
    full.extend_from_slice(argv);
    // The valgrind run is slow, so it gets no timeout of its own. The first run already passed the timeout.
    let slow = Limits {
        timeout: None,
        output_cap: limits.output_cap,
    };
    run_bounded(&full, input, &slow)?;
    let mut total: Option<u64> = None;
    for entry in std::fs::read_dir(work)? {
        let path = entry?.path();
        let is_log = path
            .file_name()
            .and_then(|n| n.to_str())
            .is_some_and(|n| n.starts_with("cachegrind."));
        if is_log && let Some(count) = parse_cachegrind(&std::fs::read_to_string(&path)?) {
            total = Some(total.unwrap_or(0).saturating_add(count));
        }
    }
    Ok(total)
}

fn scratch_dir() -> io::Result<PathBuf> {
    static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let n = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("rulean-bench-{}-{n}", std::process::id()));
    std::fs::create_dir_all(&dir)?;
    Ok(dir)
}

fn path_arg(path: &Path) -> String {
    path.to_string_lossy().into_owned()
}

/// The `/usr/bin/time` of this machine.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TimeWrapper {
    /// GNU time, on Linux.
    Gnu,
    /// BSD time with `-l`, on macOS.
    Bsd,
    /// No wrapper.
    Absent,
}

#[derive(Debug, Default, PartialEq)]
struct Usage {
    cpu_time: f64,
    max_rss: u64,
    instructions: Option<u64>,
}

impl TimeWrapper {
    fn detect() -> TimeWrapper {
        if !Path::new("/usr/bin/time").exists() {
            return TimeWrapper::Absent;
        }
        if cfg!(target_os = "linux") {
            TimeWrapper::Gnu
        } else if cfg!(target_os = "macos") {
            TimeWrapper::Bsd
        } else {
            TimeWrapper::Absent
        }
    }

    fn prefix(self, out: &Path) -> Vec<String> {
        let out = path_arg(out);
        match self {
            TimeWrapper::Gnu => vec![
                "/usr/bin/time".into(),
                "-f".into(),
                "%U %S %M".into(),
                "-o".into(),
                out,
                "--".into(),
            ],
            TimeWrapper::Bsd => vec!["/usr/bin/time".into(), "-l".into(), "-o".into(), out],
            TimeWrapper::Absent => Vec::new(),
        }
    }

    fn parse(self, text: &str) -> Usage {
        match self {
            TimeWrapper::Gnu => parse_gnu_time(text),
            TimeWrapper::Bsd => parse_bsd_time(text),
            TimeWrapper::Absent => Usage::default(),
        }
    }
}

/// GNU time writes "Command exited with non-zero status" or "Command terminated by signal" before the format line, so the last line holds the values. The format is "%U %S %M": user seconds, system seconds and peak memory in KiB.
fn parse_gnu_time(text: &str) -> Usage {
    let Some(line) = text.lines().rev().find(|l| !l.trim().is_empty()) else {
        return Usage::default();
    };
    let fields: Vec<&str> = line.split_whitespace().collect();
    let [user, sys, rss] = fields[..] else {
        return Usage::default();
    };
    let seconds = |s: &str| s.parse::<f64>().unwrap_or(0.0);
    Usage {
        cpu_time: seconds(user) + seconds(sys),
        max_rss: rss.parse::<u64>().unwrap_or(0).saturating_mul(1024),
        instructions: None,
    }
}

/// BSD time with `-l` writes "N real N user N sys", then one line for each value, with the value first. On macOS the peak memory is in bytes.
fn parse_bsd_time(text: &str) -> Usage {
    let mut usage = Usage::default();
    for line in text.lines() {
        let fields: Vec<&str> = line.split_whitespace().collect();
        if fields.len() == 6 && fields[1] == "real" {
            let seconds = |s: &str| s.parse::<f64>().unwrap_or(0.0);
            usage.cpu_time = seconds(fields[2]) + seconds(fields[4]);
            continue;
        }
        let Some((value, label)) = line.trim().split_once(char::is_whitespace) else {
            continue;
        };
        match label.trim() {
            "maximum resident set size" => usage.max_rss = value.parse().unwrap_or(0),
            "instructions retired" => usage.instructions = value.parse().ok(),
            _ => {}
        }
    }
    usage
}

/// `perf stat -x ,` writes one line for each event. The first field is the count, or a text such as `<not supported>`.
fn parse_perf(text: &str) -> Option<u64> {
    text.lines()
        .filter(|l| !l.starts_with('#'))
        .find(|l| {
            l.split(',')
                .nth(2)
                .is_some_and(|e| e.starts_with("instructions"))
        })
        .and_then(|l| l.split(',').next())
        .and_then(|v| v.trim().parse().ok())
}

/// Cachegrind writes `==PID== I refs: 1,234,567` at the end of each process.
fn parse_cachegrind(text: &str) -> Option<u64> {
    text.lines().find_map(|line| {
        let rest = line.split_once("==").map_or(line, |(_, r)| r);
        let rest = rest.split_once("==").map_or(rest, |(_, r)| r).trim_start();
        let value = rest.strip_prefix('I')?.trim_start().strip_prefix("refs:")?;
        value.trim().replace(',', "").parse().ok()
    })
}

struct Run {
    exit_code: i32,
    timed_out: bool,
    wall_time: f64,
    stdout: String,
    stderr: String,
}

fn run_bounded(argv: &[String], input: &Path, limits: &Limits) -> io::Result<Run> {
    let (program, args) = argv
        .split_first()
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "no command"))?;
    let mut command = Command::new(program);
    command
        .args(args)
        .env("IN", input)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    own_group(&mut command);
    let start = Instant::now();
    let mut child = command.spawn()?;
    let out = reader(child.stdout.take(), limits.output_cap);
    let err = reader(child.stderr.take(), limits.output_cap);
    let pid = child.id();
    let (status, timed_out) = wait(child, pid, limits.timeout)?;
    let wall_time = start.elapsed().as_secs_f64();
    Ok(Run {
        exit_code: exit_code(status),
        timed_out,
        wall_time,
        stdout: out.join().unwrap_or_default(),
        stderr: err.join().unwrap_or_default(),
    })
}

fn wait(mut child: Child, pid: u32, timeout: Option<Duration>) -> io::Result<(ExitStatus, bool)> {
    let Some(timeout) = timeout else {
        return Ok((child.wait()?, false));
    };
    let (tx, rx) = mpsc::channel();
    let waiter = std::thread::spawn(move || {
        let _ = tx.send(child.wait());
    });
    let (status, timed_out) = match rx.recv_timeout(timeout) {
        Ok(status) => (status?, false),
        Err(_) => {
            kill_group(pid);
            let status = rx
                .recv()
                .map_err(|_| io::Error::other("the waiter thread stopped"))??;
            (status, true)
        }
    };
    let _ = waiter.join();
    Ok((status, timed_out))
}

fn reader<R: Read + Send + 'static>(stream: Option<R>, cap: usize) -> JoinHandle<String> {
    std::thread::spawn(move || {
        let Some(mut stream) = stream else {
            return String::new();
        };
        let mut kept = Vec::new();
        let mut buf = [0u8; 8192];
        // Read to the end, so that the child does not block on a full pipe, but keep only the first `cap` bytes.
        while let Ok(n) = stream.read(&mut buf) {
            if n == 0 {
                break;
            }
            let room = cap.saturating_sub(kept.len());
            kept.extend_from_slice(&buf[..n.min(room)]);
        }
        String::from_utf8_lossy(&kept).into_owned()
    })
}

#[cfg(unix)]
fn own_group(command: &mut Command) {
    use std::os::unix::process::CommandExt;
    command.process_group(0);
}

#[cfg(not(unix))]
fn own_group(_command: &mut Command) {}

/// Stop the command and all of its children. The command is the leader of its own process group, so the group has the same number as the process.
#[cfg(unix)]
fn kill_group(pid: u32) {
    let _ = Command::new("kill")
        .args(["-KILL", "--", &format!("-{pid}")])
        .status();
}

#[cfg(windows)]
fn kill_group(pid: u32) {
    let _ = Command::new("taskkill")
        .args(["/F", "/T", "/PID", &pid.to_string()])
        .stdout(Stdio::null())
        .status();
}

#[cfg(not(any(unix, windows)))]
fn kill_group(_pid: u32) {}

#[cfg(unix)]
fn exit_code(status: ExitStatus) -> i32 {
    use std::os::unix::process::ExitStatusExt;
    status
        .code()
        .or_else(|| status.signal().map(|s| 128 + s))
        .unwrap_or(-1)
}

#[cfg(not(unix))]
fn exit_code(status: ExitStatus) -> i32 {
    status.code().unwrap_or(-1)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn perf_output_gives_the_count() {
        let text =
            "# started on Sat Nov 21 10:00:00 2026\n\n12345678,,instructions:u,1000000,100.00,,\n";
        assert_eq!(parse_perf(text), Some(12_345_678));
        assert_eq!(
            parse_perf("<not supported>,,instructions:u,0,100.00,,\n"),
            None
        );
    }

    #[test]
    fn gnu_time_output_gives_cpu_and_memory() {
        let usage = parse_gnu_time("Command exited with non-zero status 1\n1.50 0.25 2048\n");
        assert_eq!(
            usage,
            Usage {
                cpu_time: 1.75,
                max_rss: 2048 * 1024,
                instructions: None
            }
        );
        assert_eq!(parse_gnu_time(""), Usage::default());
    }

    #[test]
    fn bsd_time_output_gives_cpu_memory_and_instructions() {
        let text = "        1.00 real         0.50 user         0.25 sys\n             1196032  maximum resident set size\n                   0  swaps\n            13494507  instructions retired\n";
        assert_eq!(
            parse_bsd_time(text),
            Usage {
                cpu_time: 0.75,
                max_rss: 1_196_032,
                instructions: Some(13_494_507)
            }
        );
    }

    #[test]
    fn cachegrind_output_gives_the_count() {
        let text = "==4242== Cachegrind, a high-precision tracing profiler\n==4242== \n==4242== I refs:        1,234,567\n";
        assert_eq!(parse_cachegrind(text), Some(1_234_567));
        assert_eq!(parse_cachegrind("==1== I   refs:      42\n"), Some(42));
        assert_eq!(parse_cachegrind("==1== no count\n"), None);
    }

    #[test]
    fn counter_names_round_trip() {
        for counter in [
            Counter::Perf,
            Counter::Cachegrind,
            Counter::Rusage,
            Counter::None,
        ] {
            assert_eq!(Counter::parse(counter.as_str()), Some(counter));
        }
        assert_eq!(Counter::parse("cycles"), None);
    }

    #[cfg(unix)]
    fn sh(script: &str) -> Vec<String> {
        vec!["sh".into(), "-c".into(), script.into()]
    }

    #[cfg(unix)]
    #[test]
    fn the_exit_code_and_the_output_are_kept() {
        let limits = Limits {
            timeout: None,
            output_cap: 4,
        };
        let sample = measure(
            &sh("echo \"$IN\"; exit 3"),
            Path::new("abcdefgh"),
            Counter::None,
            &limits,
        )
        .expect("run");
        assert_eq!(sample.exit_code, 3);
        assert!(!sample.timed_out);
        assert_eq!(sample.stdout, "abcd");
    }

    #[cfg(unix)]
    #[test]
    fn the_timeout_stops_the_command() {
        let limits = Limits {
            timeout: Some(Duration::from_millis(200)),
            output_cap: 64,
        };
        let sample = measure(&sh("sleep 30"), Path::new("x"), Counter::None, &limits).expect("run");
        assert!(sample.timed_out);
        assert!(sample.wall_time < 10.0, "wall time {}", sample.wall_time);
    }
}
