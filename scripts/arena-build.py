#!/usr/bin/env python3
"""Build the exports of Arena tests that are not in the Arena tarball.

Usage: scripts/arena-build.py [--check RULEAN] ARENA RESULTS OUT [NAME...]

ARENA is a checkout of the lean-kernel-arena repository at the commit of RESULTS. RESULTS is the results.json of scripts/arena-fetch.sh. OUT gets the exports in the layout of scripts/arena-fetch.sh: an accept test goes to OUT/good, a reject test goes to OUT/bad and an "either" test goes to OUT/either. Each NAME selects the tests whose name starts with NAME. Without NAME, the script builds the "either" tests.

The script does what lka.py of the Arena does. For a test with a `file` field, it copies the file. For a test with a `leanfile` field or a `dir` and `module` field, it builds the Lean module with lake and exports it with the `leanexport` binary of the Lean toolchain. The toolchain must be on PATH, and it must be the toolchain of ARENA/tests/lean-toolchain. For a test with a `url` field, such as Mathlib, it fetches the `rev` commit of the repository, runs the `pre-build` commands with bash, builds the module and exports it with the `leanexport` binary of the toolchain of the repository. A `url` test needs elan, because each repository selects its own toolchain. A toolchain before Lean v4.35.0 has no `leanexport` binary, and the script does not build one. The script keeps the work directory of a `url` test, and a later run uses it again if it has the fetch and the pre-build of the same `rev`.

The script keeps only the exports whose SHA-256 is the hash in RESULTS, because the expected verdicts and the Arena numbers are for those exports. It exits with 1 if a selected test was not built or has another hash.

With `--check RULEAN`, the script does not write the exports. It sends each export to `RULEAN check --profile v4.35 -` and computes the hash of the export at the same time. The report of the check goes to OUT/NAME.report.json. The script compares the exit code with the expected verdict of RESULTS. For an "either" test, the expected verdict is the verdict in docs/arena/either-v4.35.tsv. Use this mode for a large export, such as Mathlib, that the disk cannot keep.
"""

import hashlib
import json
import os
import shutil
import subprocess
import sys

LAKEFILE = 'name = "test"\n\n[[lean_lib]]\nname = "Test"'


def fields(path):
    """The fields of a test file. The script uses PyYAML if it is installed. Without PyYAML, it reads only the top-level `key: value` fields that are one line long."""
    try:
        import yaml
    except ImportError:
        yaml = None
    if yaml is not None:
        with open(path, encoding="utf-8") as f:
            return yaml.safe_load(f)
    out = {}
    for line in open(path, encoding="utf-8"):
        if line[:1] in (" ", "#", "\n", "-"):
            continue
        k, sep, v = line.partition(":")
        if not sep:
            continue
        v = v.strip()
        if v.startswith("["):
            v = json.loads(v)
        out[k.strip()] = v
    return out


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        while True:
            b = f.read(1 << 20)
            if not b:
                break
            h.update(b)
    return h.hexdigest()


def run(cmd, cwd, out=None):
    print("  " + " ".join(cmd), file=sys.stderr)
    r = subprocess.run(cmd, cwd=cwd, stdout=out, check=False)
    return r.returncode == 0


def fetch(test, work):
    """Fetches the `rev` commit of the `url` repository into work, as lka.py does. The checkout has an `origin` remote, because `lake exe cache get` of Mathlib asks git for the remote and the commit."""
    os.makedirs(work)
    for cmd in (
        ["git", "init", "--quiet"],
        ["git", "remote", "add", "origin", test["url"]],
        ["git", "fetch", "--quiet", "--depth", "1", "origin", test["rev"]],
        ["git", "checkout", "--quiet", "FETCH_HEAD"],
    ):
        if not run(cmd, work):
            return False
    return True


def find_leanexport(work, url):
    """The `leanexport` binary of the toolchain of work. For a `url` test, this is the toolchain that elan selects in the repository."""
    if url:
        r = subprocess.run(["elan", "which", "leanexport"], cwd=work, capture_output=True, text=True, check=False)
        if r.returncode == 0 and r.stdout.strip():
            return r.stdout.strip()
        return None
    return shutil.which("leanexport")


def export(arena, test, work, dest, check):
    """Writes the export of one test to dest, or sends it to the check of `check`. The result is False on a failure."""
    if "file" in test:
        if check is not None:
            with open(os.path.join(arena, test["file"]), "rb") as f:
                return check.run_from(f)
        shutil.copy(os.path.join(arena, test["file"]), dest)
        return True
    url = "url" in test
    stamp = os.path.join(work, ".arena-build-done")
    reuse = url and os.path.exists(stamp) and open(stamp, encoding="utf-8").read() == test.get("rev")
    if os.path.exists(work) and not reuse:
        shutil.rmtree(work)
    if reuse:
        print("  the work directory has the fetch and the pre-build of this rev", file=sys.stderr)
        module = test["module"]
    elif url:
        if "rev" not in test or "module" not in test:
            print("  the test has a url field but no rev or module field", file=sys.stderr)
            return False
        if not fetch(test, work):
            return False
        module = test["module"]
    elif "leanfile" in test:
        os.makedirs(work)
        shutil.copy(os.path.join(arena, test["leanfile"]), os.path.join(work, "Test.lean"))
        shutil.copy(os.path.join(arena, "tests", "lean-toolchain"), work)
        with open(os.path.join(work, "lakefile.toml"), "w", encoding="utf-8") as f:
            f.write(LAKEFILE)
        module = "Test"
    elif "dir" in test and "module" in test:
        shutil.copytree(os.path.join(arena, test["dir"]), work)
        module = test["module"]
    else:
        print("  the test has no file, leanfile or dir field", file=sys.stderr)
        return False
    pre = test.get("pre-build")
    if not reuse and pre and not run(["bash", "-e", "-c", pre], work):
        return False
    if url and not reuse:
        with open(stamp, "w", encoding="utf-8") as f:
            f.write(test["rev"])
    if not run(["lake", "build", module], work):
        return False
    leanexport = find_leanexport(work, url)
    if leanexport is None:
        print("  the toolchain has no leanexport binary", file=sys.stderr)
        return False
    cmd = ["lake", "env", leanexport, module]
    if test.get("export-decls"):
        cmd += ["--"] + [str(d) for d in test["export-decls"]]
    if check is not None:
        print("  " + " ".join(cmd), file=sys.stderr)
        p = subprocess.Popen(cmd, cwd=work, stdout=subprocess.PIPE)
        good = check.run_from(p.stdout)
        p.stdout.close()
        return p.wait() == 0 and good
    with open(dest, "wb") as out:
        return run(cmd, work, out)


class Check:
    """The `--check` mode: sends an export to rulean and computes its hash."""

    def __init__(self, rulean, report):
        self.rulean = rulean
        self.report = report
        self.digest = ""
        self.code = None

    def run_from(self, src):
        """Copies the bytes of src to the standard input of rulean. The result is False if rulean did not start."""
        cmd = [self.rulean, "check", "--profile", "v4.35", "--report", self.report, "-"]
        print("  " + " ".join(cmd), file=sys.stderr)
        h = hashlib.sha256()
        p = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.DEVNULL)
        while True:
            b = src.read(1 << 20)
            if not b:
                break
            h.update(b)
            p.stdin.write(b)
        p.stdin.close()
        self.code = p.wait()
        self.digest = h.hexdigest()
        return True


def pinned(here):
    """The pinned verdicts of the "either" tests, from docs/arena/either-v4.35.tsv."""
    out = {}
    with open(os.path.join(here, "docs", "arena", "either-v4.35.tsv"), encoding="utf-8") as f:
        for line in f:
            parts = line.rstrip("\n").split("\t")
            if len(parts) >= 2 and not line.startswith("#"):
                out[parts[0]] = parts[1]
    return out


def main():
    args = sys.argv[1:]
    rulean = None
    if args[:1] == ["--check"]:
        if len(args) < 2:
            sys.exit("--check needs the rulean binary")
        rulean = os.path.abspath(args[1])
        args = args[2:]
    if len(args) < 3:
        sys.exit("usage: scripts/arena-build.py [--check RULEAN] ARENA RESULTS OUT [NAME...]")
    arena, results, out = args[0], args[1], args[2]
    prefixes = args[3:]
    here = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    pins = pinned(here)
    meta = {t["name"]: t for t in json.load(open(results, encoding="utf-8"))["tests"]}
    names = []
    for n, t in sorted(meta.items()):
        if prefixes:
            if any(n.startswith(p) for p in prefixes):
                names.append(n)
        elif t["outcome"] == "either":
            names.append(n)
    if not names:
        sys.exit("no test is selected")
    out = os.path.abspath(out)
    kind = {"accept": "good", "reject": "bad", "either": "either"}
    failed = []
    for n in names:
        print(n, file=sys.stderr)
        path = os.path.join(arena, "tests", n + ".yaml")
        if not os.path.exists(path):
            failed.append(n + ": no test file")
            continue
        test = fields(path)
        dest = os.path.join(out, kind[meta[n]["outcome"]], n + ".ndjson")
        os.makedirs(os.path.dirname(dest), exist_ok=True)
        work = os.path.join(out, "work", n)
        check = None
        if rulean is not None:
            check = Check(rulean, os.path.join(out, n + ".report.json"))
        if not export(arena, test, work, dest, check):
            failed.append(n + ": the build or the export failed")
            if os.path.exists(dest):
                os.remove(dest)
            continue
        if check is None:
            got = sha256(dest)
        else:
            got = check.digest
        if got != meta[n]["sha256"]:
            failed.append(n + ": the export has the hash " + got + ", not the hash of the results")
            if os.path.exists(dest):
                os.remove(dest)
            continue
        if check is not None:
            want = {"accept": 0, "reject": 1}.get(meta[n]["outcome"])
            pin = pins.get(n)
            if pin is not None:
                want = {"accept": 0, "reject": 1}.get(pin)
            if want is None:
                print(f"  exit {check.code}, the test has no pinned verdict", file=sys.stderr)
            elif check.code != want:
                failed.append(f"{n}: exit {check.code}, expected {want}")
            else:
                print(f"  exit {check.code}, as expected", file=sys.stderr)
    for f in failed:
        print("FAIL " + f)
    if rulean is None:
        print(f"built {len(names) - len(failed)} of {len(names)} tests")
    else:
        print(f"{len(names) - len(failed)} of {len(names)} tests are built and give the expected verdict")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
