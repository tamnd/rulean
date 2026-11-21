#!/usr/bin/env python3
"""Build the exports of Arena tests that are not in the Arena tarball.

Usage: scripts/arena-build.py ARENA RESULTS OUT [NAME...]

ARENA is a checkout of the lean-kernel-arena repository at the commit of RESULTS. RESULTS is the results.json of scripts/arena-fetch.sh. OUT gets the exports in the layout of scripts/arena-fetch.sh: an accept test goes to OUT/good, a reject test goes to OUT/bad and an "either" test goes to OUT/either. Each NAME selects the tests whose name starts with NAME. Without NAME, the script builds the "either" tests.

The script does what lka.py of the Arena does for a test with a `file`, `leanfile` or `dir` and `module` field: it copies the file, or it builds the Lean module with lake and exports it with the `leanexport` binary of the Lean toolchain. The toolchain must be on PATH, and it must be the toolchain of ARENA/tests/lean-toolchain. A test with a `url` field, such as Mathlib, is not built.

The script keeps only the exports whose SHA-256 is the hash in RESULTS, because the expected verdicts and the Arena numbers are for those exports. It exits with 1 if a selected test was not built or has another hash.
"""

import hashlib
import json
import os
import shutil
import subprocess
import sys

LAKEFILE = 'name = "test"\n\n[[lean_lib]]\nname = "Test"'


def fields(path):
    """The top-level `key: value` fields of a test file. The values that the script reads are one line long."""
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


def export(arena, test, work, dest):
    """Writes the export of one test to dest. The result is False on a failure."""
    if "file" in test:
        shutil.copy(os.path.join(arena, test["file"]), dest)
        return True
    if os.path.exists(work):
        shutil.rmtree(work)
    if "leanfile" in test:
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
    if not run(["lake", "build", module], work):
        return False
    leanexport = shutil.which("leanexport")
    if leanexport is None:
        print("  leanexport is not on PATH", file=sys.stderr)
        return False
    cmd = ["lake", "env", leanexport, module]
    if test.get("export-decls"):
        cmd += ["--"] + test["export-decls"]
    with open(dest, "wb") as out:
        return run(cmd, work, out)


def main():
    if len(sys.argv) < 4:
        sys.exit("usage: scripts/arena-build.py ARENA RESULTS OUT [NAME...]")
    arena, results, out = sys.argv[1], sys.argv[2], sys.argv[3]
    prefixes = sys.argv[4:]
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
        if "url" in test:
            failed.append(n + ": the test needs a git checkout, which this script does not do")
            continue
        dest = os.path.join(out, kind[meta[n]["outcome"]], n + ".ndjson")
        os.makedirs(os.path.dirname(dest), exist_ok=True)
        work = os.path.join(out, "work", n)
        if not export(arena, test, work, dest):
            failed.append(n + ": the build or the export failed")
            if os.path.exists(dest):
                os.remove(dest)
            continue
        got = sha256(dest)
        if got != meta[n]["sha256"]:
            failed.append(n + ": the export has the hash " + got + ", not the hash of the results")
            os.remove(dest)
    for f in failed:
        print("FAIL " + f)
    print(f"built {len(names) - len(failed)} of {len(names)} tests")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
