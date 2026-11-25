#!/usr/bin/env python3
"""Compute the primitive pinning digests of spec 05.8 from lean4export NDJSON files.

Usage: scripts/pin-digests.py [--axiom] EXPORT...

The script reads each export, computes the digest of each target declaration that it finds, and writes the Rust array of crates/rulean-core/src/pin_ref_v4_35.in to stdout. With --axiom, the script writes the array of crates/rulean-core/src/pin_axiom_v4_35.in. This array has the digest of the axiom that has the level parameters and the type of each target definition. For a target inductive type, the entry is zero. Two exports that give different digests for one target are an error. A target that no export has is an error.

The encoding is the encoding of crates/rulean-core/src/pin.rs. A change to one file must have the same change in the other file.
"""

import hashlib
import json
import sys

TARGETS = [
    "Nat",
    "Nat.add",
    "Nat.sub",
    "Nat.mul",
    "Nat.pow",
    "Nat.gcd",
    "Nat.mod",
    "Nat.div",
    "Nat.beq",
    "Nat.ble",
    "Nat.land",
    "Nat.lor",
    "Nat.xor",
    "Nat.shiftLeft",
    "Nat.shiftRight",
    "String",
    "String.ofList",
    "Char",
    "Char.ofNat",
    "List",
    "eagerReduce",
]


def u64(v):
    return v.to_bytes(8, "little")


def bstr(b):
    return u64(len(b)) + b


def h(tag, *parts):
    return hashlib.sha256(bytes([tag]) + b"".join(parts)).digest()


def nat_bytes(v):
    return v.to_bytes((v.bit_length() + 7) // 8, "little")


def digests(path, axiom):
    names = {0: h(0x01)}
    text = {0: ""}
    levels = {0: h(0x08)}
    exprs = {}
    out = {}

    def lparams(ps):
        return u64(len(ps)) + b"".join(names[p] for p in ps)

    for line in open(path, encoding="utf-8"):
        o = json.loads(line)
        if "meta" in o:
            continue
        if "in" in o:
            i = o["in"]
            if "str" in o:
                pre, s = o["str"]["pre"], o["str"]["str"]
                names[i] = h(0x02, names[pre], bstr(s.encode("utf-8")))
                text[i] = (text[pre] + "." if text[pre] else "") + s
            else:
                pre, k = o["num"]["pre"], o["num"]["i"]
                names[i] = h(0x03, names[pre], u64(k))
                text[i] = (text[pre] + "." if text[pre] else "") + str(k)
            continue
        if "il" in o:
            i = o["il"]
            if "succ" in o:
                levels[i] = h(0x09, levels[o["succ"]])
            elif "max" in o:
                levels[i] = h(0x0A, levels[o["max"][0]], levels[o["max"][1]])
            elif "imax" in o:
                levels[i] = h(0x0B, levels[o["imax"][0]], levels[o["imax"][1]])
            else:
                levels[i] = h(0x0C, names[o["param"]])
            continue
        if "ie" in o:
            i = o["ie"]
            if "bvar" in o:
                exprs[i] = h(0x10, u64(o["bvar"]))
            elif "sort" in o:
                exprs[i] = h(0x11, levels[o["sort"]])
            elif "const" in o:
                us = o["const"]["us"]
                exprs[i] = h(0x12, names[o["const"]["name"]], u64(len(us)), *[levels[u] for u in us])
            elif "app" in o:
                exprs[i] = h(0x13, exprs[o["app"]["fn"]], exprs[o["app"]["arg"]])
            elif "lam" in o:
                exprs[i] = h(0x14, exprs[o["lam"]["type"]], exprs[o["lam"]["body"]])
            elif "forallE" in o:
                exprs[i] = h(0x15, exprs[o["forallE"]["type"]], exprs[o["forallE"]["body"]])
            elif "letE" in o:
                b = o["letE"]
                exprs[i] = h(0x16, exprs[b["type"]], exprs[b["value"]], exprs[b["body"]])
            elif "natVal" in o:
                exprs[i] = h(0x17, bstr(nat_bytes(int(o["natVal"]))))
            elif "strVal" in o:
                exprs[i] = h(0x18, bstr(o["strVal"].encode("utf-8")))
            elif "proj" in o:
                b = o["proj"]
                exprs[i] = h(0x19, names[b["typeName"]], u64(b["idx"]), exprs[b["struct"]])
            elif "mdata" in o:
                exprs[i] = exprs[o["mdata"]["expr"]]
            else:
                sys.exit(f"{path}: unknown expression {o}")
            continue
        if "def" in o:
            d = o["def"]
            n = text[d["name"]]
            if n in TARGETS and d["safety"] == "safe" and axiom:
                out[n] = h(0x22, lparams(d["levelParams"]), exprs[d["type"]])
            elif n in TARGETS and d["safety"] == "safe":
                out[n] = h(0x20, lparams(d["levelParams"]), exprs[d["type"]], exprs[d["value"]])
        if "inductive" in o:
            b = o["inductive"]
            ctors = {c["name"]: c for c in b["ctors"]}
            for t in b["types"]:
                n = text[t["name"]]
                if n in TARGETS and not t["isUnsafe"]:
                    parts = [lparams(t["levelParams"]), exprs[t["type"]], u64(t["numParams"]), u64(t["numIndices"]), u64(len(t["ctors"]))]
                    for c in t["ctors"]:
                        parts.append(names[c])
                        parts.append(exprs[ctors[c]["type"]])
                    out[n] = bytes(32) if axiom else h(0x21, *parts)
    return out


def main():
    args = sys.argv[1:]
    axiom = len(args) > 0 and args[0] == "--axiom"
    if axiom:
        args = args[1:]
    if len(args) < 1:
        sys.exit("usage: scripts/pin-digests.py [--axiom] EXPORT...")
    found = {}
    for path in args:
        for n, d in digests(path, axiom).items():
            if n in found and found[n] != d:
                sys.exit(f"{path}: the digest of {n} is not the digest of an earlier export")
            found[n] = d
    missing = [n for n in TARGETS if n not in found]
    if missing:
        sys.exit("no export has " + ", ".join(missing))
    print("// Generated by scripts/pin-digests.py. Do not edit.")
    print("[")
    for n in TARGETS:
        print(f"    // {n}")
        print("    [" + ", ".join(f"0x{b:02x}" for b in found[n]) + "],")
    print("]")


if __name__ == "__main__":
    main()
