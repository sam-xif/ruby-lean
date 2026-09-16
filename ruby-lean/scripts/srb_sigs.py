#!/usr/bin/env python3
"""`srb -p symbol-table` -> a signature manifest in **this package's** `Ty` encoding.

A vendored, retargeted copy of `../sorbet-cert/srb_sigs.py` (that PoC's reader, whose
header documents *why* the symbol table rather than the `sig` source text: resolved sigs,
method owners, and absence-of-annotation all in one pass). Two differences, both forced:

* the wire encoding is `Ratchet/Ty.lean`'s `{"tag": ...}`, not `RubyCore`'s `{"k": ...}`;
* the type grammar is this package's `Ty`, which has `hashOf`/`inst`/`never` that the
  other one does not, and no `Ty.any` inference (see `Ratchet/Ty.lean`: `.any` is
  "only usable as a declared parameter type", which is exactly this file's output).

Nothing here is trusted. `../docs/semantics/certificate-language.md` §1: generation owns
completeness, validation owns soundness. A signature read wrong costs a body that fails
to certify, never a wrong accept -- and `Ratchet/Deriv.lean`'s header says where that
argument bottoms out.

**`T.untyped` maps to no claim at all** (not to `Ty.any`), so an unannotated parameter
makes the emitter block with a named reason rather than quietly widening. That is the
fragment gate, and it is what makes "rewrite the corpus to be typed" a measurable job:
`--untyped=any` turns it off.

Output: `{"version":1, "file":, "sigs":[{cls,name,params:[{name,ty}],ret,line}],
"dropped":[{cls,name,why}], "errors": <srb's own diagnostics count>}`.
"""
from __future__ import annotations

import argparse
import glob
import json
import os
import re
import subprocess
import sys


def find_sorbet() -> str:
    if os.environ.get("SORBET"):
        return os.environ["SORBET"]
    pats = [
        "/opt/homebrew/lib/ruby/gems/*/gems/sorbet-static-*/libexec/sorbet",
        os.path.expanduser("~/.gem/ruby/*/gems/sorbet-static-*/libexec/sorbet"),
        "/usr/local/lib/ruby/gems/*/gems/sorbet-static-*/libexec/sorbet",
    ]
    for pat in pats:
        hits = sorted(glob.glob(pat))
        if hits:
            return hits[-1]
    return "srb"


# --------------------------------------------------------------------------
# The type mapping, into `Ratchet/Ty.lean`'s grammar
# --------------------------------------------------------------------------

GROUND = {
    "Integer": {"tag": "int"},
    "Float": {"tag": "float"},
    "Symbol": {"tag": "sym"},
    "NilClass": {"tag": "nilT"},
    "TrueClass": {"tag": "bool"},
    "FalseClass": {"tag": "bool"},
    "T::Boolean": {"tag": "bool"},
}

# `Ty.cls` is for the builtin classes, "whose instances have no ivars this checker
# models" (`Ratchet/Ty.lean`). A *user* class's instances are `Ty.inst name <spine>`,
# and the spine is not in the signature -- it comes from the instantiation. So a bare
# user-class name maps to `.cls`, which is a **known divergence**, recorded in
# `emit_deriv.rb`'s header as the gap it is rather than papered over here.
BUILTIN_CLS = {"String", "Regexp", "Array", "Hash", "Object", "Exception",
               "StandardError", "RuntimeError", "ArgumentError", "TypeError",
               "NameError", "NoMethodError", "ZeroDivisionError", "IndexError",
               "KeyError", "RangeError", "IOError", "FrozenError",
               "NotImplementedError"}

FLAT_NAME = re.compile(r"^[A-Z][A-Za-z0-9_]*$")


def split_args(s: str) -> list[str]:
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


def to_ty(s: str, untyped: str = "exclude") -> dict | None:
    """A Sorbet type string to a `Ty`, or `None` for "no claim made". Never raises."""
    s = s.strip()
    if not s:
        return None
    if s in GROUND:
        return GROUND[s]
    if s == "T.untyped":
        return {"tag": "any"} if untyped == "any" else None
    if s in ("T.noreturn", "T.absurd"):
        return {"tag": "never"}
    # A `.void` return: "a value the caller may not use". `Ty.any` is the same reading
    # on the declaration side -- `Ratchet/Ty.lean` calls it "some value, of a type the
    # checker does not pin ... only usable as a declared parameter type" -- and nothing
    # propagates it, because `.any` has no `PrimSig` row: the first send to a `.void`
    # result blocks. Mapping it to `nilT` would be a lie (a `.void` method returns its
    # body's value at runtime); dropping it would make every `initialize` unusable.
    if s in ("Sorbet::Private::Static::Void", "void"):
        return {"tag": "any"}
    if s.startswith("T.nilable(") and s.endswith(")"):
        inner = to_ty(s[len("T.nilable("):-1], untyped)
        if inner is None:
            return None
        return inner if inner == {"tag": "nilT"} else {"tag": "nilable", "elem": inner}
    if s.startswith("T.class_of(") and s.endswith(")"):
        inner = s[len("T.class_of("):-1].strip()
        return {"tag": "clsOf", "name": inner} if FLAT_NAME.match(inner) else None
    if s.startswith("T::Array[") and s.endswith("]"):
        inner = to_ty(s[len("T::Array["):-1], untyped)
        return {"tag": "arrayOf", "elem": inner} if inner else None
    if s.startswith("T::Hash[") and s.endswith("]"):
        parts = split_args(s[len("T::Hash["):-1])
        if len(parts) != 2:
            return None
        k, v = (to_ty(p, untyped) for p in parts)
        return {"tag": "hashOf", "key": k, "val": v} if k and v else None
    if s.startswith("T.any(") and s.endswith(")"):
        parts = split_args(s[len("T.any("):-1])
        tys = [to_ty(p, untyped) for p in parts]
        if len(tys) != 2 or any(t is None for t in tys):
            return None
        a, b = tys
        if a == b:
            return a
        nil = {"tag": "nilT"}
        if a == nil:
            return b if b == nil else {"tag": "nilable", "elem": b}
        if b == nil:
            return {"tag": "nilable", "elem": a}
        return {"tag": "union", "l": a, "r": b}
    if FLAT_NAME.match(s):
        return {"tag": "cls", "name": s}
    return None


# --------------------------------------------------------------------------
# Reading `-p symbol-table`
# --------------------------------------------------------------------------

METHOD = re.compile(
    r"^\s*method ::(?P<owner>\S+?)#(?P<name>[^\s(]+)"
    r"(?P<vis> : \w+)? \((?P<args>[^)]*)\)"
    r"(?: -> (?P<ret>.+?))? @ (?P<loc>\S+)\s*$"
)
ARGUMENT = re.compile(
    r"^\s*argument (?P<name>[^<]+)<(?P<kind>[^>]*)>(?: -> (?P<ty>.+?))? @ "
)

SYNTHETIC = ("<static-init>", "<block>", "<any>")


def run(path: str, binary: str, args: list[str]) -> subprocess.CompletedProcess:
    return subprocess.run(
        [binary, "--no-config", "--silence-dev-message", "--typed=true", *args, path],
        capture_output=True, text=True)


def parse(text: str, target: str, untyped: str) -> tuple[list, list]:
    base = os.path.basename(target)
    sigs: list[dict] = []
    dropped: list[dict] = []
    cur: dict | None = None

    def close(entry: dict | None) -> None:
        if entry is None:
            return
        common = {"cls": entry["owner"], "name": entry["name"], "line": entry["line"]}
        if entry["owner_dropped"]:
            dropped.append({**common, "why": entry["owner_dropped"]})
            return
        if entry["raw_ret"] is None:
            dropped.append({**common, "why": "no declared return type"})
            return
        ret = to_ty(entry["raw_ret"], untyped)
        if ret is None:
            dropped.append({**common, "why": f"return type not in Ty: {entry['raw_ret']}"})
            return
        params = []
        for name, raw_ty in entry["args"]:
            if raw_ty is None:
                dropped.append({**common, "why": f"no declared type for parameter {name}"})
                return
            ty = to_ty(raw_ty, untyped)
            if ty is None:
                dropped.append({**common, "why": f"parameter {name} not in Ty: {raw_ty}"})
                return
            params.append({"name": name, "ty": ty})
        sigs.append({**common, "params": params, "ret": ret})

    for line in text.splitlines():
        m = METHOD.match(line)
        if m:
            close(cur)
            cur = None
            owner, name, loc = m.group("owner"), m.group("name"), m.group("loc")
            if os.path.basename(loc.rsplit(":", 1)[0]) != base:
                continue
            if name in SYNTHETIC:
                continue
            why = None
            if owner.startswith("<Class:"):
                why = "singleton method (def self.x) -- outside the fragment"
            elif "::" in owner:
                why = f"namespaced owner {owner} -- Ty.cls carries flat names here"
            cur = {"owner": owner.split("::")[-1] if why is None else owner,
                   "name": name, "line": int(loc.split(":")[-1]),
                   "raw_ret": m.group("ret"), "args": [], "owner_dropped": why}
            continue
        if cur is None:
            continue
        a = ARGUMENT.match(line)
        if a:
            if a.group("kind") == "block" or a.group("name").strip() == "<blk>":
                continue
            cur["args"].append((a.group("name").strip(), a.group("ty")))
            continue
        if line.strip() and not line.startswith((" " * 6, "\t")):
            close(cur)
            cur = None
    close(cur)
    return sigs, dropped


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("file")
    ap.add_argument("--untyped", choices=["exclude", "any"], default="exclude")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args(argv)

    binary = find_sorbet()
    # Two passes: the symbol table (which srb prints even for a file with type errors),
    # and a plain check whose diagnostics are the rung's `expect_sorbet` answer.
    table = run(args.file, binary, ["-p", "symbol-table"])
    check = run(args.file, binary, [])
    if not table.stdout.strip():
        print(f"srb produced no symbol table for {args.file} (binary: {binary})",
              file=sys.stderr)
        return 2
    sigs, dropped = parse(table.stdout, args.file, args.untyped)
    out = {"version": 1, "file": args.file, "sorbet": binary,
           "sigs": sigs, "dropped": dropped,
           "srb_clean": check.returncode == 0,
           "srb_diagnostics": (check.stderr or check.stdout).strip().splitlines()[:20]}
    print(json.dumps(out, indent=1))
    if not args.quiet:
        for d in dropped:
            print(f"  dropped {d['cls']}#{d['name']} -- {d['why']}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
