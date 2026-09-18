#!/usr/bin/env python3
"""annotate_corpus.py -- put a Sorbet `sig` on every corpus method this fragment can type.

Idempotent: re-running it over an annotated corpus changes nothing. The table below is
the hand work, and it is the *point* of the exercise rather than a preliminary to it --
`Ratchet/Check/Deriv.lean`'s header says why the declared type cannot be inferred here and
cannot be trusted there. Types are written to say what the rung means, not to make
Sorbet quiet: `054-fun-body-mismatch` declares `Integer` for a body that adds `true`,
and Sorbet rejecting that is the rung's content (`expect_sorbet: false` in its meta).

Keys are method names. A name defined more than once in a file (an override, a reopened
class, a nested `def`) takes a **list**, applied in source order -- so the two `speak`s
of `066-class-inheritance-override` are annotated independently.

`extend T::Sig` is added per scope: once at top level if a toplevel `def` is annotated,
and once inside each `class`/`module` body that has one. The strip stack deletes all of
it again (`difftest/ruby/sig_strip.rb`), which is the whole design: the certificate is
about the plain program.
"""
from __future__ import annotations

import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CORPUS = os.path.join(ROOT, "corpus")

V = "void"
def P(*ps: str) -> str:
    return "params(" + ", ".join(ps) + ")"

SIGS: dict[str, dict[str, object]] = {
    # -- tier 6: toplevel methods ------------------------------------------
    "052-simple-fun": {"add": P("x: Integer", "y: Integer") + ".returns(Integer)"},
    "053-fun-wrong-arity": {"add": P("x: Integer", "y: Integer") + ".returns(Integer)"},
    "054-fun-body-mismatch": {"bad": P("x: Integer") + ".returns(Integer)"},
    "055-fun-zero-arg": {"get5": "returns(Integer)"},
    "057-fun-calling-another-fun": {
        "inc": P("x: Integer") + ".returns(Integer)",
        "twice": P("x: Integer") + ".returns(Integer)"},
    "058-fun-three-params": {
        "sum3": P("a: Integer", "b: Integer", "c: Integer") + ".returns(Integer)"},
    "059-fun-returning-array": {
        "make_pair": P("x: Integer", "y: Integer") + ".returns(T::Array[Integer])"},
    "060-fun-recursive-factorial": {"fact": P("n: Integer") + ".returns(Integer)"},
    # -- tier 7: classes ----------------------------------------------------
    "061-class-basic": {"initialize": P("x: Integer", "y: Integer") + "." + V,
                        "getX": "returns(Integer)"},
    "062-class-method-with-param": {"initialize": P("n: Integer") + "." + V,
                                    "add": P("k: Integer") + ".returns(Integer)"},
    "063-class-two-getters": {"initialize": P("x: Integer", "y: Integer") + "." + V,
                              "getX": "returns(Integer)", "getY": "returns(Integer)"},
    "064-class-method-calls-method": {
        "initialize": P("w: Integer", "h: Integer") + "." + V,
        "area": "returns(Integer)", "describe": "returns(String)"},
    "065-class-inheritance-field": {"initialize": P("name: String") + "." + V,
                                    "speak": "returns(String)"},
    "066-class-inheritance-override": {"speak": ["returns(String)", "returns(String)"]},
    "067-class-super-call": {
        "initialize": [P("sides: Integer") + "." + V, V],
        "sides": "returns(Integer)"},
    "068-class-multiple-instances": {"initialize": P("x: Integer") + "." + V,
                                     "getX": "returns(Integer)"},
    "069-class-no-initialize": {"hi": "returns(String)"},
    # `@secret` is never assigned: the honest declared type is `NilClass`, and the
    # emitter still blocks (it will not read an ivar it never saw set).
    "070-class-ivar-lazy-nil": {"reveal": "returns(NilClass)"},
    "071-class-array-of-instances": {"initialize": P("x: Integer") + "." + V},
    "072-class-instance-in-hash": {"initialize": P("x: Integer") + "." + V},
    "073-class-factory-method": {"initialize": P("x: Integer", "y: Integer") + "." + V,
                                 "self.origin": "returns(Point)"},
    "074-class-setter-method": {"initialize": P("size: Integer") + "." + V,
                                "grow": "returns(Integer)"},
    "075-class-instance-as-fun-arg": {"initialize": P("x: Integer") + "." + V,
                                      "getX": "returns(Integer)",
                                      "describe": P("p: Point") + ".returns(Integer)"},
    # `T.self_type` is not in this `Ty`; the concrete class is the honest declaration
    # for a final class and keeps the rung inside the fragment.
    "076-class-self-returning-method": {"initialize": P("x: Integer") + "." + V,
                                        "getX": "returns(Integer)",
                                        "myself": "returns(Point)"},
    # -- tier 9: blocks, lambdas, yield --------------------------------------
    "094-yield-arith": {"twice": "returns(Integer)"},
    "095-block-param-ampersand": {
        "run": P("b: T.proc.params(x: Integer).returns(Integer)") + ".returns(Integer)"},
    "100-lambda-as-argument": {
        "apply": P("f: T.proc.params(x: Integer).returns(Integer)", "v: Integer")
                 + ".returns(Integer)"},
    "105-lambda-explicit-return": {"apply_twice": "returns(Integer)"},
    "109-metaprog-class-reopening": {"a": "returns(Integer)", "b": "returns(Integer)"},
    "113-metaprog-method-missing-fixed-arity": {
        "method_missing": P("name: Symbol") + ".returns(String)"},
    "114-metaprog-method-missing-splat": {
        "method_missing": P("name: Symbol", "args: T.untyped") + ".returns(String)"},
    "115-xc-class-block-param": {
        "a": P("blk: T.proc.params(v: Integer).returns(Integer)") + ".returns(Integer)"},
    "116-xc-class-yield-ivar": {"initialize": P("n: Integer") + "." + V,
                                "bump": "returns(Integer)"},
    "117-xc-lambda-in-ivar": {
        "initialize": P("f: T.proc.params(x: Integer).returns(Integer)") + "." + V,
        "apply": P("v: Integer") + ".returns(Integer)"},
    "119-xc-inherit-implicit-block": {"wrap": "returns(String)", "show": "returns(String)"},
    # A method whose value is its block's has no type this `Ty` can write down; the
    # declaration says so, and the emitter reports `T.untyped` as the boundary.
    "120-xc-block-retypes-capture": {"t": "returns(T.untyped)"},
    "121-xc-block-accumulates-capture": {"t": "returns(T.untyped)"},
    "122-xc-ivar-array-map": {
        "initialize": P("items: T::Array[Integer]") + "." + V,
        "names": "returns(T::Array[String])"},
    "124-xc-block-retypes-ivar": {"initialize": P("x: Integer") + "." + V,
                                  "run": "returns(T.untyped)", "go": "returns(Integer)"},
    # -- tier 12: narrowing ---------------------------------------------------
    "130-narrow-union-subclass": {"speak": "returns(String)", "fetch": "returns(String)",
                                  "make": P("flag: T::Boolean") + ".returns(Animal)"},
    "131-narrow-guard-clause": {
        "first_or_zero": P("a: T::Array[Integer]") + ".returns(Integer)"},
    "135-narrow-backwards-unsafe": {
        "pick": P("flag: T::Boolean") + ".returns(T.any(Integer, String))"},
    "146-const-attr-reader": {"initialize": P("x: Integer", "y: Integer") + "." + V},
    "147-const-alias": {"size": "returns(Integer)"},
    # -- tiers 14-15: parameters and arguments --------------------------------
    "150-param-optional": {
        "greet": P("name: String", "greeting: String") + ".returns(String)"},
    "151-param-optional-uses-earlier": {
        "pad": P("s: String", "n: Integer") + ".returns(Integer)"},
    "152-param-rest": {"total": P("ns: Integer") + ".returns(Integer)"},
    "153-param-req-then-rest": {
        "tag": P("first: Integer", "rest: Integer") + ".returns(Integer)"},
    "154-param-keyword": {"build": P("type: String", "name: String") + ".returns(String)"},
    "155-param-keyword-default": {
        "build": P("name: String", "version: T.nilable(String)") + ".returns(String)"},
    "156-param-kwrest": {"opts": P("kw: T.untyped") + ".returns(Integer)"},
    "157-param-block": {
        "run": P("b: T.proc.params(x: Integer).returns(Integer)") + ".returns(Integer)"},
    "158-arg-splat-call": {"add": P("a: Integer", "b: Integer") + ".returns(Integer)"},
    "160-arg-kwsplat-call": {"build": P("type: String", "name: String") + ".returns(String)"},
    "161-param-shorthand-kwarg": {
        "build": P("type: String", "name: String") + ".returns(String)"},
    "162-param-all-kinds": {
        "f": P("a: Integer", "b: Integer", "rest: Integer", "c: Integer", "d: Integer",
               "kw: T.untyped", "blk: T.untyped") + ".returns(Integer)"},
    "163-param-arity-unsafe": {"f": P("a: Integer") + ".returns(Integer)"},
    "164-param-missing-keyword-unsafe": {
        "build": P("type: String", "name: String") + ".returns(String)"},
    "167-str-interpolation-in-method": {"initialize": P("v: Integer") + "." + V,
                                        "to_s": "returns(String)"},
    # -- tier 16: control flow -------------------------------------------------
    "192-ctl-rescue": {"parse": P("s: String") + ".returns(Integer)"},
    "194-ctl-raise-custom": {"cmp": P("a: T.nilable(Integer)") + ".returns(Integer)"},
    "196-ctl-return-early": {
        "first_or": P("a: T::Array[Integer]", "d: Integer") + ".returns(Integer)"},
    "197-ctl-case-when-string": {"kind": P("t: String") + ".returns(String)"},
    "199-lib-comparable": {"initialize": P("n: Integer") + "." + V,
                           "n": "returns(Integer)",
                           "<=>": P("other: Rev") + ".returns(Integer)"},
    # -- the unsafe rungs: annotated to say what the program means, not to pass ---
    "236-nested-def-redefines-unsafe": {"bar": ["returns(Integer)", "returns(String)"],
                                        "foo": "returns(Integer)"},
    "237-shadowed-lambda-unsafe": {"lambda": "returns(Integer)"},
    "238-yield-two-types-string-to-s": {"hello": "returns(T.untyped)"},
    "239-method-missing-bare-name-unsafe": {
        "method_missing": P("n: T.untyped") + ".returns(Integer)"},
    "240-ivar-asgn-stale-inst-unsafe": {"initialize": V, "get": "returns(Integer)",
                                        "leak": "returns(Integer)"},
    "241-reopen-integer-is-a-unsafe": {"is_a?": P("c: T.untyped") + ".returns(String)"},
    "242-array-lit-element-mutated-unsafe": {"initialize": V, "get": "returns(Integer)"},
    "244-self-class-subclass-unsafe": {"whoami": "returns(T.class_of(C))",
                                       "tag": ["returns(Integer)", "returns(String)"]},
    "247-rescue-subclass-message-unsafe": {"message": "returns(Integer)"},
    "249-nilq-narrow-redefined-unsafe": {"nil?": "returns(T::Boolean)"},
    "251-proc-return-escapes-unsafe": {"f": "returns(Integer)"},
    "252-iter-block-return-escapes-unsafe": {"h": "returns(Integer)"},
    "253-yield-block-return-escapes-unsafe": {"m": "returns(T.untyped)",
                                              "h": "returns(Integer)"},
    "254-block-pass-proc-return-escapes-unsafe": {"h": "returns(Integer)"},
}

DEF = re.compile(r"^(\s*)def\s+(self\.)?([^\s(;]+)")
SCOPE = re.compile(r"^(\s*)(class|module)\b")


def annotate(path: str, table: dict) -> bool:
    with open(path) as fh:
        lines = fh.read().splitlines()
    if any("extend T::Sig" in ln for ln in lines):
        return False                                   # already annotated
    # Which sig goes on which `def`, by source order within each name.
    seen: dict[str, int] = {}
    out: list[str] = []
    scopes_needing_sig: set[int] = set()               # index of the class/module line
    for i, ln in enumerate(lines):
        m = DEF.match(ln)
        if not m:
            out.append(ln)
            continue
        indent, slf, name = m.group(1), m.group(2) or "", m.group(3)
        key = slf + name
        entry = table.get(key)
        if entry is None:
            out.append(ln)
            continue
        k = seen.get(key, 0)
        seen[key] = k + 1
        body = entry[k] if isinstance(entry, list) else entry
        out.append(f"{indent}sig {{ {body} }}")
        out.append(ln)
        # The scope this `def` lives in needs `extend T::Sig`.
        owner = -1
        for j in range(i - 1, -1, -1):
            s = SCOPE.match(lines[j])
            if s and len(s.group(1)) < len(indent):
                owner = j
                break
        scopes_needing_sig.add(owner)

    if not seen:
        return False

    # Insert `extend T::Sig` once per scope, walking bottom-up so indices stay valid.
    text = "\n".join(out)
    res: list[str] = []
    inserted_at: set[int] = set()
    oi = 0                                             # index into the *original* lines
    for ln in out:
        res.append(ln)
        if oi < len(lines) and ln == lines[oi]:
            if oi in scopes_needing_sig and oi not in inserted_at:
                s = SCOPE.match(lines[oi])
                res.append(" " * (len(s.group(1)) + 2) + "extend T::Sig")
                inserted_at.add(oi)
            oi += 1
    if -1 in scopes_needing_sig:
        # A toplevel `def`: `extend T::Sig` goes right after the `# typed:` sigil.
        for i, ln in enumerate(res):
            if ln.startswith("# typed:"):
                res.insert(i + 1, "extend T::Sig")
                break
    text = "\n".join(res) + "\n"
    with open(path, "w") as fh:
        fh.write(text)
    return True


def main(argv: list[str]) -> int:
    n = 0
    missing = []
    for base, table in sorted(SIGS.items()):
        path = os.path.join(CORPUS, base + ".rb")
        if not os.path.exists(path):
            missing.append(base)
            continue
        if annotate(path, table):
            n += 1
        meta_path = os.path.join(CORPUS, base + ".meta.json")
        with open(meta_path) as fh:
            meta = json.load(fh)
        meta["annotated"] = True
        with open(meta_path, "w") as fh:
            json.dump(meta, fh, indent=2)
            fh.write("\n")
    print(f"annotated {n} rungs ({len(SIGS)} in the table)")
    for b in missing:
        print(f"  !! no such rung: {b}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
