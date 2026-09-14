#!/usr/bin/env python3
"""emit_deriv.py -- the **untrusted** emitter: a sig-stripped AST + Sorbet's signatures,
out a `Deriv` (`Ratchet/Deriv.lean`).

    emit_deriv.py --ast build/NNN.ast.json --sigs build/NNN.sigs.json

Stage 4 of `scripts/build_rung.sh`'s five, and the only one that has to think. Nothing
here is trusted: it proposes a derivation, and `validateD` accepts or rejects it. The
contract is `certificate-language.md` §1's -- generation owns completeness, validation
owns soundness -- so this file is allowed to be wrong in exactly one direction: it may
**block** (say "I cannot build a derivation for this"), and it may propose a derivation
that the checker then rejects. It may not cause a wrong accept, because every type it
writes down is re-derived on the other side.

## The program it is about

The **sig-stripped** one. `sorbet-cert/README.md` §1 is the argument, and it is not an
efficiency matter: `sorbet-runtime` executes as ordinary Ruby, so a `sig` is ~217
machine steps of reflective metaprogramming inside the program being certified. Stage 2
deletes the annotations and Sorbet's answer survives only as data in `sigs.json`, handed
back in here.

## Known gap: a user class's instance type

`Ratchet/Ty.lean` types an instance of a user class as `.inst name <ivar spine>`,
because "an object's observable type is not its class name" -- `Point.new(1,2)` and
`Point.new("a","b")` are both `Point`s. A Sorbet signature says `Point` and carries no
spine, so `srb_sigs.py` maps it to `.cls "Point"`, which is **not** the type the checker
will synthesize for the receiver. The emitter reconstructs a spine where it can (from
`initialize`'s signature and the `@x = x` assignments in its body) and uses `.cls` where
it cannot. This is the first thing `check` will reject, and it is the right place for it
to be rejected: a named divergence in an untrusted emitter, not an assumption.

## Output

`{"status":"ok","deriv":{...}}` or `{"status":"blocked","why":"..."}`, on stdout, exit 0
either way -- a block is a measurement, not a failure (`found-issues.md` §F24 vs §F25:
run the control).
"""
from __future__ import annotations

import argparse
import json
import sys

# --------------------------------------------------------------------------
# `Ty` constructors, in `Ratchet/Ty.lean`'s wire encoding
# --------------------------------------------------------------------------

INT = {"tag": "int"}
BOOL = {"tag": "bool"}
NIL = {"tag": "nilT"}
SYM = {"tag": "sym"}
FLOAT = {"tag": "float"}
NEVER = {"tag": "never"}
STR = {"tag": "cls", "name": "String"}
IVAR0 = {"tag": "ivar0"}


def cls(n: str) -> dict:
    return {"tag": "cls", "name": n}


def array_of(t: dict) -> dict:
    return {"tag": "arrayOf", "elem": t}


def hash_of(k: dict, v: dict) -> dict:
    return {"tag": "hashOf", "key": k, "val": v}


def spine(pairs: list[tuple[str, dict]]) -> dict:
    """An ivar/capture spine, built right to left (`Ty.ivarCons`)."""
    out = IVAR0
    for name, ty in reversed(pairs):
        out = {"tag": "ivarCons", "name": name, "ty": ty, "rest": out}
    return out


def join(a: dict, b: dict) -> dict:
    """Mirror `joinT`: structural cases first, then an ordered, deduplicated union."""
    if a == NEVER:
        return b
    if b == NEVER:
        return a
    if a == b:
        return a
    if a == NIL:
        return {"tag": "nilable", "elem": b}
    if b == NIL:
        return {"tag": "nilable", "elem": a}
    if a == {"tag": "nilable", "elem": b}:
        return a
    if b == {"tag": "nilable", "elem": a}:
        return b

    def members(t):
        if t.get("tag") == "union":
            return members(t["l"]) + members(t["r"])
        return [t]

    unique = []
    for t in members(a) + members(b):
        if t not in unique:
            unique.append(t)
    out = unique[-1]
    for t in reversed(unique[:-1]):
        out = {"tag": "union", "l": t, "r": out}
    return out


class Blocked(Exception):
    """Out of the emitter's fragment. The message is the measurement."""


# --------------------------------------------------------------------------
# The builtin signature table
# --------------------------------------------------------------------------
#
# A **subset** of `Ratchet/Judge.lean`'s `PrimSig`, written here only so the emitter can
# propose a `Deriv.prim`'s result type. It is not the authority: `check` re-derives the
# row from `PrimSig` itself, so a row missing here costs a block and a row wrong here
# costs a reject. Keyed by (receiver tag or class name, method, arity).

def prim_ret(recv: dict, m: str, args: list[dict]) -> dict | None:
    t = recv.get("tag")
    n = recv.get("name")
    if t == "int":
        if m in ("+", "-", "*", "/", "<=>") and args == [INT]:
            return INT
        if m in ("<", "<=", ">", ">=") and args == [INT]:
            return BOOL
        if m == "to_s" and not args:
            return STR
        if m == "zero?" and not args:
            return BOOL
    if t == "cls" and n == "String":
        if m == "+" and args == [STR]:
            return STR
        if m in ("strip", "downcase", "upcase") and not args:
            return STR
        if m == "length" and not args:
            return INT
        if m == "empty?" and not args:
            return BOOL
        if m == "start_with?" and args == [STR]:
            return BOOL
        if m == "split" and args == [STR]:
            return array_of(STR)
    if t == "arrayOf":
        if m == "length" and not args:
            return INT
        if m == "empty?" and not args:
            return BOOL
        if m == "[]" and args == [INT]:
            return {"tag": "nilable", "elem": recv["elem"]}
        if m == "<<" and args == [recv["elem"]]:
            return recv
    if t == "hashOf":
        if m == "length" and not args:
            return INT
        if m == "[]" and len(args) == 1:
            return {"tag": "nilable", "elem": recv["val"]}
        if m == "fetch" and len(args) == 1:
            return recv["val"]
    if t == "sym" and m == "to_s" and not args:
        return STR
    if t == "bool" and m == "!" and not args:
        return BOOL
    # `Judge.prim`'s `objEq` row: `==` at an `EqSafe` receiver, argument unconstrained.
    if m == "==" and len(args) == 1 and t in ("int", "float", "bool", "nilT", "sym",
                                              "cls", "hashOf"):
        return BOOL
    if m == "nil?" and not args and t in ("int", "float", "bool", "nilT", "sym", "cls",
                                          "arrayOf", "hashOf"):
        return BOOL
    return None


# --------------------------------------------------------------------------
# The emitter
# --------------------------------------------------------------------------

class Emitter:
    def __init__(self, sigs: dict):
        # (owner, name) -> {"params": [{name,ty}], "ret": ty}
        self.sigs: dict[tuple[str, str], dict] = {}
        for s in sigs.get("sigs", []):
            self.sigs[(s["cls"], s["name"])] = s
        self.dropped = {(d["cls"], d["name"]): d["why"] for d in sigs.get("dropped", [])}
        self.env: dict[str, dict] = {}          # locals
        self.ivars: dict[str, dict] = {}        # the current self's ivars
        self.cls_ivars: dict[str, list] = {}    # class name -> [(ivar, ty)]
        self.supers: dict[str, str] = {}        # class name -> superclass name
        self.self_cls: str | None = None

    # -- helpers ----------------------------------------------------------

    def sig_for(self, owner: str, name: str) -> dict:
        """The declared signature of `owner#name`, inherited if the class does not
        define it. Sorbet reports the **owner**, so an inherited method is filed under
        the superclass and the walk is this package's, not the manifest's."""
        cur: str | None = owner
        while cur is not None:
            key = (cur, name)
            if key in self.sigs:
                return self.sigs[key]
            if key in self.dropped:
                raise Blocked(f"{cur}#{name}: {self.dropped[key]}")
            cur = self.supers.get(cur)
        raise Blocked(f"no signature for {owner}#{name}")

    def as_inst(self, t: dict) -> dict:
        """A declared `Ty.cls C` for a *user* class C, recovered as `Ty.inst C <spine>`.

        The header's known gap: a Sorbet signature says `Point` and carries no ivar
        spine, but `Ratchet/Ty.lean` types an instance as `.inst name <spine>`. Where
        the class body has been seen, the spine is known and this closes the gap; where
        it has not, the `.cls` stays and the first method call on it blocks."""
        if t.get("tag") == "cls" and t.get("name") in self.cls_ivars:
            return {"tag": "inst", "name": t["name"],
                    "ivars": spine(self.cls_ivars[t["name"]])}
        return t

    # -- the walk ---------------------------------------------------------

    def go(self, node) -> tuple[dict, dict]:
        """`node` -> (deriv, type). Raises `Blocked` outside the fragment."""
        tag = node[0]
        m = getattr(self, "n_" + tag.replace("?", "_q"), None)
        if m is None:
            raise Blocked(f"no rule for AST node '{tag}'")
        return m(node)

    def go_all(self, nodes) -> tuple[list, list]:
        ds, ts = [], []
        for n in nodes:
            d, t = self.go(n)
            ds.append(d)
            ts.append(t)
        return ds, ts

    # literals
    def n_int(self, n):   return {"rule": "intLit", "n": n[1]}, INT
    def n_str(self, n):   return {"rule": "strLit", "s": n[1]}, STR
    def n_sym(self, n):   return {"rule": "symLit", "s": n[1]}, SYM
    def n_true(self, n):  return {"rule": "truLit"}, BOOL
    def n_false(self, n): return {"rule": "flsLit"}, BOOL
    def n_nil(self, n):   return {"rule": "nilLit"}, NIL
    def n_self(self, n):
        if self.self_cls is None:
            raise Blocked("`self` outside a class body")
        return {"rule": "selfExpr"}, {"tag": "inst", "name": self.self_cls,
                                      "ivars": spine(list(self.ivars.items()))}

    def n_flt(self, n):
        # `Expr.flt` carries IEEE-754 bits; the AST carries the double.
        import struct
        bits = struct.unpack("<Q", struct.pack("<d", float(n[1])))[0]
        return {"rule": "fltLit", "bits": bits}, FLOAT

    # variables
    def n_var(self, n):
        kind, name = n[1], n[2]
        if kind == "ivar":
            if name not in self.ivars:
                raise Blocked(f"read of unset ivar {name}")
            return {"rule": "ivarRead", "name": name, "ty": self.ivars[name]}, self.ivars[name]
        if kind != "local":
            raise Blocked(f"{kind} variables are outside the fragment")
        if name not in self.env:
            raise Blocked(f"read of unbound local {name}")
        return {"rule": "var", "kind": "lvar", "name": name}, self.env[name]

    def n_vasgn(self, n):
        kind, name, val = n[1], n[2], n[3]
        d, t = self.go(val)
        if kind == "ivar":
            self.ivars[name] = t
            return {"rule": "ivarAsgn", "name": name, "value": d}, t
        if kind != "local":
            raise Blocked(f"{kind} assignment is outside the fragment")
        self.env[name] = t
        return {"rule": "vasgn", "kind": "lvar", "name": name, "value": d}, t

    def n_const(self, n):
        return {"rule": "constCls", "name": n[1]}, {"tag": "clsOf", "name": n[1]}

    # control
    def n_seq(self, n):
        ds, ts = self.go_all(n[1:])
        return {"rule": "seq", "stmts": ds}, (ts[-1] if ts else NIL)

    def n_if(self, n):
        dc, _ = self.go(n[1])
        # Both branches are typed in the incoming environment's *copy*: this emitter does
        # not join environments, so a branch that rebinds a local is a block rather than
        # a guess (`Judge.if'` joins; reproducing that here is not this commit's job).
        before = dict(self.env)
        dt, tt = self.go(n[2])
        then_env = self.env
        self.env = dict(before)
        if n[3] is None:
            de, te = None, NIL
        else:
            de_, te = self.go(n[3])
            de = de_
        if self.env != then_env:
            raise Blocked("the two branches of an `if` leave different local types")
        return ({"rule": "if", "cond": dc, "then": dt, "else": de,
                 "join": join(tt, te)}, join(tt, te))

    # aggregates
    def n_array(self, n):
        ds, ts = self.go_all(n[1])
        elem = NEVER
        for t in ts:
            elem = join(elem, t)
        return {"rule": "arrayLit", "elems": ds, "elem": elem}, array_of(elem)

    def n_hash(self, n):
        kds, kts, vds, vts = [], [], [], []
        for pair in n[1]:
            if pair[0] != "pair":
                raise Blocked(f"hash entry '{pair[0]}' is outside the fragment")
            kd, kt = self.go(pair[1])
            vd, vt = self.go(pair[2])
            kds.append(kd); kts.append(kt); vds.append(vd); vts.append(vt)
        k, v = NEVER, NEVER
        for t in kts:
            k = join(k, t)
        for t in vts:
            v = join(v, t)
        return ({"rule": "hashLit", "keys": kds, "vals": vds, "key": k, "val": v},
                hash_of(k, v))

    # sends
    def n_vcall(self, n):
        if n[1] == "x":
            return {"rule": "bareName", "name": "x"}, {"tag": "any"}
        return self.implicit_send(n[1], [])

    def n_send(self, n):
        recv, m, args, blk = n[1], n[2], n[3], n[4]
        if blk is not None:
            raise Blocked("a block argument is outside the fragment")
        if recv is None:
            return self.implicit_send(m, args)
        # `C.new(...)`
        if m == "new" and recv[0] == "const":
            return self.new_inst(recv[1], args)
        dr, tr = self.go(recv)
        tr = self.as_inst(tr)
        dargs, targs = self.go_all(args)
        ret = prim_ret(tr, m, targs)
        if ret is not None:
            return ({"rule": "prim", "recv": dr, "method": m, "args": dargs,
                     "recvTy": tr, "retTy": ret}, ret)
        if tr.get("tag") == "inst":
            sig = self.sig_for(tr["name"], m)
            return ({"rule": "callMethodSig", "recv": dr, "name": m, "args": dargs,
                     "ret": sig["ret"]}, sig["ret"])
        raise Blocked(f"no builtin signature for {tr.get('tag')}#{m}/{len(targs)}")

    def implicit_send(self, m: str, args) -> tuple[dict, dict]:
        dargs, _ = self.go_all(args)
        owner = self.self_cls or "Object"
        sig = self.sig_for(owner, m)
        return {"rule": "callSig", "name": m, "args": dargs, "ret": sig["ret"]}, sig["ret"]

    def new_inst(self, name: str, args) -> tuple[dict, dict]:
        dargs, targs = self.go_all(args)
        ivars = self.cls_ivars.get(name)
        if ivars is None:
            raise Blocked(f"`{name}.new` before `class {name}` is defined")
        ty = {"tag": "inst", "name": name, "ivars": spine(ivars)}
        return {"rule": "newInst", "cls": name, "args": dargs, "ty": ty}, ty

    # declarations
    def n_def(self, n):
        name, params, body = n[1], n[2], n[3]
        owner = self.self_cls or "Object"
        sig = self.sig_for(owner, name)
        if len(sig["params"]) != len(params):
            raise Blocked(f"{owner}#{name}: sig declares {len(sig['params'])} params, "
                          f"the def has {len(params)}")
        sps = []
        for p, s in zip(params, sig["params"]):
            if p[0] != "preq":
                raise Blocked(f"{owner}#{name}: parameter kind '{p[0]}' is outside the "
                              "fragment (required positionals only)")
            sps.append({"name": p[1], "ty": self.as_inst(s["ty"])})
        outer_env = self.env
        self.env = {p["name"]: p["ty"] for p in sps}
        dbody, _ = self.go(body)
        self.env = outer_env
        return ({"rule": "defDecl", "name": name, "params": sps, "ret": sig["ret"],
                 "body": dbody}, SYM)

    def n_class(self, n):
        name, sup, body = n[1], n[2], n[3]
        if sup is not None and sup[0] != "const":
            raise Blocked("a computed superclass is outside the fragment")
        supname = sup[1] if sup is not None else None
        if supname is not None:
            self.supers[name] = supname
        outer_cls, outer_ivars, outer_env = self.self_cls, self.ivars, self.env
        self.self_cls, self.env = name, {}
        # A subclass starts from its parent's ivars: `class Dog < Animal; end` has
        # `Animal`'s, and `Dog.new("Rex").speak` reads one.
        self.ivars = dict(self.cls_ivars.get(supname, [])) if supname else {}
        # `initialize` first, so that the ivar spine exists before any other method body
        # reads an ivar. One pass, in source order, is not enough for that.
        self.seed_ivars(name, body)
        dbody, _ = self.go(body)
        if not self.ivars and supname is not None and supname in self.cls_ivars:
            self.ivars = dict(self.cls_ivars[supname])
        self.cls_ivars[name] = list(self.ivars.items())
        self.self_cls, self.ivars, self.env = outer_cls, outer_ivars, outer_env
        return ({"rule": "classDecl", "name": name, "super": supname, "body": dbody},
                {"tag": "clsOf", "name": name})

    def seed_ivars(self, name: str, body) -> None:
        """The ivar spine of `name`, read off `initialize`'s declared parameters.

        Only the `@x = <param>` / `@x = <literal>` shapes, which is what the corpus's
        constructors are. Anything else leaves the ivar unset, and the first read of it
        blocks -- visible, rather than typed at a guess.
        """
        stmts = body[1:] if body[0] == "seq" else [body]
        for st in stmts:
            if st[0] != "def" or st[1] != "initialize":
                continue
            sig = self.sigs.get((name, "initialize"))
            if sig is None:
                return
            penv = {}
            for p, s in zip(st[2], sig["params"]):
                if p[0] == "preq":
                    penv[p[1]] = s["ty"]
            ibody = st[3]
            for s2 in (ibody[1:] if ibody[0] == "seq" else [ibody]):
                if s2[0] == "vasgn" and s2[1] == "ivar":
                    v = s2[3]
                    if v[0] == "var" and v[1] == "local" and v[2] in penv:
                        self.ivars[s2[2]] = penv[v[2]]
                    elif v[0] == "int":
                        self.ivars[s2[2]] = INT
                    elif v[0] == "str":
                        self.ivars[s2[2]] = STR


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--ast", required=True)
    ap.add_argument("--sigs", required=True)
    args = ap.parse_args(argv)

    with open(args.ast) as fh:
        ast = json.load(fh)
    with open(args.sigs) as fh:
        sigs = json.load(fh)

    em = Emitter(sigs)
    try:
        deriv, ty = em.go(ast["ast"])
    except Blocked as b:
        print(json.dumps({"status": "blocked", "why": str(b)}))
        return 0
    except RecursionError:
        print(json.dumps({"status": "blocked", "why": "AST too deep"}))
        return 0
    print(json.dumps({"status": "ok", "ty": ty, "deriv": deriv}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
