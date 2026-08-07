"""Type-directed generation of Sorbet-annotated Ruby.

`docs/semantics/static-soundness-poc.md` §7. `fragment_fuzz.py` generates plain
Ruby inside the P0 checker fragment; this generates *annotated* programs, and it
does so **type-first**: a term is built downward from the type it must have, so
well-typedness is a property of the construction rather than something checked
afterwards. That is the standard technique for fuzzing type-directed tools
(Palka et al., testing GHC with random well-typed lambda terms; QuickChick's
generators-for-inductive-relations) and it is strictly easier than checking —
there is no inference, no join, no fixpoint, no subsumption decision anywhere
below.

## Independence from the artifact under test

**Nothing here may import `builtinSig`, and nothing here may consult
`rubycore --check`.** If "well-typed" were defined by the checker we are
testing, agreement would be guaranteed by construction and the harness would
measure nothing. `BUILTINS` below is written from *Sorbet's* RBIs, deliberately
as a second, independent table — and the two tables disagreeing is a finding we
want, not a defect to paper over. (They already do: Sorbet's `Integer#+` accepts
`T.any(Integer, Float, Rational, BigDecimal, Complex)`, ours accepts `Integer`.
Ours being narrower is incompleteness, which is allowed.)

## Where approximation is and is not acceptable

The well-typed population is **exact** — by construction, not by filtering. The
ill-typed population is only ever *intended* ill-typed; `srb` adjudicates. A
mislabelled case therefore surfaces as a generator-vs-`srb` disagreement, which
is diagnosable and cannot corrupt the check-vs-`srb` zeros.

## Two knobs, and why they are coupled

`sigil` and `coverage` (the fraction of methods carrying a sig) cannot vary
independently: at `# typed: strict` every unsig'd method draws 7017, so partial
coverage requires `# typed: true` [V, srb 0.6.13405]. Partial coverage is the
interesting setting — it is the partially-typed population
`typed-portion-safety.md` §7's M0 wanted to measure and had no corpus for.

Note also that calls to an unsig'd method are `T.untyped` to Sorbet, so they
cannot produce a type error. That is the gradual boundary doing exactly what it
is designed to do, and it means coverage below 1 mechanically dilutes the
error-injection population.
"""

from __future__ import annotations

import random
from dataclasses import dataclass, field

# ---------------------------------------------------------------------------
# A small piece of Sorbet's type language
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Ty:
    head: str
    args: tuple["Ty", ...] = ()

    def render(self) -> str:
        if not self.args:
            return self.head
        inner = ", ".join(a.render() for a in self.args)
        return f"{self.head}({inner})"


INT = Ty("Integer")
STR = Ty("String")
BOOL = Ty("T::Boolean")
NILC = Ty("NilClass")
OBJ = Ty("Object")

ATOMS = (INT, STR, BOOL)


def nilable(t: Ty) -> Ty:
    return Ty("T.nilable", (t,))


def anyof(*ts: Ty) -> Ty:
    return Ty("T.any", ts)


# Supertypes we can safely widen a declared type to. Verified against srb:
# `sig { returns(Object) }` over an `Integer` body is clean, so return-position
# widening is legal and is exactly where a checker is liable to over-reject.
def supertypes(t: Ty) -> list[Ty]:
    out = [OBJ, nilable(t)]
    for other in ATOMS:
        if other != t:
            out.append(anyof(t, other))
    return out


# A type NOT compatible with `t`, or None when none exists. `Object` has no
# incompatible type, so it can never carry an injected error — the generator must
# skip those sites rather than emit a program it wrongly believes is broken.
def incompatible(t: Ty) -> Ty | None:
    if t.head == "Object":
        return None
    if t.head == "T.nilable":
        return incompatible(t.args[0])
    if t.head == "T.any":
        for cand in ATOMS + (NILC,):
            if all(cand != a for a in t.args):
                return cand
        return None
    return STR if t == INT else INT


# ---------------------------------------------------------------------------
# Builtins, transcribed from Sorbet's RBIs (NOT from our builtinSig)
# ---------------------------------------------------------------------------

# recv -> [(name, [param types], return type)]
BUILTINS: dict[str, list[tuple[str, list[Ty], Ty]]] = {
    "Integer": [
        ("+", [INT], INT),
        ("-", [INT], INT),
        ("*", [INT], INT),
        ("<", [INT], BOOL),
        ("<=", [INT], BOOL),
        (">", [INT], BOOL),
        (">=", [INT], BOOL),
    ],
    "String": [
        ("+", [STR], STR),
        ("length", [], INT),
    ],
}


def _ops_returning(ty: Ty) -> list[tuple[str, str, list[Ty]]]:
    """(receiver type name, method, param types) whose return is `ty`."""
    out = []
    for recv, entries in BUILTINS.items():
        for name, params, ret in entries:
            if ret == ty:
                out.append((recv, name, params))
    return out


# ---------------------------------------------------------------------------
# Synthesis
# ---------------------------------------------------------------------------


@dataclass
class Method:
    name: str
    params: list[tuple[str, Ty]]
    declared: Ty  # what the sig says (may be a supertype of `actual`)
    actual: Ty  # what the body really produces
    sigged: bool
    body: str = ""


@dataclass
class Program:
    sigil: str
    methods: list[Method] = field(default_factory=list)
    main: list[str] = field(default_factory=list)
    intent: str = "wellformed"
    mutation: str | None = None

    def render(self) -> str:
        out = [f"# typed: {self.sigil}", 'require "sorbet-runtime"', "extend T::Sig", ""]
        for m in self.methods:
            if m.sigged:
                if m.params:
                    ps = ", ".join(f"{n}: {t.render()}" for n, t in m.params)
                    out.append(f"sig {{ params({ps}).returns({m.declared.render()}) }}")
                else:
                    out.append(f"sig {{ returns({m.declared.render()}) }}")
            names = ", ".join(n for n, _ in m.params)
            head = f"def {m.name}({names})" if m.params else f"def {m.name}"
            out += [head, f"  {m.body}", "end", ""]
        out += self.main
        return "\n".join(out) + "\n"


class Gen:
    def __init__(self, rng: random.Random):
        self.rng = rng

    def var_of(self, ty: Ty, env: dict[str, Ty]) -> str | None:
        cands = [n for n, t in env.items() if t == ty]
        return self.rng.choice(cands) if cands else None

    def literal(self, ty: Ty, env: dict[str, Ty]) -> str:
        if ty == INT:
            return str(self.rng.randint(-40, 40))
        if ty == STR:
            return '"' + self.rng.choice(("a", "bc", "xyz", "")) + '"'
        if ty == BOOL:
            return self.rng.choice(("true", "false"))
        if ty == NILC:
            return "nil"
        if ty.head == "T.nilable":
            return "nil" if self.rng.random() < 0.4 else self.expr(ty.args[0], env, 0)
        if ty.head == "T.any":
            return self.expr(self.rng.choice(ty.args), env, 0)
        if ty.head == "Object":
            return self.expr(self.rng.choice(ATOMS), env, 0)
        raise ValueError(f"no literal for {ty}")  # pragma: no cover

    def expr(self, ty: Ty, env: dict[str, Ty], depth: int) -> str:
        """A Ruby expression of type `ty`. Every branch preserves the type, so
        the result is well-typed by construction."""
        # A variable of exactly this type is always safe.
        if self.rng.random() < 0.3:
            v = self.var_of(ty, env)
            if v:
                return v
        if depth <= 0 or self.rng.random() < 0.4:
            return self.literal(ty, env)

        # Widening: any expression of a subtype inhabits Object / nilable / any.
        if ty.head in ("Object", "T.nilable", "T.any"):
            return self.literal(ty, env)

        ops = _ops_returning(ty)
        if not ops:
            return self.literal(ty, env)
        recv_name, meth, params = self.rng.choice(ops)
        recv = self.expr(Ty(recv_name), env, depth - 1)
        if not params:
            return f"({recv}.{meth})"
        args = ", ".join(self.expr(p, env, depth - 1) for p in params)
        sym = meth if meth.isalpha() else f" {meth} "
        if meth.isalpha():
            return f"({recv}.{meth}({args}))"
        return f"({recv}{sym}{args})"


# ---------------------------------------------------------------------------
# Programs
# ---------------------------------------------------------------------------

MUTATIONS = ("arg-type", "return-type", "builtin-arg")


def build(rng: random.Random, *, sigil: str = "true", coverage: float = 1.0,
          loose: float = 0.25, intent: str = "wellformed",
          n_methods: int = 2, prefix: str = "") -> Program:
    """One program. `intent="illtyped"` applies exactly one mutation, so a
    program that `srb` accepts anyway is a candidate finding rather than a pile
    of confounded breakages."""
    g = Gen(rng)
    prog = Program(sigil=sigil, intent=intent)

    for i in range(n_methods):
        n_params = rng.randint(0, 2)
        params = [(f"p{j}", rng.choice(ATOMS)) for j in range(n_params)]
        actual = rng.choice(ATOMS)
        declared = actual
        if rng.random() < loose:
            declared = rng.choice(supertypes(actual))
        # coverage < 1 requires `# typed: true`; at `strict` an unsig'd method
        # draws 7017 and the program is rejected for a reason unrelated to types.
        sigged = True if sigil == "strict" else (rng.random() < coverage)
        # `prefix` uniquifies method names across a batch. Toplevel `def`s land
        # on Object, so a batched `srb --dir` run would otherwise have every
        # program redefining `m0` — the hazard `fragment_fuzz.srb_batch`'s
        # docstring warns about. Uniquifying keeps batching (fast) and cannot
        # affect typing.
        m = Method(f"{prefix}m{i}", params, declared, actual, sigged)
        m.body = g.expr(actual, dict(params), rng.randint(1, 2))
        prog.methods.append(m)

    # Call every method, so a sig'd signature is actually exercised.
    for m in prog.methods:
        args = ", ".join(g.expr(t, {}, 1) for _, t in m.params)
        prog.main.append(f"{m.name}({args})" if m.params else m.name)

    if intent == "illtyped":
        _mutate(rng, g, prog)
    return prog


def _mutate(rng: random.Random, g: Gen, prog: Program) -> None:
    """Break exactly one thing, and record what. Only *sig'd* methods are
    breakable: a call to an unsig'd method is `T.untyped` to Sorbet and cannot
    produce an error, which is the gradual boundary working as designed."""
    for kind in rng.sample(MUTATIONS, len(MUTATIONS)):
        if kind == "arg-type":
            cands = [
                (i, m, j, t)
                for i, m in enumerate(prog.methods) if m.sigged
                for j, (_, t) in enumerate(m.params)
                if incompatible(t) is not None
            ]
            if not cands:
                continue
            i, m, j, t = rng.choice(cands)
            bad = g.expr(incompatible(t), {}, 0)
            args = [g.expr(pt, {}, 1) for _, pt in m.params]
            args[j] = bad
            prog.main[i] = f"{m.name}({', '.join(args)})"
            prog.mutation = kind
            return
        if kind == "return-type":
            cands = [m for m in prog.methods
                     if m.sigged and incompatible(m.declared) is not None]
            if not cands:
                continue
            m = rng.choice(cands)
            m.body = g.expr(incompatible(m.declared), {}, 0)
            prog.mutation = kind
            return
        if kind == "builtin-arg":
            # `<int expr> + nil` — no sig needed, so this always applies.
            prog.main.append(f"({g.expr(INT, {}, 1)} + nil)")
            prog.mutation = kind
            return
    # Unreachable in practice: builtin-arg always applies.
    prog.mutation = "none"  # pragma: no cover


@dataclass(frozen=True)
class Sample:
    name: str
    intent: str
    mutation: str | None
    sigil: str
    coverage: float
    source: str


def sample(count: int, seed: int, *, sigil: str = "true", coverage: float = 1.0,
           loose: float = 0.25) -> list[Sample]:
    """Half well-typed, half intended ill-typed. Deterministic by seed, so any
    program in a report can be reproduced from the numbers printed with it."""
    rng = random.Random(seed)
    out = []
    for i in range(count):
        intent = "wellformed" if i % 2 == 0 else "illtyped"
        name = f"s{i:04d}"
        p = build(rng, sigil=sigil, coverage=coverage, loose=loose, intent=intent,
                  prefix=f"{name}_")
        out.append(Sample(name, intent, p.mutation, sigil, coverage, p.render()))
    return out


# ---------------------------------------------------------------------------
# The run
# ---------------------------------------------------------------------------

# The generator's own relation, distinct from `checker_relation.py`'s. This one
# compares *intent* against `srb`; that one compares `check` against `srb`.
GEN_CELLS: dict[str, str] = {
    "gen-unsoundness-witness": (
        "intended ill-typed; srb clean AND CRuby raised a type-family error — "
        "a confirmed hole in Sorbet"
    ),
    "gen-typed-rejected": (
        "intended well-typed; srb reported an error. A generator bug, or a "
        "finding about Sorbet — either way the population is suspect until it "
        "is explained"
    ),
    "gen-illtyped-accepted": (
        "intended ill-typed; srb clean but CRuby did not raise either — an "
        "unsoundness *candidate*, or a mutation that was not really a type error"
    ),
    "gen-typed-agrees": "intended well-typed; srb clean",
    "gen-illtyped-caught": "intended ill-typed; srb caught it",
}

# Only the well-typed-but-rejected cell fails the run: it means the generator is
# emitting programs it wrongly believes are well typed, which invalidates every
# other number in the report. The unsoundness cells are *findings* — the same
# stance `sorbet_check.py` takes on `unsoundness-witness`.
GEN_PINNED_ZERO_CELLS = ("gen-typed-rejected",)


def run_siggen(count: int, seed: int, out_dir, *, sigil: str = "true",
               coverage: float = 1.0, loose: float = 0.25,
               timeout: float = 300.0) -> dict:
    import json

    from .checker_relation import CHECK_CELLS, PINNED_ZERO_CELLS, relate
    from .control import CRubyRunner
    from .fragment_fuzz import srb_batch
    from .sorbet import StaticChecker
    from .sorbet_check import TYPE_ERROR_FAMILY, runtime_kind

    samples = sample(count, seed, sigil=sigil, coverage=coverage, loose=loose)
    errors = srb_batch(samples, timeout=timeout)
    control = CRubyRunner(timeout=timeout)
    checker = StaticChecker(runner=control)

    rows = []
    for s in samples:
        errs = errors[s.name]
        verdict = checker.check(s.source)
        # CRuby is run only where it can change a verdict: an intended-ill-typed
        # program srb accepted (does it really fail?), or one our checker
        # accepted (the model-bug zero). Everywhere else it would cost a process
        # per program to confirm what srb already settled.
        exc_class = None
        rt = None
        if (s.intent == "illtyped" and not errs) or (
            verdict is not None and verdict.verdict == "accept"
        ):
            obs = control.run(s.source)
            rt = runtime_kind(obs.exception)
            exc_class = obs.exception[0] if obs.exception else None

        if s.intent == "wellformed":
            cell = "gen-typed-agrees" if not errs else "gen-typed-rejected"
        elif errs:
            cell = "gen-illtyped-caught"
        elif exc_class in TYPE_ERROR_FAMILY:
            cell = "gen-unsoundness-witness"
        else:
            cell = "gen-illtyped-accepted"

        rows.append({
            "name": s.name, "intent": s.intent, "mutation": s.mutation,
            "cell": cell, "runtime": rt,
            "srb_errors": [e.to_json() for e in errs],
            "check_verdict": verdict.verdict if verdict else None,
            # The annotated population guards the three pinned zeros too. It is
            # not redundant with the `fuzz` arm: these programs reach `check`
            # through a *method-shaped* AST whose toplevel body still lands in
            # the fragment, which is a shape the fragment generator cannot emit.
            "check_cell": relate(
                verdict.verdict if verdict else None, errs, exc_class,
                TYPE_ERROR_FAMILY,
            ),
            "source": s.source,
        })

    out_dir.mkdir(parents=True, exist_ok=True)
    with (out_dir / "cases.jsonl").open("w") as fh:
        for r in rows:
            fh.write(json.dumps(r) + "\n")

    caught = sum(1 for r in rows if r["cell"] == "gen-illtyped-caught")
    injected = sum(1 for r in rows if r["intent"] == "illtyped")
    summary = {
        "count": count, "seed": seed, "sigil": sigil,
        "coverage": coverage, "loose": loose,
        "cells": {c: sum(1 for r in rows if r["cell"] == c) for c in GEN_CELLS},
        # Per mutation kind, so a kind srb never catches stands out instead of
        # being averaged away.
        "by_mutation": {
            k: {
                "total": sum(1 for r in rows if r["mutation"] == k),
                "caught": sum(1 for r in rows
                              if r["mutation"] == k and r["cell"] == "gen-illtyped-caught"),
            }
            for k in MUTATIONS
        },
        "srb_catch_rate": (caught / injected) if injected else None,
        # What our checker made of the same programs. Expected to be all
        # `unknown` until P1 lands methods — recorded so the day it stops being
        # all `unknown` is visible.
        "check_verdicts": {
            v: sum(1 for r in rows if r["check_verdict"] == v)
            for v in ("accept", "reject", "unknown", None)
        },
        "check_cells": {
            c: sum(1 for r in rows if r["check_cell"] == c) for c in CHECK_CELLS
        },
        "violations": [
            r["name"] for r in rows
            if r["cell"] in GEN_PINNED_ZERO_CELLS or r["check_cell"] in PINNED_ZERO_CELLS
        ],
        "findings": [r["name"] for r in rows
                     if r["cell"] in ("gen-unsoundness-witness", "gen-illtyped-accepted")],
    }
    (out_dir / "summary.json").write_text(json.dumps(summary, indent=2))
    return summary
