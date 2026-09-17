"""Random programs inside the P0 checker fragment, and the relation over them.

Part of the checker difftest (see `checker_relation.py`). Mining the
bootstraptest corpus gave 21 accepts and **zero** rejects, so the dangerous
verdict has no natural population and has to be generated.

## Why source, not `Expr`

The checker consumes RubyCore `Expr` but `srb` consumes Ruby. Generating `Expr`
would need an `Expr -> Ruby` printer *and* trust in it; generating source reuses
the existing desugar pipeline and guarantees both oracles read the same artifact.

## What the fragment can and cannot express

`builtinSig` carries `+ - *` only, so there is **no comparison operator**, so a
loop condition cannot be typed and a terminating typed loop is inexpressible.
`while` is therefore absent from the grammar below, and `if` conditions can only
be the literals `true`/`false` — which `srb` always flags 7006, an excluded
code. Adding `Integer#<` is the single change that would unlock both; it needs a
Bool-returning variant of `int_bin_dispatch`, since the current one is
`Int -> Int -> Int`. That is the top ratchet item and it is a checker change,
not a harness one.

## Three intents, three different expectations

- `wellformed` — should `accept`. Anything else is a checker regression.
- `injected-literal` — a bad operand under a *literal-rooted* receiver, so
  `defTy` knows both operand types. Should `reject`; the rate at which it does
  is the refutation pass's **recall**, the number that says whether `reject`
  earns its risk.
- `injected-local` — the same bad operand under a *local* receiver. Expected to
  be `unknown`, because `defTy` takes no environment. Generated deliberately:
  it keeps the known incompleteness measured rather than assumed, and it is the
  population that would move if `defTy` ever gains an environment.
"""

from __future__ import annotations

import random
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path

from .sorbet import StaticError, srb_path

OPS = ("+", "-", "*")
BAD_OPERANDS = ("nil", "true", "false")

INTENTS = ("wellformed", "injected-literal", "injected-local")


# ---------------------------------------------------------------------------
# Generation
# ---------------------------------------------------------------------------


def _lit_expr(rng: random.Random, depth: int) -> str:
    """An expression with no locals, so `defTy` gives it an unconditional type.
    That is what makes an injected error *refutable* rather than merely wrong."""
    if depth <= 0 or rng.random() < 0.35:
        return str(rng.randint(-50, 50))
    return f"({_lit_expr(rng, depth - 1)} {rng.choice(OPS)} {_lit_expr(rng, depth - 1)})"


def _expr(rng: random.Random, depth: int, names: list[str]) -> str:
    if depth <= 0 or rng.random() < 0.35:
        if names and rng.random() < 0.5:
            return rng.choice(names)
        return str(rng.randint(-50, 50))
    return f"({_expr(rng, depth - 1, names)} {rng.choice(OPS)} {_expr(rng, depth - 1, names)})"


def _statements(rng: random.Random, names: list[str], n: int) -> list[str]:
    out = []
    for i in range(n):
        if rng.random() < 0.6:
            name = f"v{i}"
            out.append(f"{name} = {_expr(rng, rng.randint(1, 3), names)}")
            names.append(name)
        else:
            out.append(_expr(rng, rng.randint(1, 3), names))
    return out


def generate(rng: random.Random, intent: str) -> str:
    """One program. Always ends in an expression so the whole program has a
    type — a trailing assignment would too, but ending on a bare expression
    exercises the `seq` tail rule that `evalExpr` special-cases."""
    names: list[str] = []
    body = _statements(rng, names, rng.randint(1, 4))

    if intent == "wellformed":
        body.append(_expr(rng, rng.randint(1, 3), names))
    elif intent == "injected-literal":
        bad = rng.choice(BAD_OPERANDS)
        body.append(f"{_lit_expr(rng, rng.randint(1, 2))} {rng.choice(OPS)} {bad}")
    elif intent == "injected-local":
        bad = rng.choice(BAD_OPERANDS)
        if not names:
            names.append("v0")
            body.append("v0 = 1")
        body.append(f"{rng.choice(names)} {rng.choice(OPS)} {bad}")
    else:  # pragma: no cover - guarded by the CLI
        raise ValueError(f"unknown intent {intent}")

    return "# typed: true\n" + "\n".join(body) + "\n"


@dataclass(frozen=True)
class Sample:
    name: str
    intent: str
    source: str


def sample(count: int, seed: int) -> list[Sample]:
    """Deterministic by seed, so a failing program can always be reproduced from
    the two numbers printed in the report."""
    rng = random.Random(seed)
    out = []
    for i in range(count):
        intent = INTENTS[i % len(INTENTS)]
        out.append(Sample(f"g{i:04d}", intent, generate(rng, intent)))
    return out


# ---------------------------------------------------------------------------
# Batched srb
# ---------------------------------------------------------------------------


def srb_batch(samples: list[Sample], srb: str | None = None,
              timeout: float = 300.0) -> dict[str, list[StaticError]]:
    """One `srb tc` over the whole sample, keyed by program name.

    Per-file checking (what `SorbetStatic` does, for hermeticity) costs a
    process launch each and dominates a fuzz run. Batching is safe *here* and
    only here: generated programs use nothing but top-level locals, which are
    file-scoped in Ruby, so no two files can interact. Introduce constants,
    methods or classes into the grammar and this must go back to per-file.
    """
    srb = srb or srb_path()
    if srb is None:
        raise RuntimeError("srb not found")
    errors: dict[str, list[StaticError]] = {s.name: [] for s in samples}
    with tempfile.TemporaryDirectory(prefix="difftest-fuzz-") as d:
        root = Path(d)
        (root / "sorbet").mkdir()
        (root / "sorbet" / "config").write_text("false\n")
        for s in samples:
            (root / f"{s.name}.rb").write_text(s.source)
        proc = subprocess.run(
            [srb, "tc", "--dir", ".", "--color=never"],
            capture_output=True, text=True, timeout=timeout, cwd=root,
        )
        raw = proc.stdout + proc.stderr
    for line in raw.splitlines():
        if not line.startswith("./"):
            continue
        head, _, rest = line.partition(":")
        name = Path(head).stem
        if name not in errors:
            continue
        lineno, _, msg = rest.partition(":")
        code = None
        if "https://srb.help/" in msg:
            tail = msg.rsplit("https://srb.help/", 1)[1].strip()
            if tail.isdigit():
                code = int(tail)
        errors[name].append(
            StaticError(int(lineno) if lineno.isdigit() else 0, code, msg.strip())
        )
    return errors


# ---------------------------------------------------------------------------
# The run
# ---------------------------------------------------------------------------


def run_fuzz(count: int, seed: int, out_dir: Path, timeout: float = 300.0) -> dict:
    """Generate, check, srb, and relate. Returns the summary dict; the caller
    exits nonzero on `violations`."""
    import json

    from .checker_relation import CHECK_CELLS, PINNED_ZERO_CELLS, relate
    from .control import CRubyRunner
    from .sorbet import StaticChecker
    from .sorbet_check import TYPE_ERROR_FAMILY, runtime_kind

    samples = sample(count, seed)
    control = CRubyRunner(timeout=timeout)
    checker = StaticChecker(runner=control)
    errors = srb_batch(samples, timeout=timeout)

    rows = []
    for s in samples:
        verdict = checker.check(s.source)
        obs = control.run(s.source)
        cell = relate(
            verdict.verdict if verdict else None,
            errors[s.name],
            obs.exception[0] if obs.exception else None,
            TYPE_ERROR_FAMILY,
        )
        rows.append({
            "name": s.name,
            "intent": s.intent,
            "verdict": verdict.verdict if verdict else None,
            "cell": cell,
            "srb_errors": [e.to_json() for e in errors[s.name]],
            "runtime": runtime_kind(obs.exception),
            "source": s.source,
        })

    out_dir.mkdir(parents=True, exist_ok=True)
    with (out_dir / "cases.jsonl").open("w") as fh:
        for r in rows:
            fh.write(json.dumps(r) + "\n")

    def by(intent, verdict):
        return sum(1 for r in rows if r["intent"] == intent and r["verdict"] == verdict)

    per_intent = {
        i: {
            "total": sum(1 for r in rows if r["intent"] == i),
            "accept": by(i, "accept"),
            "reject": by(i, "reject"),
            "unknown": by(i, "unknown"),
            "undecidable": by(i, None),
        }
        for i in INTENTS
    }
    inj = per_intent["injected-literal"]
    summary = {
        "count": count,
        "seed": seed,
        "cells": {c: sum(1 for r in rows if r["cell"] == c) for c in CHECK_CELLS},
        "per_intent": per_intent,
        # The number that says whether `reject` earns its risk.
        "reject_recall": (inj["reject"] / inj["total"]) if inj["total"] else None,
        "violations": [r["name"] for r in rows if r["cell"] in PINNED_ZERO_CELLS],
        # A wellformed program that is not accepted is a checker regression, not
        # a relation violation — tracked separately so it cannot hide in the
        # `unknown` count.
        "wellformed_not_accepted": [
            r["name"] for r in rows
            if r["intent"] == "wellformed" and r["verdict"] != "accept"
        ],
    }
    (out_dir / "summary.json").write_text(json.dumps(summary, indent=2))
    return summary
