"""Random programs inside the P0 checker fragment, and the Sorbet relation over
them.

Mining the bootstraptest corpus gave 21 accepts and **zero** rejects, so the
dangerous verdict has no natural population and has to be generated. With the
pre-ratchet `check` query removed, the surviving oracle here is `srb`: each
generated program declares an *intent* (well typed, or ill typed with the error
injected under a literal- or local-rooted receiver), and the relation is intent
against `srb`'s answer.

## Why source, not `Expr`

The checker consumes RubyCore `Expr` but `srb` consumes Ruby. Generating `Expr`
would need an `Expr -> Ruby` printer *and* trust in it; generating source reuses
the existing desugar pipeline and guarantees both oracles read the same artifact.

## What the fragment can and cannot express

`builtinSig` carries `+ - *` only, so there is **no comparison operator**, so a
loop condition cannot be typed and a terminating typed loop is inexpressible.
`while` is therefore absent from the grammar below, and `if` conditions can only
be the literals `true`/`false` — which `srb` always flags 7006, an excluded
code.

## Three intents, three different expectations

- `wellformed` — `srb` should report no error. An error here is a generator bug.
- `injected-literal` — a bad operand under a *literal-rooted* receiver, so the
  operand types are locally knowable. `srb` should catch it; the rate at which it
  does is its **recall** on this population.
- `injected-local` — the same bad operand under a *local* receiver. Generated
  deliberately: it keeps a population srb may miss measured rather than assumed.
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

# What each intent should see from `srb`, checked against what it actually sees.
# The intents make different claims, so the interesting outcome differs per
# intent: a `wellformed` program srb rejects is a generator bug, while an
# `injected-*` program srb accepts is an unsoundness candidate.
FUZZ_CELLS: dict[str, str] = {
    "fuzz-typed-srb-rejected": (
        "intended well-typed; srb reported an error — a generator bug or a "
        "finding about Sorbet"
    ),
    "fuzz-injected-srb-caught": (
        "intended ill-typed; srb reported an error, as it should"
    ),
    "fuzz-injected-srb-missed": (
        "intended ill-typed; srb reported no error — an unsoundness candidate, "
        "or a mutation that was not really a type error"
    ),
    "fuzz-typed-srb-clean": "intended well-typed; srb reported no error",
}

# Only well-typed-but-rejected fails the run: it means the generator is emitting
# programs it wrongly believes are well typed, which invalidates the rest.
FUZZ_PINNED_ZERO_CELLS = ("fuzz-typed-srb-rejected",)


def run_fuzz(count: int, seed: int, out_dir: Path, timeout: float = 300.0) -> dict:
    """Generate, srb, and relate. Returns the summary dict; the caller exits
    nonzero on `violations`."""
    import json

    from .control import CRubyRunner
    from .sorbet_check import runtime_kind

    samples = sample(count, seed)
    control = CRubyRunner(timeout=timeout)
    errors = srb_batch(samples, timeout=timeout)

    rows = []
    for s in samples:
        errs = errors[s.name]
        if s.intent == "wellformed":
            cell = "fuzz-typed-srb-rejected" if errs else "fuzz-typed-srb-clean"
        else:
            cell = "fuzz-injected-srb-caught" if errs else "fuzz-injected-srb-missed"
        obs = control.run(s.source)
        rows.append({
            "name": s.name,
            "intent": s.intent,
            "cell": cell,
            "srb_errors": [e.to_json() for e in errs],
            "runtime": runtime_kind(obs.exception),
            "source": s.source,
        })

    out_dir.mkdir(parents=True, exist_ok=True)
    with (out_dir / "cases.jsonl").open("w") as fh:
        for r in rows:
            fh.write(json.dumps(r) + "\n")

    def by(intent, cell):
        return sum(1 for r in rows if r["intent"] == intent and r["cell"] == cell)

    inj = sum(1 for r in rows if r["intent"] == "injected-literal")
    summary = {
        "count": count,
        "seed": seed,
        "cells": {c: sum(1 for r in rows if r["cell"] == c) for c in FUZZ_CELLS},
        # The number that says whether `srb` catches injected errors on the
        # populations the generator can express.
        "srb_recall_injected_literal": (
            by("injected-literal", "fuzz-injected-srb-caught") / inj if inj else None
        ),
        "violations": [r["name"] for r in rows if r["cell"] in FUZZ_PINNED_ZERO_CELLS],
    }
    (out_dir / "summary.json").write_text(json.dumps(summary, indent=2))
    return summary
