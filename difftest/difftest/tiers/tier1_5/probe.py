"""Eval-order probe transform for tier "1.5".

Structurally separate from the tier-1 generator: tier 1.5 reuses the *entire*
tier-1 grammar unchanged (see `..tier1.strategies.programs`) and layers a pure
AST->AST transform that wraps every leaf operand in a probe call
`__t(label, leaf)`. `__t` prints the label and returns the leaf, so the stdout
trace records the exact left-to-right evaluation order of subexpressions. Labels
are a per-program counter baked into the (identical) source both control and SUT
run, so a reordering or double-evaluation between them shows up as a trace
difference and can never be a false positive.

No shared mutable state and no flags: the counter is local to
`add_eval_order_probes`, and the transform is composed onto the shared generator
via `Strategy.map` in `strategies.py`.
"""

from __future__ import annotations

import dataclasses
import itertools
from typing import Iterator

from ..tier1 import ast as A

# Leaf value-position nodes: replacing `leaf` with `__t("n", leaf)` is always
# valid (same value, plus an observable print). Raw ints/strings elsewhere in the
# AST (loop counts, raise messages, param/var names) are not `Node`s, so the
# generic walk leaves them untouched.
_LEAVES = (
    A.IntLit,
    A.StrLit,
    A.SymLit,
    A.BoolLit,
    A.NilLit,
    A.LocalRead,
    A.IvarRead,
    A.BlockGiven,
    A.ConstRead,
)


def _probe_def() -> A.Node:
    """`def __t(l, v); puts(l); v; end` — prepended once per program. Built
    directly (never itself probe-wrapped)."""
    return A.MethodDef("__t", ("l", "v"), (A.Puts((A.LocalRead("l"),)), A.LocalRead("v")))


def _wrap(node: A.Node, counter: Iterator[int]) -> A.Node:
    """Probe-wrap a leaf; otherwise rebuild the node with its children walked."""
    if isinstance(node, _LEAVES):
        return A.Call("__t", (A.StrLit(str(next(counter))), node))
    fields = {f.name: _walk(getattr(node, f.name), counter) for f in dataclasses.fields(node)}
    return type(node)(**fields)


def _walk(x, counter: Iterator[int]):
    """Recurse into a field value: a Node, a (possibly nested) tuple of Nodes, or
    a raw scalar left as-is."""
    if isinstance(x, A.Node):
        return _wrap(x, counter)
    if isinstance(x, tuple):
        return tuple(_walk(e, counter) for e in x)
    return x


def add_eval_order_probes(program: A.Program) -> A.Program:
    """Tier-1 program -> tier-1.5 program: every leaf probe-wrapped, `__t`
    prepended. Pure and deterministic (fresh counter per program), so it composes
    cleanly under `Strategy.map` and preserves shrinking."""
    counter = itertools.count()
    probed = tuple(_wrap(stmt, counter) for stmt in program.stmts)
    return A.Program((_probe_def(),) + probed)
