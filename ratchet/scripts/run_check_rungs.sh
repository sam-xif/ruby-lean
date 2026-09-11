#!/usr/bin/env bash
# The evidence behind every climbed rung: for each hand-authored `Judge` derivation in
# `Ratchet/Rungs.lean`, check (a) that the rung's committed corpus JSON really
# decodes to the `Expr` the derivation is about, and (b) that running the *real*
# semantics (`../lean/RubyCore`'s `stepFn`, via `Semantics/Interp.lean`) on the
# same program produces a value whose class the derived `Ty` names, with no
# type-stuck outcome. Exit code is nonzero iff any of those fails.
#
# This is what makes "N rungs climbed" a claim about Ruby rather than a claim
# about a Bool. See `CheckRungs.lean`'s docstring.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

lake build checkrungs
exec .lake/build/bin/checkrungs corpus-untyped
