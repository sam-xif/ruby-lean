#!/usr/bin/env bash
# The evidence behind rungs 1-13: for each hand-authored `Judge` derivation in
# `Ratchet/Rungs13.lean`, check (a) that the rung's committed corpus JSON really
# decodes to the `Expr` the derivation is about, (b) that its certificate is
# empty, so no trusted claim is involved, and (c) that running the *real*
# semantics (`../lean/RubyCore`'s `stepFn`, via `Semantics/Interp.lean`) on the
# same program produces a value whose class the derived `Ty` names, with no
# type-stuck outcome. Exit code is nonzero iff any of those fails.
#
# This is what makes "13 rungs climbed" a claim about Ruby rather than a claim
# about a Bool. See `Check13.lean`'s docstring.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

lake build check13
exec .lake/build/bin/check13 corpus
