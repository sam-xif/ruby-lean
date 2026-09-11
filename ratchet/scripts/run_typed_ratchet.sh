#!/usr/bin/env bash
# The **typed** ratchet: Sorbet in the loop, end to end.
#
#   corpus/NNN.rb  (annotated, the source of truth)
#     1. srb -p symbol-table   -> the signature manifest        ] untrusted
#     2. the strip stack       -> the plain program             ] untrusted
#     3. export-json           -> the AST                       ] untrusted
#     4. emit_deriv.py         -> a `Deriv`, or a named block   ] untrusted
#     5. lake exe ratchetd     -> `validateD`'s Bool            ] TRUSTED, and only this
#
# Four steps, in the order that matters:
#
#   0. **The negative controls** (`Ratchet/DerivControls.lean`, `#guard`ed at build
#      time): a checker that accepts everything would pass every rung below, so the
#      controls are checked before any count is reported.
#   1. **Stages 1-4** over every rung, into `build/`.
#   2. **Agreement** (`--sut lean`) over the *stripped* programs -- the ones the
#      certificates are about. A rung the model runs differently from CRuby is a rung
#      whose type is a statement about a fiction. Skip with RATCHET_SKIP_AGREEMENT=1.
#   3. **The report** (`lake exe ratchetd`), whose exit code is non-zero on a moved
#      Sorbet verdict or a new upstream failure -- both ratchets -- and zero on a
#      *block*, which is the emitter reporting its own fragment boundary.
#
# `validateD` is a SHAPE CHECK in this commit; see `Ratchet/Deriv.lean`.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
RATCHET_DIR="$PWD"

echo "=== the negative controls (#guard, at build time) ==="
lake build Ratchet.DerivControls ratchetd
echo

echo "=== stages 1-4: sorbet -> strip -> desugar -> emit ==="
python3 scripts/build_corpus.py "$@"
echo

if [[ "${RATCHET_SKIP_AGREEMENT:-0}" == "1" ]]; then
  echo "=== agreement (CRuby vs the Lean semantics): SKIPPED (RATCHET_SKIP_AGREEMENT=1)"
else
  echo "=== agreement over the sig-stripped programs (CRuby vs the Lean semantics) ==="
  ( cd ../difftest && uv run python -m difftest replay "$RATCHET_DIR/build" --sut lean )
fi
echo

echo "=== stage 5: the typed ladder ==="
exec .lake/build/bin/ratchetd build
