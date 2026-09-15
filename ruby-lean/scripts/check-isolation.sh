#!/usr/bin/env bash
# The layering check, and the reason it exists as a script at all.
#
# `Ratchet/` — the certificate checker — is deliberately isolated from `RubyCore/`:
# its `Expr` and `Ty` are *copied text*, not imports, so the checker can be read,
# audited and re-implemented without the 24k-line model in scope. `Semantics/` is
# the one deliberate exception (it imports the real `stepFn`), and `Denote/` is the
# one library allowed to see both, because a denotation is by definition a
# statement relating the two.
#
# That used to be enforced structurally: the checker was its own Lake package (`ratchet/`)
# and `RubyCore` was not in its import path at all. Merging the two packages into
# `ruby-lean/` bought one build, one toolchain and one manifest, and cost exactly
# this: the compiler no longer refuses the import. So the refusal moved here, and
# `scripts/run_typed_ratchet.sh` runs it as its first stage.
#
#   scripts/check-isolation.sh
#
# Exit 0 iff no module under `Ratchet/` imports anything under `RubyCore/` or
# `Semantics/`, and no module under `Ratchet/` or `RubyCore/` imports `Denote/`.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 1

rc=0

# 1. The checker sees neither the model nor the bridge to it.
BAD=$(grep -rnE '^import +(RubyCore|Semantics|Denote)\b' Ratchet/ Ratchet.lean 2>/dev/null)
if [[ -n "$BAD" ]]; then
  echo "FAIL: Ratchet/ imports the model — the checker's isolation is gone:"
  echo "$BAD" | sed 's/^/  /'
  rc=1
fi

# 2. The model does not depend on the checker or its denotation. (The dependency
#    runs one way: Denote/ -> {Ratchet/, Semantics/} -> RubyCore/.)
BAD=$(grep -rnE '^import +(Ratchet|Denote|Semantics)\b' RubyCore/ RubyCore.lean Main.lean ConcolicMain.lean 2>/dev/null)
if [[ -n "$BAD" ]]; then
  echo "FAIL: RubyCore/ imports the checker layer — the layering is inverted:"
  echo "$BAD" | sed 's/^/  /'
  rc=1
fi

# 3. The bridge is the *only* place the model is imported on the checker side, and
#    it is meant to stay small: one file, named in the lakefile for that reason.
BAD=$(grep -rlE '^import +RubyCore' Semantics/ 2>/dev/null | grep -v '^Semantics/Interp.lean$')
if [[ -n "$BAD" ]]; then
  echo "NOTE: a second file under Semantics/ imports RubyCore (the bridge was one file):"
  echo "$BAD" | sed 's/^/  /'
  echo "  Not a failure — but update AGENTS.md and this script if the boundary really moved."
fi

[[ $rc == 0 ]] && echo "OK: Ratchet/ does not see RubyCore/; the layering runs one way."
exit $rc
