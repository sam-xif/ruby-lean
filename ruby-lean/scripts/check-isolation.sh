#!/usr/bin/env bash
# The layering check.
#
#   scripts/check-isolation.sh
#
# `Checker/`, the type checker, is isolated from `RubyCore/`, the model: its
# `Expr` and `Ty` are copied text, not imports, so the checker can be read,
# audited and re-implemented without the model in scope. The one place the two
# meet is the checker's soundness proof, which relates them by definition, and
# that lives in another package (`../books/`).
#
# The checker and the model share this Lake package, so the compiler does not
# refuse the import. This script does, and `../books/scripts/check-soundness.sh`
# runs it as its first stage.
#
# Exit 0 iff no module under `Checker/` imports anything under `RubyCore/`, no
# module under `RubyCore/` imports `Checker/`, and nothing in this package
# imports a proof from `../books/`.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 1

rc=0

# 1. The checker does not see the model.
BAD=$(grep -rnE '^import +RubyCore\b' Checker/ MainValidateOne.lean 2>/dev/null)
if [[ -n "$BAD" ]]; then
  echo "FAIL: Checker/ imports the model — the checker's isolation is gone:"
  echo "$BAD" | sed 's/^/  /'
  rc=1
fi

# 2. The model does not depend on the checker.
BAD=$(grep -rnE '^import +Checker\b' RubyCore/ RubyCore.lean Main.lean GenPrelude.lean 2>/dev/null)
if [[ -n "$BAD" ]]; then
  echo "FAIL: RubyCore/ imports the checker — the layering is inverted:"
  echo "$BAD" | sed 's/^/  /'
  rc=1
fi

# 3. Neither depends on a proof. The dependency runs one way:
#    ../books/ -> {Checker/, RubyCore/}.
BAD=$(grep -rnE '^import +Books\b' --include='*.lean' --exclude-dir=.lake . 2>/dev/null)
if [[ -n "$BAD" ]]; then
  echo "FAIL: this package imports a proof from ../books/:"
  echo "$BAD" | sed 's/^/  /'
  rc=1
fi

[[ $rc == 0 ]] && echo "OK: Checker/ does not see RubyCore/; the layering runs one way."
exit $rc
