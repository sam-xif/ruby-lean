#!/usr/bin/env bash
# CI is `make check` split into jobs. This fails if a target that `make check`
# runs is not run by .github/workflows/ci.yml, so the two cannot drift apart.
#
#   scripts/check-ci-matches-make.sh
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

targets=$(make -pn check 2>/dev/null | sed -n 's/^CHECKS := //p' | head -1)
[[ -n "$targets" ]] || { echo "FAIL: could not read CHECKS from the Makefile" >&2; exit 1; }

missing=0
for t in $targets; do
  if ! grep -qE "run: make ([a-z-]+ )*$t( |\$)" .github/workflows/ci.yml; then
    echo "FAIL: \`make check\` runs \`$t\`, but no CI step runs \`make $t\`"
    missing=1
  fi
done
[[ $missing == 0 ]] && echo "OK: CI runs every target of \`make check\`"
exit $missing
