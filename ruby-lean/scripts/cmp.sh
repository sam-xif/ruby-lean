#!/bin/bash
# Compare the Lean model against the CRuby oracle on a snippet (dev loop; the
# authoritative check is `difftest run --tier 0 --sut lean`).
#
#   scripts/cmp.sh 'p [1,2,3].select { |x| x > 1 }'
#   scripts/cmp.sh -f file.rb
RUBY="$(brew --prefix ruby)/bin/ruby"
HERE="$(cd "$(dirname "$0")/.." && pwd)"
if [ "$1" = "-f" ]; then SRC="$2"; else SRC=/tmp/cmp_$$.rb; printf '%s\n' "$1" > "$SRC"; fi
CR=$("$RUBY" "$SRC" 2>&1)
LN=$("$RUBY" "$HERE/../desugar-dt/bin/export-json" "$SRC" 2>&1 | "$HERE/.lake/build/bin/rubycore" 2>&1)
if [ "${LN:0:1}" != "{" ]; then
  echo "GATE   $LN"
else
  # extract stdout + result_repr for a rough eyeball comparison
  LOUT=$(printf '%s' "$LN" | python3 -c 'import json,sys; d=json.load(sys.stdin); print((d["stdout"] or "")+("!"+str(d["exception"]) if d["exception"] else ""))')
  if [ "$CR" = "$(printf '%s' "$LOUT" | sed -e "s/[[:space:]]*$//")" ] || [ "$CR
" = "$LOUT" ]; then
    echo "AGREE  $(printf '%s' "$LOUT" | tr '\n' '|')"
  else
    echo "DIFF   cruby=[$(printf '%s' "$CR" | tr '\n' '|')]  lean=[$(printf '%s' "$LOUT" | tr '\n' '|')]"
  fi
fi
