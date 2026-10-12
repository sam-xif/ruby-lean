#!/usr/bin/env bash
# Check the external tools this repository needs, and say what is missing and
# how to get it. Exit 0 iff everything `make check` needs is present.
#
#   scripts/check-prereqs.sh
set -uo pipefail

ok=0
have() { command -v "$1" >/dev/null 2>&1; }
say()  { printf '  %-10s %s\n' "$1" "$2"; }
bad()  { ok=1; printf '  %-10s MISSING — %s\n' "$1" "$2"; }

echo "ruby-lean prerequisites"
echo

# 1. Lean, via elan. The toolchain is pinned in ruby-lean/lean-toolchain
#    (v4.32.2); elan reads that file and fetches it, so only elan must be present.
if have lake && have elan; then
  say "lean" "$(lake --version 2>/dev/null | head -1)  (pinned: $(cat ruby-lean/lean-toolchain))"
else
  bad "lean" "install elan: curl https://elan.lean-lang.org/elan-init.sh -sSf | sh"
fi

# 2. CRuby — the differential-testing oracle, and the interpreter the desugar
#    harness itself runs under. The model is validated against 4.0.x.
RUBY_BIN="${RUBY:-$(command -v ruby || true)}"
if [[ -n "$RUBY_BIN" ]]; then
  say "ruby" "$("$RUBY_BIN" --version)"
else
  bad "ruby" "brew install ruby   (then put it on PATH, or set \$RUBY)"
fi

# 3. Sorbet — reads the signatures of a typed program. The pipeline uses the
#    binary inside the `sorbet-static` gem, so the gem is enough; `srb` need not
#    be on PATH. `$SORBET` overrides it. The lookup lives in exactly one place —
#    `books/scripts/srb_sigs.py:find_sorbet()` — and this script asks it rather
#    than re-implementing it, so the two cannot drift (issue #41).
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SORBET_BIN="$(python3 "$HERE/books/scripts/srb_sigs.py" --print-sorbet 2>/dev/null || true)"
if [[ -n "$SORBET_BIN" && -x "$SORBET_BIN" ]] || have srb; then
  say "sorbet" "${SORBET_BIN:-$(command -v srb)}"
else
  bad "sorbet" "make deps   (installs the gems pinned in Gemfile.lock)"
fi

# 4. uv — runs the differential tests in their own environment.
if have uv; then
  say "uv" "$(uv --version)"
else
  bad "uv" "brew install uv   (or: curl -LsSf https://astral.sh/uv/install.sh | sh)"
fi

# 5. Python — drives the corpus pipeline.
if have python3; then
  say "python3" "$(python3 --version)  (3.12+ required by difftest)"
else
  bad "python3" "install Python 3.12 or newer"
fi

echo
if [[ $ok == 0 ]]; then
  echo "All prerequisites present. Next: make check"
else
  echo "Install what is marked MISSING above, then re-run this script."
fi
exit $ok
