#!/usr/bin/env bash
# Check the four external tools this repo needs, and say what is missing and how
# to get it. Exit 0 iff everything needed for `scripts/reproduce.sh` is present.
#
#   scripts/check-prereqs.sh
set -uo pipefail

ok=0
have() { command -v "$1" >/dev/null 2>&1; }
say()  { printf '  %-10s %s\n' "$1" "$2"; }
bad()  { ok=1; printf '  %-10s MISSING — %s\n' "$1" "$2"; }

echo "ruby-lean prerequisites"
echo

# 1. Lean, via elan. The toolchain itself is pinned per package in lean-toolchain
#    (v4.32.2); elan reads that file and fetches it, so only elan must be present.
if have lake && have elan; then
  say "lean" "$(lake --version 2>/dev/null | head -1)  (pinned: $(cat lean/lean-toolchain))"
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

# 3. Sorbet — stage 1 of the typed pipeline. `srb_sigs.py` finds the gem's
#    bundled binary by glob, so the gem is enough; `srb` need not be on PATH.
if python3 - <<'PY' 2>/dev/null
import glob, os, sys
pats = ["/opt/homebrew/lib/ruby/gems/*/gems/sorbet-static-*/libexec/sorbet",
        os.path.expanduser("~/.gem/ruby/*/gems/sorbet-static-*/libexec/sorbet"),
        "/usr/local/lib/ruby/gems/*/gems/sorbet-static-*/libexec/sorbet"]
sys.exit(0 if any(glob.glob(p) for p in pats) or __import__("shutil").which("srb") else 1)
PY
then
  say "sorbet" "found (override with \$SORBET)"
else
  bad "sorbet" "gem install sorbet sorbet-runtime   (supplies sorbet-static)"
fi

# 4. uv — runs the difftest engine (the agreement stage) in its own env.
if have uv; then
  say "uv" "$(uv --version)"
else
  bad "uv" "brew install uv   (or: curl -LsSf https://astral.sh/uv/install.sh | sh)"
fi

# 5. Python — the untrusted pipeline stages (strip/desugar/emit drivers).
if have python3; then
  say "python3" "$(python3 --version)  (3.12+ required by difftest)"
else
  bad "python3" "install Python 3.12 or newer"
fi

echo
if [[ $ok == 0 ]]; then
  echo "All prerequisites present. Next: scripts/reproduce.sh"
else
  echo "Install what is marked MISSING above, then re-run this script."
fi
exit $ok
