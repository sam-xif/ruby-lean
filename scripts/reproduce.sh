#!/usr/bin/env bash
# Reproduce every headline number in README.md, from a clean checkout.
#
#   scripts/reproduce.sh              # build + the typed ratchet gate  (~20 min cold)
#   scripts/reproduce.sh --with-difftest   # also replay the tier-0 bootstraptest corpus
#   scripts/reproduce.sh --with-proofs     # also build the metatheory and check axioms
#
# Every step is a command you can run by hand; this script only puts them in
# order and stops at the first one that fails. Nothing here is trusted by the
# result — the only trusted artifact in the repo is `validateD`'s Bool, produced
# by step 3 (see README §What is trusted).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WITH_DIFFTEST=0
WITH_PROOFS=0
for a in "$@"; do
  case "$a" in
    --with-difftest) WITH_DIFFTEST=1 ;;
    --with-proofs)   WITH_PROOFS=1 ;;
    -h|--help) sed -n '2,12p' "$0"; exit 0 ;;
    *) echo "unknown flag: $a" >&2; exit 2 ;;
  esac
done

step() { echo; echo "── $* ──"; }

step "0. prerequisites"
"$ROOT/scripts/check-prereqs.sh"

step "1-2. build the Lean project (ruby-lean/ — the rubycore SUT, and validateD with its proofs)"
# One Lake package (`ruby-lean/`): the model (RubyCore/), the checker (Ratchet/), the
# bridge to the real semantics (Semantics/) and the denotation that joins them
# (Denote/) are four libraries in it, and `lake build` builds all of them.
( cd "$ROOT/ruby-lean" && lake build )

step "3. the typed ratchet gate (the headline numbers)"
# Sorbet -> strip -> desugar -> emit -> validateD, over every corpus rung, plus
# the negative controls, the CRuby/model agreement replay and the safety
# cross-check. Prints GREEN or RED on its last line.
( cd "$ROOT/ruby-lean" && ./scripts/run_typed_ratchet.sh )

if [[ $WITH_DIFFTEST == 1 ]]; then
  step "4. differential test: the Lean model vs CRuby over MRI's bootstraptest"
  # The corpus is *harvested*, not vendored: MRI's bootstraptest suite is not part
  # of an installed Ruby and is not ours to ship. One sparse clone gets it.
  CORPUS="$ROOT/harness/desugar-dt/corpus/bootstraptest"
  if [[ ! -d "$CORPUS" ]]; then
    RUBY_SRC="${RUBY_SRC:-/tmp/ruby-src}"
    echo "no bootstraptest corpus yet — harvesting it into ${CORPUS}"
    if [[ ! -d "$RUBY_SRC/bootstraptest" ]]; then
      echo "  cloning ruby/ruby (sparse, blobless) into ${RUBY_SRC}"
      git clone --depth 1 --filter=blob:none --sparse https://github.com/ruby/ruby "$RUBY_SRC"
      ( cd "$RUBY_SRC" && git sparse-checkout set bootstraptest )
    fi
    "$ROOT/harness/desugar-dt/bin/harvest_bootstraptest" "$RUBY_SRC/bootstraptest"
  fi
  ( cd "$ROOT/difftest" && uv sync --quiet && uv run python -m difftest run --tier 0 --sut lean )
fi

if [[ $WITH_PROOFS == 1 ]]; then
  step "5. the metatheory, and its axiom cleanliness"
  # Off the default build target because it is slow and the SUT does not depend
  # on it — which is exactly why it needs its own command, and why it rots.
  #
  # KNOWN RED at 0.01: RubyCore/Proof/Static/Preservation.lean has three broken
  # proofs, so this step exits non-zero. It is reported, not hidden — but it is
  # also not a failure of anything above it: the ratchet's own proofs and
  # `validateD_safe_boot` are on the default target and built in step 2.
  ( cd "$ROOT/ruby-lean" && ./scripts/check-proofs.sh ) || {
    echo
    echo "step 5 FAILED — expected at 0.01, see README §Status and limits."
    echo "Steps 1-4 above are the reproduction; this one is a known-red target."
    exit 1
  }
fi

echo
echo "Done. The verdict that matters is the GREEN/RED line printed by step 3."
