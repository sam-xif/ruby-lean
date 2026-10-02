#!/usr/bin/env bash
# Harvest MRI's bootstraptest corpus for the tier-0 differential run.
#
# bootstraptest ships in the ruby/ruby source tree, not an installed Ruby, so CI
# does a sparse, blobless clone once and caches the result. Mirrors the recipe in
# difftest/README.md and docs/reproducing.md.
#
#   scripts/ci/harvest_bootstraptest.sh
#
# Honors $RUBY_SRC (default /tmp/ruby-src). Idempotent: skips if the corpus is
# already harvested, reuses the checkout if it exists.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
RUBY_SRC="${RUBY_SRC:-/tmp/ruby-src}"
CORPUS="$ROOT/desugar/corpus/bootstraptest"

if [[ -d "$CORPUS" ]]; then
  echo "bootstraptest corpus already present at $CORPUS"
  exit 0
fi

if [[ ! -d "$RUBY_SRC/bootstraptest" ]]; then
  echo "cloning ruby/ruby (sparse, blobless) into $RUBY_SRC"
  git clone --depth 1 --filter=blob:none --sparse https://github.com/ruby/ruby "$RUBY_SRC"
  ( cd "$RUBY_SRC" && git sparse-checkout set bootstraptest )
fi

"$ROOT/desugar/bin/harvest_bootstraptest" "$RUBY_SRC/bootstraptest"
