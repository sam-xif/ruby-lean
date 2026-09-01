#!/usr/bin/env bash
# Build the isolated `ratchet` package and run it against the corpus,
# printing per-rung results plus the tier summary. Exit code is nonzero iff
# some rung's actual behavior (validate or execution) disagrees with what
# the corpus recorded as expected -- i.e. iff there is a bug in this harness
# itself, not merely an unimplemented tier (those are `[frontier]` and
# always expect `validate=false`, so they never fail this check by design).
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

lake build
exec .lake/build/bin/ratchet corpus
