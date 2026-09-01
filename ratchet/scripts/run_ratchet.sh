#!/usr/bin/env bash
# Build the isolated `ratchet` package and run it against the corpus,
# printing per-rung results plus the tier summary (each tier split into
# "structural" vs "claim-assisted" -- see Main.lean's docstring for why those
# are two numbers). Exit code is nonzero while any rung's actual verdict
# differs from the corpus's recorded target, which today is most rungs above
# tier 2 -- the climb, not a bug.
#
# `scripts/run_check13.sh` is the companion: the evidence behind the rungs the
# hand-authored judgment (`Ratchet/Judge.lean`) actually covers.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

lake build
exec .lake/build/bin/ratchet corpus
