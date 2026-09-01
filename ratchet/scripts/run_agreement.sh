#!/usr/bin/env bash
# Differential-test every corpus rung: run its `.rb` under **CRuby** (the oracle)
# and under the **Lean semantics** (`../lean/RubyCore`, via the difftest engine's
# `--sut lean`), and compare the observations -- stdout, the `inspect` of the
# final value, and the escaping exception's (class, message).
#
# Why the ratchet needs this. A corpus rung asserts two things: that its `.json`
# is what the real desugarer emits for its `.rb` (guaranteed by construction --
# `scripts/generate_corpus.py` runs the desugarer, nothing is hand-transcribed),
# and that the Lean model this whole package types *agrees with Ruby* on that
# program. The second is not guaranteed by anything, and it is the load-bearing
# one: a rung the model runs differently from CRuby is a rung whose type is a
# statement about a fiction. `run_ratchet.sh` runs this first for that reason.
#
# It also keeps the `unsafe_program` targets honest in both directions: a rung
# recorded as raising TypeError has to actually raise it, on both sides.
#
# Requires `uv` (the difftest engine's runner) and a CRuby on PATH (override
# with DIFFTEST_RUBY=/path/to/ruby). Set RATCHET_SKIP_AGREEMENT=1 to skip --
# e.g. when iterating on `chk` alone, where nothing about the corpus changed.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

RATCHET_DIR="$PWD"
cd ../difftest
exec uv run python -m difftest replay "$RATCHET_DIR/corpus" --sut lean "$@"
