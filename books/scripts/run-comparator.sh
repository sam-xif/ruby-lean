#!/usr/bin/env bash
# Check the validator's safety theorems with `leanprover/comparator` — an independent
# judge that does not load this package's .olean files into an elaborator at all.
#
#   scripts/run-comparator.sh
#
# What a pass means. For `validateD_safe`, `validateD_safe_boot` and `validateD_safe_run`
# (`Comparator/config.json`), the comparator:
#
#   1. exports the statements from `Comparator/Challenge.lean` (statement only, `sorry`
#      for a proof) and from `Books/TypeSoundness/Soundness.lean` with `lean4export`, and checks that each
#      statement — and every constant it transitively mentions — is identical in both;
#   2. checks that the proofs in `Books.TypeSoundness.Soundness` depend on no axiom beyond `propext`,
#      `Quot.sound` and `Classical.choice`;
#   3. replays the whole exported dependency closure of the proofs into a fresh Lean
#      kernel.
#
# This is a stronger statement than `#print axioms`: it does not trust the elaborator,
# the environment extensions, or anything a file could do at elaboration time.
#
# ## Two things that are not stock, both visible in the output
#
# * **The replay is patched** (`Comparator/replay-mutual-siblings.patch`). The comparator
#   release for Lean 4.32 replays with `Lean4Checker.Replay`, which, on reaching a mutual
#   inductive block, pre-replays the constants used by the entry inductive's type and by
#   every constructor, but not by the *types of the other inductives* in the block.
#   `Checker.Audit.DJudge` is reached through its sibling `DMethod`, and its type is the
#   only thing in the block that mentions `Checker.ctx0` (through `optParam Ctx ctx0`), so
#   the unpatched replay stops with `(kernel) unknown constant 'Checker.ctx0'`. The patch
#   is three lines and can only make the replay send *more* declarations to the kernel
#   first; every declaration still goes through `addDeclCore`. `COMPARATOR_UNPATCHED=1`
#   runs the stock tool, to see the failure. Lean's own `Lean/Replay.lean` has the same
#   loop; reported upstream, with a one-file reproducer, as
#   https://github.com/leanprover/lean4/issues/15529.
# * **The sandbox is real only on Linux.** `landrun` is Landlock; off Linux, or without it
#   on PATH, this falls back to the comparator's own `fake-landrun.sh`, which sandboxes
#   nothing. That weakens exactly one of the comparator's guarantees — protection against
#   a *malicious* solution file tampering with the build — and none of 1–3 above. It is
#   the right trade for checking our own proof and the wrong one for judging a stranger's.
#   Set `COMPARATOR_LANDRUN` to use a real one.
#
# The comparator is fetched into `.lake/comparator` (ignored) at a pinned commit and built
# on this package's own toolchain, which is what `lean4export` has to match.
set -euo pipefail
cd "$(dirname "$0")/.." || exit 1

COMPARATOR_REPO=https://github.com/leanprover/comparator
COMPARATOR_REV=07bc4ea40f2266dcb861820a2ec1fa3244ed307f   # tag v4.32.0
DIR=.lake/comparator
REPLAY=$DIR/.lake/packages/Lean4Checker/Lean4Checker/Replay.lean
PATCH=$PWD/Comparator/replay-mutual-siblings.patch

if [[ ! -d $DIR/.git ]]; then
  echo "== fetching comparator @ ${COMPARATOR_REV:0:12}"
  mkdir -p "$DIR"
  git -C "$DIR" init -q
  git -C "$DIR" remote add origin "$COMPARATOR_REPO"
  git -C "$DIR" fetch -q --depth 1 origin "$COMPARATOR_REV"
  git -C "$DIR" checkout -q FETCH_HEAD
fi
if [[ $(git -C "$DIR" rev-parse HEAD) != "$COMPARATOR_REV" ]]; then
  echo "FAIL: $DIR is not at the pinned commit; remove it and rerun"
  exit 1
fi
cp lean-toolchain "$DIR/lean-toolchain"

# Fetch the dependencies before deciding the replay's patch state, then build.
[[ -f $REPLAY ]] || (cd "$DIR" && lake build Lean4Checker.Replay >/dev/null)
git -C "$(dirname "$REPLAY")/.." checkout -q -- Lean4Checker/Replay.lean
if [[ ${COMPARATOR_UNPATCHED:-0} == 1 ]]; then
  echo "== replay: STOCK (COMPARATOR_UNPATCHED=1)"
else
  echo "== replay: patched with Comparator/replay-mutual-siblings.patch"
  git -C "$(dirname "$REPLAY")/.." apply "$PATCH"
fi
echo "== building comparator and lean4export on $(cat lean-toolchain)"
if ! (cd "$DIR" && lake build lean4export comparator 2>&1 | tail -1); then
  echo "FAIL: the comparator does not build"
  exit 1
fi

ABS=$PWD/$DIR

# A checkout that predates the move of the proofs into this package can still hold a
# compiled `Comparator.Challenge` under the *model's* build directory, with the old
# theorem names. It is on the search path ahead of ours, and the exporter would read it.
STALE=../ruby-lean/.lake/build/lib/lean/Comparator
if [[ -e $STALE ]]; then
  echo "FAIL: stale build output at $STALE (from before the proofs moved to books/)"
  echo "  remove it and rerun:  rm -rf ../ruby-lean/.lake/build/{lib/lean,ir}/{Comparator,Denote,Ratchet,Semantics}"
  exit 1
fi
export COMPARATOR_LEAN4EXPORT=${COMPARATOR_LEAN4EXPORT:-$ABS/.lake/packages/lean4export/.lake/build/bin/lean4export}
if [[ -z ${COMPARATOR_LANDRUN:-} ]]; then
  if command -v landrun >/dev/null; then
    COMPARATOR_LANDRUN=$(command -v landrun)
    echo "== sandbox: landrun ($COMPARATOR_LANDRUN)"
  else
    COMPARATOR_LANDRUN=$ABS/scripts/fake-landrun.sh
    echo "== sandbox: NONE — landrun not found, using the comparator's fake-landrun.sh"
  fi
fi
export COMPARATOR_LANDRUN

echo "== comparator: Comparator.Challenge vs Books.TypeSoundness.Soundness"
LOG=$(mktemp /tmp/rubylean-comparator-XXXXXX.log)
trap 'rm -f "$LOG"' EXIT
lake env "$ABS/.lake/build/bin/comparator" Comparator/config.json >"$LOG" 2>&1 && rc=0 || rc=$?
# The build replay is hundreds of lines of linter output; keep the comparator's own.
grep -E "^(Building|Exporting|Running|Lean default kernel|Your solution|uncaught|error)|Child exited" "$LOG" | cut -c1-240 || true
if [[ $rc != 0 ]] || ! grep -q "^Your solution is okay!" "$LOG"; then
  echo "FAIL: the comparator did not accept (exit $rc)"
  exit 1
fi
echo "OK: the comparator accepts — statements match, axioms are Lean's three, the kernel replays the closure"
