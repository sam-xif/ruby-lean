#!/bin/bash
# Build the metatheory and re-verify axiom cleanliness — `PLAN.md` §4 norm 5,
# "build the `Proof/` files at batch boundaries; a green ratchet does not mean the
# proofs still work".
#
# That norm existed and was not followed, and the cost was three independent
# breaks sitting undetected for 24 commits (L119):
#
#   * L101 put `matchGlobal` in front of the gvar read, so `Step.varGvar`'s
#     "a gvar read is `getGlobal`" stopped being true → `Step.sound` failed, and
#     with it every file that imports it (14 of 15);
#   * L103 retired the global `reprPure` flag, so `StaticSoundness` was still
#     case-splitting on a `reprSensitive` constant that no longer existed;
#   * the boot heap grew from 37 to 40 objects, so `T5Loop`'s hard-coded `clsA`
#     id pointed at an existing boot object.
#
# None of them is deep. All three were invisible because `Proof/` is off the
# default build target — which is the right call for build times and the wrong
# call for drift, so this script is the compromise: one command, run it at batch
# boundaries.
#
#   scripts/check-proofs.sh
#
# Exit 0 iff every proof file builds and every headline theorem depends on
# nothing beyond Lean's own three axioms.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 1

echo "== building RubyCore/Proof/ (lake build Metatheory)"
if ! lake build Metatheory 2>&1 | tail -3; then
  echo "FAIL: the metatheory does not build"
  exit 1
fi
if lake build Metatheory 2>&1 | grep -qE "^error:"; then
  echo "FAIL: the metatheory does not build"
  exit 1
fi

# `#print axioms` on the results that are claimed elsewhere (AGENTS.md, PLAN.md
# §9). "Axiom-clean" here means *exactly* Lean's three — `sorryAx` or any
# project-local axiom is a failure.
AX=$(mktemp /tmp/rubycore-axioms-XXXXXX.lean)
trap 'rm -f "$AX"' EXIT
cat > "$AX" <<'LEAN'
import RubyCore.Proof.StaticSoundness
import RubyCore.Proof.Adequacy
import RubyCore.Proof.T5
import RubyCore.Proof.T5Loop
import RubyCore.Proof.SorbetConcrete
#print axioms RubyCore.Proof.invariant_sound
#print axioms RubyCore.Proof.invariant_sound_from
#print axioms RubyCore.Proof.Static.check_sound
#print axioms RubyCore.Proof.Step.sound
#print axioms RubyCore.Proof.Step.complete
#print axioms RubyCore.Proof.Step.deterministic
#print axioms RubyCore.Proof.Step.adequacy
#print axioms RubyCore.Proof.T5Loop.t5_loop_type_safe
LEAN

echo "== axioms"
OUT=$(lake env lean "$AX" 2>&1)
echo "$OUT"
if echo "$OUT" | grep -qE "sorryAx|error"; then
  echo "FAIL: a theorem is missing, or depends on sorry / an unexpected axiom"
  exit 1
fi
echo "OK: metatheory builds; every theorem above rests on propext + Classical.choice + Quot.sound only"
