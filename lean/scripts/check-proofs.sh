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
import RubyCore.Proof.PreludeInv
import RubyCore.Proof.Adequacy
import RubyCore.Proof.T5
import RubyCore.Proof.T5Loop
import RubyCore.Proof.SorbetConcrete
import RubyCore.Proof.AncestorsGrow
import RubyCore.Proof.Static.Mono
import RubyCore.Proof.Static.Assn
#print axioms RubyCore.Proof.invariant_sound
#print axioms RubyCore.Proof.invariant_sound_from
#print axioms RubyCore.Proof.Static.check_sound
#print axioms RubyCore.Proof.Static.check_sound_withPrelude
#print axioms RubyCore.Proof.Static.check_sound_withPrelude'
#print axioms RubyCore.Proof.Step.sound
#print axioms RubyCore.Proof.Step.complete
#print axioms RubyCore.Proof.Step.deterministic
#print axioms RubyCore.Proof.Step.adequacy
#print axioms RubyCore.Proof.T5Loop.t5_loop_type_safe
#print axioms RubyCore.Proof.ancestors_congr_grow
#print axioms RubyCore.Proof.saturatedB_sound
#print axioms RubyCore.Proof.Static.DeclsOk_grow
#print axioms RubyCore.Proof.Static.inv_grow_value
#print axioms RubyCore.Proof.Static.infer_mono
-- The assertion language (L165). `denote_declAssn` is the faithfulness theorem —
-- `⟦declAssn D⟧ h ↔ DeclsOk D h`, both directions — and it is what closes
-- `assertion-language.md` §9.3's honest weak point for the declaration fragment:
-- the syntax-to-semantics map is *checked*, not merely defined. `assn_sound_from`
-- is the invariant restated over it, inheriting every consecution case.
#print axioms RubyCore.Proof.Static.denote_declAssn
#print axioms RubyCore.Proof.Static.entail_sound
#print axioms RubyCore.Proof.Static.assn_sound_from
#print axioms RubyCore.Proof.Static.assn_check_sound
LEAN

echo "== axioms"
OUT=$(lake env lean "$AX" 2>&1)
echo "$OUT"
if echo "$OUT" | grep -qE "sorryAx|error"; then
  echo "FAIL: a theorem is missing, or depends on sorry / an unexpected axiom"
  exit 1
fi
# F0's certificate (`homebrew/widening-the-fragment.md` §3). `check_sound_withPrelude`
# assumes `heapOkB` of the prelude-booted heap, and that Bool cannot be decided in
# the kernel (`Lean.Json.parse` does not reduce; L94 bans `native_decide`), so it is
# decided by running it. The probe computes the *same* function the lemma names —
# `RubyCore/HeapCert.lean`, outside `Proof/` precisely so there is one copy.
echo "== F0 certificate (heapOkB at the prelude-booted heap)"
if ! lake env lean --run scripts/heapok_probe.lean; then
  echo "FAIL: the prelude-booted heap does not satisfy the heap half of Inv"
  exit 1
fi

# L144's certificate, and it is here for the same reason F0's is: `ancestors_congr_grow`
# — the ancestor congruence across an *allocating* step — assumes `Saturated`, i.e. the
# ancestor walk has finished before its fuel runs out. `saturatedB` decides it, the
# probe runs it at the prelude-booted heap, and if a prelude change ever makes a walk
# fuel-sensitive the hypothesis silently stops being satisfiable. The probe also
# reports the clause `HANDOFF.md` proposed instead (the chain descending in `ObjId`),
# which is **false** at the booted heap — 10 edges — and is kept visible on purpose.
echo "== L144 certificate (saturatedB at the prelude-booted heap)"
if ! lake env lean --run scripts/ancestors_probe.lean; then
  echo "FAIL: the ancestor walk is not saturated at the booted heap, or an edge points out of bounds"
  exit 1
fi

# F1b.9's measurement, kept as a check rather than a one-off. A declaration row is
# keyed on a class *name*, so `DeclsOk`'s obligation quantifies over every class
# object with that name while a `def` installs on exactly one — `ClassOk`'s
# uniqueness clause is what closes the gap, and this reports the general fact it
# restricts. If a prelude change ever makes two class objects share a name, the row
# stops being witnessable and this says so before a proof does.
echo "== F1b.9 measurement (no two class objects share a name)"
if ! lake env lean --run scripts/names_probe.lean; then
  echo "FAIL: two class objects share a name at the booted heap"
  exit 1
fi

echo "OK: metatheory builds; every theorem above rests on propext + Classical.choice + Quot.sound only; heapOkB and saturatedB hold at the booted heap; class names are unique"
