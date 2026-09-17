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
#
# ## What this audits, after the pre-ratchet layers were removed
#
# The four earlier type-checking iterations (`Types/` + `Proof/Static/`'s checker
# soundness, `Cert/`, `Judgment/`, the Iris `HJudge/`) are gone, and with them ~60
# of the 71 names this script used to print. What is left is two things, and they
# are different in kind:
#
#   1. **The machine's own metatheory** — `Step` and its adequacy, the reachability
#      invariant (`invariant_sound`, which is what "type safety by reachability"
#      names), the ancestor-growth congruence, the worked type-safe programs.
#      Nothing downstream depends on these; they are claims about the semantics.
#   2. **The lemmas the live checker actually uses** — `Denote/Sem/` imports
#      `Proof/Judgment/{ClsFresh,ModFresh}` and, through them, `Proof/Static/`'s
#      declaration-table and locals lemmas. These are *on* the default target by
#      way of `Denote`, so the ratchet gate already fails if they break; they are
#      audited here for their axioms, which the gate does not check.
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

# `#print axioms` on the results that are claimed elsewhere (AGENTS.md, README).
# "Axiom-clean" here means *exactly* Lean's three — `sorryAx` or any project-local
# axiom is a failure.
AX=$(mktemp /tmp/rubycore-axioms-XXXXXX.lean)
trap 'rm -f "$AX"' EXIT
cat > "$AX" <<'LEAN'
import RubyCore.Proof.Adequacy
import RubyCore.Proof.TypeSafety
import RubyCore.Proof.T5Loop
import RubyCore.Proof.AncestorsGrow
import RubyCore.Proof.SorbetSafety
import RubyCore.Proof.Static.Mono
import RubyCore.Proof.Static.Decls
import RubyCore.Proof.Static.Locals
import RubyCore.Proof.Judgment.ClsFresh
import RubyCore.Proof.Judgment.ModFresh
import RubyCore.Proof.Judgment.TableRet
-- 1. The machine. `Step` is the definition of record and `stepFn` its executable
-- witness; the three say the two agree, in both directions, uniquely.
#print axioms RubyCore.Proof.Step.sound
#print axioms RubyCore.Proof.Step.complete
#print axioms RubyCore.Proof.Step.deterministic
#print axioms RubyCore.Proof.Step.adequacy
-- Type safety **by reachability**: no type system, just "no reachable state is
-- type-stuck". `invariant_sound` is the general form, the other two its results.
#print axioms RubyCore.Proof.invariant_sound
#print axioms RubyCore.Proof.invariant_result_sound
#print axioms RubyCore.Proof.invariant_sound_from
-- The same statement narrowed to the Sorbet blame family (the typed-portion-safety note).
#print axioms RubyCore.Proof.sorbet_invariant_sound
-- A worked end: the T5 dispatch loop runs type-safe at the booted heap.
#print axioms RubyCore.Proof.T5Loop.t5_loop_type_safe
-- L144's congruence — ancestors agree across an *allocating* step — and the
-- certificate its `Saturated` hypothesis is decided by (`scripts/probes/`).
#print axioms RubyCore.Proof.ancestors_congr_grow
#print axioms RubyCore.Proof.saturatedB_sound
-- 2. What the live checker imports. `Denote/Sem/{ClassHeap,ClassGrowth,SubclassHeap}`
-- and `Denote/Typed/{ClassActivation,ClassEntry}` take class/module freshness from
-- here, so these lemmas sit under `validateD_safe_boot` even though they live in
-- `Proof/`. The declaration-table lemmas below are what they in turn rest on.
#print axioms RubyCore.Proof.Judgment.evalExpr_class_fresh
#print axioms RubyCore.Proof.Judgment.judge_table_ret
#print axioms RubyCore.Proof.Static.DeclsOk_grow
#print axioms RubyCore.Proof.Static.DeclsOk_addRow_here
#print axioms RubyCore.Proof.Static.DeclsOk_of_subDecls
#print axioms RubyCore.Proof.Static.inv_grow_value
#print axioms RubyCore.Proof.Static.infer_mono
LEAN

echo "== axioms"
OUT=$(lake env lean "$AX" 2>&1)
echo "$OUT"
if echo "$OUT" | grep -qE "sorryAx|error"; then
  echo "FAIL: a theorem is missing, or depends on sorry / an unexpected axiom"
  exit 1
fi

# The measurements. None of these is a theorem's certificate any more — the one
# that was (`heapOkB`, F0's, for the deleted `check_sound_withPrelude`) went with
# its theorem. What they still are is a *ratchet on the prelude*: each decides a
# heap fact that a surviving proof assumes or that a prelude change could quietly
# falsify, so a red line here is a reason to look before the proofs notice.
echo "== L144 certificate (saturatedB at the prelude-booted heap)"
if ! lake env lean --run scripts/probes/ancestors_probe.lean; then
  echo "FAIL: the ancestor walk is not saturated at the booted heap, or an edge points out of bounds"
  exit 1
fi

echo "== F1b.9 measurement (no two class objects share a name)"
if ! lake env lean --run scripts/probes/names_probe.lean; then
  echo "FAIL: two class objects share a name at the booted heap"
  exit 1
fi

echo "== L176 measurement (a name-keyed constant table is not shadowed)"
if ! lake env lean --run scripts/probes/consts_probe.lean; then
  echo "FAIL: a class in front of Object on an admitted chain owns a constant, or Object is unreachable"
  exit 1
fi

echo "== L180 measurement (no class object is plainRecv)"
if ! lake env lean --run scripts/probes/classobj_probe.lean; then
  echo "FAIL: a class object is plainRecv — entry_dispatch's receiver split is unsound"
  exit 1
fi

echo "== L186 measurement (a Module#=== row on the class-object arm is witnessable)"
if ! lake env lean --run scripts/probes/classeq_probe.lean; then
  echo "FAIL: \`===\` on a class object no longer resolves to the Module#=== builtin"
  exit 1
fi

echo "== L189 measurement (which class names are admissible)"
lake env lean --run scripts/probes/reopen_probe.lean

echo "OK: metatheory builds; every theorem above rests on propext + Classical.choice + Quot.sound only; the booted heap's ancestor walk is saturated and its class names are unique"
