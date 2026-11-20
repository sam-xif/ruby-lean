#!/bin/bash
# Check the model's metatheory (Books/Metatheory/).
#
#   check-metatheory.sh          (from the repository root: make metatheory)
#
#   1. Build every file of the book.
#   2. Print the axioms of each headline theorem and of the lemmas the soundness
#      proof imports. Anything beyond propext, Classical.choice and Quot.sound
#      (including `sorry`) is a failure.
#   3. Run the heap probes. Some lemmas assume a fact about the heap the prelude
#      boots (for example, that no two classes share a name). Those facts are
#      decided here by running them on the real booted heap, so a change to the
#      prelude that would falsify one is caught.
#
# Exit 0 iff all three hold.
set -uo pipefail
cd "$(dirname "$0")/../../.." || exit 1   # books/, the Lake package

echo "== building Books/Metatheory/"
if ! lake build --log-level=error Metatheory; then
  echo "FAIL: the metatheory does not build"
  exit 1
fi

AX=$(mktemp /tmp/rubycore-axioms-XXXXXX.lean)
trap 'rm -f "$AX"' EXIT
cat > "$AX" <<'LEAN'
import Books.Metatheory.Machine.Adequacy
import Books.Metatheory.Reachability.TypeSafety
import Books.Metatheory.Examples.T5Loop
import Books.Metatheory.Heap.AncestorsGrow
import Books.Metatheory.Reachability.SorbetSafety
import Books.Metatheory.Typing.Infer.Mono
import Books.Metatheory.Typing.Infer.Decls
import Books.Metatheory.Typing.Infer.Locals
import Books.Metatheory.Heap.BootedHeap
import Books.Metatheory.Typing.Judge.FreshClass
import Books.Metatheory.Typing.Judge.FreshModule
import Books.Metatheory.Typing.Judge.TableRet
-- The machine. `Step` is the relational definition and `stepFn` the executable
-- one; these say the two agree, in both directions, uniquely.
#print axioms RubyCore.Proof.Step.sound
#print axioms RubyCore.Proof.Step.complete
#print axioms RubyCore.Proof.Step.deterministic
#print axioms RubyCore.Proof.Step.adequacy
-- Type safety by reachability: no type system, just "no reachable state is
-- type-stuck". `invariant_sound` is the general form, the other two its results.
#print axioms RubyCore.Proof.invariant_sound
#print axioms RubyCore.Proof.invariant_result_sound
#print axioms RubyCore.Proof.invariant_sound_from
-- The same statement narrowed to the failures Sorbet's runtime blames on the program.
#print axioms RubyCore.Proof.sorbet_invariant_sound
-- A worked instance: a method-dispatch loop runs type-safe from the booted heap.
#print axioms RubyCore.Proof.T5Loop.t5_loop_type_safe
-- The ancestor walk gives the same answer after the heap allocates, given the
-- `Saturated` hypothesis that `Probes/Ancestors.lean` decides.
#print axioms RubyCore.Proof.ancestors_congr_grow
#print axioms RubyCore.Proof.saturatedB_sound
-- The prelude boot produces exactly the generated literal, so a program can be
-- started on the literal without running the boot.
#print axioms RubyCore.Proof.boot_eq_booted
#print axioms RubyCore.Proof.initWithPrelude_eq_initOnBooted
-- What the type-soundness book imports: what creating a fresh class or module
-- does to the heap, and the declaration-table lemmas those rest on.
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
# Every `#print axioms` must have answered, and with nothing outside Lean's three.
if ! python3 -c '
import re, sys
asked = sum(1 for line in open(sys.argv[1]) if line.startswith("#print axioms"))
out = sys.argv[2]
allowed = {"propext", "Classical.choice", "Quot.sound"}
clean = len(re.findall(r"does not depend on any axioms", out))
lists = re.findall(r"depends on axioms: \[(.*?)\]", out, re.S)
extra = set()
for axioms in lists:
    extra |= {a.strip() for a in axioms.split(",")} - allowed
if extra:
    print("FAIL: unexpected axioms: " + ", ".join(sorted(extra)))
if clean + len(lists) != asked:
    print(f"FAIL: {asked} theorems asked for, {clean + len(lists)} answered")
sys.exit(1 if extra or clean + len(lists) != asked or "error" in out else 0)
' "$AX" "$OUT"; then
  echo "FAIL: a theorem is missing, or depends on sorry or an unexpected axiom"
  exit 1
fi

probe() {
  local label="$1" file="$2" failure="$3"
  echo "== booted heap: $label"
  if ! lake env lean --run "Books/Metatheory/Probes/$file"; then
    echo "FAIL: $failure"
    exit 1
  fi
}
probe "the ancestor walk is saturated" Ancestors.lean \
  "the ancestor walk is not saturated at the booted heap, or an edge points out of bounds"
probe "no two class objects share a name" Names.lean \
  "two class objects share a name at the booted heap"
probe "a name-keyed constant table is not shadowed" Consts.lean \
  "a class in front of Object on an admitted chain owns a constant, or Object is unreachable"
probe "no class object is a plain receiver" ClassObj.lean \
  "a class object is a plain receiver, so dispatch's receiver case split is not exhaustive"
probe "=== on a class object resolves to Module#===" ClassEq.lean \
  "=== on a class object no longer resolves to the Module#=== builtin"
probe "which class names can be reopened" Reopen.lean \
  "the reopen probe did not run"

echo "OK: the metatheory builds; every theorem above rests on propext, Classical.choice and Quot.sound only; the booted heap satisfies the assumptions the proofs make about it"
