import Lean

import Books.TypeSoundness.Checker.Static.NativeInstanceNames
import Books.TypeSoundness.Conformance.Names.NativeGuards

/-! The copied selector set is checked against the model, and absence excludes native
instance interception. Singleton and optional-library sources must be excluded
for the actual prefix separately; they are not consequences of instance-name absence.

Both directions of the copy are checked, so the hand-maintained list in
`Checker.Static.NativeInstanceNames` cannot drift from the model silently: a name
the model defines but the copy lacks fails `instance_covered`, and a name the copy
retains but the model no longer defines fails the `#guard` on
`extraNativeInstanceNames`. -/
set_option autoImplicit false
namespace Checker.Soundness
open RubyCore Checker

-- The copy can drift in two directions, and only the first used to be checked, so
-- the second could narrow the checker's native-prefix declines with nothing to
-- notice (issue #55). `#eval` either one for the offenders when a guard fails.

/-- Names the model defines that the copy lacks: what a `FOLD` addition leaves out. -/
def missingNativeInstanceNames : List String :=
  (crubyMethodNames.flatMap (·.2)).eraseDups.filter fun n =>
    !nativeInstanceNames.contains n

/-- Names the copy declines that the model does not define: what a shrunken table
    leaves behind. -/
def extraNativeInstanceNames : List String :=
  nativeInstanceNames.filter fun n =>
    !crubyMethodNames.any (fun p => p.2.contains n)

-- `instance_covered` below is the direction `nativeInstanceFreeB_sound` needs; a
-- `decide` failure names neither the selector nor the class, so the same two
-- questions are asked here where the answer is a list.
#guard missingNativeInstanceNames.isEmpty
#guard extraNativeInstanceNames.isEmpty

private theorem instance_covered : crubyMethodNames.all
    (fun p => p.2.all nativeInstanceNames.contains) = true := by decide +kernel

theorem nativeInstanceFreeB_sound {name : String} (h : nativeInstanceFreeB name = true) :
    ∀ cn, crubyClassDefines cn name = false := by
  have hn : nativeInstanceNames.contains name = false := by
    simpa only [nativeInstanceFreeB, Bool.not_eq_true'] using h
  intro cn
  unfold crubyClassDefines
  cases hf : crubyMethodNames.find? (·.1 == cn) with
  | none => rfl
  | some p =>
    have hc := List.all_eq_true.mp instance_covered p (List.mem_of_find?_eq_some hf)
    cases hm : p.2.contains name with
    | false => exact hm
    | true =>
      have ht := List.all_eq_true.mp hc name (List.contains_iff_mem.mp hm)
      rw [hn] at ht
      cases ht

theorem crubyShadow_free {h : Heap} {chain : List ObjId} {name : String}
    (hf : ∀ cn, crubyClassDefines cn name = false)
    (hs : ∀ k ∈ chain, Interp.nativeSingletonMethod h k name = false)
    (hl : ∀ k ∈ chain, Interp.featureMethod h k name = false) :
    Interp.crubyShadow h chain name = none := by
  induction chain with
  | nil => rfl
  | cons k ks ih =>
    simpa [Interp.crubyShadow, List.firstM, hf, hs k (by simp), hl k (by simp)] using
      ih (fun j hj => hs j (by simp [hj])) (fun j hj => hl j (by simp [hj]))

theorem nativeInstanceFreeB_shadow {h : Heap} {chain : List ObjId} {name : String}
    (hf : nativeInstanceFreeB name = true)
    (hs : ∀ k ∈ chain, Interp.nativeSingletonMethod h k name = false)
    (hl : ∀ k ∈ chain, Interp.featureMethod h k name = false) :
    Interp.crubyShadow h chain name = none :=
  crubyShadow_free (nativeInstanceFreeB_sound hf) hs hl

#guard nativeInstanceFreeB "speak"
#guard !nativeInstanceFreeB "to_s"
#guard !nativeInstanceFreeB "length"
#print axioms nativeInstanceFreeB_shadow
end Checker.Soundness
