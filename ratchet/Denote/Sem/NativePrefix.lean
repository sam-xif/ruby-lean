import Ratchet.NativeInstanceNames
import Denote.Sem.NativeGuards

/-! The copied selector set is checked against the model, and absence excludes native
interception on any heap/prefix. No class-name/heap-label agreement is assumed. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

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
    (hf : ∀ cn, crubyClassDefines cn name = false) : Interp.crubyShadow h chain name = none := by
  induction chain with
  | nil => rfl
  | cons k ks ih => simpa [Interp.crubyShadow, List.firstM, hf] using ih

theorem nativeInstanceFreeB_shadow {h : Heap} {chain : List ObjId} {name : String}
    (hf : nativeInstanceFreeB name = true) : Interp.crubyShadow h chain name = none :=
  crubyShadow_free (nativeInstanceFreeB_sound hf)

#guard nativeInstanceFreeB "speak"
#guard !nativeInstanceFreeB "to_s"
#guard !nativeInstanceFreeB "length"
#print axioms nativeInstanceFreeB_shadow
end Ratchet.Denote
