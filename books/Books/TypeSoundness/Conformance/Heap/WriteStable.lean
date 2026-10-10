import Books.TypeSoundness.Checker.Guards.WriteTypes
import Books.TypeSoundness.Conformance.Heap.WriteState

/-! The executable type guard is sufficient for denotation preservation, including
collection nesting. It does not assert that arbitrary instance field snapshots survive.
-/
set_option autoImplicit false
namespace Checker.Soundness
open RubyCore Checker

theorem denM_writeStable_aux (m : Machine) (x : String) (v : Value) :
    ∀ τ : Ty, IvarStable τ = true →
    (∀ w, denM τ m w ↔ denM τ (Interp.bindIvar m x v) w) ∧
    (∀ seen g, denSpineFrom seen τ m g ↔ denSpineFrom seen τ (Interp.bindIvar m x v) g) := by
  have hi := bindIvar_ivarOnly m x v
  have ha (w : Value) : arrElems? (Interp.bindIvar m x v).heap w = arrElems? m.heap w := by
    cases w <;> simp only [arrElems?, hi.payload]
  have hh (w : Value) : hshEntries? (Interp.bindIvar m x v).heap w = hshEntries? m.heap w := by
    cases w <;> simp only [hshEntries?, hi.payload]
  intro τ
  induction τ with
  | int | bool | nilT | sym | float | any | never | ivar0 =>
    intro _; exact ⟨fun _ => by simp [denM], fun _ _ => by simp [denSpineFrom]⟩
  | cls cn =>
    intro _
    exact ⟨fun _ => by simp only [denM, bindIvar_isAName], fun _ _ => by simp [denSpineFrom]⟩
  | clsOf cn =>
    intro _
    exact ⟨fun _ => by simp only [denM, isClassRefNamed, bindIvar_classNamed],
      fun _ _ => by simp [denSpineFrom]⟩
  | nilable τ ih =>
    intro hf
    exact ⟨fun _ => by rw [denM, denM]; exact or_congr_right ((ih hf).1 _),
      fun _ _ => by simp [denSpineFrom]⟩
  | union σ τ ihσ ihτ =>
    intro hf
    simp only [IvarStable, Bool.and_eq_true] at hf
    exact ⟨fun _ => by rw [denM, denM]; exact or_congr ((ihσ hf.1).1 _) ((ihτ hf.2).1 _),
      fun _ _ => by simp [denSpineFrom]⟩
  | sameAs y τ ih =>
    intro hf
    exact ⟨fun _ => by rw [denM, denM]; exact (ih hf).1 _, fun _ _ => by simp [denSpineFrom]⟩
  | arrayOf τ ih =>
    intro hf
    refine ⟨fun w => ?_, fun _ _ => by simp [denSpineFrom]⟩
    simp only [denM, ha]
    exact exists_congr fun xs => and_congr_right fun _ =>
      forall_congr' fun w => imp_congr_right fun _ => (ih hf).1 w
  | hashOf k w ihk ihw =>
    intro hf
    simp only [IvarStable, Bool.and_eq_true] at hf
    refine ⟨fun z => ?_, fun _ _ => by simp [denSpineFrom]⟩
    simp only [denM, hh]
    exact exists_congr fun es => and_congr_right fun _ =>
      forall_congr' fun p => imp_congr_right fun _ =>
        and_congr ((ihk hf.1).1 p.1) ((ihw hf.2).1 p.2)
  | inst cn I ih =>
    intro hf
    cases I <;> try cases hf
    exact ⟨fun _ => by simp only [denM, denSpineFrom, bindIvar_isExactInst],
      fun _ _ => by simp [denSpineFrom]⟩
  | ivarCons y σ rest ihσ ihrest =>
    intro hf
    simp only [IvarStable, Bool.and_eq_true] at hf
    refine ⟨fun _ => by simp [denM], fun seen g => ?_⟩
    simp only [denSpineFrom]
    exact and_congr (or_congr_right ((ihσ hf.1).1 _)) ((ihrest hf.2).2 _ _)
  | arrow0 _ _ | arrowCons _ _ _ _ | clos _ _ _ _ _ => intro hf; cases hf

theorem denM_writeStable {m : Machine} {x : String} {v w : Value} {τ : Ty}
    (ht : IvarStable τ = true) (h : denM τ m w) : denM τ (Interp.bindIvar m x v) w :=
  ((denM_writeStable_aux m x v τ ht).1 w).mp h

theorem ivarStable_firstOrder {τ : Ty} (h : IvarStable τ = true) : FirstOrder τ = true := by
  induction τ with
  | inst cn I ih => cases I <;> simp_all [IvarStable, FirstOrder]
  | _ => simp_all [IvarStable, FirstOrder, Bool.and_eq_true]

/-- The relative data contract of initialization, including objects allocated after the
outer heap anchor. Field snapshots may change; types admitted by IvarStable survive. -/
def IvarTypePres (m n : Machine) : Prop :=
  ∀ τ, IvarStable τ = true → ∀ v, denM τ m v → denM τ n v

theorem IvarTypePres.refl (m : Machine) : IvarTypePres m m := fun _ _ _ h => h

theorem IvarTypePres.trans {m n p : Machine} (h : IvarTypePres m n)
    (h' : IvarTypePres n p) : IvarTypePres m p :=
  fun τ ht v hv => h' τ ht v (h τ ht v hv)

theorem IvarTypePres.reheap {m n m' n' : Machine} (h : IvarTypePres m n)
    (hm : m'.heap = m.heap) (hn : n'.heap = n.heap) : IvarTypePres m' n' := by
  intro τ ht v hv
  have hf := ivarStable_firstOrder ht
  exact (denM_heap_only hf hn).mpr (h τ ht v ((denM_heap_only hf hm).mp hv))

theorem IvarTypePres.bindIvar (m : Machine) (x : String) (v : Value) :
    IvarTypePres m (Interp.bindIvar m x v) := fun _ ht _ hv => denM_writeStable ht hv

#print axioms denM_writeStable
#print axioms IvarTypePres.reheap
end Checker.Soundness
