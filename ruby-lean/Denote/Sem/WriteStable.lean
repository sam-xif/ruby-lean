import Ratchet.WriteTypes
import Denote.Sem.WriteState

/-! The executable type guard is sufficient for denotation preservation, including
collection nesting. It does not assert that arbitrary instance field snapshots survive.
-/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

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

#print axioms denM_writeStable
end Ratchet.Denote
