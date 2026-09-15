import Ratchet.ClassGuards
import Denote.Sem.ClassTables
import Denote.Sem.Reframe

/-! Interpret static frame guards without baking in a class or demanding empty class
tables: any number of unqualified class records have no nested-name claims. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

theorem reframeTypesB_sound {κ : Ctx} {I : Ty} (h : reframeTypesB κ I = true) : ReframeFO κ I := by
  simp only [reframeTypesB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hi, hs⟩, hb⟩, hc⟩ := h
  have entry (x : String) (τ : Ty) (hx : envGet? κ.consts x = some τ) : FirstOrder τ = true := by
    obtain ⟨y, hy⟩ := envGet?_mem hx
    exact List.all_eq_true.mp hc (y, τ) hy
  refine ⟨hi, ?_, ?_, ?_, entry⟩
  · intro τ ht; simpa only [ht, Option.all_some] using hs
  · intro τ ht; simpa only [ht, Option.all_some] using hb
  · intro x τ ht
    obtain ⟨p, hp⟩ := constGet?_entry ht
    exact entry p τ hp

theorem plainClassTablesB_sound {κ : Ctx} {name : String} {m : Machine}
    (h : plainClassTablesB κ = true) : ClassTablesFrame κ name m := by
  simp only [plainClassTablesB, Bool.and_eq_true] at h
  obtain ⟨hc, ht⟩ := h
  have hc : κ.consts = [] := List.isEmpty_iff.mp hc
  refine ⟨?_, ?_, ?_⟩
  · intro x τ hx; rw [constGet?_empty hc x] at hx; cases hx
  · intro owner x τ hx; simp [hc, envGet?] at hx
  · intro owner x c hx
    have hmem := List.mem_of_find?_eq_some hx
    have hname : c.name = owner ++ "::" ++ x := by simpa using List.find?_some hx
    exact False.elim (unqualifiedClassB_ne_path (List.all_eq_true.mp ht c hmem) owner x hname)

theorem explicitReceiverB_sound {e : Ratchet.Expr} (h : explicitReceiverB e = true) :
    (match toRuby e with | .self' => .selfRecv | _ => .explicit) = SendSite.explicit := by
  cases e <;> first | rfl | cases h

#print axioms reframeTypesB_sound
#print axioms plainClassTablesB_sound
end Ratchet.Denote
