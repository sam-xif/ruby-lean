import Denote.Sem.Core.State

/-! Input framing for constant and nested-class claims across fresh registration. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

structure ClassTablesFrame (κ : Ctx) (name : String) (m : Machine) : Prop where
  consts : ∀ cn τ, constGet? κ cn = some τ → FirstOrder τ = true
  paths : ∀ owner cn τ, envGet? κ.consts (constKeyIn owner cn) = some τ →
    FirstOrder τ = true ∧ cn ≠ name ∧ ∃ k, classNamed? m.heap owner = some k
  nested : ∀ owner cn c, clsGet? κ.classes (owner ++ "::" ++ cn) = some c →
    cn ≠ name ∧ ∃ k, classNamed? m.heap owner = some k

theorem ClassTablesFrame.heap {κ : Ctx} {name : String} {m n : Machine}
    (h : ClassTablesFrame κ name m) (hh : n.heap = m.heap) : ClassTablesFrame κ name n :=
  ⟨h.consts, by simpa only [hh] using h.paths, by simpa only [hh] using h.nested⟩

theorem ClassTablesFrame.empty {κ : Ctx} {name : String} {m : Machine}
    (hc : κ.consts = []) (hk : κ.classes = []) : ClassTablesFrame κ name m := by
  refine ⟨?_, ?_, ?_⟩
  · intro cn τ ht
    simp only [constGet?, constPaths] at ht
    cases he : κ.frame <;> simp [he, hc, envGet?] at ht
  · intro owner cn τ ht; simp [hc, envGet?] at ht
  · intro owner cn c ht; simp [hk, clsGet?] at ht

end Ratchet.Denote
