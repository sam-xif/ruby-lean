import Denote.Rules.Expr.BranchNilQuery

/-! `if x.nil?` on a nilable String local. Object#nil? at a String answers false, or
gates as unsupported at a byte-string operand. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem RunWith.unsupported {origin start : Machine} {Γ : Env} {τ I : Ty} {κ : Ctx}
    {P : Value → Machine → Prop} {msg : String}
    (ha : answerPoint start = none) (hs : Interp.stepFn start = .unsupported msg) :
    RunWith origin start Γ τ κ I P := by
  refine ⟨(RunSpec.unsupported (origin := origin) (Γ := Γ) (τ := τ) (κ := κ) (I := I) ha hs).1, ?_⟩
  intro fuel a m rest hr
  cases fuel with
  | zero => rw [runA_zero ha] at hr; cases hr
  | succ f => rw [runA_succ ha, hs] at hr; cases hr

theorem str_nil_run (m : Machine) (o : ObjId) :
    Builtins.run "Object#nil?" (.ref o) [] m = .ok (.bool false) m ∨
      ∃ msg, Builtins.run "Object#nil?" (.ref o) [] m = .unsupported msg := by
  have hq : ("Object#nil?".endsWith "#==" || "Object#nil?".endsWith "#eql?" ||
      "Object#nil?".endsWith "#!=" || Builtins.pureEqualityBids.contains "Object#nil?") = false := by
    decide +kernel
  simp only [Builtins.run]
  split
  · exact .inr ⟨_, rfl⟩
  · simp only [hq, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    left; rfl

end Ratchet.Denote.Typed
