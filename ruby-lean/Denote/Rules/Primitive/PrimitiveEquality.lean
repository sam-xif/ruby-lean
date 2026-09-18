import Denote.Rules.Primitive.PrimitiveStep

/-! Integer equality can reverse into the argument's `==`. A name-free guard excludes
program-defined equality, so the primitive row may accept any argument type. -/

set_option autoImplicit false
set_option maxRecDepth 4000
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem no_program_eq {κ : Ctx} {I : Ty} {Γ : Env} {m : Machine} (hm : StateOk κ Γ I m)
    (v : Value) (hfree : nameFreeN κ "==" = true := by rfl) : Builtins.hasProgramEq m.heap v = false := by
  unfold Builtins.hasProgramEq
  cases hl : lookup m.heap v "==" with
  | none => rfl
  | some p =>
    obtain ⟨owner, md⟩ := p
    rcases hm.exact.lookup hl with hp | hb | hf
    · simp [hp]
    · cases h : md.builtin <;> simp_all
    · rw [hfree] at hf; cases hf

theorem int_eq_defer {κ : Ctx} {I : Ty} {Γ : Env} {m : Machine} (hm : StateOk κ Γ I m)
    (x : Int) (v : Value) (hfree : nameFreeN κ "==" = true := by rfl) :
    Builtins.deferTwin? m.heap "Integer#==" (.int x) [v] = none := by
  simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
    Builtins.toAryDefer?, Builtins.num?, no_program_eq hm v hfree]

theorem int_eq_step {κ : Ctx} {I : Ty} {Γ : Env} {m : Machine} (hm : StateOk κ Γ I m)
    (hk : m.kont = []) (x : Int) (v : Value) :
    StepSpec m Γ .bool (builtinStep (Builtins.run "Integer#==" (.int x) [v] m)) κ I := by
  rw [Builtins.run]
  split
  · trivial
  · change StepSpec m Γ .bool (builtinStep (Builtins.runNumerics "Integer#==" (.int x) [v] m)) κ I
    simp only [Builtins.runNumerics, Builtins.binArg]
    cases Builtins.num? v <;> exact stepSpec_value hm hk (by simp [denM, isBoolV])
  all_goals intro o h; cases h

#print axioms int_eq_step
end Ratchet.Denote.Typed
