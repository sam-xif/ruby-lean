import Denote.Typed.PrimitiveAlloc
import Denote.Typed.PrimitiveEquality

/-! Each `DPrim` row discharges against the interpreter and preserves conformance on values. -/

set_option autoImplicit false
set_option maxRecDepth 4000
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

inductive ArgsDen (m : Machine) : List Ty → List Value → Prop
  | nil : ArgsDen m [] []
  | cons {τ : Ty} {v : Value} {tys : List Ty} {vs : List Value} :
      denM τ m v → ArgsDen m tys vs → ArgsDen m (τ :: tys) (v :: vs)

private theorem int_value {m : Machine} {v : Value} (h : denM .int m v) :
    ∃ n, v = .int n := by cases v <;> simp_all [denM, isIntV]

private theorem bool_value {m : Machine} {v : Value} (h : denM .bool m v) :
    ∃ b, v = .bool b := by cases v <;> simp_all [denM, isBoolV]

theorem primitive_builtin {site : SendSite} {Γ : Env} {m : Machine} {recv : Value} {args : List Value}
    {σ τ : Ty} {tys : List Ty} {name : String} (hp : DPrim σ name tys τ)
    (hm : StateOk ctx0 Γ .ivar0 m) (hk : m.kont = []) (hr : denM σ m recv)
    (ha : ArgsDen m tys args) :
    StepSpec m Γ τ (Interp.invoke m recv site name args none []) := by
  cases hp with
  | intAdd =>
    cases ha
    rename_i v vs hv hs
    cases hs
    obtain ⟨x, rfl⟩ := int_value hr
    obtain ⟨y, rfl⟩ := int_value hv
    rw [invoke_int_add hm x y]
    exact stepSpec_value hm hk (by simp [denM, isIntV])
  | intSub =>
    cases ha
    rename_i v vs hv hs
    cases hs
    obtain ⟨x, rfl⟩ := int_value hr
    obtain ⟨y, rfl⟩ := int_value hv
    rw [primitive_invoke (bid := "Integer#-") (k := Boot.integerId) hm
      (by simp [primitiveMethods]) rfl (by rfl) (by intro o ho; cases ho) (by rfl) (by rfl),
      int_sub_run]
    exact stepSpec_value hm hk (by simp [denM, isIntV])
  | intMul =>
    cases ha
    rename_i v vs hv hs
    cases hs
    obtain ⟨x, rfl⟩ := int_value hr
    obtain ⟨y, rfl⟩ := int_value hv
    rw [primitive_invoke (bid := "Integer#*") (k := Boot.integerId) hm
      (by simp [primitiveMethods]) rfl (by rfl) (by intro o ho; cases ho) (by rfl) (by rfl),
      int_mul_run]
    exact stepSpec_value hm hk (by simp [denM, isIntV])
  | intDiv =>
    cases ha
    rename_i v vs hv hs
    cases hs
    obtain ⟨x, rfl⟩ := int_value hr
    obtain ⟨y, rfl⟩ := int_value hv
    rw [primitive_invoke (bid := "Integer#/") (k := Boot.integerId) hm
      (by simp [primitiveMethods]) rfl (by rfl) (by intro o ho; cases ho) (by rfl) (by rfl),
      int_div_run]
    split
    · exact stepSpec_zeroDiv hm hk _
    · exact stepSpec_value hm hk (by simp [denM, isIntV])
  | intLt =>
    cases ha
    rename_i v vs hv hs
    cases hs
    obtain ⟨x, rfl⟩ := int_value hr
    obtain ⟨y, rfl⟩ := int_value hv
    rw [primitive_invoke (bid := "Integer#<") (k := Boot.integerId) hm
      (by simp [primitiveMethods]) rfl (by rfl) (by intro o ho; cases ho) (by rfl) (by rfl),
      int_lt_run]
    exact stepSpec_value hm hk (by simp [denM, isBoolV])
  | intToS =>
    cases ha
    obtain ⟨x, rfl⟩ := int_value hr
    rw [primitive_invoke (bid := "Integer#to_s") (k := Boot.integerId) hm
      (by simp [primitiveMethods]) rfl (by rfl) (by intro o ho; cases ho) (by rfl) (by rfl),
      int_to_s_run]
    exact stepSpec_string hm hk _ false
  | intEq =>
    cases ha
    rename_i v vs hv hs
    cases hs
    obtain ⟨x, rfl⟩ := int_value hr
    rw [primitive_invoke (bid := "Integer#==") (k := Boot.integerId) hm
      (by simp [primitiveMethods]) rfl (by rfl) (by intro o ho; cases ho)
      (int_eq_defer hm x v) (by rfl)]
    exact int_eq_step hm hk x v
  | strAdd =>
    cases ha
    rename_i v vs hv hs
    cases hs
    obtain ⟨o, s, rfl, hs⟩ := string_payload hm hr
    obtain ⟨p, t, rfl, ht⟩ := string_payload hm hv
    rw [primitive_invoke (bid := "String#+") (k := Boot.stringId) hm
      (by simp [primitiveMethods]) (string_class hm hr) (by rfl)
      (by intro k hk; cases hk; exact ⟨s, hs⟩) (by rfl) (by rfl), string_add_run]
    simp only [Builtins.runStrings, Builtins.binArg, Builtins.strPayload?, hs, ht]
    cases he : Builtins.concatEnc m.heap (.ref o) s (.ref p) t with
    | ok binary => exact stepSpec_string hm hk _ binary
    | error msg => trivial
  | notBool =>
    cases ha
    obtain ⟨b, rfl⟩ := bool_value hr
    cases b <;>
      rw [primitive_invoke (bid := "Object#!") hm
        (by simp [primitiveMethods, classOf]) rfl (by rfl)
        (by intro o ho; cases ho) (by rfl) (by rfl), bool_not_run] <;>
      exact stepSpec_value hm hk (by simp [denM, isBoolV])

#print axioms primitive_builtin
end Ratchet.Denote.Typed
