import Denote.Ty.Val

/-! A name-based alternative to knowing the receiver's payload. These names bypass
Proc/Hash/Class interception and the model's unmodeled singleton-method guard. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

def payloadSendNames : List String :=
  ["call", "()", "[]", "yield", "new", "escape", "quote", "union", "sqrt", "exp", "log"]

structure DirectSendName (name : String) : Prop where
  payload : name ∉ payloadSendNames
  singleton : ∀ cn, crubySingletonDefines cn name = false

def directSendNameB (name : String) : Bool :=
  !payloadSendNames.contains name && crubySingletonNames.all (fun p => !p.2.contains name)

theorem directSendNameB_sound {name : String} (h : directSendNameB name = true) :
    DirectSendName name := by
  simp only [directSendNameB, Bool.and_eq_true, Bool.not_eq_true'] at h
  refine ⟨by simpa using h.1, ?_⟩
  intro cn
  unfold crubySingletonDefines
  cases hf : crubySingletonNames.find? (·.1 == cn) with
  | none => rfl
  | some p =>
    have hp := List.all_eq_true.mp h.2 p (List.mem_of_find?_eq_some hf)
    simpa using hp

theorem DirectSendName.singletonShadow {name : String} (hn : DirectSendName name)
    (h : Heap) (recv : Value) : Interp.crubySingletonShadow h recv name = none := by
  have hz (ks : List ObjId) :
      ks.firstM (fun k => if crubySingletonDefines (className h k) name then some (className h k) else none) = none := by
    induction ks with
    | nil => rfl
    | cons k ks ih => simpa [List.firstM, hn.singleton] using ih
  cases recv <;> simp only [Interp.crubySingletonShadow]
  rename_i o
  cases (h.get o).payload <;> first | rfl | exact hz _

#print axioms directSendNameB_sound
end Ratchet.Denote
