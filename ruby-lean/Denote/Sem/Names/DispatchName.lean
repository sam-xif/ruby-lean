import Denote.Ty.Val

/-! A name-based alternative to knowing the receiver's payload. These names avoid
payload interception before ordinary lookup dispatch. Native methods preceding a
resolved owner are checked separately; a user method at the owner wins. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

def payloadSendNames : List String :=
  ["call", "()", "[]", "yield", "new", "escape", "quote", "union", "sqrt", "exp", "log"]

structure DirectSendName (name : String) : Prop where
  payload : name ∉ payloadSendNames

def directSendNameB (name : String) : Bool :=
  !payloadSendNames.contains name

theorem directSendNameB_sound {name : String} (h : directSendNameB name = true) :
    DirectSendName name := ⟨by simpa [directSendNameB] using h⟩

#print axioms directSendNameB_sound
end Ratchet.Denote
