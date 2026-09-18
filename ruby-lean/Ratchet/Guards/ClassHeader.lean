import Ratchet.Guards.ClassCtx
import Ratchet.Guards.DeclLookupFrame

/-! A pending header must not activate previously unknown ancestor/dispatch claims. -/
set_option autoImplicit false
namespace Ratchet

def unqualifiedClassB (name : String) : Bool := !name.toList.contains ':'

theorem unqualifiedClassB_ne_path {name : String} (hn : unqualifiedClassB name = true)
    (owner leaf : String) : name ≠ owner ++ "::" ++ leaf := by
  intro he
  subst name
  simp [unqualifiedClassB, String.toList_append] at hn

abbrev HeaderTableFrame (C : CTable) (name : String) :=
  DeclLookupFrame C (classHeader name :: C)

def headerTableFrameB (C : CTable) (name : String) : Bool :=
  declLookupFrameB C (classHeader name :: C)

theorem headerTableFrameB_sound {C : CTable} {name : String}
    (hf : headerTableFrameB C name = true) : HeaderTableFrame C name :=
  declLookupFrameB_sound hf

#guard headerTableFrameB [] "Point"
#guard headerTableFrameB [classHeader "Older"] "Point"
-- An unknown superclass becomes known: this needs a new proof, not table transport.
#guard !headerTableFrameB [{ classHeader "Child" with super? := some "Point" }] "Point"

#print axioms headerTableFrameB_sound
end Ratchet
