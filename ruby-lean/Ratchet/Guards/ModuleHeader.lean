import Ratchet.Guards.ClassHeader

/-! Module metadata carries no allocator permission. Body and singleton-method checking
are separate from publishing the executed header. -/
set_option autoImplicit false
namespace Ratchet

def moduleHeader (name : String) : Cls := { classHeader name with isModule := true }

def moduleHeaderCtx (κ : Ctx) (name : String) : Ctx :=
  { κ with pos := { κ.pos with classes := moduleHeader name :: κ.classes } }

theorem moduleHeader_ancestors (C : CTable) (name : String) :
    ancestors? (moduleHeader name :: C) name = some [name] := by
  simp [ancestors?, ancestorsUp, clsGet?, moduleHeader, classHeader, mixinAncestors?]

#guard (instClsGet? [moduleHeader "M"] "M").isNone
#guard isAAnswer [moduleHeader "M"] [] "Object" (.inst "M" .ivar0) == some false
#guard isAAnswer [classHeader "C"] [] "Object" (.inst "C" .ivar0) == some true
end Ratchet
