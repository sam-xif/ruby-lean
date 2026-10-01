import Ratchet.Guards.ClassHeader

/-! Module metadata carries no allocator permission. Body and singleton-method checking
are separate from publishing the executed header. -/
set_option autoImplicit false
namespace Ratchet

def moduleHeader (name : String) : Cls := { classHeader name with isModule := true }

/-- Class and module bodies share lexical activation; neither scope grants allocation. -/
abbrev moduleBodyCtx (κ : Ctx) (name : String) : Ctx := classBodyCtx κ name

def moduleHeaderCtx (κ : Ctx) (name : String) : Ctx :=
  { κ with pos := { κ.pos with classes := moduleHeader name :: κ.classes } }

abbrev ModuleHeaderFrame (C : CTable) (name : String) :=
  DeclLookupFrame C (moduleHeader name :: C)

def moduleHeaderFrameB (C : CTable) (name : String) : Bool :=
  declLookupFrameB C (moduleHeader name :: C)

theorem moduleHeaderFrameB_sound {C : CTable} {name : String}
    (hf : moduleHeaderFrameB C name = true) : ModuleHeaderFrame C name :=
  declLookupFrameB_sound hf

theorem moduleHeader_ancestors (C : CTable) (name : String) :
    ancestors? (moduleHeader name :: C) name = some [name] := by
  simp [ancestors?, ancestorsUp, clsGet?, moduleHeader, classHeader, mixinAncestors?]

#guard (instClsGet? [moduleHeader "M"] "M").isNone
#guard isAAnswer [moduleHeader "M"] [] "Object" (.inst "M" .ivar0) == some false
#guard isAAnswer [classHeader "C"] [] "Object" (.inst "C" .ivar0) == some true
#guard moduleHeaderFrameB [classHeader "Older", moduleHeader "Existing"] "More"
#guard !moduleHeaderFrameB [{ classHeader "Waiting" with super? := some "More" }] "More"
end Ratchet
