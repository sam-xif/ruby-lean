import Ratchet.ClassHeader

/-! Publish only the executed subclass header. Finite table comparisons establish the
new chain and frame old claims; no method annotation or body is admitted by these guards. -/
set_option autoImplicit false
namespace Ratchet

def subclassHeader (name parent : String) : Cls := { classHeader name with super? := some parent }

def subclassHeaderCtx (κ : Ctx) (name parent : String) : Ctx :=
  { κ with pos := { κ.pos with
    classes := subclassHeader name parent :: κ.classes
    plainAlloc := name :: κ.pos.plainAlloc } }

def subclassHeaderFrameB (C : CTable) (name parent : String) : Bool :=
  declLookupFrameB C (subclassHeader name parent :: C) &&
    match ancestors? C parent with
    | none => false
    | some ns => ancestors? (subclassHeader name parent :: C) name == some (name :: ns)

structure SubclassHeaderFrame (C : CTable) (name parent : String) : Prop where
  old : DeclLookupFrame C (subclassHeader name parent :: C)
  chain : ∃ ns, ancestors? C parent = some ns ∧
    ancestors? (subclassHeader name parent :: C) name = some (name :: ns)

theorem subclassHeaderFrameB_sound {C : CTable} {name parent : String}
    (hb : subclassHeaderFrameB C name parent = true) : SubclassHeaderFrame C name parent := by
  obtain ⟨hold, hchain⟩ := Bool.and_eq_true_iff.mp hb
  refine ⟨declLookupFrameB_sound hold, ?_⟩
  cases he : ancestors? C parent with
  | none => simp only [he, Bool.false_eq_true] at hchain
  | some ns => exact ⟨ns, rfl, by simpa only [he, beq_iff_eq] using hchain⟩

#guard subclassHeaderFrameB [classHeader "Carrier"] "Relay" "Carrier"
#guard subclassHeaderFrameB [subclassHeader "Relay" "Carrier", classHeader "Carrier"] "Leaf" "Relay"
#guard !subclassHeaderFrameB [classHeader "Carrier"] "Relay" "Unknown"
#guard !subclassHeaderFrameB [subclassHeader "Waiting" "Relay", classHeader "Carrier"] "Relay" "Carrier"
#guard !subclassHeaderFrameB [classHeader "Carrier"] "Carrier" "Carrier"

#print axioms subclassHeaderFrameB_sound
end Ratchet
