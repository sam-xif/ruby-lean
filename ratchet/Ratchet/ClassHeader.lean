import Ratchet.ClassCtx

/-! A pending header must not activate previously unknown ancestor/dispatch claims. -/
set_option autoImplicit false
namespace Ratchet

def unqualifiedClassB (name : String) : Bool := !name.toList.contains ':'

theorem unqualifiedClassB_ne_path {name : String} (hn : unqualifiedClassB name = true)
    (owner leaf : String) : name ≠ owner ++ "::" ++ leaf := by
  intro he
  subst name
  simp [unqualifiedClassB, String.toList_append, List.contains_append] at hn

structure HeaderTableFrame (C : CTable) (name : String) : Prop where
  newMiss : ∀ c ∈ C, smroGet? (classHeader name :: C) c.name "new" = none →
    smroGet? C c.name "new" = none
  chain : ∀ c ∈ C, ∀ ch, ancestors? (classHeader name :: C) c.name = some ch →
    ancestors? C c.name = some ch

def headerTableFrameB (C : CTable) (name : String) : Bool :=
  C.all fun c =>
    (!(smroGet? (classHeader name :: C) c.name "new").isNone ||
      (smroGet? C c.name "new").isNone) &&
    (ancestors? (classHeader name :: C) c.name == ancestors? C c.name)

theorem headerTableFrameB_sound {C : CTable} {name : String}
    (hf : headerTableFrameB C name = true) : HeaderTableFrame C name := by
  have rows := List.all_eq_true.mp hf
  refine ⟨?_, ?_⟩
  · intro c hc hn
    have h := (Bool.and_eq_true_iff.mp (rows c hc)).1
    simpa only [hn, Option.isNone_none, Bool.not_true, Bool.false_or,
      Option.isNone_iff_eq_none] using h
  · intro c hc ch hh
    have he := (Bool.and_eq_true_iff.mp (rows c hc)).2
    have eqn : ancestors? (classHeader name :: C) c.name = ancestors? C c.name :=
      by simpa only [beq_iff_eq] using he
    exact eqn.symm.trans hh

#guard headerTableFrameB [] "Point"
#guard headerTableFrameB [classHeader "Older"] "Point"
-- An unknown superclass becomes known: this needs a new proof, not table transport.
#guard !headerTableFrameB [{ classHeader "Child" with super? := some "Point" }] "Point"

#print axioms headerTableFrameB_sound
end Ratchet
