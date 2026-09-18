import Ratchet.Static.All

/-! Preserve the claims made by old class names when the positive table grows. -/
set_option autoImplicit false
namespace Ratchet

structure DeclLookupFrame (C C' : CTable) : Prop where
  newMiss : ∀ c ∈ C, smroGet? C' c.name "new" = none → smroGet? C c.name "new" = none
  chain : ∀ c ∈ C, ∀ ch, ancestors? C' c.name = some ch → ancestors? C c.name = some ch

def declLookupFrameB (C C' : CTable) : Bool :=
  C.all fun c =>
    (!(smroGet? C' c.name "new").isNone || (smroGet? C c.name "new").isNone) &&
    (ancestors? C' c.name == ancestors? C c.name)

theorem declLookupFrameB_sound {C C' : CTable} (hf : declLookupFrameB C C' = true) :
    DeclLookupFrame C C' := by
  have rows := List.all_eq_true.mp hf
  refine ⟨?_, ?_⟩
  · intro c hc hn
    have h := (Bool.and_eq_true_iff.mp (rows c hc)).1
    simpa only [hn, Option.isNone_none, Bool.not_true, Bool.false_or,
      Option.isNone_iff_eq_none] using h
  · intro c hc ch hh
    have he := (Bool.and_eq_true_iff.mp (rows c hc)).2
    have eqn : ancestors? C' c.name = ancestors? C c.name := by simpa only [beq_iff_eq] using he
    exact eqn.symm.trans hh

end Ratchet
