import Denote.Rules.Closure.FrameReturn

/-! Nil-valued slots and absent slots have equal reads but different write ownership.
Saved binding domains survive real writes; value-level EnvOk cannot identify them. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.CaptureBindingControls
open RubyCore Ratchet Ratchet.Denote

private def outer (slots : List (String × Value)) : RubyCore.Frame :=
  { self := .nil, defmod := 0, kind := .toplevel, locals := slots }
private def inner : RubyCore.Frame :=
  { self := .nil, defmod := 0, kind := .block, captured := some 0 }
private def caller (m : Machine) (slots : List (String × Value)) : Machine :=
  { m with frames := #[outer slots], stack := [0] }
private def body (m : Machine) (slots : List (String × Value)) : Machine :=
  pushMethodFrame (caller m slots) inner

private def PriorFramePres (m n : Machine) : Prop :=
  m.frames.size ≤ n.frames.size ∧
  frameScope (n.frames.getD (n.stack.headD 0) default) =
    frameScope (m.frames.getD (m.stack.headD 0) default) ∧
  (RootUncaptured m → ∀ i, i < m.frames.size → i ≠ m.stack.headD 0 →
    n.frames.getD i default = m.frames.getD i default) ∧
  (∀ i, i < m.frames.size → i ≠ m.stack.headD 0 →
    savedFrame (n.frames.getD i default) = savedFrame (m.frames.getD i default)) ∧
  (CaptureLive m (some (m.stack.headD 0)) → ∀ i, i < m.frames.size →
    ¬ CapturePath m (some (m.stack.headD 0)) i →
      n.frames.getD i default = m.frames.getD i default)

theorem prior_allows_nil_slot (m : Machine) :
    PriorFramePres (body m []) (body m [("x", .nil)]) := by
  refine ⟨by change 2 ≤ 2; decide, rfl, ?_, ?_, ?_⟩
  · intro h
    change some 0 = none at h
    cases h
  · intro i hi hn
    have he : i = 0 := by change i < 2 at hi; change i ≠ 1 at hn; omega
    subst i
    rfl
  · intro _ i hi hn
    have he : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
    rcases he with rfl | rfl
    · exact False.elim (hn (.next (.here 0)))
    · exact False.elim (hn (.here 1))

theorem nil_slot_insertion_rejected (m : Machine) :
    ¬ FramePres (body m []) (body m [("x", .nil)]) := by
  intro h
  have he := h.bindings.saved 0 (by change 0 < 2; decide) (by change 0 ≠ 1; decide) "x"
  change true = false at he
  cases he

theorem captured_write_keeps_slots (m : Machine) :
    frameBinds ((body m [("x", .nil)]).setLocal "x" (.int 1)) 0 "x" = true ∧
    frameBinds ((body m []).setLocal "x" (.int 1)) 0 "x" = false ∧
    frameBinds ((body m []).setLocal "x" (.int 1)) 1 "x" = true := ⟨rfl, rfl, rfl⟩

theorem same_env_different_write_target (m : Machine) :
    EnvOk [] (caller m []) ∧ EnvOk [] (caller m [("x", .nil)]) ∧
    (popMethodFrame ((body m []).setLocal "x" (.int 1))).getLocal "x" = .nil ∧
    (popMethodFrame ((body m [("x", .nil)]).setLocal "x" (.int 1))).getLocal "x" = .int 1 := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · refine ⟨by simp [envGet?], fun x _ => ?_⟩
    rw [getLocal_uncaptured (by rfl)]
    rfl
  · refine ⟨by simp [envGet?], fun x _ => ?_⟩
    rw [getLocal_uncaptured (by rfl)]
    change (([("x", Value.nil)].find? (·.1 == x)).map (·.2)).getD .nil = .nil
    by_cases hx : "x" = x <;> simp [hx]

#print axioms prior_allows_nil_slot
#print axioms nil_slot_insertion_rejected
#print axioms captured_write_keeps_slots
#print axioms same_env_different_write_target
end Ratchet.Denote.Typed.CaptureBindingControls
