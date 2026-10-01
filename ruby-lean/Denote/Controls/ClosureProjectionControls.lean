import Denote.Rules.Closure.ProjectedReturn

/-! A hidden nil caller slot is retained, a fresh body local is removed, and an alias
to that removed local must not survive even when both body values were equal. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.ClosureProjectionControls
open RubyCore Ratchet Ratchet.Denote

private def outer : RubyCore.Frame :=
  { self := .nil, defmod := 0, kind := .toplevel, locals := [("x", .nil)] }
private def inner : RubyCore.Frame :=
  { self := .nil, defmod := 0, kind := .block, captured := some 0 }
private def caller (m : Machine) : Machine := { m with frames := #[outer], stack := [0] }
private def body (m : Machine) : Machine := pushMethodFrame (caller m) inner
private def written (m : Machine) : Machine := ((body m).setLocal "x" (.int 7)).setLocal "y" (.int 7)
private def bodyEnv : Env := [("x", .sameAs "y" .int), ("y", .int)]

private theorem body_read (m : Machine) (z : String) :
    (written m).getLocal z = if z = "x" ∨ z = "y" then .int 7 else .nil := by
  have hl : (body m).stack.headD 0 < (body m).frames.size := by change 1 < 2; decide
  by_cases hx : z = "x"
  · subst z
    rw [written, getLocal_setLocal_ne _ _ _ (by decide), getLocal_setLocal_self _ _ _ hl]
    simp
  · by_cases hy : z = "y"
    · subst z
      rw [written, getLocal_setLocal_self _ _ _ (by simpa using hl)]
      simp
    · rw [written, getLocal_setLocal_ne _ _ _ hy, getLocal_setLocal_ne _ _ _ hx]
      change (match (outer.locals.find? (·.1 == z)) with
        | some (_, v) => v | none => .nil) = _
      simp [outer, Ne.symm hx, hx, hy]

private theorem body_env (m : Machine) : EnvOk bodyEnv (written m) := by
  constructor
  · intro z τ hz
    by_cases hx : z = "x"
    · subst z
      have ht : τ = .sameAs "y" .int := by simpa [bodyEnv, envGet?] using hz.symm
      subst τ
      refine ⟨by rw [body_read]; simp [stripAlias, denM, isIntV], ?_⟩
      intro y ρ hy
      cases hy
      rw [body_read, body_read]; rfl
    · by_cases hy : z = "y"
      · subst z
        have ht : τ = .int := by simpa [bodyEnv, envGet?] using hz.symm
        subst τ
        exact ⟨by rw [body_read]; simp [stripAlias, denM, isIntV], by intros; contradiction⟩
      · simp [bodyEnv, envGet?, Ne.symm hx, Ne.symm hy] at hz
  · intro z hz
    have hx : z ≠ "x" := by intro he; subst z; simp [bodyEnv, envGet?] at hz
    have hy : z ≠ "y" := by intro he; subst z; simp [bodyEnv, envGet?] at hz
    rw [body_read]; simp [hx, hy]

theorem projected_caller (m : Machine) : EnvOk [("x", .int)] (popMethodFrame (written m)) := by
  have hd : FrameSlots ["x"] (caller m) := by
    intro x
    change ([("x", Value.nil)].any (·.1 == x)) = (["x"].contains x)
    simp only [List.any_cons, List.any_nil, List.contains_cons, List.contains_nil, Bool.or_false, BEq.comm]
  have he := closure_projected_env (m := caller m) (f := inner)
    ⟨by change ([0] : List FrameId) ≠ []; decide, by change 0 < 1; decide⟩ rfl rfl
    (captureSlots_of_frameSlots hd bodyEnv)
    (by intros; rfl)
    ((Framed_setLocal (body m) "x" (.int 7)).trans
      (Framed_setLocal ((body m).setLocal "x" (.int 7)) "y" (.int 7))) (body_env m) (by
        intro x τ hx _ v hv
        exact (denM_heap_only (m₁ := written m) (m₂ := popMethodFrame (written m)) (τ := stripAlias τ)
          (by
            obtain ⟨z, hz⟩ := envGet?_mem hx
            simp only [bodyEnv, List.mem_cons, List.not_mem_nil, or_false] at hz
            rcases hz with hz | hz <;> cases hz <;> rfl) rfl).mp hv)
  exact he

theorem retained_alias_rejected (m : Machine) :
    ¬ EnvOk [("x", .sameAs "y" .int)] (popMethodFrame (written m)) := by
  intro h
  have he := (h.1 "x" (.sameAs "y" .int) rfl).2 "y" .int rfl
  have hp := projected_caller m
  have hv := (hp.1 "x" .int rfl).1
  rw [he, hp.2 "y" rfl] at hv
  simp [stripAlias, denM, isIntV] at hv

theorem hidden_nil_is_a_slot (m : Machine) : ¬ FrameSlots [] (caller m) := by
  intro h
  have he := h "x"
  change true = false at he
  cases he

#print axioms projected_caller
#print axioms retained_alias_rejected
#print axioms hidden_nil_is_a_slot
end Ratchet.Denote.Typed.ClosureProjectionControls
