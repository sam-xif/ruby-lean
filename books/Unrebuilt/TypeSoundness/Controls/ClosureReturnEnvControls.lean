import Books.TypeSoundness.Rules.Closure.ReturnState

/-! A parameter hides an unmentioned nil caller slot; another capture changes; a new
body-local alias target disappears. Return typing handles all three together. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.ClosureReturnEnvControls
open RubyCore Checker Checker.Soundness

private def outer : RubyCore.Frame :=
  { self := .nil, defmod := 0, kind := .toplevel, locals := [("x", .nil), ("y", .int 1)] }
private def inner : RubyCore.Frame :=
  { self := .nil, defmod := 0, kind := .block, captured := some 0, locals := [("x", .int 2)] }
private def caller (m : Machine) : Machine := { m with frames := #[outer], stack := [0] }
private def body (m : Machine) : Machine := pushMethodFrame (caller m) inner
private def written (m : Machine) : Machine :=
  (((body m).setLocal "x" (.int 9)).setLocal "y" (.int 7)).setLocal "z" (.int 7)
private def bodyEnv : Env := [("x", .int), ("y", .sameAs "z" .int), ("z", .int)]

private theorem body_read (m : Machine) (q : String) :
    (written m).getLocal q = if q = "x" then .int 9 else if q = "y" ∨ q = "z" then .int 7 else .nil := by
  have hl : (body m).stack.headD 0 < (body m).frames.size := by change 1 < 2; decide
  by_cases hx : q = "x"
  · subst q
    rw [written, getLocal_setLocal_ne _ _ _ (by decide), getLocal_setLocal_ne _ _ _ (by decide),
      getLocal_setLocal_self _ _ _ hl]
    simp
  · by_cases hy : q = "y"
    · subst q
      rw [written, getLocal_setLocal_ne _ _ _ (by decide),
        getLocal_setLocal_self _ _ _ (by simpa using hl)]
      simp
    · by_cases hz : q = "z"
      · subst q
        rw [written, getLocal_setLocal_self _ _ _ (by simpa using hl)]
        simp
      · rw [written, getLocal_setLocal_ne _ _ _ hz, getLocal_setLocal_ne _ _ _ hy,
          getLocal_setLocal_ne _ _ _ hx]
        simp [body, caller, pushMethodFrame, Machine.getLocal, Machine.getLocal.go,
          outer, inner, Array.getD, Ne.symm hx, Ne.symm hy, hx, hy, hz]

private theorem body_env (m : Machine) : EnvOk bodyEnv (written m) := by
  constructor
  · intro q τ hq
    by_cases hx : q = "x"
    · subst q
      have ht : τ = .int := by simpa [bodyEnv, envGet?] using hq.symm
      subst τ
      exact ⟨by rw [body_read]; simp [stripAlias, denM, isIntV], by intros; contradiction⟩
    · by_cases hy : q = "y"
      · subst q
        have ht : τ = .sameAs "z" .int := by simpa [bodyEnv, envGet?] using hq.symm
        subst τ
        refine ⟨by rw [body_read]; simp [stripAlias, denM, isIntV], ?_⟩
        intro z ρ hz
        cases hz
        rw [body_read, body_read]; rfl
      · by_cases hz : q = "z"
        · subst q
          have ht : τ = .int := by simpa [bodyEnv, envGet?] using hq.symm
          subst τ
          exact ⟨by rw [body_read]; simp [stripAlias, denM, isIntV], by intros; contradiction⟩
        · simp [bodyEnv, envGet?, Ne.symm hx, Ne.symm hy, Ne.symm hz] at hq
  · intro q hq
    have hx : q ≠ "x" := by intro h; subst q; simp [bodyEnv, envGet?] at hq
    have hy : q ≠ "y" := by intro h; subst q; simp [bodyEnv, envGet?] at hq
    have hz : q ≠ "z" := by intro h; subst q; simp [bodyEnv, envGet?] at hq
    rw [body_read]; simp [hx, hy, hz]

private theorem caller_env (m : Machine) : EnvOk [("y", .int)] (caller m) := by
  constructor
  · intro q τ hq
    have hq' : q = "y" ∧ τ = .int := by
      by_cases h : q = "y"
      · subst q; simpa [envGet?] using hq.symm
      · simp [envGet?, Ne.symm h] at hq
    obtain ⟨rfl, rfl⟩ := hq'
    exact ⟨by change denM .int (caller m) (.int 1); simp [denM, isIntV],
      by intros; contradiction⟩
  · intro q hq
    have hy : q ≠ "y" := by intro h; subst q; simp [envGet?] at hq
    rw [getLocal_uncaptured (m := caller m) rfl]
    by_cases hx : q = "x"
    · subst q; rfl
    · simp [caller, outer, Array.getD, Ne.symm hx, Ne.symm hy]

theorem returned_caller (m : Machine) : EnvOk [("y", .int)] (popMethodFrame (written m)) := by
  have hd : FrameSlots ["x", "y"] (caller m) := by
    intro q
    change ([("x", Value.nil), ("y", Value.int 1)].any (·.1 == q)) = (["x", "y"].contains q)
    simp only [List.any_cons, List.any_nil, List.contains_cons, List.contains_nil, Bool.or_false, BEq.comm]
  exact closure_return_env (m := caller m) (f := inner) (Γ := [("y", .int)])
    (shadow := ["x"]) (names := ["x", "y"]) (Γb := bodyEnv)
    ⟨by change [0] ≠ []; decide, by change 0 < 1; decide⟩ rfl rfl
    (captureSlots_of_frameSlots hd _)
    (by intro q; change ([("x", Value.int 2)].any (·.1 == q)) = (["x"].contains q)
        simp only [List.any_cons, List.any_nil, List.contains_cons, List.contains_nil, Bool.or_false, BEq.comm])
    (((Framed_setLocal (body m) "x" (.int 9)).trans
      (Framed_setLocal ((body m).setLocal "x" (.int 9)) "y" (.int 7))).trans
      (Framed_setLocal (((body m).setLocal "x" (.int 9)).setLocal "y" (.int 7)) "z" (.int 7)))
    (caller_env m) (body_env m)
    (by
      intro x τ hx v hv
      obtain ⟨q, hq⟩ := envGet?_mem hx
      simp only [List.mem_singleton] at hq
      cases hq
      exact (denM_heap_only (m₁ := caller m) (m₂ := popMethodFrame (written m)) rfl rfl).mp hv)
    (by
      intro x τ hx _ v hv
      obtain ⟨q, hq⟩ := envGet?_mem hx
      simp only [bodyEnv, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with hq | hq | hq <;> cases hq <;>
        exact (denM_heap_only (m₁ := written m) (m₂ := popMethodFrame (written m))
          (τ := .int) rfl rfl).mp hv)

theorem parameter_type_not_caller_type (m : Machine) :
    ¬ EnvOk [("x", .int), ("y", .int)] (popMethodFrame (written m)) := by
  intro h
  have hv := (h.1 "x" .int rfl).1
  rw [(returned_caller m).2 "x" rfl] at hv
  simp [stripAlias, denM, isIntV] at hv

#print axioms returned_caller
#print axioms parameter_type_not_caller_type
end Checker.Soundness.Typed.ClosureReturnEnvControls
