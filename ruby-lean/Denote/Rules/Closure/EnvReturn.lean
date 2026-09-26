import Denote.Rules.Closure.ReadReturn

/-! Project body types onto the caller's physical slots. New body locals disappear;
aliases are erased because their target may be one of those discarded locals. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

def captureEnv (names : List String) : Env → Env
  | [] => []
  | (x, τ) :: Γ => if names.contains x then (x, deAlias τ) :: captureEnv names Γ else captureEnv names Γ

/-- Only names typed in the body output need ownership classification. Untyped names
already read nil there, so hidden nil slots elsewhere need not be enumerated. -/
def CaptureSlots (names : List String) (Γ : Env) (m : Machine) : Prop :=
  ∀ x τ, envGet? Γ x = some τ → frameBinds m (m.stack.headD 0) x = names.contains x

theorem captureSlots_of_frameSlots {names : List String} {m : Machine}
    (h : FrameSlots names m) (Γ : Env) : CaptureSlots names Γ m := fun x _ _ => h x

theorem envGet?_captureEnv (names : List String) (Γ : Env) (x : String) :
    envGet? (captureEnv names Γ) x = if names.contains x then (envGet? Γ x).map deAlias else none := by
  induction Γ with
  | nil => simp [captureEnv, envGet?]
  | cons p Γ ih =>
    obtain ⟨y, τ⟩ := p
    by_cases hy : y = x
    · subst y
      cases hn : names.contains x <;>
        simp only [captureEnv, hn, Bool.false_eq_true, if_true, if_false,
          envGet?_cons_self, Option.map_some, ih]
    · by_cases hn : names.contains y = true
      · simp only [captureEnv, hn, if_true]
        rw [envGet?_cons_ne _ _ hy, envGet?_cons_ne _ _ hy]
        exact ih
      · simp only [captureEnv, hn, if_false]
        rw [envGet?_cons_ne _ _ hy]
        exact ih

theorem closure_pop_slots {m n : Machine} {f : RubyCore.Frame} {names : List String}
    (hl : FrameInRange m) (hd : FrameSlots names m) (h : Framed (pushMethodFrame m f) n) :
    FrameSlots names (popMethodFrame n) := by
  have hs : (popMethodFrame n).stack = m.stack := by simp [popMethodFrame, h.stack, pushMethodFrame]
  intro x
  change frameBinds (popMethodFrame n) ((popMethodFrame n).stack.headD 0) x = _
  rw [hs]
  exact (closure_saved_bindings h.frames _ hl.2 x).trans (hd x)

theorem closure_absent_read {m n : Machine} {f : RubyCore.Frame}
    (hl : FrameInRange m) (hu : RootUncaptured m) (h : Framed (pushMethodFrame m f) n)
    (x : String) (hx : frameBinds m (m.stack.headD 0) x = false) :
    (popMethodFrame n).getLocal x = .nil := by
  have hs : (popMethodFrame n).stack = m.stack := by simp [popMethodFrame, h.stack, pushMethodFrame]
  have hc : RootUncaptured (popMethodFrame n) := by
    change (n.frames.getD ((popMethodFrame n).stack.headD 0) default).captured = none
    rw [hs]
    have he := congrArg RubyCore.Frame.captured (closure_saved_metadata h.frames _ hl.2)
    exact he.trans hu
  have hb := (closure_saved_bindings h.frames _ hl.2 x).trans hx
  have hf := find?_eq_none_of_any_false _ _ hb
  rw [getLocal_uncaptured hc, hs]
  change (((n.frames.getD (m.stack.headD 0) default).locals.find? (·.1 == x)).map (·.2)).getD .nil = _
  rw [hf]; rfl

/-- Entry may bind fresh parameters/block locals, but must not shadow a caller slot.
Higher-order values retain their types through the supplied activation transport. -/
theorem closure_projected_env {m n : Machine} {f : RubyCore.Frame} {names : List String} {Γb : Env}
    (hl : FrameInRange m) (hu : RootUncaptured m) (hc : f.captured = some (m.stack.headD 0))
    (hd : CaptureSlots names Γb m)
    (hf : ∀ x, frameBinds m (m.stack.headD 0) x = true → f.locals.any (·.1 == x) = false)
    (h : Framed (pushMethodFrame m f) n) (he : EnvOk Γb n)
    (hmove : ∀ x τ, envGet? Γb x = some τ → names.contains x = true → ∀ v, denM (stripAlias τ) n v →
      denM (stripAlias τ) (popMethodFrame n) v) :
    EnvOk (captureEnv names Γb) (popMethodFrame n) := by
  constructor
  · intro x τ hx
    rw [envGet?_captureEnv] at hx
    by_cases hb : names.contains x = true
    · rw [hb] at hx
      cases hg : envGet? Γb x with
      | none => simp [hg] at hx
      | some σ =>
        have ht : deAlias σ = τ := by simpa [hg] using hx
        subst τ
        have hs : frameBinds m (m.stack.headD 0) x = true := (hd x σ hg).trans hb
        refine ⟨?_, fun y ρ hy => False.elim (deAlias_ne_sameAs σ y ρ hy)⟩
        rw [closure_bound_read hl hu hc h x (hf x hs) hs]
        exact denM_stripAlias.mpr (denM_deAlias.mpr
          (denM_stripAlias.mp (hmove x σ hg hb _ (he.1 x σ hg).1)))
    · simp only [if_neg hb] at hx
      cases hx
  · intro x hx
    by_cases hb : frameBinds m (m.stack.headD 0) x = true
    · have heq : envGet? Γb x = none := by
        cases hg : envGet? Γb x with
        | none => rfl
        | some σ =>
          have hn : names.contains x = true := (hd x σ hg).symm.trans hb
          rw [envGet?_captureEnv, hn, hg] at hx
          cases hx
      rw [closure_bound_read hl hu hc h x (hf x hb) hb]
      exact he.2 x heq
    · exact closure_absent_read hl hu h x (Bool.eq_false_iff.mpr hb)

#print axioms closure_pop_slots
#print axioms closure_projected_env
end Ratchet.Denote.Typed
