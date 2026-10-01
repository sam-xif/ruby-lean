import Denote.Rules.Closure.EnvReturn
import Denote.Rules.Closure.ShadowReturn

/-! Return typing distinguishes a parameter's final type from the type of the caller
slot it hides. Ownership classification is needed only outside the shadowed names. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem envGet?_append (a b : Env) (x : String) :
    envGet? (a ++ b) x = (envGet? a x).orElse (fun _ => envGet? b x) := by
  induction a with
  | nil => rfl
  | cons p a ih =>
    obtain ⟨y, τ⟩ := p
    by_cases hy : y = x
    · subst y
      rw [List.cons_append, envGet?_cons_self, envGet?_cons_self]
      rfl
    · rw [List.cons_append, envGet?_cons_ne _ _ hy, envGet?_cons_ne _ _ hy]
      exact ih

theorem envGet?_withoutNames (names : List String) (Γ : Env) (x : String) :
    envGet? (withoutNames names Γ) x = if names.contains x then none else envGet? Γ x := by
  induction Γ with
  | nil => simp [withoutNames, envGet?]
  | cons p Γ ih =>
    obtain ⟨y, τ⟩ := p
    by_cases hy : y = x
    · subst y
      cases hn : names.contains x <;>
        simp only [withoutNames, hn, Bool.false_eq_true, if_true, if_false, envGet?_cons_self, ih, hn]
    · by_cases hn : names.contains y = true
      · simp only [withoutNames, hn, if_true, envGet?_cons_ne _ _ hy]
        exact ih
      · simp only [withoutNames, hn, Bool.false_eq_true, if_false, envGet?_cons_ne _ _ hy]
        exact ih

theorem envGet?_closureReturnEnv (shadow names : List String) (Γ Γb : Env) (x : String) :
    envGet? (closureReturnEnv shadow names Γ Γb) x =
      if shadow.contains x then (envGet? Γ x).map deAlias
      else if names.contains x then (envGet? Γb x).map deAlias else none := by
  rw [closureReturnEnv, envGet?_append, envGet?_captureEnv, envGet?_captureEnv,
    envGet?_withoutNames]
  cases hs : shadow.contains x <;> cases hn : names.contains x <;>
    cases hg : envGet? Γ x <;> rfl

/-- Environment merging depends on three proved read relations, independent of
how many inert activations stand between the block and its captured caller. -/
theorem closure_return_env_of_reads {m n out : Machine}
    {shadow names : List String} {Γ Γb : Env}
    (hd : CaptureSlots names (withoutNames shadow Γb) m)
    (hshadow : ∀ x, shadow.contains x = true → out.getLocal x = m.getLocal x)
    (hbound : ∀ x, shadow.contains x = false → frameBinds m (m.stack.headD 0) x = true →
      out.getLocal x = n.getLocal x)
    (habsent : ∀ x, frameBinds m (m.stack.headD 0) x = false → out.getLocal x = .nil)
    (he : EnvOk Γ m) (hb : EnvOk Γb n)
    (hbefore : ∀ x τ, envGet? Γ x = some τ → ∀ v, denM (stripAlias τ) m v →
      denM (stripAlias τ) out v)
    (hafter : ∀ x τ, envGet? Γb x = some τ → names.contains x = true → ∀ v,
      denM (stripAlias τ) n v → denM (stripAlias τ) out v) :
    EnvOk (closureReturnEnv shadow names Γ Γb) out := by
  constructor
  · intro x τ hx
    rw [envGet?_closureReturnEnv] at hx
    by_cases hs : shadow.contains x = true
    · rw [hs] at hx
      cases hg : envGet? Γ x with
      | none => simp [hg] at hx
      | some σ =>
        have ht : deAlias σ = τ := by simpa [hg] using hx
        subst τ
        refine ⟨?_, fun y ρ hy => False.elim (deAlias_ne_sameAs σ y ρ hy)⟩
        rw [hshadow x hs]
        exact denM_stripAlias.mpr (denM_deAlias.mpr
          (denM_stripAlias.mp (hbefore x σ hg _ (he.1 x σ hg).1)))
    · have hs0 := Bool.eq_false_iff.mpr hs
      rw [hs0] at hx
      by_cases hn : names.contains x = true
      · rw [hn] at hx
        cases hg : envGet? Γb x with
        | none => simp [hg] at hx
        | some σ =>
          have ht : deAlias σ = τ := by simpa [hg] using hx
          subst τ
          have hslot : frameBinds m (m.stack.headD 0) x = true :=
            (hd x σ (by rw [envGet?_withoutNames, hs0]; exact hg)).trans hn
          refine ⟨?_, fun y ρ hy => False.elim (deAlias_ne_sameAs σ y ρ hy)⟩
          rw [hbound x hs0 hslot]
          exact denM_stripAlias.mpr (denM_deAlias.mpr
            (denM_stripAlias.mp (hafter x σ hg hn _ (hb.1 x σ hg).1)))
      · simp only [if_neg hn] at hx
        cases hx
  · intro x hx
    rw [envGet?_closureReturnEnv] at hx
    by_cases hs : shadow.contains x = true
    · have hg : envGet? Γ x = none := by
        cases hg : envGet? Γ x with
        | none => rfl
        | some σ => rw [hs, hg] at hx; cases hx
      rw [hshadow x hs]
      exact he.2 x hg
    · have hs0 := Bool.eq_false_iff.mpr hs
      by_cases hslot : frameBinds m (m.stack.headD 0) x = true
      · have hg : envGet? Γb x = none := by
          cases hg : envGet? Γb x with
          | none => rfl
          | some σ =>
            have hn : names.contains x = true :=
              (hd x σ (by rw [envGet?_withoutNames, hs0]; exact hg)).symm.trans hslot
            rw [hs0, hn, hg] at hx
            cases hx
        rw [hbound x hs0 hslot]
        exact hb.2 x hg
      · exact habsent x (Bool.eq_false_iff.mpr hslot)
theorem closure_return_env {m n : Machine} {f : RubyCore.Frame}
    {shadow names : List String} {Γ Γb : Env}
    (hl : FrameInRange m) (hu : RootUncaptured m) (hc : f.captured = some (m.stack.headD 0))
    (hd : CaptureSlots names (withoutNames shadow Γb) m)
    (hf : ∀ x, f.locals.any (·.1 == x) = shadow.contains x)
    (h : Framed (pushMethodFrame m f) n) (he : EnvOk Γ m) (hb : EnvOk Γb n)
    (hbefore : ∀ x τ, envGet? Γ x = some τ → ∀ v, denM (stripAlias τ) m v →
      denM (stripAlias τ) (popMethodFrame n) v)
    (hafter : ∀ x τ, envGet? Γb x = some τ → names.contains x = true → ∀ v,
      denM (stripAlias τ) n v → denM (stripAlias τ) (popMethodFrame n) v) :
    EnvOk (closureReturnEnv shadow names Γ Γb) (popMethodFrame n) :=
  closure_return_env_of_reads hd
    (fun x hs => closure_shadowed_read hl hu hc h x ((hf x).trans hs))
    (fun x hs hx => closure_bound_read hl hu hc h x ((hf x).trans hs) hx)
    (fun x hx => closure_absent_read hl hu h x hx) he hb hbefore hafter

#print axioms closure_return_env_of_reads
#print axioms closure_return_env
end Ratchet.Denote.Typed
