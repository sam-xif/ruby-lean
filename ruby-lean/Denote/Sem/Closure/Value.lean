import Denote.Sem.Closure.Reify

/-! Captured environments and exact code in the callable value denotation. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

private theorem envToSpine_denFrom {m : Machine} (Γ : Env) (seen : List String)
    (h : ∀ x τ, envGet? Γ x = some τ → x ∉ seen → denM (stripAlias τ) m (m.getLocal x)) :
    denSpineFrom seen (envToSpine Γ) m m.getLocal := by
  induction Γ generalizing seen with
  | nil => simp [envToSpine, denSpineFrom]
  | cons p Γ ih =>
    obtain ⟨x, τ⟩ := p
    rw [envToSpine, denSpineFrom]
    refine ⟨?_, ih (x :: seen) ?_⟩
    · by_cases hx : x ∈ seen
      · exact Or.inl hx
      · exact Or.inr (h x τ (envGet?_cons_self _ _ _) hx)
    · intro y σ hy hn
      have hxy : x ≠ y := by intro he; subst y; exact hn (List.mem_cons_self)
      exact h y σ ((envGet?_cons_ne τ Γ hxy).trans hy)
        (fun hs => hn (List.mem_cons_of_mem x hs))

theorem EnvOk.capture {Γ : Env} {m : Machine} (h : EnvOk Γ m) :
    denSpine (envToSpine Γ) m m.getLocal :=
  envToSpine_denFrom Γ [] (fun x τ hx _ => (h.1 x τ hx).1)

theorem reified_den {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) (code : ClosureCode) :
    denM (.clos code (envToSpine Γ) (κ.selfTy.getD .never))
      (reifiedMachine m (toRubyParams code.params) code.locals (toRuby code.body) code.lam)
      (.ref m.heap.objs.size) := by
  rw [denM]
  refine ⟨_, reified_payload m _ _ _ _, ⟨rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
  · rw [reified_locals]
    exact denSpine_ext (reified_ext hm _ _ _ _) hm.env.capture
  · cases hs : κ.selfTy with
    | none => exact Or.inl rfl
    | some σ =>
      apply Or.inr
      rw [reified_self hm.frameInRange]
      exact denM_ext (reified_ext hm _ _ _ _) (by simpa only [SelfTyOk, hs, Option.getD] using hm.selfTy)

/-- A consumer recovers real code, never a table entry inferred from an unchecked index. -/
theorem closure_value_code {code : ClosureCode} {cap selfT : Ty} {m : Machine} {f : Value}
    (h : denM (.clos code cap selfT) m f) :
    ∃ cl, procClosure? m.heap f = some cl ∧ ClosureMatches code cl := by
  rw [denM] at h
  obtain ⟨cl, hp, hc, _⟩ := h
  exact ⟨cl, hp, hc⟩

#print axioms reified_den
#print axioms closure_value_code
end Ratchet.Denote
