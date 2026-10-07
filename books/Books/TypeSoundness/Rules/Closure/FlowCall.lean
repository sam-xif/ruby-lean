import Checker.Guards.ClosureFlow
import Books.TypeSoundness.Rules.Closure.TrackedCall
import Books.TypeSoundness.Conformance.Closure.Transport
import Books.TypeSoundness.Judgment.LocalFlow

/-! Static guards discharge the tracked call's activation and return transports.
Only output names need ownership classification; known bound slots may suffice. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem activationStable_transport {τ : Ty} {m n : Machine} {v : Value}
    (ht : activationStableB τ = true)
    (hfirst : ∀ σ, FirstOrder σ = true → ∀ w, denM σ m w → denM σ n w)
    (hproc : ProcPres m.heap n.heap) (hv : denM τ m v) : denM τ n v := by
  by_cases hf : FirstOrder τ = true
  · exact hfirst τ hf v hv
  · simp only [activationStableB, Bool.or_eq_true] at ht
    rcases ht with ht | htail
    · exact False.elim (hf ht)
    cases τ <;> try simp only at htail
    all_goals try cases htail
    rename_i code cap selfT
    cases cap <;> try simp only at htail
    all_goals try cases htail
    cases selfT <;> try simp only at htail
    all_goals try cases htail
    exact hproc.empty_capture_den hv

theorem activationStable_heap {τ : Ty} {m n : Machine} {v : Value}
    (ht : activationStableB τ = true) (hh : n.heap = m.heap) (hv : denM τ m v) : denM τ n v :=
  activationStable_transport ht (fun _ hf _ hv => (denM_heap_only hf hh.symm).mp hv)
    (by rw [hh]; exact .refl _) hv

theorem activationStable_framed {τ : Ty} {m n : Machine} {v : Value}
    (ht : activationStableB τ = true) (h : Framed m n) (hv : denM τ m v) : denM τ n v :=
  activationStable_transport ht h.firstOrder h.procs hv

theorem captureNames_sound {facts : LocalFacts} {Γ : Env} {m : Machine} {names : List String}
    (hf : LocalFactsOk facts m) (hn : facts.captureNames? Γ = some names) : CaptureSlots names Γ m := by
  cases hs : facts.slots with
  | some known =>
    simp only [LocalFacts.captureNames?, hs, Option.some.injEq] at hn
    subst names
    exact captureSlots_of_frameSlots (hf.slots _ hs) Γ
  | none =>
    simp only [LocalFacts.captureNames?, hs] at hn
    split at hn
    · rename_i hall
      cases hn
      intro x τ hx
      have hy : (x, τ) ∈ Γ := by
        induction Γ with
        | nil => cases hx
        | cons p Γ ih =>
          obtain ⟨y, σ⟩ := p
          by_cases he : y = x
          · subst y
            rw [envGet?_cons_self] at hx
            cases hx
            exact List.mem_cons_self
          · rw [envGet?_cons_ne _ _ he] at hx
            exact List.mem_cons_of_mem _ (ih (List.all_eq_true.mpr (fun p hp =>
              List.all_eq_true.mp hall p (List.mem_cons_of_mem _ hp))) hx)
      have hb := List.all_eq_true.mp hall (x, τ) hy
      exact (hf.bound x (by simpa using hb)).trans hb.symm
    · cases hn

theorem SemFlow.call {κ : Ctx} {Γ Γb : Env} {I τ cap selfT : Ty}
    {facts : LocalFacts} {names : List String} {code : ClosureCode} (name : String)
    (hc : closureMainB κ I = true) (ha : activationEnvB Γ = true)
    (ha' : activationEnvB Γb = true) (ht : FirstOrder τ = true)
    (hn : facts.captureNames? Γb = some names) (hx : name ∈ facts.currentProcs)
    (hv : envGet? Γ name = some (.clos code cap selfT)) (hfree : nameFreeN κ "call" = true)
    (hp : code.params = []) (hls : code.locals = []) (hl : code.lam = true)
    (hb : SemSafeCtxA (closureBodyCtx κ) Γ I code.body τ (closureBodyCtx κ) Γb I) :
    SemFlow κ Γ I facts (.send (some (.var .lvar name)) "call" [] none) τ false
      κ (captureEnv names Γb) I .unknown := by
  simp only [closureMainB, Bool.and_eq_true, Option.isNone_iff_eq_none,
    List.isEmpty_iff, and_assoc] at hc
  obtain ⟨hr, hw, hclass, hasm, hself, hblock, hconst, hi⟩ := hc
  have hin p (hp : p ∈ Γ) := List.all_eq_true.mp ha p hp
  have hout p (hp : p ∈ Γb) := List.all_eq_true.mp ha' p hp
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hin hout
  intro m hm hf
  have h := tracked_local_lambda_call hm hf (captureNames_sound hf hn) name hx hv hfree hp hls hl
    (ReframeFO.empty hi hself hblock hconst) hasm hr
    (fun x => (constGet?_empty (κ := κ.withFrame none) hconst x).trans
      (constGet?_empty hconst x).symm) ht
    (fun p hp => (hin p hp).2)
    (fun _ p hp _ hv => activationStable_heap (m := m) (hin p hp).1 rfl hv) hb
    (ReframeFO.empty hi hself hblock hconst) hw hclass
    (fun x => (constGet?_empty (κ := closureBodyCtx κ) hconst x).trans
      (constGet?_empty (κ := returnScopeCtx κ (closureBodyCtx κ)) hconst x).symm)
    (by
      intro n x σ hx _ v hv
      obtain ⟨y, hy⟩ := envGet?_mem hx
      exact denM_stripAlias.mpr
        (activationStable_heap (m := n) (hout (y, σ) hy).1 rfl (denM_stripAlias.mp hv)))
  exact h.withPost (fun _ n _ => ⟨.unknown n, by intro h; cases h⟩)

#print axioms SemFlow.call
#print axioms activationStable_framed
end Checker.Soundness.Typed
