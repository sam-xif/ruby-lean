import Ratchet.Judgment.DMethodFlow
import Denote.Rules.Method.BodyBridge
import Denote.Rules.Method.FlowCall
import Denote.Rules.Method.FlowSequence

/-! Interpret staged method flow uniformly over all matching checked callbacks.
Embedded existing method derivations still pass through their registered bridge. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open Ratchet Ratchet.Denote

def SemMethodFlowBody (κ : Ctx) (I : Ty) (fr : Frame) (ps : List Ty) (ret : Ty)
    (Γm : Env) (facts : CallbackFacts) (e : Expr) (τ : Ty) (callback : Bool)
    (Γm' : Env) (out : CallbackFacts) : Prop :=
  ∀ {Γ : Env} (cb : CheckedCallback κ Γ I), cb.params.map (·.2) = ps → cb.ret = ret →
    SemMethodFlow cb fr Γm facts e τ callback Γm' out

def SemMethodFlowBodySeq (κ : Ctx) (I : Ty) (fr : Frame) (ps : List Ty) (ret : Ty)
    (Γm : Env) (facts : CallbackFacts) (es : List Expr) (τ : Ty) (callback : Bool)
    (Γm' : Env) (out : CallbackFacts) : Prop :=
  ∀ {Γ : Env} (cb : CheckedCallback κ Γ I), cb.params.map (·.2) = ps → cb.ret = ret →
    SemMethodFlowSeq cb fr Γm facts es τ callback Γm' out

theorem dmethodFlow_context {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret τ : Ty}
    {Γ Γ' : Env} {facts out : CallbackFacts} {e : Expr} {callback : Bool}
    (h : DMethodFlow κ I fr ps ret Γ facts e τ callback Γ' out) :
    SemMethodFlowBody κ I fr ps ret Γ facts e τ callback Γ' out := by
  refine DMethodFlow.rec
    (motive_1 := fun ps ret Γ facts e τ c Γ' out _ =>
      SemMethodFlowBody κ I fr ps ret Γ facts e τ c Γ' out)
    (motive_2 := fun ps ret Γ facts es τ c Γ' out _ =>
      SemMethodFlowBodySeq κ I fr ps ret Γ facts es τ c Γ' out)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro ps ret τ Γ Γ' facts e he Γc cb hp hr
    exact .embed facts (dmethod_context he cb hp hr)
  · intro ps ret Γ facts n Γc cb _ _
    exact .intLit facts n
  · intro ps ret Γ facts Γc cb _ _
    exact .nilLit facts
  · intro ps ret τ Γ facts x hg ha Γc cb _ _
    exact .var facts hg ha
  · intro ps ret τ Γ Γ' facts out e x c he hc ha hk hi ih Γc cb hp hr
    exact (ih cb hp hr).vasgn hc ha (hk cb.code) hi
  · intro ps ret τ Γ Γ' facts out es c he ih Γc cb hp hr
    exact .sequence (ih cb hp hr)
  · intro σ τ ret Γ Γ₁ Γ₂ facts mid out recv arg name c he ha ht hplain hf hn ihr iha Γc cb hp hr
    obtain ⟨param, hparams⟩ : ∃ param, cb.params = [(param, σ)] := by
      cases hps : cb.params with
      | nil => simp [hps] at hp
      | cons p tail =>
        rcases p with ⟨param, ty⟩
        simp only [hps, List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at hp
        exact ⟨param, by rw [hp.1, hp.2]⟩
    simpa only [hr] using (ihr cb hp hr).call (iha cb hp hr) hparams ht hplain hf hn
  · intro ps ret τ Γ Γ' facts out e c he ih Γc cb hp hr
    exact .last (ih cb hp hr)
  · intro ps ret σ τ Γ Γ₁ Γ₂ facts mid out e e' es c c' he ht ih ih' Γc cb hp hr
    exact .cons (ih cb hp hr) (ih' cb hp hr)

#print axioms dmethodFlow_context
end Ratchet.Denote.Typed
