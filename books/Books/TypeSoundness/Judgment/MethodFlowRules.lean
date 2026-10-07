import Books.TypeSoundness.Judgment.MethodRules
import Books.TypeSoundness.Rules.Method.FlowCall
import Books.TypeSoundness.Rules.Method.FlowSequence

/-! Alias-aware method families and their constructor-derived semantic rules. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open Checker Checker.Soundness

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

theorem SemSafeCtxA.DMethodFlow.embed {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret τ : Ty}
      {Γ Γ' : Env} {facts : CallbackFacts} {e : Expr} :
      SemMethodBody κ I fr ps ret Γ e τ Γ' →
      SemMethodFlowBody κ I fr ps ret Γ facts e τ false Γ' .empty :=
  fun he => fun cb hp hr => .embed facts (he cb hp hr)

theorem SemSafeCtxA.DMethodFlow.intLit {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret : Ty}
      {Γ : Env} {facts : CallbackFacts} {n : Int} :
      SemMethodFlowBody κ I fr ps ret Γ facts (.int n) .int false Γ facts :=
  fun _ _ _ => .intLit facts n

theorem SemSafeCtxA.DMethodFlow.nilLit {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret : Ty}
      {Γ : Env} {facts : CallbackFacts} :
      SemMethodFlowBody κ I fr ps ret Γ facts .nil .nilT false Γ facts :=
  fun _ _ _ => .nilLit facts

theorem SemSafeCtxA.DMethodFlow.var {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret τ : Ty}
      {Γ : Env} {facts : CallbackFacts} {x : String} :
      envGet? Γ x = some τ → isAliasTy τ = false →
      SemMethodFlowBody κ I fr ps ret Γ facts (.var .lvar x) τ (facts.aliases.contains x) Γ facts :=
  fun hg ha => fun _ _ _ => .var facts hg ha

theorem SemSafeCtxA.DMethodFlow.vasgn {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret τ : Ty}
      {Γ Γ' : Env} {facts out : CallbackFacts} {e : Expr} {x : String} {callback : Bool} :
      SemMethodFlowBody κ I fr ps ret Γ facts e τ callback Γ' out →
      capStale x τ τ = false → isAliasTy τ = false →
      (∀ code, capStaleCtx x τ (callbackMethodCtx κ fr code) = false) →
      killClosOverSpine I x τ = I →
      SemMethodFlowBody κ I fr ps ret Γ facts (.vasgn .lvar x e) τ callback (envAfter Γ' x τ)
        (out.write x callback) :=
  fun he hc ha hk hi => fun cb hp hr => (he cb hp hr).vasgn hc ha (hk cb.code) hi

theorem SemSafeCtxA.DMethodFlow.sequence {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret τ : Ty}
      {Γ Γ' : Env} {facts out : CallbackFacts} {es : List Expr} {callback : Bool} :
      SemMethodFlowBodySeq κ I fr ps ret Γ facts es τ callback Γ' out →
      SemMethodFlowBody κ I fr ps ret Γ facts (.seq es) τ callback Γ' out :=
  fun he => fun cb hp hr => .sequence (he cb hp hr)

theorem SemSafeCtxA.DMethodFlow.call {κ : Ctx} {I : Ty} {fr : Frame} {σ τ ret : Ty} {Γ Γ₁ Γ₂ : Env}
      {facts mid out : CallbackFacts} {recv arg : Expr} {name : String} {callback : Bool} :
      SemMethodFlowBody κ I fr [σ] ret Γ facts recv τ true Γ₁ mid →
      SemMethodFlowBody κ I fr [σ] ret Γ₁ mid arg σ callback Γ₂ out →
      activationReturnB Γ₂ = true → plainArgB arg = true → nameFreeN κ name = true →
      procCallNameB name = true →
      SemMethodFlowBody κ I fr [σ] ret Γ facts (.send (some recv) name [arg] none) ret false Γ₂ out :=
  by
  intro he ha ht hplain hf hn Γc cb hp hr
  obtain ⟨param, hparams⟩ : ∃ param, cb.params = [(param, σ)] := by
    cases hps : cb.params with
    | nil => simp [hps] at hp
    | cons p tail =>
      rcases p with ⟨param, ty⟩
      simp only [hps, List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at hp
      exact ⟨param, by rw [hp.1, hp.2]⟩
  simpa only [hr] using (he cb hp hr).call (ha cb hp hr) hparams ht hplain hf hn

theorem SemSafeCtxA.DMethodFlowSeq.last {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret τ : Ty}
      {Γ Γ' : Env} {facts out : CallbackFacts} {e : Expr} {callback : Bool} :
      SemMethodFlowBody κ I fr ps ret Γ facts e τ callback Γ' out →
      SemMethodFlowBodySeq κ I fr ps ret Γ facts [e] τ callback Γ' out :=
  fun he => fun cb hp hr => .last (he cb hp hr)

theorem SemSafeCtxA.DMethodFlowSeq.cons {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret σ τ : Ty}
      {Γ Γ₁ Γ₂ : Env} {facts mid out : CallbackFacts} {e e' : Expr} {es : List Expr} {c c' : Bool} :
      SemMethodFlowBody κ I fr ps ret Γ facts e σ c Γ₁ mid →
      SemMethodFlowBodySeq κ I fr ps ret Γ₁ mid (e' :: es) τ c' Γ₂ out →
      SemMethodFlowBodySeq κ I fr ps ret Γ facts (e :: e' :: es) τ c' Γ₂ out :=
  fun he ht => fun cb hp hr => .cons (he cb hp hr) (ht cb hp hr)

end Checker.Soundness.Typed
