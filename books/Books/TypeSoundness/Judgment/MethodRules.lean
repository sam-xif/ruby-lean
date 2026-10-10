import Books.TypeSoundness.Checker.Judgment.DMethod
import Books.TypeSoundness.Rules.Method.BodyAssign
import Books.TypeSoundness.Rules.Method.BodyPrimitive

/-! Interpret a method signature uniformly over checked callbacks. A matching arrow
alone is insufficient: CheckedCallback supplies the real body and capture invariant. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open Checker Checker.Soundness

def SemMethodBody (κ : Ctx) (I : Ty) (fr : Frame) (ps : List Ty) (ret : Ty)
    (Γm : Env) (e : Expr) (τ : Ty) (Γm' : Env) : Prop :=
  ∀ {Γ : Env} (cb : CheckedCallback κ Γ I), cb.params.map (·.2) = ps → cb.ret = ret →
    SemMethod cb fr Γm e τ Γm'

def SemMethodBodyAll (κ : Ctx) (I : Ty) (fr : Frame) (ps : List Ty) (ret : Ty)
    (Γm : Env) (es : List Expr) (tys : List Ty) (Γm' : Env) : Prop :=
  ∀ {Γ : Env} (cb : CheckedCallback κ Γ I), cb.params.map (·.2) = ps → cb.ret = ret →
    SemMethodAll cb fr Γm es tys Γm'

def SemMethodBodySeq (κ : Ctx) (I : Ty) (fr : Frame) (ps : List Ty) (ret : Ty)
    (Γm : Env) (es : List Expr) (τ : Ty) (Γm' : Env) : Prop :=
  ∀ {Γ : Env} (cb : CheckedCallback κ Γ I), cb.params.map (·.2) = ps → cb.ret = ret →
    SemMethodSeq cb fr Γm es τ Γm'

theorem SemSafeCtxA.DMethod.ordinary {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret τ : Ty}
    {Γ Γ' : Env} {e : Expr}
    (h : ∀ code, SemSafeCtxA (callbackMethodCtx κ fr code) Γ I e τ (callbackMethodCtx κ fr code) Γ' I) :
    SemMethodBody κ I fr ps ret Γ e τ Γ' := fun cb _ _ => .ordinary (h cb.code)

theorem SemSafeCtxA.DMethod.vasgn {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret τ : Ty}
    {Γ Γ' : Env} {e : Expr} {x : String} (h : SemMethodBody κ I fr ps ret Γ e τ Γ')
    (hc : capStale x τ τ = false) (ha : isAliasTy τ = false)
    (hk : ∀ code, capStaleCtx x τ (callbackMethodCtx κ fr code) = false)
    (hi : killClosOverSpine I x τ = I) :
    SemMethodBody κ I fr ps ret Γ (.vasgn .lvar x e) τ (envAfter Γ' x τ) :=
  fun cb hp hr => (h cb hp hr).vasgn hc ha (hk cb.code) hi

theorem SemSafeCtxA.DMethod.sequence {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret τ : Ty}
    {Γ Γ' : Env} {es : List Expr} (h : SemMethodBodySeq κ I fr ps ret Γ es τ Γ') :
    SemMethodBody κ I fr ps ret Γ (.seq es) τ Γ' := fun cb hp hr => .sequence (h cb hp hr)

theorem SemSafeCtxA.DMethod.prim {κ : Ctx} {I : Ty} {fr : Frame} {ps tys : List Ty} {ret σ τ : Ty}
    {Γ Γ₁ Γ₂ : Env} {recv : Expr} {name : String} {args : List Expr}
    (hr : SemMethodBody κ I fr ps ret Γ recv σ Γ₁) (ha : SemMethodBodyAll κ I fr ps ret Γ₁ args tys Γ₂)
    (hp : DPrim σ name tys τ) (hf : nameFreeN κ name = true)
    (hs : σ = .cls "String" → isANoOk κ.wholeCls (["String", "Comparable"] ++ rootAncestors) = true) :
    SemMethodBody κ I fr ps ret Γ (.send (some recv) name args none) τ Γ₂ :=
  fun cb hps hret => (hr cb hps hret).prim (ha cb hps hret) hp hf hs

theorem SemSafeCtxA.DMethod.yieldOne {κ : Ctx} {I : Ty} {fr : Frame} {σ ret : Ty}
    {Γ Γ' : Env} {arg : Expr} (h : SemMethodBody κ I fr [σ] ret Γ arg σ Γ')
    (ht : activationReturnB Γ' = true) (hplain : plainArgB arg = true) :
    SemMethodBody κ I fr [σ] ret Γ (.yield' [arg]) ret Γ' := by
  intro Γc cb hp hr
  obtain ⟨name, hparams⟩ : ∃ name, cb.params = [(name, σ)] := by
    cases hps : cb.params with
    | nil => simp [hps] at hp
    | cons p tail =>
      rcases p with ⟨name, ty⟩
      simp only [hps, List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at hp
      exact ⟨name, by rw [hp.1, hp.2]⟩
  have plain : Plain arg := by cases arg <;> simp_all [plainArgB, Plain]
  simpa only [hr] using (h cb hp hr).yieldOne hparams ht plain

theorem SemSafeCtxA.DMethodAll.nil {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret : Ty} {Γ : Env} :
    SemMethodBodyAll κ I fr ps ret Γ [] [] Γ := fun _ _ _ => .nil

theorem SemSafeCtxA.DMethodAll.cons {κ : Ctx} {I : Ty} {fr : Frame} {ps tys : List Ty} {ret τ : Ty}
    {Γ Γ₁ Γ₂ : Env} {e : Expr} {es : List Expr}
    (h : SemMethodBody κ I fr ps ret Γ e τ Γ₁) (hs : SemMethodBodyAll κ I fr ps ret Γ₁ es tys Γ₂)
    (hp : plainArgB e = true) : SemMethodBodyAll κ I fr ps ret Γ (e :: es) (τ :: tys) Γ₂ :=
  fun cb hps hret => .cons (h cb hps hret) (hs cb hps hret) hp

theorem SemSafeCtxA.DMethodSeq.last {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret τ : Ty}
    {Γ Γ' : Env} {e : Expr} (h : SemMethodBody κ I fr ps ret Γ e τ Γ') :
    SemMethodBodySeq κ I fr ps ret Γ [e] τ Γ' := fun cb hp hr => .last (h cb hp hr)

theorem SemSafeCtxA.DMethodSeq.cons {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret σ τ : Ty}
    {Γ Γ₁ Γ₂ : Env} {e e' : Expr} {es : List Expr}
    (h : SemMethodBody κ I fr ps ret Γ e σ Γ₁) (hs : SemMethodBodySeq κ I fr ps ret Γ₁ (e' :: es) τ Γ₂) :
    SemMethodBodySeq κ I fr ps ret Γ (e :: e' :: es) τ Γ₂ :=
  fun cb hp hr => .cons (h cb hp hr) (hs cb hp hr)

#print axioms SemSafeCtxA.DMethod.yieldOne
#print axioms SemSafeCtxA.DMethod.prim
end Checker.Soundness.Typed
