import Denote.Rules.Bounded.BoundedExpr
import Denote.Rules.Bounded.BoundedPrimitive

/-! A recursive annotation is usable only within its body scope. Its semantic hypothesis
holds at strictly smaller execution bounds; closing the body discharges it by induction.
These interpretations are family fields in the registry, not raw syntactic premises. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open Ratchet Ratchet.Denote

def RecHyp (N : Nat) (κ : Ctx) (I : Ty) (s : RecScope) : Prop :=
  ∀ n, n < N → ∃ Γb, SemSafeCtxAt n κ s.params I s.decl.body s.ret κ Γb I

def SemRec (κ : Ctx) (I : Ty) (s : RecScope) (Γ : Env)
    (e : Ratchet.Expr) (τ : Ty) (Γ' : Env) : Prop :=
  ∀ N, RecHyp N κ I s → SemSafeCtxAt N κ Γ I e τ κ Γ' I

def SemRecAll (κ : Ctx) (I : Ty) (s : RecScope) (Γ : Env)
    (es : List Ratchet.Expr) (tys : List Ty) (Γ' : Env) : Prop :=
  ∀ N, RecHyp N κ I s → SemAllCtxAt N κ Γ I es tys κ Γ' I

theorem SemSafeCtxA.recursive {κ : Ctx} {I : Ty} {s : RecScope} {Γb : Env}
    (_hp : plainArgB s.decl.body = true)
    (hb : SemRec κ I s s.params s.decl.body s.ret Γb) :
    SemSafeCtxA κ s.params I s.decl.body s.ret κ Γb I := by
  apply semSafeCtxA_of_guarded
  intro N ih
  exact hb N (fun n hn => ⟨Γb, ih n hn⟩)

theorem SemSafeCtxA.DJudgeRec.embed {κ : Ctx} {I : Ty} {s : RecScope}
    {Γ Γ' : Env} {e : Ratchet.Expr} {τ : Ty}
    (h : SemSafeCtxA κ Γ I e τ κ Γ' I) : SemRec κ I s Γ e τ Γ' :=
  fun N _ => h.at N

theorem SemSafeCtxA.DJudgeRec.prim {κ : Ctx} {I : Ty} {s : RecScope}
    {Γ Γ₁ Γ₂ : Env} {recv : Ratchet.Expr} {name : String}
    {args : List Ratchet.Expr} {σ τ : Ty} {tys : List Ty}
    (hr : SemRec κ I s Γ recv σ Γ₁) (ha : SemRecAll κ I s Γ₁ args tys Γ₂)
    (hp : DPrim σ name tys τ) (hf : nameFreeN κ name = true)
    (hs : σ = .cls "String" →
      isANoOk κ.wholeCls (["String", "Comparable"] ++ rootAncestors) = true) :
    SemRec κ I s Γ (.send (some recv) name args none) τ Γ₂ :=
  fun N h => SemSafeCtxAt.prim (hr N h) (ha N h) hp hf hs

theorem SemSafeCtxA.DJudgeRec.if' {κ : Ctx} {I : Ty} {s : RecScope}
    {Γ Γc Γ₁ Γ₂ : Env} {c t e : Ratchet.Expr} {σ τ₁ τ₂ : Ty}
    (hc : SemRec κ I s Γ c σ Γc) (ht : SemRec κ I s Γc t τ₁ Γ₁)
    (he : SemRec κ I s Γc e τ₂ Γ₂) :
    SemRec κ I s Γ (.if' c t (some e)) (joinT τ₁ τ₂) (joinEnv Γ₁ Γ₂) :=
  fun N h => SemSafeCtxAt.if' (hc N h) (ht N h) (he N h)

theorem SemSafeCtxA.DJudgeRec.selfCall {κ : Ctx} {I : Ty} {s : RecScope}
    {Γ Γ' : Env} {args : List Ratchet.Expr}
    (ha : SemRecAll κ I s Γ args (s.params.map (·.2)) Γ')
    (hp : s.decl.params = s.params.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ s.params, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (ht : FirstOrder s.ret = true) (hd : s.decl ∈ κ.defs)
    (hframe : κ.withFrame (some ⟨"Object", "Object", s.decl.name⟩) = κ)
    (hm : κ.scope.runtimeMain = true) (hs : κ.selfTy = none) (hb : κ.blockTy = none)
    (hc : κ.consts = []) (has : κ.asms = []) (hi : FirstOrder I = true)
    (hg : ∀ p ∈ Γ', FirstOrder (stripAlias p.2) = true) :
    SemRec κ I s Γ (.send none s.decl.name args none) s.ret Γ' := by
  intro N h
  cases N with
  | zero => exact SemSafeCtxAt.zero
  | succ n =>
    obtain ⟨Γb, hbody⟩ := h n (Nat.lt_succ_self n)
    apply SemSafeCtxAt.callSig hp hps ht (Γb := Γb)
      (by simpa only [hframe] using hbody)
      ((ha (n + 1) h).mono (Nat.le_succ n)) hd hm hm hs hb hc has hi hg

theorem SemSafeCtxA.DJudgeRecAll.nil {κ : Ctx} {I : Ty} {s : RecScope} {Γ : Env} :
    SemRecAll κ I s Γ [] [] Γ := fun _ _ => .nil

theorem SemSafeCtxA.DJudgeRecAll.cons {κ : Ctx} {I : Ty} {s : RecScope}
    {Γ Γ₁ Γ₂ : Env} {e : Ratchet.Expr} {es : List Ratchet.Expr} {τ : Ty} {tys : List Ty}
    (he : SemRec κ I s Γ e τ Γ₁) (ht : SemRecAll κ I s Γ₁ es tys Γ₂)
    (hp : plainArgB e = true) : SemRecAll κ I s Γ (e :: es) (τ :: tys) Γ₂ :=
  fun N h => .cons (he N h) (ht N h) hp

#print axioms SemSafeCtxA.recursive
#print axioms SemSafeCtxA.DJudgeRec.selfCall
end Ratchet.Denote.Typed
