import Denote.Typed.Run

/-! Context-indexed answer safety, before admitting definitions. Incoming and outgoing
contexts are separate: a declaration installs a method, and a method body has its own frame.
The current `SemSafeA` is exactly the `ctx0`/`ivar0` specialization, not a weaker contract.
`RunSpec.bindSpec` supplies continuation composition without fixing the context to `ctx0`.

This is infrastructure, not a declaration rule. A future definition rule must check its
body against the annotations, including uncalled bodies; a signature alone is not evidence.
-/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

def SemSafeCtxA (κ : Ctx) (Γ : Env) (I : Ty) (e : Ratchet.Expr) (τ : Ty)
    (κ' : Ctx) (Γ' : Env) (I' : Ty) : Prop :=
  ∀ m, StateOk κ Γ I m → RunSpec m (evalFrom m e) Γ' τ κ' I'

theorem semSafeA_iff_context {Γ Γ' : Env} {e : Ratchet.Expr} {τ : Ty} :
    SemSafeA Γ e τ Γ' ↔ SemSafeCtxA ctx0 Γ .ivar0 e τ ctx0 Γ' .ivar0 :=
  ⟨fun h _ hm => h.runSpec hm, semSafe_of_runSpec⟩

theorem SemSafeCtxA.closed {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {e : Ratchet.Expr}
    (h : SemSafeCtxA κ Γ I e τ κ' Γ' I') {m : Machine} (hm : StateOk κ Γ I m) :
    StuckFree m e := (h m hm).1

/-- A one-step value rule transports its actual state, not a fixed top-level environment. -/
theorem SemSafeCtxA.leaf {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {e : Ratchet.Expr}
    (h : ∀ m, StateOk κ Γ I m → ∃ n v,
      Interp.stepFn (evalFrom m e) = .next (deliverA (.val v) n []) ∧
      ResultOk m Γ' τ (.val v) n κ' I') : SemSafeCtxA κ Γ I e τ κ' Γ' I' := by
  intro m hm
  obtain ⟨n, v, hs, hr⟩ := h m hm
  exact RunSpec.step (answerPoint_evalFrom _ _) hs (RunSpec.answer hr)

theorem SemSafeCtxA.intLit {κ : Ctx} {Γ : Env} {I : Ty} {n : Int} :
    SemSafeCtxA κ Γ I (.int n) .int κ Γ I := by
  apply SemSafeCtxA.leaf
  intro m hm
  exact ⟨m, .int n, rfl, .refl m, by simp [AnsOk, denM, isIntV], fun _ _ => hm⟩

theorem SemSafeCtxA.var {κ : Ctx} {Γ : Env} {I τ : Ty} {x : String}
    (hg : envGet? Γ x = some τ) (ha : isAliasTy τ = false) :
    SemSafeCtxA κ Γ I (.var .lvar x) τ κ Γ I := by
  apply SemSafeCtxA.leaf
  intro m hm
  exact ⟨m, m.getLocal x, stepFn_var m x, .refl m,
    denM_getLocal hm hg ha, fun _ _ => hm⟩

/-- A write may invalidate captured ivar types. `capStaleCtx` also protects the context's
self, block, and constant types; unlike at `ctx0`, that premise is not automatically false. -/
theorem SemSafeCtxA.vasgn {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty}
    {e : Ratchet.Expr} {x : String}
    (h : SemSafeCtxA κ Γ I e τ κ' Γ' I')
    (hc : capStale x τ τ = false) (ha : isAliasTy τ = false)
    (hk : capStaleCtx x τ κ' = false) :
    SemSafeCtxA κ Γ I (.vasgn .lvar x e) τ κ' (envAfter Γ' x τ)
      (killClosOverSpine I' x τ) := by
  intro m hm
  apply RunSpec.step (answerPoint_evalFrom _ _)
    (show Interp.stepFn (evalFrom m (.vasgn .lvar x e)) =
      .next (pushK [.asgnK .lvar x] (evalFrom m e)) from rfl)
  apply (h m hm).bindSpec (catchFree_asgnK x)
  intro a n hr
  cases a with
  | val v =>
    let base := reCtl n (.value v) []
    have hn : StateOk κ' Γ' I' base := StateOk_reCtl (hr.2.2 v rfl) _ _
    have hd : denM τ base v := denM_reCtl.mpr hr.2.1
    have hout : StateOk κ' (envAfter Γ' x τ) (killClosOverSpine I' x τ)
        (base.setLocal x v) :=
      StateOk_setLocal hn hd hc hk (ρ := τ)
        (by cases τ <;> simp_all [stripAlias, isAliasTy])
        (by intro y σ hy; rw [hy] at ha; simp [isAliasTy] at ha)
    have hresult : ResultOk m (envAfter Γ' x τ) τ (.val v) (base.setLocal x v)
        κ' (killClosOverSpine I' x τ) :=
      ⟨hr.1.trans ((Framed_reCtl n _ []).trans (Framed_setLocal base x v)), denM_setLocal hd hc hd,
        fun _ _ => hout⟩
    apply RunSpec.step (by rfl)
      (show Interp.stepFn (deliverA (.val v) n [.asgnK .lvar x]) =
        .next (deliverA (.val v) (base.setLocal x v) []) from rfl)
    exact RunSpec.answer hresult
  | esc j =>
    apply RunSpec.step (by rfl)
      (show Interp.stepFn (deliverA (.esc j) n [.asgnK .lvar x]) =
        .next (deliverA (.esc j) n []) from by cases j <;> rfl)
    exact RunSpec.answer ⟨hr.1, hr.2.1, fun _ hv => by cases hv⟩

/-- Sequential composition consumes the first expression's *outgoing* context, locals,
and ivar spine. There is no obligation to retain its incoming declaration table. -/
theorem SemSafeCtxA.seq {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ σ τ : Ty}
    {e₁ e₂ : Ratchet.Expr} (h₁ : SemSafeCtxA κ Γ I e₁ σ κ₁ Γ₁ I₁)
    (h₂ : SemSafeCtxA κ₁ Γ₁ I₁ e₂ τ κ₂ Γ₂ I₂) :
    SemSafeCtxA κ Γ I (.seq [e₁, e₂]) τ κ₂ Γ₂ I₂ := by
  have hcf (es : List RubyCore.Expr) : RubyCore.Proof.CatchFree [.seqK es] := by
    intro k hk tag
    simp only [List.mem_singleton] at hk
    subst hk
    simp
  have hesc (es : List RubyCore.Expr) (n : Machine) (j : Jump) :
      Interp.stepFn (deliverA (.esc j) n [.seqK es]) =
        .next (deliverA (.esc j) n []) := by cases j <;> rfl
  intro m hm
  apply RunSpec.step (answerPoint_evalFrom _ _)
    (show Interp.stepFn (evalFrom m (.seq [e₁, e₂])) =
      .next (pushK [.seqK [toRuby e₂]] (evalFrom m e₁)) from rfl)
  apply (h₁ m hm).bindSpec (hcf _)
  intro a n hr
  cases a with
  | esc j =>
    apply RunSpec.step (by rfl) (hesc _ n j)
    exact RunSpec.answer ⟨hr.1, hr.2.1, fun _ hv => by cases hv⟩
  | val v =>
    apply RunSpec.step (by rfl)
      (show Interp.stepFn (deliverA (.val v) n [.seqK [toRuby e₂]]) =
        .next (pushK [.seqK []] (evalFrom n e₂)) from rfl)
    apply RunSpec.rebase (hf := hr.1)
    apply (h₂ n (hr.2.2 v rfl)).bindSpec (hcf [])
    intro a' n' hr'
    cases a' with
    | esc j =>
      exact RunSpec.step (by rfl) (hesc [] n' j) (RunSpec.answer hr')
    | val w =>
      exact RunSpec.step (by rfl)
        (show Interp.stepFn (deliverA (.val w) n' [.seqK []]) =
          .next (deliverA (.val w) n' []) from rfl) (RunSpec.answer hr')

#print axioms semSafeA_iff_context
#print axioms SemSafeCtxA.vasgn
#print axioms SemSafeCtxA.seq
end Ratchet.Denote.Typed
