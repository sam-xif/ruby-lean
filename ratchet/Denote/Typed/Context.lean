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

theorem SemSafeCtxA.weaken {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ σ τ : Ty}
    {e : Ratchet.Expr} (h : SemSafeCtxA κ Γ I e σ κ₁ Γ₁ I₁)
    (hout : ∀ m v, StateOk κ₁ Γ₁ I₁ m → denM σ m v →
      StateOk κ₂ Γ₂ I₂ m ∧ denM τ m v) : SemSafeCtxA κ Γ I e τ κ₂ Γ₂ I₂ :=
  fun m hm => (h m hm).weaken hout

/-- A frame selects a following expression on values and propagates escapes. The selected
expression starts at the premise's outgoing state index, not the outer expression's. -/
theorem SemSafeCtxA.frame {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ σ τ : Ty}
    {sub out : Ratchet.Expr} {k : Kont} {branch : Value → Ratchet.Expr}
    (hp : SemSafeCtxA κ Γ I sub σ κ₁ Γ₁ I₁)
    (hb : ∀ v, SemSafeCtxA κ₁ Γ₁ I₁ (branch v) τ κ₂ Γ₂ I₂)
    (hK : RubyCore.Proof.CatchFree [k])
    (heval : ∀ m, Interp.stepFn (evalFrom m out) =
      .next (pushK [k] (evalFrom m sub)))
    (hval : ∀ m v, Interp.stepFn (deliverA (.val v) m [k]) =
      .next (evalFrom m (branch v)))
    (hesc : ∀ m j, Interp.stepFn (deliverA (.esc j) m [k]) =
      .next (deliverA (.esc j) m [])) : SemSafeCtxA κ Γ I out τ κ₂ Γ₂ I₂ := by
  intro m hm
  apply RunSpec.step (answerPoint_evalFrom _ _) (heval m)
  apply (hp m hm).bindSpec hK
  intro a n hr
  have hap : answerPoint (deliverA a n [k]) = none := by simp [answerPoint, deliverA]
  cases a with
  | val v => exact RunSpec.step hap (hval n v) ((hb v n (hr.2.2 v rfl)).rebase hr.1)
  | esc j =>
    exact RunSpec.step hap (hesc n j)
      (RunSpec.answer ⟨hr.1, hr.2.1, fun _ hv => by cases hv⟩)

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

theorem SemSafeCtxA.fltLit {κ : Ctx} {Γ : Env} {I : Ty} {b : UInt64} :
    SemSafeCtxA κ Γ I (.flt b) .float κ Γ I := by
  apply SemSafeCtxA.leaf
  intro m hm
  exact ⟨m, .flt (Float.ofBits b), rfl, .refl m, by simp [AnsOk, denM, isFltV], fun _ _ => hm⟩

theorem SemSafeCtxA.symLit {κ : Ctx} {Γ : Env} {I : Ty} {s : String} :
    SemSafeCtxA κ Γ I (.sym s) .sym κ Γ I := by
  apply SemSafeCtxA.leaf
  intro m hm
  exact ⟨m, .sym s, rfl, .refl m, by simp [AnsOk, denM, isSymV], fun _ _ => hm⟩

theorem SemSafeCtxA.truLit {κ : Ctx} {Γ : Env} {I : Ty} :
    SemSafeCtxA κ Γ I .tru .bool κ Γ I := by
  apply SemSafeCtxA.leaf
  intro m hm
  exact ⟨m, .bool true, rfl, .refl m, by simp [AnsOk, denM, isBoolV], fun _ _ => hm⟩

theorem SemSafeCtxA.flsLit {κ : Ctx} {Γ : Env} {I : Ty} :
    SemSafeCtxA κ Γ I .fls .bool κ Γ I := by
  apply SemSafeCtxA.leaf
  intro m hm
  exact ⟨m, .bool false, rfl, .refl m, by simp [AnsOk, denM, isBoolV], fun _ _ => hm⟩

theorem SemSafeCtxA.nilLit {κ : Ctx} {Γ : Env} {I : Ty} :
    SemSafeCtxA κ Γ I .nil .nilT κ Γ I := by
  apply SemSafeCtxA.leaf
  intro m hm
  exact ⟨m, .nil, rfl, .refl m, by simp [AnsOk, denM, isNilV], fun _ _ => hm⟩

theorem SemSafeCtxA.strLit {κ : Ctx} {Γ : Env} {I : Ty} {s : String} :
    SemSafeCtxA κ Γ I (.str s) (.cls "String") κ Γ I := by
  apply SemSafeCtxA.leaf
  intro m hm
  obtain ⟨hok, hden⟩ := strLit_alloc_ok (s := s) [] hm
  exact ⟨reCtl { m with heap := pushHeap m.heap (strObj s) } (.value (.ref m.heap.objs.size)) [],
    .ref m.heap.objs.size, rfl,
    Framed.of_ext ((ext_push (m := m) (strObj s) hm.sat hm.core.basicSelf
      (fun c => by simp [strObj]) rfl rfl
      (by simpa [strObj] using hm.core.stringBasic)).trans (Ext_toReCtl _ _ _)),
    hden, fun _ _ => hok⟩

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

#print axioms semSafeA_iff_context
#print axioms SemSafeCtxA.vasgn
#print axioms SemSafeCtxA.strLit
end Ratchet.Denote.Typed
