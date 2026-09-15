import Denote.Typed.ConstructorReturn

/-! Complete initialized construction through the real frameK/newK return path. The
initializer's own return type is checked, but new returns the initialized receiver. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem step_newK_value (n : Machine) (v recv : Value) :
    Interp.stepFn (deliverA (.val v) n [.newK recv]) =
      .next (deliverA (.val recv) n []) := rfl

theorem newK_escape {origin n : Machine} {Γ : Env} {τ I : Ty} {κ : Ctx}
    (recv : Value) (j : Jump) (he : EscOk n j)
    (hr : RunSpec origin (deliverA (.esc j) n []) Γ τ κ I) :
    RunSpec origin (deliverA (.esc j) n [.newK recv]) Γ τ κ I := by
  cases j with
  | retJ => cases he
  | throwJ => cases he
  | raiseJ | brkJ | nxtJ | redoJ | retryJ =>
    exact RunSpec.step (by rfl) (show Interp.stepFn _ = .next _ from rfl) hr

theorem constructor_continue {κ κb : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {m n : Machine}
    {cn ownerCn : String} {k : ObjId} {md : MethodDef} {ps : List SigParam} {args : List Value}
    {a : Answer} (hm : StateOk κ Γ I m)
    (ht : ReframeFO (returnScopeCtx κ κb) I) (ha : κ.asms = [])
    (hr : κ.scope.runtimeMain = true) (hw : κb.pos.mainWorld = true)
    (hcl : κ.scope.runtimeClass = none) (hq : κb.scope.runtimeClass = some ownerCn)
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hs : κb.selfTy = some (.inst cn .ivar0)) (hi : FirstOrder Ib = true)
    (h : InitResultOk m.heap (constructorFrame m k md ps args) Γb τ a n κb Ib) :
    RunSpec m (deliverA a n [.frameK m.frames.size, .newK (.ref m.heap.objs.size)])
      Γ (.inst cn Ib) (returnScopeCtx κ κb) I := by
  have hf := constructor_pop_framed hm.frameInRange h.1
  cases a with
  | val v =>
    have hn := h.2.2 v rfl
    apply RunSpec.step (by rfl) (step_frameK_value n _ v)
    apply RunSpec.step (by rfl) (step_newK_value _ v _)
    exact RunSpec.answer ⟨hf, constructor_result h.1 hn.typed hs hi,
      fun _ _ => constructor_pop_main_state hm ht ha hr hw hcl hq hk hΓ h.1 hn.typed⟩
  | esc j =>
    apply frameK_escape _ j h.2.1
    apply newK_escape _ j (show EscOk (popMethodFrame n) j from h.2.1)
    apply RunSpec.answer
    exact ⟨hf, h.2.1, fun _ hv => by cases hv⟩

theorem constructor_body_runSpec {κ κb : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {m : Machine}
    {cn ownerCn : String} {k : ObjId} {md : MethodDef} {ps : List SigParam} {args : List Value}
    {body : Ratchet.Expr} (hm : StateOk κ Γ I m)
    (ht : ReframeFO (returnScopeCtx κ κb) I) (ha : κ.asms = [])
    (hr : κ.scope.runtimeMain = true) (hw : κb.pos.mainWorld = true)
    (hcl : κ.scope.runtimeClass = none) (hq : κb.scope.runtimeClass = some ownerCn)
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hs : κb.selfTy = some (.inst cn .ivar0)) (hi : FirstOrder Ib = true)
    (hb : InitRunSpec m.heap (constructorFrame m k md ps args)
      (evalFrom (constructorFrame m k md ps args) body) Γb τ κb Ib) :
    RunSpec m (pushK [.frameK m.frames.size, .newK (.ref m.heap.objs.size)]
      (evalFrom (constructorFrame m k md ps args) body)) Γ (.inst cn Ib) (returnScopeCtx κ κb) I := by
  apply hb.bindRunSpec (by
    intro c hc tag
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp)
  intro a n hn
  exact constructor_continue hm ht ha hr hw hcl hq hk hΓ hs hi hn

/-- A checked initializer domain is used once, at required-parameter entry, then its
result contract is composed through both real return continuations. -/
theorem constructor_runSpec_at {κ κb : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {m : Machine}
    {cn ownerCn : String} {k ownerId : ObjId} {md : MethodDef} {ps : List SigParam} {args : List Value}
    {body : Ratchet.Expr}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hout : ReframeFO (returnScopeCtx κ κb) I)
    (hc : PlainAllocator m.heap k) (site : InstanceSite κ cn k m.heap)
    (owner : InstanceSite κ ownerCn ownerId m.heap)
    (hd : NewDispatch m.heap (classOf m.heap (.ref k)))
    (code : InstanceMethodCode ownerId "initialize" md) (hi : Interp.userInit? m.heap k = some md)
    (hparams : md.params = (ps.map (·.1)).map RubyCore.Param.req) (hbody : md.body = toRuby body)
    (hlen : args.length = ps.length) (hargs : DenAll (ps.map (·.2)) m args)
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hentry : ∀ x, constGet? (initializerBodyCtxAt κ cn ownerCn) x = constGet? κ x)
    (hr : κ.scope.runtimeMain = true) (hw : κb.pos.mainWorld = true)
    (hcl : κ.scope.runtimeClass = none) (hq : κb.scope.runtimeClass = some ownerCn)
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hs : κb.selfTy = some (.inst cn .ivar0)) (hIb : FirstOrder Ib = true)
    (hkont : m.kont = [])
    (hb : SemInitA (initializerBodyCtxAt κ cn ownerCn) ps .ivar0 body τ κb Γb Ib) :
    ∃ n, Interp.finishSend m (.ref k) .explicit "new" args .none = .next n ∧
      RunSpec m n Γ (.inst cn Ib) (returnScopeCtx κ κb) I := by
  have he := constructor_frame_state_at hm ht ha hc site owner (hm.runtime hr).phase code hlen hargs hps hentry
  have hrun := constructor_body_runSpec hm hout ha hr hw hcl hq hk hΓ hs hIb
    (hb m.heap (constructorFrame m k md ps args) he)
  refine ⟨_, constructor_required_entry hc hd hi hparams code.captured code.declared
    (by simpa using hlen), ?_⟩
  simpa only [constructorFrame, ctorAllocated, pushMethodFrame, Interp.withKont, evalFrom,
    pushK, reCtl, hbody, hkont, List.nil_append] using hrun

/-- Own constructors are the coincident receiver/owner specialization. -/
theorem constructor_runSpec {κ κb : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {m : Machine}
    {cn : String} {k : ObjId} {md : MethodDef} {ps : List SigParam} {args : List Value}
    {body : Ratchet.Expr}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hout : ReframeFO (returnScopeCtx κ κb) I)
    (hc : PlainAllocator m.heap k) (site : InstanceSite κ cn k m.heap)
    (hd : NewDispatch m.heap (classOf m.heap (.ref k)))
    (code : InstanceMethodCode k "initialize" md) (hi : Interp.userInit? m.heap k = some md)
    (hparams : md.params = (ps.map (·.1)).map RubyCore.Param.req) (hbody : md.body = toRuby body)
    (hlen : args.length = ps.length) (hargs : DenAll (ps.map (·.2)) m args)
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hentry : ∀ x, constGet? (initializerBodyCtx κ cn) x = constGet? κ x)
    (hr : κ.scope.runtimeMain = true) (hw : κb.pos.mainWorld = true)
    (hcl : κ.scope.runtimeClass = none) (hq : κb.scope.runtimeClass = some cn)
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hs : κb.selfTy = some (.inst cn .ivar0)) (hIb : FirstOrder Ib = true)
    (hkont : m.kont = [])
    (hb : SemInitA (initializerBodyCtx κ cn) ps .ivar0 body τ κb Γb Ib) :
    ∃ n, Interp.finishSend m (.ref k) .explicit "new" args .none = .next n ∧
      RunSpec m n Γ (.inst cn Ib) (returnScopeCtx κ κb) I :=
  constructor_runSpec_at hm ht ha hout hc site site hd code hi hparams hbody hlen hargs hps
    hentry hr hw hcl hq hk hΓ hs hIb hkont hb

#print axioms constructor_continue
#print axioms constructor_body_runSpec
#print axioms constructor_runSpec_at
#print axioms constructor_runSpec
end Ratchet.Denote.Typed
