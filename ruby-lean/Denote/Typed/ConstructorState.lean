import Denote.Typed.ConstructorEntry
import Denote.Typed.InstanceState
import Denote.Typed.InitRun

/-! Allocation establishes the initializer's full annotated entry state, anchored before
the new object exists. No body or call-site specialization is hidden in this transport. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem ctorAllocated_ext {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {k : ObjId}
    (hm : StateOk κ Γ I m) (hc : PlainAllocator m.heap k) : Ext m (ctorAllocated m k) := by
  have he := ext_push { klass := k } hm.sat hm.core.basicSelf (by intro c; cases c; simp)
    rfl rfl hc.rooted
  exact he.trans (Ext_toReCtl _ m.ctl (.newK (.ref m.heap.objs.size) :: m.kont))

theorem ctorAllocated_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {k : ObjId}
    (hm : StateOk κ Γ I m) (hc : PlainAllocator m.heap k) :
    StateOk κ Γ I (ctorAllocated m k) := by
  exact StateOk_ext hm (ctorAllocated_ext hm hc)
    (stringPayloadOk_push hm.stringPayload (by simpa using hc.notString))
    (arrayPayloadOk_push hm.arrayPayload (by simp))
    (hashPayloadOk_push hm.hashPayload (by simp)) rfl

theorem ctorAllocated_receiver {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {k : ObjId}
    {cn : String} (hm : StateOk κ Γ I m) (hc : PlainAllocator m.heap k)
    (hn : classNamed? m.heap cn = some k) :
    denM (.inst cn .ivar0) (ctorAllocated m k) (.ref m.heap.objs.size) := by
  have he := ctorAllocated_ext hm hc
  rw [denM]
  simp only [isExactInst, he.classNamed?_eq, hn]
  simp [ctorAllocated, pushHeap_get_self, denSpineFrom]

def constructorFrame (m : Machine) (k : ObjId) (md : MethodDef)
    (ps : List SigParam) (args : List Value) : Machine :=
  pushMethodFrame (ctorAllocated m k)
    (requiredFrame (.ref m.heap.objs.size) "initialize" md (ps.map (·.1)) args)

theorem constructor_frame_state_at {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {cn ownerCn : String} {k ownerId : ObjId} {md : MethodDef} {ps : List SigParam} {args : List Value}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hc : PlainAllocator m.heap k) (site : InstanceSite κ cn k m.heap)
    (owner : InstanceSite κ ownerCn ownerId m.heap)
    (hp : m.preludeMode = false) (code : InstanceMethodCode ownerId "initialize" md)
    (hlen : args.length = ps.length) (hargs : DenAll (ps.map (·.2)) m args)
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hk : ∀ x, constGet? (initializerBodyCtxAt κ cn ownerCn) x = constGet? κ x) :
    InitState m.heap (initializerBodyCtxAt κ cn ownerCn) ps .ivar0
      (constructorFrame m k md ps args) := by
  have he := ctorAllocated_ext hm hc
  have hs := instance_enter_state_at (ctorAllocated_state hm hc) ht ha
    (site.ext he hc.live) (owner.ext he owner.live) hp code rfl
    (ctorAllocated_receiver hm hc site.named) hlen (denAll_ext he hargs) hps hk
  refine ⟨{ hs with selfSpine := ?_ }, he.initGrow, ?_⟩
  · refine ⟨hs.selfSpine.1, ?_⟩
    intro x _ _
    simp only [constructorFrame, currentFrame_pushMethodFrame, requiredFrame]
    change ivarOf (pushHeap m.heap { klass := k }) (.ref m.heap.objs.size) x = .nil
    simp [ivarOf, pushHeap_get_self]
  · refine ⟨m.heap.objs.size, ?_, Nat.le_refl _, ?_, ?_⟩
    · simp [constructorFrame, currentFrame_pushMethodFrame, requiredFrame]
    · simp [constructorFrame, pushMethodFrame, ctorAllocated]
    · simp [constructorFrame, pushMethodFrame, ctorAllocated, pushHeap_get_self]

/-- Own initialization is the same proof with coincident receiver and lexical owner. -/
theorem constructor_frame_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {cn : String} {k : ObjId} {md : MethodDef} {ps : List SigParam} {args : List Value}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hc : PlainAllocator m.heap k) (site : InstanceSite κ cn k m.heap)
    (hp : m.preludeMode = false) (code : InstanceMethodCode k "initialize" md)
    (hlen : args.length = ps.length) (hargs : DenAll (ps.map (·.2)) m args)
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hk : ∀ x, constGet? (initializerBodyCtx κ cn) x = constGet? κ x) :
    InitState m.heap (initializerBodyCtx κ cn) ps .ivar0 (constructorFrame m k md ps args) :=
  constructor_frame_state_at hm ht ha hc site site hp code hlen hargs hps hk

/-- Actual constructor dispatch consumes a body proof over the annotated parameter
domain. The returned run is body-local; newK/caller restoration are a separate obligation. -/
theorem constructor_body_entry_at {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {m : Machine}
    {cn ownerCn : String} {k ownerId : ObjId} {md : MethodDef} {ps : List SigParam} {args : List Value}
    {body : Ratchet.Expr}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hc : PlainAllocator m.heap k) (site : InstanceSite κ cn k m.heap)
    (owner : InstanceSite κ ownerCn ownerId m.heap)
    (hd : NewDispatch m.heap (classOf m.heap (.ref k)))
    (hp : m.preludeMode = false) (code : InstanceMethodCode ownerId "initialize" md)
    (hi : Interp.userInit? m.heap k = some md)
    (hparams : md.params = (ps.map (·.1)).map RubyCore.Param.req)
    (hbody : md.body = toRuby body)
    (hlen : args.length = ps.length) (hargs : DenAll (ps.map (·.2)) m args)
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hk : ∀ x, constGet? (initializerBodyCtxAt κ cn ownerCn) x = constGet? κ x)
    (hb : SemInitA (initializerBodyCtxAt κ cn ownerCn) ps .ivar0 body τ κ' Γ' I') :
    ∃ n, Interp.finishSend m (.ref k) .explicit "new" args .none = .next n ∧
      n.ctl = .eval (toRuby body) ∧
      InitState m.heap (initializerBodyCtxAt κ cn ownerCn) ps .ivar0 n ∧
      InitRunSpec m.heap n (evalFrom n body) Γ' τ κ' I' := by
  have he := constructor_frame_state_at hm ht ha hc site owner hp code hlen hargs hps hk
  let n := Interp.withKont (constructorFrame m k md ps args) (.eval md.body) (.frameK m.frames.size)
  have hn : InitState m.heap (initializerBodyCtxAt κ cn ownerCn) ps .ivar0 n := he.reCtl _ _
  exact ⟨n, constructor_required_entry hc hd hi hparams code.captured code.declared
    (by simpa using hlen), congrArg Ctl.eval hbody, hn, hb m.heap n hn⟩

theorem constructor_body_entry {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {m : Machine}
    {cn : String} {k : ObjId} {md : MethodDef} {ps : List SigParam} {args : List Value}
    {body : Ratchet.Expr}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hc : PlainAllocator m.heap k) (site : InstanceSite κ cn k m.heap)
    (hd : NewDispatch m.heap (classOf m.heap (.ref k)))
    (hp : m.preludeMode = false) (code : InstanceMethodCode k "initialize" md)
    (hi : Interp.userInit? m.heap k = some md)
    (hparams : md.params = (ps.map (·.1)).map RubyCore.Param.req)
    (hbody : md.body = toRuby body)
    (hlen : args.length = ps.length) (hargs : DenAll (ps.map (·.2)) m args)
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hk : ∀ x, constGet? (initializerBodyCtx κ cn) x = constGet? κ x)
    (hb : SemInitA (initializerBodyCtx κ cn) ps .ivar0 body τ κ' Γ' I') :
    ∃ n, Interp.finishSend m (.ref k) .explicit "new" args .none = .next n ∧
      n.ctl = .eval (toRuby body) ∧
      InitState m.heap (initializerBodyCtx κ cn) ps .ivar0 n ∧
      InitRunSpec m.heap n (evalFrom n body) Γ' τ κ' I' :=
  constructor_body_entry_at hm ht ha hc site site hd hp code hi hparams hbody hlen hargs hps hk hb

#print axioms ctorAllocated_state
#print axioms constructor_frame_state_at
#print axioms constructor_body_entry_at
#print axioms constructor_frame_state
#print axioms constructor_body_entry
end Ratchet.Denote.Typed
