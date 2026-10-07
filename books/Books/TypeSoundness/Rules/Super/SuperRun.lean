import Books.TypeSoundness.Rules.Super.SuperState
import Books.TypeSoundness.Rules.Super.SuperDispatch

/-! Checked parent initialization through the real doSuper/frameK path. The same
receiver and allocation anchor return with the parent's output spine and child's locals. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem super_initializer_continue {anchor : Heap} {κ κb : Ctx} {Γ Γb : Env} {I Ib τ : Ty}
    {m n : Machine} {f : RubyCore.Frame} {ownerName recvName bodyOwner : String} {a : Answer}
    (hm : InitState anchor κ Γ I m) (ht : ReframeFO (returnScopeCtx κ κb) Ib)
    (ha : κ.asms = []) (hr : κ.scope.runtimeMain = false)
    (hcl : κ.scope.runtimeClass = some ownerName) (hq : κb.scope.runtimeClass = some bodyOwner)
    (hself : κ.selfTy = some (.inst recvName .ivar0)) (hblock : κ.blockTy = none)
    (hclosed : κ.scope.closedIvars = κb.scope.closedIvars)
    (ho : ownerName ∈ κb.classes.map (·.name)) (hv : recvName ∈ κb.classes.map (·.name))
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hΓ : ∀ p ∈ Γ, IvarStable (stripAlias p.2) = true) (hτ : FirstOrder τ = true)
    (hc : f.captured = none) (hs : f.self = m.currentFrame.self)
    (h : InitResultOk anchor (pushMethodFrame m f) Γb τ a n κb Ib) :
    InitRunSpec anchor m (deliverA a n [.frameK m.frames.size])
      Γ τ (returnScopeCtx κ κb) Ib := by
  have hp := h.1.pop hm.typed.frameInRange.2 hc
  cases a with
  | val v =>
    apply InitRunSpec.step (by rfl) (step_frameK_value n _ v)
    exact InitRunSpec.answer ⟨hp, (denM_heap_only (m₁ := n) (m₂ := popMethodFrame n) hτ rfl).mp h.2.1,
      fun _ _ => super_initializer_pop_state hm ht ha hr hcl hq hself hblock hclosed
        ho hv hk hΓ hc hs h.1 (h.2.2 v rfl)⟩
  | esc j =>
    have he := h.2.1
    have hr : InitRunSpec anchor m (deliverA (.esc j) (popMethodFrame n) [])
        Γ τ (returnScopeCtx κ κb) Ib :=
      InitRunSpec.answer ⟨hp, he, fun _ hv => by cases hv⟩
    cases j with
    | retJ | throwJ | brkJ | nxtJ | redoJ | retryJ => cases he
    | raiseJ =>
      exact InitRunSpec.step (by rfl) (show Interp.stepFn _ = .next _ from rfl) hr

/-- Full conformance and a checked super route select the parent's annotated body.
Neither physical lookup nor a call-site-specialized body proof is an input. -/
theorem declared_super_initializer_runSpec {anchor : Heap} {κ κb : Ctx} {Γ Γb : Env}
    {I Ib τ : Ty} {m : Machine} {receiver : Cls} {current owner : String} {d : Defn}
    {ps : List SigParam} {args : List Value}
    (hm : InitState anchor κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hout : ReframeFO (returnScopeCtx κ κb) Ib) (hr : receiver ∈ κ.classes)
    (hf : κ.frame = some ⟨receiver.name, current, d.name, false⟩)
    (hc : κ.scope.runtimeClass = some current) (hmain : κ.scope.runtimeMain = false)
    (hself : κ.selfTy = some (.inst receiver.name .ivar0)) (hblock : κ.blockTy = none)
    (hclosed : κ.scope.closedIvars = true) (hclosed' : κb.scope.closedIvars = true)
    (hn : d.name = "initialize") (route : SuperRoute κ.classes receiver.name current owner d)
    (hparams : d.params = ps.map (fun p => Checker.Param.req p.1))
    (hlen : args.length = ps.length) (hargs : DenAll (ps.map (·.2)) m args)
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hentry : ∀ x, constGet? (initializerBodyCtxAt κ receiver.name owner) x = constGet? κ x)
    (hq : κb.scope.runtimeClass = some owner)
    (ho : current ∈ κb.classes.map (·.name)) (hv : receiver.name ∈ κb.classes.map (·.name))
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hΓ : ∀ p ∈ Γ, IvarStable (stripAlias p.2) = true) (hτ : FirstOrder τ = true)
    (hkont : m.kont = [])
    (hb : SemInitA (initializerBodyCtxAt κ receiver.name owner) ps I d.body τ κb Γb Ib) :
    ∃ n, Interp.doSuper m args none = .next n ∧
      InitRunSpec anchor m n Γ τ (returnScopeCtx κ κb) Ib := by
  obtain ⟨k, md, hkn, hp, hbody, code, hd⟩ := declared_super_dispatch hm.typed hr hf hc hself
    (by rw [hn]; decide) route
  obtain ⟨r, site⟩ := hm.typed.classSites receiver.name
    (List.mem_append_left _ (List.mem_map.mpr ⟨receiver, hr, rfl⟩))
  obtain ⟨j, ownerSite⟩ := hm.typed.classSites owner
    (List.mem_append_left _ (List.mem_map.mpr ⟨route.cls, route.member, route.nameOk⟩))
  have heq : j = k := Option.some.inj (ownerSite.named.symm.trans hkn)
  subst j
  have code' : InstanceMethodCode k "initialize" md := by simpa only [hn] using code
  obtain ⟨_, scope⟩ := hm.typed.classRuntime current hc
  let entry := pushMethodFrame m (requiredFrame m.currentFrame.self "initialize" md (ps.map (·.1)) args)
  have he : InitState anchor (initializerBodyCtxAt κ receiver.name owner) ps I entry :=
    super_initializer_state hm ht ha site ownerSite scope.phase code' hself hclosed hlen hargs hps hentry
  have run := (hb anchor entry he).bindSpec (origin := m) he.typed.rootClean
    (K := [.frameK m.frames.size]) (by intro c hc; simp at hc; subst hc; rfl)
    (fun _ _ hh => super_initializer_continue
      (f := requiredFrame m.currentFrame.self "initialize" md (ps.map (·.1)) args)
      hm hout ha hmain hc hq hself hblock
      (hclosed.trans hclosed'.symm) ho hv hk hΓ hτ rfl rfl hh)
  have hp' : md.params = (ps.map (·.1)).map RubyCore.Param.req :=
    hp.trans (by rw [hparams]; exact toRubyParams_required ps)
  refine ⟨_, hd.trans (by
    rw [hn]
    exact enterUserMethod_required m m.currentFrame.self "initialize" md _ args hp'
      code.captured code.declared (by simpa using hlen) code.fromBlock code.forTargets), ?_⟩
  simpa only [entry, pushMethodFrame, Interp.withKont, evalFrom, pushK, reCtl,
    hbody, hkont, List.nil_append] using run

#print axioms super_initializer_continue
#print axioms declared_super_initializer_runSpec
end Checker.Soundness.Typed
