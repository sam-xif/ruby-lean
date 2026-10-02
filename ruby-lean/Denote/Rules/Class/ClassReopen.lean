import Denote.Rules.Class.ClassDeclActual
import Denote.Sem.Names.ConstLive

/-! Reopening an existing top-level class: the heap is unchanged, a class frame is pushed
on the class object, and the body's frame is popped by the ordinary class return. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote
open RubyCore.Proof.Judgment (freshModFrame)

variable {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {k : ObjId} {body : RubyCore.Expr}
local notation "entry" => classCallbackBody m k body

theorem reopen_current : (entry).currentFrame = freshModFrame k m.currentFrame.cref := by
  simp [classCallbackBody, Machine.currentFrame, Array.getD_eq_getD_getElem?]

theorem reopen_getLocal (x : String) : (entry).getLocal x = .nil := by
  simp [Machine.getLocal, Machine.getLocal.go, Machine.localFrameId, Machine.localFrameId.go,
    classCallbackBody, freshModFrame, Array.getD_eq_getD_getElem?]

theorem reopen_state {name : String} (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true)
    (ha : κ.asms = []) (hin : κ.pos.mainWorld = true) (hco : κ.consts = [])
    (site : InstanceSite κ name k m.heap) :
    StateOk (reopenBodyCtx κ name) [] .ivar0 entry := by
  have hmain := hm.runtime hr
  have hcur := reopen_current (m := m) (k := k) (body := body)
  have hcref : (entry).currentFrame.cref = [k] := by
    rw [hcur]; simp [freshModFrame, hmain.cref]
  have hown : (entry).currentFrame.defmod = k := by rw [hcur]; rfl
  exact {
    runtime := by intro h; cases h
    mainSite := fun _ => hm.mainSite hin
    moduleBase := hm.moduleBase
    classRuntime := by
      intro cn hcn
      change some name = some cn at hcn
      cases hcn
      exact ⟨k, ⟨site.named, site.live, hown, hcref, by rw [hcur]; rfl, hmain.phase,
        by simp only [defaultDefVis, hcur, freshModFrame]; rfl, site.hook,
        by rw [hcur]; rfl, by rw [hcur]; rfl, site.detached, site.unfrozen, site.mainLive,
        site.notMain, by rw [hcur]; rfl, by rw [hcur]; rfl⟩⟩
    singletonRuntime := by intro cn h; cases h
    classSites := by
      intro cn hcn
      change cn ∈ κ.classes.map (·.name) ++ [name] at hcn
      rcases List.mem_append.mp hcn with hcn | hcn
      · exact hm.classSites cn (List.mem_append_left _ hcn)
      · rw [List.mem_singleton.mp hcn]; exact ⟨k, site⟩
    allocators := hm.allocators
    globalConsts := fun cn v hv => List.mem_cons_of_mem _ (hm.globalConsts cn v hv)
    sat := hm.sat
    primitiveDispatch := hm.primitiveDispatch
    primitiveErrors := hm.primitiveErrors
    primitiveInit := hm.primitiveInit
    stringPayload := hm.stringPayload
    arrayPayload := hm.arrayPayload
    hashPayload := hm.hashPayload
    frozenFields := hm.frozenFields
    core := hm.core
    frameInRange := by simp [FrameInRange, classCallbackBody]
    env := ⟨fun x τ hx => by simp [envGet?] at hx, fun x _ => reopen_getLocal x⟩
    selfSpine := ⟨by simp [denSpine, denSpineFrom], fun _ _ h => by cases h⟩
    classes := hm.classes
    ownNames := hm.ownNames
    classChains := hm.classChains
    rootInit := hm.rootInit
    defs := hm.defs
    asms := by intro a ham; change a ∈ κ.asms at ham; rw [ha] at ham; cases ham
    frame := by change FrameOk none _; simp [FrameOk, hcur, freshModFrame]
    closures := trivial
    blockTy := by change BlockTyOk none _; simp [BlockTyOk, hcur, freshModFrame]
    selfTy := by
      change SelfTyOk (some (.clsOf name)) _
      simp only [SelfTyOk, hcur, denM]
      have hn : classNamed? (entry).heap name = some k := site.named
      simp [freshModFrame, isClassRefNamed, hn]
    consts := by
      intro cn τ hc
      have h0 := constGet?_empty (κ := reopenBodyCtx κ name) (by change κ.consts = []; exact hco) cn
      rw [h0] at hc; cases hc
    constPaths := by
      intro owner cn τ j hc
      change envGet? κ.consts _ = _ at hc
      simp [hco, envGet?] at hc
    nested := hm.nested
    privConsts := trivial
    constScope := InstanceSite.constScope site hcref hown
    exact := hm.exact
    nameFree := by
      intro mn hmn j hj owner md hl
      rcases List.mem_cons.mp hj with hj | hj
      · subst hj
        rw [hcur] at hl
        exact site.classNames mn hmn owner md hl
      · exact hm.nameFree mn hmn j (List.mem_cons_of_mem _ hj) owner md hl
    bareFree := by intro _ _ _ hself; cases hself
    missFree := by intro _ hself; cases hself
    query := hm.query
    clsQuery := hm.clsQuery
    declCls := hm.declCls
    baseChains := hm.baseChains
    nilQuery := hm.nilQuery
    selfLive := by
      intro o ho
      rw [hcur] at ho
      change Value.ref k = .ref o at ho
      cases ho
      exact site.live
    names := hm.names
    localAlias := by rw [hcur]; rfl
    capturedLive := by rw [hcur]; exact CaptureLive.none
    rootClean := hm.rootClean }

#print axioms reopen_state

theorem stepFn_reopen {name : String} {b : Ratchet.Expr} (hm : StateOk κ Γ I m)
    (hr : κ.scope.runtimeMain = true) (c : Cls) (hc : c ∈ κ.classes) (hcn : c.name = name)
    (hmod : c.isModule = false) (hk : classNamed? m.heap name = some k) :
    Interp.stepFn (evalFrom m (.class' name none b)) =
      .next (classCallbackBody (evalFrom m (.class' name none b)) k (toRuby b)) := by
  have hmain := hm.runtime hr
  let start := evalFrom m (.class' name none b)
  have hl : start.lexicalNamespace = Boot.objectId := by
    simp [start, Machine.lexicalNamespace, evalFrom, hmain.cref]
  have hown : constOwn start.heap start.lexicalNamespace name = some (.ref k) := by
    rw [hl]; exact classNamed_constOwn hk
  have hdecl := (hm.declCls c hc k (hcn ▸ hk)).2.2.2.1
  rw [hmod] at hdecl
  obtain ⟨cp, hcp, hcpm⟩ : ∃ cp, m.heap.classPayload? k = some cp ∧ cp.isModule = false := by
    cases hq : m.heap.classPayload? k with
    | none => rw [hq] at hdecl; cases hdecl
    | some cp => rw [hq] at hdecl; exact ⟨cp, rfl, by simpa using hdecl⟩
  have hcp' : start.heap.classPayload? k = some cp := hcp
  change Interp.enterClassBody start name false none (toRuby b) = _
  simp only [Interp.enterClassBody, hown, hcp', hcpm, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  exact pushClassFrame_ordinary hmain.phase hmain.origin

theorem reopen_runSpec {κb : Ctx} {Γb : Env} {Ib τ : Ty} {c : Cls} {b : Ratchet.Expr}
    (hm : StateOk κ Γ I m) (ht : ReframeFO (returnScopeCtx κ κb) I) (ha : κ.asms = [])
    (hr : κ.scope.runtimeMain = true) (hin : κ.pos.mainWorld = true)
    (hw : κb.pos.mainWorld = true) (hcl : κ.scope.runtimeClass = none)
    (hq : κb.scope.runtimeClass = some c.name)
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) (hτ : FirstOrder τ = true)
    (hco : κ.consts = []) (hc : c ∈ κ.classes) (hmod : c.isModule = false)
    (hb : SemSafeCtxA (reopenBodyCtx κ c.name) [] .ivar0 b τ κb Γb Ib) :
    RunSpec m (evalFrom m (.class' c.name none b)) Γ τ (returnScopeCtx κ κb) I := by
  obtain ⟨j, site⟩ := hm.classSites.of_class hc
  let start := evalFrom m (.class' c.name none b)
  have hstart : StateOk κ Γ I start := StateOk_reCtl hm _ []
  have hs := stepFn_reopen (b := b) hm hr c hc rfl hmod site.named
  have hheader := reopen_state (m := start) (body := toRuby b) hstart hr ha hin hco site
  have hbody := hb _ (StateOk_reCtl hheader (.eval (toRuby b)) [])
  have hrun := ClassActivation.runSpec (k := j) (h := start.heap) hstart (Framed.refl start)
    ht ha hr hw hcl hq hk hΓ hτ (hbody.rebase (Framed.of_heap_stack rfl rfl (.of_eq rfl rfl)))
  exact RunSpec.step (answerPoint_evalFrom _ _) hs (hrun.rebase (Framed_reCtl m _ []))

end Ratchet.Denote.Typed

namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemSafeCtxA.classReopen {κ κb : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {c : Cls} {b : Ratchet.Expr}
    (hc : c ∈ κ.classes) (hmod : c.isModule = false)
    (hb : SemSafeCtxA (reopenBodyCtx κ c.name) [] .ivar0 b τ κb Γb Ib)
    (hg : reopenRuleB κ κb Γ I τ c.name = true) :
    SemSafeCtxA κ Γ I (.class' c.name none b) τ (returnScopeCtx κ κb) Γ I := by
  simp only [reopenRuleB, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨ht, hΓ⟩, hτ⟩, ha, hr, hf, hin, hw, hcl, hq, hco⟩, htab⟩, _⟩ := hg
  have hco' : κ.consts = [] := by
    simp only [plainClassTablesB, Bool.and_eq_true, List.isEmpty_iff] at htab; exact htab.1
  intro m hm
  exact reopen_runSpec hm (reframeTypesB_sound ht) ha hr hin hw hcl hq
    (fun x => (constGet?_empty hco x).trans (constGet?_empty (κ := returnScopeCtx κ κb) hco x).symm)
    (List.all_eq_true.mp hΓ) hτ hco' hc hmod hb

#print axioms reopen_runSpec
#print axioms SemSafeCtxA.classReopen
end Ratchet.Denote.Typed
