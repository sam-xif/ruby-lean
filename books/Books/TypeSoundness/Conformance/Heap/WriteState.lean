import Books.TypeSoundness.Conformance.Heap.IvarMutation
import Books.TypeSoundness.Conformance.Instance.InstanceSiteWrite
import Books.TypeSoundness.Conformance.Instance.MainSiteWrite

/-! A write preserves dispatch and machine structure, not arbitrary typed data.
The six value-sensitive conformance components must be re-established explicitly.
This transport is not a typing rule and does not assume universal denotation preservation.
-/
set_option autoImplicit false
namespace Checker.Soundness
open RubyCore Checker

theorem bindIvar_later (m : Machine) (x : String) (v : Value) :
    Later m (Interp.bindIvar m x v) := by
  have hi := bindIvar_ivarOnly m x v
  exact ⟨by simp, by simp, by rw [hi.size]; exact Nat.le_refl _, fun o _ => hi.klass o,
    fun o _ => hi.eigen o, fun o _ => hi.payload o, fun o _ => hi.frozen o,
    hi.classPayload, hi.ancestors_eq⟩

theorem bindIvar_classNamed (m : Machine) (x : String) (v : Value) (cn : String) :
    classNamed? (Interp.bindIvar m x v).heap cn = classNamed? m.heap cn := by
  simp only [classNamed?, constLookup, (bindIvar_ivarOnly m x v).classPayload]

theorem bindIvar_isAName (m : Machine) (x : String) (v w : Value) (cn : String) :
    isAName (Interp.bindIvar m x v).heap w cn = isAName m.heap w cn := by
  simp only [isAName, bindIvar_classNamed, isA, (bindIvar_ivarOnly m x v).classOf_eq,
    (bindIvar_ivarOnly m x v).ancestors_eq]

theorem bindIvar_isExactInst (m : Machine) (x : String) (v w : Value) (cn : String) :
    isExactInst (Interp.bindIvar m x v).heap w cn = isExactInst m.heap w cn := by
  have hi := bindIvar_ivarOnly m x v
  simp only [isExactInst, bindIvar_classNamed]
  cases classNamed? m.heap cn <;> cases w <;> simp only [hi.size, hi.eigen, hi.klass]

theorem FrozenFieldsOk.bindIvar {m : Machine} {x : String} {v : Value}
    (h : FrozenFieldsOk m.heap)
    (hfz : ∀ o, m.currentFrame.self = .ref o → (m.heap.get o).frozen = false) :
    FrozenFieldsOk (Interp.bindIvar m x v).heap := by
  intro k hk
  cases hs : m.currentFrame.self with
  | ref o =>
    by_cases hko : k = o
    · subst hko
      rw [(bindIvar_ivarOnly m x v).frozen, hfz k hs] at hk
      cases hk
    · rw [bindIvar_get_other hs hko] at hk ⊢; exact h k hk
  | _ => simp only [Interp.bindIvar, hs] at hk ⊢; exact h k hk

theorem StateOk_bindIvar {κ : Ctx} {Γ Γ' : Env} {I I' : Ty} {m : Machine}
    (h : StateOk κ Γ I m) (x : String) (v : Value)
    (he : EnvOk Γ' (Interp.bindIvar m x v))
    (hi : SelfSpineOk I' (Interp.bindIvar m x v) κ.scope.closedIvars)
    (hb : BlockTyOk κ.blockTy (Interp.bindIvar m x v))
    (hs : SelfTyOk κ.selfTy (Interp.bindIvar m x v))
    (hc : ConstsOk κ (Interp.bindIvar m x v))
    (hp : ConstPathsOk κ (Interp.bindIvar m x v))
    (hfz : ∀ o, m.currentFrame.self = .ref o → (m.heap.get o).frozen = false) :
    StateOk κ Γ' I' (Interp.bindIvar m x v) := by
  have hw := bindIvar_ivarOnly m x v
  have hn := bindIvar_classNamed m x v
  have ha := bindIvar_isAName m x v
  have hphase : (Interp.bindIvar m x v).preludeMode = m.preludeMode := by
    unfold Interp.bindIvar; split <;> rfl
  have hd (o : ObjId) : ((Interp.bindIvar m x v).heap.get o).hashDflt = (m.heap.get o).hashDflt := by
    simpa only using congrArg Object.hashDflt (bindIvar_data m x v o)
  have hmethod (k : ObjId) (name : String) :
      Interp.methodOn (Interp.bindIvar m x v).heap k name = Interp.methodOn m.heap k name := by
    simp only [Interp.methodOn, hw.ancestors_eq, hw.lookup_go_eq]
  have hshadow (ks : List ObjId) (name : String) :
      Interp.crubyShadow (Interp.bindIvar m x v).heap ks name = Interp.crubyShadow m.heap ks name := by
    simp only [Interp.crubyShadow, Interp.nativeSingletonMethod, Interp.featureMethod,
      Interp.featureHas, Interp.libraryNamespace, hw.classPayload, hw.className_eq]
    rfl
  have hlookup (k : ObjId) (name : String) :
      constLookupFrom (Interp.bindIvar m x v).heap k name = constLookupFrom m.heap k name := by
    simp only [constLookupFrom, hw.classPayload, hw.ancestors_eq]
  have hresolve (name : String) :
      constResolveAt (Interp.bindIvar m x v) name = constResolveAt m name := by
    simp only [constResolveAt, Interp.lexicalConstant, Machine.lexicalNamespace, bindIvar_currentFrame, hw.constOwn_eq, hlookup, hw.classPayload]
    rfl
  have herr : primitiveErrorB (Interp.bindIvar m x v).heap = primitiveErrorB m.heap := by
    funext cls; simp only [primitiveErrorB, hw.ancestors_eq]
  refine {
    runtime := ?_
    rootClean := by unfold Interp.bindIvar; split <;> exact h.rootClean
    names := hw.namesOk h.names
    localAlias := by simpa only [bindIvar_currentFrame] using h.localAlias
    capturedLive := by
      rw [bindIvar_currentFrame]
      exact h.capturedLive.frames_preserved (by simp) (fun _ _ => by simp)
    mainSite := fun hr => (h.mainSite hr).ivarOnly hw
    moduleBase := h.moduleBase.ivarOnly hw
    classSites := h.classSites.ivarOnly hw
    allocators := h.allocators.ivarOnly hw
    globalConsts := h.globalConsts.ivarOnly hw
    classRuntime := by
      intro cn hr
      obtain ⟨k, hk⟩ := h.classRuntime cn hr
      exact ⟨k, ⟨by simpa only [hn] using hk.named,
        by simpa only [hw.size] using hk.live,
        by simpa only [bindIvar_currentFrame] using hk.owner,
        by simpa only [bindIvar_currentFrame] using hk.cref,
        by simpa only [bindIvar_currentFrame] using hk.captured,
        hphase.trans hk.phase,
        by simpa only [defaultDefVis, bindIvar_currentFrame] using hk.visibility,
        by simpa only [definitionHookQuietB, hw.lookup_eq] using hk.hook,
        by simpa only [bindIvar_currentFrame] using hk.origin,
        by simpa only [bindIvar_currentFrame] using hk.defFrame,
        by simpa only [hw.classPayload] using hk.detached,
        by simpa only [hw.frozen] using hk.unfrozen,
        by simpa only [hw.size] using hk.mainLive,
        by simpa only [hw.classOf_eq] using hk.notMain,
        by simpa only [bindIvar_currentFrame] using hk.superScope,
        by simpa only [bindIvar_currentFrame] using hk.methodOwner⟩⟩
    singletonRuntime := by
      intro cn hr
      obtain ⟨k, e, scope⟩ := h.singletonRuntime cn hr
      exact ⟨k, e, ⟨by simpa only [hn] using scope.named,
        by simpa only [hw.size] using scope.live,
        by rw [hw.eigen]; exact scope.cached,
        by simpa only [bindIvar_currentFrame] using scope.self,
        by simpa only [bindIvar_currentFrame] using scope.owner,
        by simpa only [bindIvar_currentFrame] using scope.cref,
        by simpa only [bindIvar_currentFrame] using scope.captured, hphase.trans scope.phase⟩⟩
    sat := ?_
    primitiveDispatch := by simpa only [primitiveDispatchB, nativeDispatchB, eachDispatchB,
      hmethod, hw.ancestors_eq, hshadow] using h.primitiveDispatch
    primitiveErrors := by simpa only [primitiveErrorsB, herr] using h.primitiveErrors
    primitiveInit := by simpa only [primitiveInitB, primitiveInitShapeB, errorInitOwn, hw.classPayload, hmethod, hw.ancestors_eq, hshadow] using h.primitiveInit
    stringPayload := by simpa only [StringPayloadOk, hw.classOf_eq, hw.payload] using h.stringPayload
    arrayPayload := by simpa only [ArrayPayloadOk, hw.classOf_eq, hw.payload] using h.arrayPayload
    hashPayload := by simpa only [HashPayloadOk, hw.classOf_eq, hw.payload, hd] using h.hashPayload
    frozenFields := h.frozenFields.bindIvar hfz
    core := ?_
    frameInRange := by simpa only [FrameInRange, bindIvar_stack, bindIvar_frames] using h.frameInRange
    env := he
    selfSpine := hi
    classes := by simpa only [ClassesOk, SingletonRows, ownCode, hn, hw.classPayload, hw.eigen] using h.classes
    ownNames := by simpa only [ClassOwnNames, ownMethods, hn, hw.classPayload] using h.ownNames
    classChains := h.classChains.heap hn hw.ancestors_eq
    rootInit := h.rootInit.transport id (hmethod _ _)
    defs := by simpa only [DefsOk, hw.classPayload] using h.defs
    asms := fun a ha n hl args hargs w n' hr =>
      h.asms a ha n ((bindIvar_later m x v).trans hl) args hargs w n' hr
    frame := by
      cases hf : κ.frame with
      | none => simpa only [FrameOk, hf, bindIvar_currentFrame] using h.frame
      | some f =>
        cases hs : f.singleton <;>
          simpa only [FrameOk, hf, Frame.recvTy, hs, Bool.false_eq_true, ↓reduceIte,
            denM, bindIvar_currentFrame, ha, isClassRefNamed, hn] using h.frame
    closures := trivial
    blockTy := hb
    selfTy := hs
    consts := hc
    constPaths := hp
    nested := by simpa only [NestedClassesOk, hn, hlookup, isClassRefNamed] using h.nested
    privConsts := trivial
    constScope := by simpa only [ConstScopeOk, hresolve, constLookup, hw.classPayload] using h.constScope
    exact := by simpa only [MethodsExact, hw.classPayload] using h.exact
    nameFree := by
      simpa only [NameFreeOk, nameFreeSites, bindIvar_currentFrame, hw.classOf_eq, hmethod]
        using h.nameFree
    bareFree := by simpa only [BareNameFree, bindIvar_currentFrame, hw.lookup_eq] using h.bareFree
    missFree := by simpa only [MissFree, bindIvar_currentFrame, hw.classOf_eq, hmethod] using h.missFree
    query := by simpa only [QueryOk, hmethod, hw.ancestors_eq, hshadow] using h.query
    clsQuery := by simpa only [ClsQueryOk, ClassQuerySite, hmethod, hw.classPayload,
      hw.classOf_eq, hw.ancestors_eq, hshadow] using h.clsQuery
    declCls := by simpa only [DeclClassOk, hn, hw.classPayload, hw.classOf_eq, hw.ancestors_eq,
      hmethod, hshadow, userInit?] using h.declCls
    baseChains := by simpa only [BaseChainsOk, hn, hw.ancestors_eq] using h.baseChains
    nilQuery := by simpa only [NilQueryOk, hmethod, hw.ancestors_eq, hshadow] using h.nilQuery
    selfLive := by simpa only [SelfLive, bindIvar_currentFrame, hw.size] using h.selfLive }
  · intro hr
    have hm := h.runtime hr
    refine ⟨by simpa only [bindIvar_currentFrame] using hm.self,
      by simpa only [bindIvar_currentFrame] using hm.owner,
      by simpa only [bindIvar_currentFrame] using hm.cref,
      by simpa only [bindIvar_currentFrame] using hm.captured,
      hphase.trans hm.phase, by simpa only [hw.size] using hm.live,
      by simpa only [hw.payload] using hm.payload,
      by simpa only [hw.classOf_eq, hw.ancestors_eq] using hm.chain,
      by simpa only [ha] using hm.object,
      by simpa only [hw.classPayload] using hm.classLive,
      by simpa only [objectHookQuietB, definitionHookQuietB, hw.lookup_eq] using hm.hook,
      by simpa only [hw.classPayload] using hm.detached,
      by simpa only [hw.frozen] using hm.unfrozen,
      by simpa only [bindIvar_currentFrame] using hm.origin,
      by simpa only [mainOwnNamesB, ownMethods, hw.classOf_eq, hw.classPayload] using hm.mainNames,
      ?_, by simpa only [objectClassFlagsB, hw.classPayload] using hm.classFlags,
      by simpa only [bindIvar_currentFrame] using hm.defFrame,
      by rw [singletonHooksQuietB_congr (h := m.heap)
        (by simp only [singletonHookSites, hw.classOf_eq])
        (fun k _ => hw.ancestors_eq k) (fun _ _ j _ => by rw [hw.classPayload])]; exact hm.singletonHooks⟩
    rw [show classHooksQuietB (Interp.bindIvar m x v).heap = classHooksQuietB m.heap from
      classHooksQuietB_congr
        (by simp only [objectCallbackPrefix, hw.classOf_eq, hw.ancestors_eq])
        (fun _ _ _ => by rw [hw.classPayload])]
    exact hm.classHooks
  · simpa only [HeapSaturated, Proof.Saturated, hw.size,
      Proof.modAncestors_go_congr hw.shape, Proof.ancestors_go_congr hw.shape] using h.sat
  · exact ⟨h.core.classReady.ivarOnly hw,
      h.core.rootNames.ivarOnly hw,
      by simpa only [hw.classOf_eq] using h.core.metaConstants.ivarOnly hw,
      by simpa only [hw.ancestors_eq] using h.core.basicSelf,
      by simpa only [hw.ancestors_eq] using h.core.moduleBasic,
      by simpa only [hn] using h.core.stringNamed,
      by simpa only [hw.ancestors_eq] using h.core.stringSelf,
      by simpa only [hw.ancestors_eq] using h.core.stringBasic,
      by simpa only [hn] using h.core.regexpNamed,
      by simpa only [hw.ancestors_eq] using h.core.regexpSelf,
      by simpa only [hw.ancestors_eq] using h.core.regexpBasic,
      by simpa only [hw.ancestors_eq] using h.core.procBasic,
      by simpa only [hw.ancestors_eq] using h.core.arrayBasic,
      by simpa only [hw.ancestors_eq] using h.core.hashBasic,
      by simpa only [constLookup, hw.classPayload] using h.core.coreNamed,
      by simpa only [hw.classOf_eq] using h.core.intMeta,
      by simpa only [hw.classOf_eq] using h.core.strMeta,
      by simpa only [hn] using h.core.namesInj⟩

#print axioms StateOk_bindIvar
end Checker.Soundness
