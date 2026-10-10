import Books.TypeSoundness.Conformance.Heap.ConstAdd
import Books.TypeSoundness.Checker.Guards.ConstGuards
import Books.TypeSoundness.Conformance.Class.ClassConstScopeActual

/-! Full conformance after binding a fresh top-level constant in a class-free context.
The new table entry is the only typed constant; everything else transports unchanged. -/
set_option autoImplicit false
namespace Checker.Soundness.ConstAdd
open RubyCore Checker RubyCore.Proof

theorem key_inj {a b : String} (h : constKey a = constKey b) : a = b := by
  simpa [constKey] using h

theorem key_ne_in {n owner cn : String} (hc : ':' ∉ n.toList) : constKeyIn owner cn ≠ constKey n := by
  intro h
  apply hc
  have h' := congrArg String.toList h
  simp [constKey, constKeyIn, String.toList_append] at h'
  rw [← h']
  simp

theorem getLocal_heap (m : Machine) (H : Heap) (x : String) :
    ({ m with heap := H } : Machine).getLocal x = m.getLocal x := by
  have go : ∀ (fuel : Nat) (fid : FrameId),
      Machine.getLocal.go ({ m with heap := H } : Machine) x fid fuel = Machine.getLocal.go m x fid fuel := by
    intro fuel
    induction fuel with
    | zero => intro fid; rfl
    | succ n ih =>
      intro fid
      simp only [Machine.getLocal.go, localFrameId_frames_eq (m := m) (n := { m with heap := H }) rfl]
      split
      · rfl
      · split
        · exact ih _
        · rfl
  exact go _ _

theorem fresh_of_global {κ : Ctx} {m : Machine} {n : String}
    (hg : GlobalConstsOk κ.pos.globalConsts m.heap) (hn : n ∉ κ.pos.globalConsts) :
    constLookup m.heap n = none := by
  rw [Subclass.const_eq_own]
  cases h : constOwn m.heap Boot.objectId n with
  | none => rfl
  | some w => exact absurd (hg n w h) hn

theorem state {κ : Ctx} {Γ : Env} {I τ : Ty} {m : Machine} {n : String} {v : Value}
    (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true) (hcls : κ.classes = [])
    (hco : κ.consts = []) (hfr : κ.frame = none) (hrc : κ.scope.runtimeClass = none)
    (hst : κ.selfTy = none) (hbt : κ.blockTy = none) (ha : κ.asms = [])
    (hgl : n ∉ κ.pos.globalConsts) (hres : n ∉ reservedConstNames) (hcolon : ':' ∉ n.toList)
    (hv : NonClassVal m.heap v) (hτ : denM τ m v) (hτfo : FirstOrder τ = true)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) (hIfo : FirstOrder I = true) :
    StateOk (constAddCtx κ n τ) Γ I { m with heap := constSetIn m.heap Boot.objectId n v } := by
  have hmain := hm.runtime hr
  have hO := hmain.classLive
  have hfresh := fresh_of_global hm.globalConsts hgl
  have hc := hm.core.classReady.chains
  have hp : DataPres m.heap (constSetIn m.heap Boot.objectId n v) :=
    dataPres hc hm.core.basicSelf hO hfresh hv
  let M : Machine := { m with heap := constSetIn m.heap Boot.objectId n v }
  have hpM : DataPres m.heap M.heap := hp
  have hden {σ : Ty} (hσ : FirstOrder σ = true) {w : Value} (hw : denM σ m w) : denM σ M w :=
    hpM.denM hσ hw
  have hnamed := named_eq hO hfresh hv
  have hobjChain := hm.core.classReady.objectChain
  have hmainLookup (cn : String) :
      constLookupFrom M.heap Boot.objectId cn = constLookup M.heap cn := by
    by_cases hcn : cn = n
    · subst hcn
      rw [lookup_self hO]
      have ho : constOwn M.heap Boot.objectId cn = some v := by
        rw [← Subclass.const_eq_own]; exact lookup_self hO
      rw [FreshClassActual.const_from_eq_firstM, anc, hobjChain]
      simp only [List.firstM, ho]; rfl
    · rw [from_ne hcn, lookup_ne hcn]
      rw [← constResolveAt_top hmain.cref]
      exact hm.constScope cn
  have hfall {k : ObjId} (hk : ConstFallback m.heap k) : ConstFallback M.heap k := by
    intro cn hcn
    by_cases he : cn = n
    · subst he; rw [lookup_self hO] at hcn; cases hcn
    · rw [from_ne he]; rw [lookup_ne he] at hcn; exact hk cn hcn
  have hnf : nameFreeN (constAddCtx κ n τ) = nameFreeN κ := rfl
  have hsel : (constAddCtx κ n τ).selfTy = κ.selfTy := rfl
  have hcf : ({ m with heap := constSetIn m.heap Boot.objectId n v } : Machine).currentFrame =
      m.currentFrame := rfl
  have hgl (x : String) : ({ m with heap := constSetIn m.heap Boot.objectId n v } : Machine).getLocal x =
      m.getLocal x := getLocal_heap m _ x
  have hmethods (k : ObjId) := metaEq (n := n) (v := v) (h := m.heap) ClassPayload.methods (fun _ => rfl) k
  exact {
    runtime := fun _ => mainReady hmain hO hfresh hv
    mainSite := fun hw => by
      have site := hm.mainSite hw
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact mainReady (m := mainView m.heap) site.ready hO hfresh hv
      · intro nm hnm owner md hl
        rw [classOf_eq, methodOn_eq] at hl
        exact site.names nm hnm owner md hl
      · intro nm hb hf; rw [lookup_eq]; exact site.bare nm hb hf
      · intro hf owner md hl
        rw [classOf_eq, methodOn_eq] at hl
        exact site.missing hf owner md hl
      · intro cn
        exact hmainLookup cn
      · intro hf
        exact (site.newDispatch hf).transport (by rw [classOf_eq, methodOn_eq])
          (fun owner => by rw [classOf_eq, anc, shadow_eq])
    moduleBase := by
      have b := hm.moduleBase
      refine ⟨?_, ?_, hfall b.constants⟩
      · intro nm hnm owner md hl
        rw [methodOn_eq] at hl
        exact b.names nm hnm owner md hl
      · simpa only [moduleHookQuietB, methodOn_eq] using b.hook
    classRuntime := by intro cn h; change κ.scope.runtimeClass = some cn at h; rw [hrc] at h; cases h
    singletonRuntime := by
      intro cn h
      obtain ⟨k, e, scope⟩ := hm.singletonRuntime cn h
      exact ⟨k, e, ⟨by rw [hnamed]; exact scope.named, by simpa only [size] using scope.live,
        by rw [(fields k).2.2.1]; exact scope.cached, scope.self, scope.owner, scope.cref,
        scope.captured, scope.phase⟩⟩
    classSites := by
      intro cn hcn
      change cn ∈ κ.classes.map (·.name) ++ κ.scope.runtimeClass.toList at hcn
      simp [hcls, hrc] at hcn
    allocators := by
      intro cn hcn
      obtain ⟨k, hk, hpa⟩ := hm.allocators cn hcn
      exact ⟨k, by rw [hnamed]; exact hk, hpa.transport (by rw [size]; exact Nat.le_refl _)
        (metaEq (·.isModule) (fun _ => rfl) k) (anc k)
        (by simp only [plainAllocationReadyB]; exact anyEq allocationReadyB (fun _ => rfl) k)⟩
    globalConsts := by
      intro cn w hw
      by_cases he : cn = n
      · subst he; exact List.mem_cons_self
      · apply List.mem_cons_of_mem
        rw [constOwn_constSetIn_ne _ _ _ _ _ _ (Or.inr he)] at hw
        exact hm.globalConsts cn w hw
    sat := by
      simpa only [HeapSaturated] using RubyCore.Proof.saturated_constSetIn hm.sat
    primitiveDispatch := by
      simpa only [primitiveDispatchB, nativeDispatchB, eachDispatchB, methodOn_eq, anc, shadow_eq, hnf, hcf]
        using hm.primitiveDispatch
    primitiveErrors := by
      have herr : primitiveErrorB (constSetIn m.heap Boot.objectId n v) = primitiveErrorB m.heap := by
        funext cls; simp only [primitiveErrorB, anc]
      simpa only [primitiveErrorsB, herr] using hm.primitiveErrors
    primitiveInit := by
      have heo (k : ObjId) : errorInitOwn (constSetIn m.heap Boot.objectId n v) k = errorInitOwn m.heap k :=
        by unfold errorInitOwn
           exact bindEq (n := n) (v := v) (h := m.heap) (α := MethodDef)
            (fun cp : ClassPayload => (cp.methods.find? (fun p : String × MethodDef => p.1 == "initialize")).map
              (fun p => p.2)) (fun _ => rfl) k
      simpa only [primitiveInitB, primitiveInitShapeB, heo, methodOn_eq, anc, shadow_eq]
        using hm.primitiveInit
    stringPayload := by
      intro o ho
      rw [classOf_eq] at ho
      obtain ⟨st, hs⟩ := hm.stringPayload o ho
      by_cases hob : o = Boot.objectId
      · subst hob
        obtain ⟨cp, hcp⟩ := Option.isSome_iff_exists.mp hO
        unfold Heap.classPayload? at hcp
        rw [hs] at hcp; cases hcp
      · exact ⟨st, by rw [get_ne hob]; exact hs⟩
    arrayPayload := by
      intro o xs hx
      rw [classOf_eq]
      by_cases hob : o = Boot.objectId
      · subst hob
        have hs := (isSome_eq (n := n) (v := v) (h := m.heap) Boot.objectId).trans hO
        unfold Heap.classPayload? at hs; rw [hx] at hs; cases hs
      · rw [get_ne hob] at hx; exact hm.arrayPayload o xs hx
    hashPayload := by
      intro o xs hx
      by_cases hob : o = Boot.objectId
      · subst hob
        have hs := (isSome_eq (n := n) (v := v) (h := m.heap) Boot.objectId).trans hO
        unfold Heap.classPayload? at hs; rw [hx] at hs; cases hs
      · rw [get_ne hob] at hx ⊢
        obtain ⟨h1, h2⟩ := hm.hashPayload o xs hx
        exact ⟨by rw [classOf_eq]; exact h1, h2⟩
    frozenFields := by
      intro k hk
      rw [(fields k).2.2.2] at hk
      rw [(fields k).1]; exact hm.frozenFields k hk
    core := by
      have hcr := hm.core.classReady
      have hres' : n ∉ coreClsNames := by
        have : coreClsNames = reservedConstNames := rfl
        rw [this]; exact hres
      refine ⟨⟨by rw [size]; exact hcr.bootEnd, chainsIn_constSetIn hcr.chains,
        by simpa only [(fields _).2.2.1, anc] using hcr.objectEigen,
        by simpa only [anc] using hcr.classBasic,
        by simpa only [(fields _).2.2.1] using hcr.eigenSeparate, ?_,
        by simpa only [anc] using hcr.objectChain⟩,
        hm.core.rootNames.transport hnamed,
        by rw [classOf_eq]; exact hfall hm.core.metaConstants,
        by simpa only [anc] using hm.core.basicSelf,
        by simpa only [anc] using hm.core.moduleBasic,
        by rw [hnamed]; exact hm.core.stringNamed,
        by simpa only [anc] using hm.core.stringSelf,
        by simpa only [anc] using hm.core.stringBasic,
        by rw [hnamed]; exact hm.core.regexpNamed,
        by simpa only [anc] using hm.core.regexpSelf,
        by simpa only [anc] using hm.core.regexpBasic,
        by simpa only [anc] using hm.core.procBasic,
        by simpa only [anc] using hm.core.arrayBasic,
        by simpa only [anc] using hm.core.hashBasic, ?_,
        by rw [classOf_eq]; exact hm.core.intMeta,
        by rw [classOf_eq]; exact hm.core.strMeta,
        by simpa only [hnamed] using hm.core.namesInj⟩
      · intro cn k hk
        rw [size]
        by_cases he : cn = n
        · subst he
          rw [RubyCore.Proof.Judgment.constOwn_constSetIn_self hO (lt_size_of_classPayload hO)] at hk
          cases hk; exact (hv k rfl).2
        · rw [constOwn_constSetIn_ne _ _ _ _ _ _ (Or.inr he)] at hk
          exact hcr.constRefs cn k hk
      · intro cn hcn w hw
        have he : cn ≠ n := fun h => hres' (h ▸ hcn)
        rw [lookup_ne he] at hw
        obtain ⟨o, rfl, hp'⟩ := hm.core.coreNamed cn hcn w hw
        exact ⟨o, rfl, by rw [isSome_eq]; exact hp'⟩
    frameInRange := hm.frameInRange
    env := ⟨fun x σ hx => ⟨by
          have hmem : ∃ p ∈ Γ, p.2 = σ := by
            unfold envGet? at hx
            cases hf : Γ.find? (·.1 == x) with
            | none => rw [hf] at hx; cases hx
            | some p => rw [hf] at hx; cases hx; exact ⟨p, List.mem_of_find?_eq_some hf, rfl⟩
          obtain ⟨p, hpm, rfl⟩ := hmem
          rw [hgl]; exact hden (hΓ p hpm) (hm.env.1 x _ hx).1,
        by simpa only [hgl] using (hm.env.1 x σ hx).2⟩, fun x hx => by rw [hgl]; exact hm.env.2 x hx⟩
    selfSpine := by
      have hss := hm.selfSpine
      have hiv : ivarOf (constSetIn m.heap Boot.objectId n v) m.currentFrame.self =
          ivarOf m.heap m.currentFrame.self := by
        funext x; cases hs : m.currentFrame.self <;> simp [ivarOf, (fields _).1]
      refine ⟨?_, ?_⟩
      · change denSpineFrom [] I _ (ivarOf (constSetIn m.heap Boot.objectId n v) m.currentFrame.self)
        rw [hiv]
        exact (hpM.denM_aux I hIfo).2 [] _ hss.1
      · intro x hx hcl
        change ivarOf (constSetIn m.heap Boot.objectId n v) m.currentFrame.self x = .nil
        rw [hiv]; exact hss.2 x hx hcl
    classes := by intro c hc'; change c ∈ κ.classes at hc'; rw [hcls] at hc'; cases hc'
    ownNames := by intro c hc'; change c ∈ κ.classes at hc'; rw [hcls] at hc'; cases hc'
    classChains := by intro c hc'; change c ∈ κ.classes at hc'; rw [hcls] at hc'; cases hc'
    rootInit := hm.rootInit.transport id (methodOn_eq _ _)
    defs := by
      intro d hd
      obtain ⟨h1, md, h2, rest⟩ := hm.defs d hd
      refine ⟨h1, md, ?_, rest⟩
      rw [bindEq (n := n) (v := v) (h := m.heap) (α := MethodDef)
        (fun cp : ClassPayload => (cp.methods.find? (fun p : String × MethodDef => p.1 == d.name)).map
          (fun p => p.2)) (fun _ => rfl)]
      exact h2
    asms := by intro a h; change a ∈ κ.asms at h; rw [ha] at h; cases h
    frame := by
      change FrameOk κ.frame _
      have hf := hm.frame
      rw [hfr] at hf ⊢
      simpa only [FrameOk, hcf] using hf
    closures := trivial
    blockTy := by
      change BlockTyOk κ.blockTy _
      have hb := hm.blockTy
      rw [hbt] at hb ⊢
      simpa only [BlockTyOk, hcf] using hb
    selfTy := by change SelfTyOk κ.selfTy _; rw [hst]; trivial
    consts := by
      intro cn σ hσ
      have hσ' : envGet? [(constKey n, τ)] (constKey cn) = some σ := by
        change (constPaths (constAddCtx κ n τ) cn).findSome?
          (fun k => envGet? (envSet κ.pos.consts (constKey n) τ) k) = _ at hσ
        have hpaths : constPaths (constAddCtx κ n τ) cn = [constKey cn] := by
          have hfr' : (constAddCtx κ n τ).frame = none := hfr
          simp [constPaths, hfr']
        have hc0 : κ.pos.consts = [] := hco
        rw [hpaths, hc0] at hσ
        simpa [envSet] using hσ
      by_cases he : constKey n = constKey cn
      · have hcn := key_inj he
        subst hcn
        simp [envGet?] at hσ'
        subst hσ'
        refine ⟨v, ?_, hden hτfo hτ⟩
        rw [constResolveAt_top (by rw [hcf]; exact hmain.cref), hmainLookup, lookup_self hO]
      · simp [envGet?, he] at hσ'
    constPaths := by
      intro owner cn σ k hk
      change envGet? (envSet κ.pos.consts (constKey n) τ) _ = _ at hk
      have hc0 : κ.pos.consts = [] := hco
      rw [hc0] at hk
      have hne := key_ne_in (owner := owner) (cn := cn) hcolon
      simp [envSet, envGet?, Ne.symm hne] at hk
    nested := by
      intro owner cn c hc'
      change clsGet? κ.classes _ = _ at hc'
      rw [hcls] at hc'; simp [clsGet?] at hc'
    privConsts := trivial
    constScope := by
      intro cn
      rw [constResolveAt_top (by rw [hcf]; exact hmain.cref)]
      exact hmainLookup cn
    exact := by
      intro k cp hk nm md hmem hu
      have hmm := metaEq (n := n) (v := v) (h := m.heap) ClassPayload.methods (fun _ => rfl) k
      rw [hk] at hmm
      cases h0 : m.heap.classPayload? k with
      | none => rw [h0] at hmm; cases hmm
      | some cp0 =>
        rw [h0] at hmm
        have heq : cp.methods = cp0.methods := Option.some.inj hmm
        exact hm.exact k cp0 h0 nm md (heq ▸ hmem) hu
    nameFree := by
      simpa only [NameFreeOk, nameFreeSites, classOf_eq, methodOn_eq, hnf, hcf] using hm.nameFree
    bareFree := by simpa only [BareNameFree, lookup_eq, hnf, hcf, hsel] using hm.bareFree
    missFree := by simpa only [MissFree, classOf_eq, methodOn_eq, hnf, hcf, hsel] using hm.missFree
    query := by simpa only [QueryOk, methodOn_eq, anc, shadow_eq, hnf, hcf] using hm.query
    clsQuery := by
      simpa only [ClsQueryOk, ClassQuerySite, methodOn_eq, isSome_eq, classOf_eq, anc, shadow_eq, hnf]
        using hm.clsQuery
    declCls := by intro c hc'; change c ∈ κ.classes at hc'; rw [hcls] at hc'; cases hc'
    baseChains := by
      change BaseChainsOk κ _
      simpa only [BaseChainsOk, hnamed, anc] using hm.baseChains
    nilQuery := by simpa only [NilQueryOk, methodOn_eq, anc, shadow_eq, hnf, hcf, hnf, hcf] using hm.nilQuery
    selfLive := by simpa only [SelfLive, size, hnf, hcf] using hm.selfLive
    names := namesOk_constSetIn hm.names _ _ _
    localAlias := hm.localAlias
    capturedLive := hm.capturedLive.frames_preserved (by simp) (fun _ _ => by simp)
    rootClean := hm.rootClean }

end Checker.Soundness.ConstAdd
