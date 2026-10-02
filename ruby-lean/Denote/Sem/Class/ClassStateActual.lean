import Ratchet.Guards.ClassCtx
import Denote.Sem.Class.ClassNative
import Denote.Sem.Class.ClassTablesActual
import Denote.Sem.Class.ClassMainActual
import Denote.Sem.Class.ClassSitesActual
import Denote.Sem.Class.ClassBasesActual
import Denote.Sem.Class.ClassPrimitiveInitActual
import Denote.Sem.Class.ClassAllocatorsActual
import Denote.Sem.Class.ClassPayloadActual
import Denote.Sem.Class.ClassNameEntryActual

/-! Repair the original full body-entry record using actual registration and callbacks.
The reachability premise is explicit: current constant equality alone cannot supply it. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClassActual
open RubyCore Ratchet RubyCore.Proof
/-- Parent-class facts consumed by fresh class entry; Object's come from main. -/
structure ParentFacts (κ : Ctx) (h : Heap) (p e : ObjId) : Prop where
  live : p < h.objs.size
  classLive : (h.classPayload? p).isSome = true
  eigen : (h.get p).eigen = some e
  metaReady : MetaReady h p
  hook : definitionHookQuietB h p = true
  names : NamesAt (nameFreeN κ) h p
  classNames : NamesAt (nameFreeN κ) h e
  metaConstants : ConstFallback h e
  singletonHook : singletonDefHookQuietB h p = true
  bases : ∀ base ch, (base, ch) ∈ builtinBases → p ≠ base ∧ e ≠ base
  inheritedHook : (lookup h (.ref p) "inherited").any (fun (_, md) =>
    !md.undefined && md.builtin == some "Class#inherited") = true

variable {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
variable {name : String} {e : ObjId} {body : RubyCore.Expr} {p : ObjId}
local notation "entry" => machine m name e body p

theorem stateAt (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true)
    (hf : κ.frame = none) (ha : κ.asms = [])
    (ht : ClassTablesFrame κ name m) (hq : FreshClass.NativeFrame κ name)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false)
    (hp : ParentFacts κ m.heap p e)
    (hpc : ∀ cn, constLookupFrom (heap m name e p) p cn = constLookup (heap m name e p) cn)
    (hreach : ∀ cn ∈ κ.classes.map (·.name), ∀ k, InstanceSite κ cn k m.heap →
      Boot.objectId ∈ ancestors m.heap k ∨ (m.heap.classPayload? k).any (·.isModule) = true) :
    StateOk (classBodyCtx κ name) [] .ivar0 entry := by
  have hc := hm.core.classReady.chains
  have ho := hc.boot.2.2.2.2
  have hmain := hm.runtime hr
  have htop : m.lexicalNamespace = Boot.objectId := by
    simp only [Machine.lexicalNamespace, hmain.cref, List.headD_nil]
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ ho
  have he := hp.eigen
  have hpl := hp.live
  have hel := hc.eigen _ hpl _ he
  obtain ⟨ep, he', hb, _⟩ := hp.metaReady
  rw [he] at he'; cases he'
  have hconst (cn : String) : constLookupFrom m.heap Boot.objectId cn = constLookup m.heap cn := by
    rw [← constResolveAt_top hmain.cref]; exact hm.constScope cn
  have hnames : NamesAt (nameFreeN κ) m.heap e := hp.classNames
  have hinst : NamesAt (nameFreeN κ) m.heap p := hp.names
  have hscope : ConstScopeOk entry := const_scopeAt hm.core.classReady hm.sat hmain hpl hpc
  have hdata : DataPres m.heap (entry).heap :=
    dataPres hm.core.classReady hm.sat hm.core.basicSelf htop hn hel hb
  have htyped : ConstsOk κ entry :=
    constants htop ho hn rfl hdata hm.constScope hscope ht.consts hm.consts
  exact {
    runtime := by intro h; cases h
    mainSite := fun hr => mainSite hm.names (hm.mainSite hr) hm.core.classReady hm.sat htop rfl hdata
    moduleBase := moduleBase hm.moduleBase hc hm.sat htop hmain.classLive
    allocators := allocators hc hm.sat htop hn hm.allocators
    globalConsts := globalConsts htop ho hm.globalConsts
    singletonRuntime := by intro cn h; cases h
    classRuntime := by
      intro cn hr
      change some name = some cn at hr
      cases hr
      exact scope_ready hc hm.sat hpl he hp.hook hmain
    classSites := by
      intro cn hcn
      change cn ∈ κ.classes.map (·.name) ++ [name] at hcn
      rcases List.mem_append.mp hcn with hcn | hcn
      · obtain ⟨k, site⟩ := hm.classSites cn (List.mem_append_left _ hcn)
        exact ⟨k, instanceSite_old site hm.core.classReady hm.sat htop hmain.classLive hn hconst
          (hreach cn hcn k site)⟩
      · have heq := List.mem_singleton.mp hcn
        subst cn
        exact ⟨m.heap.objs.size, instanceSiteAt hm.core.classReady hm.sat htop hmain.classLive hpl
          hp.metaReady he hp.hook hpc hinst hnames hp.metaConstants
          hm.core.classReady.bootEnd hmain.live hp.singletonHook hp.inheritedHook⟩
    sat := saturated hc hm.sat hd hel hpl
    primitiveDispatch := (primitiveDispatch hm.names hc hm.sat hd _).trans hm.primitiveDispatch
    primitiveErrors := (primitiveErrors hc hm.sat hd).trans hm.primitiveErrors
    primitiveInit := (primitiveInit hm.core.classReady hm.sat hm.names hd).trans hm.primitiveInit
    stringPayload := stringPayload hc hd hm.stringPayload
    arrayPayload := arrayPayload hd hm.arrayPayload
    hashPayload := hashPayload hd hm.hashPayload
    frozenFields := frozenFields hd hm.frozenFields
    core := core hm.core hm.sat htop hmain.classLive hn hpl he
    frameInRange := frame_in_range
    env := env_empty
    selfSpine := spine_empty hd
    classes := classes htop ho hn rfl hm.classes
    ownNames := ownNames htop ho hn hm.classes hm.ownNames
    classChains := classChains hm.core.classReady hm.sat htop hn hm.classes hm.classChains
    rootInit := hm.rootInit.transport id (method_old hc hm.sat hd ho "initialize")
    defs := defs hd rfl hm.defs
    asms := by
      intro a ham
      change a ∈ κ.asms at ham
      rw [ha] at ham
      cases ham
    frame := frame_ok
    closures := trivial
    blockTy := block_none
    selfTy := self_type htop hmain.classLive
    consts := fun cn τ hct => htyped cn τ (by rwa [classBodyCtx_constGet hf] at hct)
    constPaths := paths (κ := κ) hc hm.sat htop hn rfl hdata ht hm.constPaths
    nested := nested (κ := κ) hc hm.sat htop hn rfl hdata ht hm.nested
    privConsts := trivial
    constScope := hscope
    exact := methodsExact hd rfl hm.exact
    nameFree := nameFree hc hm.sat hd hel hnames hm.nameFree
    bareFree := by intro _ _ _ hself; cases hself
    missFree := by intro _ hself; cases hself
    query := query hm.names hc hm.sat hd hmain.live hel hpl hne hq.query rfl hm.query
    clsQuery := clsQuery hm.names hc hm.sat hd hmain.live hp.classLive he hne hq.clsQuery rfl hm.clsQuery
    declCls := declared hm.names hc hm.sat htop hmain.classLive hn rfl hm.classes hm.declCls
    baseChains := baseChains hm.core.classReady hm.sat htop hmain.classLive hn hpl he
      hp.bases rfl hm.baseChains
    nilQuery := nilQuery hm.names hc hm.sat hd hmain.live hel hpl hne hq.nilQuery rfl hm.nilQuery
    selfLive := self_live
    names := namesOk hc hm.names hd hne
    localAlias := local_alias
    capturedLive := captured_live
    rootClean := root_clean hm.rootClean }


theorem ParentFacts.object {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {e : ObjId}
    (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true)
    (he : (m.heap.get Boot.objectId).eigen = some e) : ParentFacts κ m.heap Boot.objectId e := by
  have hc := hm.core.classReady
  have hmain := hm.runtime hr
  refine ⟨hc.chains.boot.2.2.2.2, hmain.classLive, he, hc.metaObject, hmain.hook, ?_, ?_,
    by simpa only [classOf, he] using hm.core.metaConstants, ?_,
    fun base ch hb => ⟨fun h => (builtinBase_bound hb).2 h.symm, hc.eigenSeparate e he base ch hb⟩, ?_⟩
  · intro n hn owner md hmd
    exact hm.nameFree n hn _ (by simp [nameFreeSites]) owner md hmd
  · intro n hn owner md hmd
    apply hm.nameFree n hn e _ owner md hmd
    simp only [nameFreeSites, classOf, he]
    simp
  · exact singletonDefHookQuietB_of_methodOn (by simp only [classOf, he]; rfl)
      (by have hco : e = classOf m.heap (.ref Boot.objectId) := by simp only [classOf, he]
          rw [hco]
          exact singletonHooksQuietB_methodOn hmain.singletonHooks hc.chains
            (by simp [singletonHookSites]))
  · obtain ⟨owner, md, hl, hu, hb⟩ := classHooksQuietB_lookup hmain.classHooks hc.chains
      (by simp [classHookNames] : ("inherited", "Class#inherited") ∈ classHookNames)
    simp [hl, hu, hb]

theorem state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {name : String} {e : ObjId}
    {body : RubyCore.Expr} (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true)
    (hf : κ.frame = none) (ha : κ.asms = [])
    (ht : ClassTablesFrame κ name m) (hq : FreshClass.NativeFrame κ name)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false)
    (he : (m.heap.get Boot.objectId).eigen = some e)
    (hreach : ∀ cn ∈ κ.classes.map (·.name), ∀ k, InstanceSite κ cn k m.heap →
      Boot.objectId ∈ ancestors m.heap k ∨ (m.heap.classPayload? k).any (·.isModule) = true) :
    StateOk (classBodyCtx κ name) [] .ivar0 (machine m name e body) := by
  have hmain := hm.runtime hr
  have htop : m.lexicalNamespace = Boot.objectId := by
    simp only [Machine.lexicalNamespace, hmain.cref, List.headD_nil]
  have hconst (cn : String) : constLookupFrom m.heap Boot.objectId cn = constLookup m.heap cn := by
    rw [← constResolveAt_top hmain.cref]; exact hm.constScope cn
  exact stateAt hm hr hf ha ht hq hn hne (ParentFacts.object hm hr he)
    (main_constants hm.core.classReady hm.sat htop hmain.classLive hconst) hreach

#print axioms stateAt
#print axioms state
end Ratchet.Denote.FreshClassActual
