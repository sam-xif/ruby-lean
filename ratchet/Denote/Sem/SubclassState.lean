import Ratchet.ClassCtx
import Denote.Sem.ClassNative
import Denote.Sem.SubclassTables
import Denote.Sem.SubclassGlobals
import Denote.Sem.SubclassMain
import Denote.Sem.SubclassSites
import Denote.Sem.SubclassNameEntry
import Denote.Sem.SubclassBases

/-! Full conformance at fresh subclass-body entry. ParentCaps packages existing input
facts; it is not a new state invariant or a certificate route. No new body is accepted here. -/
set_option autoImplicit false
namespace Ratchet.Denote.Subclass
open RubyCore Ratchet

structure ParentCaps (κ : Ctx) (h : Heap) (parent : ObjId) : Prop where
  classLive : (h.classPayload? parent).isSome = true
  metaclass : MetaReady h parent
  hook : definitionHookQuietB h parent = true
  constants : ∀ cn, (constLookup h cn).orElse (fun _ => constLookupFrom h parent cn) = constLookup h cn
  names : NamesAt (nameFreeN κ) h parent
  classNames : NamesAt (nameFreeN κ) h (classOf h (.ref parent))
  bases : ∀ base ch, (base, ch) ∈ builtinBases → isANoOk κ.wholeCls ch = true → parent ≠ base

theorem ParentCaps.of_main {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true) : ParentCaps κ m.heap Boot.objectId := by
  have ready := hm.runtime hr
  exact ⟨ready.classLive, hm.core.classReady.metaObject, ready.hook,
    fallback_of_main ready.cref ready.owner hm.constScope,
    fun n hn owner md hmd => hm.nameFree n hn _ (by simp [nameFreeSites]) owner md hmd,
    fun n hn owner md hmd => hm.nameFree n hn _ (by simp [nameFreeSites]) owner md hmd,
    fun _ _ hb _ => (builtinBase_bound hb).2.symm⟩

theorem ParentCaps.of_declared {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {c : Cls} {parent : ObjId} (hm : StateOk κ Γ I m) (hc : c ∈ κ.classes)
    (hp : classNamed? m.heap c.name = some parent) (hb : subclassBaseFrameB κ c.name = true) :
    ParentCaps κ m.heap parent := by
  have site := hm.classSites.at_class hc hp
  refine ⟨?_, site.metaclass, site.hook, fallback_of_instance site.constants,
    site.names, site.classNames, fun _ _ hbase hneg => hm.subclass_parent_separate hc hp hb hbase hneg⟩
  simpa using congrArg Option.isSome (hm.declCls c hc parent hp).2.2.2.1

variable {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
variable {name : String} {parent eParent : ObjId} {body : RubyCore.Expr}
local notation "entry" => machine m Boot.objectId m.currentFrame.cref name name parent eParent body

theorem state (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true)
    (hf : κ.frame = none) (ha : κ.asms = [])
    (ht : ClassTablesFrame κ name m) (hq : FreshClass.NativeFrame κ name)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false)
    (hp : ParentCaps κ m.heap parent) (he : (m.heap.get parent).eigen = some eParent) :
    StateOk (classBodyCtx κ name) [] .ivar0 entry := by
  have hc := hm.core.classReady.chains
  have ho := hc.boot.2.2.2.2
  have hl := lt_size_of_classPayload hp.classLive
  have hel := hc.eigen parent hl eParent he
  have hmain := hm.runtime hr
  obtain ⟨ep, he', hb, hsep⟩ := hp.metaclass
  rw [he] at he'; cases he'
  have hnames : NamesAt (nameFreeN κ) m.heap eParent := by simpa only [classOf, he] using hp.classNames
  have hscope : ConstScopeOk entry := const_scope hc hm.sat hmain.classLive hl hmain.cref hp.constants
  have hd : DataPres m.heap (entry).heap := dataPres hm.core.classReady hm.sat hm.core.basicSelf hn hel hb
  have hconst : ConstsOk κ entry := constants ho hn rfl hd hm.constScope hscope ht.consts hm.consts
  exact {
    runtime := by intro h; cases h
    mainSite := fun hr => mainSite (hm.mainSite hr) hc hm.sat hd
    allocators := allocators hc hm.sat hn hm.allocators
    globalConsts := globalConsts ho hm.globalConsts
    classRuntime := by
      intro cn hr
      change some name = some cn at hr
      cases hr
      exact scope_ready hc hm.sat hmain.classLive hl he hp.hook hmain.cref hmain.phase
    classSites := by
      intro cn hcn
      change cn ∈ κ.classes.map (·.name) ++ [name] at hcn
      rcases List.mem_append.mp hcn with hcn | hcn
      · obtain ⟨k, site⟩ := hm.classSites cn (List.mem_append_left _ hcn)
        exact ⟨k, instanceSite_old site hc hm.sat hmain.classLive hn⟩
      · have heq := List.mem_singleton.mp hcn
        subst cn
        exact ⟨m.heap.objs.size, instanceSite hc hm.sat hmain.classLive hl he hb hp.hook hp.constants hp.names hnames⟩
    sat := saturated hc hm.sat hl hel
    primitiveDispatch := (primitiveDispatch hc hm.sat _).trans hm.primitiveDispatch
    primitiveErrors := (primitiveErrors hc hm.sat).trans hm.primitiveErrors
    stringPayload := stringPayload hc hm.stringPayload
    arrayPayload := arrayPayload hm.arrayPayload
    hashPayload := hashPayload hm.hashPayload
    core := core hm.core hm.sat hmain.classLive hn hl hel
    frameInRange := frame_in_range
    env := env_empty
    selfSpine := spine_empty
    classes := classes ho hn rfl hm.classes
    ownNames := ownNames ho hn hm.classes hm.ownNames
    classChains := classChains hm.core.classReady hm.sat hn hm.classes hm.classChains
    rootInit := hm.rootInit.transport id (method_old hc hm.sat ho "initialize")
    defs := defs rfl hm.defs
    asms := by
      intro a ham
      change a ∈ κ.asms at ham
      rw [ha] at ham
      cases ham
    frame := frame_ok
    closures := trivial
    blockTy := block_none
    selfTy := self_type hmain.classLive
    consts := fun cn τ hct => hconst cn τ (by rwa [classBodyCtx_constGet hf] at hct)
    constPaths := paths (κ := κ) hc hm.sat hn rfl hd ht hm.constPaths
    nested := nested (κ := κ) hc hm.sat hn rfl hd ht hm.nested
    privConsts := trivial
    constScope := hscope
    exact := methodsExact rfl hm.exact
    nameFree := nameFree hc hm.sat hel hnames hm.nameFree
    bareFree := by intro _ _ _ hself; cases hself
    missFree := by intro _ hself; cases hself
    query := query hc hm.sat hl hel hne hq.query rfl hm.query
    clsQuery := clsQuery hc hm.sat hp.classLive he hne hq.clsQuery rfl hm.clsQuery
    declCls := declared hc hm.sat hmain.classLive hn rfl hm.classes hm.declCls
    baseChains := baseChains hm.core.classReady hm.sat hmain.classLive hn hl hel hp.bases hsep rfl hm.baseChains
    nilQuery := nilQuery hc hm.sat hl hel hne hq.nilQuery rfl hm.nilQuery
    selfLive := self_live }

#print axioms ParentCaps.of_main
#print axioms ParentCaps.of_declared
#print axioms state
end Ratchet.Denote.Subclass
