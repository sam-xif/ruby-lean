import Ratchet.Guards.ModuleHeader
import Denote.Sem.Class.ClassNative
import Denote.Sem.Module.ModuleTables
import Denote.Sem.Module.ModuleGlobals
import Denote.Sem.Module.ModuleMain
import Denote.Sem.Module.ModuleSites
import Denote.Sem.Module.ModuleNameEntry
import Denote.Sem.Module.ModuleBases
import Denote.Sem.Module.ModuleQueries

/-! Full conformance at real fresh module-body entry. The shared lexical scope does
not grant ordinary-class ancestry or allocation; the retained Module base supplies dispatch. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshModule
open RubyCore Ratchet RubyCore.Proof.Judgment

variable {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
variable {name : String} {body : RubyCore.Expr}
local notation "entry" => freshModMachine m Boot.objectId m.currentFrame.cref name name body

theorem state (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true)
    (hf : κ.frame = none) (ha : κ.asms = [])
    (ht : ClassTablesFrame κ name m) (hq : FreshClass.NativeFrame κ name)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false) :
    StateOk (moduleBodyCtx κ name) [] .ivar0 entry := by
  have hc := hm.core.classReady.chains
  have ho := hc.boot.2.2.2.2
  have hmain := hm.runtime hr
  have hscope : ConstScopeOk entry := const_scope hmain.cref
  have hd : DataPres m.heap (entry).heap := dataPres hm.core.classReady hm.sat hm.core.basicSelf hn hm.core.moduleBasic
  have hconst : ConstsOk κ entry := constants ho hn rfl hd hm.constScope hscope ht.consts hm.consts
  exact {
    runtime := by intro h; cases h
    mainSite := fun hr => mainSite hm.names (hm.mainSite hr) hc hm.sat hd
    moduleBase := moduleBase hm.moduleBase hc hm.sat hmain.classLive
    allocators := allocators hc hm.sat hn hm.allocators
    globalConsts := globalConsts ho hm.globalConsts
    singletonRuntime := by intro cn h; cases h
    classRuntime := by
      intro cn hr
      change some name = some cn at hr
      cases hr
      exact scope_ready hm.moduleBase hc hm.sat hmain.classLive hmain.cref hmain.phase
    classSites := by
      intro cn hcn
      change cn ∈ κ.classes.map (·.name) ++ [name] at hcn
      rcases List.mem_append.mp hcn with hcn | hcn
      · obtain ⟨k, site⟩ := hm.classSites cn (List.mem_append_left _ hcn)
        exact ⟨k, instanceSite_old site hc hm.sat hmain.classLive hn⟩
      · have heq := List.mem_singleton.mp hcn
        subst cn
        exact ⟨m.heap.objs.size, instanceSite hm.moduleBase hc hm.sat hmain.classLive hm.core.moduleBasic⟩
    sat := saturated_fresh hc hm.sat ho
    primitiveDispatch := (primitiveDispatch hm.names hc hm.sat _).trans hm.primitiveDispatch
    primitiveErrors := (primitiveErrors hc hm.sat).trans hm.primitiveErrors
    stringPayload := stringPayload hc hm.stringPayload
    arrayPayload := arrayPayload hm.arrayPayload
    hashPayload := hashPayload hm.hashPayload
    core := core hm.core hm.sat hmain.classLive hn
    names := namesOk hc hm.names hne
    localAlias := by rw [current_frame]; rfl
    capturedLive := by rw [current_frame]; exact .none
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
    nameFree := nameFree hc hm.sat hm.moduleBase hm.nameFree
    bareFree := by intro _ _ _ hself; cases hself
    missFree := by intro _ hself; cases hself
    query := query hm.names hc hm.sat hne hq.query rfl hm.query
    clsQuery := clsQuery hm.names hc hm.sat hne hq.clsQuery rfl hm.clsQuery
    declCls := declared hm.names hc hm.sat hmain.classLive hn rfl hm.classes hm.declCls
    baseChains := baseChains hm.core.classReady hm.sat hmain.classLive hn rfl hm.baseChains
    nilQuery := nilQuery hm.names hc hm.sat hne hq.nilQuery rfl hm.nilQuery
    selfLive := self_live }

#print axioms state
end Ratchet.Denote.FreshModule
