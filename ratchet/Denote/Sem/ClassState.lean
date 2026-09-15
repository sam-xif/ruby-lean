import Ratchet.ClassCtx
import Denote.Sem.ClassTables
import Denote.Sem.ClassNative
import Denote.Sem.ClassNames
import Denote.Sem.ClassMethods
import Denote.Sem.ClassDeclared
import Denote.Sem.ClassScopeEntry
import Denote.Sem.InstanceSiteEntry
import Denote.Sem.InstanceSiteClass
import Denote.Sem.MainSiteClass
import Denote.Sem.ClassAllocators
import Denote.Sem.ClassGlobalConsts
import Denote.Sem.ClassOwnNames

/-! Full conformance at entry to an empty fresh class scope. The body is still to be
checked, and no future definition has been inserted into the positive table. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsMachine)

variable {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
variable {name : String} {e : ObjId} {body : RubyCore.Expr}
local notation "entry" => freshClsMachine m Boot.objectId m.currentFrame.cref name name e body

theorem state (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true)
    (hf : κ.frame = none) (ha : κ.asms = [])
    (ht : ClassTablesFrame κ name m) (hq : NativeFrame κ name)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false)
    (he : (m.heap.get Boot.objectId).eigen = some e) :
    StateOk (classBodyCtx κ name) [] .ivar0 entry := by
  have hc := hm.core.classReady.chains
  have ho := hc.boot.2.2.2.2
  have hel := hc.eigen Boot.objectId ho e he
  have hmain := hm.runtime hr
  have hscope : ConstScopeOk entry :=
    const_scope hc hm.sat hmain.classLive hmain.cref hmain.owner hm.constScope
  have hd : DataPres m.heap (entry).heap :=
    dataPres hm.core.classReady hm.sat hm.core.basicSelf hn he
  have hconst : ConstsOk κ entry :=
    constants ho hn rfl hd hm.constScope hscope ht.consts hm.consts
  exact {
    runtime := by intro h; cases h
    mainSite := fun hr => mainSite (hm.mainSite hr) hm.core.classReady hm.sat hm.core.basicSelf hn he
    allocators := allocators hc hm.sat hn hm.allocators
    globalConsts := globalConsts ho hm.globalConsts
    classRuntime := by
      intro cn hr
      change some name = some cn at hr
      cases hr
      exact scope_ready hc hm.sat he hmain
    classSites := by
      intro cn hcn
      change cn ∈ κ.classes.map (·.name) ++ [name] at hcn
      rcases List.mem_append.mp hcn with hcn | hcn
      · obtain ⟨k, site⟩ := hm.classSites cn (List.mem_append_left _ hcn)
        exact ⟨k, instanceSite_old site hc hm.sat hmain.classLive hn⟩
      · have heq := List.mem_singleton.mp hcn
        subst cn
        exact ⟨m.heap.objs.size, (instanceSite (κ := κ) (body := body) hm hr he).recontext
          (fun _ hn => hn)⟩
    sat := Proof.Judgment.saturated_freshC hc hm.sat ho hel
    primitiveDispatch := (primitiveDispatch hc hm.sat _).trans hm.primitiveDispatch
    primitiveErrors := (primitiveErrors hc hm.sat).trans hm.primitiveErrors
    stringPayload := stringPayload hc hm.stringPayload
    arrayPayload := arrayPayload hm.arrayPayload
    hashPayload := hashPayload hm.hashPayload
    core := core hm.core hm.sat hmain.classLive hn he
    frameInRange := frame_in_range
    env := env_empty
    selfSpine := spine_empty
    classes := classes ho hn rfl hm.classes
    ownNames := ownNames ho hn hm.classes hm.ownNames
    defs := defs ho rfl hm.defs
    asms := by
      intro a ham
      change a ∈ κ.asms at ham
      rw [ha] at ham
      cases ham
    frame := frame_ok
    closures := trivial
    blockTy := block_none
    selfTy := self_type hmain.classLive
    consts := fun cn τ hct => hconst cn τ (by
      rwa [classBodyCtx_constGet hf] at hct)
    constPaths := paths (κ := κ) hc hm.sat hn rfl hd ht hm.constPaths
    nested := nested (κ := κ) hc hm.sat hn rfl hd ht hm.nested
    privConsts := trivial
    constScope := hscope
    exact := methodsExact ho rfl hm.exact
    nameFree := nameFree hc hm.sat he hm.nameFree
    bareFree := by intro _ _ _ hself; cases hself
    missFree := by intro _ hself; cases hself
    query := query hc hm.sat hel hne hq.query rfl hm.query
    clsQuery := clsQuery hc hm.sat hmain.classLive he hne hq.clsQuery rfl hm.clsQuery
    declCls := declared hc hm.sat hmain.classLive hn rfl hm.classes hm.declCls
    baseChains := baseChains hm.core.classReady hm.sat hmain.classLive hn he rfl hm.baseChains
    nilQuery := nilQuery hc hm.sat hel hne hq.nilQuery rfl hm.nilQuery
    selfLive := self_live }

#print axioms state
end Ratchet.Denote.FreshClass
