import Books.TypeSoundness.Conformance.Class.ClassStateActual
import Books.TypeSoundness.Conformance.Class.ClassHeaderActual
import Books.TypeSoundness.Conformance.Class.ClassPublish

/-! Publish the fresh header over the actual class-body entry state. -/
set_option autoImplicit false
namespace Checker.Soundness.FreshClassActual
open RubyCore Checker RubyCore.Proof
variable {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
variable {name : String} {e : ObjId} {body : RubyCore.Expr}
local notation "entry" => machine m name e body

theorem header (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true)
    (hf : κ.frame = none) (ha : κ.asms = []) (hin : κ.pos.mainWorld = true)
    (ht : ClassTablesFrame κ name m) (hq : FreshClass.NativeFrame κ name)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false)
    (he : (m.heap.get Boot.objectId).eigen = some e)
    (hreach : ∀ cn ∈ κ.classes.map (·.name), ∀ k, InstanceSite κ cn k m.heap →
      Boot.objectId ∈ ancestors m.heap k ∨ (m.heap.classPayload? k).any (·.isModule) = true)
    (hnew : nameFreeN κ "new" = true) (hquiet : classNativeQuietB name "new" = true)
    (hplain : unqualifiedClassB name = true) (hframe : HeaderTableFrame κ.classes name) :
    StateOk (classHeaderCtx (classBodyCtx κ name) name) [] .ivar0 entry := by
  have hs := state (body := body) hm hr hf ha ht hq hn hne he hreach
  have hc := hm.core.classReady
  have hmain := hm.runtime hr
  have htop : m.lexicalNamespace = Boot.objectId := by
    simp only [Machine.lexicalNamespace, hmain.cref, List.headD_nil]
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ lt_size_of_classPayload hmain.classLive
  exact StateOk_publish_empty_class (c := classHeader name) hs rfl rfl rfl hplain
    (declared_header (κ := classBodyCtx κ name) hm.names hc hm.sat hm.core.rootNames htop
      hmain.classLive hn hne he hmain.live hquiet hmain.classFlags
      ((hm.mainSite hin).newDispatch hnew) rfl hm.classes hm.declCls hframe)
    ⟨_, named_fresh htop hmain.classLive, plain hc hm.sat hd hmain.classFlags⟩
    (ownNames_header htop hmain.classLive hn hm.classes hm.ownNames)
    (classChains_header hc hm.sat hm.core.rootNames htop hmain.classLive hn hm.classes
      hm.classChains hframe)

#print axioms header
end Checker.Soundness.FreshClassActual
