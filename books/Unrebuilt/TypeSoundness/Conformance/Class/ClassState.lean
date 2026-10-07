import Books.TypeSoundness.Conformance.Subclass.SubclassState
import Checker.Guards.ClassCtx
import Books.TypeSoundness.Conformance.Class.ClassTables
import Books.TypeSoundness.Conformance.Class.ClassNative
import Books.TypeSoundness.Conformance.Class.ClassNames
import Books.TypeSoundness.Conformance.Class.ClassMethods
import Books.TypeSoundness.Conformance.Class.ClassDeclared
import Books.TypeSoundness.Conformance.Class.ClassScopeEntry
import Books.TypeSoundness.Conformance.Instance.InstanceSiteEntry
import Books.TypeSoundness.Conformance.Instance.InstanceSiteClass
import Books.TypeSoundness.Conformance.Instance.MainSiteClass
import Books.TypeSoundness.Conformance.Class.ClassAllocators
import Books.TypeSoundness.Conformance.Class.ClassGlobalConsts
import Books.TypeSoundness.Conformance.Class.ClassOwnNames
import Books.TypeSoundness.Conformance.Class.ClassChainsFresh

/-! Full conformance at entry to an empty fresh class scope. The body is still to be
checked, and no future definition has been inserted into the positive table. -/
set_option autoImplicit false
namespace Checker.Soundness.FreshClass
open RubyCore Checker
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
  exact Subclass.state hm hr hf ha ht hq hn hne (Subclass.ParentCaps.of_main hm hr) he

#print axioms state
end Checker.Soundness.FreshClass
