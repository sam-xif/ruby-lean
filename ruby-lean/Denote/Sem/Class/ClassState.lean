import Denote.Sem.Subclass.SubclassState
import Ratchet.Guards.ClassCtx
import Denote.Sem.Class.ClassTables
import Denote.Sem.Class.ClassNative
import Denote.Sem.Class.ClassNames
import Denote.Sem.Class.ClassMethods
import Denote.Sem.Class.ClassDeclared
import Denote.Sem.Class.ClassScopeEntry
import Denote.Sem.Instance.InstanceSiteEntry
import Denote.Sem.Instance.InstanceSiteClass
import Denote.Sem.Instance.MainSiteClass
import Denote.Sem.Class.ClassAllocators
import Denote.Sem.Class.ClassGlobalConsts
import Denote.Sem.Class.ClassOwnNames
import Denote.Sem.Class.ClassChainsFresh

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
  exact Subclass.state hm hr hf ha ht hq hn hne (Subclass.ParentCaps.of_main hm hr) he

#print axioms state
end Ratchet.Denote.FreshClass
