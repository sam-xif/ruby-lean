import Denote.Sem.SubclassState
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
import Denote.Sem.ClassChainsFresh

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
