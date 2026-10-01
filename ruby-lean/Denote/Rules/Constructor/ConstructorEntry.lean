import Denote.Sem.Class.ClassShape
import Denote.Sem.Class.ClassNew
import Denote.Rules.Method.MethodEntry

/-! The actual new/initialize interception and required-parameter frame. This does not
certify an initializer body: its annotated InitState/run obligation is separate. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

def ctorAllocated (m : Machine) (k : ObjId) : Machine :=
  { m with heap := pushHeap m.heap { klass := k }, kont := .newK (.ref m.heap.objs.size) :: m.kont }

end Ratchet.Denote.Typed
