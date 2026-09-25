import Denote.Sem.Core.Ready

/-! Physical scope of a singleton activation. Its class-valued self and lexical cref
refer to the named class; defmod refers to that class's cached eigenclass. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

structure SingletonScopeAt (cn : String) (k e : ObjId) (m : Machine) : Prop where
  named : classNamed? m.heap cn = some k
  live : k < m.heap.objs.size
  cached : (m.heap.get k).eigen = some e
  self : m.currentFrame.self = .ref k
  owner : m.currentFrame.defmod = e
  cref : m.currentFrame.cref = [k, Boot.objectId]
  captured : m.currentFrame.captured = none
  phase : m.preludeMode = false

end Ratchet.Denote
