import Books.TypeSoundness.Conformance.Subclass.SubclassGlobals
import Books.TypeSoundness.Conformance.Class.ClassHeap
import Books.TypeSoundness.Conformance.Names.GlobalConsts

/-! Fresh entry adds just the executed binding to the upper bound; future declarations
are never pre-published. The statement is independent of the new class's name or body. -/
set_option autoImplicit false
namespace Checker.Soundness.FreshClass
open RubyCore
open RubyCore.Proof.Judgment (freshClsHeap)

theorem globalConsts {names : List String} {h : Heap} {name : String} {e : ObjId}
    (ho : Boot.objectId < h.objs.size) (hc : GlobalConstsOk names h) :
    GlobalConstsOk (name :: names) (freshClsHeap h Boot.objectId name name e) := by
  exact Subclass.globalConsts ho hc

#print axioms globalConsts
end Checker.Soundness.FreshClass
