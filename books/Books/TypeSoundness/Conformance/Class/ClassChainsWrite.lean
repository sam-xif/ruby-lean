import Books.TypeSoundness.Conformance.Class.ClassChains
import Books.TypeSoundness.Conformance.Instance.MethodHeap

/-! Method installation preserves ancestry and class bindings; publication may change
only the method rows, not activate a different ancestor walk for an old name. -/
set_option autoImplicit false
namespace Checker.Soundness
open RubyCore Checker

theorem ClassChains.methodWrite {C : CTable} {h : Heap} {cls : ObjId} {name : String}
    {md : MethodDef} (hp : ClassChains C h) : ClassChains C (defineMethod h cls name md) :=
  hp.heap (fun _ => classNamed?_defineMethod ..) (fun _ => Proof.ancestors_defineMethod ..)

end Checker.Soundness
