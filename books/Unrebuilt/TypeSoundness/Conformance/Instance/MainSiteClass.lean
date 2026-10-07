import Books.TypeSoundness.Conformance.Subclass.SubclassMain
import Books.TypeSoundness.Conformance.Class.ClassCore
import Books.TypeSoundness.Conformance.Class.ClassConstants

/-! Fresh classes leave the retained top-level receiver and its dispatch sites intact. -/
set_option autoImplicit false
namespace Checker.Soundness.FreshClass
open RubyCore Checker
open RubyCore.Proof.Judgment (freshClsHeap)

theorem mainSite {κ : Ctx} {h : Heap} {name : String} {e : ObjId}
    (site : MainSite κ h) (hc : ClassReady h) (hs : Proof.Saturated h)
    (hb : ancestors h Boot.basicObjectId = [Boot.basicObjectId])
    (hn : constOwn h Boot.objectId name = none) (he : (h.get Boot.objectId).eigen = some e) :
    MainSite κ (freshClsHeap h Boot.objectId name name e) :=
  Subclass.mainSite site hc.chains hs (dataPres hc hs hb hn he)

#print axioms mainSite
end Checker.Soundness.FreshClass
