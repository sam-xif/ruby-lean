import Ratchet.Judge

/-! Static framing for builtin negative ancestry answers during subclass creation.
No heap ids enter this guard; its interpretation follows from existing conformance. -/
namespace Ratchet

def subclassBaseFrameB (κ : Ctx) (parent : String) : Bool :=
  builtinChains.all fun ch => !isANoOk κ.wholeCls ch ||
    match ancestors? κ.classes parent, ch.head? with
    | some ns, some bn => coreConstFreeN κ && mixinFreeChain κ.wholeCls rootAncestors &&
        !(ns ++ rootAncestors).contains bn
    | _, _ => false

end Ratchet
