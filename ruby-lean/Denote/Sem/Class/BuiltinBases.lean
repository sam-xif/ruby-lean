import Ratchet.Static.All
import RubyCore.Heap

namespace Ratchet.Denote
open RubyCore

/-- **The base class of each `builtinAncestors` row**, paired with the row itself. The table is
the bridge between `Ratchet/Static/`'s *static* chains and the heap's own class ids, and it
is the reason `BaseChainsOk` can be one statement rather than eight.

Ordered exactly as `builtinAncestors`' rows, and the chain includes the base's own name first —
`isANoOk` reads `ch.head?` to find the base it must check for declared subclasses. -/
def builtinBases : List (ObjId × List String) :=
  [(Boot.integerId, ["Integer", "Numeric", "Comparable"] ++ Ratchet.rootAncestors),
   (Boot.floatId, ["Float", "Numeric", "Comparable"] ++ Ratchet.rootAncestors),
   (Boot.nilClassId, "NilClass" :: Ratchet.rootAncestors),
   (Boot.symbolId, ["Symbol", "Comparable"] ++ Ratchet.rootAncestors),
   (Boot.stringId, ["String", "Comparable"] ++ Ratchet.rootAncestors),
   (Boot.hashId, ["Hash", "Enumerable"] ++ Ratchet.rootAncestors),
   (Boot.arrayId, ["Array", "Enumerable"] ++ Ratchet.rootAncestors)]

theorem builtinBase_bound {base : ObjId} {ch : List String} (hb : (base, ch) ∈ builtinBases) :
    base ≤ Boot.procId ∧ base ≠ Boot.objectId := by
  have h := List.all_eq_true.mp
    (by decide : builtinBases.all (fun p => decide (p.1 ≤ Boot.procId ∧ p.1 ≠ Boot.objectId)) = true)
    (base, ch) hb
  exact of_decide_eq_true h

end Ratchet.Denote
