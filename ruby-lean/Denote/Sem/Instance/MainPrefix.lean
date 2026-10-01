import Ratchet.Guards.MethodCtx
import Denote.Sem.Names.OwnNames

/-! Main's native singleton selectors cannot shadow an ordinary checked def. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

def MainOwnNames (h : Heap) : Prop :=
  ∀ p ∈ ownMethods h (classOf h (.ref Boot.mainId)), p.1 ∈ mainSingletonNames

def mainOwnNamesB (h : Heap) : Bool :=
  (ownMethods h (classOf h (.ref Boot.mainId))).all fun p => mainSingletonNames.contains p.1

theorem mainOwnNamesB_iff {h : Heap} : mainOwnNamesB h = true ↔ MainOwnNames h := by
  simp only [mainOwnNamesB, MainOwnNames, List.all_eq_true, List.contains_iff_mem]

theorem MainOwnNames.no_entry {h : Heap} {name : String} (hp : MainOwnNames h)
    (hn : name ∉ mainSingletonNames) :
    (h.classPayload? (classOf h (.ref Boot.mainId))).bind
      (fun cp => (cp.methods.find? (·.1 == name)).map (·.2)) = none := by
  cases hc : h.classPayload? (classOf h (.ref Boot.mainId)) with
  | none => rfl
  | some cp =>
    have hf : cp.methods.find? (·.1 == name) = none := by
      apply List.find?_eq_none.mpr
      intro p hm
      have hb := hp p (by simpa [ownMethods, hc] using hm)
      simp only [beq_iff_eq]
      intro he
      exact hn (he ▸ hb)
    simp [hf]

/-- Writes to main itself must retain its native selector bound. -/
def MainPrefixWriteOk (h : Heap) (cls : ObjId) (name : String) : Prop :=
  cls ≠ classOf h (.ref Boot.mainId) ∨ name ∈ mainSingletonNames

#print axioms mainOwnNamesB_iff
#print axioms MainOwnNames.no_entry
end Ratchet.Denote
