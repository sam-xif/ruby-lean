import Ratchet.Guards.OwnNames
import Denote.Ty.Ext

/-! Owner-local absence, independent of method bodies and their annotations. This bound
does not assert that a permitted selector exists, nor that a present body is well typed. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

def ownMethods (h : Heap) (k : ObjId) : List (String × MethodDef) :=
  ((h.classPayload? k).map ClassPayload.methods).getD []

def ClassOwnNames (C : CTable) (h : Heap) : Prop :=
  ∀ c ∈ C, ∀ k, classNamed? h c.name = some k →
    ∀ p ∈ ownMethods h k, p.1 ∈ ownNames C c.name

def classOwnNamesB (C : CTable) (h : Heap) : Bool :=
  C.all fun c => (classNamed? h c.name).all fun k =>
    (ownMethods h k).all fun p => (ownNames C c.name).contains p.1

theorem classOwnNamesB_sound {C : CTable} {h : Heap} (hp : classOwnNamesB C h = true) :
    ClassOwnNames C h := by
  intro c hc k hk p hm
  have hb := List.all_eq_true.mp hp c hc
  rw [hk] at hb
  exact List.contains_iff_mem.mp (List.all_eq_true.mp hb p hm)

theorem ClassOwnNames.empty (h : Heap) : ClassOwnNames [] h := by
  intro c hc; cases hc

/-- A class-table name absent from the bound has no own entry, even if another class
defines the same selector. Undefined/builtin/prelude entries are included in the bound. -/
theorem ClassOwnNames.absent {C : CTable} {h : Heap} {c : Cls} {k : ObjId} {name : String}
    (hp : ClassOwnNames C h) (hc : c ∈ C) (hk : classNamed? h c.name = some k)
    (hn : name ∉ ownNames C c.name) :
    (h.classPayload? k).bind
      (fun cp => (cp.methods.find? (·.1 == name)).map (·.2)) = none := by
  cases hcp : h.classPayload? k with
  | none => rfl
  | some cp =>
    have hf : cp.methods.find? (·.1 == name) = none := by
      apply List.find?_eq_none.mpr
      intro p hm
      have hb := hp c hc k hk p (by simpa [ownMethods, hcp] using hm)
      simp only [beq_iff_eq]
      intro he
      exact hn (he ▸ hb)
    simp [hf]

/-- Same named owners and a shrinking own table preserve absence. Frame/ivar-only
changes and ordinary allocation specialize this transport. -/
theorem ClassOwnNames.transport {C : CTable} {h h' : Heap} (hp : ClassOwnNames C h)
    (hn : ∀ c ∈ C, ∀ k, classNamed? h' c.name = some k → classNamed? h c.name = some k)
    (hm : ∀ k p, p ∈ ownMethods h' k → p ∈ ownMethods h k) : ClassOwnNames C h' := by
  intro c hc k hk p hmem
  exact hp c hc k (hn c hc k hk) p (hm k p hmem)

theorem ClassOwnNames.ext {C : CTable} {m n : Machine} (hp : ClassOwnNames C m.heap)
    (he : Ext m n) : ClassOwnNames C n.heap :=
  hp.transport (fun _ _ _ hk => by simpa only [he.classNamed?_eq] using hk)
    (fun _ _ hm => by simpa only [ownMethods, he.payload] using hm)

/-- A fresh empty table adds no selector. This premise concerns the physical table,
not an empty declaration record, which by itself says nothing about hidden overrides. -/
theorem ClassOwnNames.cons_empty {C : CTable} {h : Heap} (hp : ClassOwnNames C h) (c : Cls)
    (he : ∀ k, classNamed? h c.name = some k → ownMethods h k = []) :
    ClassOwnNames (c :: C) h := by
  intro old hold k hk p hm
  rcases List.mem_cons.mp hold with rfl | hold
  · rw [he k hk] at hm; cases hm
  · exact ownNames_cons_mono c (hp old hold k hk p hm)

end Ratchet.Denote
