import Denote.Sem.Heap.WriteState
import Ratchet.Guards.ScalarWrite

/-! Scalar replacement preserves every first-order observation, including field snapshots
nested in collections. No alias or ownership assumption is hidden in this transport. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

inductive ScalarEq : Value → Value → Prop where
  | refl (v : Value) : ScalarEq v v
  | int (a b : Int) : ScalarEq (.int a) (.int b)
  | flt (a b : Float) : ScalarEq (.flt a) (.flt b)
  | sym (a b : String) : ScalarEq (.sym a) (.sym b)

theorem scalarWriteB_values {τ : Ty} {m : Machine} {v w : Value}
    (ht : scalarWriteB τ = true) (hv : denM τ m v) (hw : denM τ m w) : ScalarEq v w := by
  cases τ <;> try cases ht
  all_goals cases v <;> cases w <;>
    simp_all [denM, isIntV, isFltV, isSymV, isNilV]
  all_goals constructor

/-- The heap metadata is fixed and each field changes only within a scalar equivalence
class. Simultaneous induction follows types through arbitrary instance/collection nesting. -/
theorem scalarHeap_pres {m n : Machine} (hi : Proof.IvarOnly m.heap n.heap)
    (hfields : ∀ w x, ScalarEq (ivarOf m.heap w x) (ivarOf n.heap w x)) :
    ∀ τ, FirstOrder τ = true →
      (∀ v w, ScalarEq v w → denM τ m v → denM τ n w) ∧
      (∀ seen g g', (∀ x, ScalarEq (g x) (g' x)) →
        denSpineFrom seen τ m g → denSpineFrom seen τ n g') := by
  have hn (cn : String) : classNamed? n.heap cn = classNamed? m.heap cn := by
    simp only [classNamed?, constLookup, hi.classPayload]
  have ha {v w : Value} (h : ScalarEq v w) : classOf n.heap w = classOf m.heap v := by
    cases h with
    | refl v => exact hi.classOf_eq v
    | int | flt | sym => rfl
  have harr {v w : Value} (h : ScalarEq v w) : arrElems? n.heap w = arrElems? m.heap v := by
    cases h with
    | refl v => cases v <;> simp only [arrElems?, hi.payload]
    | int | flt | sym => rfl
  have hhash {v w : Value} (h : ScalarEq v w) : hshEntries? n.heap w = hshEntries? m.heap v := by
    cases h with
    | refl v => cases v <;> simp only [hshEntries?, hi.payload]
    | int | flt | sym => rfl
  have hinst {v w : Value} (h : ScalarEq v w) (cn : String) :
      isExactInst n.heap w cn = isExactInst m.heap v cn := by
    cases h with
    | refl v => cases v <;> simp only [isExactInst, hn, hi.size, hi.eigen, hi.klass]
    | int | flt | sym => cases hc : classNamed? m.heap cn <;> simp [isExactInst, hn, hc]
  have hget {v w : Value} (h : ScalarEq v w) (x : String) :
      ScalarEq (ivarOf m.heap v x) (ivarOf n.heap w x) := by
    cases h with
    | refl v => exact hfields v x
    | int | flt | sym => exact .refl _
  intro τ
  induction τ with
  | int | bool | nilT | sym | float | any | never | ivar0 =>
    intro _
    refine ⟨?_, fun _ _ _ _ h => by simpa only [denSpineFrom] using h⟩
    intro v w h hv
    cases h <;> simpa only [denM, isIntV, isBoolV, isNilV, isSymV, isFltV] using hv
  | cls cn =>
    intro _
    refine ⟨fun v w h hv => ?_, fun _ _ _ _ h => by simpa only [denSpineFrom] using h⟩
    simpa only [denM, isAName, hn, isA, ha h, hi.ancestors_eq] using hv
  | clsOf cn =>
    intro _
    refine ⟨fun v w h hv => ?_, fun _ _ _ _ h => by simpa only [denSpineFrom] using h⟩
    cases h <;> cases hc : classNamed? m.heap cn <;> simp_all [denM, isClassRefNamed, hn]
  | nilable τ ih =>
    intro hf
    refine ⟨fun v w h hv => ?_, fun _ _ _ _ h => by simpa only [denSpineFrom] using h⟩
    simp only [denM] at hv ⊢
    rcases hv with hn | hv
    · left; cases h <;> simpa only [isNilV] using hn
    · exact Or.inr ((ih hf).1 v w h hv)
  | union σ τ ihσ ihτ =>
    intro hf
    simp only [FirstOrder, Bool.and_eq_true] at hf
    refine ⟨?_, fun _ _ _ _ h => by simpa only [denSpineFrom] using h⟩
    intro v w h hv
    simp only [denM] at hv ⊢
    exact hv.elim (fun hv => Or.inl ((ihσ hf.1).1 v w h hv))
      (fun hv => Or.inr ((ihτ hf.2).1 v w h hv))
  | sameAs _ τ ih =>
    intro hf
    refine ⟨?_, fun _ _ _ _ h => by simpa only [denSpineFrom] using h⟩
    intro v w h hv
    simpa only [denM] using (ih hf).1 v w h (by simpa only [denM] using hv)
  | arrayOf τ ih =>
    intro hf
    refine ⟨?_, fun _ _ _ _ h => by simpa only [denSpineFrom] using h⟩
    intro v w h hv
    simp only [denM] at hv ⊢
    obtain ⟨xs, hx, ht⟩ := hv
    exact ⟨xs, (harr h).trans hx, fun z hz => (ih hf).1 z z (.refl _) (ht z hz)⟩
  | hashOf σ τ ihσ ihτ =>
    intro hf
    simp only [FirstOrder, Bool.and_eq_true] at hf
    refine ⟨?_, fun _ _ _ _ h => by simpa only [denSpineFrom] using h⟩
    intro v w h hv
    simp only [denM] at hv ⊢
    obtain ⟨es, he, ht⟩ := hv
    exact ⟨es, (hhash h).trans he, fun p hp =>
      ⟨(ihσ hf.1).1 p.1 p.1 (.refl _) (ht p hp).1,
        (ihτ hf.2).1 p.2 p.2 (.refl _) (ht p hp).2⟩⟩
  | inst cn I ih =>
    intro hf
    refine ⟨?_, fun _ _ _ _ h => by simpa only [denSpineFrom] using h⟩
    intro v w h hv
    simp only [denM] at hv ⊢
    exact ⟨(hinst h cn).trans hv.1, (ih hf).2 [] _ _ (hget h) hv.2⟩
  | ivarCons x σ rest ihσ ihr =>
    intro hf
    simp only [FirstOrder, Bool.and_eq_true] at hf
    refine ⟨fun _ _ _ h => by simpa only [denM] using h, ?_⟩
    intro seen g g' hg h
    simp only [denSpineFrom] at h ⊢
    exact ⟨h.1.imp id ((ihσ hf.1).1 _ _ (hg x)), (ihr hf.2).2 _ _ _ hg h.2⟩
  | arrow0 _ _ | arrowCons _ _ _ _ | clos _ _ _ _ _ => intro hf; cases hf

/-- An actual write changes just one field; the scalar relation also covers all aliases. -/
theorem bindIvar_scalar_fields {m : Machine} {o : ObjId} {x : String} {v : Value}
    (hs : m.currentFrame.self = .ref o) (ho : o < m.heap.objs.size)
    (hv : ScalarEq (ivarOf m.heap (.ref o) x) v) :
    ∀ w y, ScalarEq (ivarOf m.heap w y) (ivarOf (Interp.bindIvar m x v).heap w y) := by
  intro w y
  by_cases hw : w = .ref o
  · subst w
    by_cases hy : y = x
    · subst y; rw [ivarOf_bindIvar_self hs ho]; exact hv
    · rw [ivarOf_bindIvar_ne hs ho hy]; exact .refl _
  · rw [ivarOf_bindIvar_other hs hw]; exact .refl _

theorem Framed.bindIvar_scalar {m : Machine} {o : ObjId} {x : String} {v : Value}
    (hs : m.currentFrame.self = .ref o) (ho : o < m.heap.objs.size)
    (hv : ScalarEq (ivarOf m.heap (.ref o) x) v) : Framed m (Interp.bindIvar m x v) := by
  have hi := bindIvar_ivarOnly m x v
  have hfields := bindIvar_scalar_fields hs ho hv
  have hpres := scalarHeap_pres hi hfields
  refine ⟨by simp, ?_, ?_, ?_, .bindIvar m x v, ?_, ?_⟩
  · intro k hk; simpa only [hi.classPayload] using hk
  · intro w cn hw; simpa only [bindIvar_isAName] using hw
  · intro τ ht w hw; exact (hpres τ ht).1 w w (.refl _) hw
  · refine ⟨by rw [hi.size]; exact Nat.le_refl _, ?_⟩
    intro k _ y τ ht hw
    exact (hpres τ ht).1 _ _ (hfields (.ref k) y) hw
  · intro k _ e hk; simpa only [hi.eigen] using hk

#print axioms bindIvar_scalar_fields
#print axioms Framed.bindIvar_scalar
#print axioms scalarWriteB_values
#print axioms scalarHeap_pres
end Ratchet.Denote
