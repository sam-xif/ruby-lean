import Books.TypeSoundness.Rules.Instance.InstanceRead
import Books.TypeSoundness.Conformance.Heap.WriteState

/-! Field-state transport for a checked write. Retained field/local types are obligations,
not assumed consequences of an ivar-only heap update. First-binding shadowing is respected.
-/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

def SpineShape : Ty → Prop
  | .ivar0 => True
  | .ivarCons _ _ rest => SpineShape rest
  | _ => False

theorem denSpineFrom_shape {I : Ty} {m : Machine} {seen : List String} {g : String → Value}
    (h : denSpineFrom seen I m g) : SpineShape I := by
  induction I generalizing seen with
  | ivar0 => trivial
  | ivarCons _ _ rest _ ih => rw [denSpineFrom] at h; exact ih h.2
  | _ => simp [denSpineFrom] at h

theorem denSpineFrom_of_get {I : Ty} {m : Machine} {seen : List String} {g : String → Value}
    (hi : SpineShape I)
    (h : ∀ x τ, x ∉ seen → ivarGet? I x = some τ → denM τ m (g x)) :
    denSpineFrom seen I m g := by
  induction I generalizing seen with
  | ivar0 => simp [denSpineFrom]
  | ivarCons x σ rest _ ih =>
    rw [denSpineFrom]
    refine ⟨?_, ih hi ?_⟩
    · by_cases hx : x ∈ seen
      · exact Or.inl hx
      · exact Or.inr (h x σ hx (by simp [ivarGet?]))
    · intro y τ hy hg
      have hy' : y ≠ x ∧ y ∉ seen := by simpa only [List.mem_cons, not_or] using hy
      exact h y τ hy'.2 (by simp [ivarGet?, Ne.symm hy'.1, hg])
  | _ => cases hi

theorem SpineShape.set {I ρ : Ty} {x : String} (hi : SpineShape I) :
    SpineShape (ivarSet I x ρ) := by
  induction I with
  | ivar0 => trivial
  | ivarCons y σ rest _ ih =>
    simp only [ivarSet]; split
    · exact hi
    · exact ih hi
  | _ => cases hi

theorem ivarGet?_set {I ρ : Ty} {x y : String} (hi : SpineShape I) :
    ivarGet? (ivarSet I x ρ) y = if y = x then some ρ else ivarGet? I y := by
  induction I with
  | ivar0 =>
    by_cases hyx : y = x
    · subst y; simp [ivarSet, ivarGet?]
    · simp [ivarSet, ivarGet?, hyx, Ne.symm hyx]
  | ivarCons z σ rest _ ih =>
    by_cases hzx : z = x
    · subst z
      by_cases hyx : y = x
      · subst y; simp [ivarSet, ivarGet?]
      · simp [ivarSet, ivarGet?, hyx, Ne.symm hyx]
    · by_cases hzy : z = y
      · subst y; simp [ivarSet, ivarGet?, hzx]
      · simpa only [ivarSet, ivarGet?, beq_eq_false_iff_ne.mpr hzx,
          beq_eq_false_iff_ne.mpr hzy, Bool.false_eq_true, ↓reduceIte] using ih hi
  | _ => cases hi

/-- The assigned value and every untouched visible field have types in the *post* heap. -/
theorem selfSpine_bindIvar {m : Machine} {o : ObjId} {I ρ : Ty} {x : String} {v : Value}
    {closed : Bool}
    (hs : m.currentFrame.self = .ref o) (ho : o < m.heap.objs.size)
    (hi : SelfSpineOk I m closed) (hv : denM ρ (Interp.bindIvar m x v) v)
    (hkeep : ∀ y τ, y ≠ x → ivarGet? I y = some τ →
      denM τ (Interp.bindIvar m x v) (ivarOf m.heap (.ref o) y)) :
    SelfSpineOk (ivarSet I x ρ) (Interp.bindIvar m x v) closed := by
  have hshape := denSpineFrom_shape hi.1
  have hread (y : String) :
      ivarOf (Interp.bindIvar m x v).heap (.ref o) y =
        if y = x then v else ivarOf m.heap (.ref o) y := by
    by_cases hy : y = x
    · subst y; simp only [↓reduceIte, ivarOf_bindIvar_self hs ho]
    · simp only [hy, ↓reduceIte, ivarOf_bindIvar_ne hs ho hy]
  refine ⟨denSpineFrom_of_get hshape.set ?_, ?_⟩
  · intro y τ _ hg
    rw [ivarGet?_set hshape] at hg
    simp only [bindIvar_currentFrame, hs, hread]
    by_cases hy : y = x
    · simp only [hy, ↓reduceIte] at hg ⊢
      cases Option.some.inj hg; exact hv
    · simp only [hy, ↓reduceIte] at hg ⊢
      exact hkeep y τ hy hg
  · intro y hg hc
    rw [ivarGet?_set hshape] at hg
    by_cases hy : y = x
    · simp [hy] at hg
    · simp only [hy, ↓reduceIte] at hg
      simp only [bindIvar_currentFrame, hs, hread, hy, ↓reduceIte]
      simpa only [hs] using hi.2 y hg hc

#print axioms selfSpine_bindIvar
#print axioms env_bindIvar
end Checker.Soundness.Typed
