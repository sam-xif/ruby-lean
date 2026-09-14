import Denote.Den

/-! Retained field observations, including class objects that no `Ty.inst` observes.
Types, not raw values, are preserved. Fresh objects may be initialized after allocation
when publication is anchored at the preallocation heap. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

structure FieldsPres (m n : Machine) : Prop where
  size : m.heap.objs.size ≤ n.heap.objs.size
  typed : ∀ o, o < m.heap.objs.size → ∀ x τ, FirstOrder τ = true →
    denM τ m (ivarOf m.heap (.ref o) x) → denM τ n (ivarOf n.heap (.ref o) x)

theorem FieldsPres.refl (m : Machine) : FieldsPres m m :=
  ⟨Nat.le_refl _, fun _ _ _ _ _ h => h⟩

theorem FieldsPres.trans {m n p : Machine} (h : FieldsPres m n) (h' : FieldsPres n p) :
    FieldsPres m p :=
  ⟨Nat.le_trans h.size h'.size, fun o ho x τ ht hv =>
    h'.typed o (Nat.lt_of_lt_of_le ho h.size) x τ ht (h.typed o ho x τ ht hv)⟩

theorem FieldsPres.of_unchanged {m n : Machine}
    (hs : m.heap.objs.size ≤ n.heap.objs.size)
    (hi : ∀ o, o < m.heap.objs.size → ivarOf n.heap (.ref o) = ivarOf m.heap (.ref o))
    (ht : ∀ τ, FirstOrder τ = true → ∀ v, denM τ m v → denM τ n v) : FieldsPres m n :=
  ⟨hs, fun o ho x τ hf hv => by rw [hi o ho]; exact ht τ hf _ hv⟩

theorem FieldsPres.of_heap_eq {m n : Machine} (hh : n.heap = m.heap) : FieldsPres m n :=
  .of_unchanged (by rw [hh]; exact Nat.le_refl _) (fun _ _ => by rw [hh])
    (fun _ ht _ hv => (denM_heap_only ht hh.symm).mp hv)

theorem FieldsPres.reheap {m n m' n' : Machine} (h : FieldsPres m n)
    (hm : m'.heap = m.heap) (hn : n'.heap = n.heap) : FieldsPres m' n' := by
  refine ⟨by rw [hm, hn]; exact h.size, ?_⟩
  intro o ho x τ ht hv
  rw [hm] at ho hv
  rw [hn]
  exact (denM_heap_only (m₁ := n) (m₂ := n') ht hn.symm).mp
    (h.typed o ho x τ ht ((denM_heap_only (m₁ := m') (m₂ := m) ht hm).mp hv))

/-- A spine can move between different getters, provided each field keeps its type. -/
theorem denSpineFrom_mono {m n : Machine} {g g' : String → Value}
    (h : ∀ x τ, FirstOrder τ = true → denM τ m (g x) → denM τ n (g' x))
    {I : Ty} (ht : FirstOrder I = true) {seen : List String}
    (hi : denSpineFrom seen I m g) : denSpineFrom seen I n g' := by
  induction I generalizing seen with
  | ivar0 => simp [denSpineFrom]
  | ivarCons x σ rest ihσ ihr =>
    simp only [FirstOrder, Bool.and_eq_true] at ht
    rw [denSpineFrom] at hi ⊢
    exact ⟨hi.1.imp id (h x σ ht.1), ihr ht.2 hi.2⟩
  | _ => simp [denSpineFrom] at hi

#print axioms FieldsPres.reheap
#print axioms denSpineFrom_mono
end Ratchet.Denote
