import Books.Metatheory.Heap.AncestorsGrow
import Init.Data.List.Perm

/-! Bounds for the duplicate-free ancestor chains passed to native lookup. -/
namespace RubyCore.Proof

variable {h : Heap}

/-- The walk visits only old ids (the closure `ChainsIn` promises). -/
theorem modAncestors_go_mem_lt (hch : ChainsIn h) :
    ∀ (fuel : Nat) (mo : ObjId), mo < h.objs.size →
      ∀ j ∈ modAncestors.go h mo fuel, j < h.objs.size := by
  intro fuel
  induction fuel with
  | zero => intro mo hmo j hj; simp only [modAncestors.go] at hj
            rw [List.mem_singleton.mp hj]; exact hmo
  | succ fuel ih =>
    intro mo hmo j hj
    unfold modAncestors.go at hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hmo
    · cases hcp : h.classPayload? mo with
      | none => rw [hcp] at hj; simp at hj
      | some c =>
        rw [hcp] at hj
        obtain ⟨i, hi, hji⟩ := List.mem_flatMap.mp hj
        exact ih i ((hch.chain mo c hmo hcp).2.1 i (List.mem_reverse.mp hi)) j hji

theorem ancestors_go_mem_lt (hch : ChainsIn h) :
    ∀ (fuel : Nat) (k : ObjId), k < h.objs.size →
      ∀ j ∈ ancestors.go h k fuel, j < h.objs.size := by
  intro fuel
  induction fuel with
  | zero => intro k _ j hj; simp [ancestors.go] at hj
  | succ fuel ih =>
    intro k hk j hj
    unfold ancestors.go at hj
    cases hcp : h.classPayload? k with
    | none =>
      rw [hcp] at hj
      rw [List.mem_singleton.mp hj]; exact hk
    | some c =>
      rw [hcp] at hj
      obtain ⟨hsup, hincl, hpre⟩ := hch.chain k c hk hcp
      have hmodmem : ∀ i, i < h.objs.size → ∀ j' ∈ modAncestors h i,
          j' < h.objs.size := by
        intro i hi j' hj'
        exact modAncestors_go_mem_lt hch _ i hi j' hj'
      rcases List.mem_append.mp hj with hj2 | hj3
      · rcases List.mem_append.mp hj2 with hj4 | hj5
        · obtain ⟨p, hp, hjp⟩ := List.mem_flatMap.mp hj4
          exact hmodmem p (hpre p (List.mem_reverse.mp hp)) j hjp
        · rcases List.mem_cons.mp hj5 with rfl | hj6
          · exact hk
          · obtain ⟨i, hi, hji⟩ := List.mem_flatMap.mp hj6
            exact hmodmem i (hincl i (List.mem_reverse.mp hi)) j hji
      · cases hs : c.superclass with
        | none => rw [hs] at hj3; simp at hj3
        | some s => rw [hs] at hj3; exact ih s (hsup s hs) j hj3

theorem ancestors_mem_lt (hch : ChainsIn h) {k : ObjId} (hk : k < h.objs.size) :
    ∀ j ∈ ancestors h k, j < h.objs.size := by
  intro j hj
  unfold ancestors at hj
  -- the fold is a de-dup: membership in the fold implies membership in the walk
  have hsub : ∀ (l : List ObjId) (acc : List ObjId),
      j ∈ l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) acc →
      j ∈ acc ∨ j ∈ l := by
    intro l
    induction l with
    | nil => intro acc hjm; exact Or.inl hjm
    | cons x xs ih =>
      intro acc hjm
      simp only [List.foldl] at hjm
      by_cases hc : acc.contains x
      · simp only [hc, if_true] at hjm
        rcases ih acc hjm with hja | hjl
        · exact Or.inl hja
        · exact Or.inr (List.mem_cons_of_mem _ hjl)
      · simp only [hc, if_false] at hjm
        rcases ih (acc ++ [x]) hjm with hja | hjl
        · rcases List.mem_append.mp hja with hja | hjx
          · exact Or.inl hja
          · exact Or.inr (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hjx)))
        · exact Or.inr (List.mem_cons_of_mem _ hjl)
  rcases hsub _ [] hj with hja | hjl
  · simp at hja
  · exact ancestors_go_mem_lt hch _ k hk j hjl


private theorem dedup_nodup (xs acc : List ObjId) (ha : acc.Nodup) :
    (xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) acc).Nodup := by
  induction xs generalizing acc with
  | nil => exact ha
  | cons x xs ih =>
    simp only [List.foldl_cons]
    split
    · exact ih _ ha
    · rename_i hx
      apply ih
      have hn : x ∉ acc := by simpa using hx
      refine List.nodup_append.mpr ⟨ha, by simp, ?_⟩
      intro a ha b hb
      have hb : b = x := by simpa using hb
      subst b
      intro he
      exact hn (he ▸ ha)

theorem ancestors_nodup (h : Heap) (k : ObjId) : (ancestors h k).Nodup :=
  dedup_nodup _ [] (by simp)


open List in
private theorem nodup_length_le_of_subset {α : Type} {l₁ l₂ : List α}
    (h₁ : l₁.Nodup) (hsub : l₁ ⊆ l₂) : l₁.length ≤ l₂.length := by
  classical
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a t ih =>
    rw [nodup_cons] at h₁
    have ha : a ∈ l₂ := hsub (mem_cons_self ..)
    have htsub : t ⊆ l₂.erase a := by
      intro x hx
      have hxa : x ≠ a := fun h => h₁.1 (h ▸ hx)
      exact (mem_erase_of_ne hxa).2 (hsub (mem_cons_of_mem _ hx))
    have hih := ih h₁.2 htsub
    have hlen : (l₂.erase a).length = l₂.length - 1 := by rw [length_erase]; simp [ha]
    have hpos : 1 ≤ l₂.length := length_pos_of_mem ha
    calc t.length + 1 ≤ (l₂.erase a).length + 1 := Nat.succ_le_succ hih
      _ = (l₂.length - 1) + 1 := by rw [hlen]
      _ = l₂.length := Nat.sub_add_cancel hpos

theorem ancestors_length_le (hch : ChainsIn h) {k : ObjId} (hk : k < h.objs.size) :
    (ancestors h k).length ≤ h.objs.size := by
  have hs : ancestors h k ⊆ List.range h.objs.size := by
    intro j hj
    exact List.mem_range.mpr (ancestors_mem_lt hch hk j hj)
  have hb := nodup_length_le_of_subset (ancestors_nodup h k) hs
  simpa using hb

theorem ancestors_oob {k : ObjId} (hk : ¬ k < h.objs.size) : ancestors h k = [k] := by
  simp [ancestors, ancestors.go, classPayload?_oob h k hk]

theorem ancestors_length_bound (hch : ChainsIn h) (k : ObjId) :
    (ancestors h k).length ≤ h.objs.size + 1 := by
  by_cases hk : k < h.objs.size
  · exact Nat.le_trans (ancestors_length_le hch hk) (Nat.le_succ _)
  · rw [ancestors_oob hk]; simp

end RubyCore.Proof
