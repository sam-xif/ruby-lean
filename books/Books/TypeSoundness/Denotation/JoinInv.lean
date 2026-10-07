import Books.TypeSoundness.Denotation.Join

/-! The converse of the join bounds: a value in `joinT σ τ` is in one of the two sides. -/
set_option autoImplicit false
namespace Checker.Soundness
open RubyCore Checker

theorem denM_unionOf_inv : ∀ (l : List Ty) {m : Machine} {v : Value}, l ≠ [] →
    denM (unionOf l) m v → ∃ μ ∈ l, denM μ m v
  | [], _, _, h, _ => absurd rfl h
  | [ρ], _, _, _, h => ⟨ρ, by simp, by rwa [unionOf] at h⟩
  | τ :: τ' :: rest, m, v, _, h => by
    rw [show unionOf (τ :: τ' :: rest) = .union τ (unionOf (τ' :: rest)) from rfl, denM] at h
    rcases h with h | h
    · exact ⟨τ, by simp, h⟩
    · obtain ⟨μ, hμ, hd⟩ := denM_unionOf_inv (τ' :: rest) (by simp) h
      exact ⟨μ, List.mem_cons_of_mem _ hμ, hd⟩

theorem denM_of_unionMems : ∀ (σ : Ty) {μ : Ty} {m : Machine} {v : Value},
    μ ∈ unionMems σ → denM μ m v → denM σ m v
  | .union σ τ, μ, m, v, hm, h => by
    simp only [unionMems, List.mem_append] at hm
    rw [denM]
    rcases hm with hm | hm
    · exact .inl (denM_of_unionMems σ hm h)
    · exact .inr (denM_of_unionMems τ hm h)
  | .int, _, _, _, hm, h | .bool, _, _, _, hm, h | .nilT, _, _, _, hm, h | .sym, _, _, _, hm, h
  | .float, _, _, _, hm, h | .any, _, _, _, hm, h | .never, _, _, _, hm, h | .cls _, _, _, _, hm, h
  | .clsOf _, _, _, _, hm, h | .nilable _, _, _, _, hm, h | .arrayOf _, _, _, _, hm, h
  | .hashOf _ _, _, _, _, hm, h | .arrow0 _, _, _, _, hm, h | .arrowCons _ _, _, _, _, hm, h
  | .inst _ _, _, _, _, hm, h | .ivar0, _, _, _, hm, h | .ivarCons _ _ _, _, _, _, hm, h
  | .clos _ _ _, _, _, _, hm, h | .sameAs _ _, _, _, _, hm, h => by
    simp only [unionMems, List.mem_singleton] at hm
    subst hm; exact h

theorem mem_of_dedupTysAux : ∀ (l seen : List Ty) {μ : Ty},
    μ ∈ dedupTysAux seen l → μ ∈ seen ∨ μ ∈ l
  | [], seen, μ, h => .inl (by simpa [dedupTysAux] using h)
  | τ :: τs, seen, μ, h => by
    rw [dedupTysAux] at h
    by_cases hc : seen.contains τ
    · rw [if_pos hc] at h
      rcases mem_of_dedupTysAux τs seen h with h | h
      · exact .inl h
      · exact .inr (List.mem_cons_of_mem _ h)
    · rw [if_neg hc] at h
      rcases mem_of_dedupTysAux τs (τ :: seen) h with h | h
      · rcases List.mem_cons.mp h with rfl | h
        · exact .inr List.mem_cons_self
        · exact .inl h
      · exact .inr (List.mem_cons_of_mem _ h)

theorem unionMems_ne_nil : ∀ σ : Ty, unionMems σ ≠ []
  | .union σ _ => by simp [unionMems, unionMems_ne_nil σ]
  | .int | .bool | .nilT | .sym | .float | .any | .never | .cls _ | .clsOf _ | .nilable _
  | .arrayOf _ | .hashOf _ _ | .arrow0 _ | .arrowCons _ _ | .inst _ _ | .ivar0
  | .ivarCons _ _ _ | .clos _ _ _ | .sameAs _ _ => by simp [unionMems]

theorem denM_mkNilable_inv {τ : Ty} {m : Machine} {v : Value} (h : denM (mkNilable τ) m v) :
    denM .nilT m v ∨ denM τ m v := by
  unfold mkNilable at h
  split at h
  · exact .inl h
  · rw [denM] at h
    rcases h with h | h
    · exact .inl (by simpa [denM] using h)
    · exact .inr h

/-- A value in a join is in one of its sides. -/
theorem denM_joinT_inv {σ τ : Ty} {m : Machine} {v : Value} (h : denM (joinT σ τ) m v) :
    denM σ m v ∨ denM τ m v := by
  unfold joinT at h
  split at h
  · exact .inr h
  · split at h
    · exact .inl h
    · cases hj : joinTy σ τ with
      | some ρ =>
        rw [hj] at h
        simp only at h
        unfold joinTy at hj
        split at hj
        · cases hj; exact .inl h
        · split at hj
          · rename_i hn
            cases hj
            rcases denM_mkNilable_inv h with h | h
            · exact .inl (by rw [ty_eq_of_beq hn]; exact h)
            · exact .inr h
          · split at hj
            · rename_i hn
              cases hj
              rcases denM_mkNilable_inv h with h | h
              · exact .inr (by rw [ty_eq_of_beq hn]; exact h)
              · exact .inl h
            · split at hj
              · cases hj; exact .inl h
              · split at hj
                · cases hj; exact .inr h
                · cases hj
      | none =>
        rw [hj] at h
        simp only at h
        obtain ⟨μ, hμ, hd⟩ := denM_unionOf_inv _ (by
          intro he
          have : ∃ μ, μ ∈ unionMems σ := by
            cases hu : unionMems σ with
            | nil => exact absurd hu (unionMems_ne_nil σ)
            | cons a _ => exact ⟨a, by simp⟩
          obtain ⟨μ, hμ⟩ := this
          have := mem_dedupTys (l := unionMems σ ++ unionMems τ) (List.mem_append_left _ hμ)
          rw [he] at this; cases this) h
        rcases mem_of_dedupTysAux _ [] hμ with hμ | hμ
        · cases hμ
        · rcases List.mem_append.mp hμ with hμ | hμ
          · exact .inl (denM_of_unionMems σ hμ hd)
          · exact .inr (denM_of_unionMems τ hμ hd)

#print axioms denM_joinT_inv
end Checker.Soundness
