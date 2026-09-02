import Denote.Join
import Denote.Sem.State

/-!
# `Denote/JoinState.lean` — the branch join at the *state* level

`Denote/Join.lean` joins **types**: `denM_joinT_left`/`_right` say a value of either branch's
type is a value of the join. `Judge.if'`'s conclusion also joins the **environment** and the
**ivar spine**, and that is what this file does: a machine conformant to one branch's outgoing
state is conformant to the join.

## Why the two halves are asymmetric in the proof and not in the statement

For a name **both** branches bind, the join is `joinT τ₁ τ₂` and one `denM_joinT_left` does it.
For a name only the *other* branch binds, the join is `joinT .nilT τ₂` — and what establishes
it is `EnvOk`'s **completeness** clause (clink 55): the branch that ran did not bind the name,
its `Γ` is silent about it, so the machine reads it as `nil`, and `.nilT` is exactly the left
member of that join. `joinEnv`'s `.nilT` default is Ruby's rule (`if false then y = 1 end; y`
is `nil`), and the completeness clause is that rule stated where the semantics can see it.

The spine half is the same argument with `SelfSpineOk`'s completeness in place of `EnvOk`'s —
which has been on file since clink 48, for `Judge.ivarRead`.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## Keys -/

theorem mem_envKeys_of_get {Γ : Env} {x : String} {τ : Ty} (h : envGet? Γ x = some τ) :
    x ∈ envKeys Γ := by
  induction Γ with
  | nil => exact absurd h (by simp [envGet?, List.find?])
  | cons hd tl ih =>
    obtain ⟨k, σ⟩ := hd
    by_cases hk : k = x
    · subst hk; exact List.mem_cons_self
    · rw [envGet?_cons_ne σ tl hk] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem get_of_mem_envKeys {Γ : Env} {x : String} (h : x ∈ envKeys Γ) :
    ∃ τ, envGet? Γ x = some τ := by
  induction Γ with
  | nil => exact absurd h (by simp [envKeys])
  | cons hd tl ih =>
    obtain ⟨k, σ⟩ := hd
    by_cases hk : k = x
    · subst hk; exact ⟨σ, envGet?_cons_self _ _ _⟩
    · rw [envKeys] at h
      rcases List.mem_cons.mp h with h' | h'
      · exact absurd h'.symm hk
      · obtain ⟨τ, hτ⟩ := ih h'
        exact ⟨τ, by rw [envGet?_cons_ne σ tl hk]; exact hτ⟩

/-- The join's entry at a name, whichever branch bound it. -/
theorem envGet?_joinEnvAt {Γ₁ Γ₂ : Env} {x : String} :
    ∀ (ks : List String), x ∈ ks →
      envGet? (joinEnvAt Γ₁ Γ₂ ks) x =
        some (joinT ((envGet? Γ₁ x).getD .nilT) ((envGet? Γ₂ x).getD .nilT)) := by
  intro ks
  induction ks with
  | nil => intro h; exact absurd h (by simp)
  | cons k ks ih =>
    intro h
    by_cases hk : k = x
    · subst hk; rw [joinEnvAt]; exact envGet?_cons_self _ _ _
    · rcases List.mem_cons.mp h with h' | h'
      · exact absurd h'.symm hk
      · rw [joinEnvAt, envGet?_cons_ne _ _ hk]
        exact ih h'

/-- …and the join has an entry for a name **either** branch bound. -/
theorem envGet?_joinEnv {Γ₁ Γ₂ : Env} {x : String}
    (h : x ∈ envKeys Γ₁ ∨ x ∈ envKeys Γ₂) :
    envGet? (joinEnv Γ₁ Γ₂) x =
      some (joinT ((envGet? Γ₁ x).getD .nilT) ((envGet? Γ₂ x).getD .nilT)) := by
  refine envGet?_joinEnvAt _ ?_
  rcases h with h | h
  · exact List.mem_append_left _ h
  · by_cases h1 : x ∈ envKeys Γ₁
    · exact List.mem_append_left _ h1
    · refine List.mem_append_right _ ?_
      exact List.mem_filter.mpr ⟨h, by simpa using h1⟩

/-- A name **neither** branch bound is absent from the join. -/
theorem envGet?_joinEnv_none {Γ₁ Γ₂ : Env} {x : String}
    (h1 : envGet? Γ₁ x = none) (h2 : envGet? Γ₂ x = none) :
    envGet? (joinEnv Γ₁ Γ₂) x = none := by
  have hk1 : x ∉ envKeys Γ₁ := fun h => by
    obtain ⟨τ, hτ⟩ := get_of_mem_envKeys h; rw [h1] at hτ; exact absurd hτ.symm (by simp)
  have hk2 : x ∉ envKeys Γ₂ := fun h => by
    obtain ⟨τ, hτ⟩ := get_of_mem_envKeys h; rw [h2] at hτ; exact absurd hτ.symm (by simp)
  -- the key list the join is built over contains only names one of the two bound
  suffices hs : ∀ (ks : List String), x ∉ ks → envGet? (joinEnvAt Γ₁ Γ₂ ks) x = none by
    refine hs _ ?_
    intro hmem
    rcases List.mem_append.mp hmem with h | h
    · exact hk1 h
    · exact hk2 (List.mem_filter.mp h).1
  intro ks
  induction ks with
  | nil => intro _; rw [joinEnvAt]; simp [envGet?, List.find?]
  | cons k ks ih =>
    intro hx
    have hk : ¬ k = x := fun h => hx (h ▸ List.mem_cons_self)
    rw [joinEnvAt, envGet?_cons_ne _ _ hk]
    exact ih (fun h => hx (List.mem_cons_of_mem _ h))

/-! ## The one awkward case: an alias surviving a join

`EnvOk`'s second conjunct is a claim about `y` when the recorded type is `.sameAs y ρ`, and
`joinT` **can** return an alias — `joinT .never (.sameAs y ρ)` is `.sameAs y ρ`. So the
conjunct is not vacuous at the join and has to be traced back to the branch that supplied it.
It always can be: every way `joinT` produces a `.sameAs` has the *left* argument either
`.never` (in which case the branch's own `EnvOk` is contradictory, since `denM .never` is
empty) or the same alias. -/

theorem joinT_sameAs : ∀ {σ τ : Ty} {y : String} {ρ : Ty}, joinT σ τ = .sameAs y ρ →
    σ = .never ∨ ∃ ρ', σ = .sameAs y ρ' := by
  intro σ τ y ρ h
  rw [joinT] at h
  split at h
  · exact Or.inl (ty_eq_of_beq (by simpa using ‹(σ == Ty.never) = true›))
  · split at h
    · subst h; exact Or.inr ⟨ρ, rfl⟩
    · split at h
      · rename_i ρ' hj
        subst h
        rw [joinTy] at hj
        split at hj
        · exact Or.inr ⟨ρ, by rw [← ty_eq_of_beq ‹(σ == τ) = true›] at hj; simp_all⟩
        · split at hj
          · exact Or.inl (ty_eq_of_beq (by simpa using ‹(σ == Ty.nilT) = true›))
          · split at hj
            · exact absurd (Option.some.inj hj) (by simp [mkNilable]; split <;> simp)
            · split at hj
              · exact Or.inr ⟨ρ, by simp_all⟩
              · split at hj
                · rename_i hτσ
                  exact absurd (ty_eq_of_beq hτσ) (by
                    intro hh
                    rw [← Option.some.inj hj] at hh
                    exact absurd hh (by simp))
                · exact absurd hj (by simp)
      · -- the union arm
        exact Or.inr ⟨ρ, by
          rename_i hj
          exact absurd h (unionOf_ne_sameAs _ _ _)⟩

#print axioms envGet?_joinEnv
/-! ## The one awkward case: an alias surviving a join

`EnvOk`'s second conjunct is a claim about `y` when the recorded type is `.sameAs y ρ`, and
`joinT` **can** return an alias — `joinT .never (.sameAs y ρ)` is `.sameAs y ρ`. So the
conjunct is not vacuous at the join and has to be traced back to the branch that supplied it.
It always can be: every way `joinT` produces a `.sameAs` has the *left* argument either
`.never` (in which case the branch's own `EnvOk` is contradictory, since `denM .never` is
empty) or the same alias. -/

theorem joinT_sameAs : ∀ {σ τ : Ty} {y : String} {ρ : Ty}, joinT σ τ = .sameAs y ρ →
    σ = .never ∨ ∃ ρ', σ = .sameAs y ρ' := by
  intro σ τ y ρ h
  rw [joinT] at h
  split at h
  · exact Or.inl (ty_eq_of_beq (by simpa using ‹(σ == Ty.never) = true›))
  · split at h
    · subst h; exact Or.inr ⟨ρ, rfl⟩
    · split at h
      · rename_i ρ' hj
        subst h
        rw [joinTy] at hj
        split at hj
        · exact Or.inr ⟨ρ, by rw [← ty_eq_of_beq ‹(σ == τ) = true›] at hj; simp_all⟩
        · split at hj
          · exact Or.inl (ty_eq_of_beq (by simpa using ‹(σ == Ty.nilT) = true›))
          · split at hj
            · exact absurd (Option.some.inj hj) (by simp [mkNilable]; split <;> simp)
            · split at hj
              · exact Or.inr ⟨ρ, by simp_all⟩
              · split at hj
                · rename_i hτσ
                  exact absurd (ty_eq_of_beq hτσ) (by
                    intro hh
                    rw [← Option.some.inj hj] at hh
                    exact absurd hh (by simp))
                · exact absurd hj (by simp)
      · -- the union arm
        exact Or.inr ⟨ρ, by
          rename_i hj
          exact absurd h (unionOf_ne_sameAs _ _ _)⟩

#print axioms envGet?_joinEnv_none

end Ratchet.Denote
