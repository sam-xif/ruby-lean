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
        some (joinBinding ((envGet? Γ₁ x).getD .nilT) ((envGet? Γ₂ x).getD .nilT)) := by
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
      some (joinBinding ((envGet? Γ₁ x).getD .nilT) ((envGet? Γ₂ x).getD .nilT)) := by
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

/-! ## Binding joins preserve values without manufacturing identities -/

theorem denM_joinBinding_left {σ τ : Ty} {m : Machine} {v : Value}
    (h : denM σ m v) : denM (joinBinding σ τ) m v := by
  unfold joinBinding
  split
  · exact h
  · exact denM_deAlias.mpr (denM_joinT_left h)

theorem denM_joinBinding_right {σ τ : Ty} {m : Machine} {v : Value}
    (h : denM τ m v) : denM (joinBinding σ τ) m v := by
  unfold joinBinding
  split
  · rename_i heq; rw [ty_eq_of_beq heq]; exact h
  · exact denM_deAlias.mpr (denM_joinT_right h)

theorem joinBinding_alias {σ τ ρ : Ty} {y : String}
    (h : joinBinding σ τ = .sameAs y ρ) : σ = .sameAs y ρ ∧ τ = .sameAs y ρ := by
  unfold joinBinding at h
  split at h
  · rename_i heq
    exact ⟨h, (ty_eq_of_beq heq).symm.trans h⟩
  · exact False.elim (deAlias_ne_sameAs _ y ρ h)

-- The old join produced an alias from a union that made no identity promise.
#guard joinT (.union (.sameAs "y" .int) (.sameAs "y" .int)) (.sameAs "y" .int) ==
  .sameAs "y" .int
#guard joinBinding (.union (.sameAs "y" .int) (.sameAs "y" .int)) (.sameAs "y" .int) == .int
#guard joinBinding (.sameAs "y" .int) (.sameAs "y" .int) == .sameAs "y" .int

private theorem envOk_getD {Γ : Env} {m : Machine} (h : EnvOk Γ m) (x : String) :
    denM ((envGet? Γ x).getD .nilT) m (m.getLocal x) := by
  cases hg : envGet? Γ x with
  | none => simp [h.2 x hg, denM, isNilV]
  | some τ => exact denM_stripAlias.mp (h.1 x τ hg).1

private theorem envOk_alias_getD {Γ : Env} {m : Machine} (h : EnvOk Γ m)
    {x y : String} {ρ : Ty} (ha : (envGet? Γ x).getD .nilT = .sameAs y ρ) :
    m.getLocal x = m.getLocal y := by
  cases hg : envGet? Γ x with
  | none => simp [hg] at ha
  | some τ => exact (h.1 x τ hg).2 y ρ (by simpa [hg] using ha)

private theorem get_none_of_not_mem {Γ : Env} {x : String} (h : x ∉ envKeys Γ) :
    envGet? Γ x = none := by
  cases hg : envGet? Γ x with
  | none => rfl
  | some τ => exact False.elim (h (mem_envKeys_of_get hg))

/-- The side is an explicit parameter so both branches use exactly the same proof. -/
theorem envOk_joinEnv (Γ₁ Γ₂ : Env) {m : Machine} (left : Bool)
    (h : EnvOk (if left then Γ₁ else Γ₂) m) : EnvOk (joinEnv Γ₁ Γ₂) m := by
  constructor
  · intro x τ hx
    have hk : x ∈ envKeys Γ₁ ∨ x ∈ envKeys Γ₂ := by
      by_cases hl : x ∈ envKeys Γ₁
      · exact Or.inl hl
      by_cases hr : x ∈ envKeys Γ₂
      · exact Or.inr hr
      rw [envGet?_joinEnv_none (get_none_of_not_mem hl) (get_none_of_not_mem hr)] at hx
      cases hx
    rw [envGet?_joinEnv hk] at hx
    cases hx
    constructor
    · apply denM_stripAlias.mpr
      cases left with
      | false => exact denM_joinBinding_right (envOk_getD h x)
      | true => exact denM_joinBinding_left (envOk_getD h x)
    · intro y ρ ha
      obtain ⟨hl, hr⟩ := joinBinding_alias ha
      cases left with
      | false => exact envOk_alias_getD h hr
      | true => exact envOk_alias_getD h hl
  · intro x hx
    have hk : x ∉ envKeys Γ₁ ∧ x ∉ envKeys Γ₂ := by
      constructor <;> intro hk
      all_goals
        have hj := envGet?_joinEnv (Γ₁ := Γ₁) (Γ₂ := Γ₂)
          (x := x) (by first | exact Or.inl hk | exact Or.inr hk)
        rw [hx] at hj
        cases hj
    cases left with
    | false => exact h.2 x (get_none_of_not_mem hk.2)
    | true => exact h.2 x (get_none_of_not_mem hk.1)

theorem StateOk_joinEnv {κ : Ctx} {Γ₁ Γ₂ : Env} {I : Ty} {m : Machine} (left : Bool)
    (h : StateOk κ (if left then Γ₁ else Γ₂) I m) :
    StateOk κ (joinEnv Γ₁ Γ₂) I m :=
  { h with env := envOk_joinEnv Γ₁ Γ₂ left h.env }

#print axioms StateOk_joinEnv

end Ratchet.Denote
