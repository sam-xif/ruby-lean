import Denote.Sem.Narrow
import Denote.JoinState

/-!
# `Denote/Sem/NarrowState.lean` — narrowing soundness, the state half

`Denote/Sem/Narrow.lean` proves the six type-level lemmas: *the refined type still denotes the
value, given what the branch tells you about it*. This file turns those into the statement a
rung actually consumes — **`StateOk` at the refined environment** — and it splits in two:

* the **transports** (`EnvOk_refineOne`, `SelfSpineOk_ivarSet`): given the branch's fact about
  one name's value, the whole conformance survives the refinement of that one binding;
* the **inversions** (one per shape `narrowCond?` recognises): the branch's fact, read out of
  the condition's own run.

The transports are here; the inversions need the dispatch chains and live with them.

## What `refineOne` does that makes the transport non-trivial

It refines **two** bindings, not one: `Ty.sameAs`'s whole point is that `case v when C` tests a
desugarer temporary while the branch bodies use `v`, so refining only the tested name refines
the wrong one. So the transport's hypothesis is about both names — and `EnvOk`'s own alias
conjunct is what says they hold the same value, which is what makes one fact serve both.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## Why there is no "a refined type is not an alias" lemma here

There was going to be one, and it is **false**: `falsyTy (union (sameAs y ρ) int)` is
`joinT (sameAs y (falsyTy ρ)) never`, which *is* the `sameAs`. So refining a binding the
environment describes as a union would record an alias claim the union never made, and
`EnvOk`'s second conjunct is precisely that claim.

That is `found-issues.md` §F15, and it is fixed in `refineOne` rather than worked around here:
the ordinary arm now declines to refine when the result would be an alias. So this file's
transport gets the fact for free, from the `if` in the checker. -/

/-- **Replacing one binding preserves `EnvOk`**, given the two things `EnvOk` says about a
binding: the value is in the (stripped) type, and an alias holds the same object as its target.

Generic in the type, which is what makes it usable twice in `refineOne`'s alias arm — where two
bindings move — without knowing anything about the refinement functions. -/
theorem EnvOk_envSet {Γ : Env} {x : String} {τ : Ty} {m : Machine} (h : EnvOk Γ m)
    (hden : denM (Ratchet.stripAlias τ) m (m.getLocal x))
    (hal : ∀ y ρ, τ = .sameAs y ρ → m.getLocal x = m.getLocal y) :
    EnvOk (Ratchet.envSet Γ x τ) m := by
  obtain ⟨hlow, hcomp⟩ := h
  refine ⟨fun z σ hz => ?_, fun z hz => ?_⟩
  · by_cases hzx : z = x
    · subst hzx
      rw [envGet?_envSet_self] at hz
      injection hz with hz
      subst hz
      exact ⟨hden, hal⟩
    · rw [envGet?_envSet_ne Γ x z _ hzx] at hz
      exact hlow z σ hz
  · by_cases hzx : z = x
    · subst hzx; rw [envGet?_envSet_self] at hz; exact absurd hz (by simp)
    · rw [envGet?_envSet_ne Γ x z _ hzx] at hz; exact hcomp z hz

#print axioms EnvOk_envSet

/-! ## The spine transport

`narrowSpine` refines an **instance variable**'s entry, so the `.ivar` shapes need
`SelfSpineOk` to survive an `ivarSet`. Two facts do it, and the second is why `SelfSpineOk`'s
completeness conjunct exists: `ivarSet` on a name the spine does not carry **appends**, so the
refined spine can be longer than the one conformance was established for, and the appended
entry's value has to be known. -/

/-- `denSpineFrom` after an `ivarSet`: the walk sees the refined type at `x` and is unchanged
elsewhere. Stated over the `seen` set because that is what the walk threads — an entry already
shadowed stays shadowed, which is the case that makes the induction go through. -/
theorem denSpineFrom_ivarSet : ∀ (I : Ty) (seen : List String) (x : String) (ρ : Ty)
    (m : Machine) (g : String → Value),
    denSpineFrom seen I m g → (x ∈ seen ∨ denM ρ m (g x)) →
    denSpineFrom seen (Ratchet.ivarSet I x ρ) m g
  | .ivar0, seen, x, ρ, m, g, _, hρ => by
    rw [Ratchet.ivarSet, denSpineFrom]
    exact ⟨hρ, by rw [denSpineFrom]; trivial⟩
  | .ivarCons n τ rest, seen, x, ρ, m, g, h, hρ => by
    rw [Ratchet.ivarSet]
    rw [denSpineFrom] at h
    obtain ⟨hn, hrest⟩ := h
    by_cases hnx : n = x
    · subst hnx
      rw [if_pos (by simp)]
      rw [denSpineFrom]
      exact ⟨hρ, hrest⟩
    · rw [if_neg (by simpa using hnx)]
      rw [denSpineFrom]
      refine ⟨hn, denSpineFrom_ivarSet rest (n :: seen) x ρ m g hrest ?_⟩
      rcases hρ with h' | h'
      · exact Or.inl (List.mem_cons_of_mem _ h')
      · exact Or.inr h'
  | .int, _, _, _, _, _, h, _ | .float, _, _, _, _, _, h, _ | .sym, _, _, _, _, _, h, _
  | .bool, _, _, _, _, _, h, _ | .nilT, _, _, _, _, _, h, _ | .any, _, _, _, _, _, h, _
  | .never, _, _, _, _, _, h, _ | .cls _, _, _, _, _, _, h, _
  | .clsOf _, _, _, _, _, _, h, _ | .nilable _, _, _, _, _, _, h, _
  | .union _ _, _, _, _, _, _, h, _ | .arrayOf _, _, _, _, _, _, h, _
  | .hashOf _ _, _, _, _, _, _, h, _ | .inst _ _, _, _, _, _, _, h, _
  | .sameAs _ _, _, _, _, _, _, h, _ | .arrow0 _, _, _, _, _, _, h, _
  | .arrowCons .., _, _, _, _, _, h, _ | .clos .., _, _, _, _, _, h, _ => by
    -- not a spine: `denSpineFrom` is `False`, and `ivarSet` is the identity
    exact absurd h (by simp [denSpineFrom])

/-- **`SelfSpineOk` survives refining one instance variable.** -/
theorem SelfSpineOk_ivarSet {I : Ty} {x : String} {ρ : Ty} {m : Machine}
    (h : SelfSpineOk I m) (hρ : denM ρ m (ivarOf m.heap m.currentFrame.self x))
    (hcomp : ∀ y, Ratchet.ivarGet? (Ratchet.ivarSet I x ρ) y = none →
      ivarOf m.heap m.currentFrame.self y = .nil) :
    SelfSpineOk (Ratchet.ivarSet I x ρ) m := by
  obtain ⟨hden, _⟩ := h
  refine ⟨?_, hcomp⟩
  rw [denSpine] at hden ⊢
  exact denSpineFrom_ivarSet I [] x ρ m _ hden (Or.inr hρ)

#print axioms denSpineFrom_ivarSet
#print axioms SelfSpineOk_ivarSet


/-! ## The else-side environment refinement

Stated **pointwise**: the caller supplies "the refinement is true of whatever type this local's
value has", and the arms of `refineOne` are then bookkeeping. That shape is what makes the
alias arm free — `EnvOk`'s own conjunct says the alias and its target hold the *same value*, so
one fact about `x`'s value serves `y`'s binding too. -/

/-- A type the alias test rejects is its own `stripAlias`. -/
theorem stripAlias_of_not_alias {τ : Ty} (h : Ratchet.isAliasTy τ = false) :
    Ratchet.stripAlias τ = τ := by
  cases τ <;> simp_all [Ratchet.isAliasTy, Ratchet.stripAlias]

theorem EnvOk_refineOne_else {C : Ratchet.CTable} {Γ : Env} {x : String}
    {nk : Ratchet.NarrowKind} {m : Machine} (h : EnvOk Γ m)
    (hfact : ∀ τ, denM τ m (m.getLocal x) →
      denM (Ratchet.refineElse C nk τ) m (m.getLocal x)) :
    EnvOk (Ratchet.refineOne C nk false Γ x) m := by
  have hlow := h.1
  unfold Ratchet.refineOne
  dsimp only
  cases hgx : envGet? Γ x with
  | none => exact h
  | some τx =>
    cases τx with
    | sameAs y ρ =>
      -- the alias arm: the alias keeps its target and refines its payload, and `y`'s own
      -- binding is refined from itself
      simp only [Bool.false_eq_true, if_false]
      have hxy : m.getLocal x = m.getLocal y := (hlow x (.sameAs y ρ) hgx).2 y ρ rfl
      have hρ : denM ρ m (m.getLocal x) := (hlow x (.sameAs y ρ) hgx).1
      have h1 : EnvOk (Ratchet.envSet Γ x (.sameAs y (Ratchet.refineElse C nk ρ))) m :=
        EnvOk_envSet h (by
          show denM (Ratchet.refineElse C nk ρ) m (m.getLocal x)
          exact hfact ρ hρ) (fun y' ρ' he => by
          injection he with he₁ _
          rw [he₁] at hxy
          exact hxy)
      cases hgy : envGet? (Ratchet.envSet Γ x (.sameAs y (Ratchet.refineElse C nk ρ))) y with
      | none => exact h1
      | some σy =>
        have hy := (h1.1 y σy hgy).1
        rw [← hxy] at hy
        simp only [Bool.false_eq_true, if_false]
        refine EnvOk_envSet h1 ?_ ?_
        · -- `y`'s value *is* `x`'s, so the same fact applies; and §F15's guard again
          rw [← hxy]
          split
          · exact hy
          · rename_i hna
            rw [stripAlias_of_not_alias (by simpa using hna)]
            exact hfact (Ratchet.stripAlias σy) hy
        · intro y' ρ' he
          split at he
          · rw [← hxy, ← (h1.1 y σy hgy).2 y' ρ' he, hxy]
          · rename_i hna
            exact absurd he (by
              intro hc
              rw [hc] at hna
              exact absurd hna (by simp [Ratchet.isAliasTy]))
    | _ =>
      simp only [Bool.false_eq_true, if_false]
      refine EnvOk_envSet h ?_ ?_
      · split
        · exact (hlow x _ hgx).1
        · rename_i hna
          rw [stripAlias_of_not_alias (by simpa using hna)]
          exact hfact _ (hlow x _ hgx).1
      · intro y' ρ' he
        split at he
        · exact (hlow x _ hgx).2 y' ρ' he
        · rename_i hna
          exact absurd he (by
            intro hc
            rw [hc] at hna
            exact absurd hna (by simp [Ratchet.isAliasTy]))


/-- **The then side**, and it is the same proof — a near-copy rather than one lemma
parameterised over `refineOne`'s `thenSide`, which was tried first: the function's own body is
`let refine := fun τ => if thenSide then …`, so a variable side leaves an `if` inside every
goal, and `split` then picks *it* rather than the `isAliasTy` guard the proof is analysing.
Two readable scripts beat one that has to disambiguate three `if`s. -/
theorem EnvOk_refineOne_then {C : Ratchet.CTable} {Γ : Env} {x : String}
    {nk : Ratchet.NarrowKind} {m : Machine} (h : EnvOk Γ m)
    (hfact : ∀ τ, denM τ m (m.getLocal x) →
      denM (Ratchet.refineThen C nk τ) m (m.getLocal x)) :
    EnvOk (Ratchet.refineOne C nk true Γ x) m := by
  have hlow := h.1
  unfold Ratchet.refineOne
  dsimp only
  cases hgx : envGet? Γ x with
  | none => exact h
  | some τx =>
    cases τx with
    | sameAs y ρ =>
      -- the alias arm: the alias keeps its target and refines its payload, and `y`'s own
      -- binding is refined from itself
      simp only [if_true]
      have hxy : m.getLocal x = m.getLocal y := (hlow x (.sameAs y ρ) hgx).2 y ρ rfl
      have hρ : denM ρ m (m.getLocal x) := (hlow x (.sameAs y ρ) hgx).1
      have h1 : EnvOk (Ratchet.envSet Γ x (.sameAs y (Ratchet.refineThen C nk ρ))) m :=
        EnvOk_envSet h (by
          show denM (Ratchet.refineThen C nk ρ) m (m.getLocal x)
          exact hfact ρ hρ) (fun y' ρ' he => by
          injection he with he₁ _
          rw [he₁] at hxy
          exact hxy)
      cases hgy : envGet? (Ratchet.envSet Γ x (.sameAs y (Ratchet.refineThen C nk ρ))) y with
      | none => exact h1
      | some σy =>
        have hy := (h1.1 y σy hgy).1
        rw [← hxy] at hy
        simp only [if_true]
        refine EnvOk_envSet h1 ?_ ?_
        · -- `y`'s value *is* `x`'s, so the same fact applies; and §F15's guard again
          rw [← hxy]
          split
          · exact hy
          · rename_i hna
            rw [stripAlias_of_not_alias (by simpa using hna)]
            exact hfact (Ratchet.stripAlias σy) hy
        · intro y' ρ' he
          split at he
          · rw [← hxy, ← (h1.1 y σy hgy).2 y' ρ' he, hxy]
          · rename_i hna
            exact absurd he (by
              intro hc
              rw [hc] at hna
              exact absurd hna (by simp [Ratchet.isAliasTy]))
    | _ =>
      simp only [if_true]
      refine EnvOk_envSet h ?_ ?_
      · split
        · exact (hlow x _ hgx).1
        · rename_i hna
          rw [stripAlias_of_not_alias (by simpa using hna)]
          exact hfact _ (hlow x _ hgx).1
      · intro y' ρ' he
        split at he
        · exact (hlow x _ hgx).2 y' ρ' he
        · rename_i hna
          exact absurd he (by
            intro hc
            rw [hc] at hna
            exact absurd hna (by simp [Ratchet.isAliasTy]))

#print axioms EnvOk_refineOne_then

#print axioms EnvOk_refineOne_else


/-- **`ivarSet` only touches the name it sets.** So a name the *refined* spine is silent about
was already absent, which is what `SelfSpineOk`'s completeness conjunct needs. -/
theorem ivarGet?_ivarSet_none : ∀ (I : Ty) (x : String) (ρ : Ty) (y : String),
    Ratchet.ivarGet? (Ratchet.ivarSet I x ρ) y = none → Ratchet.ivarGet? I y = none
  | .ivar0, x, ρ, y, h => by
    simp [Ratchet.ivarGet?]
  | .ivarCons n τ rest, x, ρ, y, h => by
    rw [Ratchet.ivarSet] at h
    by_cases hnx : n = x
    · subst hnx
      rw [if_pos (by simp), Ratchet.ivarGet?] at h
      rw [Ratchet.ivarGet?]
      split at h
      · exact absurd h (by simp)
      · rename_i hne
        rw [if_neg hne]
        exact h
    · rw [if_neg (by simpa using hnx), Ratchet.ivarGet?] at h
      rw [Ratchet.ivarGet?]
      split at h
      · exact absurd h (by simp)
      · rename_i hne
        rw [if_neg hne]
        exact ivarGet?_ivarSet_none rest x ρ y h
  | .int, _, _, _, h | .float, _, _, _, h | .sym, _, _, _, h | .bool, _, _, _, h
  | .nilT, _, _, _, h | .any, _, _, _, h | .never, _, _, _, h | .cls _, _, _, _, h
  | .clsOf _, _, _, _, h | .nilable _, _, _, _, h | .union _ _, _, _, _, h
  | .arrayOf _, _, _, _, h | .hashOf _ _, _, _, _, h | .inst _ _, _, _, _, h
  | .sameAs _ _, _, _, _, h | .arrow0 _, _, _, _, h | .arrowCons .., _, _, _, h
  | .clos .., _, _, _, h => by
    -- not a spine: `ivarSet` is the identity
    simpa [Ratchet.ivarSet] using h

#print axioms ivarGet?_ivarSet_none


/-! `Denote/Rules/Read.lean` already has the spine projection this needed
(`denSpineFrom_get` — `ivarGet?` takes the first match and `denSpineFrom` skips a shadowed
entry, so the two agree), proved there for `Judge.ivarRead`. It is used from the assembly
rather than restated here. -/


end Ratchet.Denote
