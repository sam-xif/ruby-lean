import Denote.Sem.Judge
import Denote.Join

/-!
# `Denote/Sem/Narrow.lean` — narrowing soundness, the type-level half

`Judge.if'`/`ifNoElse` type each branch in a **narrowed** environment: if control reached the
then-branch, the condition evaluated truthy, and for a condition of a recognized shape that is
information about a local's or an instance variable's type. `Ratchet/Judge.lean`'s
`narrowEnvs`/`narrowSpine` compute it; nothing has said it is *true*.

The claim splits cleanly in two, and this file is the half that needs no run:

> **the refined type still denotes the value**, given what the branch tells you about it.

Six functions, six lemmas, each an induction over `Ty` following the function's own recursion.
The pattern is the same in all six and worth stating once:

* the arm that answers `.never` is where the branch is **unreachable**, and it is discharged by
  the hypothesis rather than by `denM` — `truthyTy .nilT = .never` is sound precisely because
  `nil` is not truthy, so `denM .nilT m v` and `v.truthy = true` cannot both hold;
* `.nilable`/`.union` recurse and rebuild with `joinT`, so they need "a join is an upper
  bound" (`Denote/Join.lean`) and nothing else;
* the catch-all `τ => τ` is `exact h`.

`Denote/Sem/notes.md`'s twelfth stall point lists these six first for a reason: they are the
part with no dependence on the interpreter at all, so if one of them is *false* the fix is in
`Ratchet/Ty.lean` and no run has to be inverted to find out.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## `if x` — truthiness -/

/-- **`truthyTy` keeps the truthy values.** The `.nilT` arm is the interesting one: it answers
`.never`, whose denotation is `False`, and that is discharged from `v.truthy = true` — `nil` is
not truthy. Everything else either recurses or is the identity. -/
theorem denM_truthyTy : ∀ (τ : Ty) {m : Machine} {v : Value},
    denM τ m v → v.truthy = true → denM (Ratchet.truthyTy τ) m v
  | .nilT, _, v, h, ht => by
    -- `denM .nilT` says the value *is* `nil`, and `nil` is not truthy
    cases v <;> simp_all [denM, isNilV, Value.truthy]
  | .nilable ρ, m, v, h, ht => by
    rw [Ratchet.truthyTy]
    rw [denM] at h
    rcases h with hnil | hρ
    · -- the `nil` half is excluded by truthiness, so the type is `ρ`'s refinement
      cases v <;> simp_all [isNilV, Value.truthy]
    · exact denM_truthyTy ρ hρ ht
  | .union σ τ, m, v, h, ht => by
    rw [Ratchet.truthyTy]
    rw [denM] at h
    rcases h with hσ | hτ
    · exact denM_joinT_left (denM_truthyTy σ hσ ht)
    · exact denM_joinT_right (denM_truthyTy τ hτ ht)
  | .int, _, _, h, _ => h
  | .bool, _, _, h, _ => h
  | .sym, _, _, h, _ => h
  | .float, _, _, h, _ => h
  | .any, _, _, h, _ => h
  | .never, _, _, h, _ => h
  | .cls _, _, _, h, _ => h
  | .clsOf _, _, _, h, _ => h
  | .arrayOf _, _, _, h, _ => h
  | .hashOf _ _, _, _, h, _ => h
  | .inst _ _, _, _, h, _ => h
  | .sameAs _ _, _, _, h, _ => h
  | .ivar0, _, _, h, _ => h
  | .ivarCons .., _, _, h, _ => h
  | .arrow0 _, _, _, h, _ => h
  | .arrowCons .., _, _, h, _ => h
  | .clos .., _, _, h, _ => h

/-- **`falsyTy` keeps the falsy values.** The catch-all is `.never` here rather than the
identity, and that is the asymmetry `Ratchet/Ty.lean`'s docstring calls the whole point: `if x`
where `x : Integer` has an unreachable else-branch. It is sound because Ruby's falsiness is
exactly `{nil, false}`, and this proof is where that is *used* — every immediate arm discharges
`.never`'s `False` from `v.truthy = false`. -/
theorem denM_falsyTy : ∀ (τ : Ty) {m : Machine} {v : Value},
    denM τ m v → v.truthy = false → denM (Ratchet.falsyTy τ) m v
  | .nilT, _, _, h, _ => h
  | .bool, _, _, h, _ => h
  | .any, _, _, h, _ => h
  | .nilable ρ, m, v, h, ht => by
    rw [Ratchet.falsyTy]
    rw [denM] at h
    rcases h with hnil | hρ
    · exact denM_joinT_left (by simpa [denM] using hnil)
    · exact denM_joinT_right (denM_falsyTy ρ hρ ht)
  | .union σ τ, m, v, h, ht => by
    rw [Ratchet.falsyTy]
    rw [denM] at h
    rcases h with hσ | hτ
    · exact denM_joinT_left (denM_falsyTy σ hσ ht)
    · exact denM_joinT_right (denM_falsyTy τ hτ ht)
  | .int, _, v, h, ht => by cases v <;> simp_all [denM, isIntV, Value.truthy]
  | .sym, _, v, h, ht => by cases v <;> simp_all [denM, isSymV, Value.truthy]
  | .float, _, v, h, ht => by cases v <;> simp_all [denM, isFltV, Value.truthy]
  | .never, _, _, h, _ => h
  -- the two nominal arms are the identity now (see `Ratchet/Ty.lean`), so they are free
  | .cls _, _, _, h, _ => h
  | .inst _ _, _, _, h, _ => h
  | .clsOf _, _, v, h, ht => by
    cases v <;> simp_all [denM, isClassRefNamed, Value.truthy]
  | .arrayOf _, _, v, h, ht => by
    cases v <;> simp_all [denM, arrElems?, Value.truthy]
  | .hashOf _ _, _, v, h, ht => by
    cases v <;> simp_all [denM, hshEntries?, Value.truthy]
  | .sameAs _ ρ, m, v, h, ht => by
    -- an alias denotes exactly its payload, and `falsyTy` now refines *under* it (the arm
    -- this proof asked for — see `Ratchet/Ty.lean`)
    rw [Ratchet.falsyTy, denM]
    rw [denM] at h
    exact denM_falsyTy ρ h ht
  -- spines are not value types: `denM` is `False`, so there is nothing to refine
  | .ivar0, _, _, h, _ => by rw [denM] at h; exact h.elim
  | .ivarCons .., _, _, h, _ => by rw [denM] at h; exact h.elim
  -- a Proc is a reference, and every reference is truthy
  | .arrow0 _, _, v, h, ht => by
    rw [denM] at h
    cases v <;> simp_all [isProcV, procClosure?, Value.truthy]
  | .arrowCons .., _, v, h, ht => by
    rw [denM] at h
    cases v <;> simp_all [isProcV, procClosure?, Value.truthy]
  | .clos .., _, v, h, ht => by
    rw [denM] at h
    obtain ⟨cl, hcl, _⟩ := h
    cases v <;> simp_all [procClosure?, Value.truthy]


/-! ## `if x.nil?` — nil-ness

`nil?` differs from truthiness at exactly one value, `false`, and that is why these are two
pairs of functions rather than one: `false.nil?` is `false`, so the then-branch of `if x.nil?`
learns strictly more than the then-branch of `if !x`. -/

/-- **`isNilTy` keeps the `nil` values.** Hypothesis is `v = .nil`, which is stronger than
falsiness — so the `.bool` arm answers `.never` here where `falsyTy` answered `.bool`. -/
theorem denM_isNilTy : ∀ (τ : Ty) {m : Machine} {v : Value},
    denM τ m v → v = .nil → denM (Ratchet.isNilTy τ) m v
  | .nilT, _, _, h, _ => h
  | .any, _, _, h, _ => h
  | .nilable _, _, v, _, hv => by subst hv; rw [Ratchet.isNilTy, denM]; rfl
  | .union σ τ, m, v, h, hv => by
    rw [Ratchet.isNilTy]
    rw [denM] at h
    rcases h with hσ | hτ
    · exact denM_joinT_left (denM_isNilTy σ hσ hv)
    · exact denM_joinT_right (denM_isNilTy τ hτ hv)
  | .sameAs _ ρ, m, v, h, hv => by
    rw [Ratchet.isNilTy, denM]
    rw [denM] at h
    exact denM_isNilTy ρ h hv
  | .cls _, _, _, h, _ => h
  | .inst _ _, _, _, h, _ => h
  | .int, _, v, h, hv => by rw [denM, hv] at h; exact absurd h (by simp [isIntV])
  | .bool, _, v, h, hv => by rw [denM, hv] at h; exact absurd h (by simp [isBoolV])
  | .sym, _, v, h, hv => by rw [denM, hv] at h; exact absurd h (by simp [isSymV])
  | .float, _, v, h, hv => by rw [denM, hv] at h; exact absurd h (by simp [isFltV])
  | .never, _, _, h, _ => h
  | .clsOf _, _, v, h, hv => by
    rw [denM, hv] at h; exact absurd h (by simp [isClassRefNamed])
  | .arrayOf _, _, v, h, hv => by
    rw [denM, hv] at h; exact absurd h (by simp [arrElems?])
  | .hashOf _ _, _, v, h, hv => by
    rw [denM, hv] at h; exact absurd h (by simp [hshEntries?])
  | .ivar0, _, _, h, _ => by rw [denM] at h; exact h.elim
  | .ivarCons .., _, _, h, _ => by rw [denM] at h; exact h.elim
  | .arrow0 _, _, v, h, hv => by
    rw [denM, hv] at h; exact absurd h.1 (by simp [isProcV, procClosure?])
  | .arrowCons .., _, v, h, hv => by
    rw [denM, hv] at h; exact absurd h.1 (by simp [isProcV, procClosure?])
  | .clos .., _, v, h, hv => by
    rw [denM, hv] at h
    obtain ⟨cl, hcl, _⟩ := h
    exact absurd hcl (by simp [procClosure?])

/-- **`nonNilTy` keeps the non-`nil` values.** The mirror image, and the one whose catch-all is
the *identity* — so, unlike `falsyTy`, it needed no correction: refusing to refine is always
sound, and this is the direction where refusing is what the function already did. -/
theorem denM_nonNilTy : ∀ (τ : Ty) {m : Machine} {v : Value},
    denM τ m v → v ≠ .nil → denM (Ratchet.nonNilTy τ) m v
  | .nilT, _, v, h, hv => by
    rw [denM] at h
    exact absurd (by cases v <;> simp_all [isNilV] : v = Value.nil) hv
  | .any, _, _, h, _ => h
  | .nilable ρ, m, v, h, hv => by
    rw [Ratchet.nonNilTy]
    rw [denM] at h
    rcases h with hnil | hρ
    · exact absurd (by cases v <;> simp_all [isNilV] : v = Value.nil) hv
    · exact denM_nonNilTy ρ hρ hv
  | .union σ τ, m, v, h, hv => by
    rw [Ratchet.nonNilTy]
    rw [denM] at h
    rcases h with hσ | hτ
    · exact denM_joinT_left (denM_nonNilTy σ hσ hv)
    · exact denM_joinT_right (denM_nonNilTy τ hτ hv)
  | .int, _, _, h, _ => h
  | .bool, _, _, h, _ => h
  | .sym, _, _, h, _ => h
  | .float, _, _, h, _ => h
  | .never, _, _, h, _ => h
  | .cls _, _, _, h, _ => h
  | .clsOf _, _, _, h, _ => h
  | .arrayOf _, _, _, h, _ => h
  | .hashOf _ _, _, _, h, _ => h
  | .inst _ _, _, _, h, _ => h
  | .sameAs _ _, _, _, h, _ => h
  | .ivar0, _, _, h, _ => h
  | .ivarCons .., _, _, h, _ => h
  | .arrow0 _, _, _, h, _ => h
  | .arrowCons .., _, _, h, _ => h
  | .clos .., _, _, h, _ => h

#print axioms denM_isNilTy
#print axioms denM_nonNilTy

#print axioms denM_truthyTy
#print axioms denM_falsyTy

end Ratchet.Denote
