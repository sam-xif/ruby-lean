import Denote.Ty.Den

/-!
# `Denote/Ty/Join.lean` — the join, and what it means

`joinT` (`Ratchet/Lang/Ty.lean`) is the checker's **total** join: two branch types in, one type out,
`Ty.union` when nothing better is available. Six rules consume it — `if'`, `ifNoElse`,
`arrayLit`/`hashLit` (through `JudgeAll`/`JudgePairs`), `beginRescue` (through
`JudgeRescues`), `while'` — and every one of them needs the same one fact about it:

> **a join is an upper bound**: `denM σ m v → denM (joinT σ τ) m v`, and the same on the right.

That is this file. It is proved once here rather than per rung, because the two statements are
about the *type language* and not about any rule — and because the union arm is the only place
in the denotation where `Ty`'s own list plumbing (`unionMems`, `dedupTys`, `unionOf`) has to be
related to `denM`, which is three small inductions that no rung should have to redo.

## The `LawfulBEq Ty` instance, and why it has to be here

`Ratchet/Lang/Ty.lean` derives `BEq Ty` **without** `LawfulBEq`, and `joinT`/`joinTy` are written
with `==` guards (`σ == .never`, `σ == .nilT`, `σ == .nilable τ`). Reading those guards as
*equations* is exactly what a proof about the join needs, and it is not available: a derived
`BEq` is a `Bool` function with no theorem attached. `Ratchet/` may not be edited from this
side of the boundary (`AGENTS.md` §Isolation, and this ratchet's rule that the checker is the
thing being measured), so the instance is proved **here**, once, by structural induction over
the twenty constructors — after which `eq_of_beq`/`simpa` work on `Ty` everywhere downstream.

Worth stating what it is not: it is not a claim about the checker, it is the missing half of a
`deriving` clause. If `Ratchet/Lang/Ty.lean` ever adds `deriving LawfulBEq`, this section deletes.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore
open Ratchet

/-! ## `Ty`'s equality is lawful -/

theorem ty_eq_of_beq : ∀ {a b : Ty}, (a == b) = true → a = b := by
  intro a
  induction a with
  | int => intro b; cases b <;> intro h <;> first | rfl | exact Bool.noConfusion h
  | bool => intro b; cases b <;> intro h <;> first | rfl | exact Bool.noConfusion h
  | nilT => intro b; cases b <;> intro h <;> first | rfl | exact Bool.noConfusion h
  | sym => intro b; cases b <;> intro h <;> first | rfl | exact Bool.noConfusion h
  | any => intro b; cases b <;> intro h <;> first | rfl | exact Bool.noConfusion h
  | float => intro b; cases b <;> intro h <;> first | rfl | exact Bool.noConfusion h
  | never => intro b; cases b <;> intro h <;> first | rfl | exact Bool.noConfusion h
  | ivar0 => intro b; cases b <;> intro h <;> first | rfl | exact Bool.noConfusion h
  | cls n =>
    intro b; cases b <;> intro h
    case cls n' => have h2 : (n == n') = true := h; simp only [beq_iff_eq] at h2; rw [h2]
    all_goals exact Bool.noConfusion h
  | clsOf n =>
    intro b; cases b <;> intro h
    case clsOf n' => have h2 : (n == n') = true := h; simp only [beq_iff_eq] at h2; rw [h2]
    all_goals exact Bool.noConfusion h
  | nilable τ ih =>
    intro b; cases b <;> intro h
    case nilable τ' => rw [ih (show (τ == τ') = true from h)]
    all_goals exact Bool.noConfusion h
  | arrayOf τ ih =>
    intro b; cases b <;> intro h
    case arrayOf τ' => rw [ih (show (τ == τ') = true from h)]
    all_goals exact Bool.noConfusion h
  | arrow0 τ ih =>
    intro b; cases b <;> intro h
    case arrow0 τ' => rw [ih (show (τ == τ') = true from h)]
    all_goals exact Bool.noConfusion h
  | hashOf k v ihk ihv =>
    intro b; cases b <;> intro h
    case hashOf k' v' =>
      have h2 : (k == k' && v == v') = true := h
      obtain ⟨e1, e2⟩ := Bool.and_eq_true _ _ |>.mp h2
      rw [ihk e1, ihv e2]
    all_goals exact Bool.noConfusion h
  | union a b iha ihb =>
    intro c; cases c <;> intro h
    case union a' b' =>
      have h2 : (a == a' && b == b') = true := h
      obtain ⟨e1, e2⟩ := Bool.and_eq_true _ _ |>.mp h2
      rw [iha e1, ihb e2]
    all_goals exact Bool.noConfusion h
  | arrowCons p r ihp ihr =>
    intro b; cases b <;> intro h
    case arrowCons p' r' =>
      have h2 : (p == p' && r == r') = true := h
      obtain ⟨e1, e2⟩ := Bool.and_eq_true _ _ |>.mp h2
      rw [ihp e1, ihr e2]
    all_goals exact Bool.noConfusion h
  | inst n I ihI =>
    intro b; cases b <;> intro h
    case inst n' I' =>
      have h2 : (n == n' && I == I') = true := h
      obtain ⟨e1, e2⟩ := Bool.and_eq_true _ _ |>.mp h2
      simp only [beq_iff_eq] at e1
      rw [e1, ihI e2]
    all_goals exact Bool.noConfusion h
  | sameAs n τ ih =>
    intro b; cases b <;> intro h
    case sameAs n' τ' =>
      have h2 : (n == n' && τ == τ') = true := h
      obtain ⟨e1, e2⟩ := Bool.and_eq_true _ _ |>.mp h2
      simp only [beq_iff_eq] at e1
      rw [e1, ih e2]
    all_goals exact Bool.noConfusion h
  | ivarCons n τ rest ihτ ihrest =>
    intro b; cases b <;> intro h
    case ivarCons n' τ' rest' =>
      have h2 : (n == n' && (τ == τ' && rest == rest')) = true := h
      obtain ⟨e1, e23⟩ := Bool.and_eq_true _ _ |>.mp h2
      obtain ⟨e2, e3⟩ := Bool.and_eq_true _ _ |>.mp e23
      simp only [beq_iff_eq] at e1
      rw [e1, ihτ e2, ihrest e3]
    all_goals exact Bool.noConfusion h
  | clos i cap slf ihcap ihslf =>
    intro b; cases b <;> intro h
    case clos i' cap' slf' =>
      have h2 : (i == i' && (cap == cap' && slf == slf')) = true := h
      obtain ⟨e1, e23⟩ := Bool.and_eq_true _ _ |>.mp h2
      obtain ⟨e2, e3⟩ := Bool.and_eq_true _ _ |>.mp e23
      simp only [beq_iff_eq] at e1
      rw [e1, ihcap e2, ihslf e3]
    all_goals exact Bool.noConfusion h

theorem ty_beq_refl : ∀ (a : Ty), (a == a) = true := by
  intro a
  induction a with
  | int | bool | nilT | sym | any | float | never | ivar0 => rfl
  | cls n | clsOf n => exact (show (n == n) = true by simp)
  | nilable τ ih | arrayOf τ ih | arrow0 τ ih => exact (show (τ == τ) = true from ih)
  | hashOf a b iha ihb | union a b iha ihb | arrowCons a b iha ihb =>
    exact (show (a == a && b == b) = true by simp [iha, ihb])
  | inst n I ihI => exact (show (n == n && I == I) = true by simp [ihI])
  | sameAs n τ ih => exact (show (n == n && τ == τ) = true by simp [ih])
  | ivarCons n τ rest ihτ ihr =>
    exact (show (n == n && (τ == τ && rest == rest)) = true by simp [ihτ, ihr])
  | clos i cap slf ihc ihs =>
    exact (show (i == i && (cap == cap && slf == slf)) = true by simp [ihc, ihs])

instance : LawfulBEq Ty where
  eq_of_beq := ty_eq_of_beq
  rfl := ty_beq_refl _


/-! ## The union plumbing

Three inductions relating `Ty`'s member-list functions to `denM`. Each is used exactly once,
by the union arm of the two join lemmas below. -/

/-- A value in one member of a list is in the union the list rebuilds. -/
theorem denM_unionOf_mem : ∀ (l : List Ty) {μ : Ty} {m : Machine} {v : Value},
    μ ∈ l → denM μ m v → denM (unionOf l) m v
  | [], _, _, _, hmem, _ => absurd hmem (by simp)
  | [ρ], μ, m, v, hmem, h => by
    rcases List.mem_singleton.mp hmem with rfl
    rw [unionOf]
    exact h
  | τ :: τ' :: rest, μ, m, v, hmem, h => by
    rw [show unionOf (τ :: τ' :: rest) = .union τ (unionOf (τ' :: rest)) from rfl, denM]
    rcases List.mem_cons.mp hmem with rfl | htl
    · exact Or.inl h
    · exact Or.inr (denM_unionOf_mem (τ' :: rest) htl h)

/-- Conversely: a value in a type is in one of that type's union members. `unionMems` of a
non-union is the singleton, so the base cases are `rfl`-shaped. -/
theorem denM_unionMems : ∀ (σ : Ty) {m : Machine} {v : Value},
    denM σ m v → ∃ μ ∈ unionMems σ, denM μ m v
  | .union σ τ, m, v, h => by
    rw [denM] at h
    rcases h with hσ | hτ
    · obtain ⟨μ, hmem, hd⟩ := denM_unionMems σ hσ
      exact ⟨μ, by simp only [unionMems]; exact List.mem_append_left _ hmem, hd⟩
    · obtain ⟨μ, hmem, hd⟩ := denM_unionMems τ hτ
      exact ⟨μ, by simp only [unionMems]; exact List.mem_append_right _ hmem, hd⟩
  | .int, _, _, h | .bool, _, _, h | .nilT, _, _, h | .sym, _, _, h | .float, _, _, h
  | .any, _, _, h | .never, _, _, h | .cls _, _, _, h | .clsOf _, _, _, h
  | .nilable _, _, _, h | .arrayOf _, _, _, h | .hashOf _ _, _, _, h | .arrow0 _, _, _, h
  | .arrowCons _ _, _, _, h | .inst _ _, _, _, h | .ivar0, _, _, h | .ivarCons _ _ _, _, _, h
  | .clos _ _ _, _, _, h | .sameAs _ _, _, _, h => ⟨_, by simp [unionMems], h⟩

/-- Duplicate removal keeps every member. Stated over the accumulator so the induction is
structural: what is dropped is a type the accumulator already holds, and the accumulator is
what the result is built from. -/
theorem mem_dedupTysAux : ∀ (l : List Ty) (seen : List Ty) {μ : Ty},
    (μ ∈ seen ∨ μ ∈ l) → μ ∈ dedupTysAux seen l
  | [], seen, μ, h => by
    rcases h with h | h
    · simpa [dedupTysAux] using h
    · exact absurd h (by simp)
  | τ :: τs, seen, μ, h => by
    rw [dedupTysAux]
    by_cases hc : seen.contains τ
    · rw [if_pos hc]
      refine mem_dedupTysAux τs seen ?_
      rcases h with h | h
      · exact Or.inl h
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inl (by simpa using hc)
        · exact Or.inr h
    · rw [if_neg hc]
      refine mem_dedupTysAux τs (τ :: seen) ?_
      rcases h with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inl List.mem_cons_self
        · exact Or.inr h

theorem mem_dedupTys {l : List Ty} {μ : Ty} (h : μ ∈ l) : μ ∈ dedupTys l :=
  mem_dedupTysAux l [] (Or.inr h)

/-- The union arm of both join lemmas: a value in either side is in the normalized union of
both sides' members. -/
theorem denM_unionOf_join {σ τ ρ : Ty} {m : Machine} {v : Value} (h : denM ρ m v)
    (hmem : ∀ μ, μ ∈ unionMems ρ → μ ∈ unionMems σ ++ unionMems τ) :
    denM (unionOf (dedupTys (unionMems σ ++ unionMems τ))) m v := by
  obtain ⟨μ, hμ, hd⟩ := denM_unionMems ρ h
  exact denM_unionOf_mem _ (mem_dedupTys (hmem μ hμ)) hd


/-! ## A join is an upper bound

Two steps, because `joinT` has two layers: the `never` guards and the delegation to `joinTy`.
The inner lemmas are where `LawfulBEq Ty` is spent — every one of `joinTy`'s five guards is a
`==` whose *equation* is what makes the branch's answer denote what the hypothesis says.

Both directions are separate proofs rather than one plus symmetry, because `joinT` is **not**
symmetric as a function: it tries `σ == .never` before `τ == .never`, and `joinTy` tries
`σ == .nilT` before `τ == .nilT`. The two answers agree up to *denotation*, which is exactly
what this pair of theorems says, and not up to `Ty` equality. -/

/-- `joinTy`'s structural cases: equal types, one side `nil`, one side the other's `nilable`.
Four of the five branches are the hypothesis unchanged; the two `nil` ones move the value into
a `nilable`'s left or right disjunct. -/
theorem denM_joinTy_left {σ τ ρ : Ty} {m : Machine} {v : Value} (hj : joinTy σ τ = some ρ)
    (h : denM σ m v) : denM ρ m v := by
  unfold joinTy mkNilable at hj
  repeat' split at hj
  all_goals try (cases hj)
  all_goals first | exact h | simp_all [denM]

theorem denM_joinTy_right {σ τ ρ : Ty} {m : Machine} {v : Value} (hj : joinTy σ τ = some ρ)
    (h : denM τ m v) : denM ρ m v := by
  unfold joinTy mkNilable at hj
  repeat' split at hj
  all_goals try (cases hj)
  all_goals first | exact h | simp_all [denM]

/-- **A value of the left branch's type is a value of the join.** The `σ == .never` case is
where the asymmetry is harmless: `denM .never` is `False`, so the branch is vacuous rather than
in need of an argument. -/
theorem denM_joinT_left {σ τ : Ty} {m : Machine} {v : Value} (h : denM σ m v) :
    denM (joinT σ τ) m v := by
  unfold joinT
  split
  · rename_i hb; rw [eq_of_beq hb] at h; exact absurd h (by simp [denM])
  · split
    · exact h
    · split
      · rename_i heq; exact denM_joinTy_left heq h
      · exact denM_unionOf_join h (fun μ hμ => List.mem_append_left _ hμ)

/-- … and of the right branch's. -/
theorem denM_joinT_right {σ τ : Ty} {m : Machine} {v : Value} (h : denM τ m v) :
    denM (joinT σ τ) m v := by
  unfold joinT
  split
  · exact h
  · split
    · rename_i hb; rw [eq_of_beq hb] at h; exact absurd h (by simp [denM])
    · split
      · rename_i heq; exact denM_joinTy_right heq h
      · exact denM_unionOf_join h (fun μ hμ => List.mem_append_right _ hμ)

#print axioms denM_joinT_left
#print axioms denM_joinT_right

end Ratchet.Denote
