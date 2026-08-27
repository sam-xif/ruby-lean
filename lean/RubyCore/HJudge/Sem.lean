/-
  RubyCore.HJudge.Sem — the H-layer's semantic judgment, and the bridge from
  the first-order layer's value judgment into the denotation.

  `HSemJudge` is `SemJudge` (J30) with one substitution: the first-order value
  judgment `VTy mf.heap v τ` becomes the semantic denotation
  `τh.den mf.heap v`. Everything else — the `Conformant` start-state set, the
  reachability-grounded safety half — is CONSUMED from the existing layer,
  not re-authored: same formula, one rung up.

  The bridge (`vty_hden`): below `HTy.ofTy?`'s domain, a `VTy` fact IS a
  denotation fact. Its content is a pair of `VTy` inversions at the two
  non-ground arms (`nilable`/`union`) — proved here by induction on the
  `SubJ` derivation, because `VTy.toValueTy` only crosses at ground types —
  plus the per-atom shape inversions, plus `HTy.lean`'s heap-generic
  denotation intros.

  House rules: no sorry, no new axioms.
-/
import RubyCore.HJudge.HTy
import RubyCore.Proof.Judgment.Sem

set_option autoImplicit false

namespace RubyCore.HJudge

open RubyCore
open RubyCore.Types
open RubyCore.Judgment
open RubyCore.Proof
open RubyCore.Proof.Static
open RubyCore.Proof.Judgment
open Interp

/-! ## The semantic judgment -/

/-- **`HSemJudge A D Γ e c τh`** — the H-layer semantic typing judgment: in
    every conformant state, `e` runs type-safely, and a terminating run's
    value **inhabits the denotation `τh.den` at the final heap**. `Judge`,
    `MFrag`, `VTy` do not appear; neither does the Iris seat — a WP is one
    way of *manufacturing* an `HSemJudge` (see `Judge.lean`), not part of its
    meaning. -/
def HSemJudge (A : SemAxioms) (D : Decls) (Γ : Env) (e : Expr) (c : JCtx)
    (τh : HTy) : Prop :=
  ∀ m : Machine, Conformant A D c Γ m → m.ctl = .eval e →
    (∀ r, ReachableResult m r → ¬ typeStuck r) ∧
    (∀ v mf, ReachableResult m (.done v mf) → τh.den mf.heap v)

/-! ## `VTy` inversions at the non-ground arms

`VTy h v τ = ∃ σ, ValueTy h v σ ∧ SubJ σ τ`, and `ValueTy` never inhabits a
union — so the union/nilable structure of `τ` can only have entered through
the `SubJ` derivation, and induction on that derivation reads it back out. -/

private theorem vty_nilable_inv {h : Heap} {v : Value} :
    ∀ {σ ρ : Ty}, SubJ σ ρ → ValueTy h v σ → ∀ {τ : Ty}, ρ = .nilable τ →
      v = .nil ∨ VTy h v τ := by
  intro σ ρ hs
  induction hs with
  | base hb =>
    intro hσ τ hρ
    subst hρ
    simp only [subTy, Bool.or_eq_true, beq_iff_eq] at hb
    rcases hb with (rfl | rfl) | hd
    · exact Or.inl (vty_nilT_eq (VTy.ofValueTy hσ))
    · rcases valueTy_nilable_cases hσ with h1 | h1
      · exact Or.inl (vty_nilT_eq (VTy.ofValueTy h1))
      · exact Or.inr (VTy.ofValueTy h1)
    · exact Or.inr ⟨_, hσ, .base hd⟩
  | unionL h1 h2 ih1 ih2 =>
    intro hσ τ hρ
    exact absurd hσ valueTy_union_false
  | unionR1 h1 ih =>
    intro hσ τ hρ
    exact absurd hρ (by simp)
  | unionR2 h1 ih =>
    intro hσ τ hρ
    exact absurd hρ (by simp)
  | nilableL hn hs' ihn ihs =>
    intro hσ τ hρ
    rcases valueTy_nilable_cases hσ with h1 | h1
    · exact ihn h1 hρ
    · exact ihs h1 hρ
  | nilableR hs' ih =>
    intro hσ τ hρ
    injection hρ with hρ'
    subst hρ'
    exact Or.inr ⟨_, hσ, hs'⟩
  | arrow0 h1 ih =>
    intro hσ τ hρ
    exact absurd hρ (by simp)
  | arrowCons h1 h2 ih1 ih2 =>
    intro hσ τ hρ
    exact absurd hρ (by simp)

/-- `VTy` at a `nilable`: nil, or the payload. -/
theorem vty_nilable_cases' {h : Heap} {v : Value} {τ : Ty}
    (hv : VTy h v (.nilable τ)) : v = .nil ∨ VTy h v τ :=
  let ⟨_, hσ, hs⟩ := hv
  vty_nilable_inv hs hσ rfl

private theorem vty_union_inv {h : Heap} {v : Value} :
    ∀ {σ ρ : Ty}, SubJ σ ρ → ValueTy h v σ → ∀ {a b : Ty}, ρ = .union a b →
      VTy h v a ∨ VTy h v b := by
  intro σ ρ hs
  induction hs with
  | base hb =>
    intro hσ a b hρ
    subst hρ
    simp only [subTy, beq_iff_eq] at hb
    subst hb
    exact absurd hσ valueTy_union_false
  | unionL h1 h2 ih1 ih2 =>
    intro hσ a b hρ
    exact absurd hσ valueTy_union_false
  | unionR1 h1 ih =>
    intro hσ a b hρ
    injection hρ with h1' h2'
    subst h1'; subst h2'
    exact Or.inl ⟨_, hσ, h1⟩
  | unionR2 h1 ih =>
    intro hσ a b hρ
    injection hρ with h1' h2'
    subst h1'; subst h2'
    exact Or.inr ⟨_, hσ, h1⟩
  | nilableL hn hs' ihn ihs =>
    intro hσ a b hρ
    rcases valueTy_nilable_cases hσ with h1 | h1
    · exact ihn h1 hρ
    · exact ihs h1 hρ
  | nilableR hs' ih =>
    intro hσ a b hρ
    exact absurd hρ (by simp)
  | arrow0 h1 ih =>
    intro hσ a b hρ
    exact absurd hρ (by simp)
  | arrowCons h1 h2 ih1 ih2 =>
    intro hσ a b hρ
    exact absurd hρ (by simp)

/-- `VTy` at a `union`: one side or the other. -/
theorem vty_union_cases {h : Heap} {v : Value} {a b : Ty}
    (hv : VTy h v (.union a b)) : VTy h v a ∨ VTy h v b :=
  let ⟨_, hσ, hs⟩ := hv
  vty_union_inv hs hσ rfl

/-! ## Per-atom shape inversions (`valueTy_int`'s proof shape, at the other
    ground atoms the bridge serves) -/

private theorem vty_shape_sym {h : Heap} {v : Value} (hv : VTy h v .sym) :
    ∃ s, v = .sym s := by
  have h' := hv.toValueTy (by simp [groundTy])
  cases v with
  | ref o =>
    exfalso
    rcases valueTy_ref_inv (by simp [subTy]) (by simp [subTy]) h' with
      ⟨-, hne⟩ | ⟨-, hne⟩ <;> exact absurd hne (by simp [subTy])
  | _ => simp_all [ValueTy, valueTy?, subTy]

private theorem vty_shape_bool {h : Heap} {v : Value} (hv : VTy h v .bool) :
    ∃ b, v = .bool b := by
  have h' := hv.toValueTy (by simp [groundTy])
  cases v with
  | ref o =>
    exfalso
    rcases valueTy_ref_inv (by simp [subTy]) (by simp [subTy]) h' with
      ⟨-, hne⟩ | ⟨-, hne⟩ <;> exact absurd hne (by simp [subTy])
  | _ => simp_all [ValueTy, valueTy?, subTy]

private theorem vty_shape_flt {h : Heap} {v : Value} (hv : VTy h v .float) :
    ∃ x, v = .flt x := by
  have h' := hv.toValueTy (by simp [groundTy])
  cases v with
  | ref o =>
    exfalso
    rcases valueTy_ref_inv (by simp [subTy]) (by simp [subTy]) h' with
      ⟨-, hne⟩ | ⟨-, hne⟩ <;> exact absurd hne (by simp [subTy])
  | _ => simp_all [ValueTy, valueTy?, subTy]

/-! ## The bridge -/

/-- **`VTy → den`, below the bridge's domain**: whenever `HTy.ofTy?` answers,
    the first-order value judgment implies the denotation — at the SAME heap,
    which is what lets `judge_semJudge`'s conclusion feed the H-layer at the
    final heap of a run. -/
theorem vty_hden {h : Heap} {v : Value} : ∀ {τ : Ty} {τh : HTy},
    VTy h v τ → HTy.ofTy? τ = some τh → τh.den h v
  | .int, _, hv, ht => by
    simp only [HTy.ofTy?, Option.some.injEq] at ht
    subst ht
    obtain ⟨n, rfl⟩ := valueTy_int (hv.toValueTy (by simp [groundTy]))
    exact HTy.den_int h n
  | .bool, _, hv, ht => by
    simp only [HTy.ofTy?, Option.some.injEq] at ht
    subst ht
    obtain ⟨b, rfl⟩ := vty_shape_bool hv
    exact HTy.den_bool h b
  | .nilT, _, hv, ht => by
    simp only [HTy.ofTy?, Option.some.injEq] at ht
    subst ht
    rw [vty_nilT_eq hv]
    exact HTy.den_nil h
  | .sym, _, hv, ht => by
    simp only [HTy.ofTy?, Option.some.injEq] at ht
    subst ht
    obtain ⟨s, rfl⟩ := vty_shape_sym hv
    exact HTy.den_sym h s
  | .float, _, hv, ht => by
    simp only [HTy.ofTy?, Option.some.injEq] at ht
    subst ht
    obtain ⟨x, rfl⟩ := vty_shape_flt hv
    exact HTy.den_flt h x
  | .any, _, _, ht => by
    simp only [HTy.ofTy?, Option.some.injEq] at ht
    subst ht
    exact HTy.den_untyped _
  | .nilable τ, _, hv, ht => by
    rw [HTy.ofTy?] at ht
    obtain ⟨τh', hτ', rfl⟩ := Option.map_eq_some_iff.mp ht
    rcases vty_nilable_cases' hv with rfl | hv'
    · exact HTy.den_nilable_nil τh'
    · exact HTy.den_nilable_of (vty_hden hv' hτ')
  | .union σ τ, τh, hv, ht => by
    rw [HTy.ofTy?] at ht
    cases hσ? : HTy.ofTy? σ with
    | none => rw [hσ?] at ht; simp at ht
    | some a =>
      cases hτ? : HTy.ofTy? τ with
      | none => rw [hσ?, hτ?] at ht; simp at ht
      | some b =>
        rw [hσ?, hτ?] at ht
        simp only [Option.some.injEq] at ht
        subst ht
        rcases vty_union_cases hv with hva | hvb
        · exact Or.inl (vty_hden hva hσ?)
        · exact Or.inr (vty_hden hvb hτ?)

/-! ## The lift from the first-order semantic judgment -/

/-- A `SemJudge` fact — however obtained: `judge_semJudge`, a J31 semantic
    axiom, a direct proof — yields the `HSemJudge` at the bridged type. -/
theorem semJudge_toH {A : SemAxioms} {D : Decls} {Γ : Env} {e : Expr}
    {c : JCtx} {τ : Ty} {τh : HTy}
    (hs : SemJudge A D Γ e c τ) (ht : HTy.ofTy? τ = some τh) :
    HSemJudge A D Γ e c τh := by
  intro m hconf hctl
  obtain ⟨hsafe, hres⟩ := hs m hconf hctl
  exact ⟨hsafe, fun v mf hr => vty_hden (hres v mf hr) ht⟩

end RubyCore.HJudge
