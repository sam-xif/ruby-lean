import RubyCore.Types.Core

/-!
# F1b.8 — `infer` is monotone in the declaration table, on `def`-free expressions

The one lemma a *growing* declaration table needs, and the reason it is one
lemma rather than a slack in the invariant.

## What it is for

`UserConforms` — the user-method arm of `EntryOk` — carries the checker's own
verdict on a method body: `infer D [] md.body = some (d.ret, Γ', D)`. That fact
enters the invariant when the `def` step installs the method, and it has to
survive every *later* step, including the program's own later `def`s, which grow
the table. So preservation owes exactly

    infer F  [] body = some (τ, Γ', F)  →  SubDecls F F'  →
    infer F' [] body = some (τ, Γ', F')

and without it the invariant needs a second table with a `SubDecls` slack
threaded through `Inv`, `CtlOk` and `KontOk`. That shape was tried first (L160)
and it does not close: the `def` case needs `declaresName` freshness at the
*invariant's* table while the rule checks the *control's*, and the slack gives
the implication the wrong way round. One lemma here removes the need for all of
it, and leaves `Inv` with a single table.

## Why the hypothesis is syntactic

`infer` is genuinely non-monotone, at exactly one rule: `def`'s guard is
`declaresName D name = false`, and a bigger table falsifies it. Every other rule
touches the table only through `sigOf`, which `SubDecls` was defined to carry
(`Types/Decls.lean` — stated over `declFor` rather than over the row lists,
because the structural reading is false for a two-class ground type). So the
side condition is `defFree`, and it is a real narrowing of the fragment: a
declared method's body may not itself define a method or reopen a class.

## The second conclusion, and why it is in the same induction

`defFree e` also implies the *output* table is the input one, and the two facts
have to be proved together: the monotone conclusion for a subexpression is only
usable once that subexpression's output table is known to be unchanged, and the
stability conclusion for a compound needs the monotone one nowhere. Splitting
them means running the same 42-case induction twice.
-/

namespace RubyCore
namespace Proof
namespace Static

open RubyCore.Types

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

/-- **Table stability from the *context* rather than from the expression** (L200).

    `infer_mono_all` below already proves `D₀ = D`, but only under `defFree e` — and
    `defFree` is not available where it is needed: `KontOk`'s constructors carry the
    `infer`/`inferSeq`/`inferArgs` equations *without* it, so an induction walking a
    continuation chain (`KontOk.retOk`) cannot use that half.

    `ctx.ret.isSome` is available there, because that is exactly the hypothesis a
    `return` rule fires under. And it suffices: at `top = false` the **only** arm that
    grows the table is `def`'s row, `class'` needing `top = true` — so L200's
    `ctx.ret.isNone` guard on that row makes the table constant along every chain
    inside a body that declares a return type.

    Same induction shape as `infer_mono_all` and a much weaker conclusion, so the
    uniform block carries it. -/
theorem infer_table_ret : ∀ (D : Decls) (Γ : Env) (e : Expr) (top : Bool) (ctx : FrameCtx),
    ctx.ret.isSome = true → top = false → ∀ τ Γ' D₀,
      infer D Γ e top ctx = some (τ, Γ', D₀) → D₀ = D := by
  intro D Γ e top ctx
  induction D, Γ, e, top, ctx using infer.induct with
  | motive2 Da Γa ta elsa topa ctxa =>
    exact ctxa.ret.isSome = true → topa = false → ∀ τ Γ' D₀,
      inferIf Da Γa ta elsa topa ctxa = some (τ, Γ', D₀) → D₀ = Da
  | motive3 Da Γa esa topa ctxa =>
    exact ctxa.ret.isSome = true → topa = false → ∀ τ Γ' D₀,
      inferSeq Da Γa esa topa ctxa = some (τ, Γ', D₀) → D₀ = Da
  | motive4 Da Γa esa topa ctxa =>
    exact ctxa.ret.isSome = true → topa = false → ∀ τs Γ' D₀,
      inferArgs Da Γa esa topa ctxa = some (τs, Γ', D₀) → D₀ = Da
  -- **The `if`-with-else arm**, explicit because the answer's table is the *then*
  -- branch's and the join's guard has to be split before either IH is usable.
  | case99 D Γ t top ctx e' τt Γt Dt τe Γe De hE hT hagree ih2 ih1 =>
    intro hret htop τ Γ' D₀ h
    obtain ⟨hΓ, hD⟩ := hagree
    simp only [inferIf, hT, hE] at h
    rw [if_pos (by exact ⟨hΓ, hD⟩)] at h
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨τj, -, -, -, rfl⟩ := h
    exact ih2 hret htop _ _ _ hT
  | _ =>
    intro hret htop τ Γ' D₀ h
    first
      | (exfalso; revert h; simp +contextual [infer, inferIf, inferSeq, inferArgs, htop]; done)
      | (simp_all only [infer, inferIf, inferSeq, inferArgs, Option.some.injEq,
           Prod.mk.injEq, reduceCtorEq]; done)
      | (simp_all [infer, inferIf, inferSeq, inferArgs, htop, hret]; done)
      | (rename_i ih1
         exact ih1 hret htop _ _ _ (by simpa [infer, inferIf, inferSeq, inferArgs] using h))
      | (rename_i ih2 ih1
         first
           | exact ih1 hret htop _ _ _ (by simpa [infer, inferSeq, inferArgs] using h)
           | exact ih2 hret htop _ _ _ (by simpa [infer, inferSeq, inferArgs] using h))
      -- a local read: the arm answers the input table outright, so unfolding the
      -- `Option.map` is the whole case.
      | (revert h; simp +contextual [infer]; done)
      | (revert h; simp +contextual [inferIf]; done)
      -- the `def` arm's **no-row** branch (L200's guard is one of the six conjuncts
      -- that can fail): the arm answers the input table, and `params.isEmpty` and the
      -- body's own stability check are already in context, so what is left is to
      -- compute the `if`s away rather than to reason.
      -- the `def` arm's **no-row** branch, where L200's guard is one of the six
      -- conjuncts that can fail: the arm answers the input table, so the case is three
      -- `if`s computed away rather than anything about types.
      | (simp only [infer] at h
         split at h <;> split at h <;> split at h <;> simp_all)
      | (simp only [infer] at h
         split at h <;> split at h <;> simp_all)

/-- The three siblings, and they are **list inductions rather than a second
    `infer.induct`**: `inferSeq`/`inferArgs` are `infer` threaded along a list and
    `inferIf` is two `infer`s plus a join, so each one composes the theorem above with
    itself. That is the whole reason to have proved the `infer` case separately. -/
theorem inferIf_table_ret {D : Decls} {Γ : Env} {t : Expr} {els : Option Expr} {top : Bool}
    {ctx : FrameCtx} {τ : Ty} {Γ' : Env} {D₀ : Decls} (hret : ctx.ret.isSome = true)
    (htop : top = false) (h : inferIf D Γ t els top ctx = some (τ, Γ', D₀)) : D₀ = D := by
  unfold inferIf at h
  cases els with
  | none =>
    cases ht : infer D Γ t top ctx with
    | none => rw [ht] at h; simp at h
    | some r =>
      obtain ⟨τt, Γt, Dt⟩ := r
      rw [ht] at h
      dsimp only at h
      split at h
      · rename_i hq
        simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
        obtain ⟨τj, -, -, -, rfl⟩ := h
        rfl
      · simp at h
  | some e =>
    cases ht : infer D Γ t top ctx with
    | none => rw [ht] at h; simp at h
    | some r =>
      obtain ⟨τt, Γt, Dt⟩ := r
      rw [ht] at h
      dsimp only at h
      cases he : infer D Γ e top ctx with
      | none => rw [he] at h; simp at h
      | some r' =>
        obtain ⟨τe, Γe, De⟩ := r'
        rw [he] at h
        dsimp only at h
        split at h
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
          obtain ⟨τj, -, -, -, rfl⟩ := h
          exact infer_table_ret D Γ t top ctx hret htop _ _ _ ht
        · simp at h

theorem inferSeq_table_ret : ∀ {es : List Expr} {D : Decls} {Γ : Env} {top : Bool}
    {ctx : FrameCtx} {τ : Ty} {Γ' : Env} {D₀ : Decls}, ctx.ret.isSome = true → top = false →
    inferSeq D Γ es top ctx = some (τ, Γ', D₀) → D₀ = D
  | [], D, Γ, top, ctx, τ, Γ', D₀, _, _, h => by
      simp only [inferSeq, Option.some.injEq, Prod.mk.injEq] at h
      exact h.2.2.symm
  | [e], D, Γ, top, ctx, τ, Γ', D₀, hret, htop, h => by
      simp only [inferSeq] at h; exact infer_table_ret D Γ e top ctx hret htop _ _ _ h
  | e :: e₂ :: rest, D, Γ, top, ctx, τ, Γ', D₀, hret, htop, h => by
      simp only [inferSeq] at h
      cases he : infer D Γ e top ctx with
      | none => rw [he] at h; simp at h
      | some r =>
        obtain ⟨τe, Γ₁, D₁⟩ := r
        rw [he] at h
        have hD : D₁ = D := infer_table_ret D Γ e top ctx hret htop _ _ _ he
        subst hD
        exact inferSeq_table_ret hret htop h

theorem inferArgs_table_ret : ∀ {es : List Expr} {D : Decls} {Γ : Env} {top : Bool}
    {ctx : FrameCtx} {τs : List Ty} {Γ' : Env} {D₀ : Decls}, ctx.ret.isSome = true →
    top = false → inferArgs D Γ es top ctx = some (τs, Γ', D₀) → D₀ = D
  | [], D, Γ, top, ctx, τs, Γ', D₀, _, _, h => by
      simp only [inferArgs, Option.some.injEq, Prod.mk.injEq] at h
      exact h.2.2.symm
  | e :: rest, Dq, Γ, top, ctx, τs, Γ', D₀, hret, htop, h => by
      simp only [inferArgs] at h
      cases he : infer Dq Γ e top ctx with
      | none => rw [he] at h; simp at h
      | some r =>
        obtain ⟨τe, Γ₁, D₁⟩ := r
        rw [he] at h
        have hD : D₁ = Dq := infer_table_ret Dq Γ e top ctx hret htop _ _ _ he
        subst hD
        dsimp only at h
        cases hr : inferArgs D₁ Γ₁ rest top ctx with
        | none => rw [hr] at h; simp at h
        | some r' =>
          obtain ⟨τr, Γ₂, D₂⟩ := r'
          rw [hr] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, -, rfl⟩ := h
          exact inferArgs_table_ret hret htop hr

/-! ### L226: the same theorem at the *loop* channel, and the same proof

`infer_table_ret` (L200) says *the table is constant along a continuation chain inside a body
that declares a return type*, and it is available because `def`'s row branch requires
`ctx.ret.isNone`. L226 gave that branch a second such guard — `ctx.inLoop.isNone` — so the
identical statement holds at the loop channel, which is what a `next` rule needs in order to
walk a `KontOk` chain down to its loop kont without the table moving under it.

**The two blocked rungs share this lemma.** `begin` (L218) and `next` (L225) were each stuck
on *"the relation is indexed by `Decls` and `KontOk` threads tables"*; this is the answer for
both. The proof below is `infer_table_ret`'s **unchanged** — the guard is the only thing that
differs, which is itself the evidence that the two channels are the same shape.
-/

theorem infer_table_loop : ∀ (D : Decls) (Γ : Env) (e : Expr) (top : Bool) (ctx : FrameCtx),
    ctx.inLoop.isSome = true → top = false → ∀ τ Γ' D₀,
      infer D Γ e top ctx = some (τ, Γ', D₀) → D₀ = D := by
  intro D Γ e top ctx
  induction D, Γ, e, top, ctx using infer.induct with
  | motive2 Da Γa ta elsa topa ctxa =>
    exact ctxa.inLoop.isSome = true → topa = false → ∀ τ Γ' D₀,
      inferIf Da Γa ta elsa topa ctxa = some (τ, Γ', D₀) → D₀ = Da
  | motive3 Da Γa esa topa ctxa =>
    exact ctxa.inLoop.isSome = true → topa = false → ∀ τ Γ' D₀,
      inferSeq Da Γa esa topa ctxa = some (τ, Γ', D₀) → D₀ = Da
  | motive4 Da Γa esa topa ctxa =>
    exact ctxa.inLoop.isSome = true → topa = false → ∀ τs Γ' D₀,
      inferArgs Da Γa esa topa ctxa = some (τs, Γ', D₀) → D₀ = Da
  -- **The `if`-with-else arm**, explicit because the answer's table is the *then*
  -- branch's and the join's guard has to be split before either IH is usable.
  | case99 D Γ t top ctx e' τt Γt Dt τe Γe De hE hT hagree ih2 ih1 =>
    intro hret htop τ Γ' D₀ h
    obtain ⟨hΓ, hD⟩ := hagree
    simp only [inferIf, hT, hE] at h
    rw [if_pos (by exact ⟨hΓ, hD⟩)] at h
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨τj, -, -, -, rfl⟩ := h
    exact ih2 hret htop _ _ _ hT
  | _ =>
    intro hret htop τ Γ' D₀ h
    first
      | (exfalso; revert h; simp +contextual [infer, inferIf, inferSeq, inferArgs, htop]; done)
      | (simp_all only [infer, inferIf, inferSeq, inferArgs, Option.some.injEq,
           Prod.mk.injEq, reduceCtorEq]; done)
      | (simp_all [infer, inferIf, inferSeq, inferArgs, htop, hret]; done)
      | (rename_i ih1
         exact ih1 hret htop _ _ _ (by simpa [infer, inferIf, inferSeq, inferArgs] using h))
      | (rename_i ih2 ih1
         first
           | exact ih1 hret htop _ _ _ (by simpa [infer, inferSeq, inferArgs] using h)
           | exact ih2 hret htop _ _ _ (by simpa [infer, inferSeq, inferArgs] using h))
      -- a local read: the arm answers the input table outright, so unfolding the
      -- `Option.map` is the whole case.
      | (revert h; simp +contextual [infer]; done)
      | (revert h; simp +contextual [inferIf]; done)
      -- the `def` arm's **no-row** branch (L200's guard is one of the six conjuncts
      -- that can fail): the arm answers the input table, and `params.isEmpty` and the
      -- body's own stability check are already in context, so what is left is to
      -- compute the `if`s away rather than to reason.
      -- the `def` arm's **no-row** branch, where L200's guard is one of the six
      -- conjuncts that can fail: the arm answers the input table, so the case is three
      -- `if`s computed away rather than anything about types.
      | (simp only [infer] at h
         split at h <;> split at h <;> split at h <;> simp_all)
      | (simp only [infer] at h
         split at h <;> split at h <;> simp_all)

/-- The three siblings, and they are **list inductions rather than a second
    `infer.induct`**: `inferSeq`/`inferArgs` are `infer` threaded along a list and
    `inferIf` is two `infer`s plus a join, so each one composes the theorem above with
    itself. That is the whole reason to have proved the `infer` case separately. -/
theorem inferIf_table_loop {D : Decls} {Γ : Env} {t : Expr} {els : Option Expr} {top : Bool}
    {ctx : FrameCtx} {τ : Ty} {Γ' : Env} {D₀ : Decls} (hret : ctx.inLoop.isSome = true)
    (htop : top = false) (h : inferIf D Γ t els top ctx = some (τ, Γ', D₀)) : D₀ = D := by
  unfold inferIf at h
  cases els with
  | none =>
    cases ht : infer D Γ t top ctx with
    | none => rw [ht] at h; simp at h
    | some r =>
      obtain ⟨τt, Γt, Dt⟩ := r
      rw [ht] at h
      dsimp only at h
      split at h
      · rename_i hq
        simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
        obtain ⟨τj, -, -, -, rfl⟩ := h
        rfl
      · simp at h
  | some e =>
    cases ht : infer D Γ t top ctx with
    | none => rw [ht] at h; simp at h
    | some r =>
      obtain ⟨τt, Γt, Dt⟩ := r
      rw [ht] at h
      dsimp only at h
      cases he : infer D Γ e top ctx with
      | none => rw [he] at h; simp at h
      | some r' =>
        obtain ⟨τe, Γe, De⟩ := r'
        rw [he] at h
        dsimp only at h
        split at h
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
          obtain ⟨τj, -, -, -, rfl⟩ := h
          exact infer_table_loop D Γ t top ctx hret htop _ _ _ ht
        · simp at h

theorem inferSeq_table_loop : ∀ {es : List Expr} {D : Decls} {Γ : Env} {top : Bool}
    {ctx : FrameCtx} {τ : Ty} {Γ' : Env} {D₀ : Decls}, ctx.inLoop.isSome = true → top = false →
    inferSeq D Γ es top ctx = some (τ, Γ', D₀) → D₀ = D
  | [], D, Γ, top, ctx, τ, Γ', D₀, _, _, h => by
      simp only [inferSeq, Option.some.injEq, Prod.mk.injEq] at h
      exact h.2.2.symm
  | [e], D, Γ, top, ctx, τ, Γ', D₀, hret, htop, h => by
      simp only [inferSeq] at h; exact infer_table_loop D Γ e top ctx hret htop _ _ _ h
  | e :: e₂ :: rest, D, Γ, top, ctx, τ, Γ', D₀, hret, htop, h => by
      simp only [inferSeq] at h
      cases he : infer D Γ e top ctx with
      | none => rw [he] at h; simp at h
      | some r =>
        obtain ⟨τe, Γ₁, D₁⟩ := r
        rw [he] at h
        have hD : D₁ = D := infer_table_loop D Γ e top ctx hret htop _ _ _ he
        subst hD
        exact inferSeq_table_loop hret htop h

theorem inferArgs_table_loop : ∀ {es : List Expr} {D : Decls} {Γ : Env} {top : Bool}
    {ctx : FrameCtx} {τs : List Ty} {Γ' : Env} {D₀ : Decls}, ctx.inLoop.isSome = true →
    top = false → inferArgs D Γ es top ctx = some (τs, Γ', D₀) → D₀ = D
  | [], D, Γ, top, ctx, τs, Γ', D₀, _, _, h => by
      simp only [inferArgs, Option.some.injEq, Prod.mk.injEq] at h
      exact h.2.2.symm
  | e :: rest, Dq, Γ, top, ctx, τs, Γ', D₀, hret, htop, h => by
      simp only [inferArgs] at h
      cases he : infer Dq Γ e top ctx with
      | none => rw [he] at h; simp at h
      | some r =>
        obtain ⟨τe, Γ₁, D₁⟩ := r
        rw [he] at h
        have hD : D₁ = Dq := infer_table_loop Dq Γ e top ctx hret htop _ _ _ he
        subst hD
        dsimp only at h
        cases hr : inferArgs D₁ Γ₁ rest top ctx with
        | none => rw [hr] at h; simp at h
        | some r' =>
          obtain ⟨τr, Γ₂, D₂⟩ := r'
          rw [hr] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, -, rfl⟩ := h
          exact inferArgs_table_loop hret htop hr

/-- **Monotonicity, with the table-stability half it needs.** Proved by the
    functional induction `infer` generates, so the case list is the rule list and
    every out-of-fragment head is discharged by its own `none`. -/
theorem infer_mono_all : ∀ (D : Decls) (Γ : Env) (e : Expr) (top : Bool) (ctx : FrameCtx),
    ∀ F', SubDecls D F' → defFree e = true → ∀ τ Γ' D₀,
      infer D Γ e top ctx = some (τ, Γ', D₀) →
      D₀ = D ∧ infer F' Γ e top ctx = some (τ, Γ', F') := by
  intro D Γ e top ctx
  induction D, Γ, e, top, ctx using infer.induct with
  | motive2 Da Γa ta elsa topa ctxa =>
    exact ∀ F', SubDecls Da F' →
      (defFree ta && (match elsa with | some e' => defFree e' | none => true)) = true →
      ∀ τ Γ' D₀, inferIf Da Γa ta elsa topa ctxa = some (τ, Γ', D₀) →
        D₀ = Da ∧ inferIf F' Γa ta elsa topa ctxa = some (τ, Γ', F')
  | motive3 Da Γa esa topa ctxa =>
    exact ∀ F', SubDecls Da F' → defFreeAll esa = true →
      ∀ τ Γ' D₀, inferSeq Da Γa esa topa ctxa = some (τ, Γ', D₀) →
        D₀ = Da ∧ inferSeq F' Γa esa topa ctxa = some (τ, Γ', F')
  -- **The argument list** (L175). Same statement, at the fourth motive: the send
  -- rules need the arguments' *types* in order, so `inferArgs` is a separate
  -- traversal from `inferSeq` and needs its own monotonicity.
  | motive4 Da Γa esa topa ctxa =>
    exact ∀ F', SubDecls Da F' → defFreeAll esa = true →
      ∀ τs Γ' D₀, inferArgs Da Γa esa topa ctxa = some (τs, Γ', D₀) →
        D₀ = Da ∧ inferArgs F' Γa esa topa ctxa = some (τs, Γ', F')
  -- **A local read.** The table appears only as the third component of the answer.
  | case7 D Γ top ctx x =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [infer, Option.map_eq_some_iff] at h
    obtain ⟨σ, hg, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    exact ⟨rfl, by simp [infer, hg]⟩
  -- **`self`** (F1b.11). The context is a parameter, not the table, so the rule is
  -- monotone for the same reason a literal's is.
  | case8 D Γ top ctx c hsome =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [infer, hsome, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [infer, hsome]⟩
  -- **`vcall`**, and the one case in the induction where `SubDecls` is used at a
  -- receiver the *context* supplies rather than an expression.
  | case10 D Γ top ctx mname c hsome τret hsig =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [infer, hsome, hsig, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [infer, hsome, SubDecls.sigOf_eq hs hsig]⟩
  -- **Assignment.** One IH, and the `rfl` it returns is what lines the output
  -- tables up — which is why the two conclusions had to be proved together.
  | case13 D Γ top ctx x rhs τr Γ₁ D₁ hrhs ih =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [defFree] at hdf
    obtain ⟨rfl, hm⟩ := ih F' hs hdf _ _ _ hrhs
    simp only [infer, hrhs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [infer, hm]⟩
  -- **`@x = e`** (L191/L196). Two accepting arms since the write checks the table:
  -- the declared case, where the widening has to preserve the *conformance* too, and
  -- the undeclared one, where there is nothing to conform to. `SubDecls`' ivar half
  -- is an equality (as its constant half is), so both are the rhs's IH plus a rewrite.
  | case15 D Γ top ctx name rhs sc hsome τr Γ₁ D₁ hrhs σ hiv hsub ih =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [defFree] at hdf
    obtain ⟨rfl, hm⟩ := ih F' hs hdf _ _ _ hrhs
    simp only [infer, hsome, hrhs, hiv, hsub, if_true, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [infer, hsome, hm, hs.ivarTy_eq, hiv, hsub]⟩
  | case17 D Γ top ctx name rhs sc hsome τr Γ₁ D₁ hrhs hiv ih =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [defFree] at hdf
    obtain ⟨rfl, hm⟩ := ih F' hs hdf _ _ _ hrhs
    simp only [infer, hsome, hrhs, hiv, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [infer, hsome, hm, hs.ivarTy_eq, hiv]⟩
  -- **`@x`** (L196). The answer comes out of the table, so like `case33`'s constant
  -- read this case *uses* `SubDecls` — through its ivar half, an equality.
  | case20 D Γ top ctx x sc hsome σ hiv =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [infer, hsome, hiv, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [infer, hsome, hs.ivarTy_eq, hiv]⟩
  -- **The unary send**, and the only case where `SubDecls` is *used* rather than
  -- carried: the signature has to be readable at the bigger table, which is what
  -- the relation was defined to say.
  | case23 D Γ top ctx recv mname arg args τr Γ₁ D₁ hrecv τs Γ₂ D₂ hargs ps τret
      hsig hsub ihR ihA =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [defFree, defFreeAll, Bool.and_eq_true] at hdf
    obtain ⟨rfl, hmR⟩ := ihR F' hs (by simp_all [defFree, defFreeAll]) _ _ _ hrecv
    obtain ⟨rfl, hmA⟩ := ihA F' hs (by simp_all [defFree, defFreeAll]) _ _ _ hargs
    simp only [infer, hrecv, hargs, hsig, hsub,
      Option.some.injEq, Prod.mk.injEq, if_pos] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [infer, hmR, hmA, SubDecls.sigOf_eq hs hsig, hsub]⟩
  -- **The zero-argument send.** Same shape, one fewer subexpression.
  | case28 D Γ top ctx recv mname τr Γ₁ D₁ hrecv τret hsig ihR =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [defFree, defFreeAll, Bool.and_eq_true] at hdf
    obtain ⟨rfl, hmR⟩ := ihR F' hs (by simp_all [defFree, defFreeAll]) _ _ _ hrecv
    simp only [infer, hrecv, hsig,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [infer, hmR, SubDecls.sigOf_eq hs hsig]⟩
  -- **The written receiverless call** (L170), `foo()`. Identical to `vcall`'s
  -- case — same receiver from the context, same `SubDecls.sigOf_eq` — which is
  -- the monotonicity half of the claim that the two rules differ only in a
  -- `SendSite`.
  | case31 D Γ top ctx mname c hsome τret hsig =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [infer, hsome, hsig, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [infer, hsome, SubDecls.sigOf_eq hs hsig]⟩
  -- **The unary written receiverless call** (L171). One subexpression and the
  -- signature read at the table it leaves — the explicit unary send's case with
  -- the receiver supplied by the context instead of by an expression.
  | case34 D Γ top ctx mname arg args c hsome τs Γ₁ D₁ hargs ps τret hsig hsub ih =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [defFree, defFreeAll, Bool.and_eq_true] at hdf
    obtain ⟨rfl, hmA⟩ := ih F' hs (by simp_all [defFree, defFreeAll]) _ _ _ hargs
    simp only [infer, hsome, hargs, hsig, hsub, Option.some.injEq, Prod.mk.injEq,
      if_pos] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [infer, hsome, hmA, SubDecls.sigOf_eq hs hsig, hsub]⟩
  -- **A constant read** (L189). The table appears only as the third component of
  -- the answer, exactly as a local read's does.
  -- **L195: the answer comes out of the table**, so this case now *uses* `SubDecls`
  -- — through its constant half, which is an equality. Before, the rule read a global
  -- list and the case was as inert as a literal's.
  | case39 D Γ top ctx n τc hre =>
    intro F' hs hdf τ Γ' D₀ h
    rw [show infer D Γ (.const n) top ctx = some (τc, Γ, D) from by
      simp only [infer, hre]] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp only [infer, hs.constTy_eq n, hre]⟩
  -- **`super()`** (L212). The answer comes out of the `supers` table, so the case
  -- *uses* `SubDecls` — through its fifth half, which is an equality (`superDecl_eq`).
  -- Same shape as `.const`'s (case39): no IH, one table read, two guards to recompute.
  | case71 D Γ top ctx mn hmeth hne dd hrow hemp =>
    intro F' hs hdf τ Γ' D₀ h
    rw [show infer D Γ (.super' [] none) top ctx = some (dd.ret, Γ, D) from by
      simp only [infer, hmeth, hrow, if_pos hne, if_pos hemp]] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by
      simp only [infer, hmeth, hs.superDecl_eq, hrow, if_pos hne, if_pos hemp]⟩
  -- **`super(args)`** (L212). The argument list's IH plus the same table read, and the
  -- read is at the table the *last* argument leaves — which is why the IH's `D₀ = D`
  -- half has to be spent before `superDecl_eq` can fire.
  | case76 D Γ top ctx arg args mn hmeth hne τs Γ₂ D₂ hargs dd hrow hsub ih =>
    intro F' hsb hdf τ Γ' D₀ h
    simp only [defFree, Bool.and_eq_true] at hdf
    obtain ⟨rfl, hm⟩ := ih F' hsb (by simp_all [defFree]) _ _ _ hargs
    rw [show infer D₂ Γ (.super' (arg :: args) none) top ctx = some (dd.ret, Γ₂, D₂) from by
      simp only [infer, hmeth, hargs, hrow, if_pos hne, if_pos hsub]] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by
      simp only [infer, hmeth, hm, hsb.superDecl_eq, hrow, if_pos hne, if_pos hsub]⟩
  -- **Bare `super`** (L214). `super()`'s case (case71) with the argument types read off
  -- the *context* instead of the expression, so it has no IH at all — and it uses
  -- `SubDecls` twice: `superDecl_eq` for the row and nothing for `ctx.params`, which is a
  -- parameter and not a table.
  | case82 D Γ top ctx mn ps hpar hmeth hne dd hrow hsub =>
    intro F' hs hdf τ Γ' D₀ h
    rw [show infer D Γ (.zsuper none) top ctx = some (dd.ret, Γ, D) from by
      simp only [infer, hmeth, hpar, hrow, if_pos hne, if_pos hsub]] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by
      simp only [infer, hmeth, hpar, hs.superDecl_eq, hrow, if_pos hne, if_pos hsub]⟩
  -- **An array literal** (L174). The elements' *types* are erased, so the only
  -- thing to transport is the threading — which makes this case the third motive
  -- applied once, with the answer type a constant.
  | case41 D Γ top ctx es τ0 Γ₁ D₁ hs ih =>
    intro F' hsub hdf τ Γ' D₀ h
    simp only [defFree] at hdf
    obtain ⟨rfl, hm⟩ := ih F' hsub hdf _ _ _ hs
    simp only [infer, hs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [infer, hm]⟩
  -- `seq` is `inferSeq` definitionally, so this case is the third motive verbatim.
  | case51 D Γ top ctx es ih =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [defFree] at hdf
    simp only [infer] at h ⊢
    exact ih F' hs hdf _ _ _ h
  | case52 D Γ top ctx c t els τc Γ₁ D₁ hc ihC ihI =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [defFree_if, Bool.and_eq_true] at hdf
    obtain ⟨⟨hc1, ht1⟩, he1⟩ := hdf
    obtain ⟨rfl, hmC⟩ := ihC F' hs hc1 _ _ _ hc
    simp only [infer, hc] at h
    obtain ⟨rfl, hmI⟩ := ihI F' hs (by simp only [ht1, Bool.true_and]; exact he1) _ _ _ h
    exact ⟨rfl, by simp [infer, hmC, hmI]⟩
  -- **The loop**, where the stability side conditions do the work: both come back
  -- as `rfl`s, so the table at `F'` is stable for the same reason it was at `F`.
  | case54 D Γ top ctx c body τc Γc Dc hc hstc τb Γb Db hbody hstb ihC ihB =>
    intro F' hs hdf τ Γ' D₀ h
    obtain ⟨rfl, rfl⟩ := hstc
    obtain ⟨rfl, rfl⟩ := hstb
    simp only [defFree, Bool.and_eq_true] at hdf
    obtain ⟨_, hmC⟩ := ihC F' hs (by simp_all [defFree]) _ _ _ hc
    obtain ⟨_, hmB⟩ := ihB F' hs (by simp_all [defFree]) _ _ _ hbody
    simp only [infer, hc, hbody, and_self, if_pos, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [infer, hmC, hmB]⟩
  -- `inferIf`, both arms: the join conditions are equalities, so they transport
  -- by the same `rfl`s the loop's stability does.
  | case99 D Γ t top ctx e' τt Γt Dt τe Γe De hE hT hagree ihT ihE =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [Bool.and_eq_true] at hdf
    obtain ⟨rfl, hmT⟩ := ihT F' hs hdf.1 _ _ _ hT
    obtain ⟨rfl, hmE⟩ := ihE F' hs hdf.2 _ _ _ hE
    obtain ⟨hΓ, -⟩ := hagree
    subst hΓ
    simp only [inferIf, hT, hE] at h
    rw [if_pos (by simp)] at h
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨τj, hjoin, rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [inferIf, hmT, hmE, hjoin]⟩
  | case102 D Γ t top ctx τt Γt Dt hT hcond ihT =>
    intro F' hs hdf τ Γ' D₀ h
    obtain ⟨rfl, rfl⟩ := hcond
    obtain ⟨_, hmT⟩ := ihT F' hs (by simp_all) _ _ _ hT
    simp only [inferIf, hT] at h
    rw [if_pos (by simp)] at h
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨τj, hjoin, rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [inferIf, hmT, hjoin]⟩
  -- `inferSeq`'s three arms, mirroring `evalExpr`'s split on `.seq`.
  | case105 D Γ top ctx =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [inferSeq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [inferSeq]⟩
  | case106 D Γ top ctx e ih =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [defFreeAll, Bool.and_eq_true] at hdf
    simp only [inferSeq] at h ⊢
    exact ih F' hs (by simp_all [defFreeAll]) _ _ _ h
  | case107 D Γ top ctx e rest hne τe Γ₁ D₁ he ihE ihR =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [defFreeAll, Bool.and_eq_true] at hdf
    obtain ⟨rfl, hmE⟩ := ihE F' hs (by simp_all [defFreeAll]) _ _ _ he
    cases rest with
    | nil => exact absurd rfl hne
    | cons e₂ r₂ =>
      simp only [inferSeq, he] at h
      obtain ⟨rfl, hmR⟩ := ihR F' hs (by simp_all [defFreeAll]) _ _ _ h
      exact ⟨rfl, by simp [inferSeq, hmE, hmR]⟩
  -- **`inferArgs`' three arms** (L175), mirroring `startArgs`' loop. The `[]` arm
  -- is a `rfl`; the recursive arm is the only place two IHs of *different* motives
  -- meet, and the reason it needs both is that an argument may itself be a send.
  -- **`inferArgs`' two accepting arms** (L175), mirroring `startArgs`' loop. The
  -- `[]` arm is a `rfl`; the recursive arm is the only place two IHs of *different*
  -- motives meet, and the reason it needs both is that an argument may itself be a
  -- send.
  | case109 D Γ top ctx =>
    intro F' hs hdf τs Γ' D₀ h
    simp only [inferArgs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [inferArgs]⟩
  | case110 D Γ top ctx e rest τe Γ₁ D₁ he τs Γ₂ D₂ hrest ihE ihR =>
    intro F' hs hdf τs' Γ' D₀ h
    simp only [defFreeAll, Bool.and_eq_true] at hdf
    obtain ⟨rfl, hmE⟩ := ihE F' hs (by simp_all [defFreeAll]) _ _ _ he
    obtain ⟨rfl, hmR⟩ := ihR F' hs (by simp_all [defFreeAll]) _ _ _ hrest
    simp only [inferArgs, he, hrest, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [inferArgs, hmE, hmR]⟩
  -- **L228's global read** (case87), and it is an *explicit case* rather than an
  -- alternative in the block below — which is the lesson of the rung. The two guards are
  -- **hypotheses** here, not `if`s in the goal, so an alternative that `split`s cannot
  -- match; and one that half-matches leaves *unsolved goals* rather than failing, which
  -- aborts `first` instead of falling through to the next alternative. A named case is
  -- immune to both.
  | case87 D Γ top ctx x σ hgt hpg =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [infer, hpg, hgt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp only [infer, hpg, hs.globalTy_eq, hgt]⟩
  -- **And the write** (case89/case90 — two cases, because the equation compiler splits
  -- the guard pair and the right-hand side's own `match` separately). Same shape with
  -- `case13`'s IH step in the middle.
  | case89 D Γ top ctx x rhs hpg τr Γr Dr hq0 σ hgt hsub ih1 =>
    intro F' hs hdf τ Γ' D₀ h
    obtain ⟨rfl, hm⟩ := ih1 F' hs (by simpa [defFree] using hdf) _ _ _ hq0
    simp only [infer, hpg, hq0, hgt, hsub, if_true, reduceIte, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp only [infer, hpg, hm, hs.globalTy_eq, hgt, hsub, if_true, reduceIte]⟩
  -- `case90` is the *refused* write — the value's type is not the declared one — and
  -- `case91` the *undeclared* one, which is the needed-declaration branch. Both make the
  -- rule answer `none`, so the hypothesis is false; kept explicit rather than left to the
  -- `exfalso` alternatives for their sibling's reason.
  | case90 D Γ top ctx x rhs hpg τr Γr Dr hq0 σ hgt hsub _ih1 =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [infer, hpg, hq0, hgt, if_neg hsub] at h
    exact absurd h (by simp)
  | case91 D Γ top ctx x rhs hpg τr Γr Dr hq0 hgt _ih1 =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [infer, hpg, hq0, hgt] at h
    exact absurd h (by simp)
  | _ =>
    intro F' hs hdf τ Γ' D₀ h
    first
      | (exfalso; revert h; simp +contextual [infer, inferIf, inferSeq, inferArgs]; done)
      | (exfalso; simp_all only [infer, inferIf, inferSeq, inferArgs, reduceCtorEq]; done)
      | (exfalso; simp_all [infer, inferIf, inferSeq, inferArgs, defFree, defFreeAll]; done)
      -- The `self`-receiver guard's negative branch, and the arms under it: `infer`
      -- answers `none` outright, so the hypothesis is refuted by computing the
      -- guard rather than by anything about types (F1b.11).
      | (exfalso; revert h; simp only [infer]; split <;> simp_all; done)
      | (simp only [infer, Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl, rfl⟩ := h
         exact ⟨rfl, by simp [infer]⟩)
      -- **`return e`** (L200), both arms. `ctx.ret` is not the declaration table, so
      -- the guard and the `subTy` check transport untouched and what is left is the
      -- returned expression's IH — `case13`'s shape.
      | (rename_i ih1
         revert h
         simp only [infer]
         split
         · rename_i hret
           split
           · rename_i hq
             split
             · rename_i hsub
               intro hq2
               simp only [Option.some.injEq, Prod.mk.injEq] at hq2
               obtain ⟨rfl, rfl, rfl⟩ := hq2
               obtain ⟨rfl, hm⟩ := ih1 F' hs (by simpa [defFree] using hdf) _ _ _ hq
               exact ⟨rfl, by simp [infer, hret, hm, hsub]⟩
             · simp
           · simp
         · simp)
      -- **L203's `::n`**, and it is `case39`'s tactic with the name left to
      -- unification: the arm is one table read, the answer's table is the input's,
      -- and `SubDecls`' constant half is an equality. Kept as an *alternative* rather
      -- than an explicit case because the hit and the miss are two cases and neither
      -- needs a hypothesis named.
      | (revert h
         simp only [infer]
         split
         · rename_i hre
           intro hq
           simp only [Option.some.injEq, Prod.mk.injEq] at hq
           obtain ⟨rfl, rfl, rfl⟩ := hq
           exact ⟨rfl, by simp only [infer, hs.constTy_eq, hre]⟩
         · simp)
      | (revert h
         simp only [infer]
         split
         · rename_i hret
           split
           · rename_i hsub
             intro hq2
             simp only [Option.some.injEq, Prod.mk.injEq] at hq2
             obtain ⟨rfl, rfl, rfl⟩ := hq2
             exact ⟨rfl, by simp [infer, hret, hsub]⟩
           · simp
         · simp)
      -- **L205's `C::n`.** One IH (the base), then two table reads — and the base's
      -- table has to come back *equal*, which is what `defFree`'s new `.cpath` arm is
      -- for: this case is what found that the catch-all's vacuous `true` made
      -- `infer_mono` false for a `def` inside a namespace expression.
      | (rename_i hbase _τa hsco ih1
         obtain ⟨rfl, hm⟩ := ih1 F' hs (by simpa [defFree] using hdf) _ _ _ hbase
         simp only [infer, hbase, hsco, Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl, rfl⟩ := h
         exact ⟨rfl, by simp only [infer, hm, hs.scopedConstTy_eq, hsco]⟩)
      -- **L227's bare `next`**, all four of its alternatives, and the arm reads *nothing*
      -- from the table: `top`, `ctx.inLoop` and `subEnvB` are all table-free, so the
      -- transport is three `split`s and a recomputation. An IH-free case, like `case105`.
      | (rename_i _ hil hse
         simp only [infer, hil, hse, if_true, reduceIte, Option.some.injEq,
           Prod.mk.injEq] at h
         obtain ⟨rfl, rfl, rfl⟩ := h
         exact ⟨rfl, by simp only [infer, hil, hse, if_true, reduceIte]⟩)
      -- No fallback: every case is closed above or by one of the four uniform
      -- tactics, and there is deliberately no `sorry` arm to hide a case the next
      -- widening adds. A new `infer` rule breaks this proof, which is the same
      -- discipline `step_ok` enforces (`HANDOFF.md` constraint 4) — and the case
      -- *numbers* move when it does, including when an existing rule merely gains a
      -- guard. Recovery, three times now (L163, L164 twice): strip the explicit
      -- cases, restore a `trace "UNSOLVED-CASE"` arm here, read the list off the
      -- trace, renumber, re-attach.

/-- **The form the invariant reads.** `UserConforms` says the body infers at the
    declared return type *and leaves the table alone*; this is that statement
    transported to a larger table, which is exactly what preservation across a
    `def` step owes for every row already in force. -/
theorem infer_mono {F F' : Decls} {Γ : Env} {e : Expr} {top : Bool} {ctx : FrameCtx}
    {τ : Ty} {Γ' : Env}
    (hs : SubDecls F F') (hdf : defFree e = true)
    (h : infer F Γ e top ctx = some (τ, Γ', F)) :
    infer F' Γ e top ctx = some (τ, Γ', F') :=
  (infer_mono_all F Γ e top ctx F' hs hdf τ Γ' F h).2

/-- The stability half on its own, which the rules' side conditions want. -/
theorem infer_decls_stable {F : Decls} {Γ : Env} {e : Expr} {top : Bool} {ctx : FrameCtx}
    {τ : Ty} {Γ' : Env} {D₀ : Decls} (hdf : defFree e = true)
    (h : infer F Γ e top ctx = some (τ, Γ', D₀)) : D₀ = F :=
  (infer_mono_all F Γ e top ctx F (SubDecls.refl F) hdf τ Γ' D₀ h).1

end Static
end Proof
end RubyCore
