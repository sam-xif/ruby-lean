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
  -- **L230: `motive4` is `inferElems` and `motive5` is `inferArgs`**, and the order is
  -- *not* the file's — the two functions have the same signature, so a swapped assignment
  -- type-checks and only the IHs' shapes reveal it. Measured with `trace_state`.
  | motive4 Da Γa esa topa ctxa =>
    exact ctxa.ret.isSome = true → topa = false → ∀ τ Γ' D₀,
      inferElems Da Γa esa topa ctxa = some (τ, Γ', D₀) → D₀ = Da
  | motive5 Da Γa esa topa ctxa =>
    exact ctxa.ret.isSome = true → topa = false → ∀ τs Γ' D₀,
      inferArgs Da Γa esa topa ctxa = some (τs, Γ', D₀) → D₀ = Da
  -- **The `if`-with-else arm**, explicit because the answer's table is the *then*
  -- branch's and the join's guard has to be split before either IH is usable.
  | case111 D Γ t top ctx e' τt Γt Dt τe Γe De hE hT hagree ih2 ih1 =>
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
      | (exfalso; revert h; simp +contextual [infer, inferIf, inferSeq, inferArgs, inferElems, htop]; done)
      | (simp_all only [infer, inferIf, inferSeq, inferArgs, inferElems, Option.some.injEq,
           Prod.mk.injEq, reduceCtorEq]; done)
      | (simp_all [infer, inferIf, inferSeq, inferArgs, inferElems, htop, hret]; done)
      | (rename_i ih1
         exact ih1 hret htop _ _ _ (by simpa [infer, inferIf, inferSeq, inferArgs, inferElems] using h))
      | (rename_i ih2 ih1
         first
           | exact ih1 hret htop _ _ _ (by simpa [infer, inferSeq, inferArgs, inferElems] using h)
           | exact ih2 hret htop _ _ _ (by simpa [infer, inferSeq, inferArgs, inferElems] using h))
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

/-- **L230's element traversal**, and it is `inferSeq_table_ret`'s proof with one more
    case: a splat element threads the table through its **operand**, which is one
    `infer_table_ret` at a different subexpression. -/
theorem inferElems_table_ret : ∀ {es : List Expr} {D : Decls} {Γ : Env} {top : Bool}
    {ctx : FrameCtx} {τ : Ty} {Γ' : Env} {D₀ : Decls}, ctx.ret.isSome = true → top = false →
    inferElems D Γ es top ctx = some (τ, Γ', D₀) → D₀ = D
  | [], D, Γ, top, ctx, τ, Γ', D₀, _, _, h => by
      simp only [inferElems, Option.some.injEq, Prod.mk.injEq] at h
      exact h.2.2.symm
  | e :: rest, D, Γ, top, ctx, τ, Γ', D₀, hret, htop, h => by
      cases e
      case splat oe =>
        cases oe with
        -- `.splat none` (an anonymous splat) has no `infer` arm, so it falls to
        -- `inferElems`' catch-all and is refused there.
        | none => exact absurd h (by simp [inferElems, infer])
        | some o =>
          simp only [inferElems] at h
          cases ho : infer D Γ o top ctx with
          | none => rw [ho] at h; exact absurd h (by simp)
          | some r =>
            obtain ⟨τo, Γ₁, D₁⟩ := r
            rw [ho] at h
            have hD : D₁ = D := infer_table_ret D Γ o top ctx hret htop _ _ _ ho
            subst hD
            cases τo with
            | cls nm =>
              by_cases hnm : nm = "Array"
              · subst hnm
                exact inferElems_table_ret hret htop h
              · simp_all
            | _ => simp_all
      all_goals
        (simp only [inferElems] at h
         cases he : infer D Γ _ top ctx with
         | none => rw [he] at h; simp at h
         | some r =>
           obtain ⟨τe, Γ₁, D₁⟩ := r
           rw [he] at h
           have hD : D₁ = D := infer_table_ret D Γ _ top ctx hret htop _ _ _ he
           subst hD
           exact inferElems_table_ret hret htop h)

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

/-! ### L234 — environment monotonicity, for the expressions a continuation stores

`inferIf` refuses two branches whose environments differ, which is what refuses every desugared
`||`, `&&` and `&.` (L231), and `begin`'s handler needs the same relation from the other side
(L233). Both want to *widen* a stored `infer` equation from an environment to a larger one, and
this is that lemma at the special case both of them are actually about: **an expression that
assigns no local**.

The general case would have to say what `envSet`'s *ordering* does under a widening, since `while`
and `if` compare environments for equality. The assign-free case has no `envSet` at all: the answer
environment *is* the argument, and the only other way `infer` reads it is `envGet?`, which `SubEnv`
pins by definition.
-/

/-- **An assign-free expression answers the environment it was given, and widening it changes
    nothing else** (L234). -/
theorem infer_env_mono : ∀ (D : Decls) (Γ : Env) (e : Expr) (top : Bool) (ctx : FrameCtx),
    asgnFree e = true → ∀ τ Γ' D₀, infer D Γ e top ctx = some (τ, Γ', D₀) →
      Γ' = Γ ∧ ∀ Γ₂, SubEnv Γ Γ₂ → infer D Γ₂ e top ctx = some (τ, Γ₂, D₀) := by
  intro D Γ e top ctx
  induction D, Γ, e, top, ctx using infer.induct with
  | motive2 Da Γa ta elsa topa ctxa =>
    exact asgnFree ta = true ∧ asgnFreeOpt elsa = true →
      ∀ τ Γ' D₀, inferIf Da Γa ta elsa topa ctxa = some (τ, Γ', D₀) →
        Γ' = Γa ∧ ∀ Γ₂, SubEnv Γa Γ₂ → inferIf Da Γ₂ ta elsa topa ctxa = some (τ, Γ₂, D₀)
  | motive3 Da Γa esa topa ctxa =>
    exact asgnFreeAll esa = true → ∀ τ Γ' D₀, inferSeq Da Γa esa topa ctxa = some (τ, Γ', D₀) →
      Γ' = Γa ∧ ∀ Γ₂, SubEnv Γa Γ₂ → inferSeq Da Γ₂ esa topa ctxa = some (τ, Γ₂, D₀)
  | motive4 Da Γa esa topa ctxa =>
    exact asgnFreeAll esa = true → ∀ τ Γ' D₀, inferElems Da Γa esa topa ctxa = some (τ, Γ', D₀) →
      Γ' = Γa ∧ ∀ Γ₂, SubEnv Γa Γ₂ → inferElems Da Γ₂ esa topa ctxa = some (τ, Γ₂, D₀)
  | motive5 Da Γa esa topa ctxa =>
    exact asgnFreeAll esa = true → ∀ τs Γ' D₀, inferArgs Da Γa esa topa ctxa = some (τs, Γ', D₀) →
      Γ' = Γa ∧ ∀ Γ₂, SubEnv Γa Γ₂ → inferArgs Da Γ₂ esa topa ctxa = some (τs, Γ₂, D₀)
  -- **`if`** (case52): the condition fixes the environment and `inferIf` answers it.
  | case53 D Γ top ctx c t els τc Γ₁ D₁ hc ih2 ih1 =>
    intro hasg τ Γ' D₀ h
    have hac : asgnFree c = true := by
      unfold asgnFree at hasg; simp only [Bool.and_eq_true] at hasg; exact hasg.1.1
    have hai : asgnFree t = true ∧ asgnFreeOpt els = true := by
      unfold asgnFree at hasg; simp only [Bool.and_eq_true] at hasg
      exact ⟨hasg.1.2, by cases els <;> simpa [asgnFreeOpt] using hasg.2⟩
    obtain ⟨rfl, hmc⟩ := ih2 hac _ _ _ hc
    simp only [infer, hc] at h
    obtain ⟨rfl, hmi⟩ := ih1 hai _ _ _ h
    exact ⟨rfl, fun Γ₂ hs => by simp only [infer, hmc Γ₂ hs, hmi Γ₂ hs]⟩
  -- **`next`** (case94), and it is the one arm whose *guard* mentions the environment: the
  -- rule checks `subEnvB Γl Γ`, and at a wider `Γ₂` that check still passes — which is one
  -- transitivity, and the reason the statement is over `SubEnv` in the first place.
  | case95 D Γ ctx Γl hil hse =>
    intro hasg τ Γ' D₀ h
    simp only [infer, hil, hse, if_true, reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨rfl, fun Γ₂ hs => ?_⟩
    have hse2 : subEnvB Γl Γ₂ = true := subEnvB_trans_sub hse hs
    simp only [infer, hil, hse2, if_true, reduceIte]
  -- **The block send** (L257), and it is the only arm whose *subexpression's environment
  -- is built from the send's own* — so this is the one case that spends `anyEnv_subEnv`.
  | case99 D Γ top ctx recv mname ps ls body τr Γ₁ D₁ hrecv x σp βret τret hbs
      τb Γb' D₂ hbody hif ihR ihB =>
    intro hasg τ Γ' D₀ h
    simp only [asgnFree, Bool.and_eq_true] at hasg
    obtain ⟨rfl, hmR⟩ := ihR hasg.1.1 _ _ _ hrecv
    obtain ⟨rfl, hmB⟩ := ihB hasg.2 _ _ _ hbody
    simp only [infer, hrecv, hbs, hbody, hif, if_true, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨rfl, fun Γ₂ hs => ?_⟩
    have hsb : SubEnv ((x, σp) :: anyEnv Γ₁) ((x, σp) :: anyEnv Γ₂) :=
      SubEnv.cons _ (anyEnv_subEnv hs)
    have hif2 : subTy τb βret = true ∧ D₂ = D₁ ∧
        subEnvB ((x, σp) :: anyEnv Γ₂) ((x, σp) :: anyEnv Γ₂) = true ∧ ctx.inBlock = false :=
      ⟨hif.1, hif.2.1, subEnvB_refl _, hif.2.2.2⟩
    simp only [infer, hmR Γ₂ hs, hbs, hmB _ hsb, hif2, if_true]
    simp
  | case100 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21
      a22 a23 a24 a25 =>
    intro _ τ Γ' D₀ h
    exfalso; revert h; simp +contextual [infer, a13, a18, a22, a23]
  | case101 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 =>
    intro _ τ Γ' D₀ h
    exfalso; revert h; simp +contextual [infer, a13, a18, a19]
  | case102 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 =>
    intro _ τ Γ' D₀ h
    exfalso; revert h; simp +contextual [infer, a13, a14]
  | case103 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 =>
    intro _ τ Γ' D₀ h
    exfalso; revert h; simp +contextual [infer, a10]
  -- **L259's arity-`n` block send.** The arity-zero case above, plus the argument
  -- traversal's own IH — and the arguments are assign-free, so their output environment
  -- is their input one and nothing new has to be transported.
  | case104 D Γ top ctx recv mname arg args ps ls body τr Γ₁ D₁ hrecv τs Γ₂ D₂ hargs
      x σp βret dps τret hbs τb Γb' D₃ hbody hif ihR ihA ihB =>
    intro hasg τ Γ' D₀ h
    simp only [asgnFree, Bool.and_eq_true] at hasg
    obtain ⟨rfl, hmR⟩ := ihR hasg.1.1 _ _ _ hrecv
    obtain ⟨rfl, hmA⟩ := ihA hasg.1.2 _ _ _ hargs
    obtain ⟨rfl, hmB⟩ := ihB hasg.2 _ _ _ hbody
    -- The two table equalities go first. `simp` would otherwise use `D₂ = D₁` as a
    -- rewrite and then `hbs` — which is stated at `D₂` — would no longer match; the
    -- arity-zero arm does not have this problem only because it reads the table
    -- *before* the arguments run.
    obtain ⟨hsts, hsub, rfl, rfl, rfl, -, hib⟩ := hif
    simp only [infer, hrecv, hargs, hbs, hbody, hsts, hsub, hib, subEnvB_refl,
      and_true, true_and, and_self, if_true, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨rfl, fun Γw hs => ?_⟩
    simp only [infer, hmR Γw hs, hmA Γw hs, hbs,
      hmB _ (SubEnv.cons _ (anyEnv_subEnv hs)), hsts, hsub, hib, subEnvB_refl,
      and_true, true_and, and_self, if_true]
  | case105 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21
      a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 =>
    intro _ τ Γ' D₀ h
    exfalso; revert h; simp +contextual [infer, a15, a19, a25, a29, a30]
  | case106 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21
      a22 a23 a24 a25 a26 a27 a28 a29 =>
    intro _ τ Γ' D₀ h
    exfalso; revert h; simp +contextual [infer, a15, a19, a25, a26]
  | case107 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21
      a22 =>
    intro _ τ Γ' D₀ h
    exfalso; revert h; simp +contextual [infer, a15, a19, a20]
  | case108 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 =>
    intro _ τ Γ' D₀ h
    exfalso; revert h; simp +contextual [infer, a15, a16]
  | case109 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 =>
    intro _ τ Γ' D₀ h
    exfalso; revert h; simp +contextual [infer, a12]
  -- **The `if` join** (case111): the two branches answer the same environment, which the arm
  -- already checked, so the join transports unchanged.
  | case111 D Γ t top ctx e' τt Γt Dt τe Γe De hE hT hag ih2 ih1 =>
    intro hasg τ Γ' D₀ h
    obtain ⟨rfl, hmT⟩ := ih2 hasg.1 _ _ _ hT
    obtain ⟨rfl, hmE⟩ := ih1 (by simpa [asgnFreeOpt] using hasg.2) _ _ _ hE
    simp only [inferIf, hT, hE] at h
    split at h
    · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      -- L236: both branches are assign-free, so each answers the environment it was
      -- given, and the rule's answer is the entry one — nothing to transport but the
      -- guard, which is `subEnvB Γ₂ Γ₂` at the wider environment.
      obtain ⟨τj, hj, rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun Γ₂ hs => ?_⟩
      simp only [inferIf, hmT Γ₂ hs, hmE Γ₂ hs]
      split
      · simp [hj]
      · rename_i hbad
        -- The guard that just failed is the one `hag` already established: after the two
        -- IHs' `rfl`s the environments are syntactically equal, so what is left is the
        -- table half, and that is `hag`'s second component.
        exact absurd hag.2.2 (by simpa using hbad)
    · exact absurd hag (by assumption)
  | _ =>
    intro hasg τ Γ' D₀ h
    first
      | (exfalso; revert h
         simp +contextual [infer, inferIf, inferSeq, inferArgs, inferElems, asgnFree,
           asgnFreeAll] at hasg ⊢
         done)
      -- **The local read**, and it is the only arm that reads the environment at all —
      -- which is why `SubEnv` is exactly the right hypothesis and why every other arm
      -- closes by computation.
      | (simp only [infer, Option.map_eq_some_iff] at h
         obtain ⟨a, hg, heq⟩ := h
         simp only [Prod.mk.injEq] at heq
         obtain ⟨rfl, rfl, rfl⟩ := heq
         exact ⟨rfl, fun Γ₂ hs => by simp [infer, hs _ _ hg]⟩)
      | (refine ⟨?_, fun Γ₂ hs => ?_⟩ <;>
           (simp_all [infer, inferIf, inferSeq, inferArgs, inferElems, asgnFree, asgnFreeAll]
            done))
      -- **Two subexpressions threaded**: the first fixes the environment (it is assign-free,
      -- so it answers the one it was given) and the second is the answer. The `rfl` from the
      -- first IH is what lets the second one apply at all — before it, the two are stated at
      -- different environments and neither composes.
      | (rename_i hc ih2 ih1
         simp only [asgnFree, Bool.and_eq_true] at hasg
         obtain ⟨rfl, hm2⟩ := ih2 (by simp_all [asgnFree]) _ _ _ hc
         obtain ⟨rfl, hm1⟩ := ih1 (by simp_all) _ _ _ h
         exact ⟨rfl, fun Γ₂ hs => by
           simp only [infer, inferIf, inferSeq, inferArgs, inferElems, hm2 Γ₂ hs, hm1 Γ₂ hs]⟩)
      -- **`def`** (case44/45), whose only dependence on the environment is the answer's
      -- second component: the body is typed at `[]` and every guard is about names and
      -- tables. So the case is the arm's guards computed away twice, at `Γ` and at `Γ₂`.
      | (refine ⟨?_, fun Γ₂ hs => ?_⟩ <;>
           (revert h
            simp only [infer]
            split <;> split <;> simp_all
            done))
      -- No fallback, for the reason the other three inductions have none: a new `infer`
      -- arm has to be looked at, not absorbed.

/-- **The sequence form** (L234), by list induction on top of `infer_env_mono` — the same
    composition the table lemmas use, and for the same reason: `inferSeq` is `infer`
    threaded along a list, so the theorem composes with itself. -/
theorem inferSeq_env_mono : ∀ {es : List Expr} {D : Decls} {Γ : Env} {top : Bool}
    {ctx : FrameCtx} {τ : Ty} {Γ' : Env} {D₀ : Decls}, asgnFreeAll es = true →
    inferSeq D Γ es top ctx = some (τ, Γ', D₀) →
    Γ' = Γ ∧ ∀ Γ₂, SubEnv Γ Γ₂ → inferSeq D Γ₂ es top ctx = some (τ, Γ₂, D₀)
  | [], D, Γ, top, ctx, τ, Γ', D₀, _, h => by
      simp only [inferSeq, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, fun Γ₂ _ => by simp [inferSeq]⟩
  | [e], D, Γ, top, ctx, τ, Γ', D₀, ha, h => by
      simp only [inferSeq] at h
      obtain ⟨rfl, hm⟩ := infer_env_mono D Γ e top ctx (by simpa [asgnFreeAll] using ha) _ _ _ h
      exact ⟨rfl, fun Γ₂ hs => by simp only [inferSeq]; exact hm Γ₂ hs⟩
  | e :: e₂ :: rest, D, Γ, top, ctx, τ, Γ', D₀, ha, h => by
      simp only [asgnFreeAll, Bool.and_eq_true] at ha
      simp only [inferSeq] at h
      cases he : infer D Γ e top ctx with
      | none => rw [he] at h; simp at h
      | some r =>
        obtain ⟨τe, Γ₁, D₁⟩ := r
        rw [he] at h
        obtain ⟨rfl, hme⟩ := infer_env_mono D Γ e top ctx ha.1 _ _ _ he
        obtain ⟨rfl, hmr⟩ := inferSeq_env_mono (by simpa [asgnFreeAll] using ha.2) h
        exact ⟨rfl, fun Γ₂ hs => by simp only [inferSeq, hme Γ₂ hs]; exact hmr Γ₂ hs⟩

/-- And the argument list's (L234). -/
theorem inferArgs_env_mono : ∀ {es : List Expr} {D : Decls} {Γ : Env} {top : Bool}
    {ctx : FrameCtx} {τs : List Ty} {Γ' : Env} {D₀ : Decls}, asgnFreeAll es = true →
    inferArgs D Γ es top ctx = some (τs, Γ', D₀) →
    Γ' = Γ ∧ ∀ Γ₂, SubEnv Γ Γ₂ → inferArgs D Γ₂ es top ctx = some (τs, Γ₂, D₀)
  | [], D, Γ, top, ctx, τs, Γ', D₀, _, h => by
      simp only [inferArgs, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, fun Γ₂ _ => by simp [inferArgs]⟩
  | e :: rest, D, Γ, top, ctx, τs, Γ', D₀, ha, h => by
      simp only [asgnFreeAll, Bool.and_eq_true] at ha
      simp only [inferArgs] at h
      cases he : infer D Γ e top ctx with
      | none => rw [he] at h; simp at h
      | some r =>
        obtain ⟨τe, Γ₁, D₁⟩ := r
        rw [he] at h
        obtain ⟨rfl, hme⟩ := infer_env_mono D Γ e top ctx ha.1 _ _ _ he
        dsimp only at h
        cases hr : inferArgs D₁ Γ₁ rest top ctx with
        | none => rw [hr] at h; simp at h
        | some r' =>
          obtain ⟨τr, Γ₂', D₂⟩ := r'
          rw [hr] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨rfl, hmr⟩ := inferArgs_env_mono (by simpa [asgnFreeAll] using ha.2) hr
          exact ⟨rfl, fun Γ₂ hs => by simp [inferArgs, hme Γ₂ hs, hmr Γ₂ hs]⟩

/-- And the array-element traversal's (L234). -/
theorem inferElems_env_mono : ∀ {es : List Expr} {D : Decls} {Γ : Env} {top : Bool}
    {ctx : FrameCtx} {τ : Ty} {Γ' : Env} {D₀ : Decls}, asgnFreeAll es = true →
    inferElems D Γ es top ctx = some (τ, Γ', D₀) →
    Γ' = Γ ∧ ∀ Γ₂, SubEnv Γ Γ₂ → inferElems D Γ₂ es top ctx = some (τ, Γ₂, D₀)
  | [], D, Γ, top, ctx, τ, Γ', D₀, _, h => by
      simp only [inferElems, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, fun Γ₂ _ => by simp [inferElems]⟩
  | e :: rest, D, Γ, top, ctx, τ, Γ', D₀, ha, h => by
      simp only [asgnFreeAll, Bool.and_eq_true] at ha
      cases e
      case splat oe =>
        cases oe with
        | none => exact absurd h (by simp [inferElems, infer])
        | some o =>
          simp only [inferElems] at h
          cases ho : infer D Γ o top ctx with
          | none => rw [ho] at h; exact absurd h (by simp)
          | some r =>
            obtain ⟨τo, Γ₁, D₁⟩ := r
            rw [ho] at h
            obtain ⟨rfl, hmo⟩ := infer_env_mono D Γ o top ctx (by simpa [asgnFree] using ha.1)
              _ _ _ ho
            cases τo with
            | cls nm =>
              by_cases hnm : nm = "Array"
              · subst hnm
                obtain ⟨rfl, hmr⟩ := inferElems_env_mono (by simpa [asgnFreeAll] using ha.2) h
                exact ⟨rfl, fun Γ₂ hs => by
                  simp only [inferElems, hmo Γ₂ hs]; exact hmr Γ₂ hs⟩
              · simp_all
            | _ => simp_all
      all_goals
        (simp only [inferElems] at h
         first
           | (cases he : infer D Γ _ top ctx with
              | none => rw [he] at h; exact absurd h (by simp)
              | some r =>
                obtain ⟨τe, Γ₁, D₁⟩ := r
                rw [he] at h
                obtain ⟨rfl, hme⟩ := infer_env_mono D Γ _ top ctx ha.1 _ _ _ he
                obtain ⟨rfl, hmr⟩ := inferElems_env_mono (by simpa [asgnFreeAll] using ha.2) h
                exact ⟨rfl, fun Γ₂ hs => by
                  simp only [inferElems, hme Γ₂ hs]; exact hmr Γ₂ hs⟩)
           | simp_all)

/-- And the `if` join's (L234), by cases on the `else` rather than by induction. -/
theorem inferIf_env_mono {D : Decls} {Γ : Env} {t : Expr} {els : Option Expr} {top : Bool}
    {ctx : FrameCtx} {τ : Ty} {Γ' : Env} {D₀ : Decls}
    (hat : asgnFree t = true) (hae : asgnFreeOpt els = true)
    (h : inferIf D Γ t els top ctx = some (τ, Γ', D₀)) :
    Γ' = Γ ∧ ∀ Γ₂, SubEnv Γ Γ₂ → inferIf D Γ₂ t els top ctx = some (τ, Γ₂, D₀) := by
  unfold inferIf at h
  cases els with
  | none =>
    cases ht : infer D Γ t top ctx with
    | none => rw [ht] at h; simp at h
    | some r =>
      obtain ⟨τt, Γt, Dt⟩ := r
      rw [ht] at h
      obtain ⟨rfl, hmt⟩ := infer_env_mono D Γ t top ctx hat _ _ _ ht
      dsimp only at h
      split at h
      · next hg =>
        simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
        obtain ⟨τj, hj, rfl, rfl, rfl⟩ := h
        refine ⟨rfl, fun Γ₂ hs => ?_⟩
        simp only [inferIf, hmt Γ₂ hs]
        split
        · simp [hj]
        · -- The guard that failed is the arm's own stability check; after the IH's `rfl`
          -- its environment half is trivial, so what is left is the table half — which is
          -- the guard the *original* run already passed.
          rename_i hbad
          exact absurd hg.2 (by simpa [subEnvB_refl] using hbad)
      · exact absurd h (by simp)
  | some e' =>
    dsimp only at h
    cases ht : infer D Γ t top ctx with
    | none => rw [ht] at h; simp at h
    | some r =>
      obtain ⟨τt, Γt, Dt⟩ := r
      cases he : infer D Γ e' top ctx with
      | none => rw [ht, he] at h; simp at h
      | some r' =>
        obtain ⟨τe, Γe, De⟩ := r'
        rw [ht, he] at h
        obtain ⟨rfl, hmt⟩ := infer_env_mono D Γ t top ctx hat _ _ _ ht
        obtain ⟨rfl, hme⟩ := infer_env_mono D _ e' top ctx (by simpa [asgnFreeOpt] using hae)
          _ _ _ he
        dsimp only at h
        split at h
        · next hg =>
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
          obtain ⟨τj, hj, rfl, rfl, rfl⟩ := h
          refine ⟨rfl, fun Γ₂ hs => ?_⟩
          simp only [inferIf, hmt Γ₂ hs, hme Γ₂ hs]
          split
          · simp [hj]
          · rename_i hbad
            exact absurd hg.2.2 (by simpa using hbad)
        · exact absurd h (by simp)

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
    exact ctxa.inLoop.isSome = true → topa = false → ∀ τ Γ' D₀,
      inferElems Da Γa esa topa ctxa = some (τ, Γ', D₀) → D₀ = Da
  | motive5 Da Γa esa topa ctxa =>
    exact ctxa.inLoop.isSome = true → topa = false → ∀ τs Γ' D₀,
      inferArgs Da Γa esa topa ctxa = some (τs, Γ', D₀) → D₀ = Da
  -- **The `if`-with-else arm**, explicit because the answer's table is the *then*
  -- branch's and the join's guard has to be split before either IH is usable.
  | case111 D Γ t top ctx e' τt Γt Dt τe Γe De hE hT hagree ih2 ih1 =>
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
      | (exfalso; revert h; simp +contextual [infer, inferIf, inferSeq, inferArgs, inferElems, htop]; done)
      | (simp_all only [infer, inferIf, inferSeq, inferArgs, inferElems, Option.some.injEq,
           Prod.mk.injEq, reduceCtorEq]; done)
      | (simp_all [infer, inferIf, inferSeq, inferArgs, inferElems, htop, hret]; done)
      | (rename_i ih1
         exact ih1 hret htop _ _ _ (by simpa [infer, inferIf, inferSeq, inferArgs, inferElems] using h))
      | (rename_i ih2 ih1
         first
           | exact ih1 hret htop _ _ _ (by simpa [infer, inferSeq, inferArgs, inferElems] using h)
           | exact ih2 hret htop _ _ _ (by simpa [infer, inferSeq, inferArgs, inferElems] using h))
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

/-- **L230's element traversal**, and it is `inferSeq_table_loop`'s proof with one more
    case: a splat element threads the table through its **operand**, which is one
    `infer_table_loop` at a different subexpression. -/
theorem inferElems_table_loop : ∀ {es : List Expr} {D : Decls} {Γ : Env} {top : Bool}
    {ctx : FrameCtx} {τ : Ty} {Γ' : Env} {D₀ : Decls}, ctx.inLoop.isSome = true → top = false →
    inferElems D Γ es top ctx = some (τ, Γ', D₀) → D₀ = D
  | [], D, Γ, top, ctx, τ, Γ', D₀, _, _, h => by
      simp only [inferElems, Option.some.injEq, Prod.mk.injEq] at h
      exact h.2.2.symm
  | e :: rest, D, Γ, top, ctx, τ, Γ', D₀, hret, htop, h => by
      cases e
      case splat oe =>
        cases oe with
        -- `.splat none` (an anonymous splat) has no `infer` arm, so it falls to
        -- `inferElems`' catch-all and is refused there.
        | none => exact absurd h (by simp [inferElems, infer])
        | some o =>
          simp only [inferElems] at h
          cases ho : infer D Γ o top ctx with
          | none => rw [ho] at h; exact absurd h (by simp)
          | some r =>
            obtain ⟨τo, Γ₁, D₁⟩ := r
            rw [ho] at h
            have hD : D₁ = D := infer_table_loop D Γ o top ctx hret htop _ _ _ ho
            subst hD
            cases τo with
            | cls nm =>
              by_cases hnm : nm = "Array"
              · subst hnm
                exact inferElems_table_loop hret htop h
              · simp_all
            | _ => simp_all
      all_goals
        (simp only [inferElems] at h
         cases he : infer D Γ _ top ctx with
         | none => rw [he] at h; simp at h
         | some r =>
           obtain ⟨τe, Γ₁, D₁⟩ := r
           rw [he] at h
           have hD : D₁ = D := infer_table_loop D Γ _ top ctx hret htop _ _ _ he
           subst hD
           exact inferElems_table_loop hret htop h)

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
      ∀ τ Γ' D₀, inferElems Da Γa esa topa ctxa = some (τ, Γ', D₀) →
        D₀ = Da ∧ inferElems F' Γa esa topa ctxa = some (τ, Γ', F')
  | motive5 Da Γa esa topa ctxa =>
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
  | case14 D Γ top ctx x rhs hib τr Γ₁ D₁ hrhs ih =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [defFree] at hdf
    obtain ⟨rfl, hm⟩ := ih F' hs hdf _ _ _ hrhs
    -- L252: the arm is under the block guard now, so the equation has to be reduced at
    -- the *same* branch before it can be inverted.
    simp only [infer, hib, hrhs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [infer, hib, hm]⟩
  -- **`@x = e`** (L191/L196). Two accepting arms since the write checks the table:
  -- the declared case, where the widening has to preserve the *conformance* too, and
  -- the undeclared one, where there is nothing to conform to. `SubDecls`' ivar half
  -- is an equality (as its constant half is), so both are the rhs's IH plus a rewrite.
  | case16 D Γ top ctx name rhs sc hsome τr Γ₁ D₁ hrhs σ hiv hsub ih =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [defFree] at hdf
    obtain ⟨rfl, hm⟩ := ih F' hs hdf _ _ _ hrhs
    simp only [infer, hsome, hrhs, hiv, hsub, if_true, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [infer, hsome, hm, hs.ivarTy_eq, hiv, hsub]⟩
  | case18 D Γ top ctx name rhs sc hsome τr Γ₁ D₁ hrhs hiv ih =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [defFree] at hdf
    obtain ⟨rfl, hm⟩ := ih F' hs hdf _ _ _ hrhs
    simp only [infer, hsome, hrhs, hiv, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [infer, hsome, hm, hs.ivarTy_eq, hiv]⟩
  -- **`@x`** (L196). The answer comes out of the table, so like `case33`'s constant
  -- read this case *uses* `SubDecls` — through its ivar half, an equality.
  | case21 D Γ top ctx x sc hsome σ hiv =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [infer, hsome, hiv, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [infer, hsome, hs.ivarTy_eq, hiv]⟩
  -- **The unary send**, and the only case where `SubDecls` is *used* rather than
  -- carried: the signature has to be readable at the bigger table, which is what
  -- the relation was defined to say.
  | case24 D Γ top ctx recv mname arg args τr Γ₁ D₁ hrecv τs Γ₂ D₂ hargs ps τret
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
  | case29 D Γ top ctx recv mname τr Γ₁ D₁ hrecv τret hsig ihR =>
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
  | case32 D Γ top ctx mname c hsome τret hsig =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [infer, hsome, hsig, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [infer, hsome, SubDecls.sigOf_eq hs hsig]⟩
  -- **The unary written receiverless call** (L171). One subexpression and the
  -- signature read at the table it leaves — the explicit unary send's case with
  -- the receiver supplied by the context instead of by an expression.
  | case35 D Γ top ctx mname arg args c hsome τs Γ₁ D₁ hargs ps τret hsig hsub ih =>
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
  | case40 D Γ top ctx n τc hre =>
    intro F' hs hdf τ Γ' D₀ h
    rw [show infer D Γ (.const n) top ctx = some (τc, Γ, D) from by
      simp only [infer, hre]] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp only [infer, hs.constTy_eq n, hre]⟩
  -- **`super()`** (L212). The answer comes out of the `supers` table, so the case
  -- *uses* `SubDecls` — through its fifth half, which is an equality (`superDecl_eq`).
  -- Same shape as `.const`'s (case39): no IH, one table read, two guards to recompute.
  | case72 D Γ top ctx mn hmeth hne dd hrow hemp =>
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
  | case77 D Γ top ctx arg args mn hmeth hne τs Γ₂ D₂ hargs dd hrow hsub ih =>
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
  | case83 D Γ top ctx mn ps hpar hmeth hne dd hrow hsub =>
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
  | case42 D Γ top ctx es τ0 Γ₁ D₁ hs ih =>
    intro F' hsub hdf τ Γ' D₀ h
    simp only [defFree] at hdf
    obtain ⟨rfl, hm⟩ := ih F' hsub hdf _ _ _ hs
    simp only [infer, hs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [infer, hm]⟩
  -- `seq` is `inferSeq` definitionally, so this case is the third motive verbatim.
  | case52 D Γ top ctx es ih =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [defFree] at hdf
    simp only [infer] at h ⊢
    exact ih F' hs hdf _ _ _ h
  | case53 D Γ top ctx c t els τc Γ₁ D₁ hc ihC ihI =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [defFree_if, Bool.and_eq_true] at hdf
    obtain ⟨⟨hc1, ht1⟩, he1⟩ := hdf
    obtain ⟨rfl, hmC⟩ := ihC F' hs hc1 _ _ _ hc
    simp only [infer, hc] at h
    obtain ⟨rfl, hmI⟩ := ihI F' hs (by simp only [ht1, Bool.true_and]; exact he1) _ _ _ h
    exact ⟨rfl, by simp [infer, hmC, hmI]⟩
  -- **The loop**, where the stability side conditions do the work: both come back
  -- as `rfl`s, so the table at `F'` is stable for the same reason it was at `F`.
  | case55 D Γ top ctx c body τc Γc Dc hc hstc τb Γb Db hbody hstb ihC ihB =>
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
  | case111 D Γ t top ctx e' τt Γt Dt τe Γe De hE hT hagree ihT ihE =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [Bool.and_eq_true] at hdf
    obtain ⟨rfl, hmT⟩ := ihT F' hs hdf.1 _ _ _ hT
    obtain ⟨rfl, hmE⟩ := ihE F' hs hdf.2 _ _ _ hE
    obtain ⟨hΓ, hΓ2, -⟩ := hagree
    simp only [inferIf, hT, hE] at h
    rw [if_pos (by exact ⟨hΓ, hΓ2, trivial⟩)] at h
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨τj, hjoin, rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [inferIf, hmT, hmE, hjoin, hΓ, hΓ2]⟩
  | case114 D Γ t top ctx τt Γt Dt hT hcond ihT =>
    intro F' hs hdf τ Γ' D₀ h
    obtain ⟨hsub1, rfl⟩ := hcond
    obtain ⟨_, hmT⟩ := ihT F' hs (by simp_all) _ _ _ hT
    simp only [inferIf, hT] at h
    rw [if_pos (by exact ⟨hsub1, trivial⟩)] at h
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨τj, hjoin, rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [inferIf, hmT, hjoin, hsub1]⟩
  -- `inferSeq`'s three arms, mirroring `evalExpr`'s split on `.seq`.
  | case117 D Γ top ctx =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [inferSeq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [inferSeq]⟩
  | case118 D Γ top ctx e ih =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [defFreeAll, Bool.and_eq_true] at hdf
    simp only [inferSeq] at h ⊢
    exact ih F' hs (by simp_all [defFreeAll]) _ _ _ h
  | case119 D Γ top ctx e rest hne τe Γ₁ D₁ he ihE ihR =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [defFreeAll, Bool.and_eq_true] at hdf
    obtain ⟨rfl, hmE⟩ := ihE F' hs (by simp_all [defFreeAll]) _ _ _ he
    cases rest with
    | nil => exact absurd rfl hne
    | cons e₂ r₂ =>
      simp only [inferSeq, he] at h
      obtain ⟨rfl, hmR⟩ := ihR F' hs (by simp_all [defFreeAll]) _ _ _ h
      exact ⟨rfl, by simp [inferSeq, hmE, hmR]⟩
  -- **L230's `inferElems`** — the array-element traversal, three accepting arms. The
  -- splat arm is the non-splat one with the operand in place of the element and its type
  -- pinned to `Array` by the pattern, which is why it has one binder fewer.
  | case121 D Γ top ctx =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [inferElems, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [inferElems]⟩
  | case122 D Γ top ctx rest o Γ₁ D₁ ho ihO ihR =>
    intro F' hs hdf τ Γ' D₀ h
    obtain ⟨rfl, hmO⟩ := ihO F' hs (by simp_all [defFreeAll, defFree]) _ _ _ ho
    simp only [inferElems, ho] at h
    obtain ⟨rfl, hmR⟩ := ihR F' hs (by simp_all [defFreeAll, defFree]) _ _ _ h
    exact ⟨rfl, by simp [inferElems, hmO, hmR]⟩
  | case124 D Γ top ctx ee rest hne τe Γ₁ D₁ he ihE ihR =>
    intro F' hs hdf τ Γ' D₀ h
    obtain ⟨rfl, hmE⟩ := ihE F' hs (by simp_all [defFreeAll, defFree]) _ _ _ he
    simp only [inferElems, he] at h
    obtain ⟨rfl, hmR⟩ := ihR F' hs (by simp_all [defFreeAll, defFree]) _ _ _ h
    exact ⟨rfl, by simp [inferElems, hmE, hmR]⟩
  -- **`inferArgs`' three arms** (L175), mirroring `startArgs`' loop. The `[]` arm
  -- is a `rfl`; the recursive arm is the only place two IHs of *different* motives
  -- meet, and the reason it needs both is that an argument may itself be a send.
  -- **`inferArgs`' two accepting arms** (L175), mirroring `startArgs`' loop. The
  -- `[]` arm is a `rfl`; the recursive arm is the only place two IHs of *different*
  -- motives meet, and the reason it needs both is that an argument may itself be a
  -- send.
  | case126 D Γ top ctx =>
    intro F' hs hdf τs Γ' D₀ h
    simp only [inferArgs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [inferArgs]⟩
  | case127 D Γ top ctx e rest τe Γ₁ D₁ he τs Γ₂ D₂ hrest ihE ihR =>
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
  | case88 D Γ top ctx x σ hgt hpg =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [infer, hpg, hgt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp only [infer, hpg, hs.globalTy_eq, hgt]⟩
  -- **And the write** (case89/case90 — two cases, because the equation compiler splits
  -- the guard pair and the right-hand side's own `match` separately). Same shape with
  -- `case13`'s IH step in the middle.
  | case90 D Γ top ctx x rhs hpg τr Γr Dr hq0 σ hgt hsub ih1 =>
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
  | case91 D Γ top ctx x rhs hpg τr Γr Dr hq0 σ hgt hsub _ih1 =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [infer, hpg, hq0, hgt, if_neg hsub] at h
    exact absurd h (by simp)
  | case92 D Γ top ctx x rhs hpg τr Γr Dr hq0 hgt _ih1 =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [infer, hpg, hq0, hgt] at h
    exact absurd h (by simp)
  | _ =>
    intro F' hs hdf τ Γ' D₀ h
    first
      | (exfalso; revert h; simp +contextual [infer, inferIf, inferSeq, inferArgs, inferElems]; done)
      | (exfalso; simp_all only [infer, inferIf, inferSeq, inferArgs, inferElems, reduceCtorEq]; done)
      | (exfalso; simp_all [infer, inferIf, inferSeq, inferArgs, inferElems, defFree, defFreeAll]; done)
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
      -- transport is three `split`s and a recomputation. An IH-free case, like `case111`.
      | (rename_i _ hil hse
         simp only [infer, hil, hse, if_true, reduceIte, Option.some.injEq,
           Prod.mk.injEq] at h
         obtain ⟨rfl, rfl, rfl⟩ := h
         exact ⟨rfl, by simp only [infer, hil, hse, if_true, reduceIte]⟩)
      -- **L236: the one-armed `if`'s refusing branch** (case103), explicit because its
      -- guard is now `subEnvB` rather than an equality — nothing `simp` can compute, so
      -- the case is the guard split and the two refutations it leaves.
      | (rename_i hinf hbad _
         simp only [inferIf, hinf] at h
         split at h
         · exact absurd (by assumption) hbad
         · exact absurd h (by simp))
      -- **L257's block send**, five alternatives and one of them substantive: the
      -- receiver's IH gives `D₁ = D` and the answer at `F'`, `SubDecls.blockSend_eq`
      -- moves the row, and the body's IH moves the body — whose `defFree` this commit
      -- had to *add* to the `.send` arm, the ninth walk into that trap.
      | (rename_i hrecv _ _ _ _ hbs _ _ _ hbody hif ihR ihB
         simp only [defFree, Bool.and_eq_true] at hdf
         obtain ⟨rfl, hmR⟩ := ihR F' hs hdf.1.1 _ _ _ hrecv
         obtain ⟨rfl, hmB⟩ := ihB F' hs hdf.2 _ _ _ hbody
         simp only [infer, hrecv, hbs, hbody, hif, if_true, Option.some.injEq,
           Prod.mk.injEq] at h
         obtain ⟨rfl, rfl, rfl⟩ := h
         exact ⟨rfl, by
           simp only [infer, hmR, hs.blockSend_eq hbs, hmB, hif, if_true]
           simp⟩)
      -- **L259's arity-`n` block send**, and the one difference from the arm above is
      -- the argument traversal's IH between the receiver's and the body's.
      | (rename_i hrecv _ _ _ hargs _ _ _ _ _ hbs _ _ _ hbody hif ihR ihA ihB
         simp only [defFree, Bool.and_eq_true] at hdf
         obtain ⟨rfl, hmR⟩ := ihR F' hs hdf.1.1 _ _ _ hrecv
         obtain ⟨rfl, hmA⟩ := ihA F' hs hdf.1.2 _ _ _ hargs
         obtain ⟨rfl, hmB⟩ := ihB F' hs hdf.2 _ _ _ hbody
         obtain ⟨hsts, hsub, hd32, hd21, hd1, hse, hib⟩ := hif
         -- The two table equalities are *rewritten into* the row read and the body,
         -- not substituted: `subst` cannot fire here (the receiver's IH has already
         -- moved `D₁`), and left as plain facts `simp` would use `D₂ = D₁` to rewrite
         -- the goal out from under `hbs`.
         simp only [hd21] at hbs hbody hse hd32
         simp only [infer, hrecv, hargs, hbs, hbody, hsts, hsub, hse, hib, hd32, hd21, hd1,
           and_true, true_and, and_self, if_true, Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl, rfl⟩ := h
         refine ⟨rfl, ?_⟩
         simp only [infer, hmR, hmA]
         rw [SubDecls.blockSendA_eq hs hbs]
         simp only [hmB]
         simp [hsts, hsub, hse, hib, hd1])
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
