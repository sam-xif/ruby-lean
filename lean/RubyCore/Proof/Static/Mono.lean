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
  -- **The unary send**, and the only case where `SubDecls` is *used* rather than
  -- carried: the signature has to be readable at the bigger table, which is what
  -- the relation was defined to say.
  | case16 D Γ top ctx recv mname arg hns τr Γ₁ D₁ hrecv Γ₂ D₂ τp τret hsig harg ihR ihA =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [defFree, defFreeAll, Bool.and_eq_true] at hdf
    obtain ⟨rfl, hmR⟩ := ihR F' hs (by simp_all [defFree, defFreeAll]) _ _ _ hrecv
    obtain ⟨rfl, hmA⟩ := ihA F' hs (by simp_all [defFree, defFreeAll]) _ _ _ harg
    simp only [infer, hns, if_false, Bool.false_eq_true, hrecv, harg, hsig,
      Option.some.injEq, Prod.mk.injEq, if_pos rfl] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [infer, hns, hmR, hmA, SubDecls.sigOf_eq hs hsig]⟩
  -- **The zero-argument send.** Same shape, one fewer subexpression.
  | case22 D Γ top ctx recv mname hns τr Γ₁ D₁ hrecv τret hsig ihR =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [defFree, defFreeAll, Bool.and_eq_true] at hdf
    obtain ⟨rfl, hmR⟩ := ihR F' hs (by simp_all [defFree, defFreeAll]) _ _ _ hrecv
    simp only [infer, hns, if_false, Bool.false_eq_true, hrecv, hsig,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [infer, hns, hmR, SubDecls.sigOf_eq hs hsig]⟩
  -- **The written receiverless call** (L170), `foo()`. Identical to `vcall`'s
  -- case — same receiver from the context, same `SubDecls.sigOf_eq` — which is
  -- the monotonicity half of the claim that the two rules differ only in a
  -- `SendSite`.
  | case25 D Γ top ctx mname c hsome τret hsig =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [infer, hsome, hsig, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [infer, hsome, SubDecls.sigOf_eq hs hsig]⟩
  -- **The unary written receiverless call** (L171). One subexpression and the
  -- signature read at the table it leaves — the explicit unary send's case with
  -- the receiver supplied by the context instead of by an expression.
  | case28 D Γ top ctx mname arg c hsome Γ₁ D₁ τp τret hsig harg ih =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [defFree, defFreeAll, Bool.and_eq_true] at hdf
    obtain ⟨rfl, hmA⟩ := ih F' hs (by simp_all [defFree, defFreeAll]) _ _ _ harg
    simp only [infer, hsome, harg, hsig, Option.some.injEq, Prod.mk.injEq,
      if_pos rfl] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [infer, hsome, hmA, SubDecls.sigOf_eq hs hsig]⟩
  -- `seq` is `inferSeq` definitionally, so this case is the third motive verbatim.
  | case41 D Γ top ctx es ih =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [defFree] at hdf
    simp only [infer] at h ⊢
    exact ih F' hs hdf _ _ _ h
  | case42 D Γ top ctx c t els τc Γ₁ D₁ hc ihC ihI =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [defFree_if, Bool.and_eq_true] at hdf
    obtain ⟨⟨hc1, ht1⟩, he1⟩ := hdf
    obtain ⟨rfl, hmC⟩ := ihC F' hs hc1 _ _ _ hc
    simp only [infer, hc] at h
    obtain ⟨rfl, hmI⟩ := ihI F' hs (by simp only [ht1, Bool.true_and]; exact he1) _ _ _ h
    exact ⟨rfl, by simp [infer, hmC, hmI]⟩
  -- **The loop**, where the stability side conditions do the work: both come back
  -- as `rfl`s, so the table at `F'` is stable for the same reason it was at `F`.
  | case44 D Γ top ctx c body τc Γc Dc hc hstc τb Γb Db hbody hstb ihC ihB =>
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
  | case50 D Γ t top ctx e' τt Γt Dt τe Γe De hE hT hagree ihT ihE =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [Bool.and_eq_true] at hdf
    obtain ⟨rfl, hmT⟩ := ihT F' hs hdf.1 _ _ _ hT
    obtain ⟨rfl, hmE⟩ := ihE F' hs hdf.2 _ _ _ hE
    obtain ⟨hτ, hΓ, -⟩ := hagree
    subst hτ; subst hΓ
    simp only [inferIf, hT, hE] at h
    rw [if_pos (by simp)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [inferIf, hmT, hmE]⟩
  | case53 D Γ t top ctx τt Γt Dt hT hcond ihT =>
    intro F' hs hdf τ Γ' D₀ h
    obtain ⟨rfl, rfl, rfl⟩ := hcond
    obtain ⟨_, hmT⟩ := ihT F' hs (by simp_all) _ _ _ hT
    simp only [inferIf, hT, and_self, if_pos, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [inferIf, hmT]⟩
  -- `inferSeq`'s three arms, mirroring `evalExpr`'s split on `.seq`.
  | case56 D Γ top ctx =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [inferSeq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [inferSeq]⟩
  | case57 D Γ top ctx e ih =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [defFreeAll, Bool.and_eq_true] at hdf
    simp only [inferSeq] at h ⊢
    exact ih F' hs (by simp_all [defFreeAll]) _ _ _ h
  | case58 D Γ top ctx e rest hne τe Γ₁ D₁ he ihE ihR =>
    intro F' hs hdf τ Γ' D₀ h
    simp only [defFreeAll, Bool.and_eq_true] at hdf
    obtain ⟨rfl, hmE⟩ := ihE F' hs (by simp_all [defFreeAll]) _ _ _ he
    cases rest with
    | nil => exact absurd rfl hne
    | cons e₂ r₂ =>
      simp only [inferSeq, he] at h
      obtain ⟨rfl, hmR⟩ := ihR F' hs (by simp_all [defFreeAll]) _ _ _ h
      exact ⟨rfl, by simp [inferSeq, hmE, hmR]⟩
  | _ =>
    intro F' hs hdf τ Γ' D₀ h
    first
      | (exfalso; revert h; simp +contextual [infer, inferIf, inferSeq]; done)
      | (exfalso; simp_all only [infer, inferIf, inferSeq, reduceCtorEq]; done)
      | (exfalso; simp_all [infer, inferIf, inferSeq, defFree, defFreeAll]; done)
      -- The `self`-receiver guard's negative branch, and the arms under it: `infer`
      -- answers `none` outright, so the hypothesis is refuted by computing the
      -- guard rather than by anything about types (F1b.11).
      | (exfalso; revert h; simp only [infer]; split <;> simp_all; done)
      | (simp only [infer, Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl, rfl⟩ := h
         exact ⟨rfl, by simp [infer]⟩)
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
