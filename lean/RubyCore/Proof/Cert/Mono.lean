import RubyCore.Cert.Validate

/-!
# `chk`'s structural laws — rung 1 of the infer-free soundness development

**Why this file exists, and what it replaces.** `validate` no longer calls `infer`
(V9–V16); the *soundness argument* still did, through `CtlOk`, whose eval clause is
literally `infer F Γ e … = some …` (`Proof/Static/Konts.lean`). A bridge from `chk`
back to `infer` was built and then deleted, because it is the wrong shape: it makes
the headline theorem depend on the function the whole pivot exists to retire, so
`infer` cannot be deprecated while the bridge holds the theorem up.

So the invariant gets restated over `chk`, and this file is the foundation that
restatement needs.

## The measurement that priced the route (V17)

`Proof/Static/Mono.lean` proves twenty structural laws about `infer` — table-return,
environment-monotonicity, loop-stability, table-monotonicity, for each of the five
mutually recursive functions. Every one of them is proved by

```lean
induction D, Γ, e, top, ctx using infer.induct with | motive2 … | motive5 …
```

the **well-founded functional induction principle** of that mutual block. `chk` has
no such principle and cannot: it is structurally recursive on *fuel*, and its list
helpers are separate top-level functions taking the recursive call as a parameter
(that separation is what makes both structural, `Cert/Check.lean` §1). So each law
has to be **restated in the fuel shape and re-proved** — induction on `n`, with one
lemma per list helper taking the fuel-level hypothesis as an argument. It is not a
port.

The cost, stated so the ladder is priced rather than aspirational:

| file | lines | what it is | status |
|---|---|---|---|
| `Proof/Cert/Mono.lean` | this | the structural laws, in the fuel shape | **rung 1, in progress** |
| `Proof/Cert/Konts.lean` | ~2200 to match | `KontOk`'s 12 constructors carry `infer`/`inferArgs`/`inferElems`/`inferSeq`/`inferIf` premises; each becomes a `chk` premise | not started |
| `Proof/Cert/Locals.lean` | ~2000 to match | `FramesOk`/`StackCtx` and the frame laws | not started |
| `Proof/Cert/Preservation.lean` | ~2700 to match | `step_ok`, 73 `simp only [infer] at hinf` sites | not started |

and that is the cost to reach **today's** coverage. `chk` has fifteen heads `infer`
does not, so the per-head work after that is additional — which is the point, and is
why the frontier is a `Bool` (`Cert/Check.lean` §5) rather than a promise.

## What this file does *not* need, and it is worth knowing

**Fuel monotonicity is not required.** The first draft of the plan budgeted for
`chk c n … = some r → chk c (n+1) … = some r`, on the grounds that a step has to
produce the successor's witness from the current one's. It does not: state the
invariant's clause as `∃ n, chk c n D Γ e top ctx = some …` and every arm of `chk`
hands its *children* a witness at `n` directly. A loop re-enters the same subterm at
the same fuel; a method body is a subterm of the program and so is covered by the
program's own bound. So the existential absorbs the whole question, and the ~45-case
callback-monotonicity argument is not owed. Recorded because it was budgeted.
-/

namespace RubyCore
namespace Proof
namespace Cert

open RubyCore.Types
open RubyCore.Cert

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-! ## 1. The table-return law

`infer_table_ret`'s statement, in the fuel shape:

> inside a method body — `ctx.ret.isSome`, `top = false` — nothing grows the table.

It is the smallest complete family and it is the one every later law leans on, because
it is what lets a rule conclude `D' = D` without inspecting the subterm. The two arms
that *can* grow the table are `.def'` (which promotes a row) and `.class'` (which
threads its body's extension out), and each is refused under exactly these
hypotheses: `.def'`'s promotion guard requires `ctx.ret.isNone`, and `.class'`
requires `top`.

The list helpers get their own statements, each taking the fuel-level fact as a
hypothesis — the shape that replaces `infer.induct`'s `motive3`…`motive5`. -/

/-- The fuel-level hypothesis, named so the four statements below read as one law. -/
def TableRet (c : Cert) (n : Nat) : Prop :=
  ∀ D Γ e top ctx τ Γ' D₀, ctx.ret.isSome = true → top = false →
    chk c n D Γ e top ctx = some (τ, Γ', D₀) → D₀ = D

theorem tableRet_zero (c : Cert) : TableRet c 0 := by
  intro D Γ e top ctx τ Γ' D₀ _ _ h
  simp [chk] at h

section
variable {c : Cert} {n : Nat}

theorem chkSeq_table_ret (ih : TableRet c n) (top : Bool) (ctx : FrameCtx)
    (hr : ctx.ret.isSome = true) (ht : top = false) :
    ∀ (es : List Expr) (D : Decls) (Γ : Env) (τ : Ty) (Γ' : Env) (D₀ : Decls),
      chkSeq (chk c n) top ctx D Γ es = some (τ, Γ', D₀) → D₀ = D
  | [], D, Γ, τ, Γ', D₀, h => by
    simp only [chkSeq, Option.some.injEq, Prod.mk.injEq] at h
    exact h.2.2.symm
  | [e], D, Γ, τ, Γ', D₀, h => ih D Γ e top ctx τ Γ' D₀ hr ht h
  | e :: e2 :: rest, D, Γ, τ, Γ', D₀, h => by
    simp only [chkSeq] at h
    cases he : chk c n D Γ e top ctx with
    | none => rw [he] at h; exact absurd h (by simp)
    | some v =>
      obtain ⟨_, Γ₁, D₁⟩ := v
      rw [he] at h
      have h1 : D₁ = D := ih D Γ e top ctx _ Γ₁ D₁ hr ht he
      subst h1
      exact chkSeq_table_ret ih top ctx hr ht (e2 :: rest) D₁ Γ₁ τ Γ' D₀ h

theorem chkArgs_table_ret (ih : TableRet c n) (top : Bool) (ctx : FrameCtx)
    (hr : ctx.ret.isSome = true) (ht : top = false) :
    ∀ (es : List Expr) (D : Decls) (Γ : Env) (τs : List Ty) (Γ' : Env) (D₀ : Decls),
      chkArgs (chk c n) top ctx D Γ es = some (τs, Γ', D₀) → D₀ = D
  | [], D, Γ, τs, Γ', D₀, h => by
    simp only [chkArgs, Option.some.injEq, Prod.mk.injEq] at h
    exact h.2.2.symm
  | e :: rest, D, Γ, τs, Γ', D₀, h => by
    simp only [chkArgs] at h
    cases he : chk c n D Γ e top ctx with
    | none => rw [he] at h; exact absurd h (by simp)
    | some v =>
      obtain ⟨_, Γ₁, D₁⟩ := v
      rw [he] at h
      dsimp only at h
      have h1 : D₁ = D := ih D Γ e top ctx _ Γ₁ D₁ hr ht he
      subst h1
      cases hrest : chkArgs (chk c n) top ctx D₁ Γ₁ rest with
      | none => rw [hrest] at h; exact absurd h (by simp)
      | some w =>
        obtain ⟨_, Γ₂, D₂⟩ := w
        rw [hrest] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        have h2 : D₂ = D₁ :=
          chkArgs_table_ret ih top ctx hr ht rest D₁ Γ₁ _ Γ₂ D₂ hrest
        rw [← h.2.2]; exact h2

theorem chkElems_table_ret (ih : TableRet c n) (top : Bool) (ctx : FrameCtx)
    (hr : ctx.ret.isSome = true) (ht : top = false) :
    ∀ (es : List Expr) (D : Decls) (Γ : Env) (τ : Ty) (Γ' : Env) (D₀ : Decls),
      chkElems (chk c n) top ctx D Γ es = some (τ, Γ', D₀) → D₀ = D
  | [], D, Γ, τ, Γ', D₀, h => by
    simp only [chkElems, Option.some.injEq, Prod.mk.injEq] at h
    exact h.2.2.symm
  | e :: rest, D, Γ, τ, Γ', D₀, h => by
    match e with
    | .splat (some o) =>
      simp only [chkElems] at h
      cases ho : chk c n D Γ o top ctx with
      | none => rw [ho] at h; exact absurd h (by simp)
      | some v =>
        obtain ⟨τo, Γ₁, D₁⟩ := v
        rw [ho] at h
        have h1 : D₁ = D := ih D Γ o top ctx _ Γ₁ D₁ hr ht ho
        subst h1
        match τo with
        | .cls sname =>
          by_cases hs : sname = "Array"
          · subst hs
            exact chkElems_table_ret ih top ctx hr ht rest D₁ Γ₁ τ Γ' D₀ h
          · exact absurd h (by simp [hs])
        | .int | .bool | .nilT | .sym | .any | .float | .clsOf _ | .nilable _
        | .arrayOf _ => exact absurd h (by simp)
    | .splat none =>
      simp only [chkElems] at h
      cases ho : chk c n D Γ (Expr.splat none) top ctx with
      | none => rw [ho] at h; exact absurd h (by simp)
      | some v =>
        obtain ⟨_, Γ₁, D₁⟩ := v
        rw [ho] at h
        have h1 : D₁ = D := ih D Γ _ top ctx _ Γ₁ D₁ hr ht ho
        subst h1
        exact chkElems_table_ret ih top ctx hr ht rest D₁ Γ₁ τ Γ' D₀ h
    | .int _ | .flt _ | .str _ | .sym _ | .tru | .fls | .nil | .self' | .var _ _
    | .vasgn _ _ _ | .const _ | .casgn _ _ | .cpath _ _ | .cpathAsgn _ _ _
    | .send _ _ _ _ | .vcall _ | .kwargs _ | .fwd | .block _ _ _ | .yield' _
    | .blockpass _ | .if' _ _ _ | .while' _ _ | .dowhile _ _ | .for' _ _ _
    | .def' _ _ _ | .array _ | .hash _ | .ret _ | .brk _ | .nxt _ | .retry' | .redo'
    | .class' _ _ _ | .module' _ _ | .scopedClass _ _ _ | .scopedModule _ _ _
    | .sclass _ _ | .defs _ _ _ _ | .begin' _ _ _ _ | .super' _ _ | .zsuper _
    | .undef _ | .alias' _ _ | .defined _ | .seq _ =>
      simp only [chkElems] at h
      cases ho : chk c n D Γ _ top ctx with
      | none => rw [ho] at h; exact absurd h (by simp)
      | some v =>
        obtain ⟨_, Γ₁, D₁⟩ := v
        rw [ho] at h
        have h1 : D₁ = D := ih D Γ _ top ctx _ Γ₁ D₁ hr ht ho
        subst h1
        exact chkElems_table_ret ih top ctx hr ht rest D₁ Γ₁ τ Γ' D₀ h

end

end Cert
end Proof
end RubyCore
