import Denote.Sem.Invariant

/-!
# `Denote/Proto/Safety.lean` — the inductive-invariant machinery, end to end, on a fragment

**Purpose: confidence, not coverage.** `Denote/Sem/Invariant.lean` proves the *reduction*
(two obligations imply no type-stuck run) and writes the invariant's three components down as
definitions, but it discharges none of them, so nothing there tells you whether the design
actually closes. This file closes it — `init`, `preserved`, `noBadStep`, safety, and two
worked programs — on a four-expression fragment with two continuation frames.

If the design were wrong, it would be wrong here first.

## What is in the fragment, and why each piece is there

| expression | why |
|---|---|
| `.int n` | a leaf that produces a value |
| `.var .lvar x` | the only place the *certificate* is spent to learn a value's type (from `EnvOk`) |
| `.vasgn .lvar x e` | pushes a frame, so the continuation is non-trivial and nests |
| `.brk none` | produces an **escape**, so the two-clause shape is exercised rather than assumed |

Konts: `[]` and `.asgnK .lvar x`. Two frames, both clauses each — the value clause writes and
passes the value on, the escape clause pops and passes the jump on.

`.brk` earns its place twice over. It is the witness in
`Denote/Sem/NoProgress.lean` that `SemJudge` has no progress content, and here it is the
expression whose *whole* content lives in the escape clause: `PJudge.brk` types it at **any**
`τ` (it never returns), so if the invariant had only a value clause this fragment would be
certified with nothing checked. It is checked: the escape is a `brkJ`, `unwind []` answers
`.stuck`, and `.stuck` is not type-stuck.

## Four departures from `Denote/Sem/Invariant.lean`, stated because they are the honest bits

(There used to be a fifth, unstated and unintended: every theorem from `pInv_init` down fixed
the *incoming environment* to `[]`. Nothing needed it — see `pInv_init` — and fixing `Γ` is
what made the adequacy theorem useless for the one job an adequacy theorem has, since a
sub-derivation lives at a non-empty environment. Now universally quantified; §7 of
`Checker.lean` exhibits a non-empty witness.)

1. **`SemJudge` is not edited in place; `PSemJudge` is a parallel definition.** Changing the
   real one breaks the 48 discharged rungs and the build goes red, which would defeat a
   prototype whose purpose is confidence. The migration is §6's business.
2. **`CatchFree` is kept.** Nothing in the fragment can produce a `catchK`, so
   `PKontOk`-typed continuations are `CatchFree` by construction (`pkontOk_catchFree`) and the
   protocol index is not needed *here*. It is needed in general — that is
   `Denote/Sem/AnswerCatch.lean`'s §`CatchFree` is the degenerate case of a protocol, and the
   reason this prototype cannot be scaled by adding frames alone.
3. **The escape arm of `PInv` carries no `StateOk`.** Nothing in the fragment reads the store
   after a jump is in flight (the frames pass it through and `unwind []` ends the run), so the
   conformance component would be dead weight. A loop's `nxtJ` *does* read it — that is
   `WhileAnswer.lean`'s `AnswerOkAt` — so this simplification is a fragment property and does
   not generalise.
4. **`κ` is fixed to `ctx0`.** The fragment declares nothing, so the context never grows.

## The two findings the prototype produced

**1. `PSemJudge` is a corollary of the invariant, not an input to it.** The answer-typed
semantic judgment is derivable *from* the invariant (§9): what `preserved` consumes is the
**syntactic** `PJudge` plus `PKontOk`, and the semantic judgment is the output. Worth knowing
before anyone restates the real `SemJudge`'s 83 obligations — the restatement is the right
*statement*, and it is not the proof device.

**2. …but only because the continuation typing is indexed by the program's own type, and that
was not in the plan.** The first `PKontOk` here had `nil : PKontOk [] Γ τ` — the empty
continuation accepts anything — and with it the invariant proves **safety while proving
nothing about types**, because `PInv`'s `∃ τ` forgets which type the certificate claimed.
Recovering the value clause forced `nil` to pin the program's type (`PKontOk τa [] Γ τa`).
That is Wright--Felleisen's context typing `E : τ ⇒ τ_ans`, and `τa` is the answer type in
Danvy--Filinski's *original* sense. So "answer type" turns up twice in this design — at the
run level (`Answer`, what a sub-computation hands back) and at the type level (`τa`, what the
whole program will hand back) — and the second one, which none of the design discussion
mentioned, is what makes the judgment derivable rather than merely true.
-/

set_option autoImplicit false

namespace Ratchet.Denote.Proto

open RubyCore Ratchet Ratchet.Denote

/-! ## §1 The certificate language

A four-rule judgment over `Ratchet.Expr`, standing in for `Judge`'s 83. The three
`vasgn` side conditions are `Judge.vasgn`'s own (`capStale`/`capStaleCtx`/`isAliasTy`) and are
here for the same reason: `StateOk_setLocal` wants them. -/

/-- The environment a write leaves behind — exactly `StateOk_setLocal`'s conclusion, so the
certificate and the conformance lemma agree by construction rather than by a rewrite. -/
def envAfter (Γ : Env) (x : String) (σ : Ty) : Env :=
  envSet (killClosOver (killAliasesTo Γ x) x σ) x σ

inductive PJudge : Env → Ratchet.Expr → Ty → Env → Prop
  | intLit {Γ : Env} {n : Int} : PJudge Γ (.int n) .int Γ
  | var {Γ : Env} {x : String} {τ : Ty} :
      envGet? Γ x = some τ → isAliasTy τ = false → PJudge Γ (.var .lvar x) τ Γ
  | vasgn {Γ Γ₁ : Env} {x : String} {e : Ratchet.Expr} {σ : Ty} :
      PJudge Γ e σ Γ₁ → capStale x σ σ = false → capStaleCtx x σ Ratchet.ctx0 = false →
      isAliasTy σ = false → PJudge Γ (.vasgn .lvar x e) σ (envAfter Γ₁ x σ)
  /-- `break` never returns, so it is typed at **any** `τ`. Every bit of its content is in the
      escape clause — which is the point of including it. -/
  | brk {Γ : Env} {τ : Ty} : PJudge Γ (.brk none) τ Γ

/-! ## §2 The answer-typed semantic judgment

The shape the design calls for: one obligation over `Answer`, with a clause per arm. The
`esc` clause is where stuck-freedom lives, and `AnsOk`'s `.raiseJ` arm is `typeStuck`'s own
predicate — which is exact, not an approximation: `StepResult.uncaught` is constructed at
**one** site in the whole interpreter (`Interp/Kont.lean:341`, `unwind`'s `[]` arm on
`raiseJ`), so every type-stuck outcome is an `esc (.raiseJ exc)` answer. -/

/-- `retJ`/`throwJ` are `False` rather than `True`: at an empty continuation both *step*, to a
`raiseErr` whose class is `LocalJumpError`/`UncaughtThrowError`, and whether those are in the
type-error family is a question about the heap's class table. Out of the fragment, and the
exclusion is recorded rather than assumed away (§F27's residue). -/
def EscOk (m₀ : Machine) : Jump → Prop
  | .raiseJ exc => Semantics.isTypeError m₀.heap exc = false
  | .retJ _ _ => False
  | .throwJ _ _ => False
  | _ => True

def AnsOk (τ : Ty) (m₀ : Machine) : Answer → Prop
  | .val v => denM τ m₀ v
  | .esc j => EscOk m₀ j

/-- **The answer-typed judgment.** Compare `Denote/Sem/Judge.lean`'s `SemJudge`: the hypothesis
is an *answer* rather than a value, so the obligation is no longer vacuous on a run that
escapes, and the two ladders are one. -/
def PSemJudge (Γ : Env) (e : Ratchet.Expr) (τ : Ty) : Prop :=
  ∀ m : Machine, StateOk Ratchet.ctx0 Γ .ivar0 m →
    ∀ (fuel : Nat) (a : Answer) (m₀ : Machine) (rest : Nat),
      runA fuel (evalFrom m e) = .ans a m₀ rest → AnsOk τ m₀ a

/-! ## §3 The continuation typing

Two constructors, and the shape is the one §3 of `Invariant.lean` argues for: a frame's value
clause says what type it accepts and what the environment becomes, and its escape clause is
`pkontOk_escapes` below — proved once for the whole relation rather than per constructor,
because in this fragment every frame passes escapes through. -/

inductive PKontOk (τa : Ty) : List Kont → Env → Ty → Prop
  /-- **The empty continuation accepts exactly the program's own type.** Not "anything" — the
      `τa` index is what lets the value clause of the judgment be *recovered* (§9), and
      dropping it is what makes an invariant prove safety while proving nothing about types.
      This is Wright--Felleisen's context typing `E : τ ⇒ τ_ans`, and `τa` is the answer type
      in Danvy--Filinski's original sense. -/
  | nil {Γ : Env} : PKontOk τa [] Γ τa
  | asgnK {rest : List Kont} {Γ : Env} {τ : Ty} {x : String} :
      capStale x τ τ = false → capStaleCtx x τ Ratchet.ctx0 = false → isAliasTy τ = false →
      PKontOk τa rest (envAfter Γ x τ) τ → PKontOk τa (.asgnK .lvar x :: rest) Γ τ

/-- Every `PKontOk` continuation is `CatchFree` — departure 2, discharged. Nothing in the
fragment builds a `catchK`, so the hypothesis `run_pushK` needs is free here. -/
theorem pkontOk_catchFree : ∀ {τa : Ty} {K : List Kont} {Γ : Env} {τ : Ty},
    PKontOk τa K Γ τ → RubyCore.Proof.CatchFree K := by
  intro τa K Γ τ h
  induction h with
  | nil => intro k hk; exact absurd hk (by simp)
  | asgnK _ _ _ _ ih =>
    intro k hk t
    rcases List.mem_cons.mp hk with rfl | hmem
    · simp
    · exact ih k hmem t

/-! ## §4 The invariant -/

/-- The jumps the fragment can put in flight. `brkJ` only — which is what makes `noBadStep`
provable, since `unwind []` answers `.stuck` for it and `.uncaught` only for `raiseJ`. -/
def PJumpOk : Jump → Prop
  | .brkJ _ => True
  | _ => False

/-- Every jump the fragment can build is safe to escape with: `brkJ` at the empty continuation
is `.stuck`, and `.stuck` is not type-stuck. This is the escape clause, in one line. -/
theorem escOk_of_pJumpOk {m₀ : Machine} {j : Jump} (h : PJumpOk j) : EscOk m₀ j := by
  cases j <;> first | trivial | exact absurd h (by simp [PJumpOk])

/-- **The invariant**, one arm per `Ctl` — `Invariant.lean`'s `CtlOk`/`KontOk` pair, spelled
out for the fragment. -/
def PInv (τa : Ty) (m : Machine) : Prop :=
  (∃ (e₀ : Ratchet.Expr) (Γ Γ' : Env) (τ : Ty),
      m.ctl = .eval (toRuby e₀) ∧ StateOk Ratchet.ctx0 Γ .ivar0 m ∧
      PJudge Γ e₀ τ Γ' ∧ PKontOk τa m.kont Γ' τ) ∨
  (∃ (v : Value) (Γ : Env) (τ : Ty),
      m.ctl = .value v ∧ StateOk Ratchet.ctx0 Γ .ivar0 m ∧ denM τ m v ∧
      PKontOk τa m.kont Γ τ) ∨
  (∃ (j : Jump) (Γ : Env) (τ : Ty),
      m.ctl = .jump j ∧ PJumpOk j ∧ PKontOk τa m.kont Γ τ)

/-! ## §5 The step lemmas

One per `stepFn` arm the invariant can reach: four `evalExpr` arms and two frame deliveries
(value and escape) for `asgnK`. Stated with `.ctl`/`.kont` hypotheses so `preserved` can apply
them after casing, rather than needing the machine in `reCtl` form. -/

theorem step_int {m : Machine} {n : Int} (hc : m.ctl = .eval (.int n)) :
    Interp.stepFn m = .next (reCtl m (.value (.int n)) m.kont) := by
  simp only [Interp.stepFn, hc, Interp.evalExpr, Interp.withCtl, reCtl]

theorem step_var {m : Machine} {x : String} (hc : m.ctl = .eval (.var .lvar x)) :
    Interp.stepFn m = .next (reCtl m (.value (m.getLocal x)) m.kont) := by
  simp only [Interp.stepFn, hc, Interp.evalExpr, Interp.withCtl, reCtl]

theorem step_brk {m : Machine} (hc : m.ctl = .eval (.brk none)) :
    Interp.stepFn m = .next (reCtl m (.jump (.brkJ .nil)) m.kont) := by
  simp only [Interp.stepFn, hc, Interp.evalExpr, Interp.withCtl, reCtl]

theorem step_vasgn {m : Machine} {x : String} {e : RubyCore.Expr}
    (hc : m.ctl = .eval (.vasgn .lvar x e)) :
    Interp.stepFn m = .next (reCtl m (.eval e) (.asgnK .lvar x :: m.kont)) := by
  simp only [Interp.stepFn, hc, Interp.evalExpr, Interp.withKont, reCtl]

/-- The machine `asgnK` leaves behind: the frame popped, the local written, the same value
still in flight. Named because the interpreter builds it in its own order (pop, then write,
then set `ctl`) and a lemma stated in any other order is not `rfl`. -/
def afterWrite (m : Machine) (x : String) (v : Value) (rest : List Kont) : Machine :=
  Interp.withCtl (({ m with kont := rest }).setLocal x v) (.value v)

theorem step_asgnK_val {m : Machine} {x : String} {v : Value} {rest : List Kont}
    (hc : m.ctl = .value v) (hk : m.kont = .asgnK .lvar x :: rest) :
    Interp.stepFn m = .next (afterWrite m x v rest) := by
  simp only [Interp.stepFn, hc, Interp.applyKont, hk, afterWrite]

/-- `withCtl` and the frame pop are both `reCtl`s, so `StateOk_reCtl`/`denM_reCtl` reach them.
Three `rfl`s, and they are the whole cost of the interpreter building its machines in its own
field order. -/
theorem withCtl_eq_reCtl (m : Machine) (c : Ctl) : Interp.withCtl m c = reCtl m c m.kont := rfl

theorem popK_eq (m : Machine) (rest : List Kont) :
    ({ m with kont := rest } : Machine) = reCtl m m.ctl rest := rfl

theorem StateOk_withCtl {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (h : StateOk κ Γ I m) (c : Ctl) : StateOk κ Γ I (Interp.withCtl m c) := by
  rw [withCtl_eq_reCtl]; exact StateOk_reCtl h _ _

theorem denM_withCtl {τ : Ty} {m : Machine} {c : Ctl} {v : Value} :
    denM τ (Interp.withCtl m c) v ↔ denM τ m v := by
  rw [withCtl_eq_reCtl]; exact denM_reCtl

theorem afterWrite_kont (m : Machine) (x : String) (v : Value) (rest : List Kont) :
    (afterWrite m x v rest).kont = rest := rfl

theorem afterWrite_ctl (m : Machine) (x : String) (v : Value) (rest : List Kont) :
    (afterWrite m x v rest).ctl = .value v := rfl

/-- A value at the empty continuation is the run's answer, not a step. -/
theorem step_value_nil {m : Machine} {v : Value} (hc : m.ctl = .value v) (hk : m.kont = []) :
    Interp.stepFn m = .done v m := by
  simp only [Interp.stepFn, hc, Interp.applyKont, hk]

/-- A `break` at the empty continuation escapes the program: `.stuck`, and `.stuck` is not
type-stuck. This is the whole of why the fragment's escape clause is satisfiable. -/
theorem step_brkJ_nil {m : Machine} {w : Value} (hc : m.ctl = .jump (.brkJ w))
    (hk : m.kont = []) :
    Interp.stepFn m = .stuck "jump escaped the program (break/next/retry at toplevel)" := by
  simp only [Interp.stepFn, hc, Interp.unwind, hk]

theorem step_asgnK_jump {m : Machine} {x : String} {j : Jump} {rest : List Kont}
    (hc : m.ctl = .jump j) (hk : m.kont = .asgnK .lvar x :: rest) :
    Interp.stepFn m = .next (reCtl m (.jump j) rest) := by
  simp only [Interp.stepFn, hc, Interp.unwind, hk]
  cases j <;> simp only [Interp.withCtl, reCtl]

/-! ## §6 The two obligations, and safety -/

/-- The self spine is `.ivar0` throughout the fragment, and `killClosOverSpine` leaves anything
that is not an `ivarCons` alone. `rfl`. -/
theorem killClosOverSpine_ivar0 (x : String) (τ : Ty) :
    killClosOverSpine .ivar0 x τ = .ivar0 := rfl

/-- `StateOk` survives the write, at the environment the certificate says. Packaged because
both the `asgnK` value delivery and nothing else needs it, and it is where all three `vasgn`
side conditions are spent. -/
theorem stateOk_write {Γ : Env} {m : Machine} {x : String} {τ : Ty} {v : Value}
    (hm : StateOk Ratchet.ctx0 Γ .ivar0 m) (hd : denM τ m v)
    (hcap : capStale x τ τ = false) (hctx : capStaleCtx x τ Ratchet.ctx0 = false)
    (halias : isAliasTy τ = false) :
    StateOk Ratchet.ctx0 (envAfter Γ x τ) .ivar0 (m.setLocal x v) := by
  have h := StateOk_setLocal hm hd hcap hctx
    (ρ := τ) (by cases τ <;> simp_all [Ratchet.stripAlias, Ratchet.isAliasTy])
    (by intro y σ hy; rw [hy] at halias; simp [Ratchet.isAliasTy] at halias)
  simpa [envAfter, killClosOverSpine_ivar0] using h

theorem preserved (τa : Ty) : ∀ m m', PInv τa m → Interp.stepFn m = .next m' → PInv τa m' := by
  intro m m' hinv hstep
  rcases hinv with ⟨e₀, Γ, Γ', τ, hc, hm, hj, hk⟩ | ⟨v, Γ, τ, hc, hm, hd, hk⟩ |
    ⟨j, Γ, τ, hc, hjo, hk⟩
  · -- **the `eval` arm**: one case per certificate rule
    cases hj with
    | @intLit n =>
      rw [step_int (by simpa [toRuby, toRubyOpt] using hc)] at hstep
      cases hstep
      refine Or.inr (Or.inl ⟨.int n, Γ, .int, rfl, StateOk_reCtl hm _ _, ?_, hk⟩)
      exact denM_reCtl.mpr (by simp [denM, isIntV])
    | var hget halias =>
      rw [step_var (by simpa [toRuby, toRubyVarKind] using hc)] at hstep
      cases hstep
      refine Or.inr (Or.inl ⟨_, Γ, τ, rfl, StateOk_reCtl hm _ _, denM_reCtl.mpr ?_, hk⟩)
      have := (hm.env.1 _ _ hget).1
      rwa [show Ratchet.stripAlias τ = τ by
        cases τ <;> simp_all [Ratchet.stripAlias, Ratchet.isAliasTy]] at this
    | vasgn hsub hcap hctx halias =>
      rw [step_vasgn (by simpa [toRuby, toRubyVarKind] using hc)] at hstep
      cases hstep
      exact Or.inl ⟨_, Γ, _, _, rfl, StateOk_reCtl hm _ _, hsub,
        PKontOk.asgnK hcap hctx halias hk⟩
    | brk =>
      rw [step_brk (by simpa [toRuby, toRubyOpt] using hc)] at hstep
      cases hstep
      exact Or.inr (Or.inr ⟨_, Γ, τ, rfl, trivial, hk⟩)
  · -- **the `value` arm**: the empty continuation is `.done`, so only `asgnK` can step
    cases hkn : m.kont with
    | nil => rw [step_value_nil hc hkn] at hstep; exact absurd hstep (by simp)
    | cons k rest =>
      rw [hkn] at hk
      cases hk with
      | @asgnK _ _ _ x hcap hctx halias hrest =>
        rw [step_asgnK_val hc hkn] at hstep
        cases hstep
        -- the popped machine, which is a `reCtl` of `m`, so conformance and typing move to it
        have hm₁ : StateOk Ratchet.ctx0 Γ .ivar0 ({ m with kont := rest } : Machine) := by
          rw [popK_eq]; exact StateOk_reCtl hm _ _
        have hd₁ : denM τ ({ m with kont := rest } : Machine) v := by
          rw [popK_eq]; exact denM_reCtl.mpr hd
        exact Or.inr (Or.inl ⟨v, envAfter Γ x τ, τ, afterWrite_ctl m x v rest,
          StateOk_withCtl (stateOk_write hm₁ hd₁ hcap hctx halias) _,
          denM_withCtl.mpr (denM_setLocal hd₁ hcap hd₁), hrest⟩)
  · -- **the `jump` arm**: the escape clause, and it is the same two frames
    cases j with
    | brkJ w =>
      cases hkn : m.kont with
      | nil => rw [step_brkJ_nil hc hkn] at hstep; exact absurd hstep (by simp)
      | cons k rest =>
        rw [hkn] at hk
        cases hk with
        | @asgnK _ _ _ x _ _ _ hrest =>
          rw [step_asgnK_jump hc hkn] at hstep
          cases hstep
          exact Or.inr (Or.inr ⟨_, envAfter Γ x τ, τ, rfl, hjo, hrest⟩)
    | _ => exact absurd hjo (by simp [PJumpOk])

theorem noBadStep (τa : Ty) : ∀ m exc m', PInv τa m → Interp.stepFn m = .uncaught exc m' →
    Semantics.isTypeError m'.heap exc = false := by
  intro m exc m' hinv hstep
  exfalso
  rcases hinv with ⟨e₀, Γ, Γ', τ, hc, -, hj, -⟩ | ⟨v, Γ, τ, hc, -, -, hk⟩ |
    ⟨j, Γ, τ, hc, hjo, hk⟩
  · cases hj with
    | intLit => rw [step_int (by simpa [toRuby, toRubyOpt] using hc)] at hstep; exact absurd hstep (by simp)
    | var _ _ =>
      rw [step_var (by simpa [toRuby, toRubyVarKind] using hc)] at hstep
      exact absurd hstep (by simp)
    | vasgn _ _ _ _ =>
      rw [step_vasgn (by simpa [toRuby, toRubyVarKind] using hc)] at hstep
      exact absurd hstep (by simp)
    | brk => rw [step_brk (by simpa [toRuby, toRubyOpt] using hc)] at hstep; exact absurd hstep (by simp)
  · -- a value in flight: `.done` at `[]`, `.next` at `asgnK`; neither is `.uncaught`
    cases hkn : m.kont with
    | nil => rw [step_value_nil hc hkn] at hstep; exact absurd hstep (by simp)
    | cons k rest =>
      rw [hkn] at hk
      cases hk with
      | asgnK _ _ _ _ =>
        rw [step_asgnK_val hc hkn] at hstep; exact absurd hstep (by simp)
  · -- **the only arm that could have been `.uncaught`**, and `PJumpOk` is what rules it out
    cases j with
    | brkJ w =>
      cases hkn : m.kont with
      | nil => rw [step_brkJ_nil hc hkn] at hstep; exact absurd hstep (by simp)
      | cons k rest =>
        rw [hkn] at hk
        cases hk with
        | asgnK _ _ _ _ =>
          rw [step_asgnK_jump hc hkn] at hstep; exact absurd hstep (by simp)
    | _ => exact absurd hjo (by simp [PJumpOk])

/-- **The obligations, packaged** — and this is the interface `safety_of_invariant` takes. -/
theorem pInv_obligations (τa : Ty) : SafetyObligations (PInv τa) :=
  ⟨preserved τa, noBadStep τa⟩

/-- **Safety.** No run from a `PInv` machine ever reaches a type-stuck outcome, at any fuel.
`safety_of_invariant` is `Denote/Sem/Invariant.lean`'s, unchanged — the reduction was proved
abstractly and this is the first thing to instantiate it. -/
theorem pInv_safe (τa : Ty) : ∀ (fuel : Nat) (m : Machine), PInv τa m →
    Semantics.typeStuck (Interp.run fuel m) = false :=
  safety_of_invariant (pInv_obligations τa)

/-! ## §7 From a program and a certificate to the invariant -/

/-- **`InvInit` for the fragment.** A derivation for `p` **at any incoming environment**, at any
machine conformant with it, is the invariant at the machine that starts running `p`. The
certificate is dropped straight into the `eval` arm and `PKontOk.nil` supplies the rest.

**`Γ` is universally quantified, and that is load-bearing rather than generous.** An earlier
version fixed `Γ = []` — the environment a *whole program* starts at — and everything below
inherited the restriction, which made the adequacy theorem (§9) useless for the one thing an
adequacy theorem is for: a sub-derivation of a larger program lives at a *non-empty* `Γ`.
Nothing in the proof ever needed the emptiness; `PInv` quantifies the environment
existentially and `PKontOk.nil` holds at every `Γ`. `κ` is still fixed to `ctx0` (departure 4),
and that one *is* forced here: `PJudge.vasgn` names `ctx0` in its `capStaleCtx` premise. -/
theorem pInv_init {p : Ratchet.Expr} {τ : Ty} {Γ Γ' : Env} (hj : PJudge Γ p τ Γ')
    {m : Machine} (hm : StateOk Ratchet.ctx0 Γ .ivar0 m) : PInv τ (evalFrom m p) :=
  Or.inl ⟨p, Γ, Γ', τ, rfl, StateOk_reCtl hm _ _, hj, PKontOk.nil⟩

/-- **The theorem the prototype exists to produce**: a type certificate rules out type-stuck
outcomes for the program it certifies. Every hypothesis is discharged; nothing is assumed. -/
theorem certificate_implies_safe {p : Ratchet.Expr} {τ : Ty} {Γ Γ' : Env}
    (hj : PJudge Γ p τ Γ') {m : Machine} (hm : StateOk Ratchet.ctx0 Γ .ivar0 m) :
    StuckFree m p :=
  fun fuel => pInv_safe τ fuel (evalFrom m p) (pInv_init hj hm)

/-! ## §8 Two worked programs

`bootOkB` is `Denote/Sanity.lean`'s `#guard`ed conformance witness for the prelude-booted
machine, so these are statements about the machine the difftest SUT actually runs. -/

/-- `x = (y = 1)` — nested writes, two `asgnK` frames, the value clause twice. -/
def progNested : Ratchet.Expr :=
  .vasgn .lvar "x" (.vasgn .lvar "y" (.int 1))

theorem cert_nested : PJudge [] progNested .int (envAfter (envAfter [] "y" .int) "x" .int) :=
  .vasgn (.vasgn .intLit (by decide) (by decide) (by decide)) (by decide) (by decide)
    (by decide)

theorem nested_safe (hb : bootOkB = true) : StuckFree bootMachine progNested :=
  certificate_implies_safe cert_nested (stateOk_boot hb)

/-- `x = break` — the escape clause, exercised. The certificate types it at `.int`, which is
*meaningless* as a value claim (the program returns no value) and is exactly why the escape
clause has to carry the content. Safety holds because the answer is a `brkJ`, not because
anything was proved about `Integer`. -/
def progBreak : Ratchet.Expr := .vasgn .lvar "x" (.brk none)

theorem cert_break : PJudge [] progBreak .int (envAfter [] "x" .int) :=
  .vasgn .brk (by decide) (by decide) (by decide)

theorem break_safe (hb : bootOkB = true) : StuckFree bootMachine progBreak :=
  certificate_implies_safe cert_break (stateOk_boot hb)

/-! ## §9 …and `PSemJudge` falls out — both arms, but only because of the `τa` index

The module docstring's finding, mechanised and **sharpened by the attempt**. The first version
of `PKontOk` had `nil : PKontOk [] Γ τ` — the empty continuation accepts *anything* — and with
it `PInv` proves safety and says **nothing about types**, because `PInv`'s `∃ τ` forgets which
type the certificate claimed. Recovering the value clause forced `nil` to pin the program's own
type (`PKontOk τa [] Γ τa`), which is Wright--Felleisen's context typing `E : τ ⇒ τ_ans` and
`τa` is the answer type in Danvy--Filinski's original sense. So "answer type" turns up twice in
this design, at the run level (`Answer`) and at the type level (`τa`), and the second one is
what makes the judgment derivable rather than merely true.

With it, the answer-typed semantic judgment is a **corollary**: what `preserved` consumes is
the *syntactic* `PJudge` plus `PKontOk`, and `PSemJudge` is the output. -/

/-- Reading the answer point back off the machine. -/
theorem ctl_kont_of_val {m : Machine} {v : Value} (h : answerPoint m = some (.val v)) :
    m.ctl = .value v ∧ m.kont = [] := by
  cases hk : m.kont with
  | cons k r => rw [answerPoint, hk] at h; simp at h
  | nil =>
    cases hc : m.ctl with
    | eval e => rw [answerPoint, hk] at h; simp only at h; rw [hc] at h; simp at h
    | jump j => rw [answerPoint, hk] at h; simp only at h; rw [hc] at h; simp at h
    | value w =>
      rw [answerPoint, hk] at h; simp only at h; rw [hc] at h
      simp only [Option.some.injEq, Answer.val.injEq] at h
      exact ⟨by rw [h], rfl⟩

theorem ctl_of_esc {m : Machine} {j : Jump} (h : answerPoint m = some (.esc j)) :
    m.ctl = .jump j := by
  cases hk : m.kont with
  | cons k r => rw [answerPoint, hk] at h; simp at h
  | nil =>
    cases hc : m.ctl with
    | eval e => rw [answerPoint, hk] at h; simp only at h; rw [hc] at h; simp at h
    | value w => rw [answerPoint, hk] at h; simp only at h; rw [hc] at h; simp at h
    | jump j' =>
      rw [answerPoint, hk] at h; simp only at h; rw [hc] at h
      simp only [Option.some.injEq, Answer.esc.injEq] at h
      rw [h]

/-- **The invariant survives the walk to the answer point.** One induction, mirroring
`runA_rest_le`; `preserved` is applied at exactly one place. -/
theorem inv_runA (τa : Ty) : ∀ (fuel : Nat) (m : Machine) (a : Answer) (m₀ : Machine)
    (rest : Nat), runA fuel m = .ans a m₀ rest → PInv τa m → PInv τa m₀ := by
  intro fuel
  induction fuel with
  | zero =>
    intro m a m₀ rest h hinv
    cases hap : answerPoint m with
    | some a' => rw [runA_ans hap] at h; injection h with h1 h2 h3; subst h2; exact hinv
    | none => rw [runA_zero hap] at h; exact absurd h (by simp)
  | succ n ih =>
    intro m a m₀ rest h hinv
    cases hap : answerPoint m with
    | some a' => rw [runA_ans hap] at h; injection h with h1 h2 h3; subst h2; exact hinv
    | none =>
      rw [runA_succ hap] at h
      cases hev : Interp.stepFn m with
      | next m' => simp only [hev] at h; exact ih m' a m₀ rest h (preserved τa m m' hinv hev)
      | done v m' =>
        exfalso
        obtain ⟨hc, hk, -⟩ := RubyCore.Proof.done_inv m v m' hev
        rw [answerPoint, hk] at hap; simp only at hap; rw [hc] at hap; simp at hap
      | uncaught exc m' => rw [hev] at h; exact absurd h (by simp)
      | unsupported r => rw [hev] at h; exact absurd h (by simp)
      | stuck msg => rw [hev] at h; exact absurd h (by simp)

/-- **The answer-typed semantic judgment, derived.** Both clauses: the value clause comes from
`PKontOk.nil`'s `τa` pin, the escape clause from `PJumpOk`. -/
theorem psemJudge_of_pjudge {p : Ratchet.Expr} {τ : Ty} {Γ Γ' : Env} (hj : PJudge Γ p τ Γ') :
    PSemJudge Γ p τ := by
  intro m hm fuel a m₀ rest hr
  have hinv := inv_runA τ fuel (evalFrom m p) a m₀ rest hr (pInv_init hj hm)
  have hap : answerPoint m₀ = some a := answerPoint_of_ans fuel (evalFrom m p) a m₀ rest hr
  cases a with
  | val v =>
    obtain ⟨hc, hk⟩ := ctl_kont_of_val hap
    rcases hinv with ⟨e₀, Γ₁, Γ₂, τ₂, hce, -, -, -⟩ | ⟨w, Γ₁, τ₂, hcw, -, hd, hkk⟩ |
      ⟨j, Γ₁, τ₂, hcj, -, -⟩
    · rw [hc] at hce; exact absurd hce (by simp)
    · -- the value arm, and `PKontOk.nil` is what forces `τ₂ = τ`
      have hvw : w = v := by rw [hc] at hcw; injection hcw with he; exact he.symm
      subst hvw
      rw [hk] at hkk
      cases hkk
      exact hd
    · rw [hc] at hcj; exact absurd hcj (by simp)
  | esc j =>
    have hc := ctl_of_esc hap
    rcases hinv with ⟨e₀, Γ₁, Γ₂, τ₂, hce, -, -, -⟩ | ⟨w, Γ₁, τ₂, hcw, -, -, -⟩ |
      ⟨j₂, Γ₁, τ₂, hcj, hjo, -⟩
    · rw [hc] at hce; exact absurd hce (by simp)
    · rw [hc] at hcw; exact absurd hcw (by simp)
    · -- the escape arm: the only jump the fragment builds is a `brkJ`, and that is safe
      have hjj : j₂ = j := by rw [hc] at hcj; injection hcj with he; exact he.symm
      subst hjj
      exact escOk_of_pJumpOk hjo

/-- The certificate's *type* claim, not just its safety claim: whenever the certified program
returns, the value is in the type the certificate named. -/
theorem certificate_types_the_value {p : Ratchet.Expr} {τ : Ty} {Γ Γ' : Env}
    (hj : PJudge Γ p τ Γ') {m : Machine} (hm : StateOk Ratchet.ctx0 Γ .ivar0 m)
    (fuel : Nat) (v : Value) (m₀ : Machine) (rest : Nat)
    (hr : runA fuel (evalFrom m p) = .ans (.val v) m₀ rest) : denM τ m₀ v :=
  psemJudge_of_pjudge hj m hm fuel _ m₀ rest hr

/-- The general escape route, kept for the shape: when the fragment grows a `raise`, this is
how the `esc` clause is discharged — from safety, through `delivers_safeA`, rather than from
`PJumpOk`. Vacuous here (nothing in the fragment raises), and that is why it is *not* what
`psemJudge_of_pjudge` uses. -/
theorem psemJudge_escOk {p : Ratchet.Expr} {τ : Ty} {Γ Γ' : Env} (hj : PJudge Γ p τ Γ')
    {m : Machine} (hm : StateOk Ratchet.ctx0 Γ .ivar0 m) :
    ∀ (fuel : Nat) (exc : Value) (m₀ : Machine) (rest : Nat),
      runA fuel (evalFrom m p) = .ans (.esc (.raiseJ exc)) m₀ rest →
      Semantics.isTypeError m₀.heap exc = false := by
  intro fuel exc m₀ rest hr
  have hsafe : SafeA (deliverA (.esc (.raiseJ exc)) m₀ []) :=
    delivers_safeA (certificate_implies_safe hj hm) fuel _ m₀ rest hr
  have := hsafe 1
  rw [show Interp.run 1 (deliverA (.esc (.raiseJ exc)) m₀ [])
        = .uncaught exc (deliverA (.esc (.raiseJ exc)) m₀ []) by
    rw [run_succ]
    simp only [Interp.stepFn, deliverA, Answer.ctl, Interp.unwind]] at this
  simpa [Semantics.typeStuck, deliverA] using this

#print axioms preserved
#print axioms noBadStep
#print axioms pInv_safe
#print axioms certificate_implies_safe
#print axioms nested_safe
#print axioms break_safe
#print axioms psemJudge_of_pjudge
#print axioms certificate_types_the_value

end Ratchet.Denote.Proto
