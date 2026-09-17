import Ratchet.Check
import Denote.Sem.SafeKont
import Denote.Sem.Transport
import Denote.Sem.Alloc
import Denote.Sanity

/-!
# `Denote/Typed/JudgeA.lean` — the answer-typed semantic judgment for `DJudge`, and its obligations

`../../AGENTS.md` §The answer-typed design §3.1, at `Ratchet/Check.lean`'s index shape. This
is the semantic reading the typed ladder's rules are proved against, and it is **not**
`Denote/Sem/Judge.lean`'s `SemJudge`. Two differences, and they are the reason the 48 existing
obligations are not reusable here:

1. **The hypothesis is an `Answer`, not a value.** `SemJudge` says *if the run returns a
   value, the value is in the type* — and `Denote/Sem/NoProgress.lean`'s
   `not_semJudgeImpliesStuckFree` proves that this says nothing at all about a run that
   escapes: `evals_brk_never` exhibits a program with no value outcome, for which every
   `SemJudge` is vacuously true. So a rule could be "justified" while the program it types
   raises `TypeError`.
2. **The conclusion says whether the run is type-stuck.** `AnsOk`'s `esc (.raiseJ exc)` arm is
   `isTypeError m₀.heap exc = false` — `Semantics.typeStuck`'s own predicate, and *exact*
   rather than an approximation: `StepResult.uncaught` is constructed at exactly one site in
   the interpreter (`RubyCore/Interp/Kont.lean:341`, `unwind`'s `[]` arm on a `raiseJ`), so
   every type-stuck outcome is an `esc (.raiseJ exc)` answer. Folding the old two ladders —
   value typing and stuck-freedom — into one answer-indexed obligation therefore loses
   nothing.

The prototype (`Denote/Proto/Safety.lean`) is the working instance of this shape at four
rules, proved end to end; read it first. This file is that shape at `DJudge`'s twelve, and
the substantive difference from the prototype is that the obligations here are **rule-local**
— premises semantic, conclusion semantic — because that is what a `Clink.sem` field has to be
(`Denote/Clink/Spec.lean`). The prototype's `psemJudge_of_pjudge` goes through the invariant
instead and is whole-derivation.

## Why rule-local composition is even possible

`evalFrom m e` is `{ m with ctl := .eval (toRuby e), kont := [] }` — it **empties the
continuation**. So every obligation here is about a run from an empty continuation, which is
why the `CatchFree` side condition `run_pushK` needs is free for the frames a rule pushes
(`AGENTS.md` §The answer-typed design §9.2 warns that `safe_pushK` is a per-rule tool and cannot be a
whole-machine invariant; at an empty base kont the warning does not bite).

## What is taken from the old checker, and it is not the checker

`Ratchet/Validate.lean` is imported transitively (via `Denote/Sanity.lean`) for exactly two
things: the **empty context value** `ctx0`, because `StateOk` is `Ctx`-indexed and `Ctx` lives
in `Ratchet/Judge.lean`, and `stateOk_boot`, the `#guard`ed conformance witness for the
prelude-booted machine. Neither is `chk`, and nothing here mentions `Judge` or `validate`.

## Rule proofs

This file proves the seven literals, local reads, and assignment. `Sequence.lean`,
`Branch.lean`, and `Primitive.lean` prove the remaining rules; `Clink.lean` registers all
of them and both list companions. `Compose.lean` lifts closed safety and answer correctness
to `SafeUnder`, using the escape clause of the continuation typing and `run_pushK`.
-/

set_option autoImplicit false

namespace Ratchet.Denote.Typed

open RubyCore Ratchet Ratchet.Denote

/-! ## §1 The judgment -/

/-- **What it means for an escape to be safe.** The `raiseJ` arm is exact (see the header).

`brkJ`/`nxtJ`/`redoJ`/`retryJ` are `True` because `unwind []` answers `.stuck` for them, and
`.stuck` is not type-stuck — a `break` outside a loop is a `LocalJumpError` *in CRuby*, but in
this model it ends the run without an exception, and the difftest agreement gate is what makes
that a fact about the model rather than an assumption.

`retJ`/`throwJ` are **`False`**, which is the *strong* choice rather than a weakening: at an
empty continuation both step to a `raiseErr` whose class is `LocalJumpError` /
`UncaughtThrowError`, and whether those are in the type-error family is a question about the
heap's class table that `StateOk` does not answer (`found-issues.md` §F27's residue). Making
the arm `False` means a rule that could produce one has to prove it cannot. No `DJudge` rule
can — the judgment has no `ret`, `throw`, `brk` or `next` rule — so the arm is discharged by
unreachability here, and the day a rule needs it, the class-table fact is what it owes. -/
def EscOk (m₀ : Machine) : Jump → Prop
  | .raiseJ exc => Semantics.isTypeError m₀.heap exc = false
  | .retJ _ _ => False
  | .throwJ _ _ => False
  | _ => True

/-- The obligation on an answer: a value is in the type, an escape is safe. One predicate
where the old design had two ladders. -/
def AnsOk (τ : Ty) (m₀ : Machine) : Answer → Prop
  | .val v => denM τ m₀ v
  | .esc j => EscOk m₀ j

/-- **The answer-typed semantic judgment**, at `Ratchet/Check.lean`'s shape.

`κ` is `ctx0` and the ivar spine is `.ivar0` because `DJudge` has neither and the fragment it
covers declares nothing (`Ratchet/Check.lean` §"Not in the judgment"). `Γ` and `Γ'` are
universally quantified, which is load-bearing rather than generous: the prototype fixed the
incoming environment to `[]` and that made its adequacy theorem useless for the one job an
adequacy theorem has, since a sub-derivation of a larger program lives at a non-empty
environment (commit `fc5fc5f`).

Three conjuncts, all three needed by composition rather than by taste: `Framed` transports a
rule's premises to its conclusion, `AnsOk` is the content, and the outgoing `StateOk` is what
the *next* statement's premise consumes — claimed on the `val` arm only, because what holds at
an escape is rule-specific and belongs in the rule's own premises (§F23 at a loop, §F25 at a
`raise`). -/
def SemJudgeA (Γ : Env) (e : Ratchet.Expr) (τ : Ty) (Γ' : Env) : Prop :=
  ∀ m : Machine, StateOk Ratchet.ctx0 Γ .ivar0 m →
    ∀ (fuel : Nat) (a : Answer) (m₀ : Machine) (rest : Nat),
      runA fuel (evalFrom m e) = .ans a m₀ rest →
      Framed m m₀ ∧ AnsOk τ m₀ a ∧
        (∀ v, a = .val v → StateOk Ratchet.ctx0 Γ' .ivar0 m₀)

/-! ### §1b …and safety, stated through the **continuation typing**

`SemJudgeA` is a statement about runs that reach an **answer**. That is not safety, and the
gap is real: a run can halt `.uncaught` — the one type-stuck outcome — which `runA` reports as
`.halt`, not `.ans`. Closing that gap by *derivation* needs `UncaughtInv`
(`AGENTS.md` §The answer-typed design §7), which does not exist. So safety is a **second obligation
carried by the same clink**.

**The shape of that obligation is the whole content of this section**, because the obvious
version is too weak. Safety of a *program* —

```
∀ m, StateOk ctx0 Γ .ivar0 m → StuckFree m e        -- too weak
```

— is about `evalFrom m e`, which **empties the continuation**. It therefore says nothing about
a machine part-way through a larger program, and it does not compose: a rule with a
sub-expression premise gets a fact about the sub-expression run *as a whole program* and needs
one about it *under the frame the rule just pushed*. Every composite rule would have to bridge
that itself with fuel arithmetic.

The obligation below is the **invariant** instead (`Denote/Sem/Invariant.lean` is the
reduction; this is its content at this judgment): a machine whose control word is this
expression and whose **continuation is well-typed** is safe. `DKontOk` is the continuation
typing, and it is indexed by the *answer type* `τa` — the type the empty continuation accepts
— which is Wright–Felleisen's context typing `E : τ ⇒ τ_ans`. The prototype found the hard way
that dropping that index makes an invariant prove safety while proving nothing about types,
because the existential over the current type forgets what the certificate claimed.

**Why this is the induction and not a substitute for it.** `DJudgeC` is Church-encoded
(`Denote/Clink/Spec.lean` §3), so a derivation is a **Π-type, not an inductive**: there is no
constructor to match on, and `preserved` cannot be proved by `cases` over the derivation the
way `Denote/Proto/Safety.lean` did over an inductive `PJudge`.

Induction with an index-only motive is *free* — it is what the definition is. What the
encoding does not hand over is **inversion** ("the last rule must have been `intLit`"). That
is recoverable by the standard pairing trick (take the motive `DJudgeC R · ∧ Inv ·`), but it
additionally needs `Closed R (DJudgeC R)`, which is provable rule by rule and not by a lemma
uniform in `c`. Nothing here has needed it, because **choosing the family to be "the invariant
holds here" *is* the inductive proof** — one case per rule, and those cases are exactly the
clink fields. Safety of every program the fragment types then follows by
instantiating at the empty continuation.

Stated as safety of the **machine** (`SafeA m`) rather than of the program, so that it
composes: a rule that pushes a frame consumes its premise at a machine whose continuation is
the frame it pushed, which is what `DKontOk`'s frame clauses will say. -/

/-- **The continuation typing.** `DKontOk τa K Γ τ`: the continuation `K` accepts a value of
type `τ` at environment `Γ`, and the run as a whole will answer at type `τa`.

The empty continuation accepts the answer type; an assignment frame writes the value
and passes it on. Other composite rules use `Compose.lean`'s proved lifting theorem to
satisfy the same `SafeUnder` target. -/
inductive DKontOk (τa : Ty) : List Kont → Env → Ty → Prop
  /-- **The empty continuation accepts exactly the program's own type.** Not "anything": with
      `nil` accepting any type the invariant proves safety and says nothing about types, which
      is the prototype's second finding and the reason `τa` is an index at all. -/
  | nil {Γ : Env} : DKontOk τa [] Γ τa
  /-- **The frame `vasgn` pushes.** It accepts a value of `τ` at `Γ`, writes `x`, and hands
      the same value on to a continuation that accepts `τ` at `envAfter Γ x τ` — the *same*
      type, because Ruby's `x = e` evaluates to `e`.

      The two side conditions are the rule's own (`DJudge.vasgn`), and they are consumed
      here rather than there: `denM_setLocal` needs `hcap` to transport the value's type
      across the write, and `StateOk_setLocal` needs it and `halias` for conformance. That is
      the invariant paying for the rule's premises at the point the frame fires. -/
  | asgnK {rest : List Kont} {Γ : Env} {τ : Ty} {x : String} :
      capStale x τ τ = false → isAliasTy τ = false →
      DKontOk τa rest (envAfter Γ x τ) τ → DKontOk τa (.asgnK .lvar x :: rest) Γ τ

/-- **Safety, through the invariant.** A machine about to evaluate `e`, conformant with the
incoming environment, under a continuation that accepts `e`'s type, is safe: no run from it
reaches a type-stuck outcome, at any fuel.

Universally quantified over `τa` and over the continuation — that is what makes it the
invariant rather than a statement about whole programs, and what lets a composite rule use its
premise at the machine it actually creates. -/
def SafeUnder (Γ : Env) (e : Ratchet.Expr) (τ : Ty) (Γ' : Env) : Prop :=
  ∀ (τa : Ty) (m : Machine), StateOk Ratchet.ctx0 Γ .ivar0 m →
    m.ctl = .eval (toRuby e) → DKontOk τa m.kont Γ' τ → SafeA m

/-- **The target of a clink**: the answer-typed reading *and* the invariant. `dsemFam` is
instantiated at this, so both are fields of the same obligation and neither can be registered
without the other. -/
def SemSafeA (Γ : Env) (e : Ratchet.Expr) (τ : Ty) (Γ' : Env) : Prop :=
  SemJudgeA Γ e τ Γ' ∧ SafeUnder Γ e τ Γ'

/-! ## §1a Three facts about `stepFn`, and nothing about any judgment

Moved here from the deleted `Denote/Rules/Lit.lean` (clink 68), which proved the old
value-shaped obligations around them. They are statements about `Interp.stepFn` alone, which
is why they survived their file: `evalFrom` sets the control word, and one step evaluates the
literal or the local read.

The six *pure* literals need no lemma at all — `stepFn (evalFrom m (.int n)) = …` is `rfl` —
so only the two that do something are here: a local read redirects the machine first
(`getLocal_reCtl`), and a string literal **allocates**. -/

/-- The one step of a local read is `.value (m.getLocal x)`, but at the *redirected* machine,
so this is `getLocal_reCtl` rather than `rfl`. -/
theorem stepFn_var (m : Machine) (x : String) :
    Interp.stepFn (evalFrom m (.var .lvar x)) = .next (reCtl m (.value (m.getLocal x)) []) := by
  simp only [evalFrom, toRuby, toRubyVarKind, Interp.stepFn, Interp.evalExpr, Interp.withCtl,
    reCtl, getLocal_reCtl]

/-- The object a string literal allocates: `Builtins.allocStr`'s. Unfrozen, no ivars, no
eigenclass — which is what makes `ext_push`'s three hypotheses `rfl`. -/
def strObj (s : String) (binary : Bool := false) : Object :=
  { klass := Boot.stringId, payload := .str s, binary }

/-- One `stepFn` step from a string literal: the fresh object is at the old heap's `size`, and
nothing but `ctl` and the heap moves. -/
theorem stepFn_str (m : Machine) (s : String) :
    Interp.stepFn (evalFrom m (.str s)) =
      .next (reCtl { m with heap := pushHeap m.heap (strObj s) }
        (.value (.ref m.heap.objs.size)) []) := rfl

/-! ## §2 The inversion lemma for a one-step expression

The answer-typed counterpart of `Denote/Rules/Core.lean`'s `evals_pure`, and **shorter than
it** — which is the first small dividend of the restatement. `evals_pure` needs two steps
(the value has to be *delivered* to the empty continuation before `Interp.run` reports
`.value`); `runA` stops at the answer point, so one step is the whole run. -/

theorem answerPoint_evalFrom (m : Machine) (e : Ratchet.Expr) :
    answerPoint (evalFrom m e) = none := by
  simp [answerPoint, evalFrom]

/-- **One step to a value at the empty continuation determines the answer.** The only thing a
leaf rule ever learns from its hypothesis. -/
theorem runA_pure {m : Machine} {e : Ratchet.Expr} {m₁ : Machine} {w : Value}
    {fuel : Nat} {a : Answer} {m₀ : Machine} {rest : Nat}
    (hstep : Interp.stepFn (evalFrom m e) = .next (reCtl m₁ (.value w) []))
    (h : runA fuel (evalFrom m e) = .ans a m₀ rest) :
    a = .val w ∧ m₀ = reCtl m₁ (.value w) [] := by
  match fuel with
  | 0 => rw [runA_zero (answerPoint_evalFrom m e)] at h; exact absurd h (by simp)
  | f + 1 =>
    simp only [runA_succ (answerPoint_evalFrom m e), hstep] at h
    rw [runA_ans (m := reCtl m₁ (.value w) []) (a := .val w)
      (by simp [answerPoint, reCtl])] at h
    injection h with h1 h2 _
    exact ⟨h1.symm, h2.symm⟩

/-- The `val`-arm packaging every leaf rule repeats: `Framed`, the denotation, and the
outgoing state, at a machine that differs from `m` only in its control word. -/
theorem leafOk {Γ : Env} {τ : Ty} {m m₁ : Machine} {w : Value}
    (hm : StateOk Ratchet.ctx0 Γ .ivar0 m) (hm₁ : m₁ = m)
    (hden : denM τ (reCtl m (.value w) []) w) :
    Framed m (reCtl m₁ (.value w) []) ∧ AnsOk τ (reCtl m₁ (.value w) []) (.val w) ∧
      (∀ v, (Answer.val w) = .val v → StateOk Ratchet.ctx0 Γ .ivar0 (reCtl m₁ (.value w) [])) := by
  subst hm₁
  exact ⟨Framed_reCtl _ _ _, hden, fun _ _ => StateOk_reCtl hm _ _⟩

/-! ### The machines a frame builds, and the conformance it needs

The interpreter builds its machines in its own field order (pop, then write, then set `ctl`),
so a lemma stated in any other order is not `rfl`. These name the shapes. -/

/-- The machine `asgnK` leaves behind: the frame popped, the local written, the same value
still in flight. -/
def afterWrite (m : Machine) (x : String) (v : Value) (rest : List Kont) : Machine :=
  Interp.withCtl (({ m with kont := rest }).setLocal x v) (.value v)

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

theorem killClosOverSpine_ivar0 (x : String) (τ : Ty) :
    killClosOverSpine .ivar0 x τ = .ivar0 := rfl

/-- **Conformance across a local write.** `StateOk_setLocal` at this fragment's context: the
ivar spine is empty so `killClosOverSpine` is the identity on it, and `capStaleCtx` at `ctx0`
is `false` by computation (no `self`, no block type, no constants) — which is why
`DJudge.vasgn` does not carry that premise. -/
theorem stateOk_write {Γ : Env} {m : Machine} {x : String} {τ : Ty} {v : Value}
    (hm : StateOk Ratchet.ctx0 Γ .ivar0 m) (hd : denM τ m v)
    (hcap : capStale x τ τ = false) (halias : isAliasTy τ = false) :
    StateOk Ratchet.ctx0 (envAfter Γ x τ) .ivar0 (m.setLocal x v) := by
  have h := StateOk_setLocal hm hd hcap (by rfl)
    (ρ := τ) (by cases τ <;> simp_all [Ratchet.stripAlias, Ratchet.isAliasTy])
    (by intro y σ hy; rw [hy] at halias; simp [Ratchet.isAliasTy] at halias)
  simpa [envAfter, killClosOverSpine_ivar0] using h

/-! ### The step facts in `ctl`-form, and the safety half of a one-step rule

`§1a`'s lemmas are stated at `evalFrom m e`, which is what `SemJudgeA` needs. `SafeUnder`
quantifies over the *machine*, so it needs the same facts from a `m.ctl = .eval …` hypothesis
with the continuation left alone. Two shapes of the same three facts; the `evalFrom` ones are
the `kont = []` instances. -/

/-! ### The step facts in `ctl`-form

§1a's lemmas are stated at `evalFrom m e`, which is what `SemJudgeA` needs. `SafeUnder`
quantifies over the *machine*, so it needs the same facts from a `m.ctl = .eval …` hypothesis
with the continuation left alone. The `evalFrom` ones are the `kont = []` instances. -/

/-- A literal: one step to its value, **continuation untouched** — which is the difference
from §1a's versions, and what makes the invariant composable. -/
theorem step_lit_ctl {m : Machine} {e : Ratchet.Expr} {w : Value}
    (hc : m.ctl = .eval (toRuby e))
    (hev : Interp.evalExpr m (toRuby e) = .next (Interp.withCtl m (.value w))) :
    Interp.stepFn m = .next (reCtl m (.value w) m.kont) := by
  simp only [Interp.stepFn, hc, hev, Interp.withCtl, reCtl]

/-- A local read. -/
theorem step_var_ctl {m : Machine} {x : String} (hc : m.ctl = .eval (toRuby (.var .lvar x))) :
    Interp.stepFn m = .next (reCtl m (.value (m.getLocal x)) m.kont) :=
  step_lit_ctl hc (by simp [toRuby, toRubyVarKind, Interp.evalExpr, Interp.withCtl])

/-- A string literal, which **allocates**. -/
theorem step_str_ctl {m : Machine} {s : String} (hc : m.ctl = .eval (toRuby (.str s))) :
    Interp.stepFn m =
      .next (reCtl { m with heap := pushHeap m.heap (strObj s) }
        (.value (.ref m.heap.objs.size)) m.kont) := by
  simp only [toRuby] at hc
  simp [Interp.stepFn, hc, Interp.evalExpr, Interp.withCtl, reCtl, Builtins.allocStr,
    pushHeap, strObj, Heap.alloc]

/-- **`vasgn` pushes its frame**: the right-hand side goes into the control word and `asgnK`
onto the continuation. The one rule so far whose step is not to a value. -/
theorem step_vasgn_ctl {m : Machine} {x : String} {e : Ratchet.Expr}
    (hc : m.ctl = .eval (toRuby (.vasgn .lvar x e))) :
    Interp.stepFn m = .next (reCtl m (.eval (toRuby e)) (.asgnK .lvar x :: m.kont)) := by
  simp only [toRuby, toRubyVarKind] at hc
  simp only [Interp.stepFn, hc, Interp.evalExpr, Interp.withKont, reCtl]

/-- The frame firing on a value: pop, write, pass the value on. -/
theorem step_asgnK_val {m : Machine} {x : String} {v : Value} {rest : List Kont}
    (hc : m.ctl = .value v) (hk : m.kont = .asgnK .lvar x :: rest) :
    Interp.stepFn m = .next (afterWrite m x v rest) := by
  simp only [Interp.stepFn, hc, Interp.applyKont, hk, afterWrite]

/-- The frame firing on an **escape**: `unwind`'s default arm pops the frame and hands the
jump back. One step, and the value clause's counterpart for the escape side. -/
theorem step_asgnK_jump {m : Machine} {x : String} {j : Jump} {rest : List Kont}
    (hc : m.ctl = .jump j) (hk : m.kont = .asgnK .lvar x :: rest) :
    Interp.stepFn m = .next (reCtl m (.jump j) rest) := by
  simp only [Interp.stepFn, hc, Interp.unwind, hk]
  cases j <;> simp only [Interp.withCtl, reCtl]

/-- Delivering an answer to a continuation changes only `ctl` and `kont`, so it is a `reCtl`
and the two transports reach it. -/
theorem deliverA_eq_reCtl (a : Answer) (m : Machine) (K : List Kont) :
    deliverA a m K = reCtl m a.ctl K := rfl

theorem denM_deliverA {τ : Ty} {a : Answer} {m : Machine} {K : List Kont} {v : Value} :
    denM τ (deliverA a m K) v ↔ denM τ m v := denM_reCtl

theorem StateOk_deliverA {κ : Ctx} {Γ : Env} {I : Ty} {a : Answer} {m : Machine}
    {K : List Kont} (h : StateOk κ Γ I m) : StateOk κ Γ I (deliverA a m K) :=
  StateOk_reCtl h _ _

/-! ### The invariant's **value clause**

A value in flight under a well-typed continuation is safe. One induction over `DKontOk`, one
case per frame — which is the shape the whole layer has: adding a frame adds a case here and
nothing anywhere else.

`nil` is the base (`safeA_value_nil`: one step to `.done`). `asgnK` writes and recurses, and
the two transports it needs are exactly the two side conditions the frame carries. -/
theorem safeA_value_kontOk : ∀ {τa : Ty} {K : List Kont} {Γ : Env} {τ : Ty},
    DKontOk τa K Γ τ → ∀ {m : Machine} {v : Value}, m.ctl = .value v → m.kont = K →
      StateOk Ratchet.ctx0 Γ .ivar0 m → denM τ m v → SafeA m := by
  intro τa K Γ τ hk
  induction hk with
  | nil =>
    intro m v hc hkm _ _
    simpa [← hc, ← hkm] using safeA_value_nil m v
  | @asgnK rest Γ τ x hcap halias _ ih =>
    intro m v hc hkm hm hd fuel
    match fuel with
    | 0 => simp [Interp.run, Semantics.typeStuck]
    | f + 1 =>
      rw [run_succ, step_asgnK_val hc hkm]
      refine ih (afterWrite_ctl m x v rest) (afterWrite_kont m x v rest) ?_ ?_ f
      · exact StateOk_withCtl
          (stateOk_write (by rw [popK_eq]; exact StateOk_reCtl hm _ _)
            (by rw [popK_eq]; exact denM_reCtl.mpr hd) hcap halias) _
      · exact denM_withCtl.mpr
          (denM_setLocal (by rw [popK_eq]; exact denM_reCtl.mpr hd) hcap
            (by rw [popK_eq]; exact denM_reCtl.mpr hd))

/-- **The invariant at a one-step rule.** Everything the seven literals and `var` derive steps
to a value with the continuation untouched; the value clause takes it from there, whatever the
continuation is. No fuel arithmetic and no `UncaughtInv` — the run never reaches `unwind`.

Specialised to `Γ' = Γ`, which is every rule it serves: a literal and a local read leave the
environment alone. -/
theorem safeUnder_of_step {Γ : Env} {e : Ratchet.Expr} {τ : Ty}
    (hstep : ∀ m : Machine, StateOk Ratchet.ctx0 Γ .ivar0 m → m.ctl = .eval (toRuby e) →
      ∃ (m' : Machine) (w : Value), Interp.stepFn m = .next m' ∧ m'.ctl = .value w ∧
        m'.kont = m.kont ∧ StateOk Ratchet.ctx0 Γ .ivar0 m' ∧ denM τ m' w) :
    SafeUnder Γ e τ Γ := by
  intro τa m hm hc hk fuel
  obtain ⟨m', w, hs, hc', hk', hm', hd⟩ := hstep m hm hc
  match fuel with
  | 0 => simp [Interp.run, Semantics.typeStuck]
  | f + 1 =>
    rw [run_succ, hs]
    exact safeA_value_kontOk (hk' ▸ hk) hc' rfl hm' hd f

/-! ### Two facts both halves of a rule need

Factored because `SemJudgeA`'s half and `SafeUnder`'s half each want them, at machines that
differ only in the continuation. -/

/-- What `StateOk`'s environment component gives about a local read, with the alias stripped
away by the rule's own premise (§F29). -/
theorem denM_getLocal {κ : Ctx} {I : Ty} {Γ : Env} {m : Machine} {x : String} {τ : Ty}
    (hm : StateOk κ Γ I m) (hget : envGet? Γ x = some τ)
    (halias : isAliasTy τ = false) : denM τ m (m.getLocal x) := by
  have hden := (hm.env.1 x τ hget).1
  have hstrip : stripAlias τ = τ := by
    cases τ <;> simp_all [Ratchet.stripAlias, Ratchet.isAliasTy]
  rw [hstrip] at hden
  exact hden

/-- **The allocation a string literal performs, as an `Ext`** — and the two facts that follow
from it: the machine still conforms, and the fresh reference really is a `String`. Stated at
an arbitrary continuation, because the two halves of `SemA.strLit` need it at `[]` and at
`m.kont` respectively. -/
theorem strLit_alloc_ok {κ : Ctx} {I : Ty} {Γ : Env} {m : Machine} {s : String} (K : List Kont)
    (hm : StateOk κ Γ I m) (binary : Bool := false) :
    StateOk κ Γ I
        (reCtl { m with heap := pushHeap m.heap (strObj s binary) } (.value (.ref m.heap.objs.size)) K) ∧
      denM (.cls "String")
        (reCtl { m with heap := pushHeap m.heap (strObj s binary) } (.value (.ref m.heap.objs.size)) K)
        (.ref m.heap.objs.size) := by
  have hext : Ext m (reCtl { m with heap := pushHeap m.heap (strObj s binary) }
      (.value (.ref m.heap.objs.size)) K) :=
    (ext_push (m := m) (strObj s binary) hm.sat hm.core.basicSelf
      (fun c => by simp [strObj]) rfl rfl (by simpa [strObj] using hm.core.stringBasic)).trans
      (Ext_toReCtl _ _ _)
  refine ⟨StateOk_ext hm hext
    (stringPayloadOk_push hm.stringPayload (fun _ => ⟨s, rfl⟩))
    (arrayPayloadOk_push hm.arrayPayload (by simp [strObj]))
    (hashPayloadOk_push hm.hashPayload (by simp [strObj])) rfl, ?_⟩
  have hanc : ∀ k, ancestors (pushHeap m.heap (strObj s binary)) k = ancestors m.heap k :=
    Proof.ancestors_congr_grow hext.shapeAgree hext.size hm.sat
  have hcls : classOf (pushHeap m.heap (strObj s binary)) (.ref m.heap.objs.size) = Boot.stringId := by
    simp [classOf, pushHeap_get_self, strObj]
  show denM (.cls "String") _ _
  rw [denM, isAName, hext.classNamed?_eq, hm.core.stringNamed]
  show (ancestors (pushHeap m.heap (strObj s binary)) _).contains _ = true
  rw [hcls, hanc]
  exact hm.core.stringSelf

/-! ## §3 The obligations, rule-local

One theorem per `DJudge` rule, in the shape a `Clink.sem` field has: premises as
`SemJudgeA`, conclusion as `SemJudgeA`. The eight below are the rules whose evaluation is a
single `stepFn` step to a value at the empty continuation, so `runA_pure` is the whole
inversion and the rest is the packaging `leafOk` factors out.

Each one is the answer-typed counterpart of an `Obl.Judge.*` that `Denote/Rules/Lit.lean`
already proved, and the proof *bodies* transfer; what changes is the packaging, and it gets
**smaller** — there is no `Plain` conjunct to discharge and one outgoing `StateOk` instead of
two. The escape arm is discharged by unreachability: `runA_pure` says the answer is a value,
so `AnsOk`'s `esc` arm never arises. -/

theorem SemA.intLit {Γ : Env} {n : Int} : SemSafeA Γ (.int n) .int Γ := by
  refine ⟨?_, safeUnder_of_step (fun m hm hc =>
    ⟨_, .int n, step_lit_ctl hc rfl, rfl, rfl, StateOk_reCtl hm _ _, by simp [denM, isIntV]⟩)⟩
  intro m hm fuel a m₀ rest h
  obtain ⟨rfl, rfl⟩ := runA_pure (w := .int n) (m₁ := m) rfl h
  exact leafOk hm rfl (by simp [denM, isIntV])

theorem SemA.fltLit {Γ : Env} {b : UInt64} : SemSafeA Γ (.flt b) .float Γ := by
  refine ⟨?_, safeUnder_of_step (fun m hm hc =>
    ⟨_, .flt (Float.ofBits b), step_lit_ctl hc rfl, rfl, rfl, StateOk_reCtl hm _ _,
     by simp [denM, isFltV]⟩)⟩
  intro m hm fuel a m₀ rest h
  obtain ⟨rfl, rfl⟩ := runA_pure (w := .flt (Float.ofBits b)) (m₁ := m) rfl h
  exact leafOk hm rfl (by simp [denM, isFltV])

theorem SemA.symLit {Γ : Env} {s : String} : SemSafeA Γ (.sym s) .sym Γ := by
  refine ⟨?_, safeUnder_of_step (fun m hm hc =>
    ⟨_, .sym s, step_lit_ctl hc rfl, rfl, rfl, StateOk_reCtl hm _ _, by simp [denM, isSymV]⟩)⟩
  intro m hm fuel a m₀ rest h
  obtain ⟨rfl, rfl⟩ := runA_pure (w := .sym s) (m₁ := m) rfl h
  exact leafOk hm rfl (by simp [denM, isSymV])

theorem SemA.truLit {Γ : Env} : SemSafeA Γ .tru .bool Γ := by
  refine ⟨?_, safeUnder_of_step (fun m hm hc =>
    ⟨_, .bool true, step_lit_ctl hc rfl, rfl, rfl, StateOk_reCtl hm _ _,
     by simp [denM, isBoolV]⟩)⟩
  intro m hm fuel a m₀ rest h
  obtain ⟨rfl, rfl⟩ := runA_pure (w := .bool true) (m₁ := m) rfl h
  exact leafOk hm rfl (by simp [denM, isBoolV])

theorem SemA.flsLit {Γ : Env} : SemSafeA Γ .fls .bool Γ := by
  refine ⟨?_, safeUnder_of_step (fun m hm hc =>
    ⟨_, .bool false, step_lit_ctl hc rfl, rfl, rfl, StateOk_reCtl hm _ _,
     by simp [denM, isBoolV]⟩)⟩
  intro m hm fuel a m₀ rest h
  obtain ⟨rfl, rfl⟩ := runA_pure (w := .bool false) (m₁ := m) rfl h
  exact leafOk hm rfl (by simp [denM, isBoolV])

theorem SemA.nilLit {Γ : Env} : SemSafeA Γ .nil .nilT Γ := by
  refine ⟨?_, safeUnder_of_step (fun m hm hc =>
    ⟨_, .nil, step_lit_ctl hc rfl, rfl, rfl, StateOk_reCtl hm _ _, by simp [denM, isNilV]⟩)⟩
  intro m hm fuel a m₀ rest h
  obtain ⟨rfl, rfl⟩ := runA_pure (w := .nil) (m₁ := m) rfl h
  exact leafOk hm rfl (by simp [denM, isNilV])

/-- **Reading a local**, and the rule where the restatement paid for itself.

`DJudge.var`'s `halias` premise is here because the obligation is not provable without it:
`StateOk`'s environment component supplies `denM (stripAlias τ)`, and at a binding whose type
is a `Ty.sameAs` that is strictly weaker than the conclusion. `found-issues.md` §F29. -/
theorem SemA.var {Γ : Env} {x : String} {τ : Ty} (hget : envGet? Γ x = some τ)
    (halias : isAliasTy τ = false) : SemSafeA Γ (.var .lvar x) τ Γ := by
  refine ⟨?_, safeUnder_of_step (fun m hm hc =>
    ⟨_, m.getLocal x, step_var_ctl hc, rfl, rfl, StateOk_reCtl hm _ _,
     denM_reCtl.mpr (denM_getLocal hm hget halias)⟩)⟩
  intro m hm fuel a m₀ rest h
  obtain ⟨rfl, rfl⟩ := runA_pure (stepFn_var m x) h
  exact leafOk hm rfl (by simpa using denM_reCtl.mpr (denM_getLocal hm hget halias))

/-- **A string literal allocates**, so the machine the answer arrives at is not `m` with a new
control word — it has a longer heap. `strLit_alloc_ok` carries conformance and the type across
the push for both halves. -/
theorem SemA.strLit {Γ : Env} {s : String} : SemSafeA Γ (.str s) (.cls "String") Γ := by
  refine ⟨?_, safeUnder_of_step (fun m hm hc =>
    ⟨_, .ref m.heap.objs.size, step_str_ctl hc, rfl, rfl,
     (strLit_alloc_ok m.kont hm).1, (strLit_alloc_ok m.kont hm).2⟩)⟩
  intro m hm fuel a m₀ rest h
  obtain ⟨rfl, rfl⟩ := runA_pure (stepFn_str m s) h
  obtain ⟨hok, hden⟩ := strLit_alloc_ok (Γ := Γ) (m := m) (s := s) [] hm
  exact ⟨Framed.of_ext ((ext_push (m := m) (strObj s) hm.sat hm.core.basicSelf
      (fun c => by simp [strObj]) rfl rfl
      (by simpa [strObj] using hm.core.stringBasic)).trans (Ext_toReCtl _ _ _)),
    hden, fun _ _ => hok⟩

/-! ## §3a `vasgn` — the first composite rule

**Before adding a rule, read `Ratchet/Check.lean` §Authoring a rule.** Twice the obligation
here has refused to close because the constructor was authored with a guessed outgoing
environment and no premises (`found-issues.md` §F29, at `var` and at `vasgn`); the working
rule extracted from it — *let the transport lemma write the premises and the outgoing
environment* — is what makes the difference between this being bookkeeping and a redesign.

The rule that has a sub-expression, and therefore the first one where the two halves are
proved by different machinery:

* the **invariant half** is five lines and needs no fuel arithmetic at all. Step to the pushed
  frame, hand the premise the machine that step created, and `DKontOk.asgnK` is exactly the
  continuation typing that machine has. This is the payoff of stating the obligation over the
  machine rather than over the program: the premise applies where the rule actually uses it.
* the **answer-typed half** needs `runA_pushK` (`Denote/Sem/Answer.lean`), the answer-level
  master equation, because `SemJudgeA` is stated at `evalFrom` on both sides and `evalFrom`
  empties the continuation. It is the whole of the work below. -/

/-- The machine `vasgn` steps to **is** the sub-expression's machine under one pushed frame.
`rfl`, and worth a name because it is what lets `runA_pushK` apply. -/
theorem vasgn_step_pushK (m : Machine) (x : String) (e : Ratchet.Expr) :
    reCtl (evalFrom m (.vasgn .lvar x e)) (.eval (toRuby e))
        (.asgnK .lvar x :: (evalFrom m (.vasgn .lvar x e)).kont)
      = pushK [.asgnK .lvar x] (evalFrom m e) := rfl

theorem catchFree_asgnK (x : String) :
    RubyCore.Proof.CatchFree [.asgnK .lvar x] := by
  intro k hk t
  rcases List.mem_cons.mp hk with rfl | hmem
  · simp
  · exact absurd hmem (by simp)

theorem SemA.vasgn {Γ Γ₁ : Env} {x : String} {e : Ratchet.Expr} {τ : Ty}
    (hprem : SemSafeA Γ e τ Γ₁) (hcap : capStale x τ τ = false) (halias : isAliasTy τ = false) :
    SemSafeA Γ (.vasgn .lvar x e) τ (envAfter Γ₁ x τ) := by
  obtain ⟨hsem, hsafe⟩ := hprem
  refine ⟨?_, ?_⟩
  · -- the answer-typed half
    intro m hm fuel a m₀ rest h
    match fuel with
    | 0 =>
      rw [runA_zero (answerPoint_evalFrom m _)] at h; exact absurd h (by simp)
    | f + 1 =>
      rw [runA_succ (answerPoint_evalFrom m _),
        step_vasgn_ctl (m := evalFrom m (.vasgn .lvar x e)) rfl] at h
      simp only at h
      rw [vasgn_step_pushK m x e, runA_pushK _ (catchFree_asgnK x) f (evalFrom m e)] at h
      cases hr : runA f (evalFrom m e) with
      | halt hh => rw [hr] at h; exact absurd h (by cases hh <;> simp [resOutA, Halt.underK])
      | oof m₂ => rw [hr] at h; exact absurd h (by simp [resOutA])
      | ans a₁ m₁ r₁ =>
        rw [hr] at h
        simp only [resOutA] at h
        obtain ⟨hfr, hans, hout⟩ := hsem m hm f a₁ m₁ r₁ hr
        cases a₁ with
        | val v =>
          have hm₁ : StateOk Ratchet.ctx0 Γ₁ .ivar0 m₁ := hout v rfl
          have hd : denM τ m₁ v := hans
          match r₁ with
          | 0 => rw [runA_zero (by simp [answerPoint, deliverA])] at h; exact absurd h (by simp)
          | g + 1 =>
            rw [runA_succ (by simp [answerPoint, deliverA]),
              step_asgnK_val (m := deliverA (.val v) m₁ [.asgnK .lvar x]) rfl rfl] at h
            simp only at h
            rw [runA_ans (m := afterWrite (deliverA (.val v) m₁ [.asgnK .lvar x]) x v [])
              (a := .val v) (by simp [answerPoint, afterWrite, Interp.withCtl])] at h
            injection h with h1 h2 _
            cases h1; cases h2
            refine ⟨?_, ?_, ?_⟩
            · exact hfr.trans
                ((Framed_reCtl m₁ (.value v) []).trans
                  ((Framed_setLocal _ x v).trans (Framed_withCtl _ (.value v))))
            · show denM τ _ v
              exact denM_withCtl.mpr (denM_setLocal
                (by rw [popK_eq]; exact denM_reCtl.mpr (denM_deliverA.mpr hd)) hcap
                (by rw [popK_eq]; exact denM_reCtl.mpr (denM_deliverA.mpr hd)))
            · intro w hw
              injection hw with hw; subst hw
              exact StateOk_withCtl (stateOk_write
                (by rw [popK_eq]; exact StateOk_reCtl (StateOk_deliverA hm₁) _ _)
                (by rw [popK_eq]; exact denM_reCtl.mpr (denM_deliverA.mpr hd)) hcap halias) _
        | esc j =>
          match r₁ with
          | 0 => rw [runA_zero (by simp [answerPoint, deliverA])] at h; exact absurd h (by simp)
          | g + 1 =>
            rw [runA_succ (by simp [answerPoint, deliverA]),
              step_asgnK_jump (m := deliverA (.esc j) m₁ [.asgnK .lvar x]) rfl rfl] at h
            simp only at h
            rw [runA_ans (m := reCtl (deliverA (.esc j) m₁ [.asgnK .lvar x]) (.jump j) [])
              (a := .esc j) (by simp [answerPoint, reCtl])] at h
            injection h with h1 h2 _
            cases h1; cases h2
            refine ⟨hfr.trans (Framed_reCtl _ _ _), ?_, ?_⟩
            · show EscOk _ j
              cases j <;> simpa [AnsOk, EscOk, reCtl, deliverA] using hans
            · intro w hw; exact absurd hw (by simp)
  · -- the invariant half
    intro τa m hm hc hk fuel
    match fuel with
    | 0 => simp [Interp.run, Semantics.typeStuck]
    | f + 1 =>
      rw [run_succ, step_vasgn_ctl hc]
      exact hsafe τa _ (StateOk_reCtl hm _ _) rfl (.asgnK hcap halias hk) f

/-! ## §4 Composite rules

`runA_pushK` is proved in `Denote/Sem/Answer.lean`. Sequence and conditional proofs live
in `Sequence.lean` and `Branch.lean`; primitive evaluation, dispatch, and allocation are
split across `Primitive*.lean`. `JoinState.lean` now proves the binding join, after correcting
the alias-normalization counterexample. See implementation-notes clink 74. -/

#print axioms SemA.intLit
#print axioms SemA.fltLit
#print axioms SemA.symLit
#print axioms SemA.truLit
#print axioms SemA.flsLit
#print axioms SemA.nilLit
#print axioms SemA.var
#print axioms SemA.vasgn
#print axioms SemA.strLit
#print axioms runA_pure

end Ratchet.Denote.Typed
