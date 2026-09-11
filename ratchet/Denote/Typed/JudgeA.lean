import Ratchet.Check
import Denote.Sem.SafeKont
import Denote.Sem.Transport
import Denote.Sem.Alloc
import Denote.Sanity

/-!
# `Denote/Typed/JudgeA.lean` — the answer-typed semantic judgment for `DJudge`, and its obligations

`../docs/semantics/answer-typed-schema.md` §3.1, at `Ratchet/Check.lean`'s index shape. This
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
(`answer-typed-schema.md` §9.2 warns that `safe_pushK` is a per-rule tool and cannot be a
whole-machine invariant; at an empty base kont the warning does not bite).

## What is taken from the old checker, and it is not the checker

`Ratchet/Validate.lean` is imported transitively (via `Denote/Sanity.lean`) for exactly two
things: the **empty context value** `ctx0`, because `StateOk` is `Ctx`-indexed and `Ctx` lives
in `Ratchet/Judge.lean`, and `stateOk_boot`, the `#guard`ed conformance witness for the
prelude-booted machine. Neither is `chk`, and nothing here mentions `Judge` or `validate`.

## What is proved here, and what is named and not

Proved, rule-local and axiom-clean: the **seven literals** and **`var`** — every `DJudge` rule
whose evaluation is a single `stepFn` step to a value at the empty continuation.

Not proved, and the reason is one missing lemma rather than eight: `seq`, `vasgn`, `prim` and
`if'` all need to decompose a run that happens **under a pushed frame**, and the decomposition
exists only for `Interp.run` (`run_pushK`) and not for `runA`. §4 states the missing equation
as a named `Prop` (`RunAPushK`) before anything is proved under it, per `HANDOFF.md`'s working
rule. It is the same induction as `run_pushK`, at the `runA` level.
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
(`answer-typed-schema.md` §7), which does not exist. So safety is a **second obligation
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
(`Denote/Clink/Spec.lean` §3), so a derivation cannot be *inverted* — there is no `cases` on
it, and `preserved` cannot be proved by case analysis over the derivation the way
`Denote/Proto/Safety.lean` did over an inductive `PJudge`. What the encoding gives instead is
elimination into any family closed under the rules, so **choosing the family to be "the
invariant holds here" *is* the inductive proof**, with one case per rule — and those cases are
exactly the clink fields. Safety of every program the fragment types then follows by
instantiating at the empty continuation.

Stated as safety of the **machine** (`SafeA m`) rather than of the program, so that it
composes: a rule that pushes a frame consumes its premise at a machine whose continuation is
the frame it pushed, which is what `DKontOk`'s frame clauses will say. -/

/-- **The continuation typing.** `DKontOk τa K Γ τ`: the continuation `K` accepts a value of
type `τ` at environment `Γ`, and the run as a whole will answer at type `τa`.

One constructor today, because **no registered rule pushes a frame** — the eight are the seven
literals and a local read. A frame joins when the rule that pushes it registers: `vasgn` will
add `asgnK`, with a value clause (write and pass on) and an escape clause (pop and pass on).
`probes/kont_census.lean` priced the full set at 36 of `Kont`'s 49 constructors before it was
deleted with the corpus it walked; that number is the target, one rule at a time. -/
inductive DKontOk (τa : Ty) : List Kont → Env → Ty → Prop
  /-- **The empty continuation accepts exactly the program's own type.** Not "anything": with
      `nil` accepting any type the invariant proves safety and says nothing about types, which
      is the prototype's second finding and the reason `τa` is an index at all. -/
  | nil {Γ : Env} : DKontOk τa [] Γ τa

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
def strObj (s : String) : Object := { klass := Boot.stringId, payload := .str s }

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

/-! ### The step facts in `ctl`-form, and the safety half of a one-step rule

`§1a`'s lemmas are stated at `evalFrom m e`, which is what `SemJudgeA` needs. `SafeUnder`
quantifies over the *machine*, so it needs the same facts from a `m.ctl = .eval …` hypothesis
with the continuation left alone. Two shapes of the same three facts; the `evalFrom` ones are
the `kont = []` instances. -/

/-- `DKontOk`'s inversion. One constructor, so: the continuation is empty and the answer type
is the expression's. As frames join, this becomes a `cases` with a clause each. -/
theorem dKontOk_inv {τa : Ty} {K : List Kont} {Γ : Env} {τ : Ty} (h : DKontOk τa K Γ τ) :
    K = [] ∧ τa = τ := by
  cases h; exact ⟨rfl, rfl⟩

/-- A literal: one step to its value, **continuation untouched** (which is the difference from
§1a's `evalFrom` versions, and what makes the invariant composable). -/
theorem step_lit_ctl {m : Machine} {e : Ratchet.Expr} {w : Value}
    (hc : m.ctl = .eval (toRuby e))
    (hev : Interp.evalExpr m (toRuby e) = .next (Interp.withCtl m (.value w))) :
    Interp.stepFn m = .next (reCtl m (.value w) m.kont) := by
  simp only [Interp.stepFn, hc, hev, Interp.withCtl, reCtl]

/-- A local read. -/
theorem step_var_ctl {m : Machine} {x : String} (hc : m.ctl = .eval (toRuby (.var .lvar x))) :
    Interp.stepFn m = .next (reCtl m (.value (m.getLocal x)) m.kont) :=
  step_lit_ctl hc (by simp [toRuby, toRubyVarKind, Interp.evalExpr, Interp.withCtl])

/-- A string literal, which **allocates**. Stated in terms of `Builtins.allocStr`'s own result
rather than in terms of `pushHeap`: the invariant only needs *some* machine and value for the
step to land on (`safeUnder_of_step`'s existential), so relating the fresh heap to `pushHeap`
would be work spent to state something nothing here reads. §1a's `stepFn_str` does relate
them, because `SemJudgeA`'s half needs the `Ext`. -/
theorem step_str_ctl {m : Machine} {s : String} (hc : m.ctl = .eval (toRuby (.str s))) :
    Interp.stepFn m =
      .next (reCtl (Builtins.allocStr m s).2 (.value (Builtins.allocStr m s).1) m.kont) := by
  simp only [toRuby] at hc
  simp [Interp.stepFn, hc, Interp.evalExpr, Interp.withCtl, reCtl, Builtins.allocStr]

/-- **The invariant at a one-step rule.** Everything the registered fragment derives steps to
a value with the continuation untouched; `DKontOk` has only `nil`, so that continuation is
empty and `safeA_value_nil` finishes it. Two fuel cases, and no `UncaughtInv` — the run never
reaches `unwind` at all.

As frames join `DKontOk`, this gains the clause that delivers a value to each, which is the
invariant's value clause and the place where the rule that pushed the frame pays for it. -/
theorem safeUnder_of_step {Γ Γ' : Env} {e : Ratchet.Expr} {τ : Ty}
    (hstep : ∀ m : Machine, m.ctl = .eval (toRuby e) → ∃ (m₁ : Machine) (w : Value),
      Interp.stepFn m = .next (reCtl m₁ (.value w) m.kont)) :
    SafeUnder Γ e τ Γ' := by
  intro τa m _ hc hk fuel
  obtain ⟨m₁, w, hs⟩ := hstep m hc
  obtain ⟨hk0, -⟩ := dKontOk_inv hk
  rw [hk0] at hs
  match fuel with
  | 0 => simp [Interp.run, Semantics.typeStuck]
  | f + 1 => rw [run_succ, hs]; exact safeA_value_nil m₁ w f

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
  refine ⟨?_, safeUnder_of_step (fun m hc => ⟨m, .int n, step_lit_ctl hc rfl⟩)⟩
  intro m hm fuel a m₀ rest h
  obtain ⟨rfl, rfl⟩ := runA_pure (w := .int n) (m₁ := m) rfl h
  exact leafOk hm rfl (by simp [denM, isIntV])

theorem SemA.fltLit {Γ : Env} {b : UInt64} : SemSafeA Γ (.flt b) .float Γ := by
  refine ⟨?_, safeUnder_of_step (fun m hc => ⟨m, .flt (Float.ofBits b), step_lit_ctl hc rfl⟩)⟩
  intro m hm fuel a m₀ rest h
  obtain ⟨rfl, rfl⟩ := runA_pure (w := .flt (Float.ofBits b)) (m₁ := m) rfl h
  exact leafOk hm rfl (by simp [denM, isFltV])

theorem SemA.symLit {Γ : Env} {s : String} : SemSafeA Γ (.sym s) .sym Γ := by
  refine ⟨?_, safeUnder_of_step (fun m hc => ⟨m, .sym s, step_lit_ctl hc rfl⟩)⟩
  intro m hm fuel a m₀ rest h
  obtain ⟨rfl, rfl⟩ := runA_pure (w := .sym s) (m₁ := m) rfl h
  exact leafOk hm rfl (by simp [denM, isSymV])

theorem SemA.truLit {Γ : Env} : SemSafeA Γ .tru .bool Γ := by
  refine ⟨?_, safeUnder_of_step (fun m hc => ⟨m, .bool true, step_lit_ctl hc rfl⟩)⟩
  intro m hm fuel a m₀ rest h
  obtain ⟨rfl, rfl⟩ := runA_pure (w := .bool true) (m₁ := m) rfl h
  exact leafOk hm rfl (by simp [denM, isBoolV])

theorem SemA.flsLit {Γ : Env} : SemSafeA Γ .fls .bool Γ := by
  refine ⟨?_, safeUnder_of_step (fun m hc => ⟨m, .bool false, step_lit_ctl hc rfl⟩)⟩
  intro m hm fuel a m₀ rest h
  obtain ⟨rfl, rfl⟩ := runA_pure (w := .bool false) (m₁ := m) rfl h
  exact leafOk hm rfl (by simp [denM, isBoolV])

theorem SemA.nilLit {Γ : Env} : SemSafeA Γ .nil .nilT Γ := by
  refine ⟨?_, safeUnder_of_step (fun m hc => ⟨m, .nil, step_lit_ctl hc rfl⟩)⟩
  intro m hm fuel a m₀ rest h
  obtain ⟨rfl, rfl⟩ := runA_pure (w := .nil) (m₁ := m) rfl h
  exact leafOk hm rfl (by simp [denM, isNilV])

/-- **Reading a local**, and the rule where the restatement paid for itself.

`DJudge.var`'s `halias` premise is here because the obligation is not provable without it:
`StateOk`'s environment component supplies `denM (stripAlias τ)`, and at a binding whose type
is a `Ty.sameAs` that is strictly weaker than the conclusion. `found-issues.md` §F29. -/
theorem SemA.var {Γ : Env} {x : String} {τ : Ty} (hget : envGet? Γ x = some τ)
    (halias : isAliasTy τ = false) : SemSafeA Γ (.var .lvar x) τ Γ := by
  refine ⟨?_, safeUnder_of_step (fun m hc => ⟨m, m.getLocal x, step_var_ctl hc⟩)⟩
  intro m hm fuel a m₀ rest h
  obtain ⟨rfl, rfl⟩ := runA_pure (stepFn_var m x) h
  refine leafOk hm rfl ?_
  have hden := (hm.env.1 x τ hget).1
  have hstrip : stripAlias τ = τ := by cases τ <;> simp_all [stripAlias, isAliasTy]
  rw [hstrip] at hden
  simpa using denM_reCtl.mpr hden

/-- **A string literal allocates**, so the machine the answer arrives at is not `m` with a new
control word — it has a longer heap. `Ext` is what carries conformance and the denotation
across the push, exactly as in `Denote/Rules/Lit.lean`'s value-shaped twin. -/
theorem SemA.strLit {Γ : Env} {s : String} : SemSafeA Γ (.str s) (.cls "String") Γ := by
  refine ⟨?_, safeUnder_of_step (fun m hc =>
    ⟨(Builtins.allocStr m s).2, (Builtins.allocStr m s).1, step_str_ctl hc⟩)⟩
  intro m hm fuel a m₀ rest h
  obtain ⟨rfl, rfl⟩ := runA_pure (stepFn_str m s) h
  have hext : Ext m (reCtl { m with heap := pushHeap m.heap (strObj s) }
      (.value (.ref m.heap.objs.size)) []) :=
    (ext_push (m := m) (strObj s) hm.sat hm.core.basicSelf
      (fun c => by simp [strObj]) rfl rfl (by simpa [strObj] using hm.core.stringBasic)).trans
      (Ext_toReCtl _ _ _)
  refine ⟨Framed.of_ext hext, ?_, fun _ _ => StateOk_ext hm hext⟩
  have hanc : ∀ k, ancestors (pushHeap m.heap (strObj s)) k = ancestors m.heap k :=
    Proof.ancestors_congr_grow hext.shapeAgree hext.size hm.sat
  have hcls : classOf (pushHeap m.heap (strObj s)) (.ref m.heap.objs.size) = Boot.stringId := by
    simp [classOf, pushHeap_get_self, strObj]
  show denM (.cls "String") _ _
  rw [denM, isAName, hext.classNamed?_eq, hm.core.stringNamed]
  show (ancestors (pushHeap m.heap (strObj s)) _).contains _ = true
  rw [hcls, hanc]
  exact hm.core.stringSelf

/-! ## §4 The missing equation, named before anything is proved under it

`HANDOFF.md`'s working rule: write the layer's target down as a named `Prop` first.
`FrameLocal.lean`'s 532 lines were proved for a target that was never stated, and the target
turned out false.

`seq`, `vasgn`, `prim` and `if'` all need to decompose a run that happens **under a pushed
frame**: `.vasgn x e` steps to `pushK [.asgnK .lvar x] (evalFrom m e)`, and the premise is
about `evalFrom m e` with an empty continuation. The decomposition exists for `Interp.run`
(`Denote/Sem/Answer.lean`'s `run_pushK`, the master equation) and **not for `runA`**, which is
what the answer-typed obligations are stated over.

So one lemma gates four rules. It is the same induction as `run_pushK`, at the `runA` level,
and `answer-typed-schema.md` §5's delete list already anticipates it (`run_split`'s body
becoming a derivation from `run_pushK`).

What each of the four needs *besides* it, so nobody prices them wrong:

* `vasgn` — nothing. `run_pushK`'s `CatchFree` side condition is free here (`[.asgnK …]`), and
  `StateOk_setLocal` is proved.
* `seq` — nothing beyond the same decomposition per statement.
* `if'` — nothing. `Denote/Join.lean`'s `denM_joinT_left`/`_right` and
  `Denote/JoinState.lean`'s environment/spine join are **already proved**; those two files were
  kept through the clink-68 sweep for this row.
* `prim` — one conformance fact per `DPrim` row (7 of them), each saying that CRuby's builtin
  really returns a value of the row's result type from the prelude-booted heap. This is the
  only one of the four whose cost grows with the table, which is why the table has 7 rows and
  not 90. -/

/-- What running under a pushed continuation does to an `ARes` — the answer-level counterpart
of `Denote/Sem/Answer.lean`'s `ARes.out`. The `ans` arm is the whole content: the inner
computation reaches an answer, and the outer run continues by delivering that answer to `K`
with the fuel that was left. -/
def resOutA (K : List Kont) : ARes → ARes
  | .ans a m rest => runA rest (deliverA a m K)
  | .halt h => .halt h
  | .oof m => .oof (pushK K m)

/-- **`RunAPushK` — the answer-level master equation.** Not proved. When it is, `SemA.vasgn`,
`SemA.seq`, `SemA.prim` and `SemA.if'` follow by the same argument
`Denote/Rules/VasgnAnswer.lean` used on the stuck axis, where the `esc` clause was **four
lines** against the projection route's 22.

Stated for an arbitrary `CatchFree K` rather than for `[.asgnK …]`, per Norm A: the four rules
push different frames and each would otherwise need its own copy. -/
def RunAPushK : Prop :=
  ∀ (K : List Kont), RubyCore.Proof.CatchFree K →
    ∀ (fuel : Nat) (m : Machine), runA fuel (pushK K m) = resOutA K (runA fuel m)

#print axioms SemA.intLit
#print axioms SemA.fltLit
#print axioms SemA.symLit
#print axioms SemA.truLit
#print axioms SemA.flsLit
#print axioms SemA.nilLit
#print axioms SemA.var
#print axioms SemA.strLit
#print axioms runA_pure

end Ratchet.Denote.Typed
