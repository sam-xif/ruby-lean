import Ratchet.Check
import Denote.Sem.SafeKont
import Denote.Rules.Core
import Denote.Rules.Lit
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

`Denote/Rules/Lit.lean` is imported for its `stepFn_var`/`stepFn_str`/`strObj` — facts about
`Interp.stepFn`, not about any judgment, and reusable for that reason.

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

theorem SemA.intLit {Γ : Env} {n : Int} : SemJudgeA Γ (.int n) .int Γ := by
  intro m hm fuel a m₀ rest h
  obtain ⟨rfl, rfl⟩ := runA_pure (w := .int n) (m₁ := m) rfl h
  exact leafOk hm rfl (by simp [denM, isIntV])

theorem SemA.fltLit {Γ : Env} {b : UInt64} : SemJudgeA Γ (.flt b) .float Γ := by
  intro m hm fuel a m₀ rest h
  obtain ⟨rfl, rfl⟩ := runA_pure (w := .flt (Float.ofBits b)) (m₁ := m) rfl h
  exact leafOk hm rfl (by simp [denM, isFltV])

theorem SemA.symLit {Γ : Env} {s : String} : SemJudgeA Γ (.sym s) .sym Γ := by
  intro m hm fuel a m₀ rest h
  obtain ⟨rfl, rfl⟩ := runA_pure (w := .sym s) (m₁ := m) rfl h
  exact leafOk hm rfl (by simp [denM, isSymV])

theorem SemA.truLit {Γ : Env} : SemJudgeA Γ .tru .bool Γ := by
  intro m hm fuel a m₀ rest h
  obtain ⟨rfl, rfl⟩ := runA_pure (w := .bool true) (m₁ := m) rfl h
  exact leafOk hm rfl (by simp [denM, isBoolV])

theorem SemA.flsLit {Γ : Env} : SemJudgeA Γ .fls .bool Γ := by
  intro m hm fuel a m₀ rest h
  obtain ⟨rfl, rfl⟩ := runA_pure (w := .bool false) (m₁ := m) rfl h
  exact leafOk hm rfl (by simp [denM, isBoolV])

theorem SemA.nilLit {Γ : Env} : SemJudgeA Γ .nil .nilT Γ := by
  intro m hm fuel a m₀ rest h
  obtain ⟨rfl, rfl⟩ := runA_pure (w := .nil) (m₁ := m) rfl h
  exact leafOk hm rfl (by simp [denM, isNilV])

/-- **Reading a local**, and the rule where the restatement paid for itself.

`DJudge.var`'s `halias` premise is here because the obligation is not provable without it:
`StateOk`'s environment component supplies `denM (stripAlias τ)`, and at a binding whose type
is a `Ty.sameAs` that is strictly weaker than the conclusion. `found-issues.md` §F29. -/
theorem SemA.var {Γ : Env} {x : String} {τ : Ty} (hget : envGet? Γ x = some τ)
    (halias : isAliasTy τ = false) : SemJudgeA Γ (.var .lvar x) τ Γ := by
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
theorem SemA.strLit {Γ : Env} {s : String} : SemJudgeA Γ (.str s) (.cls "String") Γ := by
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
becoming a derivation from `run_pushK`). -/

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
