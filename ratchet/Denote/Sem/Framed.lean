import Denote.Sem.State
import Denote.Sem.FramePres

/-!
# `Denote/Sem/Framed.lean` — the parallel judgment, semantically

Eight definitions, one per member of `Ratchet/Judge.lean`'s mutual family, each with **the
same signature as its syntactic twin** and a meaning instead of a set of constructors.

That signature match is not cosmetic — it is the mechanism. Because `SemJudge` has exactly
`Judge`'s type, a `Judge` constructor's type becomes a well-formed proposition about the
semantics by *substituting one constant for another*, which is what
`Denote/Sem/Obligations.lean` does: the 83 proof obligations of this ratchet are not
transcribed by hand, they are derived from the inductive. Change a rule in
`Ratchet/Judge.lean` and its obligation changes with it; add a rule and the ratchet's
denominator grows on its own.

## What `SemJudge κ Γ I e τ Γ' I'` says

> For every machine `m` conformant with `(κ, Γ, I)`: if evaluating `e` from `m` returns `v`
> in machine `m'`, then the frame stack is where it started, `v` is in `τ`'s denotation **at
> `m'`**, and `m'` is conformant with `(κ, Γ', I')`.

Four things chosen, each of which could have gone another way.

1. **Partial correctness.** Only runs that reach `.value` impose anything, for the reason
   `Denote/Sem/State.lean`'s `Evals` docstring gives at length. Stuck-freedom is the other
   axis (`StuckFree`), deliberately not folded in.
2. **`τ` at the post-machine, `Γ`/`I` conformance at both ends.** Evaluating `e` can allocate,
   assign, reopen a class; the denotation's nominal arms are `isA` *at the heap they are
   given*, so checking `τ` against `m` rather than `m'` would be checking against a heap that
   no longer exists. Same argument as the arrow's codomain (`Denote/Den.lean`).
3. **The outgoing state is a conclusion, not a hypothesis.** `Judge` threads `Γ → Γ'` and
   `I → I'` as *outputs*, so their semantic counterpart belongs on the right of the
   implication. This is what makes the rules compose: `JudgeSeq.cons`'s obligation can feed
   the first statement's conclusion into the second's hypothesis, and nothing else needs to
   know how the environment got there.
4. **`Framed m m'`** — two facts about what the evaluation left alone, bundled because they
   are proved and consumed in the same places (see the structure's own docstring).

`κ` is *not* threaded. It matches `Judge`, where the context is an input to every rule and
`JudgeSeq.cons`/`Ctx.afterStmt` is the one place it grows — so the growth shows up in the
obligation for that rule and nowhere else.

## The companions

`SemJudgeAll`/`SemJudgeKw`/`SemJudgePairs` describe evaluating a *list* in Ruby's left-to-right
order, so each threads the state through and each is defined over the same `Evals` primitive
applied elementwise. `SemJudgeSeq` is the statement sequence. `SemJudgeConsts` and
`SemJudgeNested` are the two class-body relations whose syntactic twins carry no `Env`
threading at all, and their semantic readings are correspondingly about the *heap after the
declaration*, not about a value — see each one's docstring.

None of the 83 obligations is discharged yet; this file is the vocabulary they are written in.
`Denote/Ladder.lean` counts.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ### `Plain` — what the *syntactic* judgment implies and the semantic one has to say

`Ratchet.Expr` has three shapes that are **not expressions**: `.splat`, `.kwargs` and `.fwd`
are argument-list *syntax*, and no `Judge` rule concludes about one (`grep` finds none). So a
`JudgeAll` derivation over a call's arguments implies each argument is a real expression — for
free, from the shape of the inductive.

`SemJudgeAll` implies no such thing: it is a ∀ over runs, and its hypothesis `EvalsAll` is
simply *unsatisfiable* at a splat (`evalExpr`'s `.splat` arm gates), so the premise is vacuous
and carries nothing. That gap makes every call rule's obligation **false**: `startArgs` routes
a splat through `.argsSplatK` and `spreadA`, so the call's run can return a value while the
argument premise says nothing at all about the values it delivered. `Judge.callNever` is the
smallest instance — its `argTys.contains .never` premise is about types the run never produced.

So the semantic judgment carries plainness explicitly. It is a conjunct rather than a
hypothesis because every rule's conclusion expression *has* a plain head, so every rung
discharges it with `trivial` — and every rule that consumes a sub-judgment gets it for free,
which is exactly the inference the syntactic inductive was making structurally. -/

/-- `e` is an expression, not argument-list syntax. -/
def Plain : Ratchet.Expr → Prop
  | .splat _ => False
  | .kwargs _ => False
  | .fwd => False
  | _ => True

def PlainAll (es : List Ratchet.Expr) : Prop := ∀ e ∈ es, Plain e

/-- **What an evaluation leaves undisturbed.** Both fields are conclusions of every semantic
judgment, and both are there because a later part of the *same* judgment would otherwise be a
claim about the wrong machine.

`stack` is frame balance: `Γ` describes the *current frame*'s locals, so a conclusion about
`Γ'` at a machine with a different frame on top would be a claim about the wrong bindings.
Every rule that pushes a frame (a call, a block) has to restore it, and stating that per-rule
is how it gets proved rather than assumed.

`cls` is **once a class, always a class** — the transport the call rules need and cannot get
any other way. A send evaluates its receiver *first*, so by the time the dispatch reads the
heap, the receiver's type was established at a machine several evaluations ago; nothing in
`StateOk` can bridge that, because `StateOk` is a predicate on one machine. `denM (.clsOf cn)`
is not preserved in general (a `Class.new` can rebind the constant, so `classNamed?` moves),
but the one fact a dispatch at a class receiver actually reads — that the receiver *is* a class
object — is monotone in the model, and a `Judge` rule with a `.clsOf` receiver premise
(`caseEqQuery`, `clsToS`, `new`) is exactly a rule that needs it carried across its own
argument list.

Stating it here rather than proving a monotonicity theorem over `stepFn` is deliberate, and it
is the same trade the `stack` conjunct makes: the theorem would have to hold for every arm of
`Builtins.run`, including bids no rung will ever reach, whereas the conjunct is discharged
per-rule and each rule pays only for the bids it dispatches to.

It is also, as invariants go, cheap to discharge: `reCtl`/`withCtl`/`setLocal` do not touch the
heap at all, an `Ext` pins `classPayload?` outright, and a rule with sub-judgments composes its
premises' fields by `Framed.trans` — which is where the transport comes from, since a send's
argument premise runs from the machine the *receiver* left behind.

`frames` adds the missing caller-isolation contract (clink 87). Equal heaps/stacks
alone permit arbitrary damage to inactive locals. `FramePres` preserves all inactive old
frames when the activation has no captured parent, and preserves that guard for composition.
Captured activations may still write through their captured chain. -/
structure Framed (m m' : Machine) : Prop where
  stack : m'.stack = m.stack
  cls : ∀ k, (m.heap.classPayload? k).isSome = true → (m'.heap.classPayload? k).isSome = true
  /-- A receiver evaluated before its arguments keeps its nominal type while they run. -/
  nominal : ∀ v n, isAName m.heap v n = true → isAName m'.heap v n = true
  /-- Retained collection elements survive later evaluations in the nonmutating fragment.
      Captured-frame types are excluded: a local write can invalidate them. -/
  firstOrder : ∀ τ, FirstOrder τ = true → ∀ v, denM τ m v → denM τ m' v
  /-- Uncaptured activations cannot modify inactive caller frames. -/
  frames : FramePres m m'

theorem Framed.refl (m : Machine) : Framed m m :=
  ⟨rfl, fun _ h => h, fun _ _ h => h, fun _ _ _ h => h, .refl m⟩

theorem Framed.trans {m₁ m₂ m₃ : Machine} (h₁ : Framed m₁ m₂) (h₂ : Framed m₂ m₃) :
    Framed m₁ m₃ :=
  ⟨by rw [h₂.stack, h₁.stack], fun k h => h₂.cls k (h₁.cls k h),
    fun v n h => h₂.nominal v n (h₁.nominal v n h),
    fun τ ht v h => h₂.firstOrder τ ht v (h₁.firstOrder τ ht v h),
    h₁.frames.trans h₂.frames h₁.stack⟩

/-- Equal heaps/stacks do not imply frame preservation; callers must supply it explicitly. -/
theorem Framed.of_heap_stack {m m' : Machine} (hh : m'.heap = m.heap)
    (hs : m'.stack = m.stack) (hf : FramePres m m') : Framed m m' :=
  ⟨hs, fun k h => by rw [hh]; exact h, fun v n h => by rw [hh]; exact h,
    fun _ ht _ h => (denM_heap_only ht hh.symm).mp h, hf⟩

/-! ## The judgment that lived here, and why the shape had to go

`SemJudge` and its seven companions — the **value-shaped** semantic judgment, *if the run
returns a value, the value is in the type* — were deleted in clink 68, along with
`EvalsAll`/`DenAllAt`/`DenPairsAt` and the 48 obligations discharged against them.

The reason is not that the proofs were wrong; they were correct, axiom-clean, and several cost
a session each. It is that the **statement** has no progress content, and that was proved
rather than argued: a program with no value outcome satisfies every `SemJudge` vacuously, so a
rule could be "justified" while the program it types raises `TypeError`. The replacement is
`Denote/Typed/JudgeA.lean`'s `SemJudgeA`, whose hypothesis is an **answer** and whose
conclusion carries whether the run reached a type-stuck outcome.

Keeping the old shape available would have let a future rule acquire a proof of the weaker
statement and count, which is the one failure mode the clink discipline exists to prevent — so
the definition goes rather than being marked deprecated. The refutation itself
(`not_semJudgeImpliesStuckFree`, and the `evals_brk_never` witness) is recorded in
`found-issues.md` §F27, `AGENTS.md`, and `Denote/Typed/JudgeA.lean`'s header.

**`Framed` survives, above**, and is the one piece the new judgment reuses: two facts about
what an evaluation left alone (the frame stack, and every class payload still being a class
payload), which every rule's conclusion needs and which compose by `Framed.trans`. -/


end Ratchet.Denote
