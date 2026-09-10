import Denote.Sem.State

/-!
# `Denote/Sem/Judge.lean` — the parallel judgment, semantically

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
argument premise runs from the machine the *receiver* left behind. -/
structure Framed (m m' : Machine) : Prop where
  stack : m'.stack = m.stack
  cls : ∀ k, (m.heap.classPayload? k).isSome = true → (m'.heap.classPayload? k).isSome = true

theorem Framed.refl (m : Machine) : Framed m m := ⟨rfl, fun _ h => h⟩

theorem Framed.trans {m₁ m₂ m₃ : Machine} (h₁ : Framed m₁ m₂) (h₂ : Framed m₂ m₃) :
    Framed m₁ m₃ :=
  ⟨by rw [h₂.stack, h₁.stack], fun k h => h₂.cls k (h₁.cls k h)⟩

/-- The two machine updates that keep the heap and the frame stack: `Framed` is free at both. -/
theorem Framed.of_heap_stack {m m' : Machine} (hh : m'.heap = m.heap)
    (hs : m'.stack = m.stack) : Framed m m' :=
  ⟨hs, fun k h => by rw [hh]; exact h⟩

/-! ### Outgoing conformance, at both ends of a rule's context

(`context-splitting.md` §3, and the resolution of L268's "`StateOk` transports in neither direction").

Threading gave `Judge` an outgoing context `κ'`, and the obvious semantic reading is to move
`SemJudge`'s conclusion to it — §8.1 step 4 says exactly that. Moving it is not enough, and the
measurement is sharp: it *weakens* the premise that every non-declaring rule lives on. Those
rules consume their sub-derivation's outgoing conformance and republish it at their own `κ`, and
with the conclusion at `κ'` alone they would receive it at `κ.afterStmt e τ` instead. Getting
back is the **down-transport**, which §3 prices at "antitone, one line" and which is *false* for
`ConstsOk`: `extendConsts` is `envSet`, which **overwrites**, so a statement that rebinds a
constant at a different type falsifies the old `ConstsOk` at the new machine. §F18's
`constAsgnOk` is precisely the premise that rules that out, and it lives on the *syntactic*
`Judge.casgn` — nothing a semantic obligation quantified over an arbitrary `SemJudge` can see.
(§10.3's "our facts are keyed and immutable-per-key" is the assumption that fails: `consts` is
keyed and **mutable** per key.)

So the outgoing state is claimed at **both** contexts, and the two are for different readers:

* `StateOk κ Γ' I' m'` — what the rule's *consumer* needs. A send republishes its receiver's
  conformance at its own context; an assignment republishes its right-hand side's. This is the
  claim that used to be the whole conclusion, and keeping it is what makes the migration
  cost the 47 discharged rungs one component rather than a re-proof.
* `StateOk κ' Γ' I' m'` — what the *next statement* needs. This is the new content, and it is
  the one §3 is about: for the five declaration rules it says "one `stepFn` step installs
  exactly what `κ'` records", which is what makes `JudgeSeq.cons` compose without transport.
  For every other rule `κ'` is `κ` definitionally, so the second conjunct is the first.

Neither direction is transported. Both are stated.

Written as two flat conjuncts rather than a bundled pair, so that a consumer that wants the
first reads it off with an extra `-` in its pattern and a producer whose `κ'` is `κ` supplies
the same term twice. Bundling would have made every existing `⟨_, _, hok⟩` silently bind `hok`
to the pair. -/

/-- **The semantic judgment.** See the module docstring for the four choices in it,
§`Plain` above for the fifth, and §Outgoing conformance for the sixth. -/
def SemJudge (κ : Ctx) (Γ : Env) (I : Ty) (e : Ratchet.Expr) (τ : Ty) (κ' : Ctx)
    (Γ' : Env) (I' : Ty) : Prop :=
  Plain e ∧
  ∀ m : Machine, StateOk κ Γ I m →
    ∀ v m', Evals m e v m' →
      Framed m m' ∧ denM τ m' v ∧ StateOk κ Γ' I' m' ∧ StateOk κ' Γ' I' m'

/-- Evaluating a list of expressions left to right, each returning a value of its own type,
threading the state. The value list is existential because the *judgment* says nothing about
which values arise — only that whatever arises is in the corresponding type.

Note this is not `∀ v, Evals (.array es) …`: an argument list is not an expression, so its
semantic reading has to be built from the per-element one. `evalsAll` is that reading. -/
def EvalsAll : Machine → List Ratchet.Expr → List Value → Machine → Prop
  | m, [], [], m' => m' = m
  | m, e :: es, v :: vs, m' => ∃ m₁, Evals m e v m₁ ∧ EvalsAll m₁ es vs m'
  | _, _, _, _ => False

/-- **Every element's value is in its own type, at the machine its own evaluation ended at.**

The seventh stall point, fixed (`Denote/Sem/notes.md`, clink 53). The previous reading was
`DenAll τs m' vs` — every argument's type at the machine the *whole list* left behind — and
that is the right machine for the *consumer* (`Judge.prim` and the call rules use the argument
types at the moment of the call) but it is not what an argument list's evaluation establishes:
it would make `JudgeAll.cons`'s obligation demand a transport of `denM τ m₁ v` across the
evaluation of every later argument, and no such transport exists (`denM_ext` wants a heap that
only grew, and evaluating an arbitrary Ruby expression can mutate an object).

So the claim is stated where it is *true*, elementwise and at each element's own post-machine,
and the transport moves to the rules that actually use the values. That was the first of the
two candidate fixes the stall point recorded, and the reason to prefer it over the second
(a non-interference component on `StateOk`) is that it puts the missing fact where it is
spent: a call rule that needs its arguments' types at the call machine now has to say so, and
`PrimSig`'s no-mutator property — which is what makes the old form true today — becomes an
argument at the consumer instead of an invisible dependency here.

Note the intermediate machines are existential again rather than shared with `EvalsAll`'s.
That costs nothing: `Interp.run` is a function, so the machine a returning run ends at is
determined by where it started, and the witness is the same one. -/
def DenAllAt : Machine → List Ratchet.Expr → List Ty → List Value → Machine → Prop
  | m, [], [], [], m' => m' = m
  | m, e :: es, τ :: τs, v :: vs, m' =>
      ∃ m₁, Evals m e v m₁ ∧ denM τ m₁ v ∧ DenAllAt m₁ es τs vs m'
  | _, _, _, _, _ => False

def SemJudgeAll (κ : Ctx) (Γ : Env) (I : Ty) (es : List Ratchet.Expr) (τs : List Ty)
    (Γ' : Env) (I' : Ty) : Prop :=
  PlainAll es ∧
  ∀ m : Machine, StateOk κ Γ I m →
    ∀ vs m', EvalsAll m es vs m' →
      Framed m m' ∧ DenAllAt m es τs vs m' ∧ StateOk κ Γ' I' m'

/-- Keyword arguments at a call site: the same shape as `SemJudgeAll`, over the `(name, type)`
pairs `JudgeKw` produces. The names are static, so only the values are evaluated — which is
why the expression list is recovered from the entries rather than being an index. -/
def kwExprs : List Ratchet.KwEntry → List Ratchet.Expr
  | [] => []
  | .pair _ v :: es => v :: kwExprs es
  | .dyn _ v :: es => v :: kwExprs es
  | .splat e :: es => e :: kwExprs es

def SemJudgeKw (κ : Ctx) (Γ : Env) (I : Ty) (es : List Ratchet.KwEntry)
    (kws : List (String × Ty)) (Γ' : Env) (I' : Ty) : Prop :=
  ∀ m : Machine, StateOk κ Γ I m →
    ∀ vs m', EvalsAll m (kwExprs es) vs m' →
      Framed m m' ∧ DenAllAt m (kwExprs es) (kws.map (·.2)) vs m' ∧
        StateOk κ Γ' I' m'

/-- A hash literal's pairs, **interleaved**: key, value, key, value — Ruby's evaluation order
and the order `evalExpr`'s `.hash` arm performs.

This is the seventh stall point's *second* defect, fixed in clink 53. The previous reading
concatenated the halves (`ps.map (·.1) ++ ps.map (·.2)`, all keys and then all values), which
coincides with the real order at one pair and diverges at two — so `JudgePairs.cons`'s
obligation was stated over an evaluation the machine never performs. That is a *hypothesis*, so
the effect was vacuity rather than falsity: the rung was unprovable-looking and `Judge.hashLit`
would have had nothing usable to consume. `pairExprs` is the order, and it is the same shape
`kwExprs` already had for keywords.

The per-element claim is `DenPairsAt`, stepwise for `DenAllAt`'s reason: each key is in the key
join at the machine *its own* evaluation ended at, and each value likewise. `JudgePairs`' two
type indices are joins over all keys and all values (`Judge.hashLit` consumes them), so "in the
join" is the right per-element claim rather than a weakening — a join is an upper bound on each
side (`Denote/Join.lean`). -/
def pairExprs : List (Ratchet.Expr × Ratchet.Expr) → List Ratchet.Expr
  | [] => []
  | (k, v) :: ps => k :: v :: pairExprs ps

def DenPairsAt : Machine → List (Ratchet.Expr × Ratchet.Expr) → Ty → Ty → List Value →
    Machine → Prop
  | m, [], _, _, [], m' => m' = m
  | m, (k, v) :: ps, kr, vr, kv :: vv :: vals, m' =>
      ∃ m₁, Evals m k kv m₁ ∧ denM kr m₁ kv ∧
        ∃ m₂, Evals m₁ v vv m₂ ∧ denM vr m₂ vv ∧ DenPairsAt m₂ ps kr vr vals m'
  | _, _, _, _, _, _ => False

def SemJudgePairs (κ : Ctx) (Γ : Env) (I : Ty) (ps : List (Ratchet.Expr × Ratchet.Expr))
    (kr vr : Ty) (Γ' : Env) (I' : Ty) : Prop :=
  ∀ m : Machine, StateOk κ Γ I m →
    ∀ vals m', EvalsAll m (pairExprs ps) vals m' →
      Framed m m' ∧ DenPairsAt m ps kr vr vals m' ∧ StateOk κ Γ' I' m'

/-- A statement sequence. Same statement as `SemJudge` — a `seq` *is* an expression, and its
value is the last statement's — but kept a separate definition to mirror `JudgeSeq`, whose
whole reason for existing is that the context grows between statements
(`Ctx.afterStmt`). -/
def SemJudgeSeq (κ : Ctx) (Γ : Env) (I : Ty) (es : List Ratchet.Expr) (τ : Ty)
    (_κ' : Ctx) (Γ' : Env) (I' : Ty) : Prop :=
  PlainAll es ∧
  ∀ m : Machine, StateOk κ Γ I m →
    ∀ v m', Evals m (.seq es) v m' →
      Framed m m' ∧ denM τ m' v ∧ StateOk κ Γ' I' m'

/-- A `begin`/`rescue`'s handlers (tier 16b). `JudgeRescues` has **no outgoing state** in its
signature — its `cons` rule pins `Γ' = Γh ++ Γ` and `I' = I` as premises instead, because a
handler's assignments must not escape a clause that may not have run. The semantic reading
keeps that shape: every handler, evaluated in the *handler* environment (the clause's binding
prepended), returns a value in `τ` and leaves the same environment conforming.

`τ` is the join over all clauses (`Judge.beginRescue` consumes it), so "in `τ`" is the right
per-clause claim rather than a weakening: a join is an upper bound on each side. -/
def SemJudgeRescues (κ : Ctx) (Γ : Env) (I : Ty)
    (rs : List (List Ratchet.Expr × Option (Ratchet.TargetKind × String) × Ratchet.Expr))
    (τ : Ty) : Prop :=
  ∀ cls binding handler, (cls, binding, handler) ∈ rs →
    ∀ names Γh, rescueClasses? cls = some names → rescueBind? names binding = some Γh →
      ∀ m : Machine, StateOk κ (Γh ++ Γ) I m →
        ∀ v m', Evals m handler v m' →
          Framed m m' ∧ denM τ m' v ∧ StateOk κ (Γh ++ Γ) I m'

/-- A class body's **constant** assignments (tier 13e). `JudgeConsts` carries no `Env`, no
machine and no result type: it is a well-formedness side condition on a `class`/`module`
statement, and its two premises per entry are "the initialiser has a literal type" and "the
initialiser is judged in the *empty* environment". So its semantic reading is just that — the
same two facts, with `SemJudge` in place of `Judge`. Nothing here needs a machine index,
because `SemJudge` quantifies over machines itself. -/
def SemJudgeConsts (κ : Ctx) (cs : List (String × Ratchet.Expr)) : Prop :=
  ∀ n e, (n, e) ∈ cs → ∃ τ, constLitTy? e = some τ ∧ SemJudge κ [] .ivar0 e τ (κ.afterStmt e τ) [] .ivar0

/-- A class body's **nested** class and module declarations (tier 13e): each nested body's own
constants are semantically judged.

**A scaffolding choice with a recorded risk.** This reads *one level* deep and leaves the
recursion into deeper nestings to `JudgeNested.cons`'s own obligation, which carries the
deeper `SemJudgeNested` as a premise exactly as the inductive constructor does. If that turns
out too weak to prove `Judge.classStmt`'s obligation with, the symptom is an **unprovable
rung** — visible, and stalling the ladder at a named rule — rather than a theorem that is
true of a definition too weak to mean anything. That failure mode is the reason the companion
definitions are worth writing before any rung is attempted: a rung that will not close is
information about the definition. -/
def SemJudgeNested (κ : Ctx) (_pfx : String) (nst : Ratchet.Nested) : Prop :=
  ∀ isMod n body, (isMod, n, body) ∈ nst →
    ∀ ms sms incs exts preps cs nst',
      classMethods? body = some (ms, sms, incs, exts, preps, cs, nst') →
      SemJudgeConsts κ cs

end Ratchet.Denote
