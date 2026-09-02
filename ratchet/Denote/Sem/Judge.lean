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
4. **`m'.stack = m.stack`.** Frame balance, and it earns its place for the same reason: `Γ`
   describes the *current frame*'s locals, so a conclusion about `Γ'` at a machine with a
   different frame on top would be a claim about the wrong bindings. Every rule that pushes a
   frame (a call, a block) has to restore it, and stating that per-rule is how it gets proved
   rather than assumed.

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

/-- **The semantic judgment.** See the module docstring for the four choices in it. -/
def SemJudge (κ : Ctx) (Γ : Env) (I : Ty) (e : Ratchet.Expr) (τ : Ty) (Γ' : Env) (I' : Ty) :
    Prop :=
  ∀ m : Machine, StateOk κ Γ I m →
    ∀ v m', Evals m e v m' →
      m'.stack = m.stack ∧ denM τ m' v ∧ StateOk κ Γ' I' m'

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
  ∀ m : Machine, StateOk κ Γ I m →
    ∀ vs m', EvalsAll m es vs m' →
      m'.stack = m.stack ∧ DenAllAt m es τs vs m' ∧ StateOk κ Γ' I' m'

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
      m'.stack = m.stack ∧ DenAllAt m (kwExprs es) (kws.map (·.2)) vs m' ∧
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
      m'.stack = m.stack ∧ DenPairsAt m ps kr vr vals m' ∧ StateOk κ Γ' I' m'

/-- A statement sequence. Same statement as `SemJudge` — a `seq` *is* an expression, and its
value is the last statement's — but kept a separate definition to mirror `JudgeSeq`, whose
whole reason for existing is that the context grows between statements
(`Ctx.afterStmt`). -/
def SemJudgeSeq (κ : Ctx) (Γ : Env) (I : Ty) (es : List Ratchet.Expr) (τ : Ty)
    (Γ' : Env) (I' : Ty) : Prop :=
  ∀ m : Machine, StateOk κ Γ I m →
    ∀ v m', Evals m (.seq es) v m' →
      m'.stack = m.stack ∧ denM τ m' v ∧ StateOk κ Γ' I' m'

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
          m'.stack = m.stack ∧ denM τ m' v ∧ StateOk κ (Γh ++ Γ) I m'

/-- A class body's **constant** assignments (tier 13e). `JudgeConsts` carries no `Env`, no
machine and no result type: it is a well-formedness side condition on a `class`/`module`
statement, and its two premises per entry are "the initialiser has a literal type" and "the
initialiser is judged in the *empty* environment". So its semantic reading is just that — the
same two facts, with `SemJudge` in place of `Judge`. Nothing here needs a machine index,
because `SemJudge` quantifies over machines itself. -/
def SemJudgeConsts (κ : Ctx) (cs : List (String × Ratchet.Expr)) : Prop :=
  ∀ n e, (n, e) ∈ cs → ∃ τ, constLitTy? e = some τ ∧ SemJudge κ [] .ivar0 e τ [] .ivar0

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
