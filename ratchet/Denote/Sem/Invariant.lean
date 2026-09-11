import Denote.Sem.SafeKont

/-!
# `Denote/Sem/Invariant.lean` — what an inductive invariant proving type safety looks like on
this side of the world

**Why this file exists.** The refutation of "`SemJudge` implies
stuck-freedom". The follow-up question is what *would* prove it, and the answer is not a
better `SemJudge`: it is an invariant over **whole machine configurations**, because the thing
to be excluded (`Semantics.typeStuck`) is a property of a *reachable machine*, and `SemJudge`
is a property of an *expression evaluated from a machine with an empty continuation*. Those are
different quantifiers, and the gap between them is the continuation.

`../type-safety-by-reachability.md` §4 is the plan; `lean/RubyCore/Proof/`'s `invariant_sound`
is the same argument already carried out over a hand-built invariant, next to `stepFn`. This
file is that argument's **ratchet-side shape**: the reduction proved, and the invariant's
three components written down as named definitions so the remaining work has a target rather
than forty arguments (this package's working rule — `Denote/Sem/Frame.lean`'s `KontFrame`,
`Denote/Adequacy.lean`'s `StuckFreeTarget`).

## §1 The reduction — proved, and it is the cheap half

Two obligations, no induction over syntax:

* **`preserved`** — `Inv` survives a `.next` step.
* **`noBadStep`** — from an `Inv` machine, a step never lands on an uncaught member of the
  `NoMethodError`/`ArgumentError`/`TypeError` family.

`safety_of_invariant` derives "no run from an `Inv` machine is ever type-stuck, at any fuel"
from exactly those two. Note what is *not* an obligation: **progress in the usual sense.**
Ruby programs legitimately raise, diverge and gate; the bad-state predicate is `typeStuck`,
not "cannot step", so the second obligation is a *bad-step exclusion* rather than "some step
exists". That is the whole point of the reachability framing and it is why divergence is free
(`../../../docs/semantics/answer-typed-judgments.md` §7).

## §2 The invariant — three components, of which two exist

```
Inv m  :=  ∃ κ Γ I τ tags,  StateOk κ Γ I m            -- the store conforms      (BUILT)
                          ∧ CtlOk κ Γ I τ m             -- what is in flight       (cheap)
                          ∧ KontOk κ Γ I τ tags m.kont  -- what is waiting for it  (NOT BUILT)
```

1. **`StateOk`** — `Denote/Sem/State.lean`, 1633 lines, and every one of the 48 discharged
   rungs already establishes and re-establishes it. Nothing new is needed.
2. **`CtlOk`** — three arms, one per `Ctl`, and this is where the checker plugs in: the
   `.eval` arm *is* a `Judge` derivation. The `.value` and `.jump` arms are the two arms of
   `Answer` (`Denote/Sem/Answer.lean`), which is why this component is a definition rather
   than a design problem. What it needs from the ladder is not `SemJudge` but the
   **answer-axis adequacy bridge** — `Judge … e … → Delivers (evalFrom m e) …` — i.e. exactly
   the premise `Denote/Rules/WhileAnswer.lean`'s `AnswerOkAt` is.
3. **`KontOk`** — the continuation, frame by frame. **This is the whole remaining cost**, and
   §3 is about its shape.

## §3 What `KontOk` has to look like, and the two things that fix its shape

### It cannot be `SafeKont`

The obvious move is to reuse `Denote/Sem/SafeKont.lean`: `Inv m := ∃ A, Delivers … A ∧ SafeKont
m.kont A Q`. **It does not scale to a whole-machine invariant, and the reason is
`CatchFree`.** `safe_pushK` requires `CatchFree m.kont`, and a machine reachable from a program
containing `catch` has a `catchK` on its continuation. `Denote/Sem/AnswerCatch.lean` explains
why that hypothesis is irreducible: `throw` reads the *whole* stack, so no per-frame
description can replace it.

So the answer-typed decomposition is a **per-rule** tool (the konts a rule pushes are
literals, and `CatchFree` holds of them by computation) and not a whole-machine invariant. The
invariant must describe the continuation *syntactically*.

### …and therefore it must carry the live `catch` tags

Which is the second fixed point of the design, and it is not an implementation detail: if
`KontOk` records the set of tags handled below a point, then `hasCatcher`'s whole-stack read
becomes a *local* question about the index, and `CatchFree` stops being needed at all. That
index is Ueno et al.'s exception context `T` (`answer-typed-judgments.md` §3.1) and Hazel's
protocol (§3.2) — so the design lands exactly where the literature said it would, arrived at
from the opposite direction.

### The per-frame shape: two clauses, not one

Each frame contributes a **value clause** ("an answer of type `τ` arriving here resumes at a
machine the invariant again describes") and an **escape clause** ("a jump arriving here is one
this frame may see, and the machine it resumes at conforms"). The escape clause is where the
premises §2.1 called unconsumable finally get consumed: `nxtPrefixOk` (§F23) is the
`whileCondK`/`whileBodyK` escape clause, and `raise`'s `excName?` (§F25) is `beginBodyK`'s.

Six representative constructors are written out below — the pass-through (`asgnK`), the
sequence (`seqK`), the back edge (`whileCondK`/`whileBodyK`), the tag (`catchK`) and the
handler (`beginBodyK`). **Forty-three remain**, and that count is the honest cost statement.

## §4 The cost, and what would reduce it

| component | state | size |
|---|---|---|
| `safety_of_invariant` (the reduction) | **proved here** | 20 lines |
| `StateOk` | **built** | `State.lean`, reused as-is |
| `CtlOk` | definition here; needs the answer-axis adequacy bridge | small |
| `KontOk` | 6 of **36** constructors sketched here | the work |
| `preserved` | one case per (`stepFn` arm × frame): 48 `evalExpr` arms + 36 frames × 2 clauses | the work |
| `noBadStep` | one case per raising site in the dispatch spine | the work |

## §5 The measurement, taken — and it is a **negative** result

§4 used to say "the one measurement that would cut the cost is how many of the 49 `Kont`
constructors are reachable from a `Judge`-derivable program", on the theory that the judged
fragment (25 of `Ratchet.Expr`'s heads, tier ≤16) would touch far fewer frames.
`probes/kont_census.lean` takes it: every committed corpus program walked under the real
`stepFn` from the prelude-booted heap, collecting the head constructor of every continuation
frame ever pushed.

```
corpus programs walked: 259; targeting validate=true: 213
Kont constructors: 49
  pushed by SOME corpus program: 36
  pushed by a program the judgment is meant to accept: 36     <- identical
  never reached (13): raiseNewK includeK defsK sclassK scopedClassDefK forStartK forBodyK
                      yieldSplatK superSplatK catchK definedRecvK definedCpathK definedGuardK
```

**36 of 49, and restricting to the judged fragment removes nothing.** The hoped-for reduction
is not there, and the reason is structural rather than accidental: `Judge` covers `send`, and
the send spine (`startArgs` → `argsK`/`argsSplatK`/`kwPairK`/`kwSplatK`/`kwDynKeyK`/`kwDynValK`,
`finishSend` → `recvK`/`frameK`/`blkFrameK`/`blkCoerceK`/`iterK`/`newK`) reaches most of the
frame set on its own. So `KontOk` is a 36-constructor relation, not a 15-constructor one, and
that is the number to plan against.

Two smaller findings from the same run:

* **`catchK` is never reached.** The tag index §3 argues `KontOk` must carry is required for
  the *design* to be closed (a program containing `catch` must satisfy the invariant) and is
  exercised by **no current rung** — so it would be built untested, which is exactly the
  vacuity risk `Denote/Sanity.lean` exists to answer on the other axis. Worth a corpus rung
  before it is worth a constructor.
* **The 13 unreached frames are a coherent set**, not a random tail: the five declaration
  frames (`defsK`, `sclassK`, `scopedClassDefK`, `includeK`, `raiseNewK`), the two `for`
  frames, the two splat-forwarding frames, and the four `catch`/`defined?` frames. Each is a
  *head* the corpus does not exercise, which means the census doubles as a coverage report on
  the corpus itself.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## §1 The reduction -/

/-- The two obligations an invariant must discharge. See §1 for why "progress" is not among
them. -/
structure SafetyObligations (Inv : Machine → Prop) : Prop where
  /-- `Inv` survives a step. -/
  preserved : ∀ m m', Inv m → Interp.stepFn m = .next m' → Inv m'
  /-- From an `Inv` machine, no step lands on an uncaught type error. -/
  noBadStep : ∀ m exc m', Inv m → Interp.stepFn m = .uncaught exc m' →
    Semantics.isTypeError m'.heap exc = false

/-- **Type safety by reachability, on this side.** An invariant satisfying the two obligations
rules out every type-stuck outcome, at every fuel — so the statement needs no termination
argument and divergence costs nothing (`.outOfFuel` is not type-stuck).

This is the ratchet-side counterpart of `RubyCore.Proof`'s `invariant_sound`, and it is
deliberately stated over an **abstract** `Inv`: the theorem is what makes a candidate
invariant worth building, and it should be on file before any candidate is. -/
theorem safety_of_invariant {Inv : Machine → Prop} (h : SafetyObligations Inv) :
    ∀ (fuel : Nat) (m : Machine), Inv m → Semantics.typeStuck (Interp.run fuel m) = false := by
  intro fuel
  induction fuel with
  | zero => intro m _; simp [run_zero, Semantics.typeStuck]
  | succ n ih =>
    intro m hm
    rw [run_succ]
    cases hev : Interp.stepFn m with
    | next m' => exact ih m' (h.preserved m m' hm hev)
    | done v m' => simp [Semantics.typeStuck]
    | uncaught exc m' =>
      simp only [Semantics.typeStuck]
      exact h.noBadStep m exc m' hm hev
    | unsupported r => simp [Semantics.typeStuck]
    | stuck msg => simp [Semantics.typeStuck]

/-- The third obligation, which is the *checker's* half: a program the judgment accepts starts
at an `Inv` machine. Stated separately because it is the only one that mentions `Judge` — the
two above are about `stepFn` alone, which is what lets them be proved by a walk. -/
def InvInit (Inv : Machine → Prop) : Prop :=
  ∀ (p : Ratchet.Expr) (τ : Ty) (κ' : Ctx) (Γ' : Env) (I' : Ty),
    Judge Ratchet.ctx0 [] .ivar0 p τ κ' Γ' I' →
    ∀ m : Machine, StateOk Ratchet.ctx0 [] .ivar0 m → Inv (evalFrom m p)

/-- **The whole theorem, assembled.** With the three obligations, the checker's verdict rules
out type-stuck outcomes for the program it accepted. Proved from §1; every hypothesis is a
named `Prop` and none of them is discharged here. -/
theorem stuckFree_of_obligations {Inv : Machine → Prop} (ho : SafetyObligations Inv)
    (hi : InvInit Inv) :
    ∀ (p : Ratchet.Expr) (τ : Ty) (κ' : Ctx) (Γ' : Env) (I' : Ty),
      Judge Ratchet.ctx0 [] .ivar0 p τ κ' Γ' I' →
      ∀ m : Machine, StateOk Ratchet.ctx0 [] .ivar0 m → StuckFree m p :=
  fun p τ κ' Γ' I' hj m hm fuel =>
    safety_of_invariant ho fuel (evalFrom m p) (hi p τ κ' Γ' I' hj m hm)

/-- …and that is exactly `StuckFreeTarget`'s shape at the top-level context, so the reduction
lands on the statement `Denote/Adequacy.lean` already names. -/
theorem stuckFreeTarget_at_ctx0 {Inv : Machine → Prop} (ho : SafetyObligations Inv)
    (hi : InvInit Inv) :
    ∀ p τ κ' Γ' I', Judge Ratchet.ctx0 [] .ivar0 p τ κ' Γ' I' →
      ∀ m, StateOk Ratchet.ctx0 [] .ivar0 m → StuckFree m p :=
  stuckFree_of_obligations ho hi

/-! ## §1a What the `∀ m` in `SemJudge` does and does not give — a correction

A first reading of §1 said adequacy gives `SemJudge` "at the initial machine". **That is
wrong**, and the correction matters because it changes which obligations are real.
`SemJudge κ Γ I e τ …` is `∀ m, StateOk κ Γ I m → …`: it is a claim about *every* machine
conformant with the description, so a sub-derivation obtained by indexing applies at a
reachable machine **without anyone having to track which machine it is**. That is a genuine
feature of the shape and it does real work in the design.

So what is left? Exactly three things, and only the first is bookkeeping.

1. **Which sub-derivation.** The derivation *position* — `KontOk` / the zipper spine, §3, and
   the 36 frames §5 measures. Unavoidable, and the part the indexing idea correctly identifies.
2. **Conformance at that position.** The derivation supplies the *static* description
   `(κ_sub, Γ_sub, I_sub)`; using the sub-judgment needs `StateOk κ_sub Γ_sub I_sub m` of the
   *actual* machine. Nothing in the derivation says that — it is precisely the invariant, and
   re-establishing it at every step is the `preserved` obligation. The `∀ m` means we carry a
   **description** rather than a machine; it does not mean conformance is free.
3. **`kont = []` vs `kont = K`, and this is the one that bites.** `SemJudge`'s hypothesis is
   `Evals m e v m'`, i.e. `∃ fuel, Interp.run fuel (evalFrom m e) = .value v m'`, and
   `evalFrom` sets **`kont := []`** (`Denote/Sem/State.lean`). So at a reachable machine the
   sub-judgment describes the run that *discards the waiting continuation*. Turning that into a
   statement about the real run is the decomposition, and `eq_pushK_evalFrom` below says the two
   machines differ by exactly one `pushK`:

       m.ctl = .eval (toRuby e) → m = pushK m.kont (evalFrom m e)

   so the bridge is `run_pushK m.kont`, whose hypothesis is `CatchFree m.kont` — **false for
   any reachable machine inside a `catch`**. Hence the protocol index
   (`Denote/Sem/AnswerCatch.lean` §`CatchFree` is the degenerate case of a protocol) is not an
   optional improvement to this plan; it is its prerequisite. The four-step sketch this file
   records turns out to be in dependency order.

Two smaller residues of the same kind, both already measured elsewhere: `SemJudge`'s conclusion
constrains only runs reaching `.value` (`Denote/Sem/NoProgress.lean`, §F27), and six of the 36
frames correspond to no derivation position at all (§5) — the call boundary, where the zipper
becomes a *stack* of derivations rather than a position in one. -/

/-- **The bridge.** A machine about to evaluate `e` *is* `evalFrom` under its own continuation.
One `rfl`-level fact, and the whole reason `run_pushK` is the connective between a judgment
(stated at `kont = []`) and an invariant (stated at an arbitrary `kont`). -/
theorem eq_pushK_evalFrom {m : Machine} {e : Ratchet.Expr} (hc : m.ctl = .eval (toRuby e)) :
    m = pushK m.kont (evalFrom m e) := by
  simp only [pushK, evalFrom, List.nil_append, ← hc]

/-! ## §2 The invariant's three components -/

/-- **What is in flight**, one arm per `Ctl` — and the last two arms are the two arms of
`Answer`, which is the payoff from `Denote/Sem/Answer.lean`: an invariant that had to read
`Interp.run`'s five-way split would need five arms and would have nothing to say about three
of them.

The `.eval` arm is the checker's interface: a machine mid-evaluation is invariant-conformant
when the expression it is evaluating is one the *judgment* derives. `hdel` is the
answer-axis adequacy bridge — see §2.3 of the module docstring; it is not `SemJudge` and
cannot be got from it. -/
def CtlOk (κ : Ctx) (Γ : Env) (I : Ty) (τ : Ty) (m : Machine) : Prop :=
  match m.ctl with
  | .eval e => ∃ (e₀ : Ratchet.Expr) (κ' : Ctx) (Γ' : Env) (I' : Ty),
      toRuby e₀ = e ∧ Judge κ Γ I e₀ τ κ' Γ' I'
  | .value v => denM τ m v
  | .jump _ => True   -- the escape clause lives in `KontOk`, where the frame that sees it is

/-- **What is waiting for it.** Indexed by the type the innermost frame expects (`τ`), by the
description the machine must conform to when the frame resumes (`Γ`/`I`), and by the **live
`catch` tags** (`tags`) — §3's second fixed point, and the index that makes `throw`'s
whole-stack read local.

Six constructors, deliberately: enough to exhibit every interesting shape, and short of the
49 it will need. **`sorry`-free**: this is a real inductive, it is just incomplete, and an
incomplete inductive is honest in a way that a complete one with `sorry`ed cases is not. -/
inductive KontOk (κ : Ctx) : List Kont → Env → Ty → Ty → List Value → Prop
  /-- The empty continuation: the program's own answer. Any type, no tags. -/
  | nil {Γ I τ} : KontOk κ [] Γ I τ []
  /-- **Pass-through.** `asgnK` accepts any value, writes it, and delivers the same value on.
      Its escape clause is trivial — `unwind`'s default arm hands the jump straight back —
      which is the same fact `jumpStuckFree_asgnK` was four lines of. -/
  | asgnK {rest Γ I τ tags x} :
      KontOk κ rest Γ I τ tags → KontOk κ (.asgnK .lvar x :: rest) Γ I τ tags
  /-- **Sequence.** Discards the value and continues with the remaining statements, which must
      themselves be judged — so this constructor is where `JudgeSeq` enters the invariant. -/
  | seqK {es rest Γ I σ τ tags κ' Γ' I'} :
      JudgeSeq κ Γ I es σ κ' Γ' I' → KontOk κ rest Γ' I' σ tags →
      KontOk κ (.seqK (es.map toRuby) :: rest) Γ I τ tags
  /-- **The back edge, condition side.** The loop may resume here on a truthy value *or* on a
      `nxtJ`, and both resume at `Γ`/`I` — which is what `Judge.while'`'s `Γc = Γ` premise
      is for, and what `nxtPrefixOk` (§F23) makes true at a mid-body `next`. -/
  | whileCondK {c body rest Γ I σ τ tags κc Γc Ic κb Γb Ib} :
      Judge κ Γ I c σ κc Γc Ic → Judge κ Γ I body τ κb Γb Ib →
      nxtPrefixOk body = true →
      KontOk κ rest Γ I .nilT tags →
      KontOk κ (.whileCondK (toRuby c) (toRuby body) :: rest) Γ I σ tags
  /-- **The back edge, body side.** Same premises, other entry point — and the two are
      mutually reachable (`nxtJ` one way, `redoJ` the other), which is why
      `Denote/Rules/WhileAnswer.lean`'s `loop_stuck` proves them together. -/
  | whileBodyK {c body rest Γ I σ τ tags κc Γc Ic κb Γb Ib} :
      Judge κ Γ I c σ κc Γc Ic → Judge κ Γ I body τ κb Γb Ib →
      nxtPrefixOk body = true →
      KontOk κ rest Γ I .nilT tags →
      KontOk κ (.whileBodyK (toRuby c) (toRuby body) :: rest) Γ I τ tags
  /-- **The tag.** The only constructor that grows `tags`, and the reason `tags` is an index:
      `Interp.hasCatcher` asks whether *any* frame below carries a matching tag, and with this
      constructor that question is answered by the index instead of by a walk. -/
  | catchK {t rest Γ I τ tags} :
      KontOk κ rest Γ I τ tags → KontOk κ (.catchK t :: rest) Γ I τ (t :: tags)

/-- **The invariant.** Three components, existentially quantified over the description — which
is right rather than lazy: a reachable machine does not come with its types attached, and the
invariant's job is to say that *some* consistent description exists. -/
def Inv (m : Machine) : Prop :=
  ∃ (κ : Ctx) (Γ : Env) (I : Ty) (τ : Ty) (tags : List Value),
    StateOk κ Γ I m ∧ CtlOk κ Γ I τ m ∧ KontOk κ m.kont Γ I τ tags

/-! ## §3 Two sanity checks on the skeleton

Neither is a step toward the proof; both are checks that the definitions are not vacuous or
mistyped, which is the failure mode a skeleton actually has. -/

/-- The empty continuation at a judged expression satisfies the `Ctl`/`Kont` halves — i.e. the
initial machine's shape is derivable, which is `InvInit`'s content modulo `StateOk`. -/
theorem inv_of_judge_init {p : Ratchet.Expr} {τ : Ty} {κ' : Ctx} {Γ' : Env} {I' : Ty}
    (hj : Judge Ratchet.ctx0 [] .ivar0 p τ κ' Γ' I')
    {m : Machine} (hm : StateOk Ratchet.ctx0 [] .ivar0 m) :
    Inv (evalFrom m p) :=
  ⟨Ratchet.ctx0, [], .ivar0, τ, [],
   StateOk_reCtl hm _ _, ⟨p, κ', Γ', I', rfl, hj⟩, KontOk.nil⟩

/-- `tags` really does track the live tags: one `catch` frame, one tag. -/
example (t : Value) (Γ : Env) (I τ : Ty) :
    KontOk Ratchet.ctx0 [.catchK t] Γ I τ [t] := KontOk.catchK KontOk.nil

/-- And the two loop entry points are the *same* premises at different indices, which is the
structural reason `loop_stuck` could not prove one without the other. -/
example {c body : Ratchet.Expr} {σ τ : Ty} {Γ : Env} {I : Ty} {κc Γc Ic κb Γb Ib}
    (hc : Judge Ratchet.ctx0 Γ I c σ κc Γc Ic)
    (hb : Judge Ratchet.ctx0 Γ I body τ κb Γb Ib)
    (hn : nxtPrefixOk body = true) :
    KontOk Ratchet.ctx0 [.whileCondK (toRuby c) (toRuby body)] Γ I σ [] ∧
    KontOk Ratchet.ctx0 [.whileBodyK (toRuby c) (toRuby body)] Γ I τ [] :=
  ⟨.whileCondK hc hb hn .nil, .whileBodyK hc hb hn .nil⟩

#print axioms eq_pushK_evalFrom
#print axioms safety_of_invariant
#print axioms stuckFree_of_obligations
#print axioms inv_of_judge_init

end Ratchet.Denote
