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

/-- The third obligation, which is the *checker's* half: a program the checker accepts starts
at an `Inv` machine.

**Parameterised by what "accepts" means** (Norm A), rather than naming a judgment. It used to
read `Judge ctx0 [] .ivar0 p τ κ' Γ' I' → …` and so was the one declaration in this file that
depended on the judgment; generalising it costs nothing — no proof below changes — and it is
what lets the reduction be instantiated at `Ratchet/Check.lean`'s `DTyped` without this file
importing the checker. The two obligations above are about `stepFn` alone, which is what lets
them be proved by a walk. -/
def InvInit (Accepted : Ratchet.Expr → Prop) (Inv : Machine → Prop) : Prop :=
  ∀ p : Ratchet.Expr, Accepted p →
    ∀ m : Machine, StateOk Ratchet.ctx0 [] .ivar0 m → Inv (evalFrom m p)

/-- **The whole theorem, assembled.** With the three obligations, the checker's verdict rules
out type-stuck outcomes for the program it accepted. Proved from §1; every hypothesis is a
named `Prop` and none of them is discharged here. -/
theorem stuckFree_of_obligations {Accepted : Ratchet.Expr → Prop} {Inv : Machine → Prop}
    (ho : SafetyObligations Inv) (hi : InvInit Accepted Inv) :
    ∀ p : Ratchet.Expr, Accepted p →
      ∀ m : Machine, StateOk Ratchet.ctx0 [] .ivar0 m → StuckFree m p :=
  fun p hp m hm fuel => safety_of_invariant ho fuel (evalFrom m p) (hi p hp m hm)

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

/-! ## §2 The invariant's three components lived here, and are gone

`CtlOk`/`KontOk`/`Inv` were the skeleton of layer 6, indexed by the deleted `Ratchet.Judge`
(its `.eval` arm asserted the expression in flight was `toRuby e₀` for a **`Judge`**-derived
`e₀`, and `KontOk`'s frame clauses carried `Judge` premises). They went with that judgment in
clink 68, along with the two sanity checks that instantiated them.

**§1 above is what survives, and it is the part that was worth keeping**: the reduction is
proved for an *abstract* `Inv`, so it is exactly as usable against `Ratchet/Check.lean`'s
`DJudge` as it was against the old one. What an instantiation now owes is the same two
obligations — `preserved` and `noBadStep` — over whatever invariant the typed ladder defines,
and `probes/kont_census.lean`'s measurement (deleted with the corpus it walked; the number is
in `AGENTS.md`) priced the frame set at 36 constructors.

Not a regression to re-derive: `Denote/Proto/Safety.lean` closed all of it end to end on a
four-expression fragment before both files were deleted, and `implementation-notes.md`
clink 65 records what that exercise found — that the continuation typing has to be indexed by
the program's own answer type, which no design discussion had anticipated. -/


#print axioms eq_pushK_evalFrom
#print axioms safety_of_invariant
#print axioms stuckFree_of_obligations

end Ratchet.Denote