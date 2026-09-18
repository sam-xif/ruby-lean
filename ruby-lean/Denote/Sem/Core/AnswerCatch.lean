import Denote.Sem.Core.SafeKont

/-!
# `Denote/Sem/Core/AnswerCatch.lean` — why `CatchFree` survives answer-typing, and why
`begin`/`rescue` needs no counterpart

Answers a question the answer-type work raises directly: `run_pushK`/`safe_pushK` still carry
`CatchFree K`, and `JumpOpaque`'s docstring lists *two* things it was for — "a `rescue` in `K`
catching what the sub-run raised, a `whileBodyK` in `K` swallowing a `break`" — so why did the
second kind of hypothesis disappear while the first did not?

Because they were never the same kind of fact.

## `CatchFree` is about **step-locality**, and it is not a control-flow condition

`stepFn` writes `kont` head-locally at all thirteen of its writers. It has exactly **one
reader of the whole continuation**: `Interp.hasCatcher` (`RubyCore/Interp/Reflect.lean:163`),
the `throw` dispatch's `m.kont.any (· matches .catchK tag)`. That is not a modelling choice —
it is CRuby's semantics for `throw`, which must decide *at the throw site* whether a matching
`catch` exists, because if none does it raises `UncaughtThrowError` **there**, where an
enclosing `rescue` can see it. Measured on CRuby 4.0.5:

```ruby
begin; throw :t; rescue UncaughtThrowError; "caught locally"; end
# => "caught locally"                     -- no catch in the tail

catch(:t) { x = begin; throw :t; rescue UncaughtThrowError; "x"; end; "finished #{x}" }
# => nil                                  -- the same begin block, and the throw left it
```

So a `catchK` in the **tail** changes what a step *inside* the sub-computation does. No
answer type can repair that: the sub-computation does not have one answer that the context
then interprets, it has two different runs. `CatchFree` is the hypothesis that says we are
not in that situation, and `RubyCore.Proof.stepFn_frame` — proved with `CatchFree K` as its
*only* continuation hypothesis — is the machine-checked statement that `catchK` is the only
obstruction of this kind in the whole interpreter.

## `rescue` is about **answer-handling**, and that is head-local

`raise` does no lookahead. `unwind` pops one frame at a time, so a `beginBodyK` in the tail
is invisible until the jump has already unwound everything above it — that is, until the
frame is at the *head*. Nearest handler wins, whatever is further out:

```ruby
begin; begin; raise "boom"; rescue RuntimeError; "inner"; end; rescue RuntimeError; "outer"; end
# => "inner"
```

So a `rescue` in `K` does not change any step of the sub-computation. It changes what happens
**after** the sub-computation hands over an escape — and that is precisely what the answer
type made into a case instead of a hypothesis. Under `run_split` the escape had to be
excluded (there was nowhere to put it), so `JumpOpaque` had to rule out rescue tails as
collateral; under `run_pushK` the escape is delivered and the `esc` clause of `SafeKont` says
what the handler does with it.

**The one-line answer**: `CatchFree` is a condition on the *step relation*, `JumpOpaque` was
a condition on the *answer*, and only the second kind is what answer-typing eliminates.
`../../AGENTS.md` §The answer-typed design §7 predicted exactly this and it holds.

The two are independent, and §Quadrant below exhibits the corner that matters:
`not_jumpOpaque_definedGuardK` together with `catchFree_definedGuardK` is a handler
continuation that `run_split` **cannot** be applied at and `run_pushK` can. So this is not a
bookkeeping difference — `JumpOpaque` is false for the whole handler family, which is why
`begin`/`rescue` never appeared in the value ladder's 48 rungs at all.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## `CatchFree` is the *degenerate case of a protocol*, not a side condition

The design note's §6 predicted this ("`CatchFree`/`JumpOpaque` stop being ad hoc — they become
the statement of *which tags* a continuation intercepts, Essence's `handle t`, Hazel's protocol
in its simplest form"). `tagsOf` is that statement and `catchFree_iff_tagsOf_nil` is the
prediction, proved.

**Why this matters for a decomposition that is unconditional in `K`.** The frame rule wants

    stepFn_T (tagsOf K ++ T) (pushK K m) = frameR K (stepFn_T T m)

— the inner computation stepped *knowing* which tags are live below it — of which today's
`stepFn_frame` is the `T = tagsOf K = []` instance. That statement cannot be written against
today's `stepFn`, because `stepFn` has no ambient-protocol parameter, and adding one is a
change to the model's interface rather than to any proof. It would be **behaviour-preserving**
(top level passes `[]`, and `hasCatcher` becomes `m.kont.any … || T.any …`), it is checkable by
difftest for exactly that reason, and it threads through everything that can reach the throw
dispatch — i.e. the whole send spine.

**And relocating the tag set does not substitute for it.** The tempting cheap version is to
move the live-tag set from the continuation into a `Machine` field, so that `hasCatcher` reads a
field instead of walking `kont`. That makes `stepFn` head-local in `kont` and buys nothing: the
decomposition claims the inner and outer runs take the *same steps*, and if `K` handles `:t`
then a `throw :t` inside the sub-computation raises in the inner run and jumps in the outer one.
Any *faithful* representation of "is `:t` handled below" must therefore differ between the two.
The non-locality is semantic, not representational — which is why the repair is an index and
not a refactor. -/

/-- The `catch` tags a continuation intercepts — `Interp.hasCatcher`'s whole-stack read,
recovered as a function of the tail alone. -/
def tagsOf : List Kont → List Value
  | [] => []
  | .catchK t :: rest => t :: tagsOf rest
  | _ :: rest => tagsOf rest

/-- **`CatchFree K` is exactly "`K` intercepts nothing".** So the hypothesis every theorem in
`Answer.lean` and `SafeKont.lean` carries is not a technical restriction on the shape of `K`;
it is the empty protocol, and the general decomposition is the same statement at a non-empty
one. -/
theorem catchFree_iff_tagsOf_nil (K : List Kont) :
    RubyCore.Proof.CatchFree K ↔ tagsOf K = [] := by
  induction K with
  | nil => exact ⟨fun _ => rfl, fun _ k hk => absurd hk (by simp)⟩
  | cons k rest ih =>
    constructor
    · intro h
      cases k with
      | catchK t => exact absurd rfl (h (.catchK t) (by simp) t)
      | _ => exact (by simpa [tagsOf] using ih.mp (fun kk hkk => h kk (by simp [hkk])))
    · intro h kk hkk t
      cases k with
      | catchK t' => exact absurd h (by simp [tagsOf])
      | _ =>
        rcases List.mem_cons.mp hkk with rfl | hmem
        · simp
        · exact ih.mpr (by simpa [tagsOf] using h) kk hmem t

/-! ## The rescue family is `CatchFree`, so `run_pushK` applies to it unconditionally -/

/-- Every continuation `begin`/`rescue`/`else`/`ensure` pushes, together with the two while
konts — the *other* thing `JumpOpaque`'s docstring listed. Not one `catchK` among them, so the
decomposition needs nothing extra, which is the whole answer to "why is there no
`RescueFree`". -/
theorem catchFree_controlKonts (n : BeginNode) (exc : Value) (pendingExcs : List RubyCore.Expr)
    (ref : Option (RubyCore.TargetKind × String)) (handler : RubyCore.Expr)
    (restClauses : List (List RubyCore.Expr × Option (RubyCore.TargetKind × String) × RubyCore.Expr))
    (saved : Option Value) (pend : Pending) (restore : Option (Option Value))
    (c body : RubyCore.Expr) :
    RubyCore.Proof.CatchFree
      [.beginBodyK n, .rescMatchK n exc pendingExcs ref handler restClauses,
       .rescueK n saved, .elseK n, .ensureK pend restore, .definedGuardK,
       .whileCondK c body, .whileBodyK c body] := by
  intro k hk t
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- The contrast, and it is the *only* one: a `catch` marker in the tail. -/
theorem not_catchFree_catchK (t : Value) : ¬ RubyCore.Proof.CatchFree [.catchK t] := by
  intro h
  exact h (.catchK t) (by simp) t rfl

/-! ## The two conditions are independent, and the interesting quadrant is non-empty

`CatchFree` and `JumpOpaque` are not comparable, and the continuation family this question is
about — handlers — sits in the quadrant `run_split` cannot serve and `run_pushK` can:
**`CatchFree` and *not* `JumpOpaque`**. `definedGuardK` is the cheapest witness (it swallows
an in-flight raise unconditionally, with no class matching and so no heap), and the argument
is `beginBodyK`'s verbatim. -/

/-- `unwind` at a `defined?` guard turns a raise into `nil`: "any exception while evaluating a
`defined?` operand makes it nil" (`Interp/Kont.lean:409`). -/
theorem stepFn_definedGuardK_raise (m : Machine) (exc : Value) :
    Interp.stepFn (deliverA (.esc (.raiseJ exc)) m [.definedGuardK])
      = .next { m with ctl := .value .nil, kont := [] } := rfl

/-- **A `CatchFree` continuation that is not `JumpOpaque`.** So `run_split`'s third hypothesis
is not a formality that every literal kont happens to satisfy — it is *false* for the whole
handler family, and `JumpOpaque`'s own docstring ("a `rescue` in `K` catching what the sub-run
raised") is describing this. `run_pushK` asks only for the first. -/
theorem not_jumpOpaque_definedGuardK : ¬ JumpOpaque [.definedGuardK] := by
  intro h
  refine h { ctl := .jump (.raiseJ .nil), kont := [.definedGuardK], stack := [],
             frames := #[], heap := ⟨#[]⟩ } (.raiseJ .nil) 2 .nil
    { ctl := .value .nil, kont := [], stack := [], frames := #[], heap := ⟨#[]⟩ } ?_
  rfl

theorem catchFree_definedGuardK : RubyCore.Proof.CatchFree [.definedGuardK] := by
  intro k hk t; rcases List.mem_singleton.mp hk with rfl; simp

/-- **The decomposition at a handler continuation, with nothing to discharge.** `run_split`
cannot be applied at `[.definedGuardK]` at all (`not_jumpOpaque_definedGuardK`); `run_pushK`
needs `catchFree_definedGuardK`, which is one line. The rescue family is the same, one
`catchFree_controlKonts` away. -/
theorem run_pushK_guard :
    ∀ (fuel : Nat) (m : Machine),
      Interp.run fuel (pushK [.definedGuardK] m) = (runA fuel m).out [.definedGuardK] :=
  run_pushK [.definedGuardK] catchFree_definedGuardK

theorem run_pushK_rescue (n : BeginNode) :
    ∀ (fuel : Nat) (m : Machine),
      Interp.run fuel (pushK [.beginBodyK n] m) = (runA fuel m).out [.beginBodyK n] :=
  run_pushK [.beginBodyK n] (by intro k hk t; rcases List.mem_singleton.mp hk with rfl; simp)

/-! ## And the information the projection threw away, at the one place it matters

A raise in flight at an empty continuation is an **answer**, not a dead end. `Interp.run`
reports it as `.uncaught` — the run is over — and `Evals` then discards it; `runA` reports it
as `.esc (.raiseJ exc)` together with the machine, which is exactly what a handler in `K`
needs. The two lemmas below are the same machine seen the two ways. -/

theorem answerPoint_raise {m : Machine} {exc : Value} (hc : m.ctl = .jump (.raiseJ exc))
    (hk : m.kont = []) : answerPoint m = some (.esc (.raiseJ exc)) := by
  rw [answerPoint, hk]; simp only; rw [hc]

/-- What the *inner* run says: the program is over. This is the arm `Evals` drops. -/
theorem run_nil_raise {m : Machine} {exc : Value} (hc : m.ctl = .jump (.raiseJ exc))
    (hk : m.kont = []) (f : Nat) : Interp.run (f + 1) m = .uncaught exc m := by
  rw [run_succ]
  have : Interp.stepFn m = .uncaught exc m := by
    simp only [Interp.stepFn, hc, Interp.unwind.eq_def, hk]
  rw [this]

/-- What the *outer* run says: the handler runs. One rewrite, no hypothesis about the jump —
the escape is carried rather than excluded. -/
theorem run_rescue_of_raise {m : Machine} {exc : Value} (n : BeginNode)
    (hc : m.ctl = .jump (.raiseJ exc)) (hk : m.kont = []) (fuel : Nat) :
    Interp.run fuel (pushK [.beginBodyK n] m)
      = Interp.run fuel (deliverA (.esc (.raiseJ exc)) m [.beginBodyK n]) := by
  rw [run_pushK_rescue n fuel m, runA_ans (answerPoint_raise hc hk)]
  rfl

#print axioms catchFree_iff_tagsOf_nil
#print axioms catchFree_controlKonts
#print axioms not_catchFree_catchK
#print axioms not_jumpOpaque_definedGuardK
#print axioms run_pushK_guard
#print axioms run_pushK_rescue
#print axioms run_rescue_of_raise

end Ratchet.Denote
