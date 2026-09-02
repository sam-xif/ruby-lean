import RubyCore.Interp
import RubyCore.Proof.FrameAttr

/-!
# `RubyCore/Proof/KontFrame.lean` — `stepFn` is local in the continuation tail

The theorem `ratchet/Denote/Sem/Frame.lean` names as `KontFrameCatchFree` and the ~40 rungs
behind the ratchet's fifth stall point consume: a step from a machine with more continuation
behind it is the same step with more continuation behind it.

**Not unconditional.** `throw` reads the *whole* continuation (`Interp/Reflect.lean`), so a
`catchK` in the appended tail can change a step; `ratchet`'s `not_KontFrame` exhibits that
machine. The hypothesis `CatchFree K` is what excludes it, and it holds at every kont a
`Judge` rule pushes.

The shape of the work, bottom-up: `Machine`'s readers do not see `kont`; the `Builtins` layer
threads the machine and never reads `kont` at all; `Interp`'s helpers either push or pass
through; `applyKont`/`unwind` read the head and pop, which is where the two pass-through
points (`kont = []`) come from.
-/

set_option autoImplicit false
set_option maxRecDepth 40000

namespace RubyCore
namespace Proof

/-! ## The tail, appended -/

/-- `m` with `K` appended below its own continuation.

**`@[reducible]`, and that is load-bearing.** The interpreter writes its machines as nested
record updates, which Lean collapses into one flat literal — so a goal about
`{ m with currentExc := e }` after a push is spelled with `kont := m.kont ++ K` inline rather
than as `pushK K _`. A non-reducible `pushK` is opaque to `simp`'s unifier there, and every
lemma below would have to be restated field-wise; reducible, the unifier looks through it and
one statement per function suffices. -/
@[reducible] def pushK (K : List Kont) (m : Machine) : Machine := { m with kont := m.kont ++ K }

@[simp, frameLem] theorem pushK_heap (K : List Kont) (m : Machine) : (pushK K m).heap = m.heap := rfl
@[simp, frameLem] theorem pushK_ctl (K : List Kont) (m : Machine) : (pushK K m).ctl = m.ctl := rfl
@[simp, frameLem] theorem pushK_stack (K : List Kont) (m : Machine) : (pushK K m).stack = m.stack := rfl
@[simp, frameLem] theorem pushK_frames (K : List Kont) (m : Machine) : (pushK K m).frames = m.frames := rfl
@[simp, frameLem] theorem pushK_globals (K : List Kont) (m : Machine) :
    (pushK K m).globals = m.globals := rfl
@[simp, frameLem] theorem pushK_out (K : List Kont) (m : Machine) : (pushK K m).out = m.out := rfl
@[simp, frameLem] theorem pushK_currentExc (K : List Kont) (m : Machine) :
    (pushK K m).currentExc = m.currentExc := rfl
@[simp, frameLem] theorem pushK_preludeMode (K : List Kont) (m : Machine) :
    (pushK K m).preludeMode = m.preludeMode := rfl
@[simp, frameLem] theorem pushK_kont (K : List Kont) (m : Machine) :
    (pushK K m).kont = m.kont ++ K := rfl

@[simp, frameLem] theorem pushK_currentFrame (K : List Kont) (m : Machine) :
    (pushK K m).currentFrame = m.currentFrame := rfl

/-- Every field but `kont` is copied, so a `pushK` commutes with any record update that does
not touch `kont`. The three that occur in this layer, as `rfl` lemmas. -/
@[simp, frameLem] theorem pushK_setHeap (K : List Kont) (m : Machine) (h : Heap) :
    pushK K { m with heap := h } = { pushK K m with heap := h } := rfl

@[simp, frameLem] theorem pushK_setOut (K : List Kont) (m : Machine) (s : String) :
    pushK K { m with out := s } = { pushK K m with out := s } := rfl

/-! ## `BRes`, with the tail carried through -/

/-- A builtin result, with the appended tail carried into whichever machine it holds. -/
def bpush (K : List Kont) : BRes → BRes
  | .ok v m => .ok v (pushK K m)
  | .err c s m => .err c s (pushK K m)
  | .throwV v m => .throwV v (pushK K m)
  | .unsupported r => .unsupported r

@[simp, frameLem] theorem bpush_ok (K : List Kont) (v : Value) (m : Machine) :
    bpush K (.ok v m) = .ok v (pushK K m) := rfl
@[simp, frameLem] theorem bpush_err (K : List Kont) (c : ObjId) (s : String) (m : Machine) :
    bpush K (.err c s m) = .err c s (pushK K m) := rfl
@[simp, frameLem] theorem bpush_throwV (K : List Kont) (v : Value) (m : Machine) :
    bpush K (.throwV v m) = .throwV v (pushK K m) := rfl
@[simp, frameLem] theorem bpush_unsupported (K : List Kont) (r : String) :
    bpush K (.unsupported r) = .unsupported r := rfl

@[simp, frameLem] theorem setCurrentFrame_frame (K : List Kont) (m : Machine) (f : Frame) :
    (pushK K m).setCurrentFrame f = pushK K (m.setCurrentFrame f) := by
  simp only [Machine.setCurrentFrame, pushK_stack, pushK_frames]
  split <;> rfl

/-! ## `StepResult`, with the tail carried through -/

/-- A step result, with the appended tail carried into whichever machine it holds. The
non-`next` outcomes are unchanged: they end the run, and what the continuation would have done
next is exactly what does not happen. -/
def frameR (K : List Kont) : StepResult → StepResult
  | .next m => .next (pushK K m)
  | r => r

@[simp, frameLem] theorem frameR_next (K : List Kont) (m : Machine) :
    frameR K (.next m) = .next (pushK K m) := rfl
@[simp, frameLem] theorem frameR_done (K : List Kont) (v : Value) (m : Machine) :
    frameR K (.done v m) = .done v m := rfl
@[simp, frameLem] theorem frameR_uncaught (K : List Kont) (v : Value) (m : Machine) :
    frameR K (.uncaught v m) = .uncaught v m := rfl
@[simp, frameLem] theorem frameR_unsupported (K : List Kont) (r : String) :
    frameR K (.unsupported r) = .unsupported r := rfl
@[simp, frameLem] theorem frameR_stuck (K : List Kont) (r : String) :
    frameR K (.stuck r) = .stuck r := rfl

/-- **A builtin's answer does not depend on the continuation.** The statement every function
in the `Builtins` layer gets, spelled once. -/
def BFrame {α : Type} (f : Machine → α) (g : List Kont → α → α) : Prop :=
  ∀ (K : List Kont) (m : Machine), f (pushK K m) = g K (f m)

/-! ## The `Builtins` leaves

Every one of these produces its machine by a record update that does not touch `kont`, so each
is `rfl` after both sides unfold. They are stated (rather than left to the dispatcher's own
`simp`) because the dispatchers are large and a named rewrite is what keeps their proofs from
re-deriving the same fact sixty times. -/

open Builtins

@[simp, frameLem] theorem allocStrEnc_frame (K : List Kont) (m : Machine) (s : String) (b : Bool) :
    allocStrEnc (pushK K m) s b = ((allocStrEnc m s b).1, pushK K (allocStrEnc m s b).2) := rfl

@[simp, frameLem] theorem allocStr_frame (K : List Kont) (m : Machine) (s : String) :
    allocStr (pushK K m) s = ((allocStr m s).1, pushK K (allocStr m s).2) := rfl

@[simp, frameLem] theorem allocArr_frame (K : List Kont) (m : Machine) (xs : Array Value) :
    allocArr (pushK K m) xs = ((allocArr m xs).1, pushK K (allocArr m xs).2) := rfl

@[simp, frameLem] theorem allocHsh_frame (K : List Kont) (m : Machine) (xs : Array (Value × Value)) :
    allocHsh (pushK K m) xs = ((allocHsh m xs).1, pushK K (allocHsh m xs).2) := rfl

@[simp, frameLem] theorem allocExc_frame (K : List Kont) (m : Machine) (c : ObjId) (s : String) :
    allocExc (pushK K m) c s = ((allocExc m c s).1, pushK K (allocExc m c s).2) := rfl

@[simp, frameLem] theorem dupObj_frame (K : List Kont) (m : Machine) (o : ObjId) (kf : Bool) :
    dupObj (pushK K m) o kf = ((dupObj m o kf).1, pushK K (dupObj m o kf).2) := rfl

@[simp, frameLem] theorem okStr_frame (K : List Kont) (m : Machine) (s : String) :
    okStr (pushK K m) s = bpush K (okStr m s) := rfl

@[simp, frameLem] theorem okStrEnc_frame (K : List Kont) (m : Machine) (b : Bool) (s : String) :
    okStrEnc (pushK K m) b s = bpush K (okStrEnc m b s) := rfl

@[simp, frameLem] theorem okStrFrom_frame (K : List Kont) (m : Machine) (src : Value) (s : String) :
    okStrFrom (pushK K m) src s = bpush K (okStrFrom m src s) := rfl

@[simp, frameLem] theorem inspectP_frame (K : List Kont) (m : Machine) (v : Value) :
    inspectP (pushK K m) v = inspectP m v := rfl

@[simp, frameLem] theorem toSP_frame (K : List Kont) (m : Machine) (v : Value) :
    toSP (pushK K m) v = toSP m v := rfl

@[simp, frameLem] theorem coerceFailed_frame (K : List Kont) (c : String) (m : Machine) (b : Value) :
    coerceFailed c (pushK K m) b = bpush K (coerceFailed c m b) := rfl

@[simp, frameLem] theorem frozenErr_frame (K : List Kont) (m : Machine) (recv : Value) (c : String) :
    frozenErr (pushK K m) recv c = bpush K (frozenErr m recv c) := by
  simp only [frozenErr, inspectP_frame]
  cases inspectP m recv <;> rfl

/-- **The exception-message reader**, which is the one leaf that is *not* `rfl`: it walks the
heap. `pushK` does not move the heap, so it is a projection. -/
@[simp, frameLem] theorem emit_frame (K : List Kont) (m : Machine) (s : String) :
    Machine.emit (pushK K m) s = pushK K (Machine.emit m s) := rfl

/-! ## The two tactics every proof below is written with

`frame_simp` fires the framing lemmas; `frame_arms` walks a `match`'s arms and closes each.
Both are macros rather than `simp` calls spelled out per proof because the dispatchers are
large and the recipe has to be identical at every one of them — a proof that needed its own
tactic would be a proof that found something, which is worth seeing.

`eq_def` rather than the per-arm equations at every dispatcher, because the equation compiler
declines to generate them for matches this large ("failed to generate equational theorem") and
the raw unfolding is all that is needed. -/

/-- Fire every framing lemma in this file. They are all `@[simp]`, so this is the default set
restricted to `only` by nothing — `simp` with the standard lemmas is what reduces the
`pushK`-of-a-record-update shapes back to `pushK`-of-a-machine. -/
syntax "frame_simp" : tactic
macro_rules
  | `(tactic| frame_simp) => `(tactic| try simp only [frameLem])

/-- The arm walker. `split` peels one `match`/`if` at a time; each arm is then either `rfl`
after the framing set has fired, or — for the arms a `split` leaves *contradictory* hypotheses
on — `simp_all`. That last stage is deliberately a **per-goal last resort** rather than a
stage in the `<;>` chain: run eagerly, `simp_all` re-folds goals that `rfl` would have closed,
which cost `callClosure` and three `Builtins` dispatchers before it was demoted. -/
syntax "frame_arms" : tactic
macro_rules
  | `(tactic| frame_arms) =>
    `(tactic| (repeat' first | rfl | split) <;>
        (try frame_simp) <;>
        (first | rfl | (try simp_all (maxSteps := 400000) [frameLem]) <;> (try rfl) | skip))

/-! ## The `Builtins` mid-level: the fuel walks and the four higher-order helpers

Two shapes here that the leaves did not have. **A fuel-recursive walk** (`putsGo`,
`flattenAll`) needs an induction on the fuel, and `putsGo` is the one that writes (`emit`), so
its statement carries the machine out. **A continuation-taking helper** (`withIndex`,
`numBin`, `numCmp`, `binArg`) frames only if its continuation does, so the hypothesis is
pointwise — which is exactly what holds at the call sites, where the continuation is a lambda
closing over the same machine. -/

@[frameLem] theorem putsGo_frame (K : List Kont) : ∀ (fuel : Nat) (m : Machine) (args : List Value),
    putsGo (pushK K m) args fuel = (putsGo m args fuel).map (pushK K)
  | 0, _, _ => rfl
  | fuel + 1, m, args => by
    rw [putsGo, putsGo]
    induction args generalizing m with
    | nil => rfl
    | cons a rest ih =>
      simp only [List.foldlM_cons, pushK_heap, toSP_frame, emit_frame,
        putsGo_frame K fuel m]
      (repeat' split) <;>
        first
          | rfl
          | (simp only [Option.some_bind, Option.none_bind, Option.map_eq_map,
                Option.map_none, Option.bind_map]; try rfl)
          | simp_all
      all_goals (try exact ih _)
      all_goals (try (cases hg : putsGo m _ fuel <;> simp_all))

@[simp, frameLem] theorem flattenAll_frame (K : List Kont) : ∀ (fuel : Nat) (m : Machine) (v : Value),
    flattenAll (pushK K m) v fuel = flattenAll m v fuel
  | 0, _, _ => rfl
  | fuel + 1, m, v => by
    have hf : ∀ x, flattenAll (pushK K m) x fuel = flattenAll m x fuel :=
      fun x => flattenAll_frame K fuel m x
    rw [flattenAll, flattenAll]
    frame_simp
    cases arrPayload? m.heap v with
    | none => rfl
    | some xs => simp only [hf]

/-- `Kernel#print`'s fold: `to_s` each argument and emit it, failing the whole call if any
`to_s` is impure. `Option`-monadic rather than the plain `foldl` the allocating folds use, so
it gets its own induction.

**Written with `pure`, not `some`, and that is not cosmetic**: the source writes `pure (m.emit
s)` inside a `do`, and `rw` matches up to reducible unfolding but not through the `Monad Option`
instance — a `some`-spelled version of this lemma is not found in the real goal. The rest of
this layer never noticed the difference because nothing else in it is monadic. -/
@[frameLem] theorem printFold_frame (K : List Kont) :
    ∀ (args : List Value) (m : Machine),
      List.foldlM (fun (m : Machine) (a : Value) =>
          match toSP m a with
          | .ok s => pure (m.emit s)
          | .error _ => none) (pushK K m) args =
        (List.foldlM (fun (m : Machine) (a : Value) =>
          match toSP m a with
          | .ok s => pure (m.emit s)
          | .error _ => none) m args).map (pushK K)
  | [], _ => rfl
  | a :: rest, m => by
    simp only [List.foldlM_cons, toSP_frame]
    cases toSP m a with
    | error e => rfl
    | ok str =>
      simp only [emit_frame]
      exact printFold_frame K rest (m.emit str)

/-- **`Kernel#print`'s whole arm**, so that it can be discharged by `exact`.

Why the arm and not just the fold: the fold *inside the arm* cannot be reached by `rw`. Its
step contains a `match`, and a `match` written in one declaration compiles to a matcher
constant belonging to **that** declaration — so the version spelled here is a different
constant from `Builtins/Objects.lean`'s, and `rw`'s keyed matching (syntactic up to reducible
unfolding) does not see through it. `exact` does, because `isDefEq` unfolds matchers. So the
statement is lifted to the level where one `exact` discharges the goal. -/
theorem printArm_frame (K : List Kont) (m : Machine) (args : List Value) :
    (match List.foldlM (fun (m : Machine) (a : Value) =>
        match toSP m a with
        | .ok s => pure (m.emit s)
        | .error _ => none) (pushK K m) args with
      | some m' => BRes.ok .nil m'
      | none => BRes.unsupported "print: impure to_s") =
      bpush K (match List.foldlM (fun (m : Machine) (a : Value) =>
        match toSP m a with
        | .ok s => pure (m.emit s)
        | .error _ => none) m args with
      | some m' => BRes.ok .nil m'
      | none => BRes.unsupported "print: impure to_s") := by
  rw [printFold_frame]
  cases List.foldlM (fun (m : Machine) (a : Value) =>
      match toSP m a with
      | .ok s => pure (m.emit s)
      | .error _ => none) m args <;> rfl

/-- **`Kernel#p`'s inner walk.** A `let rec` inside the arm, so its name is
`runObjects.go`; same shape as `printFold_frame` one constructor over (`inspect` rather than
`to_s`, and a newline per value). -/
@[frameLem] theorem objectsGo_frame (K : List Kont) :
    ∀ (m : Machine) (args : List Value),
      runObjects.go (pushK K m) args = (runObjects.go m args).map (pushK K)
  | _, [] => rfl
  | m, a :: rest => by
    rw [runObjects.go, runObjects.go]
    simp only [inspectP_frame]
    cases inspectP m a with
    | error e => rfl
    | ok str =>
      simp only [emit_frame]
      exact objectsGo_frame K (m.emit (str ++ "\n")) rest

/-! ### The four continuation-taking helpers, with the continuation's framing as a hypothesis

Unfolding them was the first attempt and it does not scale: `numBin`'s two continuations are
applied inside a match, and `simp` unfolding that across `runNumerics`' ~90 arms diverges
(recursion depth, at any limit). Stated as lemmas with a *pointwise* hypothesis instead, they
are applied by `exact`/`refine` — which is also what gets past the matcher-constant problem,
since `isDefEq` unfolds matchers and `simp`'s matching does not.

The hypothesis is exactly what holds at every call site: the continuation is a lambda closing
over the same machine, so the pushed version is the unpushed one with the tail carried. -/

theorem binArg_frame (K : List Kont) (m : Machine) (args : List Value) (k k' : Value → BRes)
    (hk : ∀ b, k' b = bpush K (k b)) :
    binArg (pushK K m) args k' = bpush K (binArg m args k) := by
  simp only [binArg]
  split
  · exact hk _
  · rfl

theorem numBin_frame (K : List Kont) (cls : String) (m : Machine) (a b : Value)
    (fi fi' : Int → Int → BRes) (ff ff' : Float → Float → BRes)
    (hi : ∀ x y, fi' x y = bpush K (fi x y))
    (hf : ∀ x y, ff' x y = bpush K (ff x y)) :
    numBin cls (pushK K m) a b fi' ff' = bpush K (numBin cls m a b fi ff) := by
  simp only [numBin]
  split
  · exact hi _ _
  · exact hf _ _
  · exact hf _ _
  · exact hf _ _
  · exact coerceFailed_frame K cls m b

theorem numCmp_frame (K : List Kont) (cls : String) (m : Machine) (a b : Value)
    (k k' : Ordering → BRes) (hk : ∀ o, k' o = bpush K (k o)) :
    numCmp cls (pushK K m) a b k' = bpush K (numCmp cls m a b k) := by
  simp only [numCmp, pushK_heap]
  split
  · exact hk _
  · -- the `Float` comparison chain: three nested `if`s over the same two conditions on both
    -- sides, so each branch is `hk` at its own `Ordering`
    repeat' first | exact hk _ | rfl | split
  · rfl

theorem withIndex_frame (K : List Kont) (m : Machine) (v : Value) (why : String)
    (k k' : Int → BRes) (numMsg : Bool) (hk : ∀ n, k' n = bpush K (k n)) :
    withIndex (pushK K m) v why k' numMsg = bpush K (withIndex m v why k numMsg) := by
  simp only [withIndex, pushK_heap]
  split
  · exact hk _
  · rfl
  · rfl

/-- The closer for an arm whose body is one of the four above, **as a fixpoint loop rather
than a recursive macro**: a `macro_rules` that mentions itself does not expand, so the first
version of this silently failed on every nested case (a `binArg` whose continuation is a
`numBin`) and cost an hour. `repeat'` gets the nesting for free, since each `refine` leaves the
continuation's obligation as a goal and the loop is applied to all goals. -/
syntax "frame_hof" : tactic
macro_rules
  | `(tactic| frame_hof) =>
    `(tactic| repeat' first
        | rfl
        | (frame_simp; done)
        | refine binArg_frame _ _ _ _ _ (fun _ => ?_)
        | refine numBin_frame _ _ _ _ _ _ _ _ _ (fun _ _ => ?_) (fun _ _ => ?_)
        | refine numCmp_frame _ _ _ _ _ _ _ (fun _ => ?_)
        | refine withIndex_frame _ _ _ _ _ _ _ (fun _ => ?_)
        | split)

/-! ## The rest of the `Builtins` mid-level

The four continuation-taking helpers (`withIndex`, `numBin`, `numCmp`, `binArg`) get no lemma
of their own: they are small, and *unfolding* them at the dispatcher applies the continuation,
which is what turns the goal into the leaf lemmas above. `simp`-unfolding them is therefore
part of the dispatcher recipe rather than a step before it. -/

@[frameLem] theorem putsImpl_frame (K : List Kont) (m : Machine) (args : List Value) :
    putsImpl (pushK K m) args = bpush K (putsImpl m args) := by
  rw [putsImpl, putsImpl, putsGo_frame]
  cases putsGo m args 100 <;> rfl

@[frameLem] theorem raiseClass_frame (K : List Kont) (m : Machine) (cls : ObjId) (msg : Option Value) :
    raiseClass (pushK K m) cls msg = bpush K (raiseClass m cls msg) := by
  rw [raiseClass.eq_def, raiseClass.eq_def]
  frame_simp
  try simp only [allocExc_frame]
  frame_arms

@[frameLem] theorem raiseImpl_frame (K : List Kont) (m : Machine) (args : List Value) :
    raiseImpl (pushK K m) args = bpush K (raiseImpl m args) := by
  rw [raiseImpl.eq_def, raiseImpl.eq_def]
  frame_simp
  try simp only [raiseClass_frame]
  frame_arms

set_option maxHeartbeats 2000000 in
@[frameLem] theorem newImpl_frame (K : List Kont) (m : Machine) (recv : Value) (args : List Value) :
    newImpl (pushK K m) recv args = bpush K (newImpl m recv args) := by
  rw [newImpl.eq_def, newImpl.eq_def]
  frame_simp
  -- **`split` does not scale to this one**, and it is the only place in the layer where that
  -- shows: the arms are nested five `if`s deep, and `split`'s own `simp` exceeds its step
  -- budget on a goal that size (no option raises it). Case-splitting the conditions by hand
  -- keeps every `simp only` local, which is all the automation was doing anyway.
  cases recv with
  | ref k =>
    cases hc : m.heap.classPayload? k with
    | none => simp only [hc]; frame_simp
    | some c =>
      simp only [hc]
      by_cases h1 : c.isModule = true
      · simp only [if_pos h1]; frame_simp
      · simp only [if_neg h1]
        by_cases h2 : (ancestors m.heap k).contains Boot.exceptionId = true
        · simp only [if_pos h2]; frame_arms
        · simp only [if_neg h2]
          by_cases h3 : (ancestors m.heap k).contains Boot.stringId = true
          · simp only [if_pos h3]; frame_arms
          · simp only [if_neg h3]
            by_cases h4 : (ancestors m.heap k).contains Boot.arrayId = true
            · simp only [if_pos h4]; frame_arms
            · simp only [if_neg h4]
              by_cases h5 : (ancestors m.heap k).contains Boot.hashId = true
              · simp only [if_pos h5]; frame_arms
              · simp only [if_neg h5]
                by_cases h6 : k == Boot.randomId
                · simp only [if_pos h6]; frame_arms
                · simp only [if_neg h6]
                  by_cases h7 : k == Boot.regexpId
                  · simp only [if_pos h7]; frame_arms
                  · simp only [if_neg h7]; frame_arms
  | _ => rfl

@[frameLem] theorem joinImpl_frame (K : List Kont) (m : Machine) (recv : Value) (args : List Value) :
    joinImpl (pushK K m) recv args = bpush K (joinImpl m recv args) := by
  rw [joinImpl.eq_def, joinImpl.eq_def]
  frame_simp
  try simp only [flattenAll_frame]
  frame_arms

@[frameLem] theorem sortImpl_frame (K : List Kont) (m : Machine) (recv : Value) :
    sortImpl (pushK K m) recv = bpush K (sortImpl m recv) := by
  rw [sortImpl.eq_def, sortImpl.eq_def]
  frame_simp

  frame_arms

/-! ## The `$~` write, and the `Regex` layer

`setMatchGlobals` is the one write in this layer that is **not** to the heap: `$~` is
frame-local (L121), so it goes through `Machine.matchFrameId`, a fuel walk over the frame
stack. `pushK` preserves both the stack and the frame array, but the walk carries `m` as a
captured argument, so agreement is an induction rather than a projection — the same shape
`ratchet`'s `getLocal_go_reCtl` has. -/

@[frameLem] theorem matchFrameOwner_frame (K : List Kont) (m : Machine) :
    ∀ (fuel : Nat) (fid : FrameId),
      Machine.matchFrameOwner (pushK K m) fid fuel = Machine.matchFrameOwner m fid fuel := by
  intro fuel
  induction fuel with
  | zero => intro fid; rfl
  | succ n ih =>
    intro fid
    simp only [Machine.matchFrameOwner, pushK_frames]
    split
    · exact ih _
    · rfl

@[frameLem] theorem matchFrameId_go_frame (K : List Kont) (m : Machine) :
    ∀ (fuel : Nat) (l : List FrameId),
      Machine.matchFrameId.go (pushK K m) l fuel = Machine.matchFrameId.go m l fuel := by
  intro fuel
  induction fuel with
  | zero => intro l; cases l <;> rfl
  | succ n ih =>
    intro l
    cases l with
    | nil => rfl
    | cons fid rest =>
      simp only [Machine.matchFrameId.go, pushK_frames]
      split
      · split
        · rfl
        · exact ih _
      · split
        · split
          · exact matchFrameOwner_frame K m n _
          · exact ih _
        · rfl

@[simp, frameLem] theorem matchFrameId_frame (K : List Kont) (m : Machine) :
    (pushK K m).matchFrameId = m.matchFrameId := by
  simp only [Machine.matchFrameId, pushK_stack]
  exact matchFrameId_go_frame K m _ _

@[simp, frameLem] theorem setLastMatchValue_frame (K : List Kont) (m : Machine) (v : Value) :
    (pushK K m).setLastMatchValue v = pushK K (m.setLastMatchValue v) := by
  simp only [Machine.setLastMatchValue, matchFrameId_frame, pushK_frames]
  split <;> rfl

@[simp, frameLem] theorem setMatchGlobals_frame (K : List Kont) (m : Machine) (md : Option Value) :
    setMatchGlobals (pushK K m) md = pushK K (setMatchGlobals m md) := by
  simp only [setMatchGlobals, setLastMatchValue_frame]

@[simp, frameLem] theorem allocRegexp_frame (K : List Kont) (m : Machine) (src : String) (opts : Nat) :
    allocRegexp (pushK K m) src opts =
      ((allocRegexp m src opts).1, pushK K (allocRegexp m src opts).2) := rfl

@[simp, frameLem] theorem allocMData_frame (K : List Kont) (m : Machine) (subj : String)
    (caps : Array (Option (Nat × Nat))) (names : List (String × Nat)) (bin : Bool) :
    allocMData (pushK K m) subj caps names bin =
      ((allocMData m subj caps names bin).1, pushK K (allocMData m subj caps names bin).2) := rfl

@[simp, frameLem] theorem setLastMatch_frame (K : List Kont) (m : Machine) (s src : String) (opts : Nat)
    (hits : List (Nat × Nat × Array (Option (Nat × Nat)))) (bin : Bool) :
    setLastMatch (pushK K m) s src opts hits bin =
      pushK K (setLastMatch m s src opts hits bin) := by
  simp only [setLastMatch]
  split
  · simp only [setMatchGlobals_frame]
  · simp only [allocMData_frame, setMatchGlobals_frame]

/-- **The one allocating `foldl` in the layer** (`String#chars`, which allocates a String per
character). The machine threads through the accumulator, so this is a list induction rather
than a rewrite — the same shape `putsGo` needed, one level down. -/
@[simp, frameLem] theorem charsFold_frame (K : List Kont) (bin : Bool) :
    ∀ (l : List Char) (acc : Array Value) (m : Machine),
      l.foldl (fun (x : Array Value × Machine) c =>
          ((x.1.push (allocStrEnc x.2 (String.singleton c) bin).1),
            (allocStrEnc x.2 (String.singleton c) bin).2)) (acc, pushK K m) =
        ((l.foldl (fun (x : Array Value × Machine) c =>
            ((x.1.push (allocStrEnc x.2 (String.singleton c) bin).1),
              (allocStrEnc x.2 (String.singleton c) bin).2)) (acc, m)).1,
          pushK K (l.foldl (fun (x : Array Value × Machine) c =>
            ((x.1.push (allocStrEnc x.2 (String.singleton c) bin).1),
              (allocStrEnc x.2 (String.singleton c) bin).2)) (acc, m)).2)
  | [], _, _ => rfl
  | c :: rest, acc, m => by
    simp only [List.foldl_cons, allocStrEnc_frame]
    exact charsFold_frame K bin rest _ (allocStrEnc m (String.singleton c) bin).2

/-! ## The allocating fold, once and polymorphically

`Builtins` builds arrays by folding an allocation over a list, and does it in five different
shapes (characters, group names, capture spans, hash entries, sort keys). One lemma covers all
of them: what the fold needs is that the *step* frames, which is the hypothesis, and then the
machine threads through the accumulator by induction. Stated for `List.foldl` and again for
`Array.foldl`, which is a different function. -/

@[frameLem] theorem allocFold_frame {α : Type} (K : List Kont) (f : Machine → α → Value × Machine)
    (hf : ∀ (m : Machine) (a : α), f (pushK K m) a = ((f m a).1, pushK K (f m a).2)) :
    ∀ (l : List α) (acc : Array Value) (m : Machine),
      List.foldl (fun (x : Array Value × Machine) (a : α) =>
          (x.1.push (f x.2 a).1, (f x.2 a).2)) (acc, pushK K m) l =
        ((List.foldl (fun (x : Array Value × Machine) (a : α) =>
            (x.1.push (f x.2 a).1, (f x.2 a).2)) (acc, m) l).1,
          pushK K (List.foldl (fun (x : Array Value × Machine) (a : α) =>
            (x.1.push (f x.2 a).1, (f x.2 a).2)) (acc, m) l).2)
  | [], _, _ => rfl
  | a :: rest, acc, m => by
    simp only [List.foldl_cons, hf m a]
    exact allocFold_frame K f hf rest _ (f m a).2

@[frameLem] theorem allocFoldArray_frame {α : Type} (K : List Kont) (f : Machine → α → Value × Machine)
    (hf : ∀ (m : Machine) (a : α), f (pushK K m) a = ((f m a).1, pushK K (f m a).2))
    (xs : Array α) (acc : Array Value) (m : Machine) :
    Array.foldl (fun (x : Array Value × Machine) (a : α) =>
        (x.1.push (f x.2 a).1, (f x.2 a).2)) (acc, pushK K m) xs =
      ((Array.foldl (fun (x : Array Value × Machine) (a : α) =>
          (x.1.push (f x.2 a).1, (f x.2 a).2)) (acc, m) xs).1,
        pushK K (Array.foldl (fun (x : Array Value × Machine) (a : α) =>
          (x.1.push (f x.2 a).1, (f x.2 a).2)) (acc, m) xs).2) := by
  simp only [← Array.foldl_toList]
  exact allocFold_frame K f hf xs.toList acc m

/-- **The fold lemma to reach for**, and the one that does not depend on `simp` matching a
lambda. The step is abstract, the hypothesis is that the step frames pointwise, and the
accumulator is any type — so a use site is one `exact` and the elaborator unifies the step up
to definitional equality.

That last part is the point. A fold step written with a `match` compiles to a **matcher
constant belonging to its own declaration**, so a lemma that spells the same syntax does not
produce the same term and `rw`/`simp` cannot match it. `exact` can, because `isDefEq` unfolds
matchers. The concrete `@[simp]` instances below are kept for the sites where `simp` does
match (they save the hypothesis proof), but this is the general tool. -/
@[frameLem] theorem foldPair_frame {α β : Type} (K : List Kont) (f : β × Machine → α → β × Machine)
    (hf : ∀ (p : β) (m : Machine) (a : α),
      f (p, pushK K m) a = ((f (p, m) a).1, pushK K (f (p, m) a).2)) :
    ∀ (l : List α) (acc : β) (m : Machine),
      l.foldl f (acc, pushK K m) =
        ((l.foldl f (acc, m)).1, pushK K (l.foldl f (acc, m)).2)
  | [], _, _ => rfl
  | a :: rest, acc, m => by
    simp only [List.foldl_cons, hf acc m a]
    exact foldPair_frame K f hf rest _ (f (acc, m) a).2

/-- The machine-**first** twin: `defineAttr` accumulates `(machine, names)` rather than
`(names, machine)`. -/
theorem foldPairFst_frame {α β : Type} (K : List Kont) (f : Machine × β → α → Machine × β)
    (hf : ∀ (m : Machine) (p : β) (a : α),
      f (pushK K m, p) a = (pushK K (f (m, p) a).1, (f (m, p) a).2)) :
    ∀ (l : List α) (m : Machine) (acc : β),
      List.foldl f (pushK K m, acc) l =
        (pushK K (List.foldl f (m, acc) l).1, (List.foldl f (m, acc) l).2)
  | [], _, _ => rfl
  | a :: rest, m, acc => by
    simp only [List.foldl_cons, hf m acc a]
    exact foldPairFst_frame K f hf rest (f (m, acc) a).1 (f (m, acc) a).2

/-- The `foldr` twin. `String#split` builds its result right-to-left, so it needs one. -/
theorem foldrPair_frame {α β : Type} (K : List Kont) (f : α → β × Machine → β × Machine)
    (hf : ∀ (a : α) (p : β) (m : Machine),
      f a (p, pushK K m) = ((f a (p, m)).1, pushK K (f a (p, m)).2)) :
    ∀ (l : List α) (acc : β) (m : Machine),
      List.foldr f (acc, pushK K m) l =
        ((List.foldr f (acc, m) l).1, pushK K (List.foldr f (acc, m) l).2)
  | [], _, _ => rfl
  | a :: rest, acc, m => by
    simp only [List.foldr_cons, foldrPair_frame K f hf rest acc m]
    exact hf a _ _

/-- And the `Array.foldl` twin, by `Array.foldl_toList`. -/
theorem foldPairArray_frame {α β : Type} (K : List Kont) (f : β × Machine → α → β × Machine)
    (hf : ∀ (p : β) (m : Machine) (a : α),
      f (p, pushK K m) a = ((f (p, m) a).1, pushK K (f (p, m) a).2))
    (xs : Array α) (acc : β) (m : Machine) :
    Array.foldl f (acc, pushK K m) xs =
      ((Array.foldl f (acc, m) xs).1, pushK K (Array.foldl f (acc, m) xs).2) := by
  simp only [← Array.foldl_toList]
  exact foldPair_frame K f hf xs.toList acc m

/-! ### The three concrete fold shapes `Builtins` actually uses

The polymorphic lemma above is the argument; these are the instances, because `simp` matches
*syntactically* and the step functions in the interpreter are written out rather than
abstracted. Each is one application of `allocFold_frame` — the naming follows what the fold
builds. -/

@[simp, frameLem] theorem namesFold_frame (K : List Kont) (l : List (String × Nat)) (acc : Array Value)
    (m : Machine) :
    List.foldl (fun (x : Array Value × Machine) (p : String × Nat) =>
        (x.1.push (allocStr x.2 p.1).1, (allocStr x.2 p.1).2)) (acc, pushK K m) l =
      ((List.foldl (fun (x : Array Value × Machine) (p : String × Nat) =>
          (x.1.push (allocStr x.2 p.1).1, (allocStr x.2 p.1).2)) (acc, m) l).1,
        pushK K (List.foldl (fun (x : Array Value × Machine) (p : String × Nat) =>
          (x.1.push (allocStr x.2 p.1).1, (allocStr x.2 p.1).2)) (acc, m) l).2) :=
  allocFold_frame K (fun m p => allocStr m p.1) (fun _ _ => rfl) l acc m

@[simp, frameLem] theorem capsFold_frame (K : List Kont) (str : String) (bin : Bool)
    (l : List (Option (Nat × Nat))) (acc : Array Value) (m : Machine) :
    List.foldl (fun (x : Array Value × Machine) (sp : Option (Nat × Nat)) =>
        match sp with
        | some (a, b) => (x.1.push (allocStrEnc x.2 (charSlice str a b) bin).1,
                          (allocStrEnc x.2 (charSlice str a b) bin).2)
        | none => (x.1.push Value.nil, x.2)) (acc, pushK K m) l =
      ((List.foldl (fun (x : Array Value × Machine) (sp : Option (Nat × Nat)) =>
          match sp with
          | some (a, b) => (x.1.push (allocStrEnc x.2 (charSlice str a b) bin).1,
                            (allocStrEnc x.2 (charSlice str a b) bin).2)
          | none => (x.1.push Value.nil, x.2)) (acc, m) l).1,
        pushK K (List.foldl (fun (x : Array Value × Machine) (sp : Option (Nat × Nat)) =>
          match sp with
          | some (a, b) => (x.1.push (allocStrEnc x.2 (charSlice str a b) bin).1,
                            (allocStrEnc x.2 (charSlice str a b) bin).2)
          | none => (x.1.push Value.nil, x.2)) (acc, m) l).2) :=
  by
  -- Not an instance of `allocFold_frame`: the `none` arm pushes `nil` *inside* the match
  -- rather than through the step function, so the two shapes are equal only up to a case
  -- analysis. One induction instead.
  induction l generalizing acc m with
  | nil => rfl
  | cons sp rest ih =>
    cases sp with
    | none =>
      simp only [List.foldl_cons]
      exact ih (acc.push Value.nil) m
    | some p =>
      simp only [List.foldl_cons, allocStrEnc_frame]
      exact ih _ (allocStrEnc m (charSlice str p.1 p.2) bin).2

@[simp, frameLem] theorem capsFoldArray_frame (K : List Kont) (str : String) (bin : Bool)
    (xs : Array (Option (Nat × Nat))) (acc : Array Value) (m : Machine) :
    Array.foldl (fun (x : Array Value × Machine) (sp : Option (Nat × Nat)) =>
        match sp with
        | some (a, b) => (x.1.push (allocStrEnc x.2 (charSlice str a b) bin).1,
                          (allocStrEnc x.2 (charSlice str a b) bin).2)
        | none => (x.1.push Value.nil, x.2)) (acc, pushK K m) xs =
      ((Array.foldl (fun (x : Array Value × Machine) (sp : Option (Nat × Nat)) =>
          match sp with
          | some (a, b) => (x.1.push (allocStrEnc x.2 (charSlice str a b) bin).1,
                            (allocStrEnc x.2 (charSlice str a b) bin).2)
          | none => (x.1.push Value.nil, x.2)) (acc, m) xs).1,
        pushK K (Array.foldl (fun (x : Array Value × Machine) (sp : Option (Nat × Nat)) =>
          match sp with
          | some (a, b) => (x.1.push (allocStrEnc x.2 (charSlice str a b) bin).1,
                            (allocStrEnc x.2 (charSlice str a b) bin).2)
          | none => (x.1.push Value.nil, x.2)) (acc, m) xs).2) := by
  simp only [← Array.foldl_toList]
  exact capsFold_frame K str bin xs.toList acc m

/-- `runRegex`'s two `where` helpers that take a machine. `allMatches` and `runSearch` take
none, so they are the same computation on both sides and need no lemma — which is the useful
half of `Builtins` being written against the heap rather than against the machine. -/
@[simp, frameLem] theorem applyTo_frame (K : List Kont) (bid : String) (m : Machine) (src : String)
    (opts : Nat) (str : String) (bin : Bool) :
    runRegex.applyTo bid (pushK K m) src opts str bin =
      bpush K (runRegex.applyTo bid m src opts str bin) := by
  rw [runRegex.applyTo.eq_def, runRegex.applyTo.eq_def]
  frame_simp
  frame_arms

@[simp, frameLem] theorem regexApply_frame (K : List Kont) (bid : String) (m : Machine)
    (re subj : Value) :
    runRegex.regexApply bid (pushK K m) re subj =
      bpush K (runRegex.regexApply bid m re subj) := by
  rw [runRegex.regexApply.eq_def, runRegex.regexApply.eq_def]
  frame_simp
  frame_arms

@[frameLem] theorem floatToInt_frame (K : List Kont) (m : Machine) (y : Float) :
    floatToInt (pushK K m) y = bpush K (floatToInt m y) := by
  simp only [floatToInt]
  split <;> rfl

@[frameLem] theorem intBitRef_frame (K : List Kont) (m : Machine) (recv : Value)
    (args : List Value) :
    intBitRef (pushK K m) recv args = bpush K (intBitRef m recv args) := by
  rw [intBitRef.eq_def, intBitRef.eq_def]
  split
  · exact withIndex_frame _ _ _ _ _ _ _ (fun _ => by repeat' first | rfl | split)
  · rfl

/-! ## The dispatcher chain, bottom-up

`Builtins.run` chains six per-class rule files, each handing what it does not recognise to the
next: `run → runObjects → runNumerics → runStrings → runCollections → runModules → runRegex`.
They are proved in reverse, so each one's fall-through is a lemma already in the set. -/

/-! ### `runRegex`'s four machine-taking `where` helpers

`allMatches` and `runSearch` take no machine, so they are the same computation on both sides
and need no lemma — the useful half of `Builtins` being written against the heap. These four do
take one, and each threads it through an allocating fold, which is `foldPair_frame`'s job. -/

set_option maxHeartbeats 1000000 in
@[frameLem] theorem scanAll_frame (K : List Kont) (m : Machine) (str src : String) (opts : Nat)
    (bin : Bool) :
    runRegex.scanAll (pushK K m) str src opts bin =
      bpush K (runRegex.scanAll m str src opts bin) := by
  rw [runRegex.scanAll.eq_def, runRegex.scanAll.eq_def]
  frame_simp
  frame_arms
  all_goals frame_hof
  -- the outer `scan` fold, via the general lemma as a **conditional** rewrite: `rw` unifies
  -- the step from the goal and leaves its framing hypothesis as a side goal, which is what
  -- gets past having to write the step (and its matcher) out by hand
  -- the outer `scan` fold and the *inner* capture fold inside its step, both via the general
  -- lemma as a **conditional** rewrite: `rw` unifies the step from the goal and leaves its
  -- framing hypothesis as a side goal, which is what gets past having to write a step (and its
  -- matcher constant) out by hand. The loop is because the hypothesis contains the next fold.
  all_goals (repeat' first
    | rfl
    | (simp only [frameLem]; done)
    | (simp [frameLem]; done)
    | rw [foldPair_frame K]
    | rw [foldrPair_frame K]
    | rw [foldPairArray_frame K]
    | intro _
    | split)

set_option maxHeartbeats 1000000 in
@[frameLem] theorem splitBy_frame (K : List Kont) (m : Machine) (str src : String) (opts : Nat)
    (lim : Int) (bin : Bool) :
    runRegex.splitBy (pushK K m) str src opts lim bin =
      bpush K (runRegex.splitBy m str src opts lim bin) := by
  rw [runRegex.splitBy.eq_def, runRegex.splitBy.eq_def]
  frame_simp
  frame_arms
  all_goals frame_hof
  all_goals (repeat' first
    | rfl
    | (simp only [frameLem]; done)
    | (simp [frameLem]; done)
    | rw [foldPair_frame K]
    | rw [foldrPair_frame K]
    | rw [foldPairArray_frame K]
    | intro _
    | split)

set_option maxHeartbeats 1000000 in
@[frameLem] theorem splitOn_frame (K : List Kont) (m : Machine) (h : Heap) (str : String)
    (pat : Value) (lim : Int) (bin : Bool) :
    runRegex.splitOn (pushK K m) h str pat lim bin =
      bpush K (runRegex.splitOn m h str pat lim bin) := by
  rw [runRegex.splitOn.eq_def, runRegex.splitOn.eq_def]
  frame_simp
  frame_arms
  all_goals frame_hof
  all_goals (repeat' first
    | rfl
    | (simp only [frameLem]; done)
    | (simp [frameLem]; done)
    | rw [foldPair_frame K]
    | rw [foldrPair_frame K]
    | rw [foldPairArray_frame K]
    | intro _
    | split)

set_option maxHeartbeats 1000000 in
@[frameLem] theorem subst_frame (K : List Kont) (m : Machine) (str src : String) (opts : Nat)
    (rep : String) (global : Bool) (recvV repV : Value) :
    runRegex.subst (pushK K m) str src opts rep global recvV repV =
      bpush K (runRegex.subst m str src opts rep global recvV repV) := by
  rw [runRegex.subst.eq_def, runRegex.subst.eq_def]
  frame_simp
  frame_arms
  all_goals frame_hof
  all_goals (repeat' first
    | rfl
    | (simp only [frameLem]; done)
    | (simp [frameLem]; done)
    | rw [foldPair_frame K]
    | rw [foldrPair_frame K]
    | rw [foldPairArray_frame K]
    | intro _
    | split)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 400000 in
@[frameLem] theorem runRegex_frame (K : List Kont) (bid : String) (recv : Value)
    (args : List Value) (m : Machine) :
    runRegex bid recv args (pushK K m) = bpush K (runRegex bid recv args m) := by
  rw [runRegex.eq_def, runRegex.eq_def]
  frame_simp
  frame_arms
  all_goals frame_hof
  all_goals (repeat' first
    | rfl
    | (simp only [frameLem]; done)
    | (simp [frameLem]; done)
    | rw [foldPair_frame K]
    | rw [foldrPair_frame K]
    | rw [foldPairArray_frame K]
    | intro _
    | split)
  all_goals frame_hof

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 400000 in
@[frameLem] theorem runModules_frame (K : List Kont) (bid : String) (recv : Value)
    (args : List Value) (m : Machine) :
    runModules bid recv args (pushK K m) = bpush K (runModules bid recv args m) := by
  rw [runModules.eq_def, runModules.eq_def]
  frame_simp
  frame_arms
  all_goals frame_hof

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 400000 in
@[frameLem] theorem runCollections_frame (K : List Kont) (bid : String) (recv : Value)
    (args : List Value) (m : Machine) :
    runCollections bid recv args (pushK K m) = bpush K (runCollections bid recv args m) := by
  rw [runCollections.eq_def, runCollections.eq_def]
  frame_simp
  frame_arms
  all_goals frame_hof

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 400000 in
@[frameLem] theorem runStrings_frame (K : List Kont) (bid : String) (recv : Value)
    (args : List Value) (m : Machine) :
    runStrings bid recv args (pushK K m) = bpush K (runStrings bid recv args m) := by
  rw [runStrings.eq_def, runStrings.eq_def]
  frame_simp
  frame_arms
  all_goals frame_hof

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 400000 in
@[frameLem] theorem runNumerics_frame (K : List Kont) (bid : String) (recv : Value) (args : List Value)
    (m : Machine) :
    runNumerics bid recv args (pushK K m) = bpush K (runNumerics bid recv args m) := by
  rw [runNumerics.eq_def, runNumerics.eq_def]
  simp only [frameLem]
  (repeat' first | rfl | split) <;> (try frame_simp) <;> frame_hof

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 400000 in
@[frameLem] theorem runObjects_frame (K : List Kont) (bid : String) (recv : Value)
    (args : List Value) (m : Machine) :
    runObjects bid recv args (pushK K m) = bpush K (runObjects bid recv args m) := by
  rw [runObjects.eq_def, runObjects.eq_def]
  -- `frame_simp` first, because the body opens with a `have h := m.heap` and `rw` cannot
  -- reach under a binder; `simp`'s zeta reduction removes it.
  frame_simp
  -- **`rw [printFold_frame]` before `split`, and inside the loop.** `Kernel#print`'s fold has
  -- to be framed while it is still one term: once `split` has case-analysed it, the two sides'
  -- outcomes are separate (contradictory) hypotheses and the lemma that reconciles them is
  -- lambda-headed, hence invisible to `simp` — eight `False` goals. It cannot be done before
  -- the loop either, because the fold sits inside a matcher arm and `rw` does not reach under
  -- a binder. So it goes *in* the loop, tried ahead of `split`: it fails at the top and fires
  -- the moment the `bid` match has been peeled.
  (repeat' first | rfl | exact printArm_frame K m args | split) <;> (try frame_simp) <;>
    (first | rfl | (try simp_all (maxSteps := 400000) [frameLem]) | skip) <;> (try rfl)
  -- one arm (`Array#to_a` on a non-Array) that `simp_all` left as a conjunction after
  -- destructuring the pair
  -- `Kernel#p`'s multi-argument arm: `simp_all` destructured the allocated pair and left the
  -- machine equality as a hypothesis rather than substituting it
  all_goals (try (rename_i hpush _ _ _; subst hpush; exact ⟨rfl, rfl⟩))
  all_goals frame_hof
  all_goals (try exact runNumerics_frame K bid recv args m)
  all_goals (repeat' first
    | rfl
    | (simp only [frameLem]; done)
    | (simp [frameLem]; done)
    | rw [foldPair_frame K]
    | rw [foldrPair_frame K]
    | rw [foldPairArray_frame K]
    | intro _
    | split)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 400000 in
@[frameLem] theorem run_frame (K : List Kont) (bid : String) (recv : Value)
    (args : List Value) (m : Machine) :
    Builtins.run bid recv args (pushK K m) = bpush K (Builtins.run bid recv args m) := by
  rw [Builtins.run.eq_def, Builtins.run.eq_def]
  frame_simp
  frame_arms
  all_goals frame_hof
  all_goals (try exact runObjects_frame K bid recv args m)

/-! ## The `Interp` layer, part one: `Interp/Support.lean`

Above `Builtins` sits the machine's own bookkeeping, and here the machine's `kont` *is* read —
but only ever pushed onto. `withKont` is the whole of it, and it frames because
`(k :: m.kont) ++ K` and `k :: (m.kont ++ K)` are the same list, definitionally: that one
`rfl` is what makes this layer as cheap as the one below.

The frame-stack readers (`methodFrameOf`, `returnTarget`, `blockOwner`, `matchFrameId`) read
`stack` and `frames`, which `pushK` does not move. `setLocal` and `setGlobal` write them, and
`setGlobal` at `$~` routes through the frame array — so those three go through the same
argument as `Builtins`' `$~` write. -/

open Interp

@[simp, frameLem] theorem withCtl_frame (K : List Kont) (m : Machine) (c : Ctl) :
    withCtl (pushK K m) c = pushK K (withCtl m c) := rfl

/-- **The one place `kont` is written in this layer, and it frames by `rfl`.** `withKont`
conses onto `m.kont`, and consing before appending is appending after consing. -/
@[simp, frameLem] theorem withKont_frame (K : List Kont) (m : Machine) (c : Ctl) (k : Kont) :
    withKont (pushK K m) c k = pushK K (withKont m c k) := rfl

@[simp, frameLem] theorem raiseErr_frame (K : List Kont) (m : Machine) (cls : ObjId) (msg : String) :
    raiseErr (pushK K m) cls msg = pushK K (raiseErr m cls msg) := rfl

@[simp, frameLem] theorem setLocal_frame (K : List Kont) (m : Machine) (x : String) (v : Value) :
    (pushK K m).setLocal x v = pushK K (m.setLocal x v) := by
  simp only [Machine.setLocal, pushK_stack, pushK_frames]
  have hgo : ∀ (fuel : Nat) (fid : FrameId),
      Machine.setLocal.owner (pushK K m) x (m.stack.headD 0) fid fuel =
        Machine.setLocal.owner m x (m.stack.headD 0) fid fuel := by
    intro fuel
    induction fuel with
    | zero => intro fid; rfl
    | succ n ih =>
      intro fid
      simp only [Machine.setLocal.owner, pushK_frames]
      split
      · rfl
      · split
        · exact ih _
        · rfl
  rw [hgo]

@[simp, frameLem] theorem setGlobal_frame (K : List Kont) (m : Machine) (x : String) (v : Value) :
    (pushK K m).setGlobal x v = pushK K (m.setGlobal x v) := by
  simp only [Machine.setGlobal, pushK_globals, setLastMatchValue_frame]
  split <;> rfl

@[simp, frameLem] theorem bindIvar_frame (K : List Kont) (m : Machine) (x : String) (v : Value) :
    bindIvar (pushK K m) x v = pushK K (bindIvar m x v) := by
  simp only [bindIvar, pushK_currentFrame, pushK_heap]
  split <;> rfl

/-- `spread` and `getGlobal` read the heap and the globals list, both of which `pushK` pins. -/
@[simp, frameLem] theorem spread_frame (K : List Kont) (m : Machine) (v : Value) :
    spread (pushK K m) v = spread m v := rfl

@[simp, frameLem] theorem getGlobal_frame (K : List Kont) (m : Machine) (x : String) :
    (pushK K m).getGlobal x = m.getGlobal x := by
  simp only [Machine.getGlobal, pushK_globals, pushK_currentExc, Machine.lastMatchValue,
    matchFrameId_frame, pushK_frames]

/-- The `MatchData` splat's fold: a **list** accumulator rather than an `Array` push, so it is
`capsFold_frame`'s twin one container over. -/
@[simp, frameLem] theorem capsFoldList_frame (K : List Kont) (subj : String) (bin : Bool) :
    ∀ (l : List (Option (Nat × Nat))) (acc : List Value) (m : Machine),
      l.foldl (fun (x : List Value × Machine) (sp : Option (Nat × Nat)) =>
          match sp with
          | some (a, b) => (x.1 ++ [(allocStrEnc x.2 (charSlice subj a b) bin).1],
                            (allocStrEnc x.2 (charSlice subj a b) bin).2)
          | none => (x.1 ++ [Value.nil], x.2)) (acc, pushK K m) =
        ((l.foldl (fun (x : List Value × Machine) (sp : Option (Nat × Nat)) =>
            match sp with
            | some (a, b) => (x.1 ++ [(allocStrEnc x.2 (charSlice subj a b) bin).1],
                              (allocStrEnc x.2 (charSlice subj a b) bin).2)
            | none => (x.1 ++ [Value.nil], x.2)) (acc, m)).1,
          pushK K (l.foldl (fun (x : List Value × Machine) (sp : Option (Nat × Nat)) =>
            match sp with
            | some (a, b) => (x.1 ++ [(allocStrEnc x.2 (charSlice subj a b) bin).1],
                              (allocStrEnc x.2 (charSlice subj a b) bin).2)
            | none => (x.1 ++ [Value.nil], x.2)) (acc, m)).2)
  | [], _, _ => rfl
  | sp :: rest, acc, m => by
    cases sp with
    | none =>
      simp only [List.foldl_cons]
      exact capsFoldList_frame K subj bin rest (acc ++ [Value.nil]) m
    | some p =>
      simp only [List.foldl_cons, allocStrEnc_frame]
      exact capsFoldList_frame K subj bin rest _
        (allocStrEnc m (charSlice subj p.1 p.2) bin).2

/-- The same fold at `Array.foldl`, which is where `spreadA` actually reaches it (`simp`
normalises `caps.toList.foldl` to this). -/
@[simp, frameLem] theorem capsFoldListArray_frame (K : List Kont) (subj : String) (bin : Bool)
    (xs : Array (Option (Nat × Nat))) (acc : List Value) (m : Machine) :
    Array.foldl (fun (x : List Value × Machine) (sp : Option (Nat × Nat)) =>
        match sp with
        | some (a, b) => (x.1 ++ [(allocStrEnc x.2 (charSlice subj a b) bin).1],
                          (allocStrEnc x.2 (charSlice subj a b) bin).2)
        | none => (x.1 ++ [Value.nil], x.2)) (acc, pushK K m) xs =
      ((Array.foldl (fun (x : List Value × Machine) (sp : Option (Nat × Nat)) =>
          match sp with
          | some (a, b) => (x.1 ++ [(allocStrEnc x.2 (charSlice subj a b) bin).1],
                            (allocStrEnc x.2 (charSlice subj a b) bin).2)
          | none => (x.1 ++ [Value.nil], x.2)) (acc, m) xs).1,
        pushK K (Array.foldl (fun (x : List Value × Machine) (sp : Option (Nat × Nat)) =>
          match sp with
          | some (a, b) => (x.1 ++ [(allocStrEnc x.2 (charSlice subj a b) bin).1],
                            (allocStrEnc x.2 (charSlice subj a b) bin).2)
          | none => (x.1 ++ [Value.nil], x.2)) (acc, m) xs).2) := by
  simp only [← Array.foldl_toList]
  exact capsFoldList_frame K subj bin xs.toList acc m

@[simp, frameLem] theorem methodFrameOf_frame (K : List Kont) (m : Machine) :
    methodFrameOf (pushK K m) = methodFrameOf m := rfl

@[simp, frameLem] theorem returnTarget_frame (K : List Kont) (m : Machine) :
    returnTarget (pushK K m) = returnTarget m := rfl

@[simp, frameLem] theorem blockOwner_frame (K : List Kont) (m : Machine) (p : Value) :
    blockOwner (pushK K m) p = blockOwner m p := rfl

@[simp, frameLem] theorem doReturn_frame (K : List Kont) (m : Machine) (v : Value) :
    doReturn (pushK K m) v = frameR K (doReturn m v) := by
  simp only [doReturn, returnTarget_frame, pushK_stack]
  split <;> rfl

@[simp, frameLem] theorem reifyBlock_frame (K : List Kont) (m : Machine) (ps : List Param)
    (ls : List String) (body : Expr) (lam : Bool) :
    reifyBlock (pushK K m) ps ls body lam =
      ((reifyBlock m ps ls body lam).1, pushK K (reifyBlock m ps ls body lam).2) := rfl

@[simp, frameLem] theorem coerceToProc_frame (K : List Kont) (m : Machine) (v : Value) :
    coerceToProc (pushK K m) v =
      (coerceToProc m v).map (fun p => (p.1, pushK K p.2)) := by
  rw [coerceToProc.eq_def, coerceToProc.eq_def]
  frame_arms

@[simp, frameLem] theorem finishRegion_frame (K : List Kont) (m : Machine) (ens : Option Expr)
    (pending : Pending) :
    finishRegion (pushK K m) ens pending = pushK K (finishRegion m ens pending) := by
  rw [finishRegion.eq_def, finishRegion.eq_def]
  frame_arms

/-- **`enterHandler`, and the one shape `simp` cannot match.** The body writes the exception
into `currentExc` and *then* writes the reference, so the machine reaching `setLocal` is a
nested record update — which Lean collapses into one flat literal whose `currentExc` field is
`some exc` rather than `?m.currentExc`. `simp` cannot unify that against `pushK K ?m` (it
would have to invent the structure field-wise), so the four writing arms get a `show` that
spells the pushed machine out and the framing lemmas fire on it. Recorded because it is the
shape that will recur at every helper that writes twice. -/
@[simp, frameLem] theorem enterHandler_frame (K : List Kont) (m : Machine) (node : BeginNode)
    (exc : Value) (ref : Option (TargetKind × String)) (handler : Expr) :
    enterHandler (pushK K m) node exc ref handler =
      pushK K (enterHandler m node exc ref handler) := by
  rw [enterHandler.eq_def, enterHandler.eq_def]
  cases ref with
  | none => rfl
  | some p =>
    obtain ⟨tk, x⟩ := p
    cases tk with
    | lvar =>
      show withKont ((pushK K { m with currentExc := some exc }).setLocal x exc)
          (.eval handler) (.rescueK node m.currentExc) = _
      rw [setLocal_frame]; rfl
    | gvar =>
      show withKont ((pushK K { m with currentExc := some exc }).setGlobal x exc)
          (.eval handler) (.rescueK node m.currentExc) = _
      rw [setGlobal_frame]; rfl
    | ivar =>
      show withKont (bindIvar (pushK K { m with currentExc := some exc }) x exc)
          (.eval handler) (.rescueK node m.currentExc) = _
      rw [bindIvar_frame]; rfl
    | const => rfl
    | cvar => rfl

@[simp, frameLem] theorem appendKwHash_frame (K : List Kont) (m : Machine) (args : List Value)
    (kw : List (Value × Value)) :
    appendKwHash (pushK K m) args kw =
      ((appendKwHash m args kw).1, pushK K (appendKwHash m args kw).2) := by
  simp only [appendKwHash, pushK_heap]
  split <;> rfl

@[simp, frameLem] theorem spreadA_frame (K : List Kont) (m : Machine) (v : Value) :
    spreadA (pushK K m) v = (spreadA m v).map (fun p => (p.1, pushK K p.2)) := by
  cases v with
  | ref o =>
    cases hp : (m.heap.get o).payload with
    | mdata subject caps names =>
      -- the `MatchData` splat's fold, through the general lemma and `exact` rather than a
      -- rewrite: the step is a `match`, so its matcher constant is this declaration's own and
      -- only `isDefEq` sees through it
      simp only [spreadA, hp]
      exact congrArg Except.ok
        (foldPair_frame K _ (by intro p m₂ a; cases a <;> rfl) caps.toList [] m)
    | _ =>
      simp only [spreadA, pushK_heap, hp, spread_frame]
      cases spread m (.ref o) <;> rfl
  | _ => simp only [spreadA, spread_frame] <;> (cases spread m _ <;> rfl)

@[simp, frameLem] theorem matchGlobal_frame (K : List Kont) (m : Machine) (x : String) :
    matchGlobal (pushK K m) x = (matchGlobal m x).map (fun p => (p.1, pushK K p.2)) := by
  rw [matchGlobal.eq_def, matchGlobal.eq_def]
  frame_arms
  -- the `$\`` / `$'` / numbered-group arms: `Option.map` has to be pushed through the `if`s
  -- and the index match before the two sides are syntactically one
  all_goals (simp only [apply_ite (Option.map (fun p : Value × Machine => (p.1, pushK K p.2)))]
             <;> frame_arms)

/-- **`callClosure`: the first helper that pushes a *frame*.** `pushK` pins `frames` and
`stack`, so the pushed frame and the new stack are the same on both sides and the `blkFrameK`
marker frames by `withKont`'s `rfl`. -/
@[simp, frameLem] theorem callClosure_frame (K : List Kont) (m : Machine) (cl : Closure)
    (args : List Value) (brk : Option FrameId) (selfOv : Option Value)
    (defmodOv : Option ObjId) :
    callClosure (pushK K m) cl args brk selfOv defmodOv =
      frameR K (callClosure m cl args brk selfOv defmodOv) := by
  rw [callClosure.eq_def, callClosure.eq_def]
  frame_simp
  frame_arms

/-! ## The `Interp` layer, part two: `destructureBind` is no longer *impossible*

`Interp/Support.lean`'s `destructureBind` was a **`partial def`** until clink 53, which meant
it compiled to an opaque constant with no equation lemmas — so *nothing* about it was provable
and the framing metatheorem was blocked in principle rather than in practice
(`ratchet/Denote/Sem/notes.md` §The fifth stall point, item 3). It now has a fuel-bounded
recursion (`destrDepth`, the nesting depth of `.destr` sub-params, passed by both call sites),
which is the fix `ancestors` already took for the same reason.

Its framing lemma is *not* here yet, and the honest status is that it is now ordinary work
rather than a wall. What it needs, measured: `rw [destructureBind, destructureBind]`, then
`simp only []` for **zeta only** — the body is a chain of `let`s and `rw` cannot reach under a
binder, while `frame_simp` goes too far and rewrites `pushK K m` into a record literal, after
which `foldPair_frame`'s `(acc, pushK ?m)` no longer unifies (`enterHandler_frame`'s shape
problem again) — then the conditional `rw [foldPair_frame K (hf := …)]` at each of its three
folds, with the `.destr` arm of each step discharged by the fuel induction hypothesis. The
first fold goes through; three arms of the outer `vals` match remain.
-/

/-- The step-framing side goal the conditional `rw [foldPair_frame]` leaves: the fold's step
is `destructureBind`'s `bindPos`, whose only machine-moving arm is `.destr` — and that is the
fuel induction hypothesis. -/
syntax "destr_step" ident ident : tactic
macro_rules
  | `(tactic| destr_step $K $fuel) =>
    `(tactic|
        (intro p m₂ a
         rcases a with ⟨prm, val⟩
         cases prm with
         | destr subs' => simp only [destructureBind_frame $K $fuel]
         | _ => rfl))

/-- The three arms of `destructureBind`'s outer `match v` all have the same body: bind the
leading positionals (a fold), allocate the `*rest` array, bind the trailing positionals
(another fold). Two conditional rewrites and their two side goals, deterministically — a
`repeat'` loop over the same alternatives *spins*, because `rw [foldPair_frame]` keeps finding
new occurrences in the side goals it just created. -/
syntax "destr_arms" ident ident : tactic
macro_rules
  | `(tactic| destr_arms $K $fuel) =>
    `(tactic|
        (rw [foldPair_frame $K, foldPair_frame $K]
         case _ => frame_simp
         case _ => destr_step $K $fuel
         case _ => destr_step $K $fuel))

/-! ## `Interp/Dispatch.lean`

Method entry, the eigenclass, class bodies, the native iterators and the mixin/reflection
probes. Three of them *push a frame* (`enterUserMethod`, `enterClassBody`,
`enterScopedClassBody`) and one pushes both a frame and a kont (`startIter`); `pushK` pins
`frames` and `stack`, so all four frame by `withKont`'s `rfl` once their callees do. -/

@[frameLem] theorem eigenclassOf_go_frame (K : List Kont) :
    ∀ (fuel : Nat) (m : Machine) (o : ObjId),
      eigenclassOf.go (pushK K m) o fuel =
        ((eigenclassOf.go m o fuel).1, pushK K (eigenclassOf.go m o fuel).2)
  | 0, _, _ => rfl
  | fuel + 1, m, o => by
    rw [eigenclassOf.go, eigenclassOf.go]
    frame_simp
    (repeat' first
      | rfl
      | (simp only [frameLem, eigenclassOf_go_frame K fuel]; done)
      | rw [eigenclassOf_go_frame K fuel]
      | split) <;> frame_simp

@[simp, frameLem] theorem eigenclassOf_frame (K : List Kont) (m : Machine) (o : ObjId) :
    eigenclassOf (pushK K m) o = ((eigenclassOf m o).1, pushK K (eigenclassOf m o).2) := by
  exact eigenclassOf_go_frame K _ m o

@[simp, frameLem] theorem symOrStr_frame (K : List Kont) (m : Machine) (v : Value) :
    symOrStr (pushK K m) v = symOrStr m v := rfl

@[simp, frameLem] theorem mixinShadow_frame (K : List Kont) (m : Machine) (recv : Value)
    (mname : String) : mixinShadow (pushK K m) recv mname = mixinShadow m recv mname := rfl

@[simp, frameLem] theorem moduleHook_frame (K : List Kont) (m : Machine) (mo : ObjId)
    (name : String) : moduleHook (pushK K m) mo name = moduleHook m mo name := rfl

@[simp, frameLem] theorem missNoMethod_frame (K : List Kont) (m : Machine) (recv : Value)
    (site : SendSite) (mname : String) (args : List Value) :
    missNoMethod (pushK K m) recv site mname args =
      frameR K (missNoMethod m recv site mname args) := by
  simp only [missNoMethod, frameLem]
  split <;> rfl

@[simp, frameLem] theorem visError?_frame (K : List Kont) (m : Machine) (recv : Value)
    (site : SendSite) (md : MethodDef) (mname : String) :
    visError? (pushK K m) recv site md mname =
      (visError? m recv site md mname).map (frameR K) := by
  rw [visError?.eq_def, visError?.eq_def]
  frame_simp
  frame_arms

@[simp, frameLem] theorem cpathContainer_frame (K : List Kont) (m : Machine) (base : Value) :
    cpathContainer (pushK K m) base =
      (cpathContainer m base).mapError (frameR K) := by
  rw [cpathContainer.eq_def, cpathContainer.eq_def]
  frame_simp
  frame_arms

@[simp, frameLem] theorem defineAttr_frame (K : List Kont) (m : Machine) (cls : ObjId)
    (mname : String) (args : List Value) :
    defineAttr (pushK K m) cls mname args =
      (pushK K (defineAttr m cls mname args).1, (defineAttr m cls mname args).2) := by
  rw [defineAttr.eq_def, defineAttr.eq_def]
  frame_simp
  -- one fold, machine in the *first* component this time
  rw [foldPairFst_frame K]
  all_goals (try frame_simp)
  all_goals (try (intro m₂ p a
                  cases a <;> ((repeat' first | rfl | split) <;> frame_simp)))

/-! ### `enterUserMethod` is the one that needs its own file

It is the largest function in the layer — `classifyFull`, two locals lists built by folds,
`destructureBind`, the frame push and the kont push — and at 4M heartbeats the `else` branch
still times out in one piece. Its proof goes in `RubyCore/Proof/KontFrameDispatch.lean`, so
that iterating on it does not recompile this file. -/

/-! ## What is proved, what is left, and the cost measured

The ratchet's fifth stall point named this layer as the part nobody could size — *"whether
`invoke`'s descent into `Builtins/` is `rfl`-transparent in `kont` at kernel speed is untested,
and that is where the 24k lines actually are"*. It is:

* **Transparent by construction.** `grep -rn '\.kont\|kont :='` over the whole
  `RubyCore/Builtins/` directory finds **zero** occurrences. Above it, `Interp/Support.lean`
  reads `kont` in exactly one place — `withKont`, which conses — and that frames by `rfl`,
  because `(k :: m.kont) ++ K` and `k :: (m.kont ++ K)` are the same list.
* **Proved here**: the `Builtins` leaves; the fuel walks (`putsGo`, `flattenAll`); the five
  `…Impl` helpers; the `$~` layer (`matchFrameId`/`setLastMatchValue`/`setMatchGlobals`/
  `setLastMatch`, the one write in the layer that is not to the heap); the four
  continuation-taking helpers (`binArg`, `numBin`, `numCmp`, `withIndex`) with the
  continuation's framing as a hypothesis; `runRegex`'s six `where` helpers; **five of the six
  dispatchers** (`runRegex`, `runModules`, `runCollections`, `runStrings`, `runNumerics`); and
  all of `Interp/Support.lean`'s machine-takers, `callClosure` — the first helper that pushes a
  *frame* — included.
* **`Interp/Dispatch.lean`, most of it**: `eigenclassOf`, `symOrStr`, `mixinShadow`,
  `moduleHook`, `missNoMethod`, `visError?`, `cpathContainer`, `defineAttr`, and — the item
  that was blocked *in principle* until clink 53 — **`destructureBind`**, whose `partial def`
  is gone and whose framing is now proved. `enterUserMethod` needs its own file (above).
* **Nothing is left of `Builtins`.** All six dispatchers and `Builtins.run` itself are proved, so the
  whole 24k-line layer is framed top to bottom. The last two arms to fall were `Kernel#print`
  and `Kernel#p`, and both taught the same lesson twice over: a `match` written in one
  declaration compiles to a matcher constant belonging to *that* declaration, so a lemma
  spelling the same syntax is a different term and `rw` cannot find it — `printArm_frame`
  states the whole arm and is discharged by `exact`, where `isDefEq` unfolds matchers.

**The four tooling facts that dominated the cost**, none of them in a manual:

1. **`rw [f.eq_def]`, never `simp only [f]`** — the equation compiler refuses per-arm equations
   at this scale ("failed to generate equational theorem for `runModules`").
2. **`split` does not scale to deeply nested arms.** On `newImpl` (five nested `if`s) `split`'s
   own `simp` reports "maximum number of steps exceeded", and neither `maxSteps` nor
   `simp.maxSteps` is a settable option. Hand case-splitting is ~15 lines per such function.
3. **`simp_all` must be a per-goal last resort, not a stage.** Run eagerly it *re-folds* goals
   that `rfl` would have closed; demoting it is what closed `callClosure` and four dispatchers
   that had looked blocked.
4. **A lemma keyed on a lambda is invisible to `simp` and visible to `rw`.** The
   discrimination tree does not index under a lambda, so a fold-framing lemma has to be applied
   by `rw` (as a *conditional* rewrite — `rw` unifies the step from the goal and leaves the
   framing hypothesis as a side goal, which is what gets past writing a step and its matcher
   constant out by hand) or by `exact`, where `isDefEq` unfolds matchers. This is the single
   biggest multiplier, and it is why the residual is per-arm rather than per-file.

**And a Lean fact worth writing down**: a `macro_rules` tactic that mentions itself does not
expand. The first `frame_hof` was written recursively and silently failed on every nested case;
as a `repeat'` fixpoint it handles the nesting for free.

What this does *not* buy is a rung. `KontFrameCatchFree` (`ratchet/Denote/Sem/Frame.lean`)
needs the rest of `Interp` too: `applyKont` and `unwind`, whose statements are **conditional**
(`kont = []` is the pass-through point); `CatchFree` threaded through the `throw` arm the
refutation found; the `Send`/`Dispatch`/`Reflect` helpers; and one `partial def`
(`destructureBind`) that has to be given a structural recursion before anything about it is
provable at all.
-/

#print axioms putsGo_frame
#print axioms flattenAll_frame
#print axioms newImpl_frame
#print axioms setLastMatch_frame
#print axioms allocFold_frame

end Proof
end RubyCore
