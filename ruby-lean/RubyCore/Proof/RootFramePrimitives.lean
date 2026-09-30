import RubyCore.Proof.RootFrame
import RubyCore.Proof.FrameAttr

/-! Builtin framing for the root-execution action. Hash operations additionally
require that the appended continuation introduce no native iteration lock. -/
set_option autoImplicit false
set_option maxRecDepth 40000
namespace RubyCore.Proof.Root

@[simp, rootFrameLem] theorem pushRootK_heap (K : List Kont) (m : Machine) : (pushRootK K m).heap = m.heap := rfl
@[simp, rootFrameLem] theorem pushRootK_ctl (K : List Kont) (m : Machine) : (pushRootK K m).ctl = m.ctl := rfl
@[simp, rootFrameLem] theorem pushRootK_stack (K : List Kont) (m : Machine) : (pushRootK K m).stack = m.stack := rfl
@[simp, rootFrameLem] theorem pushRootK_frames (K : List Kont) (m : Machine) : (pushRootK K m).frames = m.frames := rfl
@[simp, rootFrameLem] theorem pushRootK_globals (K : List Kont) (m : Machine) :
    (pushRootK K m).globals = m.globals := rfl
@[simp, rootFrameLem] theorem pushRootK_out (K : List Kont) (m : Machine) : (pushRootK K m).out = m.out := rfl
@[simp, rootFrameLem] theorem pushRootK_currentExc (K : List Kont) (m : Machine) :
    (pushRootK K m).currentExc = m.currentExc := rfl
@[simp, rootFrameLem] theorem pushRootK_preludeMode (K : List Kont) (m : Machine) :
    (pushRootK K m).preludeMode = m.preludeMode := rfl
theorem pushRootK_kont (K : List Kont) (m : Machine) :
    (pushRootK K m).kont =
      (if m.activeEnumerator.isNone then m.kont ++ K else m.kont) := rfl

@[simp, rootFrameLem] theorem pushRootK_hashIterationLocks (K : List Kont) (m : Machine) :
    (pushRootK K m).hashIterationLocks = m.hashIterationLocks := rfl

@[simp, rootFrameLem] theorem leaveHashIteration_frame (K : List Kont) (m : Machine) (kind : IterKind) :
    (pushRootK K m).leaveHashIteration kind = pushRootK K (m.leaveHashIteration kind) := by
  cases kind <;> rfl

@[simp, rootFrameLem] theorem pushRootK_activeEnumerator (K : List Kont) (m : Machine) :
    (pushRootK K m).activeEnumerator = m.activeEnumerator := rfl

@[simp, rootFrameLem] theorem pushRootK_liveBreakScopes (K : List Kont) (m : Machine) :
    (pushRootK K m).liveBreakScopes = m.liveBreakScopes := rfl

@[simp, rootFrameLem] theorem pushRootK_objectInspections (K : List Kont) (m : Machine) :
    (pushRootK K m).objectInspections = m.objectInspections := rfl

@[simp, rootFrameLem] theorem leaveObjectInspection_frame (K : List Kont) (m : Machine) (recv : Value) :
    (pushRootK K m).leaveObjectInspection recv = pushRootK K (m.leaveObjectInspection recv) := rfl

@[simp, rootFrameLem] theorem pushRootK_frozenInspections (K : List Kont) (m : Machine) :
    (pushRootK K m).frozenInspections = m.frozenInspections := rfl

@[simp, rootFrameLem] theorem leaveFrozenInspection_frame (K : List Kont) (m : Machine)
    (recv : Value) (phase : FrozenPhase) :
    (pushRootK K m).leaveFrozenInspection recv phase = pushRootK K (m.leaveFrozenInspection recv phase) := by
  cases phase <;> rfl

@[simp, rootFrameLem] theorem pushRootK_numericLiterals (K : List Kont) (m : Machine) :
    (pushRootK K m).numericLiterals = m.numericLiterals := rfl

@[simp, rootFrameLem] theorem pushRootK_missingReason (K : List Kont) (m : Machine) :
    (pushRootK K m).missingReason = m.missingReason := rfl

@[simp, rootFrameLem] theorem pushRootK_featurePrograms (K : List Kont) (m : Machine) :
    (pushRootK K m).featurePrograms = m.featurePrograms := rfl

@[simp, rootFrameLem] theorem pushRootK_loadedFeatures (K : List Kont) (m : Machine) :
    (pushRootK K m).loadedFeatures = m.loadedFeatures := rfl

@[simp, rootFrameLem] theorem pushRootK_loadingFeatures (K : List Kont) (m : Machine) :
    (pushRootK K m).loadingFeatures = m.loadingFeatures := rfl

@[simp, rootFrameLem] theorem pushRootK_attemptedFeatures (K : List Kont) (m : Machine) :
    (pushRootK K m).attemptedFeatures = m.attemptedFeatures := rfl

@[simp, rootFrameLem] theorem pushRootK_currentFrame (K : List Kont) (m : Machine) :
    (pushRootK K m).currentFrame = m.currentFrame := rfl

/-- Every field but `kont` is copied, so a `pushRootK` commutes with any record update that does
not touch `kont`. The three that occur in this layer, as `rfl` lemmas. -/
@[simp, rootFrameLem] theorem pushRootK_setHeap (K : List Kont) (m : Machine) (h : Heap) :
    pushRootK K { m with heap := h } = { pushRootK K m with heap := h } := rfl

@[simp, rootFrameLem] theorem pushRootK_setOut (K : List Kont) (m : Machine) (s : String) :
    pushRootK K { m with out := s } = { pushRootK K m with out := s } := rfl

/-! ## `BRes`, with the tail carried through -/

/-- A builtin result, with the appended tail carried into whichever machine it holds. -/
def bRootPush (K : List Kont) : BRes → BRes
  | .ok v m => .ok v (pushRootK K m)
  | .err c s m => .err c s (pushRootK K m)
  | .throwV v m => .throwV v (pushRootK K m)
  | .frozen v m => .frozen v (pushRootK K m)
  | .unsupported r => .unsupported r

@[simp, rootFrameLem] theorem bRootPush_ok (K : List Kont) (v : Value) (m : Machine) :
    bRootPush K (.ok v m) = .ok v (pushRootK K m) := rfl
@[simp, rootFrameLem] theorem bRootPush_err (K : List Kont) (c : ObjId) (s : String) (m : Machine) :
    bRootPush K (.err c s m) = .err c s (pushRootK K m) := rfl
@[simp, rootFrameLem] theorem bRootPush_throwV (K : List Kont) (v : Value) (m : Machine) :
    bRootPush K (.throwV v m) = .throwV v (pushRootK K m) := rfl
@[simp, rootFrameLem] theorem bRootPush_frozen (K : List Kont) (v : Value) (m : Machine) :
    bRootPush K (.frozen v m) = .frozen v (pushRootK K m) := rfl
@[simp, rootFrameLem] theorem bRootPush_unsupported (K : List Kont) (r : String) :
    bRootPush K (.unsupported r) = .unsupported r := rfl

@[simp, rootFrameLem] theorem setCurrentFrame_frame (K : List Kont) (m : Machine) (f : Frame) :
    (pushRootK K m).setCurrentFrame f = pushRootK K (m.setCurrentFrame f) := by
  simp only [Machine.setCurrentFrame, pushRootK_stack, pushRootK_frames]
  split <;> rfl

/-- **A builtin's answer does not depend on the continuation.** The statement every function
in the `Builtins` layer gets, spelled once. -/
def BFrame {α : Type} (f : Machine → α) (g : List Kont → α → α) : Prop :=
  ∀ (K : List Kont) (m : Machine), f (pushRootK K m) = g K (f m)

/-! ## The `Builtins` leaves

Every one of these produces its machine by a record update that does not touch `kont`, so each
is `rfl` after both sides unfold. They are stated (rather than left to the dispatcher's own
`simp`) because the dispatchers are large and a named rewrite is what keeps their proofs from
re-deriving the same fact sixty times. -/

open Builtins

@[simp, rootFrameLem] theorem allocStrEnc_frame (K : List Kont) (m : Machine) (s : String) (b : Bool) :
    allocStrEnc (pushRootK K m) s b = ((allocStrEnc m s b).1, pushRootK K (allocStrEnc m s b).2) := rfl

@[simp, rootFrameLem] theorem allocStr_frame (K : List Kont) (m : Machine) (s : String) :
    allocStr (pushRootK K m) s = ((allocStr m s).1, pushRootK K (allocStr m s).2) := rfl

@[simp, rootFrameLem] theorem allocArr_frame (K : List Kont) (m : Machine) (xs : Array Value) :
    allocArr (pushRootK K m) xs = ((allocArr m xs).1, pushRootK K (allocArr m xs).2) := rfl

@[simp, rootFrameLem] theorem allocHsh_frame (K : List Kont) (m : Machine) (xs : Array (Value × Value)) :
    allocHsh (pushRootK K m) xs = ((allocHsh m xs).1, pushRootK K (allocHsh m xs).2) := rfl

@[simp, rootFrameLem] theorem allocExc_frame (K : List Kont) (m : Machine) (c : ObjId) (s : String) :
    allocExc (pushRootK K m) c s = ((allocExc m c s).1, pushRootK K (allocExc m c s).2) := rfl

@[simp, rootFrameLem] theorem dupObj_frame (K : List Kont) (m : Machine) (o : ObjId) (kf : Bool) :
    dupObj (pushRootK K m) o kf = ((dupObj m o kf).1, pushRootK K (dupObj m o kf).2) := rfl

@[simp, rootFrameLem] theorem okStr_frame (K : List Kont) (m : Machine) (s : String) :
    okStr (pushRootK K m) s = bRootPush K (okStr m s) := rfl

@[simp, rootFrameLem] theorem okStrEnc_frame (K : List Kont) (m : Machine) (b : Bool) (s : String) :
    okStrEnc (pushRootK K m) b s = bRootPush K (okStrEnc m b s) := rfl

@[simp, rootFrameLem] theorem okStrFrom_frame (K : List Kont) (m : Machine) (src : Value) (s : String) :
    okStrFrom (pushRootK K m) src s = bRootPush K (okStrFrom m src s) := rfl

@[simp, rootFrameLem] theorem inspectP_frame (K : List Kont) (m : Machine) (v : Value) :
    inspectP (pushRootK K m) v = inspectP m v := rfl

@[simp, rootFrameLem] theorem toSP_frame (K : List Kont) (m : Machine) (v : Value) :
    toSP (pushRootK K m) v = toSP m v := rfl

@[simp, rootFrameLem] theorem coerceFailed_frame (K : List Kont) (c : String) (m : Machine) (b : Value) :
    coerceFailed c (pushRootK K m) b = bRootPush K (coerceFailed c m b) := rfl

@[simp, rootFrameLem] theorem frozenErr_frame (K : List Kont) (m : Machine) (recv : Value) (c : String) :
    frozenErr (pushRootK K m) recv c = bRootPush K (frozenErr m recv c) := rfl

/-- **The exception-message reader**, which is the one leaf that is *not* `rfl`: it walks the
heap. `pushRootK` does not move the heap, so it is a projection. -/
@[simp, rootFrameLem] theorem emit_frame (K : List Kont) (m : Machine) (s : String) :
    Machine.emit (pushRootK K m) s = pushRootK K (Machine.emit m s) := rfl

/-! ## The two tactics every proof below is written with

`root_simp` fires the framing lemmas; `root_arms` walks a `match`'s arms and closes each.
Both are macros rather than `simp` calls spelled out per proof because the dispatchers are
large and the recipe has to be identical at every one of them — a proof that needed its own
tactic would be a proof that found something, which is worth seeing.

`eq_def` rather than the per-arm equations at every dispatcher, because the equation compiler
declines to generate them for matches this large ("failed to generate equational theorem") and
the raw unfolding is all that is needed. -/

/-- Fire every framing lemma in this file. They are all `@[simp]`, so this is the default set
restricted to `only` by nothing — `simp` with the standard lemmas is what reduces the
`pushRootK`-of-a-record-update shapes back to `pushRootK`-of-a-machine. -/
syntax "root_simp" : tactic
macro_rules
  | `(tactic| root_simp) => `(tactic| try simp only [rootFrameLem])

/-- The arm walker. `split` peels one `match`/`if` at a time; each arm is then either `rfl`
after the framing set has fired, or — for the arms a `split` leaves *contradictory* hypotheses
on — `simp_all`. That last stage is deliberately a **per-goal last resort** rather than a
stage in the `<;>` chain: run eagerly, `simp_all` re-folds goals that `rfl` would have closed,
which cost `callClosure` and three `Builtins` dispatchers before it was demoted. -/
syntax "root_arms" : tactic
macro_rules
  | `(tactic| root_arms) =>
    `(tactic| (repeat' first | rfl | split) <;>
        (try root_simp) <;>
        (first | rfl | (try simp_all (maxSteps := 400000) [rootFrameLem]) <;> (try rfl) | skip))

/-! ## The `Builtins` mid-level: the fuel walks and the four higher-order helpers

Two shapes here that the leaves did not have. **A fuel-recursive walk** (`putsGo`,
`flattenAll`) needs an induction on the fuel, and `putsGo` is the one that writes (`emit`), so
its statement carries the machine out. **A continuation-taking helper** (`withIndex`,
`numBin`, `numCmp`, `binArg`) frames only if its continuation does, so the hypothesis is
pointwise — which is exactly what holds at the call sites, where the continuation is a lambda
closing over the same machine. -/

@[rootFrameLem] theorem putsGo_frame (K : List Kont) : ∀ (fuel : Nat) (m : Machine) (args : List Value),
    putsGo (pushRootK K m) args fuel = (putsGo m args fuel).map (pushRootK K)
  | 0, _, _ => rfl
  | fuel + 1, m, args => by
    rw [putsGo, putsGo]
    induction args generalizing m with
    | nil => rfl
    | cons a rest ih =>
      simp only [List.foldlM_cons, pushRootK_heap, toSP_frame, emit_frame,
        putsGo_frame K fuel m]
      (repeat' split) <;>
        first
          | rfl
          | (simp only [Option.some_bind, Option.none_bind, Option.map_eq_map,
                Option.map_none, Option.bind_map]; try rfl)
          | simp_all
      all_goals (try exact ih _)
      all_goals (try (cases hg : putsGo m _ fuel <;> simp_all))

@[simp, rootFrameLem] theorem flattenAll_frame (K : List Kont) : ∀ (fuel : Nat) (m : Machine) (v : Value),
    flattenAll (pushRootK K m) v fuel = flattenAll m v fuel
  | 0, _, _ => rfl
  | fuel + 1, m, v => by
    have hf : ∀ x, flattenAll (pushRootK K m) x fuel = flattenAll m x fuel :=
      fun x => flattenAll_frame K fuel m x
    rw [flattenAll, flattenAll]
    root_simp
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
@[rootFrameLem] theorem printFold_frame (K : List Kont) :
    ∀ (args : List Value) (m : Machine),
      List.foldlM (fun (m : Machine) (a : Value) =>
          match toSP m a with
          | .ok s => pure (m.emit s)
          | .error _ => none) (pushRootK K m) args =
        (List.foldlM (fun (m : Machine) (a : Value) =>
          match toSP m a with
          | .ok s => pure (m.emit s)
          | .error _ => none) m args).map (pushRootK K)
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
        | .error _ => none) (pushRootK K m) args with
      | some m' => BRes.ok .nil m'
      | none => BRes.unsupported "print: impure to_s") =
      bRootPush K (match List.foldlM (fun (m : Machine) (a : Value) =>
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
@[rootFrameLem] theorem objectsGo_frame (K : List Kont) :
    ∀ (m : Machine) (args : List Value),
      runObjects.go (pushRootK K m) args = (runObjects.go m args).map (pushRootK K)
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
    (hk : ∀ b, k' b = bRootPush K (k b)) :
    binArg (pushRootK K m) args k' = bRootPush K (binArg m args k) := by
  simp only [binArg]
  split
  · exact hk _
  · rfl

theorem numBin_frame (K : List Kont) (cls : String) (m : Machine) (a b : Value)
    (fi fi' : Int → Int → BRes) (ff ff' : Float → Float → BRes)
    (hi : ∀ x y, fi' x y = bRootPush K (fi x y))
    (hf : ∀ x y, ff' x y = bRootPush K (ff x y)) :
    numBin cls (pushRootK K m) a b fi' ff' = bRootPush K (numBin cls m a b fi ff) := by
  simp only [numBin]
  split
  · exact hi _ _
  · exact hf _ _
  · exact hf _ _
  · exact hf _ _
  · exact coerceFailed_frame K cls m b

theorem numCmp_frame (K : List Kont) (cls : String) (m : Machine) (a b : Value)
    (k k' : Ordering → BRes) (hk : ∀ o, k' o = bRootPush K (k o)) :
    numCmp cls (pushRootK K m) a b k' = bRootPush K (numCmp cls m a b k) := by
  simp only [numCmp, pushRootK_heap]
  split
  · exact hk _
  · -- the `Float` comparison chain: three nested `if`s over the same two conditions on both
    -- sides, so each branch is `hk` at its own `Ordering`
    repeat' first | exact hk _ | rfl | split
  · rfl

theorem withIndex_frame (K : List Kont) (m : Machine) (v : Value) (why : String)
    (k k' : Int → BRes) (numMsg : Bool) (hk : ∀ n, k' n = bRootPush K (k n)) :
    withIndex (pushRootK K m) v why k' numMsg = bRootPush K (withIndex m v why k numMsg) := by
  simp only [withIndex, pushRootK_heap]
  split
  · exact hk _
  · rfl
  · rfl

/-- The closer for an arm whose body is one of the four above, **as a fixpoint loop rather
than a recursive macro**: a `macro_rules` that mentions itself does not expand, so the first
version of this silently failed on every nested case (a `binArg` whose continuation is a
`numBin`) and cost an hour. `repeat'` gets the nesting for free, since each `refine` leaves the
continuation's obligation as a goal and the loop is applied to all goals. -/
syntax "root_hof" : tactic
macro_rules
  | `(tactic| root_hof) =>
    `(tactic| repeat' first
        | rfl
        | (root_simp; done)
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

@[rootFrameLem] theorem putsImpl_frame (K : List Kont) (m : Machine) (args : List Value) :
    putsImpl (pushRootK K m) args = bRootPush K (putsImpl m args) := by
  rw [putsImpl, putsImpl, putsGo_frame]
  cases putsGo m args 100 <;> rfl

@[rootFrameLem] theorem raiseClass_frame (K : List Kont) (m : Machine) (cls : ObjId) (msg : Option Value) :
    raiseClass (pushRootK K m) cls msg = bRootPush K (raiseClass m cls msg) := by
  rw [raiseClass.eq_def, raiseClass.eq_def]
  root_simp
  try simp only [allocExc_frame]
  root_arms

@[rootFrameLem] theorem raiseImpl_frame (K : List Kont) (m : Machine) (args : List Value) :
    raiseImpl (pushRootK K m) args = bRootPush K (raiseImpl m args) := by
  rw [raiseImpl.eq_def, raiseImpl.eq_def]
  root_simp
  try simp only [raiseClass_frame]
  root_arms

set_option maxHeartbeats 2000000 in
@[rootFrameLem] theorem newImpl_frame (K : List Kont) (m : Machine) (recv : Value) (args : List Value) :
    newImpl (pushRootK K m) recv args = bRootPush K (newImpl m recv args) := by
  rw [newImpl.eq_def, newImpl.eq_def]
  root_simp
  -- **`split` does not scale to this one**, and it is the only place in the layer where that
  -- shows: the arms are nested five `if`s deep, and `split`'s own `simp` exceeds its step
  -- budget on a goal that size (no option raises it). Case-splitting the conditions by hand
  -- keeps every `simp only` local, which is all the automation was doing anyway.
  cases recv with
  | ref k =>
    cases hc : m.heap.classPayload? k with
    | none => simp only [hc]; root_simp
    | some c =>
      simp only [hc]
      by_cases h1 : c.isModule = true
      · simp only [if_pos h1]; root_simp
      · simp only [if_neg h1]
        by_cases h2 : (ancestors m.heap k).contains Boot.exceptionId = true
        · simp only [if_pos h2]; root_arms
        · simp only [if_neg h2]
          by_cases h3 : (ancestors m.heap k).contains Boot.stringId = true
          · simp only [if_pos h3]; root_arms
          · simp only [if_neg h3]
            by_cases h4 : (ancestors m.heap k).contains Boot.arrayId = true
            · simp only [if_pos h4]; root_arms
            · simp only [if_neg h4]
              by_cases h5 : (ancestors m.heap k).contains Boot.hashId = true
              · simp only [if_pos h5]; root_arms
              · simp only [if_neg h5]
                by_cases h6 : k == Boot.randomId
                · simp only [if_pos h6]; root_arms
                · simp only [if_neg h6]
                  by_cases h7 : k == Boot.regexpId
                  · simp only [if_pos h7]; root_arms
                  · simp only [if_neg h7]; root_arms
  | _ => rfl

@[rootFrameLem] theorem joinImpl_frame (K : List Kont) (m : Machine) (recv : Value) (args : List Value) :
    joinImpl (pushRootK K m) recv args = bRootPush K (joinImpl m recv args) := by
  rw [joinImpl.eq_def, joinImpl.eq_def]
  root_simp
  try simp only [flattenAll_frame]
  root_arms

@[rootFrameLem] theorem sortImpl_frame (K : List Kont) (m : Machine) (recv : Value) :
    sortImpl (pushRootK K m) recv = bRootPush K (sortImpl m recv) := by
  rw [sortImpl.eq_def, sortImpl.eq_def]
  root_simp

  root_arms

/-! ## The `$~` write, and the `Regex` layer

`setMatchGlobals` is the one write in this layer that is **not** to the heap: `$~` is
frame-local (L121), so it goes through `Machine.matchFrameId`, a fuel walk over the frame
stack. `pushRootK` preserves both the stack and the frame array, but the walk carries `m` as a
captured argument, so agreement is an induction rather than a projection — the same shape
`ratchet`'s `getLocal_go_reCtl` has. -/

@[rootFrameLem] theorem matchFrameOwner_frame (K : List Kont) (m : Machine) :
    ∀ (fuel : Nat) (fid : FrameId),
      Machine.matchFrameOwner (pushRootK K m) fid fuel = Machine.matchFrameOwner m fid fuel := by
  intro fuel
  induction fuel with
  | zero => intro fid; rfl
  | succ n ih =>
    intro fid
    simp only [Machine.matchFrameOwner, pushRootK_frames]
    split
    · exact ih _
    · rfl

@[rootFrameLem] theorem matchFrameId_go_frame (K : List Kont) (m : Machine) :
    ∀ (fuel : Nat) (l : List FrameId),
      Machine.matchFrameId.go (pushRootK K m) l fuel = Machine.matchFrameId.go m l fuel := by
  intro fuel
  induction fuel with
  | zero => intro l; cases l <;> rfl
  | succ n ih =>
    intro l
    cases l with
    | nil => rfl
    | cons fid rest =>
      simp only [Machine.matchFrameId.go, pushRootK_frames]
      split
      · split
        · rfl
        · exact ih _
      · split
        · split
          · exact matchFrameOwner_frame K m n _
          · exact ih _
        · rfl

@[simp, rootFrameLem] theorem matchFrameId_frame (K : List Kont) (m : Machine) :
    (pushRootK K m).matchFrameId = m.matchFrameId := by
  simp only [Machine.matchFrameId, pushRootK_stack]
  exact matchFrameId_go_frame K m _ _

@[simp, rootFrameLem] theorem setLastMatchValue_frame (K : List Kont) (m : Machine) (v : Value) :
    (pushRootK K m).setLastMatchValue v = pushRootK K (m.setLastMatchValue v) := by
  simp only [Machine.setLastMatchValue, matchFrameId_frame, pushRootK_frames]
  split <;> rfl

@[simp, rootFrameLem] theorem setMatchGlobals_frame (K : List Kont) (m : Machine) (md : Option Value) :
    setMatchGlobals (pushRootK K m) md = pushRootK K (setMatchGlobals m md) := by
  simp only [setMatchGlobals, setLastMatchValue_frame]

@[simp, rootFrameLem] theorem allocRegexp_frame (K : List Kont) (m : Machine) (src : String) (opts : Nat) :
    allocRegexp (pushRootK K m) src opts =
      ((allocRegexp m src opts).1, pushRootK K (allocRegexp m src opts).2) := rfl

@[simp, rootFrameLem] theorem allocMData_frame (K : List Kont) (m : Machine) (subj : String)
    (caps : Array (Option (Nat × Nat))) (names : List (String × Nat)) (bin : Bool) :
    allocMData (pushRootK K m) subj caps names bin =
      ((allocMData m subj caps names bin).1, pushRootK K (allocMData m subj caps names bin).2) := rfl

@[simp, rootFrameLem] theorem setLastMatch_frame (K : List Kont) (m : Machine) (s src : String) (opts : Nat)
    (hits : List (Nat × Nat × Array (Option (Nat × Nat)))) (bin : Bool) :
    setLastMatch (pushRootK K m) s src opts hits bin =
      pushRootK K (setLastMatch m s src opts hits bin) := by
  simp only [setLastMatch]
  split
  · simp only [setMatchGlobals_frame]
  · simp only [allocMData_frame, setMatchGlobals_frame]

/-- **The one allocating `foldl` in the layer** (`String#chars`, which allocates a String per
character). The machine threads through the accumulator, so this is a list induction rather
than a rewrite — the same shape `putsGo` needed, one level down. -/
@[simp, rootFrameLem] theorem charsFold_frame (K : List Kont) (bin : Bool) :
    ∀ (l : List Char) (acc : Array Value) (m : Machine),
      l.foldl (fun (x : Array Value × Machine) c =>
          ((x.1.push (allocStrEnc x.2 (String.singleton c) bin).1),
            (allocStrEnc x.2 (String.singleton c) bin).2)) (acc, pushRootK K m) =
        ((l.foldl (fun (x : Array Value × Machine) c =>
            ((x.1.push (allocStrEnc x.2 (String.singleton c) bin).1),
              (allocStrEnc x.2 (String.singleton c) bin).2)) (acc, m)).1,
          pushRootK K (l.foldl (fun (x : Array Value × Machine) c =>
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

@[rootFrameLem] theorem allocFold_frame {α : Type} (K : List Kont) (f : Machine → α → Value × Machine)
    (hf : ∀ (m : Machine) (a : α), f (pushRootK K m) a = ((f m a).1, pushRootK K (f m a).2)) :
    ∀ (l : List α) (acc : Array Value) (m : Machine),
      List.foldl (fun (x : Array Value × Machine) (a : α) =>
          (x.1.push (f x.2 a).1, (f x.2 a).2)) (acc, pushRootK K m) l =
        ((List.foldl (fun (x : Array Value × Machine) (a : α) =>
            (x.1.push (f x.2 a).1, (f x.2 a).2)) (acc, m) l).1,
          pushRootK K (List.foldl (fun (x : Array Value × Machine) (a : α) =>
            (x.1.push (f x.2 a).1, (f x.2 a).2)) (acc, m) l).2)
  | [], _, _ => rfl
  | a :: rest, acc, m => by
    simp only [List.foldl_cons, hf m a]
    exact allocFold_frame K f hf rest _ (f m a).2

@[rootFrameLem] theorem allocFoldArray_frame {α : Type} (K : List Kont) (f : Machine → α → Value × Machine)
    (hf : ∀ (m : Machine) (a : α), f (pushRootK K m) a = ((f m a).1, pushRootK K (f m a).2))
    (xs : Array α) (acc : Array Value) (m : Machine) :
    Array.foldl (fun (x : Array Value × Machine) (a : α) =>
        (x.1.push (f x.2 a).1, (f x.2 a).2)) (acc, pushRootK K m) xs =
      ((Array.foldl (fun (x : Array Value × Machine) (a : α) =>
          (x.1.push (f x.2 a).1, (f x.2 a).2)) (acc, m) xs).1,
        pushRootK K (Array.foldl (fun (x : Array Value × Machine) (a : α) =>
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
@[rootFrameLem] theorem foldPair_frame {α β : Type} (K : List Kont) (f : β × Machine → α → β × Machine)
    (hf : ∀ (p : β) (m : Machine) (a : α),
      f (p, pushRootK K m) a = ((f (p, m) a).1, pushRootK K (f (p, m) a).2)) :
    ∀ (l : List α) (acc : β) (m : Machine),
      l.foldl f (acc, pushRootK K m) =
        ((l.foldl f (acc, m)).1, pushRootK K (l.foldl f (acc, m)).2)
  | [], _, _ => rfl
  | a :: rest, acc, m => by
    simp only [List.foldl_cons, hf acc m a]
    exact foldPair_frame K f hf rest _ (f (acc, m) a).2

/-- The machine-**first** twin: `defineAttr` accumulates `(machine, names)` rather than
`(names, machine)`. -/
theorem foldPairFst_frame {α β : Type} (K : List Kont) (f : Machine × β → α → Machine × β)
    (hf : ∀ (m : Machine) (p : β) (a : α),
      f (pushRootK K m, p) a = (pushRootK K (f (m, p) a).1, (f (m, p) a).2)) :
    ∀ (l : List α) (m : Machine) (acc : β),
      List.foldl f (pushRootK K m, acc) l =
        (pushRootK K (List.foldl f (m, acc) l).1, (List.foldl f (m, acc) l).2)
  | [], _, _ => rfl
  | a :: rest, m, acc => by
    simp only [List.foldl_cons, hf m acc a]
    exact foldPairFst_frame K f hf rest (f (m, acc) a).1 (f (m, acc) a).2

/-- The `foldr` twin. `String#split` builds its result right-to-left, so it needs one. -/
theorem foldrPair_frame {α β : Type} (K : List Kont) (f : α → β × Machine → β × Machine)
    (hf : ∀ (a : α) (p : β) (m : Machine),
      f a (p, pushRootK K m) = ((f a (p, m)).1, pushRootK K (f a (p, m)).2)) :
    ∀ (l : List α) (acc : β) (m : Machine),
      List.foldr f (acc, pushRootK K m) l =
        ((List.foldr f (acc, m) l).1, pushRootK K (List.foldr f (acc, m) l).2)
  | [], _, _ => rfl
  | a :: rest, acc, m => by
    simp only [List.foldr_cons, foldrPair_frame K f hf rest acc m]
    exact hf a _ _

/-- And the `Array.foldl` twin, by `Array.foldl_toList`. -/
theorem foldPairArray_frame {α β : Type} (K : List Kont) (f : β × Machine → α → β × Machine)
    (hf : ∀ (p : β) (m : Machine) (a : α),
      f (p, pushRootK K m) a = ((f (p, m) a).1, pushRootK K (f (p, m) a).2))
    (xs : Array α) (acc : β) (m : Machine) :
    Array.foldl f (acc, pushRootK K m) xs =
      ((Array.foldl f (acc, m) xs).1, pushRootK K (Array.foldl f (acc, m) xs).2) := by
  simp only [← Array.foldl_toList]
  exact foldPair_frame K f hf xs.toList acc m

/-! ### The three concrete fold shapes `Builtins` actually uses

The polymorphic lemma above is the argument; these are the instances, because `simp` matches
*syntactically* and the step functions in the interpreter are written out rather than
abstracted. Each is one application of `allocFold_frame` — the naming follows what the fold
builds. -/

@[simp, rootFrameLem] theorem namesFold_frame (K : List Kont) (l : List (String × Nat)) (acc : Array Value)
    (m : Machine) :
    List.foldl (fun (x : Array Value × Machine) (p : String × Nat) =>
        (x.1.push (allocStr x.2 p.1).1, (allocStr x.2 p.1).2)) (acc, pushRootK K m) l =
      ((List.foldl (fun (x : Array Value × Machine) (p : String × Nat) =>
          (x.1.push (allocStr x.2 p.1).1, (allocStr x.2 p.1).2)) (acc, m) l).1,
        pushRootK K (List.foldl (fun (x : Array Value × Machine) (p : String × Nat) =>
          (x.1.push (allocStr x.2 p.1).1, (allocStr x.2 p.1).2)) (acc, m) l).2) :=
  allocFold_frame K (fun m p => allocStr m p.1) (fun _ _ => rfl) l acc m

@[simp, rootFrameLem] theorem capsFold_frame (K : List Kont) (str : String) (bin : Bool)
    (l : List (Option (Nat × Nat))) (acc : Array Value) (m : Machine) :
    List.foldl (fun (x : Array Value × Machine) (sp : Option (Nat × Nat)) =>
        match sp with
        | some (a, b) => (x.1.push (allocStrEnc x.2 (charSlice str a b) bin).1,
                          (allocStrEnc x.2 (charSlice str a b) bin).2)
        | none => (x.1.push Value.nil, x.2)) (acc, pushRootK K m) l =
      ((List.foldl (fun (x : Array Value × Machine) (sp : Option (Nat × Nat)) =>
          match sp with
          | some (a, b) => (x.1.push (allocStrEnc x.2 (charSlice str a b) bin).1,
                            (allocStrEnc x.2 (charSlice str a b) bin).2)
          | none => (x.1.push Value.nil, x.2)) (acc, m) l).1,
        pushRootK K (List.foldl (fun (x : Array Value × Machine) (sp : Option (Nat × Nat)) =>
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

@[simp, rootFrameLem] theorem capsFoldArray_frame (K : List Kont) (str : String) (bin : Bool)
    (xs : Array (Option (Nat × Nat))) (acc : Array Value) (m : Machine) :
    Array.foldl (fun (x : Array Value × Machine) (sp : Option (Nat × Nat)) =>
        match sp with
        | some (a, b) => (x.1.push (allocStrEnc x.2 (charSlice str a b) bin).1,
                          (allocStrEnc x.2 (charSlice str a b) bin).2)
        | none => (x.1.push Value.nil, x.2)) (acc, pushRootK K m) xs =
      ((Array.foldl (fun (x : Array Value × Machine) (sp : Option (Nat × Nat)) =>
          match sp with
          | some (a, b) => (x.1.push (allocStrEnc x.2 (charSlice str a b) bin).1,
                            (allocStrEnc x.2 (charSlice str a b) bin).2)
          | none => (x.1.push Value.nil, x.2)) (acc, m) xs).1,
        pushRootK K (Array.foldl (fun (x : Array Value × Machine) (sp : Option (Nat × Nat)) =>
          match sp with
          | some (a, b) => (x.1.push (allocStrEnc x.2 (charSlice str a b) bin).1,
                            (allocStrEnc x.2 (charSlice str a b) bin).2)
          | none => (x.1.push Value.nil, x.2)) (acc, m) xs).2) := by
  simp only [← Array.foldl_toList]
  exact capsFold_frame K str bin xs.toList acc m

/-- `runRegex`'s two `where` helpers that take a machine. `allMatches` and `runSearch` take
none, so they are the same computation on both sides and need no lemma — which is the useful
half of `Builtins` being written against the heap rather than against the machine. -/
@[simp, rootFrameLem] theorem applyTo_frame (K : List Kont) (bid : String) (m : Machine) (src : String)
    (opts : Nat) (str : String) (bin : Bool) :
    runRegex.applyTo bid (pushRootK K m) src opts str bin =
      bRootPush K (runRegex.applyTo bid m src opts str bin) := by
  rw [runRegex.applyTo.eq_def, runRegex.applyTo.eq_def]
  root_simp
  root_arms

@[simp, rootFrameLem] theorem regexApply_frame (K : List Kont) (bid : String) (m : Machine)
    (re subj : Value) :
    runRegex.regexApply bid (pushRootK K m) re subj =
      bRootPush K (runRegex.regexApply bid m re subj) := by
  rw [runRegex.regexApply.eq_def, runRegex.regexApply.eq_def]
  root_simp
  root_arms

@[rootFrameLem] theorem floatToInt_frame (K : List Kont) (m : Machine) (y : Float) :
    floatToInt (pushRootK K m) y = bRootPush K (floatToInt m y) := by
  simp only [floatToInt]
  split <;> rfl

@[rootFrameLem] theorem intBitRef_frame (K : List Kont) (m : Machine) (recv : Value)
    (args : List Value) :
    intBitRef (pushRootK K m) recv args = bRootPush K (intBitRef m recv args) := by
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
@[rootFrameLem] theorem scanAll_frame (K : List Kont) (m : Machine) (str src : String) (opts : Nat)
    (bin : Bool) :
    runRegex.scanAll (pushRootK K m) str src opts bin =
      bRootPush K (runRegex.scanAll m str src opts bin) := by
  rw [runRegex.scanAll.eq_def, runRegex.scanAll.eq_def]
  root_simp
  root_arms
  all_goals root_hof
  -- the outer `scan` fold, via the general lemma as a **conditional** rewrite: `rw` unifies
  -- the step from the goal and leaves its framing hypothesis as a side goal, which is what
  -- gets past having to write the step (and its matcher) out by hand
  -- the outer `scan` fold and the *inner* capture fold inside its step, both via the general
  -- lemma as a **conditional** rewrite: `rw` unifies the step from the goal and leaves its
  -- framing hypothesis as a side goal, which is what gets past having to write a step (and its
  -- matcher constant) out by hand. The loop is because the hypothesis contains the next fold.
  all_goals (repeat' first
    | rfl
    | (simp only [rootFrameLem]; done)
    | (simp [rootFrameLem]; done)
    | rw [foldPair_frame K]
    | rw [foldrPair_frame K]
    | rw [foldPairArray_frame K]
    | intro _
    | split)

set_option maxHeartbeats 1000000 in
@[rootFrameLem] theorem splitBy_frame (K : List Kont) (m : Machine) (str src : String) (opts : Nat)
    (lim : Int) (bin : Bool) :
    runRegex.splitBy (pushRootK K m) str src opts lim bin =
      bRootPush K (runRegex.splitBy m str src opts lim bin) := by
  rw [runRegex.splitBy.eq_def, runRegex.splitBy.eq_def]
  root_simp
  root_arms
  all_goals root_hof
  all_goals (repeat' first
    | rfl
    | (simp only [rootFrameLem]; done)
    | (simp [rootFrameLem]; done)
    | rw [foldPair_frame K]
    | rw [foldrPair_frame K]
    | rw [foldPairArray_frame K]
    | intro _
    | split)

set_option maxHeartbeats 1000000 in
@[rootFrameLem] theorem splitOn_frame (K : List Kont) (m : Machine) (h : Heap) (str : String)
    (pat : Value) (lim : Int) (bin : Bool) :
    runRegex.splitOn (pushRootK K m) h str pat lim bin =
      bRootPush K (runRegex.splitOn m h str pat lim bin) := by
  rw [runRegex.splitOn.eq_def, runRegex.splitOn.eq_def]
  root_simp
  root_arms
  all_goals root_hof
  all_goals (repeat' first
    | rfl
    | (simp only [rootFrameLem]; done)
    | (simp [rootFrameLem]; done)
    | rw [foldPair_frame K]
    | rw [foldrPair_frame K]
    | rw [foldPairArray_frame K]
    | intro _
    | split)

set_option maxHeartbeats 1000000 in
@[rootFrameLem] theorem subst_frame (K : List Kont) (m : Machine) (str src : String) (opts : Nat)
    (rep : String) (global : Bool) (recvV repV : Value) :
    runRegex.subst (pushRootK K m) str src opts rep global recvV repV =
      bRootPush K (runRegex.subst m str src opts rep global recvV repV) := by
  rw [runRegex.subst.eq_def, runRegex.subst.eq_def]
  root_simp
  root_arms
  all_goals root_hof
  all_goals (repeat' first
    | rfl
    | (simp only [rootFrameLem]; done)
    | (simp [rootFrameLem]; done)
    | rw [foldPair_frame K]
    | rw [foldrPair_frame K]
    | rw [foldPairArray_frame K]
    | intro _
    | split)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 400000 in
@[rootFrameLem] theorem runRegex_frame (K : List Kont) (bid : String) (recv : Value)
    (args : List Value) (m : Machine) :
    runRegex bid recv args (pushRootK K m) = bRootPush K (runRegex bid recv args m) := by
  rw [runRegex.eq_def, runRegex.eq_def]
  root_simp
  root_arms
  all_goals root_hof
  all_goals (repeat' first
    | rfl
    | (simp only [rootFrameLem]; done)
    | (simp [rootFrameLem]; done)
    | rw [foldPair_frame K]
    | rw [foldrPair_frame K]
    | rw [foldPairArray_frame K]
    | intro _
    | split)
  all_goals root_hof

@[rootFrameLem] theorem nativeModuleName_frame (K : List Kont) (m : Machine) (cp : ClassPayload) :
    nativeModuleName (pushRootK K m) cp = bRootPush K (nativeModuleName m cp) := by
  unfold nativeModuleName
  root_simp
  root_arms

@[rootFrameLem] theorem setConstantVisibility_frame (K : List Kont) (m : Machine)
    (recv : Value) (o : ObjId) (privateConst : Bool) (names : List String) :
    setConstantVisibility (pushRootK K m) recv o privateConst names =
      bRootPush K (setConstantVisibility m recv o privateConst names) := by
  induction names generalizing m with
  | nil => rfl
  | cons name rest ih =>
    simp only [setConstantVisibility, rootFrameLem]
    (repeat' split) <;> first | rfl | (refine Eq.trans ?_ (ih _); rfl)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 400000 in
@[rootFrameLem] theorem runModules_frame (K : List Kont) (bid : String) (recv : Value)
    (args : List Value) (m : Machine) :
    runModules bid recv args (pushRootK K m) = bRootPush K (runModules bid recv args m) := by
  rw [runModules.eq_def, runModules.eq_def]
  root_simp
  root_arms
  all_goals root_hof
  all_goals (repeat' first
    | rfl
    | (simp_all [rootFrameLem, pushRootK, bRootPush]; done)
    | (rw [foldPairArray_frame K]; try simp only [rootFrameLem])
    | intro _)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 400000 in
@[rootFrameLem] theorem runCollections_frame (K : List Kont) (bid : String) (recv : Value)
    (args : List Value) (m : Machine) (hLock : HashLockFree K) :
    runCollections bid recv args (pushRootK K m) = bRootPush K (runCollections bid recv args m) := by
  rw [runCollections.eq_def, runCollections.eq_def]
  have hh := hashIterationActive_rootFrame K hLock
  simp only [rootFrameLem, hh]
  root_arms
  all_goals root_hof
  all_goals (repeat' first
    | rfl
    | (simp_all [rootFrameLem, pushRootK, bRootPush]; done)
    | (rw [foldPairArray_frame K]; try simp only [rootFrameLem])
    | intro _)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 400000 in
@[rootFrameLem] theorem runStrings_frame (K : List Kont) (bid : String) (recv : Value)
    (args : List Value) (m : Machine) (hLock : HashLockFree K) :
    runStrings bid recv args (pushRootK K m) = bRootPush K (runStrings bid recv args m) := by
  rw [runStrings.eq_def, runStrings.eq_def]
  root_simp
  root_arms
  all_goals root_hof
  all_goals (repeat' first
    | rfl
    | (simp_all [rootFrameLem, pushRootK, bRootPush]; done)
    | (rw [foldPairArray_frame K]; try simp only [rootFrameLem])
    | intro _)


end RubyCore.Proof.Root
