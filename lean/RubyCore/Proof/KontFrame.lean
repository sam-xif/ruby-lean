import RubyCore.Interp

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
set_option maxRecDepth 8000

namespace RubyCore
namespace Proof

/-! ## The tail, appended -/

/-- `m` with `K` appended below its own continuation. -/
def pushK (K : List Kont) (m : Machine) : Machine := { m with kont := m.kont ++ K }

@[simp] theorem pushK_heap (K : List Kont) (m : Machine) : (pushK K m).heap = m.heap := rfl
@[simp] theorem pushK_ctl (K : List Kont) (m : Machine) : (pushK K m).ctl = m.ctl := rfl
@[simp] theorem pushK_stack (K : List Kont) (m : Machine) : (pushK K m).stack = m.stack := rfl
@[simp] theorem pushK_frames (K : List Kont) (m : Machine) : (pushK K m).frames = m.frames := rfl
@[simp] theorem pushK_globals (K : List Kont) (m : Machine) :
    (pushK K m).globals = m.globals := rfl
@[simp] theorem pushK_out (K : List Kont) (m : Machine) : (pushK K m).out = m.out := rfl
@[simp] theorem pushK_currentExc (K : List Kont) (m : Machine) :
    (pushK K m).currentExc = m.currentExc := rfl
@[simp] theorem pushK_preludeMode (K : List Kont) (m : Machine) :
    (pushK K m).preludeMode = m.preludeMode := rfl
@[simp] theorem pushK_kont (K : List Kont) (m : Machine) :
    (pushK K m).kont = m.kont ++ K := rfl

@[simp] theorem pushK_currentFrame (K : List Kont) (m : Machine) :
    (pushK K m).currentFrame = m.currentFrame := rfl

/-- Every field but `kont` is copied, so a `pushK` commutes with any record update that does
not touch `kont`. The three that occur in this layer, as `rfl` lemmas. -/
@[simp] theorem pushK_setHeap (K : List Kont) (m : Machine) (h : Heap) :
    pushK K { m with heap := h } = { pushK K m with heap := h } := rfl

@[simp] theorem pushK_setOut (K : List Kont) (m : Machine) (s : String) :
    pushK K { m with out := s } = { pushK K m with out := s } := rfl

/-! ## `BRes`, with the tail carried through -/

/-- A builtin result, with the appended tail carried into whichever machine it holds. -/
def bpush (K : List Kont) : BRes → BRes
  | .ok v m => .ok v (pushK K m)
  | .err c s m => .err c s (pushK K m)
  | .throwV v m => .throwV v (pushK K m)
  | .unsupported r => .unsupported r

@[simp] theorem bpush_ok (K : List Kont) (v : Value) (m : Machine) :
    bpush K (.ok v m) = .ok v (pushK K m) := rfl
@[simp] theorem bpush_err (K : List Kont) (c : ObjId) (s : String) (m : Machine) :
    bpush K (.err c s m) = .err c s (pushK K m) := rfl
@[simp] theorem bpush_throwV (K : List Kont) (v : Value) (m : Machine) :
    bpush K (.throwV v m) = .throwV v (pushK K m) := rfl
@[simp] theorem bpush_unsupported (K : List Kont) (r : String) :
    bpush K (.unsupported r) = .unsupported r := rfl

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

@[simp] theorem allocStrEnc_frame (K : List Kont) (m : Machine) (s : String) (b : Bool) :
    allocStrEnc (pushK K m) s b = ((allocStrEnc m s b).1, pushK K (allocStrEnc m s b).2) := rfl

@[simp] theorem allocStr_frame (K : List Kont) (m : Machine) (s : String) :
    allocStr (pushK K m) s = ((allocStr m s).1, pushK K (allocStr m s).2) := rfl

@[simp] theorem allocArr_frame (K : List Kont) (m : Machine) (xs : Array Value) :
    allocArr (pushK K m) xs = ((allocArr m xs).1, pushK K (allocArr m xs).2) := rfl

@[simp] theorem allocHsh_frame (K : List Kont) (m : Machine) (xs : Array (Value × Value)) :
    allocHsh (pushK K m) xs = ((allocHsh m xs).1, pushK K (allocHsh m xs).2) := rfl

@[simp] theorem allocExc_frame (K : List Kont) (m : Machine) (c : ObjId) (s : String) :
    allocExc (pushK K m) c s = ((allocExc m c s).1, pushK K (allocExc m c s).2) := rfl

@[simp] theorem dupObj_frame (K : List Kont) (m : Machine) (o : ObjId) (kf : Bool) :
    dupObj (pushK K m) o kf = ((dupObj m o kf).1, pushK K (dupObj m o kf).2) := rfl

@[simp] theorem okStr_frame (K : List Kont) (m : Machine) (s : String) :
    okStr (pushK K m) s = bpush K (okStr m s) := rfl

@[simp] theorem okStrEnc_frame (K : List Kont) (m : Machine) (b : Bool) (s : String) :
    okStrEnc (pushK K m) b s = bpush K (okStrEnc m b s) := rfl

@[simp] theorem okStrFrom_frame (K : List Kont) (m : Machine) (src : Value) (s : String) :
    okStrFrom (pushK K m) src s = bpush K (okStrFrom m src s) := rfl

@[simp] theorem inspectP_frame (K : List Kont) (m : Machine) (v : Value) :
    inspectP (pushK K m) v = inspectP m v := rfl

@[simp] theorem toSP_frame (K : List Kont) (m : Machine) (v : Value) :
    toSP (pushK K m) v = toSP m v := rfl

@[simp] theorem coerceFailed_frame (K : List Kont) (c : String) (m : Machine) (b : Value) :
    coerceFailed c (pushK K m) b = bpush K (coerceFailed c m b) := rfl

@[simp] theorem frozenErr_frame (K : List Kont) (m : Machine) (recv : Value) (c : String) :
    frozenErr (pushK K m) recv c = bpush K (frozenErr m recv c) := by
  simp only [frozenErr, inspectP_frame]
  cases inspectP m recv <;> rfl

/-- **The exception-message reader**, which is the one leaf that is *not* `rfl`: it walks the
heap. `pushK` does not move the heap, so it is a projection. -/
@[simp] theorem emit_frame (K : List Kont) (m : Machine) (s : String) :
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
  | `(tactic| frame_simp) => `(tactic| try simp only [pushK_heap, pushK_ctl, pushK_stack,
      pushK_frames, pushK_globals, pushK_out, pushK_currentExc, pushK_preludeMode,
      pushK_kont, pushK_currentFrame, pushK_setHeap, pushK_setOut, bpush_ok, bpush_err,
      bpush_throwV, bpush_unsupported, allocStrEnc_frame, allocStr_frame, allocArr_frame,
      allocHsh_frame, allocExc_frame, dupObj_frame, okStr_frame, okStrEnc_frame,
      okStrFrom_frame, inspectP_frame, toSP_frame, coerceFailed_frame, frozenErr_frame,
      emit_frame, Builtins.binArg, Builtins.withIndex, Builtins.numBin, Builtins.numCmp])

syntax "frame_arms" : tactic
macro_rules
  | `(tactic| frame_arms) =>
    `(tactic| (repeat' first | rfl | split) <;>
        (try frame_simp) <;> (try rfl) <;> (try simp) <;> (try rfl) <;>
        (try simp_all (maxSteps := 400000)))


/-! ## The `Builtins` mid-level: the fuel walks and the four higher-order helpers

Two shapes here that the leaves did not have. **A fuel-recursive walk** (`putsGo`,
`flattenAll`) needs an induction on the fuel, and `putsGo` is the one that writes (`emit`), so
its statement carries the machine out. **A continuation-taking helper** (`withIndex`,
`numBin`, `numCmp`, `binArg`) frames only if its continuation does, so the hypothesis is
pointwise — which is exactly what holds at the call sites, where the continuation is a lambda
closing over the same machine. -/

theorem putsGo_frame (K : List Kont) : ∀ (fuel : Nat) (m : Machine) (args : List Value),
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

@[simp] theorem flattenAll_frame (K : List Kont) : ∀ (fuel : Nat) (m : Machine) (v : Value),
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
it gets its own induction. -/
@[simp] theorem printFold_frame (K : List Kont) :
    ∀ (args : List Value) (m : Machine),
      List.foldlM (fun (m : Machine) (a : Value) =>
          match toSP m a with
          | .ok s => some (m.emit s)
          | .error _ => none) (pushK K m) args =
        (List.foldlM (fun (m : Machine) (a : Value) =>
          match toSP m a with
          | .ok s => some (m.emit s)
          | .error _ => none) m args).map (pushK K)
  | [], _ => rfl
  | a :: rest, m => by
    simp only [List.foldlM_cons, toSP_frame]
    cases toSP m a with
    | error e => rfl
    | ok str =>
      simp only [emit_frame]
      exact printFold_frame K rest (m.emit str)

/-! ## The rest of the `Builtins` mid-level

The four continuation-taking helpers (`withIndex`, `numBin`, `numCmp`, `binArg`) get no lemma
of their own: they are small, and *unfolding* them at the dispatcher applies the continuation,
which is what turns the goal into the leaf lemmas above. `simp`-unfolding them is therefore
part of the dispatcher recipe rather than a step before it. -/

theorem putsImpl_frame (K : List Kont) (m : Machine) (args : List Value) :
    putsImpl (pushK K m) args = bpush K (putsImpl m args) := by
  rw [putsImpl, putsImpl, putsGo_frame]
  cases putsGo m args 100 <;> rfl

theorem raiseClass_frame (K : List Kont) (m : Machine) (cls : ObjId) (msg : Option Value) :
    raiseClass (pushK K m) cls msg = bpush K (raiseClass m cls msg) := by
  rw [raiseClass.eq_def, raiseClass.eq_def]
  frame_simp
  try simp only [allocExc_frame]
  frame_arms

theorem raiseImpl_frame (K : List Kont) (m : Machine) (args : List Value) :
    raiseImpl (pushK K m) args = bpush K (raiseImpl m args) := by
  rw [raiseImpl.eq_def, raiseImpl.eq_def]
  frame_simp
  try simp only [raiseClass_frame]
  frame_arms

set_option maxHeartbeats 2000000 in
theorem newImpl_frame (K : List Kont) (m : Machine) (recv : Value) (args : List Value) :
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

theorem joinImpl_frame (K : List Kont) (m : Machine) (recv : Value) (args : List Value) :
    joinImpl (pushK K m) recv args = bpush K (joinImpl m recv args) := by
  rw [joinImpl.eq_def, joinImpl.eq_def]
  frame_simp
  try simp only [flattenAll_frame]
  frame_arms

theorem sortImpl_frame (K : List Kont) (m : Machine) (recv : Value) :
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

theorem matchFrameOwner_frame (K : List Kont) (m : Machine) :
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

theorem matchFrameId_go_frame (K : List Kont) (m : Machine) :
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

@[simp] theorem matchFrameId_frame (K : List Kont) (m : Machine) :
    (pushK K m).matchFrameId = m.matchFrameId := by
  simp only [Machine.matchFrameId, pushK_stack]
  exact matchFrameId_go_frame K m _ _

@[simp] theorem setLastMatchValue_frame (K : List Kont) (m : Machine) (v : Value) :
    (pushK K m).setLastMatchValue v = pushK K (m.setLastMatchValue v) := by
  simp only [Machine.setLastMatchValue, matchFrameId_frame, pushK_frames]
  split <;> rfl

@[simp] theorem setMatchGlobals_frame (K : List Kont) (m : Machine) (md : Option Value) :
    setMatchGlobals (pushK K m) md = pushK K (setMatchGlobals m md) := by
  simp only [setMatchGlobals, setLastMatchValue_frame]

@[simp] theorem allocRegexp_frame (K : List Kont) (m : Machine) (src : String) (opts : Nat) :
    allocRegexp (pushK K m) src opts =
      ((allocRegexp m src opts).1, pushK K (allocRegexp m src opts).2) := rfl

@[simp] theorem allocMData_frame (K : List Kont) (m : Machine) (subj : String)
    (caps : Array (Option (Nat × Nat))) (names : List (String × Nat)) (bin : Bool) :
    allocMData (pushK K m) subj caps names bin =
      ((allocMData m subj caps names bin).1, pushK K (allocMData m subj caps names bin).2) := rfl

@[simp] theorem setLastMatch_frame (K : List Kont) (m : Machine) (s src : String) (opts : Nat)
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
@[simp] theorem charsFold_frame (K : List Kont) (bin : Bool) :
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

theorem allocFold_frame {α : Type} (K : List Kont) (f : Machine → α → Value × Machine)
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

theorem allocFoldArray_frame {α : Type} (K : List Kont) (f : Machine → α → Value × Machine)
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

/-! ### The three concrete fold shapes `Builtins` actually uses

The polymorphic lemma above is the argument; these are the instances, because `simp` matches
*syntactically* and the step functions in the interpreter are written out rather than
abstracted. Each is one application of `allocFold_frame` — the naming follows what the fold
builds. -/

@[simp] theorem namesFold_frame (K : List Kont) (l : List (String × Nat)) (acc : Array Value)
    (m : Machine) :
    List.foldl (fun (x : Array Value × Machine) (p : String × Nat) =>
        (x.1.push (allocStr x.2 p.1).1, (allocStr x.2 p.1).2)) (acc, pushK K m) l =
      ((List.foldl (fun (x : Array Value × Machine) (p : String × Nat) =>
          (x.1.push (allocStr x.2 p.1).1, (allocStr x.2 p.1).2)) (acc, m) l).1,
        pushK K (List.foldl (fun (x : Array Value × Machine) (p : String × Nat) =>
          (x.1.push (allocStr x.2 p.1).1, (allocStr x.2 p.1).2)) (acc, m) l).2) :=
  allocFold_frame K (fun m p => allocStr m p.1) (fun _ _ => rfl) l acc m

@[simp] theorem capsFold_frame (K : List Kont) (str : String) (bin : Bool)
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

@[simp] theorem capsFoldArray_frame (K : List Kont) (str : String) (bin : Bool)
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

/-- The framing set again, with everything proved since — the two macros are split at exactly
the point where the later lemmas are declared, so that the earlier proofs do not forward-refer
and the dispatchers get the full set. -/
syntax "frame_simp2" : tactic
macro_rules
  | `(tactic| frame_simp2) => `(tactic| try simp only [pushK_heap, pushK_ctl, pushK_stack,
      pushK_frames, pushK_globals, pushK_out, pushK_currentExc, pushK_preludeMode,
      pushK_kont, pushK_currentFrame, pushK_setHeap, pushK_setOut, bpush_ok, bpush_err,
      bpush_throwV, bpush_unsupported, allocStrEnc_frame, allocStr_frame, allocArr_frame,
      allocHsh_frame, allocExc_frame, dupObj_frame, okStr_frame, okStrEnc_frame,
      okStrFrom_frame, inspectP_frame, toSP_frame, coerceFailed_frame, frozenErr_frame,
      emit_frame, Builtins.binArg, Builtins.withIndex, Builtins.numBin, Builtins.numCmp,
      flattenAll_frame, putsImpl_frame, raiseClass_frame, raiseImpl_frame, newImpl_frame,
      joinImpl_frame, sortImpl_frame, matchFrameId_frame, setLastMatchValue_frame,
      setMatchGlobals_frame, allocRegexp_frame, allocMData_frame, setLastMatch_frame,
      charsFold_frame, namesFold_frame, capsFold_frame, capsFoldArray_frame,
      printFold_frame])

/-- The same set, applied to the **hypotheses** too. `split` leaves the two runs' outcomes as
hypotheses, and the contradictory cross-cases (the pushed fold answered `some`, the unpushed
one `none`) close only by rewriting *there* — which `simp only` on the goal does not do, and
which is why this variant exists. -/
syntax "frame_all" : tactic
macro_rules
  | `(tactic| frame_all) => `(tactic| try simp_all (maxSteps := 400000)
      [pushK_heap, pushK_ctl, pushK_stack, pushK_frames, pushK_globals, pushK_out,
       pushK_currentExc, pushK_preludeMode, pushK_currentFrame, bpush_ok, bpush_err,
       bpush_throwV, bpush_unsupported, allocStrEnc_frame, allocStr_frame, allocArr_frame,
       allocHsh_frame, allocExc_frame, dupObj_frame, okStr_frame, okStrEnc_frame,
       okStrFrom_frame, inspectP_frame, toSP_frame, coerceFailed_frame, frozenErr_frame,
       emit_frame, flattenAll_frame, matchFrameId_frame, setLastMatchValue_frame,
       setMatchGlobals_frame, allocRegexp_frame, allocMData_frame, setLastMatch_frame,
       charsFold_frame, namesFold_frame, capsFold_frame, capsFoldArray_frame,
       printFold_frame, putsGo_frame])

syntax "frame_arms2" : tactic
macro_rules
  | `(tactic| frame_arms2) =>
    `(tactic| (repeat' first | rfl | split) <;>
        (try frame_simp2) <;> (try rfl) <;> frame_all <;> (try rfl))

/-- `runRegex`'s two `where` helpers that take a machine. `allMatches` and `runSearch` take
none, so they are the same computation on both sides and need no lemma — which is the useful
half of `Builtins` being written against the heap rather than against the machine. -/
@[simp] theorem applyTo_frame (K : List Kont) (bid : String) (m : Machine) (src : String)
    (opts : Nat) (str : String) (bin : Bool) :
    runRegex.applyTo bid (pushK K m) src opts str bin =
      bpush K (runRegex.applyTo bid m src opts str bin) := by
  rw [runRegex.applyTo.eq_def, runRegex.applyTo.eq_def]
  frame_simp2
  frame_arms2

@[simp] theorem regexApply_frame (K : List Kont) (bid : String) (m : Machine)
    (re subj : Value) :
    runRegex.regexApply bid (pushK K m) re subj =
      bpush K (runRegex.regexApply bid m re subj) := by
  rw [runRegex.regexApply.eq_def, runRegex.regexApply.eq_def]
  frame_simp
  frame_arms

/-! ## The five dispatchers — **stated, not proved**, with the cost measured

`Builtins.run` chains five per-class rule files, and each is one theorem of the same shape:

```
runStrings bid recv args (pushK K m) = bpush K (runStrings bid recv args m)
```

All five were attempted, and the measurement is the point of this section, because
`ratchet/Denote/Sem/notes.md` §The fifth stall point named exactly this as the open question
("whether `invoke`'s descent into `Builtins/` is `rfl`-transparent in `kont` at kernel speed
is untested, and that is where the 24k lines actually are"). It is:

* **Transparent, and fast.** `runModules` (20 arms) closes in ~1.5 s with `rw [f.eq_def]` +
  `frame_arms`; `runStrings` (~100 arms, 465 lines) closes all but a handful in ~4 s. Nothing
  in `Builtins` reads `kont` — `grep` finds no `.kont` in the whole directory — so the layer
  is framing-transparent by construction and the proofs are bookkeeping.
* **`eq_def` is mandatory.** The equation compiler declines per-arm equations at this size
  ("failed to generate equational theorem for `runModules`"), so `simp only [f]` cannot be
  used; `rw [f.eq_def]` unfolds to the raw match and `split` walks it.
* **`split` does not scale to deep nesting**, and there is no knob: on `newImpl` (five nested
  `if`s over `ancestors` tests) `split`'s own `simp` reports "maximum number of steps
  exceeded", and neither `maxSteps` nor `simp.maxSteps` is a settable option. The fix is to
  case-split the conditions by hand (see `newImpl_frame`), which is mechanical but is ~15
  lines per such function rather than one tactic call.
* **The residual, counted exactly.** With the recipe and the fold lemmas above in scope:
  `runNumerics` **closes**; `runModules` leaves **1** goal (its delegation to `runRegex`),
  `runCollections` **1** (to `runModules`), `runStrings` **5**, `runObjects` **12**,
  `runRegex` **17** — and every residual is either a machine-taking `where` helper
  (`runRegex.scanAll`/`splitBy`/`splitOn`/`subst`) or one more allocating fold. Nothing else.
* **The friction that is left is `simp`'s, not the interpreter's**, and it is worth knowing
  before the next attempt: a fold lemma whose left-hand side is `List.foldlM f (pushK K m) l`
  with `f` a **lambda** is found by `rw` and *not* by `simp`/`simp_all` (the discrimination
  tree does not index under the lambda), so the contradictory cross-cases a `split` leaves
  behind — the pushed fold answered `some`, the unpushed one `none` — do not close
  automatically even with the right lemma in the simp set. That is what the eight `False`
  goals in `runObjects` are, and it is why the remaining work is per-arm rather than per-file.
* **What is actually left is the allocating folds.** Each dispatcher builds arrays by folding
  an allocation over a list, in a handful of bespoke shapes (`String#chars`, a pattern's group
  names, a match's capture spans as both `List` and `Array`, a hash's entries, `scan`'s nested
  per-match fold). Every one needs its own induction — `charsFold_frame`, `namesFold_frame`,
  `capsFold_frame`, `capsFoldArray_frame` above are four of them — *and* its own `@[simp]`
  instance, because `simp` matches syntactically and these steps are written out rather than
  abstracted. `allocFold_frame` is the general argument, and it covers only the shapes whose
  step really is a function of `(machine, element)`: the `Option`-matching ones push their
  `nil` inside the match and need the induction spelled again.

So the remaining Builtins-layer cost is **one small induction per fold plus one `where`-helper
lemma per dispatcher** (`runRegex.scanAll`, `runRegex.splitAll`, …), on the order of a few
hundred lines — bounded, mechanical, and *not* the 24k-line risk the note feared. What that
buys is one of the four layers `KontFrameCatchFree` needs; the `Interp` layer above it is the
one with the conditional statements (`applyKont`/`unwind` at `kont = []`), the `CatchFree`
threading, and the one `partial def` (`destructureBind`) that has to be given a structural
recursion before anything about it is provable at all.
-/

#print axioms putsGo_frame
#print axioms flattenAll_frame
#print axioms newImpl_frame
#print axioms setLastMatch_frame
#print axioms allocFold_frame

end Proof
end RubyCore
