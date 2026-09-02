import RubyCore.Proof.KontFrameReflect

/-!
# `RubyCore/Proof/KontFrameSend.lean` — the send layer, framed

`Interp/Send.lean`: `invoke` (the dispatch decision), `finishSend`/`startArgs`/`startKwargs`
(argument evaluation), `doSuper`/`zsuperArgs`, `doYield`, and the `for`-loop driver. Everything
here sits above `dispatchMiss`, so everything here inherits `CatchFree K`.
-/

set_option autoImplicit false
set_option maxRecDepth 400000

namespace RubyCore
namespace Proof

open Builtins
open Interp

/-! ### `getLocal`

Read through the `captured` chain, so its recursion is over `m.frames` — untouched by `pushK`,
which is why the walk transports by a plain induction on the fuel. `Machine.getLocal` is not in
`Interp`, so it had no framing lemma yet. -/

theorem getLocal_go_frame (K : List Kont) (m : Machine) (x : String) :
    ∀ (fuel : Nat) (fid : FrameId),
      Machine.getLocal.go (pushK K m) x fid fuel = Machine.getLocal.go m x fid fuel
  | 0, _ => rfl
  | fuel + 1, fid => by
    simp only [Machine.getLocal.go, pushK_frames]
    split
    · rfl
    · split
      · exact getLocal_go_frame K m x fuel _
      · rfl

@[simp, frameLem] theorem getLocal_frame (K : List Kont) (m : Machine) (x : String) :
    (pushK K m).getLocal x = m.getLocal x := by
  simp only [Machine.getLocal, pushK_frames, pushK_stack, getLocal_go_frame]

/-! ### The heap-only and machine-free leaves -/

@[simp, frameLem] theorem zsuperArgs_frame (K : List Kont) (m : Machine) :
    zsuperArgs (pushK K m) = zsuperArgs m := by
  simp only [zsuperArgs]
  frame_simp

@[simp, frameLem] theorem methodBlk_frame (K : List Kont) (m : Machine) :
    methodBlk (pushK K m) = methodBlk m := by
  simp only [methodBlk]
  frame_simp

@[simp, frameLem] theorem cvarScope_frame (K : List Kont) (m : Machine) :
    cvarScope (pushK K m) = cvarScope m := by
  simp only [cvarScope]
  frame_simp

@[simp, frameLem] theorem forwardBundle_frame (K : List Kont) (m : Machine) :
    forwardBundle (pushK K m) = forwardBundle m := by
  simp only [forwardBundle]
  frame_simp

@[simp, frameLem] theorem definedMethod?_frame (K : List Kont) (m : Machine) (recv : Value)
    (mname : String) (site : SendSite) :
    definedMethod? (pushK K m) recv mname site = definedMethod? m recv mname site := by
  simp only [definedMethod?]
  frame_simp
  -- `visError?` frames as an `Option.map`, and only its `isNone` is read here
  simp only [Option.isNone_map]

@[simp, frameLem] theorem forBind_frame (K : List Kont) (m : Machine)
    (targets : List (TargetKind × String)) (elem : Value) :
    forBind (pushK K m) targets elem = (forBind m targets elem).map (pushK K) := by
  simp only [forBind]
  frame_simp
  (repeat' first | rfl | (frame_simp; done) | split)
  -- the multi-target arm walks `setLocal` over the zipped targets
  all_goals (try (rw [foldMachine_frame K _ (fun m₂ a => by simp only [frameLem])]))
  all_goals (try rfl)
  all_goals (try (simp_all (maxSteps := 200000) [frameLem]))

/-! ### The walker for this layer, and its closer

Three things this layer needs that `Dispatch`'s and `Reflect`'s walkers did not.

* **The generic machine-fold instance.** `foldMachine_frame K _ (fun m₂ a => by simp only
  [frameLem])` — supplying the pointwise hypothesis as a `by` block rather than a named lemma
  is what makes one stage cover every machine-accumulator fold in the file, whatever its step
  happens to be.
* **`dsimp only`**, which iota-reduces a `let (v, m) := (a, b)` once framing has made the
  right-hand side a literal pair, so no `split` is needed there at all.
* **The conditional lemmas rewritten by name.** Everything from `dispatchMiss` up carries
  `CatchFree K`, so it cannot live in the `frameLem` simp set.

The closer is the interesting part. `split` on a scrutinee that *carries a machine* —
`Builtins.run bid recv args m`, whose framed form is `bpush K (…)` — leaves the two sides
related by a conjunction of component equations, `pushK K m = m'` among them. `simp_all`
splits the conjunction but can only use that equation **left to right**, which does nothing to
a goal whose right-hand side reads `pushK K (withCtl m c)`. Rewriting the goal *backwards*
with the wrapper's own framing lemma puts `pushK K m` into it, and then the hypothesis fires.
That one step is what took `invokeDispatch` from a wall of residual goals to none. -/

syntax "frame_close" ident : tactic
macro_rules
  | `(tactic| frame_close $K) =>
    `(tactic|
        (iterate 2
          (all_goals (try (frame_simp; try rfl))
           all_goals (try subst_vars)
           all_goals (try (frame_simp; try rfl))
           all_goals (try (rw [← withCtl_frame $K]; simp_all (maxSteps := 200000) [frameLem]))
           all_goals (try (rw [← withKont_frame $K]; simp_all (maxSteps := 200000) [frameLem]))
           all_goals (try (rw [← raiseErr_frame $K]; simp_all (maxSteps := 200000) [frameLem]))
           all_goals (try (simp_all (maxSteps := 400000) [frameLem]))
           all_goals (try subst_vars)
           all_goals (try (frame_simp; try rfl)))))

/-- The generic walker for this file: every stage, including the conditional lemmas. -/
syntax "send_walk" ident ident : tactic
macro_rules
  | `(tactic| send_walk $K $hK) =>
    `(tactic| repeat' first
        | rfl
        | (frame_simp; done)
        | simp only [frameLem]
        | dsimp only
        | (rw [invoke_frame $K $hK]; try rfl)
        | (rw [invokeDispatch_frame $K $hK]; try rfl)
        | (rw [dispatchMiss_frame $K $hK]; try rfl)
        | (rw [withCtl_mk $K]; try rfl)
        | (rw [withKont_mk $K]; try rfl)
        | (rw [callClosure_frame_mk_cons $K]; try rfl)
        | (rw [enterUserMethod_frame_mk_cons $K]; try rfl)
        | (rw [foldMachine_frame $K _ (fun m₂ a => by simp only [frameLem])])
        | (rw [foldOptM_frame_some $K])
        | (rw [foldPair_frame $K])
        | (intro p m₂ a; frame_simp; done)
        | (intro m₂ a; frame_simp; done)
        | (intro a; frame_simp; done)
        | split)

/-- Walk, close, and repeat. `frame_close`'s `simp_all`+`subst_vars` pair *exposes* new
applications — a `callClosure` or an `invoke` that was hidden behind a `pushK K m = m'`
equation only becomes rewritable once that equation is substituted — and only the walker can
rewrite those. Three rounds is what the largest of these functions needs. -/
syntax "send_prove" ident ident : tactic
macro_rules
  | `(tactic| send_prove $K $hK) =>
    `(tactic| (frame_simp
               iterate 3 (try (send_walk $K $hK)
                          try (frame_close $K))))

/-! ### `invoke` and its two `where` helpers

`invokeDispatch` (the dispatch decision — visibility, the ancestor walk, the tombstone and
miss paths) and `invokeMaybeNew` (`Class#new` with a user `initialize`) are non-recursive, so
they are framed first. `invoke` itself is self-recursive on the `send`/`public_send`/`__send__`
unwrapping, `termination_by args.length` — so its framing lemma is an induction on `args`,
with everything else generalised because the re-dispatch changes both the name and the site. -/

set_option maxHeartbeats 4000000 in
theorem invokeDispatch_frame (K : List Kont) (hK : CatchFree K) (m : Machine) (recv : Value)
    (implicit : SendSite) (mname : String) (args : List Value) (blk : Option Value)
    (kw : List (Value × Value)) :
    invoke.invokeDispatch (pushK K m) recv implicit mname args blk kw =
      frameR K (invoke.invokeDispatch m recv implicit mname args blk kw) := by
  rw [invoke.invokeDispatch.eq_def, invoke.invokeDispatch.eq_def]
  frame_simp
  (repeat' first
    | rfl
    | (frame_simp; done)
    | simp only [frameLem]
    | dsimp only
    | (rw [dispatchMiss_frame K hK]; try rfl)
    | (rw [withCtl_mk K]; try rfl)
    | (rw [withKont_mk K]; try rfl)
    | (rw [enterUserMethod_frame_mk_cons K]; try rfl)
    | (rw [foldMachine_frame K _ (fun m₂ a => by simp only [frameLem])])
    | split)
  frame_close K

set_option maxHeartbeats 4000000 in
theorem invokeMaybeNew_frame (K : List Kont) (hK : CatchFree K) (m : Machine) (recv : Value)
    (o : ObjId) (c : ClassPayload) (implicit : SendSite) (mname : String) (args : List Value)
    (blk : Option Value) (kw : List (Value × Value)) :
    invoke.invokeMaybeNew (pushK K m) recv o c implicit mname args blk kw =
      frameR K (invoke.invokeMaybeNew m recv o c implicit mname args blk kw) := by
  rw [invoke.invokeMaybeNew.eq_def, invoke.invokeMaybeNew.eq_def]
  frame_simp
  (repeat' first
    | rfl
    | (frame_simp; done)
    | simp only [frameLem]
    | dsimp only
    | (rw [invokeDispatch_frame K hK]; try rfl)
    | (rw [dispatchMiss_frame K hK]; try rfl)
    | (rw [withCtl_mk K]; try rfl)
    | (rw [withKont_mk K]; try rfl)
    | (rw [enterUserMethod_frame_mk_cons K]; try rfl)
    | (rw [foldMachine_frame K _ (fun m₂ a => by simp only [frameLem])])
    | split)
  frame_close K

set_option maxHeartbeats 4000000 in
theorem invoke_frame (K : List Kont) (hK : CatchFree K) (m : Machine) (recv : Value)
    (implicit : SendSite) (mname : String) (args : List Value) (blk : Option Value)
    (kw : List (Value × Value)) :
    invoke (pushK K m) recv implicit mname args blk kw =
      frameR K (invoke m recv implicit mname args blk kw) := by
  induction args generalizing m recv implicit mname blk kw with
  | nil =>
    rw [invoke.eq_def, invoke.eq_def]
    frame_simp
    (repeat' first
      | rfl
      | (frame_simp; done)
      | simp only [frameLem]
      | dsimp only
      | (rw [invokeDispatch_frame K hK]; try rfl)
      | (rw [invokeMaybeNew_frame K hK]; try rfl)
      | (rw [withCtl_mk K]; try rfl)
      | (rw [withKont_mk K]; try rfl)
      | split)
    frame_close K
  | cons a rest ih =>
    rw [invoke.eq_def, invoke.eq_def]
    frame_simp
    (repeat' first
      | rfl
      | (frame_simp; done)
      | simp only [frameLem]
      | dsimp only
      | (rw [ih]; try rfl)
      | (rw [invokeDispatch_frame K hK]; try rfl)
      | (rw [invokeMaybeNew_frame K hK]; try rfl)
      | (rw [withCtl_mk K]; try rfl)
      | (rw [withKont_mk K]; try rfl)
      | split)
    frame_close K

/-! ### The rest of the layer

`superFound` and `kwAdd` are heap-only / machine-free. Everything else pushes a continuation
or dispatches, and each is non-recursive, so they go through on the walker plus `frame_close`.
`finishSend`, `startArgs` and `startSuperArgs` reach `invoke`/`doSuper`, so they inherit
`CatchFree K` too. -/

@[simp, frameLem] theorem kwAdd_frame (kwacc : List (Value × Value)) (key val : Value) :
    kwAdd kwacc key val = kwAdd kwacc key val := rfl

set_option maxHeartbeats 4000000 in
theorem doSuper_frame (K : List Kont) (hK : CatchFree K) (m : Machine) (args : List Value)
    (blk : Option Value) (kw : List (Value × Value)) :
    doSuper (pushK K m) args blk kw = frameR K (doSuper m args blk kw) := by
  rw [doSuper.eq_def, doSuper.eq_def]
  send_prove K hK

set_option maxHeartbeats 4000000 in
theorem startSuperArgs_frame (K : List Kont) (hK : CatchFree K) (m : Machine)
    (acc : List Value) (rest : List Expr) (blk : Option Value) :
    startSuperArgs (pushK K m) acc rest blk = frameR K (startSuperArgs m acc rest blk) := by
  rw [startSuperArgs.eq_def, startSuperArgs.eq_def]
  frame_simp
  (repeat' first
    | rfl
    | (frame_simp; done)
    | simp only [frameLem]
    | dsimp only
    | (rw [doSuper_frame K hK]; try rfl)
    | (rw [withCtl_mk K]; try rfl)
    | (rw [withKont_mk K]; try rfl)
    | split)
  frame_close K

set_option maxHeartbeats 4000000 in
/-- `classNewBlock`, and the recipe for a `Builtins.run` scrutinee. Framing turns the pushed
side's `Builtins.run … (pushK K m)` into `bpush K (Builtins.run … m)`, and a `split` on *that*
peels the two sides' matches independently: it pairs a `.ok` arm of one with an `.err` arm of
the other and leaves goals whose hypotheses are contradictory only up to a conjunction it
cannot use. `generalize` the shared call and `cases` the result instead, and every arm reduces
on both sides at once. This is why the arm is a named function in the source. -/
@[simp, frameLem] theorem classNewBlock_frame (K : List Kont) (m : Machine) (recv : Value) (args : List Value)
    (v : Value) (isClass : Bool) :
    classNewBlock (pushK K m) recv args v isClass =
      frameR K (classNewBlock m recv args v isClass) := by
  rw [classNewBlock.eq_def, classNewBlock.eq_def]
  rw [run_frame K]
  generalize Builtins.run (if isClass then "Class#new" else "Module#new") recv args m = br
  cases br with
  | ok newV m₂ =>
    simp only [bpush, procClosure?_frame]
    (repeat' first
      | rfl
      | (frame_simp; done)
      | simp only [frameLem]
      | dsimp only
      | (rw [callClosure_frame_mk_cons K]; try rfl)
      | split)
    frame_close K
  | err cls msg m₂ => simp only [bpush]; frame_simp
  | throwV tv m₂ => simp only [bpush]; frame_simp
  | unsupported r => rfl

set_option maxHeartbeats 4000000 in
theorem finishSend_frame (K : List Kont) (hK : CatchFree K) (m : Machine) (recv : Value)
    (implicit : SendSite) (mname : String) (args : List Value) (pblk : PendingBlk)
    (kw : List (Value × Value)) :
    finishSend (pushK K m) recv implicit mname args pblk kw =
      frameR K (finishSend m recv implicit mname args pblk kw) := by
  rw [finishSend.eq_def, finishSend.eq_def]
  send_prove K hK
  all_goals (try (rw [invoke_frame K hK]))
  frame_close K

set_option maxHeartbeats 4000000 in
theorem startKwargs_frame (K : List Kont) (hK : CatchFree K) (m : Machine) (recv : Value)
    (implicit : SendSite) (mname : String) (posArgs : List Value)
    (kwacc : List (Value × Value)) (entries : List KwEntry) (pblk : PendingBlk) :
    startKwargs (pushK K m) recv implicit mname posArgs kwacc entries pblk =
      frameR K (startKwargs m recv implicit mname posArgs kwacc entries pblk) := by
  rw [startKwargs.eq_def, startKwargs.eq_def]
  frame_simp
  (repeat' first
    | rfl
    | (frame_simp; done)
    | simp only [frameLem]
    | dsimp only
    | (rw [finishSend_frame K hK]; try rfl)
    | (rw [withCtl_mk K]; try rfl)
    | (rw [withKont_mk K]; try rfl)
    | split)
  frame_close K

set_option maxHeartbeats 4000000 in
theorem startArgs_frame (K : List Kont) (hK : CatchFree K) (m : Machine) (recv : Value)
    (implicit : SendSite) (mname : String) (acc : List Value) (rest : List Expr)
    (pblk : PendingBlk) :
    startArgs (pushK K m) recv implicit mname acc rest pblk =
      frameR K (startArgs m recv implicit mname acc rest pblk) := by
  rw [startArgs.eq_def, startArgs.eq_def]
  frame_simp
  (repeat' first
    | rfl
    | (frame_simp; done)
    | simp only [frameLem]
    | dsimp only
    | (rw [finishSend_frame K hK]; try rfl)
    | (rw [startKwargs_frame K hK]; try rfl)
    | (rw [invoke_frame K hK]; try rfl)
    | (rw [withCtl_mk K]; try rfl)
    | (rw [withKont_mk K]; try rfl)
    | split)
  frame_close K

set_option maxHeartbeats 4000000 in
@[simp, frameLem] theorem doYield_frame (K : List Kont) (m : Machine) (args : List Value) :
    doYield (pushK K m) args = frameR K (doYield m args) := by
  rw [doYield.eq_def, doYield.eq_def]
  frame_simp
  (repeat' first
    | rfl
    | (frame_simp; done)
    | simp only [frameLem]
    | dsimp only
    | (rw [callClosure_frame_mk_cons K]; try rfl)
    | (rw [withCtl_mk K]; try rfl)
    | (rw [withKont_mk K]; try rfl)
    | split)
  frame_close K

set_option maxHeartbeats 4000000 in
@[simp, frameLem] theorem startYield_frame (K : List Kont) (m : Machine) (acc : List Value)
    (rest : List Expr) : startYield (pushK K m) acc rest = frameR K (startYield m acc rest) := by
  rw [startYield.eq_def, startYield.eq_def]
  frame_simp
  (repeat' first
    | rfl
    | (frame_simp; done)
    | simp only [frameLem]
    | dsimp only
    | (rw [doYield_frame K]; try rfl)
    | (rw [withCtl_mk K]; try rfl)
    | (rw [withKont_mk K]; try rfl)
    | split)
  frame_close K

set_option maxHeartbeats 4000000 in
@[simp, frameLem] theorem continueArray_frame (K : List Kont) (m : Machine) (acc : List Value)
    (rest : List Expr) :
    continueArray (pushK K m) acc rest = frameR K (continueArray m acc rest) := by
  rw [continueArray.eq_def, continueArray.eq_def]
  frame_simp
  (repeat' first
    | rfl
    | (frame_simp; done)
    | simp only [frameLem]
    | dsimp only
    | (rw [withCtl_mk K]; try rfl)
    | (rw [withKont_mk K]; try rfl)
    | split)
  frame_close K

set_option maxHeartbeats 4000000 in
@[simp, frameLem] theorem forStep_frame (K : List Kont) (m : Machine)
    (targets : List (TargetKind × String)) (body : Expr) (rest : List Value) (coll : Value) :
    forStep (pushK K m) targets body rest coll =
      frameR K (forStep m targets body rest coll) := by
  rw [forStep.eq_def, forStep.eq_def]
  frame_simp
  (repeat' first
    | rfl
    | (frame_simp; done)
    | simp only [frameLem]
    | dsimp only
    | (rw [withCtl_mk K]; try rfl)
    | (rw [withKont_mk K]; try rfl)
    | split)
  frame_close K

#print axioms doSuper_frame
#print axioms finishSend_frame
#print axioms startArgs_frame
#print axioms doYield_frame
#print axioms forStep_frame

#print axioms invokeDispatch_frame
#print axioms invokeMaybeNew_frame
#print axioms invoke_frame

end Proof
end RubyCore
