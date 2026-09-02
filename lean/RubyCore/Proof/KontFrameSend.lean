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

#print axioms invokeDispatch_frame
#print axioms invokeMaybeNew_frame
#print axioms invoke_frame

end Proof
end RubyCore
