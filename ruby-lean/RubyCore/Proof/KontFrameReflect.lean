import RubyCore.Proof.KontFrameDispatch

/-!
# `RubyCore/Proof/KontFrameReflect.lean` — the reflective layer, framed

`Interp/Reflect.lean`: `tryReflect` (the `attr_*`/`define_method`/`respond_to?`/`alias_method`
family, 390 lines and one `match` on the method name) and `dispatchMiss`, the funnel every
lookup miss goes through — `tryIterator`, then `tryMixin`, then `tryReflect`, then the CRuby
shadow gates, then `method_missing` or the byte-exact `NoMethodError`.

`dispatchMiss` is the reason the whole `Dispatch` file had to be framed first: it calls
`enterUserMethod`, and *it* is what `invoke` calls on a miss.
-/

set_option autoImplicit false
set_option maxRecDepth 400000

namespace RubyCore
namespace Proof

open Builtins
open Interp

/-! ### A fold over `Option Machine`

`tryReflect`'s `attr_*` and `alias_method`/`undef_method` arms walk a name list with a step
that returns `none` on the first failure, so the accumulator is an `Option Machine` rather
than a machine. Two lemmas: once `none`, always `none`; and the fold commutes with the push. -/

theorem foldOptM_none {α : Type} (f : Option Machine → α → Option Machine)
    (hn : ∀ a, f none a = none) : ∀ (l : List α), l.foldl f none = none
  | [] => rfl
  | a :: rest => by simp only [List.foldl_cons, hn]; exact foldOptM_none f hn rest

theorem foldOptM_frame {α : Type} (K : List Kont) (f : Option Machine → α → Option Machine)
    (hf : ∀ (m : Machine) (a : α),
      f (some (pushK K m)) a = (f (some m) a).map (pushK K))
    (hn : ∀ a, f none a = none) :
    ∀ (l : List α) (o : Option Machine),
      l.foldl f (o.map (pushK K)) = (l.foldl f o).map (pushK K)
  | [], _ => rfl
  | a :: rest, none => by
    simp only [Option.map_none, List.foldl_cons, hn, foldOptM_none f hn]
  | a :: rest, some m => by
    simp only [Option.map_some, List.foldl_cons, hf]
    exact foldOptM_frame K f hf hn rest (f (some m) a)

/-! ### `CatchFree`: the one place framing is *conditional*

`reflectThrow` reads the **whole** continuation — `m.kont.any (· is a `catchK` for this tag)`
decides whether the throw has a catcher, and CRuby raises `UncaughtThrowError` at the throw
site when it does not. So `reflectThrow (pushK K m) ≠ frameR K (reflectThrow m)` in general:
a `catchK` inside `K` turns a raise into a jump. This is the same fact the ratchet's
`Denote/Sem/Core/Frame.lean` records as the refutation of an unconditional `KontFrame`, met here
from the other side, and the repair is the same — the continuation being pushed has to be
catch-free. Every lemma above `reflectThrow` therefore carries the hypothesis, up to
`stepFn`; it is not an artefact of the proof. -/

/-- No frame of `K` is a `catch` marker. -/
def CatchFree (K : List Kont) : Prop := ∀ k ∈ K, ∀ t, k ≠ .catchK t

/-- Generic, and generic **on purpose**: the predicate is a parameter. `reflectThrow`'s
`m.kont.any (…)` uses a matcher constant generated for *that declaration*, and a lemma stating
the same match in this file generates a *different* constant — so a lemma phrased with the
match spelled out does not rewrite. With `p` a variable, unification supplies it. -/
theorem any_append_of_false {α : Type} (p : α → Bool) (l K : List α) (h : K.any p = false) :
    (l ++ K).any p = l.any p := by
  simp only [List.any_append, h, Bool.or_false]

theorem CatchFree.any_false {K : List Kont} (hK : CatchFree K) (p : Kont → Bool)
    (hp : ∀ k, (∀ t, k ≠ Kont.catchK t) → p k = false) : K.any p = false := by
  simp only [List.any_eq_false]
  intro k hk
  exact (Bool.not_eq_true _).mpr (hp k (hK k hk))

/-- The conditional framing lemma, and the reason `hasCatcher` is a named function in the
source: with a head constant on the left, `simp only [hasCatcher_frame K hK]` rewrites it
*under* a `match` arm, which is where `reflectThrow` reads it (the predicate there mentions the
arm-bound `tag`, so `rw` cannot abstract it from outside). -/
theorem hasCatcher_frame (K : List Kont) {hK : CatchFree K} (m : Machine) (tag : Value) :
    hasCatcher (pushK K m) tag = hasCatcher m tag := by
  simp only [hasCatcher, pushK_kont]
  exact any_append_of_false _ _ K (hK.any_false _ (by intro k h; cases k <;> simp_all))

/-- `foldOptM_frame` at the accumulator the source actually starts from. -/
theorem foldOptM_frame_some {α : Type} (K : List Kont) (f : Option Machine → α → Option Machine)
    (hf : ∀ (m : Machine) (a : α), f (some (pushK K m)) a = (f (some m) a).map (pushK K))
    (hn : ∀ a, f none a = none) (l : List α) (m : Machine) :
    l.foldl f (some (pushK K m)) = (l.foldl f (some m)).map (pushK K) :=
  foldOptM_frame K f hf hn l (some m)

/-! ### The leaves -/

@[simp, frameLem] theorem procClosure?_frame (K : List Kont) (m : Machine) (v : Value) :
    procClosure? (pushK K m) v = procClosure? m v := by
  simp only [procClosure?, pushK_heap]

@[simp, frameLem] theorem blockClosure?_frame (K : List Kont) (m : Machine)
    (blk : Option Value) : blockClosure? (pushK K m) blk = blockClosure? m blk := by
  simp only [blockClosure?]
  exact congrArg blk.bind (funext fun v => procClosure?_frame K m v)

/-- The `define_method` target id: machine-free, so `pushK` cannot change it. -/
@[simp, frameLem] theorem dmTarget?_frame (K : List Kont) (m : Machine) (recv : Value)
    (singleton : Bool) : dmTarget? (pushK K m) recv singleton = dmTarget? m recv singleton := by
  simp only [dmTarget?, pushK_heap, eigenclassOf_frame]

/-- …and the machine it grows. -/
@[simp, frameLem] theorem dmTargetM_frame (K : List Kont) (m : Machine) (recv : Value)
    (singleton : Bool) :
    dmTargetM (pushK K m) recv singleton = pushK K (dmTargetM m recv singleton) := by
  simp only [dmTargetM, eigenclassOf_frame]
  split
  all_goals (try split)
  all_goals rfl

/-! ### `tryReflect`

One `match` on `mname`, so `split` peels it by name and each arm is small on its own. The
`some`/`Option.map` return type is why the statement is a `.map (frameR K)` rather than an
equation between `StepResult`s. -/

/-- The arm walker for the reflective layer. The shape is `KontFrame.lean`'s `frame_hof`, not
its `frame_arms`: the stages are **interleaved with** `split` rather than run after it. That
matters here and did not in `Dispatch` — `tryReflect` is matches nested six deep, and splitting
to exhaustion first desynchronises the two sides (a `let m := …` under a push becomes an opaque
`m✝` that has lost its relation to the unpushed side's, and 566 goals are left, 123 of them the
impossible `none = some …`). Closing each arm as it appears keeps the scrutinees equal. -/
syntax "reflect_arms" ident : tactic
macro_rules
  | `(tactic| reflect_arms $K) =>
    `(tactic| repeat' first
        | rfl
        | (frame_simp; done)
        -- **without `done`, and deliberately.** `simp only` *fails* when it cannot make
        -- progress, so it cannot loop here — and the `(frame_simp; done)` alternative above
        -- rolls its own progress back when it does not finish the goal, which is what left
        -- the two `Option Machine` folds unframed: the rewrite that follows needs
        -- `symOrStr (pushK K m)` normalised first.
        | simp only [frameLem]
        | (rw [withCtl_mk $K]; try rfl)
        | (rw [withKont_mk $K]; try rfl)
        | (rw [callClosure_frame_mk_cons $K]; try rfl)
        | (rw [enterUserMethod_frame_mk_cons $K]; try rfl)
        | (rw [foldOptM_frame_some $K])
        | (rw [foldOptM_frame $K])
        | (rw [foldPair_frame $K])
        | (intro p m₂ a; frame_simp; done)
        | (intro m₂ a; frame_simp; done)
        | (intro a; frame_simp; done)
        | split)

/-! ### Point-free variants

`symOrStr_frame` and `procClosure?_frame` are stated applied, and the source uses both
*partially* applied — `args.filterMap (symOrStr m)`, `blk.bind (procClosure? m)` — where an
applied lemma cannot rewrite. One `funext` each, and both shapes are covered. -/

@[simp, frameLem] theorem symOrStr_frame_fun (K : List Kont) (m : Machine) :
    symOrStr (pushK K m) = symOrStr m := funext fun v => symOrStr_frame K m v

@[simp, frameLem] theorem procClosure?_frame_fun (K : List Kont) (m : Machine) :
    procClosure? (pushK K m) = procClosure? m := funext fun v => procClosure?_frame K m v

/-! ### The two `Option Machine` walks

`removeNames` and `visNames` fold a heap-only step over the requested names. Each is framed
once, and then its `Bool` decision and its machine are framed *separately* — which is the
whole reason the source splits them that way. -/

theorem removeNames_frame (K : List Kont) (m : Machine) (o : ObjId) (undef : Bool)
    (names : List String) :
    removeNames (pushK K m) o undef names = (removeNames m o undef names).map (pushK K) := by
  simp only [removeNames]
  refine foldOptM_frame_some K _ ?_ (fun _ => rfl) names m
  intro m₂ a
  simp only [Option.bind_some, pushK_heap]
  split
  · split
    · rfl
    · split
      · split <;> rfl
      · rfl
  · rfl

@[simp, frameLem] theorem removeOk_frame (K : List Kont) (m : Machine) (o : ObjId)
    (undef : Bool) (names : List String) :
    removeOk (pushK K m) o undef names = removeOk m o undef names := by
  simp only [removeOk, removeNames_frame, Option.isSome_map]

@[simp, frameLem] theorem removeRun_frame (K : List Kont) (m : Machine) (o : ObjId)
    (undef : Bool) (names : List String) :
    removeRun (pushK K m) o undef names = pushK K (removeRun m o undef names) := by
  simp only [removeRun, removeNames_frame]
  cases removeNames m o undef names <;> rfl

theorem visNames_frame (K : List Kont) (m : Machine) (o target : ObjId) (vis : Visibility)
    (modFun : Bool) (names : List String) :
    visNames (pushK K m) o target vis modFun names =
      (visNames m o target vis modFun names).map (pushK K) := by
  simp only [visNames]
  refine foldOptM_frame_some K _ ?_ (fun _ => rfl) names m
  intro m₂ a
  simp only [Option.bind_some, pushK_heap]
  split
  · split
    · rfl
    · split
      · rw [eigenclassOf_frame_mk K]
        rfl
      · rfl
  · rfl

@[simp, frameLem] theorem visOk_frame (K : List Kont) (m : Machine) (o target : ObjId)
    (vis : Visibility) (modFun : Bool) (names : List String) :
    visOk (pushK K m) o target vis modFun names = visOk m o target vis modFun names := by
  simp only [visOk, visNames_frame, Option.isSome_map]

@[simp, frameLem] theorem visRun_frame (K : List Kont) (m : Machine) (o target : ObjId)
    (vis : Visibility) (modFun : Bool) (names : List String) :
    visRun (pushK K m) o target vis modFun names = pushK K (visRun m o target vis modFun names) := by
  simp only [visRun, visNames_frame]
  cases visNames m o target vis modFun names <;> rfl

/-! ### The sixteen arms, one at a time

`tryReflect` used to be one 390-line `match mname with`, and proving it in one go left 566
residual goals (166 after interleaving the stages with `split`, 135 after naming its
machine-carrying `let`) — most of them impossible, because `split` had paired an arm of the
pushed side's match with a *different* arm of the unpushed side's. The 390 lines are now one
`def` per method family in `Interp/Reflect.lean`, which is the right shape for the source
independently of this proof, and each arm's framing lemma is small enough to iterate on in
seconds. `tryReflect_frame` is then a `split` over the name and sixteen `exact`s. -/

set_option maxHeartbeats 4000000 in
@[simp, frameLem] theorem reflectDefineMethod_frame (K : List Kont) (m : Machine) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value) :
    reflectDefineMethod (pushK K m) recv mname args blk =
      (reflectDefineMethod m recv mname args blk).map (frameR K) := by
  rw [reflectDefineMethod.eq_def, reflectDefineMethod.eq_def]
  frame_simp
  reflect_arms K
  all_goals (try (frame_simp; try rfl))
  all_goals (try (simp_all (maxSteps := 400000) [frameLem]))
  all_goals (try grind)

set_option maxHeartbeats 4000000 in
@[simp, frameLem] theorem reflectEval_frame (K : List Kont) (m : Machine) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value) :
    reflectEval (pushK K m) recv mname args blk =
      (reflectEval m recv mname args blk).map (frameR K) := by
  rw [reflectEval.eq_def, reflectEval.eq_def]
  frame_simp
  reflect_arms K
  all_goals (try (frame_simp; try rfl))
  all_goals (try (simp_all (maxSteps := 400000) [frameLem]))
  all_goals (try grind)

set_option maxHeartbeats 4000000 in
@[simp, frameLem] theorem reflectCatch_frame (K : List Kont) (m : Machine) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value) :
    reflectCatch (pushK K m) recv mname args blk =
      (reflectCatch m recv mname args blk).map (frameR K) := by
  rw [reflectCatch.eq_def, reflectCatch.eq_def]
  frame_simp
  reflect_arms K
  all_goals (try (frame_simp; try rfl))
  all_goals (try (simp_all (maxSteps := 400000) [frameLem]))
  all_goals (try grind)

set_option maxHeartbeats 4000000 in
theorem reflectThrow_frame (K : List Kont) (hK : CatchFree K) (m : Machine) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value) :
    reflectThrow (pushK K m) recv mname args blk =
      (reflectThrow m recv mname args blk).map (frameR K) := by
  rw [reflectThrow.eq_def, reflectThrow.eq_def]
  simp only [hasCatcher_frame (hK := hK) K]
  frame_simp
  reflect_arms K
  all_goals (try (frame_simp; try rfl))
  all_goals (try (simp_all (maxSteps := 400000) [frameLem]))
  all_goals (try grind)

set_option maxHeartbeats 4000000 in
@[simp, frameLem] theorem reflectVisibility_frame (K : List Kont) (m : Machine) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value) :
    reflectVisibility (pushK K m) recv mname args blk =
      (reflectVisibility m recv mname args blk).map (frameR K) := by
  rw [reflectVisibility.eq_def, reflectVisibility.eq_def]
  frame_simp
  reflect_arms K
  all_goals (try (frame_simp; try rfl))
  all_goals (try (simp_all (maxSteps := 400000) [frameLem]))
  all_goals (try grind)

set_option maxHeartbeats 4000000 in
@[simp, frameLem] theorem reflectSingletonClass_frame (K : List Kont) (m : Machine) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value) :
    reflectSingletonClass (pushK K m) recv mname args blk =
      (reflectSingletonClass m recv mname args blk).map (frameR K) := by
  rw [reflectSingletonClass.eq_def, reflectSingletonClass.eq_def]
  frame_simp
  reflect_arms K
  all_goals (try (frame_simp; try rfl))
  all_goals (try (simp_all (maxSteps := 400000) [frameLem]))
  all_goals (try grind)

set_option maxHeartbeats 4000000 in
@[simp, frameLem] theorem reflectIvarGet_frame (K : List Kont) (m : Machine) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value) :
    reflectIvarGet (pushK K m) recv mname args blk =
      (reflectIvarGet m recv mname args blk).map (frameR K) := by
  rw [reflectIvarGet.eq_def, reflectIvarGet.eq_def]
  frame_simp
  reflect_arms K
  all_goals (try (frame_simp; try rfl))
  all_goals (try (simp_all (maxSteps := 400000) [frameLem]))
  all_goals (try grind)

set_option maxHeartbeats 4000000 in
@[simp, frameLem] theorem reflectIvarSet_frame (K : List Kont) (m : Machine) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value) :
    reflectIvarSet (pushK K m) recv mname args blk =
      (reflectIvarSet m recv mname args blk).map (frameR K) := by
  rw [reflectIvarSet.eq_def, reflectIvarSet.eq_def]
  frame_simp
  reflect_arms K
  all_goals (try (frame_simp; try rfl))
  all_goals (try (simp_all (maxSteps := 400000) [frameLem]))
  all_goals (try grind)

set_option maxHeartbeats 4000000 in
@[simp, frameLem] theorem reflectIvarNames_frame (K : List Kont) (m : Machine) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value) :
    reflectIvarNames (pushK K m) recv mname args blk =
      (reflectIvarNames m recv mname args blk).map (frameR K) := by
  rw [reflectIvarNames.eq_def, reflectIvarNames.eq_def]
  frame_simp
  reflect_arms K
  all_goals (try (frame_simp; try rfl))
  all_goals (try (simp_all (maxSteps := 400000) [frameLem]))
  all_goals (try grind)

set_option maxHeartbeats 4000000 in
@[simp, frameLem] theorem reflectConstGet_frame (K : List Kont) (m : Machine) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value) :
    reflectConstGet (pushK K m) recv mname args blk =
      (reflectConstGet m recv mname args blk).map (frameR K) := by
  rw [reflectConstGet.eq_def, reflectConstGet.eq_def]
  frame_simp
  reflect_arms K
  all_goals (try (frame_simp; try rfl))
  all_goals (try (simp_all (maxSteps := 400000) [frameLem]))
  all_goals (try grind)

set_option maxHeartbeats 4000000 in
@[simp, frameLem] theorem reflectConstSet_frame (K : List Kont) (m : Machine) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value) :
    reflectConstSet (pushK K m) recv mname args blk =
      (reflectConstSet m recv mname args blk).map (frameR K) := by
  rw [reflectConstSet.eq_def, reflectConstSet.eq_def]
  frame_simp
  reflect_arms K
  all_goals (try (frame_simp; try rfl))
  all_goals (try (simp_all (maxSteps := 400000) [frameLem]))
  all_goals (try grind)

set_option maxHeartbeats 4000000 in
@[simp, frameLem] theorem reflectRemoveMethod_frame (K : List Kont) (m : Machine) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value) :
    reflectRemoveMethod (pushK K m) recv mname args blk =
      (reflectRemoveMethod m recv mname args blk).map (frameR K) := by
  rw [reflectRemoveMethod.eq_def, reflectRemoveMethod.eq_def]
  frame_simp
  reflect_arms K
  all_goals (try (frame_simp; try rfl))
  all_goals (try (simp_all (maxSteps := 400000) [frameLem]))
  all_goals (try grind)

set_option maxHeartbeats 4000000 in
@[simp, frameLem] theorem reflectAliasMethod_frame (K : List Kont) (m : Machine) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value) :
    reflectAliasMethod (pushK K m) recv mname args blk =
      (reflectAliasMethod m recv mname args blk).map (frameR K) := by
  rw [reflectAliasMethod.eq_def, reflectAliasMethod.eq_def]
  frame_simp
  reflect_arms K
  all_goals (try (frame_simp; try rfl))
  all_goals (try (simp_all (maxSteps := 400000) [frameLem]))
  all_goals (try grind)

set_option maxHeartbeats 4000000 in
@[simp, frameLem] theorem reflectAttr_frame (K : List Kont) (m : Machine) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value) :
    reflectAttr (pushK K m) recv mname args blk =
      (reflectAttr m recv mname args blk).map (frameR K) := by
  rw [reflectAttr.eq_def, reflectAttr.eq_def]
  frame_simp
  reflect_arms K
  all_goals (try (frame_simp; try rfl))
  all_goals (try (simp_all (maxSteps := 400000) [frameLem]))
  all_goals (try grind)

set_option maxHeartbeats 4000000 in
@[simp, frameLem] theorem reflectMethodDefined_frame (K : List Kont) (m : Machine) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value) :
    reflectMethodDefined (pushK K m) recv mname args blk =
      (reflectMethodDefined m recv mname args blk).map (frameR K) := by
  rw [reflectMethodDefined.eq_def, reflectMethodDefined.eq_def]
  frame_simp
  reflect_arms K
  all_goals (try (frame_simp; try rfl))
  all_goals (try (simp_all (maxSteps := 400000) [frameLem]))
  all_goals (try grind)

set_option maxHeartbeats 4000000 in
@[simp, frameLem] theorem reflectRespondTo_frame (K : List Kont) (m : Machine) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value) :
    reflectRespondTo (pushK K m) recv mname args blk =
      (reflectRespondTo m recv mname args blk).map (frameR K) := by
  rw [reflectRespondTo.eq_def, reflectRespondTo.eq_def]
  frame_simp
  reflect_arms K
  all_goals (try (frame_simp; try rfl))
  all_goals (try (simp_all (maxSteps := 400000) [frameLem]))
  all_goals (try grind)

theorem tryReflect_frame (K : List Kont) (hK : CatchFree K) (m : Machine) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value) :
    tryReflect (pushK K m) recv mname args blk =
      (tryReflect m recv mname args blk).map (frameR K) := by
  rw [tryReflect.eq_def, tryReflect.eq_def]
  -- one `split` on the name, then the sixteen arm lemmas — fifteen of them are in the
  -- `frameLem` set, and `reflectThrow`'s is the conditional one
  split
  all_goals (try (rw [reflectThrow_frame K hK]))
  all_goals (try (frame_simp; try rfl))
  all_goals rfl

/-! ### `dispatchMiss`, the funnel

Every lookup miss goes through here, so this is the lemma the dispatch layer above actually
consumes: `tryIterator`, then `tryMixin`, then `tryReflect`, then the three CRuby shadow gates
(heap-only), then `method_missing` or the byte-exact `NoMethodError`. It inherits
`reflectThrow`'s hypothesis, and everything above it will too — up to `stepFn`. -/

set_option maxHeartbeats 4000000 in
theorem dispatchMiss_frame (K : List Kont) (hK : CatchFree K) (m : Machine) (recv : Value)
    (implicit : SendSite) (mname : String) (args : List Value) (blk : Option Value) :
    dispatchMiss (pushK K m) recv implicit mname args blk =
      frameR K (dispatchMiss m recv implicit mname args blk) := by
  rw [dispatchMiss.eq_def, dispatchMiss.eq_def]
  rw [tryReflect_frame K hK]
  frame_simp
  (repeat' first
    | rfl
    | (frame_simp; done)
    | simp only [frameLem]
    | (rw [withCtl_mk K]; try rfl)
    | (rw [enterUserMethod_frame_mk_cons K]; try rfl)
    | split)
  all_goals (try (frame_simp; try rfl))
  all_goals (try (simp_all (maxSteps := 400000) [frameLem]))

#print axioms tryReflect_frame
#print axioms dispatchMiss_frame

end Proof
end RubyCore
