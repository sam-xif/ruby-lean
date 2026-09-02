import RubyCore.Proof.KontFrame

/-!
# `RubyCore/Proof/KontFrameDispatch.lean` — the frame-pushing entries

`RubyCore/Proof/KontFrame.lean` carries the continuation-framing lemmas for `Builtins`,
`Interp/Support.lean` and most of `Interp/Dispatch.lean`. This file continues with the
functions that were too large to iterate on there: a change here does not recompile that one.

Every function in this file **pushes a frame**, and that is why they are grouped: `pushK` pins
`frames` and `stack`, so the pushed frame and the new stack are the same on both sides and the
`frameK`/`blkFrameK` marker frames by `withKont`'s `rfl`. What is expensive is not the
argument, it is the size of the arms.
-/

set_option autoImplicit false
set_option maxRecDepth 400000

namespace RubyCore
namespace Proof

open Builtins
open Interp

/-- `frame_arms` without its `simp_all` stage. On these two functions `simp_all` destructures
`StepResult.next X = StepResult.next Y` into field equations and then *mismatches the arms* —
comparing a `raiseErr` against a `withKont` — which is the same "`simp_all` must be a last
resort" lesson as `KontFrame.lean`'s, in its sharpest form yet. -/
syntax "frame_arms_pure" : tactic
macro_rules
  | `(tactic| frame_arms_pure) =>
    `(tactic| (repeat' first | rfl | split) <;> (try frame_simp) <;> (try rfl))

/-! ### What does *not* work here, recorded because it looked obvious

A `@[simp]` lemma re-folding a flat machine literal into `pushK K ⟨…⟩` — the missing direction
for the arms where Lean has collapsed nested record updates — makes things **worse**: simp then
uses structure eta to expand every machine into a field-wise literal
(`{ctl := X.ctl, kont := X.kont, …}` for each of nine fields), and a two-arm goal becomes
ninety. The shape problem has to be handled per arm instead, which is what the two proofs
below do by *not* normalising: `split` and `rfl` alone, since `pushK` is `@[reducible]` and
`rfl` therefore sees through it. -/

/-- `eigenclassOf`'s framing lemma **at a machine literal**, which is the shape
`enterClassBody` reaches it in: the machine there is `{ m with heap := constSetIn … }` after a
push, and Lean has collapsed that into one flat literal whose `kont` is `k ++ K` — which
`eigenclassOf_frame`'s `pushK K ?m` cannot unify with. Keyed on `eigenclassOf` rather than on
"any machine literal", which is what keeps it from triggering the structure-eta blowup
described above. -/
@[simp, frameLem] theorem eigenclassOf_frame_mk (K : List Kont) (c : Ctl) (k : List Kont)
    (st : List FrameId) (fr : Array Frame) (h : Heap) (g : List (String × Value))
    (out : String) (ce : Option Value) (pm : Bool) (o : ObjId) :
    eigenclassOf ⟨c, k ++ K, st, fr, h, g, out, ce, pm⟩ o =
      ((eigenclassOf ⟨c, k, st, fr, h, g, out, ce, pm⟩ o).1,
        pushK K (eigenclassOf ⟨c, k, st, fr, h, g, out, ce, pm⟩ o).2) :=
  eigenclassOf_frame K ⟨c, k, st, fr, h, g, out, ce, pm⟩ o

set_option maxHeartbeats 4000000 in
@[simp, frameLem] theorem enterClassBody_frame (K : List Kont) (m : Machine) (name : String)
    (isMod : Bool) (sup? : Option ObjId) (body : Expr) :
    enterClassBody (pushK K m) name isMod sup? body =
      frameR K (enterClassBody m name isMod sup? body) := by
  rw [enterClassBody.eq_def, enterClassBody.eq_def]
  -- `frame_simp` **first**, to make the two sides' scrutinees syntactically equal: without it
  -- `split` peels the pushed and unpushed matches *independently* and pairs arm `i` of one
  -- with arm `j` of the other, which is where the nonsense goals comparing a `raiseErr`
  -- against a `withKont` came from.
  frame_simp
  (repeat' first | rfl | split) <;> (try rfl) <;> (try (simp only [withKont, pushK]; rfl))
    <;> (try (frame_simp; try rfl)) <;> (try (simp_all (maxSteps := 400000) [frameLem]))

set_option maxHeartbeats 4000000 in
@[simp, frameLem] theorem enterScopedClassBody_frame (K : List Kont) (m : Machine)
    (container : ObjId) (name : String) (isMod : Bool) (body : Expr) :
    enterScopedClassBody (pushK K m) container name isMod body =
      frameR K (enterScopedClassBody m container name isMod body) := by
  rw [enterScopedClassBody.eq_def, enterScopedClassBody.eq_def]
  -- `frame_simp` **first**, to make the two sides' scrutinees syntactically equal: without it
  -- `split` peels the pushed and unpushed matches *independently* and pairs arm `i` of one
  -- with arm `j` of the other, which is where the nonsense goals comparing a `raiseErr`
  -- against a `withKont` came from.
  frame_simp
  (repeat' first | rfl | split) <;> (try rfl) <;> (try (simp only [withKont, pushK]; rfl))
    <;> (try (frame_simp; try rfl)) <;> (try (simp_all (maxSteps := 400000) [frameLem]))

/-- The **machine-only** fold: `enterUserMethod` finishes by `setLocal`-ing the phase-B
bindings one after another, with the machine as the whole accumulator. -/
theorem foldMachine_frame {α : Type} (K : List Kont) (f : Machine → α → Machine)
    (hf : ∀ (m : Machine) (a : α), f (pushK K m) a = pushK K (f m a)) :
    ∀ (l : List α) (m : Machine),
      List.foldl f (pushK K m) l = pushK K (List.foldl f m l)
  | [], _ => rfl
  | a :: rest, m => by
    simp only [List.foldl_cons, hf m a]
    exact foldMachine_frame K f hf rest (f m a)

/-- The `setLocal` fold **at a machine literal** — the shape problem again, and the last place
it comes up. `enterUserMethod` pushes the activation frame and the `frameK` marker by record
update, so the machine reaching the phase-B `setLocal` walk is a flat literal whose `kont` is
`.frameK fid :: (m.kont ++ K)`; `foldMachine_frame`'s `pushK K ?m` cannot unify with that, and
this keyed variant can. -/
theorem foldSetLocal_mk (K : List Kont) (c : Ctl) (k : List Kont) (st : List FrameId)
    (fr : Array Frame) (h : Heap) (g : List (String × Value)) (out : String)
    (ce : Option Value) (pm : Bool) (l : List (String × Value)) :
    List.foldl (fun (m : Machine) (nv : String × Value) => m.setLocal nv.1 nv.2)
        ⟨c, k ++ K, st, fr, h, g, out, ce, pm⟩ l =
      pushK K (List.foldl (fun (m : Machine) (nv : String × Value) => m.setLocal nv.1 nv.2)
        ⟨c, k, st, fr, h, g, out, ce, pm⟩ l) :=
  foldMachine_frame K _ (fun m₂ nv => setLocal_frame K m₂ nv.1 nv.2) l
    ⟨c, k, st, fr, h, g, out, ce, pm⟩

/-- `enterUserMethod`'s arm walker, as a **sequence of `all_goals` stages** rather than a
`<;>` chain: the conditional rewrites create new goals halfway through, and a chain applies its
later stages only to the goals that existed when it started. -/
syntax "enter_arms" ident : tactic
macro_rules
  | `(tactic| enter_arms $K) =>
    `(tactic|
        ((repeat' first | split | rfl)
         all_goals (try rfl)
         all_goals (try (rw [foldPair_frame $K]))
         all_goals (try (rw [foldSetLocal_mk $K]))
         all_goals (try rfl)
         all_goals (try (intro p m₂ a
                         frame_simp
                         try rfl))
         all_goals (try (intro p m₂ a
                         rw [destructureBind_frame $K]
                         try rfl))
         all_goals (try (simp only [withKont, pushK]; rfl))
         all_goals (try (frame_simp; try rfl))
         all_goals (try rfl)
         -- second and third rounds: the `*rest`/`**kwrest` allocations and the destructuring
         -- fold behind them only become reachable once what precedes them has been framed
         all_goals (try (simp [frameLem]))
         all_goals (try rfl)
         all_goals (try (rw [foldPair_frame $K]))
         all_goals (try (intro p m₂ a; frame_simp; try rfl))
         all_goals (try (rw [foldSetLocal_mk $K]))
         all_goals (try (simp [frameLem]))
         all_goals (try rfl)))

example (K : List Kont) (m : Machine) (subs : List Param) (v : Value) :
    (destructureBind (pushK K m) subs v (destrDepth subs + 1)).1 =
      (destructureBind m subs v (destrDepth subs + 1)).1 := by
  rw [destructureBind_frame K]

/-! ### `enterUserMethod`, the largest function in the layer

135 lines, `classifyFull`, two locals lists built by folds, `destructureBind`, the activation
frame and the `frameK` push. Three things make it go through, and each was measured:

1. **Generalise the machine-free scrutinees first.** `classifyFull md.params` occurs ~20 times
   in the body and mentions no machine; `generalize hfp : … = fp?` then `cases fp?` takes the
   proof from *a timeout at 40M heartbeats* to **40 seconds**. The keyword-collapse pair
   `appendKwHash m args kw`, rebound by an `if` whose branches each occur ~15 times, is
   generalised the same way (after `obtain ⟨args', m'⟩`, so the pair's projections do not
   re-expand).
2. **`frame_simp` must run at the top**, before those generalisations: without it the two
   sides' scrutinees are not syntactically equal, `split` peels the pushed and unpushed matches
   independently, and there are **457** goals instead of 32.
3. **Two keyed variants of the `setLocal` fold**, for the two shapes the phase-B walk is
   reached in — `foldSetLocal_mk_cons` for the flat literal (32 goals → 12) and
   `foldSetLocal_push` for the `pushK`-exposed one (12 → 0). The `_mk_cons` shape is the whole
   story of the shape problem: the activation push puts `.frameK fid` on the *front* of an
   already-appended kont, so the field reads `kk :: (k ++ K)` where `foldSetLocal_mk` wants
   `k ++ K` — one `List.cons_append` apart, and `rw` does not see it.
-/

/-- The `setLocal` fold at a machine already in pushed form. `foldSetLocal_mk`'s companion:
that one is keyed on a flat literal, this one on `pushK`. -/
theorem foldSetLocal_push (K : List Kont) (l : List (String × Value)) (m : Machine) :
    List.foldl (fun (m : Machine) (nv : String × Value) => m.setLocal nv.1 nv.2) (pushK K m) l =
      pushK K (List.foldl (fun (m : Machine) (nv : String × Value) => m.setLocal nv.1 nv.2) m l) :=
  foldMachine_frame K _ (fun m₂ nv => setLocal_frame K m₂ nv.1 nv.2) l m

/-- The `setLocal` fold at a literal whose kont is `kk :: (k ++ K)` — the activation frame's
`.frameK fid` consed onto the pushed continuation, which is how `enterUserMethod` reaches the
phase-B walk. One `List.cons_append` from `foldSetLocal_mk`, and that is exactly the distance
`rw` cannot cover on its own. -/
theorem foldSetLocal_mk_cons (K : List Kont) (kk : Kont) (c : Ctl) (k : List Kont)
    (st : List FrameId) (fr : Array Frame) (h : Heap) (g : List (String × Value))
    (out : String) (ce : Option Value) (pm : Bool) (l : List (String × Value)) :
    List.foldl (fun (m : Machine) (nv : String × Value) => m.setLocal nv.1 nv.2)
        ⟨c, kk :: (k ++ K), st, fr, h, g, out, ce, pm⟩ l =
      pushK K (List.foldl (fun (m : Machine) (nv : String × Value) => m.setLocal nv.1 nv.2)
        ⟨c, kk :: k, st, fr, h, g, out, ce, pm⟩ l) := by
  rw [← List.cons_append]
  exact foldSetLocal_mk K c (kk :: k) st fr h g out ce pm l

set_option maxHeartbeats 40000000 in
@[simp, frameLem] theorem enterUserMethod_frame (K : List Kont) (m : Machine) (recv : Value)
    (mname : String) (md : MethodDef) (args : List Value) (blk : Option Value)
    (kw : List (Value × Value)) :
    enterUserMethod (pushK K m) recv mname md args blk kw =
      frameR K (enterUserMethod m recv mname md args blk kw) := by
  rw [enterUserMethod.eq_def, enterUserMethod.eq_def]
  frame_simp
  generalize hfp : classifyFull md.params = fp?
  cases fp? with
  | none => rfl
  | some fp =>
    simp only [Option.isNone_some, Option.getD_some, Bool.false_eq_true, if_false, reduceIte]
    by_cases hkw : (!fp.keys.isEmpty || fp.kwrest?.isSome) = true
    · simp only [if_pos hkw]
      enter_arms K
      all_goals (try (rw [foldSetLocal_mk_cons K]))
      all_goals (try rfl)
      all_goals (try (rw [foldSetLocal_push K]))
      all_goals (try rfl)
    · simp only [if_neg hkw]
      generalize hak : appendKwHash m args kw = am
      obtain ⟨args', m'⟩ := am
      enter_arms K
      all_goals (try (rw [foldSetLocal_mk_cons K]))
      all_goals (try rfl)
      all_goals (try (rw [foldSetLocal_push K]))
      all_goals (try rfl)


/-! ### The `_mk_cons` idiom

Every function that pushes a continuation *and then calls another machine function* reaches
that callee at a literal whose kont is `kk :: (k ++ K)`, one `List.cons_append` from the
`k ++ K` a `pushK`-shaped lemma wants. The repair is one derived lemma per callee, proved by
`rw [← List.cons_append]` and the general lemma — mechanical, and cheaper than a global
re-folding `simp` lemma, which triggers the structure-eta blowup this file's header warns
about. -/

/-! ### The two general shape lemmas

Both are `rfl`, and both are *patterns* where a `pushK`-shaped lemma is not: the machine is a
literal whose `kont` field is syntactically `k ++ K`, and every other field is a metavariable
that matches whatever is there — including the projections of a bigger term that structure eta
has smeared across all nine fields, which is the shape `simp` leaves behind and the reason a
`pushK K ?m` lemma fails to fire. Between them they close most of what the arms of the pushing
functions reduce to. -/

/-- `withCtl` at an appended-kont literal. -/
theorem withCtl_mk (K : List Kont) (c₀ : Ctl) (c : Ctl) (k : List Kont) (st : List FrameId)
    (fr : Array Frame) (h : Heap) (g : List (String × Value)) (out : String)
    (ce : Option Value) (pm : Bool) :
    withCtl ⟨c, k ++ K, st, fr, h, g, out, ce, pm⟩ c₀ =
      pushK K (withCtl ⟨c, k, st, fr, h, g, out, ce, pm⟩ c₀) := rfl

/-- `withKont` at an appended-kont literal. -/
theorem withKont_mk (K : List Kont) (c₀ : Ctl) (kk : Kont) (c : Ctl) (k : List Kont)
    (st : List FrameId) (fr : Array Frame) (h : Heap) (g : List (String × Value))
    (out : String) (ce : Option Value) (pm : Bool) :
    withKont ⟨c, k ++ K, st, fr, h, g, out, ce, pm⟩ c₀ kk =
      pushK K (withKont ⟨c, k, st, fr, h, g, out, ce, pm⟩ c₀ kk) := rfl

/-- `enterUserMethod` at a consed-then-appended kont: `tryMixin` reaches it that way, under
its own `.includeK`. -/
theorem enterUserMethod_frame_mk_cons (K : List Kont) (kk : Kont) (c : Ctl) (k : List Kont)
    (st : List FrameId) (fr : Array Frame) (h : Heap) (g : List (String × Value))
    (out : String) (ce : Option Value) (pm : Bool) (recv : Value) (mname : String)
    (md : MethodDef) (args : List Value) (blk : Option Value) (kw : List (Value × Value)) :
    enterUserMethod ⟨c, kk :: (k ++ K), st, fr, h, g, out, ce, pm⟩ recv mname md args blk kw =
      frameR K (enterUserMethod ⟨c, kk :: k, st, fr, h, g, out, ce, pm⟩ recv mname md args
        blk kw) := by
  rw [← List.cons_append]
  exact enterUserMethod_frame K ⟨c, kk :: k, st, fr, h, g, out, ce, pm⟩ recv mname md args blk kw

/-- `callClosure` at a consed-then-appended kont: `iterStep` reaches it under its own
`.iterK`, and `Interp/Send.lean`'s yield paths reach it the same way. -/
theorem callClosure_frame_mk_cons (K : List Kont) (kk : Kont) (c : Ctl) (k : List Kont)
    (st : List FrameId) (fr : Array Frame) (h : Heap) (g : List (String × Value))
    (out : String) (ce : Option Value) (pm : Bool) (cl : Closure) (args : List Value)
    (brk : Option FrameId) (selfOv : Option Value) (defmodOv : Option ObjId) :
    callClosure ⟨c, kk :: (k ++ K), st, fr, h, g, out, ce, pm⟩ cl args brk selfOv defmodOv =
      frameR K (callClosure ⟨c, kk :: k, st, fr, h, g, out, ce, pm⟩ cl args brk selfOv
        defmodOv) := by
  rw [← List.cons_append]
  exact callClosure_frame K ⟨c, kk :: k, st, fr, h, g, out, ce, pm⟩ cl args brk selfOv defmodOv

/-! ### The native block iterators

`iterStep` is the loop driver and `startIter` its entry. Both push, and `iterStep`'s
zero-elements arm allocates (`.collect`), so this needs `allocArr_frame` and
`callClosure_frame` — the whole `Builtins` layer under it is already framed. -/

set_option maxHeartbeats 1000000 in
@[simp, frameLem] theorem iterStep_frame (K : List Kont) (m : Machine) (cl : Closure)
    (brk : FrameId) (rest : List (List Value)) (kind : IterKind) (acc : List Value)
    (retVal : Value) :
    iterStep (pushK K m) cl brk rest kind acc retVal =
      frameR K (iterStep m cl brk rest kind acc retVal) := by
  rw [iterStep.eq_def, iterStep.eq_def]
  frame_simp
  (repeat' first | rfl | split) <;> (try rfl)
    <;> (try (rw [callClosure_frame_mk_cons K]))
    <;> (try rfl)
    <;> (try (frame_simp; try rfl))

/-- `iterStep` at the shape `startIter` hands it: the iterator activation's `.frameK fid`
consed onto the pushed continuation. -/
theorem iterStep_frame_mk_cons (K : List Kont) (kk : Kont) (c : Ctl) (k : List Kont)
    (st : List FrameId) (fr : Array Frame) (h : Heap) (g : List (String × Value))
    (out : String) (ce : Option Value) (pm : Bool) (cl : Closure) (brk : FrameId)
    (rest : List (List Value)) (kind : IterKind) (acc : List Value) (retVal : Value) :
    iterStep ⟨c, kk :: (k ++ K), st, fr, h, g, out, ce, pm⟩ cl brk rest kind acc retVal =
      frameR K (iterStep ⟨c, kk :: k, st, fr, h, g, out, ce, pm⟩ cl brk rest kind acc
        retVal) := by
  rw [← List.cons_append]
  exact iterStep_frame K ⟨c, kk :: k, st, fr, h, g, out, ce, pm⟩ cl brk rest kind acc retVal

set_option maxHeartbeats 1000000 in
@[simp, frameLem] theorem startIter_frame (K : List Kont) (m : Machine) (recv : Value)
    (mname : String) (cl : Closure) (elemArgs : List (List Value)) (kind : IterKind)
    (initAcc : List Value) (retVal : Value) :
    startIter (pushK K m) recv mname cl elemArgs kind initAcc retVal =
      frameR K (startIter m recv mname cl elemArgs kind initAcc retVal) := by
  rw [startIter.eq_def, startIter.eq_def]
  -- the frame's `defmod`/`cref` read the heap and the current frame, both `pushK`-invariant
  simp only [pushK_heap, pushK_currentFrame, pushK_frames, pushK_stack]
  rw [iterStep_frame_mk_cons K]

set_option maxHeartbeats 1000000 in
@[simp, frameLem] theorem tryIterator_frame (K : List Kont) (m : Machine) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value) :
    tryIterator (pushK K m) recv mname args blk =
      (tryIterator m recv mname args blk).map (frameR K) := by
  rw [tryIterator.eq_def, tryIterator.eq_def]
  frame_simp
  -- the hash arm folds `allocArr` over the pairs to build the `[k, v]` element lists, so this
  -- needs `foldPair_frame`'s conditional `rw` (the side goal is the pointwise hypothesis)
  enter_arms K
  all_goals (try (rw [foldPair_frame K]))
  all_goals (try (frame_simp; try rfl))
  all_goals (try (intro p m₂ a; frame_simp; try rfl))

/-! ### `include`/`prepend`/`extend`

`mixinDefines` reads only the heap. `tryMixin` writes a class payload and, on an `included`
hook, enters a user method under an `.includeK` — the `_mk_cons` shape. -/

@[simp, frameLem] theorem mixinDefines_frame (K : List Kont) (m : Machine) (cls : ObjId)
    (name : String) :
    mixinDefines (pushK K m) cls name = mixinDefines m cls name := by
  simp only [mixinDefines, pushK_heap]

set_option maxHeartbeats 1000000 in
@[simp, frameLem] theorem tryMixin_frame (K : List Kont) (m : Machine) (recv : Value)
    (mname : String) (args : List Value) :
    tryMixin (pushK K m) recv mname args = (tryMixin m recv mname args).map (frameR K) := by
  rw [tryMixin.eq_def, tryMixin.eq_def]
  frame_simp
  -- `moduleHook` reads only the heap, so rather than a `_mk` variant keyed on the
  -- payload-updated literal it is cheaper to unfold it: the literal's `.heap` projection
  -- reduces, and the two sides' scrutinees become equal before `split` runs.
  simp only [moduleHook]
  (repeat' first | rfl | split)
  all_goals (try rfl)
  all_goals (try (rw [enterUserMethod_frame_mk_cons K]))
  all_goals (try rfl)
  all_goals (try (rw [withCtl_mk K]))
  all_goals (try rfl)
  all_goals (try (simp only [Option.map_some, Option.map_none]; try rfl))
  all_goals (try (frame_simp; try rfl))
  -- the last arm is `none = some …`: `split` peeled the two sides' `classPayload?` matches
  -- against *structure-eta-expanded* copies of `m` and so paired a `none` arm with a `some`
  -- one. The hypotheses are contradictory up to that eta, which is what `simp_all` sees and
  -- a syntactic rewrite cannot (a lemma collapsing `⟨m.ctl, m.kont, …⟩` to `m` has a
  -- projection-of-metavariable on the left, so it is not a pattern).
  all_goals (try (simp_all (maxSteps := 200000) [frameLem]))

#print axioms enterClassBody_frame
#print axioms enterScopedClassBody_frame
#print axioms enterUserMethod_frame
#print axioms iterStep_frame
#print axioms startIter_frame
#print axioms tryIterator_frame
#print axioms tryMixin_frame

end Proof
end RubyCore
