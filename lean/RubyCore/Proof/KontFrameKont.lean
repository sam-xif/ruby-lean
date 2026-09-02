import RubyCore.Proof.KontFrameSend

/-!
# `RubyCore/Proof/KontFrameKont.lean` — the continuation appliers, framed

`applyKont` and `unwind` are the two functions whose framing lemma is **conditional on the
continuation being non-empty**, and that is not a technicality: both branch on `m.kont`
itself, and their empty-continuation arms are the ones that *end the program* —
`applyKont [] v = .done v m`, `unwind [] (.raiseJ exc) = .uncaught exc m`. Pushing `K` onto an
empty continuation turns "the program is over" into "keep going in `K`", which is exactly what
the run-level decomposition wants to happen and exactly why it cannot be an equation between
one-step results.

So: `m.kont ≠ []` here, and `CatchFree K` inherited from below.
-/

set_option autoImplicit false
set_option maxRecDepth 400000

namespace RubyCore
namespace Proof

open Builtins
open Interp

/-! ### `nextClause`, and the `_mk` one-liners

`nextClause` (the rescue-clause walk, `Interp/Support.lean`) is the one function in the layers
below that had no framing lemma — nothing under `Dispatch` calls it, only `applyKont` and
`unwind` do.

The rest of this section is the `_mk` idiom at its cheapest. `pushK K ⟨c, k, …⟩` is
*definitionally* `⟨c, k ++ K, …⟩`, so each of these is the general lemma applied at a literal
machine and nothing more — but stating it that way turns the left-hand side into a **pattern**
`rw` can match, which `pushK K ?m` is not once the continuation pop has left a nine-field
literal behind. -/

@[simp, frameLem] theorem nextClause_frame (K : List Kont) (m : Machine) (node : BeginNode)
    (exc : Value)
    (clauses : List (List Expr × Option (TargetKind × String) × Expr)) :
    nextClause (pushK K m) node exc clauses = pushK K (nextClause m node exc clauses) := by
  induction clauses with
  | nil => rw [nextClause.eq_def, nextClause.eq_def]; frame_simp
  | cons cl rest ih =>
    rw [nextClause.eq_def, nextClause.eq_def]
    frame_simp
    (repeat' first
      | rfl
      | (frame_simp; done)
      | simp only [frameLem]
      | dsimp only
      | (rw [ih]; try rfl)
      | split)
    frame_close K

theorem nextClause_frame_mk (K : List Kont) (c : Ctl) (k : List Kont) (st : List FrameId)
    (fr : Array Frame) (h : Heap) (g : List (String × Value)) (out : String)
    (ce : Option Value) (pm : Bool) (node : BeginNode) (exc : Value)
    (clauses : List (List Expr × Option (TargetKind × String) × Expr)) :
    nextClause ⟨c, k ++ K, st, fr, h, g, out, ce, pm⟩ node exc clauses =
      pushK K (nextClause ⟨c, k, st, fr, h, g, out, ce, pm⟩ node exc clauses) :=
  nextClause_frame K ⟨c, k, st, fr, h, g, out, ce, pm⟩ node exc clauses

/-- The combinator that fixes the four `*splat` arms: `generalize` the shared `spreadA` call
and `cases` its result, so both sides' matches reduce at once, with the continuation's own
framing supplied pointwise. -/
theorem withSpread_frame (K : List Kont) (m : Machine) (v : Value)
    (k : Machine → List Value → StepResult)
    (hk : ∀ (m₂ : Machine) (vs : List Value), k (pushK K m₂) vs = frameR K (k m₂ vs)) :
    withSpread (pushK K m) v k = frameR K (withSpread m v k) := by
  rw [withSpread.eq_def, withSpread.eq_def, spreadA_frame K]
  generalize spreadA m v = r
  cases r with
  | error e => rfl
  | ok p => obtain ⟨vs, m₂⟩ := p; exact hk m₂ vs

theorem spreadA_frame_mk (K : List Kont) (c : Ctl) (k : List Kont) (st : List FrameId)
    (fr : Array Frame) (h : Heap) (g : List (String × Value)) (out : String)
    (ce : Option Value) (pm : Bool) (v : Value) :
    spreadA ⟨c, k ++ K, st, fr, h, g, out, ce, pm⟩ v =
      (spreadA ⟨c, k, st, fr, h, g, out, ce, pm⟩ v).map
        (fun p => (p.1, pushK K p.2)) :=
  spreadA_frame K ⟨c, k, st, fr, h, g, out, ce, pm⟩ v

theorem startArgs_frame_mk (K : List Kont) (hK : CatchFree K) (c : Ctl) (k : List Kont)
    (st : List FrameId) (fr : Array Frame) (h : Heap) (g : List (String × Value))
    (out : String) (ce : Option Value) (pm : Bool) (recv : Value) (implicit : SendSite)
    (mname : String) (acc : List Value) (rest : List Expr) (pblk : PendingBlk) :
    startArgs ⟨c, k ++ K, st, fr, h, g, out, ce, pm⟩ recv implicit mname acc rest pblk =
      frameR K (startArgs ⟨c, k, st, fr, h, g, out, ce, pm⟩ recv implicit mname acc rest pblk) :=
  startArgs_frame K hK ⟨c, k, st, fr, h, g, out, ce, pm⟩ recv implicit mname acc rest pblk

theorem startSuperArgs_frame_mk (K : List Kont) (hK : CatchFree K) (c : Ctl) (k : List Kont)
    (st : List FrameId) (fr : Array Frame) (h : Heap) (g : List (String × Value))
    (out : String) (ce : Option Value) (pm : Bool) (acc : List Value) (rest : List Expr)
    (blk : Option Value) :
    startSuperArgs ⟨c, k ++ K, st, fr, h, g, out, ce, pm⟩ acc rest blk =
      frameR K (startSuperArgs ⟨c, k, st, fr, h, g, out, ce, pm⟩ acc rest blk) :=
  startSuperArgs_frame K hK ⟨c, k, st, fr, h, g, out, ce, pm⟩ acc rest blk

theorem startYield_frame_mk (K : List Kont) (c : Ctl) (k : List Kont) (st : List FrameId)
    (fr : Array Frame) (h : Heap) (g : List (String × Value)) (out : String)
    (ce : Option Value) (pm : Bool) (acc : List Value) (rest : List Expr) :
    startYield ⟨c, k ++ K, st, fr, h, g, out, ce, pm⟩ acc rest =
      frameR K (startYield ⟨c, k, st, fr, h, g, out, ce, pm⟩ acc rest) :=
  startYield_frame K ⟨c, k, st, fr, h, g, out, ce, pm⟩ acc rest

theorem continueArray_frame_mk (K : List Kont) (c : Ctl) (k : List Kont) (st : List FrameId)
    (fr : Array Frame) (h : Heap) (g : List (String × Value)) (out : String)
    (ce : Option Value) (pm : Bool) (acc : List Value) (rest : List Expr) :
    continueArray ⟨c, k ++ K, st, fr, h, g, out, ce, pm⟩ acc rest =
      frameR K (continueArray ⟨c, k, st, fr, h, g, out, ce, pm⟩ acc rest) :=
  continueArray_frame K ⟨c, k, st, fr, h, g, out, ce, pm⟩ acc rest

theorem invoke_frame_mk (K : List Kont) (hK : CatchFree K) (c : Ctl) (k : List Kont)
    (st : List FrameId) (fr : Array Frame) (h : Heap) (g : List (String × Value))
    (out : String) (ce : Option Value) (pm : Bool) (recv : Value) (implicit : SendSite)
    (mname : String) (args : List Value) (blk : Option Value) (kw : List (Value × Value)) :
    invoke ⟨c, k ++ K, st, fr, h, g, out, ce, pm⟩ recv implicit mname args blk kw =
      frameR K (invoke ⟨c, k, st, fr, h, g, out, ce, pm⟩ recv implicit mname args blk kw) :=
  invoke_frame K hK ⟨c, k, st, fr, h, g, out, ce, pm⟩ recv implicit mname args blk kw

/-! ### `Except.mapError`, in the framing set

`cpathContainer` returns `Except StepResult ObjId`, and its framing lemma carries the machine
out through `Except.mapError (frameR K)`. Core's reduction lemmas for that are `simp` lemmas
but not `frameLem` ones, so `simp only [frameLem]` — which is what the walker runs — left
`Except.mapError (frameR K) (.error sr) = .error sr'` sitting in a hypothesis. -/

@[simp, frameLem] theorem mapError_error {α β ε ε' : Type} (f : ε → ε') (x : ε) :
    (Except.error x : Except ε α).mapError f = Except.error (f x) := rfl

@[simp, frameLem] theorem exceptMap_ok {α β ε : Type} (f : α → β) (a : α) :
    (Except.ok a : Except ε α).map f = Except.ok (f a) := rfl

@[simp, frameLem] theorem exceptMap_error {α β ε : Type} (f : α → β) (x : ε) :
    (Except.error x : Except ε α).map f = Except.error x := rfl

@[simp, frameLem] theorem mapError_ok {α ε ε' : Type} (f : ε → ε') (a : α) :
    (Except.ok a : Except ε α).mapError f = Except.ok a := rfl

/-- The walker for this file: `send_walk` plus explicit rewrites for the conditional lemmas of
the send layer, which the continuation arms reach directly. -/
syntax "kont_walk" ident ident : tactic
macro_rules
  | `(tactic| kont_walk $K $hK) =>
    `(tactic| repeat' first
        | rfl
        | (frame_simp; done)
        | simp only [frameLem]
        | dsimp only
        -- `rw`, not `simp only`: as a simp lemma `mk_push` ping-pongs against the framing
        -- set (it re-folds a literal into `pushK`, a `frameLem` lemma unfolds it back) and
        -- `repeat'` never terminates. One rewrite per goal is what is wanted anyway.
        | (rw [mk_push $K]; try rfl)
        | (rw [startArgs_frame $K $hK]; try rfl)
        | (rw [startArgs_frame_mk $K $hK]; try rfl)
        | (rw [startSuperArgs_frame_mk $K $hK]; try rfl)
        | (rw [startYield_frame_mk $K]; try rfl)
        | (rw [continueArray_frame_mk $K]; try rfl)
        | (rw [invoke_frame_mk $K $hK]; try rfl)
        | (rw [nextClause_frame_mk $K]; try rfl)
        | (rw [spreadA_frame_mk $K]; try rfl)
        | refine withSpread_frame $K _ _ _ (fun m₂ vs => ?_)
        | (rw [startKwargs_frame $K $hK]; try rfl)
        | (rw [startSuperArgs_frame $K $hK]; try rfl)
        | (rw [finishSend_frame $K $hK]; try rfl)
        | (rw [doSuper_frame $K $hK]; try rfl)
        | (rw [invoke_frame $K $hK]; try rfl)
        | (rw [invokeDispatch_frame $K $hK]; try rfl)
        | (rw [dispatchMiss_frame $K $hK]; try rfl)
        | (rw [tryReflect_frame $K $hK]; try rfl)
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

/-- Walk, close, repeat — `send_prove`'s shape with this file's walker. -/
syntax "kont_prove" ident ident : tactic
macro_rules
  | `(tactic| kont_prove $K $hK) =>
    `(tactic| (frame_simp
               iterate 3 (try (kont_walk $K $hK)
                          try (frame_close $K))
               -- the reverse-rewrite closer, for the conditional lemmas: `frame_close` has it
               -- for the wrappers (`withCtl`/`withKont`/`raiseErr`) but cannot know about the
               -- ones carrying `CatchFree K`
               all_goals (try (rw [← invoke_frame $K $hK]
                               simp_all (maxSteps := 200000) [frameLem]))
               all_goals (try (rw [← startArgs_frame $K $hK]
                               simp_all (maxSteps := 200000) [frameLem]))))

@[simp, frameLem] theorem undefAliasMiss_frame (K : List Kont) (m : Machine) (name : String) :
    undefAliasMiss (pushK K m) name = frameR K (undefAliasMiss m name) := by
  rw [undefAliasMiss.eq_def, undefAliasMiss.eq_def]
  frame_simp
  (repeat' first | rfl | (frame_simp; done) | simp only [frameLem] | dsimp only | split)
  frame_close K

@[simp, frameLem] theorem undefNames_frame (K : List Kont) (m : Machine) (defmod : ObjId) :
    ∀ (l : List String), undefNames (pushK K m) defmod l = frameR K (undefNames m defmod l) := by
  intro l
  induction l generalizing m with
  | nil => rw [undefNames.eq_def, undefNames.eq_def]; rfl
  | cons a rest ih =>
    rw [undefNames.eq_def, undefNames.eq_def]
    frame_simp
    -- the recursion is on a *heap-updated* machine, so the induction hypothesis is general in
    -- it — and `mk_push` is what turns the literal simp leaves behind back into `pushK`-shape
    -- so that hypothesis applies
    (repeat' first
      | rfl
      | (frame_simp; done)
      | simp only [frameLem]
      | dsimp only
      | (rw [mk_push K]; try rw [ih]; try rfl)
      | (rw [ih]; try rfl)
      | split)
    frame_close K

set_option maxHeartbeats 8000000 in
theorem applyKont_frame (K : List Kont) (hK : CatchFree K) (m : Machine) (v : Value)
    (h : m.kont ≠ []) :
    applyKont (pushK K m) v = frameR K (applyKont m v) := by
  rw [applyKont.eq_def, applyKont.eq_def]
  cases hk : m.kont with
  | nil => exact absurd hk h
  | cons k rest =>
    -- Pop the head, then **case on which continuation frame it is**: the same move that made
    -- `tryReflect` tractable, for the same reason — thirty small arms instead of one goal the
    -- size of the file. `mk_push` re-folds the machine the pop leaves behind
    -- (`⟨m.ctl, rest ++ K, …⟩`) into `pushK`-shape so the framing set can see it.
    simp only [pushK_kont, hk, List.cons_append]
    cases k <;> simp only [mk_push K] <;> kont_prove K hK

set_option maxHeartbeats 8000000 in
theorem unwind_frame (K : List Kont) (hK : CatchFree K) (m : Machine) (j : Jump)
    (h : m.kont ≠ []) :
    unwind (pushK K m) j = frameR K (unwind m j) := by
  rw [unwind.eq_def, unwind.eq_def]
  cases hk : m.kont with
  | nil => exact absurd hk h
  | cons k rest =>
    simp only [pushK_kont, hk, List.cons_append]
    cases k <;> simp only [mk_push K] <;> kont_prove K hK

#print axioms unwind_frame
#print axioms undefNames_frame
#print axioms applyKont_frame

end Proof
end RubyCore
