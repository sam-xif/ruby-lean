import Denote.Sem.Locals

/-!
# `Denote/Sem/FrameLocal.lean` — the layer's grind, bottom-up

`Denote/Sem/Locals.lean` proves what a *write* can reach. This file proves what the interpreter
*does*, layer by layer, in `RubyCore/Proof/KontFrame*.lean`'s order and for the same reason:
`Builtins` first (it threads the machine and is the widest), then `Interp`'s helpers, then the
step function.

## The claim, and why it is about `locals` rather than `frames`

The first attempt was "`Builtins.run` never touches `frames`", which is what a grep suggests —
no file under `RubyCore/Builtins/` mentions `frames` or `stack` at all. It is **false**, and the
counterexample is one arm: a builtin that sets the current frame's `matchXparent` flag through
`Machine.setCurrentFrame`, which is a `frames.set!`. The flag is not a local, so the honest
claim is the one the layer actually needs:

```
LocalsSame m m'  :=  m'.stack = m.stack  ∧  ∀ f, (m'.frames.getD f default).locals = …
```

That is also the claim `getLocal_congr` consumes, so nothing is lost by weakening to it.

## What is proved

The whole `Builtins` layer: `builtins_run_locals`, and the six per-class dispatchers under it.
Six hundred-odd arms, closed by one tactic whose entire content is a list of twenty
machine-threading helpers to unfold — plus five hand-written proofs where that was not enough
(`Regex`'s fold-carrying helpers, and `newImpl`, for the reason in §What is not here yet).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Ratchet.Denote

open RubyCore

/-- **Every frame's locals, and the stack, are where they were.** -/
def LocalsSame (m m' : Machine) : Prop :=
  m'.stack = m.stack ∧
  ∀ f, (m'.frames.getD f default).locals = (m.frames.getD f default).locals

theorem LocalsSame.refl (m : Machine) : LocalsSame m m := ⟨rfl, fun _ => rfl⟩

theorem LocalsSame.trans {a b c : Machine} (h₁ : LocalsSame a b) (h₂ : LocalsSame b c) :
    LocalsSame a c :=
  ⟨by rw [h₂.1, h₁.1], fun f => by rw [h₂.2 f, h₁.2 f]⟩

/-- A machine that differs only in the heap (or in any field other than `frames`/`stack`). -/
theorem LocalsSame.of_eq {m m' : Machine} (hs : m'.stack = m.stack)
    (hf : m'.frames = m.frames) : LocalsSame m m' :=
  ⟨hs, fun f => by rw [hf]⟩

/-- **`setCurrentFrame` keeps the locals it was handed.** The one shape in the `Builtins` layer
that writes `frames` at all: a flag on the current frame, with `locals` copied. -/
theorem LocalsSame.setCurrentFrame {m : Machine} {fr : RubyCore.Frame}
    (h : fr.locals = m.currentFrame.locals) : LocalsSame m (m.setCurrentFrame fr) := by
  unfold Machine.setCurrentFrame
  cases hs : m.stack with
  | nil => simp only [hs]; exact LocalsSame.refl m
  | cons fid rest =>
    simp only [hs]
    refine ⟨hs.symm, fun f => ?_⟩
    show ((m.frames.set! fid fr).getD f default).locals = _
    by_cases hf : f = fid
    · subst hf
      by_cases hlt : f < m.frames.size
      · rw [getD_set!_self m.frames f fr hlt, h]
        simp only [Machine.currentFrame, hs]
      · -- out of bounds `set!` is the identity, and both reads answer `default`
        rw [getD_set!_oob m.frames f fr hlt]
    · rw [getD_set!_ne m.frames fid f fr hf]

#print axioms LocalsSame.setCurrentFrame


/-! ### The machine-threading helpers

Every `Builtins` helper that hands a machine back. Most are `LocalsSame` because they build the
result with a record update on `heap` or `out`; `putsGo` is the one with a fold in it, and it
gets the `foldlM` induction `RubyCore/Proof/KontFrame.lean`'s `foldPair_frame` would have. -/

theorem emit_locals (m : Machine) (s : String) : LocalsSame m (m.emit s) :=
  LocalsSame.of_eq rfl rfl

theorem allocArr_locals (m : Machine) (xs : Array Value) :
    LocalsSame m (Builtins.allocArr m xs).2 := LocalsSame.of_eq rfl rfl

theorem allocHsh_locals (m : Machine) (xs : Array (Value × Value)) :
    LocalsSame m (Builtins.allocHsh m xs).2 := LocalsSame.of_eq rfl rfl

theorem allocExc_locals (m : Machine) (cls : ObjId) (msg : String) :
    LocalsSame m (Builtins.allocExc m cls msg).2 := LocalsSame.of_eq rfl rfl

/-- **A fold whose every step keeps the locals keeps them.** The shape
`RubyCore/Proof/KontFrame.lean`'s `foldPair_frame` has, in `Option` rather than in the framing
equation, and stated over an arbitrary step so the caller can `split` the step's own match. -/
theorem foldlM_locals {α : Type} (f : Machine → α → Option Machine)
    (hf : ∀ m a m', f m a = some m' → LocalsSame m m') :
    ∀ (l : List α) (m m' : Machine), l.foldlM f m = some m' → LocalsSame m m'
  | [], m, m', h => by
    simp only [List.foldlM_nil] at h
    injection h with h
    exact h ▸ LocalsSame.refl m
  | a :: rest, m, m', h => by
    rw [List.foldlM_cons] at h
    cases hstep : f m a with
    | none => rw [hstep] at h; exact absurd h (by simp)
    | some m₁ =>
      rw [hstep] at h
      exact (hf m a m₁ hstep).trans (foldlM_locals f hf rest m₁ m' h)

theorem putsGo_locals : ∀ (fuel : Nat) (m : Machine) (args : List Value) (m₂ : Machine),
    Builtins.putsGo m args fuel = some m₂ → LocalsSame m m₂ := by
  intro fuel
  induction fuel with
  | zero => intro m args m₂ h; simp [Builtins.putsGo] at h
  | succ n ih =>
    intro m args m₂ h
    rw [Builtins.putsGo] at h
    refine foldlM_locals _ ?_ args m m₂ h
    intro m' a m'' hstep
    repeat (any_goals (first
      | (cases hstep; exact emit_locals _ _)
      | (obtain ⟨-, rfl⟩ := hstep; exact emit_locals _ _)
      | (simp at hstep)
      | (exact ih m' _ m'' hstep)
      | split at hstep))

theorem putsImpl_locals (m : Machine) (args : List Value) :
    ∀ v m', Builtins.putsImpl m args = .ok v m' → LocalsSame m m' := by
  intro v m' h
  rw [Builtins.putsImpl] at h
  cases hg : Builtins.putsGo m args 100 with
  | none => rw [hg] at h; exact absurd h (by simp)
  | some m₁ =>
    rw [hg] at h
    simp only [BRes.ok.injEq] at h
    exact (putsGo_locals 100 m args m₁ hg).trans (h.2 ▸ LocalsSame.of_eq rfl rfl)


/-- `Object#print`'s fold: one `toSP` per argument, emitting. -/
theorem printFold_locals : ∀ (args : List Value) (m m₂ : Machine),
    args.foldlM (fun m a => match Builtins.toSP m a with
      | .ok s => some (m.emit s)
      | .error _ => none) m = some m₂ → LocalsSame m m₂ := by
  refine foldlM_locals _ (fun m a m' hs => ?_)
  split at hs
  · cases hs; exact emit_locals _ _
  · exact absurd hs (by simp)

/-- `Object#p`'s own `let rec`, which is the same walk written as a recursion. -/
theorem pGo_locals : ∀ (m : Machine) (args : List Value) (m₂ : Machine),
    Builtins.runObjects.go m args = some m₂ → LocalsSame m m₂
  | m, [], m₂, h => by
    rw [Builtins.runObjects.go] at h
    injection h with h
    exact h ▸ LocalsSame.refl m
  | m, a :: rest, m₂, h => by
    rw [Builtins.runObjects.go] at h
    split at h
    · exact (emit_locals _ _).trans (pGo_locals _ rest m₂ h)
    · exact absurd h (by simp)


/-! ### The rest of the `Builtins` helpers

The list is what the automation asked for, and it is short: the arms it could not close on its
own are exactly the ones that thread the machine through a named helper. Most are one line —
the helper builds its answer with a record update on `heap` or `out`. Three are not: the two
frame writers (`setCurrentFrame` above, `setLastMatchValue` here, both keeping `locals`), and
`Regex`'s five, which allocate inside folds. -/

theorem allocStr_locals (m : Machine) (s : String) :
    LocalsSame m (Builtins.allocStr m s).2 := LocalsSame.of_eq rfl rfl

theorem allocStrEnc_locals (m : Machine) (s : String) (b : Bool) :
    LocalsSame m (Builtins.allocStrEnc m s b).2 := LocalsSame.of_eq rfl rfl

/-- `$~`'s write: the frame's `lastMatch`, with `locals` copied. -/
theorem setLastMatchValue_locals (m : Machine) (v : Value) :
    LocalsSame m (m.setLastMatchValue v) := by
  unfold Machine.setLastMatchValue
  by_cases hlt : m.matchFrameId < m.frames.size
  · rw [if_pos hlt]
    refine ⟨rfl, fun f => ?_⟩
    show ((m.frames.set! m.matchFrameId _).getD f default).locals = _
    by_cases hf : f = m.matchFrameId
    · rw [hf, getD_set!_self m.frames m.matchFrameId _ hlt]
    · rw [getD_set!_ne m.frames m.matchFrameId f _ hf]
  · rw [if_neg hlt]; exact LocalsSame.refl m

theorem setMatchGlobals_locals (m : Machine) (md : Option Value) :
    LocalsSame m (Builtins.setMatchGlobals m md) := setLastMatchValue_locals _ _


#print axioms putsImpl_locals
#print axioms setLastMatchValue_locals

/-! ### `Regex`'s five, and the fold they share

The last of the `Builtins` layer, and the only helpers that allocate *inside a fold*. The shape
is `RubyCore/Proof/KontFrame.lean`'s `foldPair_frame`: a `List.foldl` over a pair whose second
component is the machine. One lemma covers all of them, stated over an arbitrary step so each
caller can `split` its own match. -/

theorem foldPair_locals {α β : Type} (f : β × Machine → α → β × Machine)
    (hf : ∀ p a, LocalsSame (p : β × Machine).2 (f p a).2) :
    ∀ (l : List α) (p : β × Machine), LocalsSame p.2 (l.foldl f p).2
  | [], p => LocalsSame.refl p.2
  | a :: rest, p => by
    rw [List.foldl_cons]
    exact (hf p a).trans (foldPair_locals f hf rest (f p a))

theorem foldPairArray_locals {α β : Type} (f : β × Machine → α → β × Machine)
    (hf : ∀ p a, LocalsSame (p : β × Machine).2 (f p a).2) (l : Array α) (p : β × Machine) :
    LocalsSame p.2 (l.foldl f p).2 := by
  rw [← Array.foldl_toList]
  exact foldPair_locals f hf _ p

theorem allocMData_locals (m : Machine) (s : String)
    (caps : Array (Option (Nat × Nat))) (names : List (String × Nat)) (bin : Bool) :
    LocalsSame m (Builtins.allocMData m s caps names bin).2 := LocalsSame.of_eq rfl rfl

theorem setLastMatch_locals (m : Machine) (s src : String) (opts : Nat)
    (hits : List (Nat × Nat × Array (Option (Nat × Nat)))) (bin : Bool) :
    LocalsSame m (Builtins.setLastMatch m s src opts hits bin) := by
  unfold Builtins.setLastMatch
  split
  · exact setMatchGlobals_locals _ _
  · exact (allocMData_locals _ _ _ _ _).trans (setMatchGlobals_locals _ _)

#print axioms setLastMatch_locals
#print axioms foldPair_locals


/-! ### `Regex`'s five

Each one is: split the `allMatches` result, then chain `setLastMatch` (where it happens) with
the fold and the allocation. The step's own `match`/`if` is split *inside* `foldPair_locals`'s
hypothesis, which is why the hypothesis is stated pointwise rather than as an equation. -/

theorem regexApply_locals (bid : String) (m : Machine) (re subj : Value) :
    ∀ v m', Builtins.runRegex.regexApply bid m re subj = .ok v m' → LocalsSame m m' := by
  intro v m' h
  unfold Builtins.runRegex.regexApply at h
  repeat (any_goals (first
    | (cases h; exact LocalsSame.refl _)
    | (cases h; exact setMatchGlobals_locals _ _)
    | (cases h; exact (allocMData_locals _ _ _ _ _).trans (setMatchGlobals_locals _ _))
    | (simp at h)
    | (unfold Builtins.runRegex.applyTo at h)
    | split at h))

theorem scanAll_locals (m : Machine) (s src : String) (opts : Nat) (bin : Bool) :
    ∀ v m', Builtins.runRegex.scanAll m s src opts bin = .ok v m' → LocalsSame m m' := by
  intro v m' h
  unfold Builtins.runRegex.scanAll at h
  split at h
  · exact absurd h (by simp)
  · dsimp only at h
    cases h
    refine (setLastMatch_locals _ _ _ _ _ _).trans
      (LocalsSame.trans (foldPair_locals _ ?_ _ _) (allocArr_locals _ _))
    intro p a
    split
    · exact allocStrEnc_locals _ _ _
    · refine LocalsSame.trans (foldPair_locals _ ?_ _ (#[], p.snd)) (allocArr_locals _ _)
      intro q b
      split
      · exact allocStrEnc_locals _ _ _
      · exact LocalsSame.refl _

theorem splitBy_locals (m : Machine) (s src : String) (opts : Nat) (lim : Int) (bin : Bool) :
    ∀ v m', Builtins.runRegex.splitBy m s src opts lim bin = .ok v m' → LocalsSame m m' := by
  intro v m' h
  unfold Builtins.runRegex.splitBy at h
  split at h
  · dsimp only at h
    cases h
    exact allocArr_locals _ _
  · split at h
    · exact absurd h (by simp)
    · dsimp only at h
      cases h
      refine LocalsSame.trans (foldPair_locals _ ?_ _ _) (allocArr_locals _ _)
      intro p a
      exact allocStrEnc_locals _ _ _

theorem splitOn_locals (m : Machine) (hp : Heap) (s : String) (pat : Value) (lim : Int)
    (bin : Bool) :
    ∀ v m', Builtins.runRegex.splitOn m hp s pat lim bin = .ok v m' → LocalsSame m m' := by
  intro v m' h
  unfold Builtins.runRegex.splitOn at h
  repeat (any_goals (first
    | (exact splitBy_locals _ _ _ _ _ _ _ _ h)
    | (simp at h)
    | split at h))

theorem subst_locals (m : Machine) (s src : String) (opts : Nat) (rep : String)
    (global : Bool) (recvV repV : Value) :
    ∀ v m', Builtins.runRegex.subst m s src opts rep global recvV repV = .ok v m' →
      LocalsSame m m' := by
  intro v m' h
  unfold Builtins.runRegex.subst at h
  split at h
  · exact absurd h (by simp)
  · dsimp only at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · dsimp only [Builtins.okStrEnc, Builtins.allocStrEnc] at h
        cases h
        exact (setLastMatch_locals _ _ _ _ _ _).trans (LocalsSame.of_eq rfl rfl)



/-- **`Class#new`'s allocator**, and the one helper that needs its splits *ordered*.

`split at h` picks a scrutinee it finds anywhere in the hypothesis, and `newImpl`'s body has a
`match Builtins.toSP m msgV with` under a `match args with | [msgV] => …` — so left to itself
the tactic reaches for a scrutinee whose binder is not in scope yet and fails, with the outer
`if` still standing. Naming the payload and peeling the `if`s by hand fixes the order; the arms
themselves are the same automation. -/
theorem newImpl_locals (m : Machine) (recv : Value) (args : List Value) :
    ∀ v m', Builtins.newImpl m recv args = .ok v m' → LocalsSame m m' := by
  intro v m' h
  unfold Builtins.newImpl at h
  split at h
  · rename_i o
    split at h
    · exact absurd h (by simp)
    · rename_i c hc
      by_cases hmod : c.isModule = true
      · rw [if_pos hmod] at h; exact absurd h (by simp)
      · rw [if_neg hmod] at h
        by_cases hexc : (ancestors m.heap o).contains Boot.exceptionId = true
        · rw [if_pos hexc] at h
          repeat (any_goals (first
            | (cases h; exact LocalsSame.of_eq rfl rfl)
            | (simp at h)
            | split at h))
        · rw [if_neg hexc] at h
          by_cases hstr : (ancestors m.heap o).contains Boot.stringId = true
          · rw [if_pos hstr] at h
            repeat (any_goals (first
              | (cases h; exact LocalsSame.of_eq rfl rfl)
              | (simp at h)
              | split at h))
          · rw [if_neg hstr] at h
            repeat (any_goals (first
              | (cases h; exact LocalsSame.of_eq rfl rfl)
              | (simp at h)
              | split at h))
  · exact absurd h (by simp)

/-! ## The seven dispatchers

`Builtins.run` chains six per-class rule files, each handing what it does not recognise to the
next (`RubyCore/Proof/KontFrame.lean` §The dispatcher chain), so they are proved in reverse and
each one's fall-through is a lemma already in the set.

One tactic closes all of them. Reduce the dispatcher's own equation, then repeatedly: close a
leaf where the machine came back unchanged (`cases h`), or where the arm answered something that
is not `.ok` (`simp at h`), or split the arm's next scrutinee, or unfold the machine-threading
helper the arm went through. The helper list is the whole content of the tactic and it is
short — twenty names for six hundred arms. -/

/-! The closer refers to the hypothesis by the fixed name `h`, which is why hygiene is off: the
alternative is threading the name through an antiquotation of the right syntax kind for each of
`cases`/`simp at`/`split at`/`unfold at`, four different kinds. -/

set_option hygiene false in
macro "builtin_arms" : tactic => `(tactic|
  repeat (any_goals (first
    | (cases h; exact LocalsSame.refl _)
    | (obtain ⟨-, rfl⟩ := h; exact LocalsSame.setCurrentFrame rfl)
    | (obtain ⟨-, rfl⟩ := h; exact LocalsSame.refl _)
    | (obtain ⟨-, rfl⟩ := h; exact setMatchGlobals_locals _ _)
    | (obtain ⟨-, rfl⟩ := h; first
        | (exact printFold_locals _ _ _ (by assumption))
        | (exact pGo_locals _ _ _ (by assumption))
        | (exact (pGo_locals _ _ _ (by assumption)).trans (allocArr_locals _ _))
        | (exact (printFold_locals _ _ _ (by assumption)).trans (allocArr_locals _ _)))
    | (exact putsImpl_locals _ _ _ _ h)
    | (exact regexApply_locals _ _ _ _ _ _ h)
    | (exact scanAll_locals _ _ _ _ _ _ _ h)
    | (exact splitBy_locals _ _ _ _ _ _ _ _ h)
    | (exact splitOn_locals _ _ _ _ _ _ _ _ h)
    | (exact subst_locals _ _ _ _ _ _ _ _ _ _ h)
    | (exact (setMatchGlobals_locals _ _).trans (splitOn_locals _ _ _ _ _ _ _ _ h))
    | (exact (setMatchGlobals_locals _ _).trans (splitBy_locals _ _ _ _ _ _ _ _ h))
    | (exact ((allocMData_locals _ _ _ _ _).trans (setMatchGlobals_locals _ _)).trans
        (runRegex_locals _ _ _ _ _ _ h))
    | (obtain ⟨-, rfl⟩ := h; exact ((allocMData_locals _ _ _ _ _).trans
        (setMatchGlobals_locals _ _)).trans (runRegex_locals _ _ _ _ _ _ (by assumption)))
    | (obtain ⟨-, rfl⟩ := h; first
        | (exact LocalsSame.of_eq rfl rfl)
        | (refine LocalsSame.trans (foldPair_locals _ ?_ _ _) (LocalsSame.of_eq rfl rfl)
           intro p a
           repeat (any_goals (first
             | exact LocalsSame.refl _
             | exact LocalsSame.of_eq rfl rfl
             | split)))
        | (refine LocalsSame.trans (foldPairArray_locals _ ?_ _ _) (LocalsSame.of_eq rfl rfl)
           intro p a
           repeat (any_goals (first
             | exact LocalsSame.refl _
             | exact LocalsSame.of_eq rfl rfl
             | split))))
    | (simp at h)
    | split at h
    | (unfold Builtins.numBin at h)
    | (unfold Builtins.okStrFrom at h)
    | (unfold Builtins.binArg at h)
    | (unfold Builtins.frozenErr at h)
    | (unfold Builtins.coerceFailed at h)
    | (unfold Builtins.floatToInt at h)
    | (unfold Builtins.raiseImpl at h)
    | (unfold Builtins.raiseClass at h)
    | (unfold Builtins.withIndex at h)
    | (unfold Builtins.intBitRef at h)
    | (unfold Builtins.numCmp at h)
    | (unfold Builtins.sortImpl at h)
    | (exact newImpl_locals _ _ _ _ _ h)
    | (unfold Builtins.joinImpl at h)
    | (unfold Builtins.okStr at h)
    | (unfold Builtins.okStrEnc at h)
    | (unfold Builtins.allocStr at h)
    | (unfold Builtins.allocStrEnc at h)
    | (unfold Builtins.allocArr at h)
    | (unfold Builtins.allocHsh at h)
    | (unfold Builtins.allocExc at h)
    | (exact runRegex_locals _ _ _ _ _ _ h)
    | (exact runModules_locals _ _ _ _ _ _ h)
    | (exact runCollections_locals _ _ _ _ _ _ h)
    | (exact runStrings_locals _ _ _ _ _ _ h)
    | (exact runNumerics_locals _ _ _ _ _ _ h)
    | (exact runObjects_locals _ _ _ _ _ _ h))))

set_option maxHeartbeats 0 in
theorem runRegex_locals (bid : String) (recv : Value) (args : List Value) (m : Machine) :
    ∀ v m', Builtins.runRegex bid recv args m = .ok v m' → LocalsSame m m' := by
  intro v m' h
  rw [Builtins.runRegex.eq_def] at h
  dsimp only at h
  builtin_arms

set_option maxHeartbeats 0 in
theorem runModules_locals (bid : String) (recv : Value) (args : List Value) (m : Machine) :
    ∀ v m', Builtins.runModules bid recv args m = .ok v m' → LocalsSame m m' := by
  intro v m' h
  rw [Builtins.runModules.eq_def] at h
  dsimp only at h
  builtin_arms

set_option maxHeartbeats 0 in
theorem runCollections_locals (bid : String) (recv : Value) (args : List Value) (m : Machine) :
    ∀ v m', Builtins.runCollections bid recv args m = .ok v m' → LocalsSame m m' := by
  intro v m' h
  rw [Builtins.runCollections.eq_def] at h
  dsimp only at h
  builtin_arms

set_option maxHeartbeats 0 in
theorem runStrings_locals (bid : String) (recv : Value) (args : List Value) (m : Machine) :
    ∀ v m', Builtins.runStrings bid recv args m = .ok v m' → LocalsSame m m' := by
  intro v m' h
  rw [Builtins.runStrings.eq_def] at h
  dsimp only at h
  builtin_arms

set_option maxHeartbeats 0 in
theorem runNumerics_locals (bid : String) (recv : Value) (args : List Value) (m : Machine) :
    ∀ v m', Builtins.runNumerics bid recv args m = .ok v m' → LocalsSame m m' := by
  intro v m' h
  rw [Builtins.runNumerics.eq_def] at h
  dsimp only at h
  builtin_arms

set_option maxHeartbeats 0 in
theorem runObjects_locals (bid : String) (recv : Value) (args : List Value) (m : Machine) :
    ∀ v m', Builtins.runObjects bid recv args m = .ok v m' → LocalsSame m m' := by
  intro v m' h
  rw [Builtins.runObjects.eq_def] at h
  dsimp only at h
  builtin_arms

/-! **The whole `Builtins` layer**: a builtin that answers with a value leaves every frame's
locals, and the frame stack, where they were. -/

set_option maxHeartbeats 0 in
theorem builtins_run_locals (bid : String) (recv : Value) (args : List Value) (m : Machine) :
    ∀ v m', Builtins.run bid recv args m = .ok v m' → LocalsSame m m' := by
  intro v m' h
  rw [Builtins.run.eq_def] at h
  dsimp only at h
  builtin_arms

#print axioms builtins_run_locals

/-! ## What is **not** here yet

The `Interp` layer: `evalExpr`, `applyKont`, `unwind` and the helpers under
`RubyCore/Interp/`. Those are where the claim stops being "the machine came back unchanged" —
the interpreter *does* write `frames`, at exactly four sites (`setLocal`, `setCurrentFrame`,
`setLastMatchValue`, and six `frames.push`es), which is what `Denote/Sem/Locals.lean`'s
`ReachesB` and `Sealed` are for. The `Builtins` half being uniform is what makes that half
tractable: it is the widest layer and it needed no case analysis about *which* frame was
written.

**Three things worth not re-deriving** from building this:

* the claim has to be about `locals`, not `frames`. "`Builtins` never touches `frames`" is what
  a grep suggests and it is false twice over: `Object#__match_xparent` writes the current frame
  through `Machine.setCurrentFrame`, and `$~`'s write reaches a frame `matchFrameId` may pick
  **below** the current one. Neither touches `locals`.
* `rw [f]` on a `where`-helper brings the arm equations and with them the "no earlier pattern
  matched" side conditions (`subj = Value.nil → False`, unprovable at that point). `unfold f at h`
  is the form that works — the same trap `Denote/Rules/ClassOf.lean` records for
  `isClassRefNamed`, one layer down.
* `split at h` reaches for a scrutinee **anywhere** in the hypothesis, so a helper with an inner
  `match` under a binder (`newImpl`'s `match toSP m msgV` under `match args with | [msgV]`) has
  to have its outer `if`s peeled by hand first. That is the whole reason `newImpl_locals` is a
  written-out proof rather than another line in the closer.
-/

end Ratchet.Denote
