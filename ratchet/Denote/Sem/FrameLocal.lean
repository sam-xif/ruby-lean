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
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

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

/-! ### What is **not** here yet

The seven `Builtins` dispatchers and `Regex`'s five fold-carrying helpers. They were built and
then taken back out: the dispatchers close on the automation described above (measured: one
`repeat (any_goals (first | … | split at h | unfold <helper> at h))` with the twenty helpers
below in the unfold list takes `runObjects` from 200-odd arms to **one** open goal, the
fall-through), and what is left is `Regex`'s five, where the machine is threaded through a
`List.foldl` over a pair and the step's own `match` has to be split *inside*
`foldPair_locals`'s hypothesis. Those five are the next session's first job, and the vocabulary
they need — `foldPair_locals`, `setLastMatch_locals`, `allocStrEnc_locals` — is all here.

**Two measurements worth not re-deriving**, both from that attempt:

* the claim has to be about `locals`, not `frames`. `Object#__match_xparent` writes the current
  frame through `Machine.setCurrentFrame`, and `$~`'s write (`setLastMatchValue`) writes a frame
  `matchFrameId` may pick *below* the current one — so "`Builtins` never touches `frames`",
  which a grep suggests, is false twice over. Neither touches `locals`.
* `rw [f]` on a `where`-helper generates the arm equations and with them the "no earlier pattern
  matched" side conditions (`subj = Value.nil → False`, unprovable at that point). `unfold f at h`
  is the form that works, and it is the same trap `Denote/Rules/ClassOf.lean` records for
  `isClassRefNamed`.
-/

end Ratchet.Denote
