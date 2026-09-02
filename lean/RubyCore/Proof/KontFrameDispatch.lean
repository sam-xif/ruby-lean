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

/-! ### `enterUserMethod`: measured to 32 goals of one shape

The largest function in the layer — `classifyFull`, two locals lists built by folds,
`destructureBind`, the frame push and the kont push — and the only one this file does not
close. What was learned is worth more than the theorem would be, so it is recorded rather than
left as a `sorry`:

* **Generalising first is what makes it tractable at all.** `classifyFull md.params` is
  machine-free and occurs ~20 times in the body; `generalize hfp : classifyFull md.params = fp?`
  followed by `cases fp?` takes the proof from *ten minutes and a timeout at 40M heartbeats* to
  **32 seconds**. The same move on the keyword-collapse pair (`(args, m)`, rebound by an `if`
  whose branches each occur ~15 times) takes it further.
* **The remaining 32 goals are all one shape**, and the obstacle is the **structure-eta
  blowup**: the activation frame is pushed onto the *destructuring fold's* machine
  (`{ (fold …).snd with frames := …, stack := … }`), and `simp` expands that into a literal
  whose nine fields are projections of the fold — after which no framing lemma matches, and the
  goal is ten thousand lines wide. Framing the fold *before* the push is the fix, and doing
  that needs either a keyed variant for that specific fold or `enterUserMethod` split into
  named helpers in `RubyCore` (which is what its 135 lines argue for anyway).
* **`frame_simp` must still run at the top**, before the generalisations: without it the two
  sides' scrutinees differ and `split` desynchronises the arms — 457 goals instead of 32.

Everything `enterUserMethod` calls is framed (`appendKwHash`, `allocArr`, `allocHsh`,
`destructureBind`, `setLocal`, `withCtl`/`withKont`), so this is the last function in
`Dispatch` and not a dependency of anything below it.
-/

#print axioms enterClassBody_frame
#print axioms enterScopedClassBody_frame

end Proof
end RubyCore
