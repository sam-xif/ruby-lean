import RubyCore.Proof.RootFrameComplex

set_option autoImplicit false
namespace RubyCore.Proof.Root
open Builtins

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 400000 in
@[rootFrameLem] theorem runNumerics_frame (K : List Kont) (bid : String) (recv : Value) (args : List Value)
    (m : Machine) (hLock : HashLockFree K) :
    runNumerics bid recv args (pushRootK K m) = bRootPush K (runNumerics bid recv args m) := by
  rw [runNumerics.eq_def, runNumerics.eq_def]
  simp only [rootFrameLem]
  (repeat' first | rfl | split) <;> (try root_simp) <;> root_hof
  exact runComplex_frame K m bid recv args hLock

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 400000 in
@[rootFrameLem] theorem runObjects_frame (K : List Kont) (bid : String) (recv : Value)
    (args : List Value) (m : Machine) (hLock : HashLockFree K) :
    runObjects bid recv args (pushRootK K m) = bRootPush K (runObjects bid recv args m) := by
  rw [runObjects.eq_def, runObjects.eq_def]
  -- `root_simp` first, because the body opens with a `have h := m.heap` and `rw` cannot
  -- reach under a binder; `simp`'s zeta reduction removes it.
  root_simp
  -- **`rw [printFold_frame]` before `split`, and inside the loop.** `Kernel#print`'s fold has
  -- to be framed while it is still one term: once `split` has case-analysed it, the two sides'
  -- outcomes are separate (contradictory) hypotheses and the lemma that reconciles them is
  -- lambda-headed, hence invisible to `simp` — eight `False` goals. It cannot be done before
  -- the loop either, because the fold sits inside a matcher arm and `rw` does not reach under
  -- a binder. So it goes *in* the loop, tried ahead of `split`: it fails at the top and fires
  -- the moment the `bid` match has been peeled.
  (repeat' first | rfl | exact printArm_frame K m args | split) <;> (try root_simp) <;>
    (first | rfl | (try simp_all (maxSteps := 400000) [rootFrameLem]) | skip) <;> (try rfl)
  -- one arm (`Array#to_a` on a non-Array) that `simp_all` left as a conjunction after
  -- destructuring the pair
  -- `Kernel#p`'s multi-argument arm: `simp_all` destructured the allocated pair and left the
  -- machine equality as a hypothesis rather than substituting it
  all_goals (try (rename_i hpush _ _ _; subst hpush; exact ⟨rfl, rfl⟩))
  all_goals root_hof
  all_goals (try exact runNumerics_frame K bid recv args m hLock)
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
@[rootFrameLem] theorem run_frame (K : List Kont) (bid : String) (recv : Value)
    (args : List Value) (m : Machine) (hLock : HashLockFree K) :
    Builtins.run bid recv args (pushRootK K m) = bRootPush K (Builtins.run bid recv args m) := by
  rw [Builtins.run.eq_def, Builtins.run.eq_def]
  root_simp
  root_arms
  all_goals root_hof
  all_goals (try exact runObjects_frame K bid recv args m hLock)


end RubyCore.Proof.Root
