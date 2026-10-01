import RubyCore.Proof.RootFramePrimitives

/-! Framing the stateful Rational and Complex primitives. -/
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace RubyCore.Proof.Root
open Builtins

@[rootFrameLem] theorem allocRat_frame (K : List Kont) (m : Machine) (n : Int) (d : Nat) :
    allocRat (pushRootK K m) n d = ((allocRat m n d).1, pushRootK K (allocRat m n d).2) := rfl

@[rootFrameLem] theorem ratResult_frame (K : List Kont) (m : Machine) (n d : Int) :
    ratResult (pushRootK K m) n d = bRootPush K (ratResult m n d) := by
  unfold ratResult
  split <;> rfl

@[rootFrameLem] theorem rationalConstructor_frame (K : List Kont) (m : Machine) (args : List Value) :
    rationalConstructor (pushRootK K m) args = bRootPush K (rationalConstructor m args) := by
  unfold rationalConstructor
  root_simp
  root_arms

@[rootFrameLem] theorem rationalBinary_frame (K : List Kont) (bid : String) (recv other : Value)
    (m : Machine) (n : Int) (d : Nat) :
    rationalBinary bid recv other (pushRootK K m) n d =
      bRootPush K (rationalBinary bid recv other m n d) := by
  unfold rationalBinary
  root_simp
  root_arms

@[rootFrameLem] theorem runRationals_frame (K : List Kont) (bid : String) (recv : Value)
    (args : List Value) (m : Machine) (hLock : HashLockFree K) :
    runRationals bid recv args (pushRootK K m) = bRootPush K (runRationals bid recv args m) := by
  unfold runRationals
  root_simp
  root_arms
  all_goals root_hof

/-- Frame both the stateful result and any error that retains a machine. -/
def cRootPush {α : Type} (K : List Kont) : Except BRes (α × Machine) → Except BRes (α × Machine)
  | .ok (a, m) => .ok (a, pushRootK K m)
  | .error r => .error (bRootPush K r)

@[rootFrameLem] theorem cRootPush_ok {α : Type} (K : List Kont) (a : α) (m : Machine) :
    cRootPush K (.ok (a, m)) = .ok (a, pushRootK K m) := rfl
@[rootFrameLem] theorem cRootPush_error {α : Type} (K : List Kont) (r : BRes) :
    cRootPush (α := α) K (.error r) = .error (bRootPush K r) := rfl

@[rootFrameLem] theorem complexAlloc_frame (K : List Kont) (m : Machine) (r i : Value) :
    (complexAlloc r i) (pushRootK K m) = cRootPush K ((complexAlloc r i) m) := rfl

@[rootFrameLem] theorem complexRat_frame (K : List Kont) (m : Machine) (n d : Int) :
    (complexRat n d) (pushRootK K m) = cRootPush K ((complexRat n d) m) := by
  unfold complexRat
  dsimp only [getThe, MonadState.get, MonadStateOf.get, StateT.get, Bind.bind,
    StateT.bind, Pure.pure, Except.pure, Except.bind, StateT.run]
  rw [ratResult_frame]
  cases ratResult m n d <;> rfl

@[rootFrameLem] theorem complexNegate_frame (K : List Kont) (m : Machine) (v : Value) :
    (complexNegate v) (pushRootK K m) = cRootPush K ((complexNegate v) m) := by
  unfold complexNegate
  cases v <;> (try rfl)
  all_goals
    dsimp only [getThe, MonadState.get, MonadStateOf.get, StateT.get, Bind.bind,
      StateT.bind, Pure.pure, Except.pure, Except.bind, StateT.run]
    simp only [rootFrameLem]
    cases rationalPayload? m.heap (.ref _) with
    | none => rfl
    | some pair => exact complexRat_frame K m (-pair.1) pair.2


end RubyCore.Proof.Root
