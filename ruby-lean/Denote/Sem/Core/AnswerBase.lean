import Denote.Sem.Core.Frame
import RubyCore.Proof.RootFrameStep
import RubyCore.Proof.NotDone

/-! Answer observations, before choosing how to attach an outer continuation.
Queued sends keep running; only values and escapes at an empty stack are cuts. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

inductive Answer where
  | val (v : Value)
  | esc (j : Jump)
deriving Inhabited

/-- The control word an answer is in flight as. -/
def Answer.ctl : Answer → Ctl
  | .val v => .value v
  | .esc j => .jump j

/-- **The answer point**: an empty continuation with something in flight. These are exactly
the two states `RubyCore.Proof.stepFn_frame`'s side condition excludes — i.e. exactly the
states at which appending a continuation changes what happens next — which is why they are
the right place to cut. -/
def answerPoint (m : Machine) : Option Answer :=
  match m.kont with
  | [] =>
    match m.ctl with
    | .value v => some (.val v)
    | .jump j => some (.esc j)
    | .eval _ | .send .. => none
  | _ :: _ => none

/-- Handing answer `a` to continuation `K` from machine `m`. Generalises
`Denote/Sem/Core/Decompose.lean`'s `deliver`, which is the `val` arm. -/
def deliverA (a : Answer) (m : Machine) (K : List Kont) : Machine :=
  { m with ctl := a.ctl, kont := K }

/-- An outcome that is **not** handed to anything: the run is over whatever is below it.
`.unsupported` and `.stuck` carry the pre-step machine, which is why the continuation has to
be re-applied when the halt is reported from inside a `pushK`. -/
inductive Halt where
  | uncaught (exc : Value) (m : Machine)
  | unsupported (reason : String) (m : Machine)
  | stuck (msg : String) (m : Machine)

/-- The result of running to the next answer. -/
inductive ARes where
  | ans (a : Answer) (m : Machine) (rest : Nat)
  | halt (h : Halt)
  | oof (m : Machine)

/-- **`Interp.run`, stopped at the answer point.** Identical to `Interp.run` except that it
does not step *through* an empty-continuation value or jump — it reports it, with the fuel
that was left. -/
def runA (fuel : Nat) (m : Machine) : ARes :=
  match answerPoint m with
  | some a => .ans a m fuel
  | none =>
    match fuel with
    | 0 => .oof m
    | f + 1 =>
      match Interp.stepFn m with
      | .next m' => runA f m'
      -- unreachable: `done_inv` puts `.done` at an answer point, and this branch is not one
      | .done v m' => .ans (.val v) m' f
      | .uncaught exc m' => .halt (.uncaught exc m')
      | .unsupported r => .halt (.unsupported r m)
      | .stuck msg => .halt (.stuck msg m)

/-- What a halt looks like from outside a `pushK K`. -/
def Halt.out (K : List Kont) : Halt → Interp.RunResult
  | .uncaught exc m => .uncaught exc m
  | .unsupported r m => .unsupported r (RubyCore.Proof.pushRootK K m)
  | .stuck msg m => .stuck msg (RubyCore.Proof.pushRootK K m)

/-- **The reassembly.** Given what the inner computation did, what the run under `K` is. -/
def ARes.out (K : List Kont) : ARes → Interp.RunResult
  | .ans a m rest => Interp.run rest (deliverA a m K)
  | .halt h => h.out K
  | .oof m => .outOfFuel (RubyCore.Proof.pushRootK K m)

/-! ## Unfolding lemmas -/

theorem runA_ans {m : Machine} {a : Answer} (h : answerPoint m = some a) (fuel : Nat) :
    runA fuel m = .ans a m fuel := by
  rw [runA.eq_def, h]

theorem runA_zero {m : Machine} (h : answerPoint m = none) : runA 0 m = .oof m := by
  rw [runA.eq_def, h]

theorem runA_succ {m : Machine} (h : answerPoint m = none) (f : Nat) :
    runA (f + 1) m =
      (match Interp.stepFn m with
       | .next m' => runA f m'
       | .done v m' => .ans (.val v) m' f
       | .uncaught exc m' => .halt (.uncaught exc m')
       | .unsupported r => .halt (.unsupported r m)
       | .stuck msg => .halt (.stuck msg m)) := by
  rw [runA, h]

end Ratchet.Denote
