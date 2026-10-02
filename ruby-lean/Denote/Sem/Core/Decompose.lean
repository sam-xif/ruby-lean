import Denote.Sem.Core.KontFrameBase
import RubyCore.Proof.KontFrame
import RubyCore.Proof.NotDone

/-! Continuation framing now follows saved root executions. The old unconditional
stack-only frame equation and immediate-raise escape lemmas were false after
Enumerator fibers and queued exception initialization were introduced. Their
run-level replacement is RootAnswer.run_pushRootK; its stack-only specialization
requires clean entry and answer boundaries. No admitted rule uses the retired
value-only run_split or jump_empty_never_value helpers. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

theorem catchFree_iff (K : List Kont) : CatchFree K ↔ Proof.CatchFree K := Iff.rfl

theorem kontFrameCatchFree : KontFrameCatchFree :=
  fun m K hK hside => Proof.Root.stepFn_frame_eq K hK m hside

/-- Retained to state the handler counterexample; no arbitrary tail is assumed opaque. -/
def JumpOpaque (K : List Kont) : Prop :=
  ∀ (m : Machine) (j : Jump) (fuel : Nat) (v : Value) (m' : Machine),
    Interp.run fuel { m with ctl := .jump j, kont := K } ≠ .value v m'

abbrev deliver (m : Machine) (v : Value) (K : List Kont) : Machine :=
  { m with ctl := .value v, kont := K }

theorem pushK_eq_deliver (K : List Kont) {m : Machine} {w : Value} (hc : m.ctl = .value w)
    (hk : m.kont = []) : pushK K m = deliver m w K := by
  simp only [pushK, deliver, hk, List.nil_append, ← hc]

#print axioms kontFrameCatchFree
end Ratchet.Denote
