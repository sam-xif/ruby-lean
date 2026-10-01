import Denote.Sem.Core.RootAnswer
import Denote.Sem.Core.Decompose

/-! The stack-only interface used by typed rules, derived from exact root framing.
Entry and answer quiescence are explicit proof obligations. Halts and out-of-fuel
states retain the full saved-execution frame action. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

theorem deliverA_val (m : Machine) (v : Value) (K : List Kont) :
    deliverA (.val v) m K = deliver m v K := rfl

abbrev Halt.underK := Halt.underRoot

def resOutA (K : List Kont) : ARes → ARes
  | .ans a m rest => runA rest (deliverA a m K)
  | .halt h => .halt (h.underK K)
  | .oof m => .oof (Proof.pushRootK K m)

theorem answerPoint_pushK_none {m : Machine} (K : List Kont) (h : answerPoint m = none) :
    answerPoint (pushK K m) = none := by
  cases hk : m.kont <;> cases hc : m.ctl <;> simp_all [answerPoint, pushK]
  all_goals cases K <;> rfl

theorem pushK_eq_deliverA {m : Machine} {a : Answer} (K : List Kont)
    (hap : answerPoint m = some a) : pushK K m = deliverA a m K := by
  exact (congrArg (pushK K) (answerPoint_deliver_nil hap)).symm.trans rfl

theorem run_pushK (K : List Kont) (hK : Proof.CatchFree K)
    (fuel : Nat) (m : Machine) (hm : RootClean m)
    (hout : ∀ a n rest, runA fuel m = .ans a n rest → RootClean n) :
    Interp.run fuel (pushK K m) = (runA fuel m).out K :=
  run_pushK_clean K hK fuel m hm hout

theorem runA_pushK (K : List Kont) (hK : Proof.CatchFree K)
    (fuel : Nat) (m : Machine) (hm : RootClean m)
    (hout : ∀ a n rest, runA fuel m = .ans a n rest → RootClean n) :
    runA fuel (pushK K m) = resOutA K (runA fuel m) := by
  rw [pushK, ← Proof.pushRootK_quiescent K m hm.1 hm.2, runA_pushRootK K hK]
  cases hr : runA fuel m with
  | ans a n rest =>
    simp only [rootResOutA, resOutA, deliverRootA_clean a n K (hout a n rest hr)]
  | halt h => rfl
  | oof n => rfl

theorem run_eq_out_nil (fuel : Nat) (m : Machine) :
    Interp.run fuel m = (runA fuel m).out [] := run_eq_out_nil_root fuel m

#print axioms run_pushK
#print axioms runA_pushK
#print axioms run_eq_out_nil
end Ratchet.Denote
