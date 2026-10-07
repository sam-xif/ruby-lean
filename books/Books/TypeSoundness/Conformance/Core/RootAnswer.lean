import Books.TypeSoundness.Conformance.Core.AnswerBase
import Books.TypeSoundness.Denotation.Root

/-! Exact run decomposition through saved root executions. At typed boundaries
RootClean recovers the ordinary stack-only delivery used by the typing rules.
No invariant is assumed for intermediate out-of-fuel or halted states. -/
set_option autoImplicit false
namespace Checker.Soundness
open RubyCore

private theorem answerPoint_spec {m : Machine} {a : Answer}
    (h : answerPoint m = some a) : m.ctl = a.ctl ∧ m.kont = [] := by
  cases hk : m.kont with
  | cons k ks => simp [answerPoint, hk] at h
  | nil =>
    cases hc : m.ctl <;> simp [answerPoint, hk, hc] at h
    all_goals cases h; exact ⟨rfl, rfl⟩

theorem answerPoint_deliver_nil {m : Machine} {a : Answer}
    (h : answerPoint m = some a) : deliverA a m [] = m := by
  obtain ⟨hc, hk⟩ := answerPoint_spec h
  simp only [deliverA, ← hc, ← hk]

/-- The frame action is identity at an empty tail, including saved executions. -/
theorem pushRootK_nil (m : Machine) : Proof.pushRootK [] m = m := by
  have he (e : Execution) : Proof.frameExecution [] e = e := by
    simp [Proof.frameExecution]
  have hef : Proof.frameExecution [] = id := funext he
  have hs (s : EnumState) : Proof.frameEnumState [] s = s := by
    simp [Proof.frameEnumState, hef]
  simp [Proof.pushRootK, hs]

def deliverRootA (a : Answer) (m : Machine) (K : List Kont) : Machine :=
  Proof.pushRootK K (deliverA a m [])

theorem deliverRootA_clean (a : Answer) (m : Machine) (K : List Kont)
    (hm : RootClean m) : deliverRootA a m K = deliverA a m K := by
  rw [deliverRootA, Proof.pushRootK_quiescent K (deliverA a m []) hm.1 hm.2]
  rfl

def ARes.rootOut (K : List Kont) : ARes → Interp.RunResult
  | .ans a m rest => Interp.run rest (deliverRootA a m K)
  | .halt h => h.out K
  | .oof m => .outOfFuel (Proof.pushRootK K m)

def Halt.underRoot (K : List Kont) : Halt → Halt
  | .uncaught exc m => .uncaught exc m
  | .unsupported r m => .unsupported r (Proof.pushRootK K m)
  | .stuck msg m => .stuck msg (Proof.pushRootK K m)

def rootResOutA (K : List Kont) : ARes → ARes
  | .ans a m rest => runA rest (deliverRootA a m K)
  | .halt h => .halt (h.underRoot K)
  | .oof m => .oof (Proof.pushRootK K m)

private theorem stepFn_root_none (K : List Kont) (hK : Proof.Root.ContextFree K)
    (m : Machine) (h : answerPoint m = none) :
    Interp.stepFn (Proof.pushRootK K m) = Proof.rootFrameR K (Interp.stepFn m) := by
  cases hc : m.ctl with
  | eval e =>
    exact Proof.Root.stepFn_frame_eq K hK m (Or.inr ⟨e, hc⟩)
  | send recv site name args blk kw =>
    simp only [Interp.stepFn, Proof.Root.pushRootK_ctl, hc,
      Proof.Root.invokeQueued_frame K hK]
  | value v =>
    apply Proof.Root.stepFn_frame_eq K hK m
    left; intro hk; simp [answerPoint, hk, hc] at h
  | jump j =>
    apply Proof.Root.stepFn_frame_eq K hK m
    left; intro hk; simp [answerPoint, hk, hc] at h

private theorem answerPoint_root_none (K : List Kont) {m : Machine}
    (h : answerPoint m = none) : answerPoint (Proof.pushRootK K m) = none := by
  cases ha : m.activeEnumerator <;> cases hk : m.kont <;> cases hc : m.ctl <;>
    simp_all [answerPoint, Proof.pushRootK]
  all_goals cases K <;> rfl

theorem run_pushRootK (K : List Kont) (hK : Proof.Root.ContextFree K) :
    ∀ fuel m, Interp.run fuel (Proof.pushRootK K m) = (runA fuel m).rootOut K := by
  intro fuel
  induction fuel with
  | zero =>
    intro m
    cases ha : answerPoint m with
    | some a =>
      rw [runA_ans ha]
      simp only [ARes.rootOut, deliverRootA, answerPoint_deliver_nil ha]
    | none => rw [runA_zero ha]; rfl
  | succ fuel ih =>
    intro m
    cases ha : answerPoint m with
    | some a =>
      rw [runA_ans ha]
      simp only [ARes.rootOut, deliverRootA, answerPoint_deliver_nil ha]
    | none =>
      rw [runA_succ ha, Interp.run, stepFn_root_none K hK m ha]
      cases hs : Interp.stepFn m with
      | next n => exact ih n
      | done v n =>
        obtain ⟨hc, hk, _⟩ := Proof.done_inv m v n hs
        simp [answerPoint, hc, hk] at ha
      | uncaught exc n => rfl
      | unsupported msg => rfl
      | stuck msg => rfl

theorem runA_pushRootK (K : List Kont) (hK : Proof.Root.ContextFree K) :
    ∀ fuel m, runA fuel (Proof.pushRootK K m) = rootResOutA K (runA fuel m) := by
  intro fuel
  induction fuel with
  | zero =>
    intro m
    cases ha : answerPoint m with
    | some a =>
      rw [runA_ans ha]
      simp only [rootResOutA, deliverRootA, answerPoint_deliver_nil ha]
    | none =>
      rw [runA_zero ha, runA_zero (answerPoint_root_none K ha)]
      rfl
  | succ fuel ih =>
    intro m
    cases ha : answerPoint m with
    | some a =>
      rw [runA_ans ha]
      simp only [rootResOutA, deliverRootA, answerPoint_deliver_nil ha]
    | none =>
      rw [runA_succ ha, runA_succ (answerPoint_root_none K ha), stepFn_root_none K hK m ha]
      cases hs : Interp.stepFn m with
      | next n => exact ih n
      | done v n =>
        obtain ⟨hc, hk, _⟩ := Proof.done_inv m v n hs
        simp [answerPoint, hc, hk] at ha
      | uncaught exc n => rfl
      | unsupported msg => rfl
      | stuck msg => rfl

/-- Stack-only composition is a consequence at clean entry/answer boundaries.
The intermediate run still uses the full saved-execution frame action. -/
theorem run_pushK_clean (K : List Kont) (hK : Proof.Root.ContextFree K)
    (fuel : Nat) (m : Machine) (hm : RootClean m)
    (hout : ∀ a n rest, runA fuel m = .ans a n rest → RootClean n) :
    Interp.run fuel (pushK K m) = (runA fuel m).out K := by
  rw [pushK, ← Proof.pushRootK_quiescent K m hm.1 hm.2, run_pushRootK K hK]
  cases hr : runA fuel m with
  | ans a n rest =>
    simp only [ARes.rootOut, ARes.out, deliverRootA_clean a n K (hout a n rest hr)]
  | halt h => rfl
  | oof n => rfl

theorem run_eq_out_nil_root (fuel : Nat) (m : Machine) :
    Interp.run fuel m = (runA fuel m).out [] := by
  have h := run_pushRootK [] (by intro k hk; simp at hk) fuel m
  rw [pushRootK_nil] at h
  rw [h]
  cases runA fuel m <;> simp only [ARes.rootOut, ARes.out, deliverRootA, pushRootK_nil]

#print axioms run_pushRootK
#print axioms runA_pushRootK
#print axioms run_pushK_clean
#print axioms run_eq_out_nil_root
end Checker.Soundness
