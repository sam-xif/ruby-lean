import Denote.Rules.Iterator.FrameReturn
import Denote.Rules.Closure.Return
import Denote.Judgment.BoundedRun
import Denote.Rules.Primitive.PrimitiveStep

/-! Array#each reads the live payload after every yield. Sorbet 0.6.13405 gives
the block the array element type, returns the receiver and requires captured types
to remain stable across iterations (clink 224). Fuel induction covers growing arrays;
body entry, invariant preservation and caller conformance remain explicit premises. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

def eachArrayStep (m : Machine) (cl : Closure) (brk o : ObjId) (index : Nat) : StepResult :=
  Interp.iterStep { m with kont := [.frameK brk] } cl brk [] (.arrayEach o index) [] (.ref o)

theorem eachArrayStep_more (m : Machine) (cl : Closure) (brk o : ObjId) (index : Nat)
    (xs : Array Value) (name : String) (e : Ratchet.Expr)
    (hx : (m.heap.get o).payload = .arr xs) (hi : index < xs.size)
    (hp : cl.params = [.req name]) (he : cl.body = toRuby e)
    (henum : cl.enumYield = none) (hfor : cl.forTargets = none) :
    eachArrayStep m cl brk o index = .next
      (pushK [.blkFrameK m.frames.size cl.lam (closureBrk m cl (some brk)) cl [xs[index]],
        .iterK cl brk [] (.arrayEach o (index + 1)) [] (.ref o) xs[index], .frameK brk]
        (evalFrom (pushMethodFrame m (requiredClosureFrame m cl [name] [xs[index]])) e)) := by
  unfold eachArrayStep Interp.iterStep
  simp only [hx, hi, ↓reduceDIte]
  rw [callClosure_required _ cl [name] [xs[index]] _ none none hp rfl henum hfor, he]
  simp only [requiredClosureFrame, definitionFrameId_reCtl]
  rfl

theorem eachArrayStep_end (m : Machine) (cl : Closure) (brk o : ObjId) (index : Nat)
    (xs : Array Value) (hx : (m.heap.get o).payload = .arr xs) (hi : ¬ index < xs.size) :
    eachArrayStep m cl brk o index = .next (deliverA (.val (.ref o)) m [.frameK brk]) := by
  simp only [eachArrayStep, Interp.iterStep, hx, hi, ↓reduceDIte]
  rfl

/-- The loop invariant includes the captured caller below the iterator, the receiver
and the cursor. Each body sees a fresh live element. Neither the length nor the payload
is required to stay equal to its entry value. Only raises may escape a certified body. -/
structure EachArrayContract (origin : Machine) (cl : Closure) (name : String)
    (e : Ratchet.Expr) (o : ObjId) (P : Machine → Nat → Prop)
    (Γ : Env) (τ : Ty) (κ : Ctx) (I : Ty) (Γb : Env) (ρ : Ty) (κb : Ctx) (Ib : Ty) : Prop where
  params : cl.params = [.req name]
  code : cl.body = toRuby e
  enumNone : cl.enumYield = none
  forNone : cl.forTargets = none
  root : ∀ m i, P m i → RootClean m
  array : ∀ m i, P m i → ∃ xs, (m.heap.get o).payload = .arr xs
  body : ∀ m i, P m i → ∀ xs, (m.heap.get o).payload = .arr xs → ∀ hi : i < xs.size,
    RunSpec (pushMethodFrame m (requiredClosureFrame m cl [name] [xs[i]]))
      (evalFrom (pushMethodFrame m (requiredClosureFrame m cl [name] [xs[i]])) e) Γb ρ κb Ib
  next : ∀ m i, P m i → ∀ xs, (m.heap.get o).payload = .arr xs → ∀ hi : i < xs.size, ∀ v n,
    ResultOk (pushMethodFrame m (requiredClosureFrame m cl [name] [xs[i]])) Γb ρ (.val v) n κb Ib →
    P (deliverA (.val v) (popMethodFrame n) []) (i + 1)
  done : ∀ m i, P m i → ResultOk origin Γ τ (.val (.ref o)) (popMethodFrame m) κ I
  escape : ∀ m i, P m i → ∀ xs, (m.heap.get o).payload = .arr xs → ∀ hi : i < xs.size, ∀ j n,
    ResultOk (pushMethodFrame m (requiredClosureFrame m cl [name] [xs[i]])) Γb ρ (.esc j) n κb Ib →
    ResultOk origin Γ τ (.esc j) (popMethodFrame (popMethodFrame n)) κ I

theorem eachArrayStep_specAt {origin : Machine} {cl : Closure} {name : String}
    {e : Ratchet.Expr} {o : ObjId} {P : Machine → Nat → Prop}
    {Γ Γb : Env} {τ ρ I Ib : Ty} {κ κb : Ctx}
    (h : EachArrayContract origin cl name e o P Γ τ κ I Γb ρ κb Ib)
    (brk : FrameId) (N : Nat) (m : Machine) (index : Nat) (hm : P m index) :
    StepSpecAt N origin Γ τ (eachArrayStep m cl brk o index) κ I := by
  induction N generalizing m index with
  | zero =>
    obtain ⟨xs, hx⟩ := h.array m index hm
    by_cases hi : index < xs.size
    · rw [eachArrayStep_more m cl brk o index xs name e hx hi h.params h.code h.enumNone h.forNone]
      exact RunSpecAt.zero (by rfl)
    · rw [eachArrayStep_end m cl brk o index xs hx hi]
      exact RunSpecAt.zero (by rfl)
  | succ N ih =>
    obtain ⟨xs, hx⟩ := h.array m index hm
    by_cases hi : index < xs.size
    · rw [eachArrayStep_more m cl brk o index xs name e hx hi h.params h.code h.enumNone h.forNone]
      apply ((h.body m index hm xs hx hi).at (N + 1)).bindSpec (h.root m index hm) (by
        intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> rfl)
      intro a n hn
      cases a with
      | val v =>
        apply RunSpecAt.step (by rfl) (step_blkFrameK_value n _ cl.lam (closureBrk m cl (some brk)) cl [xs[index]] v)
        apply RunSpecAt.of_stepSpecWithin (by rfl)
        exact ih (deliverA (.val v) (popMethodFrame n) []) (index + 1)
          (h.next m index hm xs hx hi v n hn)
      | esc j =>
        obtain ⟨exc, rfl, _⟩ := hn.2.1.only_raise
        apply RunSpecAt.stepWithin (by rfl) (show Interp.stepFn _ = .next _ from rfl)
        apply RunSpecAt.stepWithin (by rfl) (show Interp.stepFn _ = .next _ from rfl)
        apply RunSpecAt.stepWithin (by rfl) (show Interp.stepFn _ = .next _ from rfl)
        exact RunSpecAt.answer (h.escape m index hm xs hx hi (.raiseJ exc) n hn)
    · rw [eachArrayStep_end m cl brk o index xs hx hi]
      apply RunSpecAt.stepWithin (by rfl) (show Interp.stepFn _ = .next _ from rfl)
      exact RunSpecAt.answer (h.done m index hm)

theorem eachArrayStep_spec {origin : Machine} {cl : Closure} {name : String}
    {e : Ratchet.Expr} {o : ObjId} {P : Machine → Nat → Prop}
    {Γ Γb : Env} {τ ρ I Ib : Ty} {κ κb : Ctx}
    (h : EachArrayContract origin cl name e o P Γ τ κ I Γb ρ κb Ib)
    (brk : FrameId) (m : Machine) (index : Nat) (hm : P m index) :
    StepSpec origin Γ τ (eachArrayStep m cl brk o index) κ I := by
  have hall := fun N => eachArrayStep_specAt h brk N m index hm
  cases hs : eachArrayStep m cl brk o index with
  | next n =>
    apply runSpec_iff_allAt.mpr
    intro N
    simpa only [hs, StepSpecAt] using hall N
  | unsupported _ => trivial
  | done v n => simpa only [hs, StepSpecAt] using hall 0
  | uncaught v n => simpa only [hs, StepSpecAt] using hall 0
  | stuck msg => simpa only [hs, StepSpecAt] using hall 0

#print axioms eachArrayStep_more
#print axioms eachArrayStep_spec
end Ratchet.Denote.Typed
