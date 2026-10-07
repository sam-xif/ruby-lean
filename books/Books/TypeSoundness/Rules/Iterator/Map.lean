import Books.TypeSoundness.Rules.Iterator.FrameReturn
import Books.TypeSoundness.Rules.Closure.Return
import Books.TypeSoundness.Judgment.BoundedRun
import Books.TypeSoundness.Rules.Primitive.PrimitiveStep

/-! Array#map/collect use a live cursor and collect each body result (model L274).
Sorbet 0.6.13405 gives Array[Integer]#map Integer→String the result Array[String],
and rejects captured type changes (clink 228). Fuel induction permits growing input;
the invariant tracks the accumulated values and the caller below the iterator. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

def mapArrayStep (m : Machine) (cl : Closure) (brk o : ObjId) (index : Nat) (acc : List Value) : StepResult :=
  Interp.iterStep { m with kont := [.frameK brk] } cl brk [] (.arrayMap o index) acc .nil

theorem mapArrayStep_more (m : Machine) (cl : Closure) (brk o : ObjId) (index : Nat) (acc : List Value)
    (xs : Array Value) (name : String) (e : Checker.Expr)
    (hx : (m.heap.get o).payload = .arr xs) (hi : index < xs.size)
    (hp : cl.params = [.req name]) (he : cl.body = toRuby e)
    (henum : cl.enumYield = none) (hfor : cl.forTargets = none) :
    mapArrayStep m cl brk o index acc = .next
      (pushK [.blkFrameK m.frames.size cl.lam (closureBrk m cl (some brk)) cl [xs[index]],
        .iterK cl brk [] (.arrayMap o (index + 1)) acc .nil xs[index], .frameK brk]
        (evalFrom (pushMethodFrame m (requiredClosureFrame m cl [name] [xs[index]])) e)) := by
  unfold mapArrayStep Interp.iterStep
  simp only [hx, hi, ↓reduceDIte]
  rw [callClosure_required _ cl [name] [xs[index]] _ none none hp rfl henum hfor, he]
  simp only [requiredClosureFrame, definitionFrameId_reCtl]
  rfl

theorem mapArrayStep_end (m : Machine) (cl : Closure) (brk o : ObjId) (index : Nat) (acc : List Value)
    (xs : Array Value) (hx : (m.heap.get o).payload = .arr xs) (hi : ¬ index < xs.size) :
    mapArrayStep m cl brk o index acc = .next (deliverA (.val (Builtins.allocArr m acc.toArray).1)
      (Builtins.allocArr m acc.toArray).2 [.frameK brk]) := by
  simp only [mapArrayStep, Interp.iterStep, hx, hi, ↓reduceDIte]
  rfl

/-- The loop invariant includes the captured caller, receiver, cursor and accumulated
results. Each body sees a fresh live element. Neither the length nor the payload
is required to stay equal to its entry value. Only raises may escape a certified body. -/
structure MapArrayContract (origin : Machine) (cl : Closure) (name : String)
    (e : Checker.Expr) (o : ObjId) (P : Machine → Nat → List Value → Prop)
    (Γ : Env) (τ : Ty) (κ : Ctx) (I : Ty) (Γb : Env) (ρ : Ty) (κb : Ctx) (Ib : Ty) : Prop where
  params : cl.params = [.req name]
  code : cl.body = toRuby e
  enumNone : cl.enumYield = none
  forNone : cl.forTargets = none
  root : ∀ m i acc, P m i acc → RootClean m
  array : ∀ m i acc, P m i acc → ∃ xs, (m.heap.get o).payload = .arr xs
  body : ∀ m i acc, P m i acc → ∀ xs, (m.heap.get o).payload = .arr xs → ∀ hi : i < xs.size,
    RunSpec (pushMethodFrame m (requiredClosureFrame m cl [name] [xs[i]]))
      (evalFrom (pushMethodFrame m (requiredClosureFrame m cl [name] [xs[i]])) e) Γb ρ κb Ib
  next : ∀ m i acc, P m i acc → ∀ xs, (m.heap.get o).payload = .arr xs → ∀ hi : i < xs.size, ∀ v n,
    ResultOk (pushMethodFrame m (requiredClosureFrame m cl [name] [xs[i]])) Γb ρ (.val v) n κb Ib →
    P (deliverA (.val v) (popMethodFrame n) []) (i + 1) (acc ++ [v])
  done : ∀ m i acc, P m i acc → ResultOk origin Γ τ
    (.val (Builtins.allocArr m acc.toArray).1) (popMethodFrame (Builtins.allocArr m acc.toArray).2) κ I
  escape : ∀ m i acc, P m i acc → ∀ xs, (m.heap.get o).payload = .arr xs → ∀ hi : i < xs.size, ∀ j n,
    ResultOk (pushMethodFrame m (requiredClosureFrame m cl [name] [xs[i]])) Γb ρ (.esc j) n κb Ib →
    ResultOk origin Γ τ (.esc j) (popMethodFrame (popMethodFrame n)) κ I

theorem mapArrayStep_specAt {origin : Machine} {cl : Closure} {name : String}
    {e : Checker.Expr} {o : ObjId} {P : Machine → Nat → List Value → Prop}
    {Γ Γb : Env} {τ ρ I Ib : Ty} {κ κb : Ctx}
    (h : MapArrayContract origin cl name e o P Γ τ κ I Γb ρ κb Ib)
    (brk : FrameId) (N : Nat) (m : Machine) (index : Nat) (acc : List Value) (hm : P m index acc) :
    StepSpecAt N origin Γ τ (mapArrayStep m cl brk o index acc) κ I := by
  induction N generalizing m index acc with
  | zero =>
    obtain ⟨xs, hx⟩ := h.array m index acc hm
    by_cases hi : index < xs.size
    · rw [mapArrayStep_more m cl brk o index acc xs name e hx hi h.params h.code h.enumNone h.forNone]
      exact RunSpecAt.zero (by rfl)
    · rw [mapArrayStep_end m cl brk o index acc xs hx hi]
      exact RunSpecAt.zero (by rfl)
  | succ N ih =>
    obtain ⟨xs, hx⟩ := h.array m index acc hm
    by_cases hi : index < xs.size
    · rw [mapArrayStep_more m cl brk o index acc xs name e hx hi h.params h.code h.enumNone h.forNone]
      apply ((h.body m index acc hm xs hx hi).at (N + 1)).bindSpec (h.root m index acc hm) (by
        intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> rfl)
      intro a n hn
      cases a with
      | val v =>
        apply RunSpecAt.step (by rfl) (step_blkFrameK_value n _ cl.lam (closureBrk m cl (some brk)) cl [xs[index]] v)
        apply RunSpecAt.of_stepSpecWithin (by rfl)
        exact ih (deliverA (.val v) (popMethodFrame n) []) (index + 1) (acc ++ [v])
          (h.next m index acc hm xs hx hi v n hn)
      | esc j =>
        obtain ⟨exc, rfl, _⟩ := hn.2.1.only_raise
        apply RunSpecAt.stepWithin (by rfl) (show Interp.stepFn _ = .next _ from rfl)
        apply RunSpecAt.stepWithin (by rfl) (show Interp.stepFn _ = .next _ from rfl)
        apply RunSpecAt.stepWithin (by rfl) (show Interp.stepFn _ = .next _ from rfl)
        exact RunSpecAt.answer (h.escape m index acc hm xs hx hi (.raiseJ exc) n hn)
    · rw [mapArrayStep_end m cl brk o index acc xs hx hi]
      apply RunSpecAt.stepWithin (by rfl) (show Interp.stepFn _ = .next _ from rfl)
      exact RunSpecAt.answer (h.done m index acc hm)

theorem mapArrayStep_spec {origin : Machine} {cl : Closure} {name : String}
    {e : Checker.Expr} {o : ObjId} {P : Machine → Nat → List Value → Prop}
    {Γ Γb : Env} {τ ρ I Ib : Ty} {κ κb : Ctx}
    (h : MapArrayContract origin cl name e o P Γ τ κ I Γb ρ κb Ib)
    (brk : FrameId) (m : Machine) (index : Nat) (acc : List Value) (hm : P m index acc) :
    StepSpec origin Γ τ (mapArrayStep m cl brk o index acc) κ I := by
  have hall := fun N => mapArrayStep_specAt h brk N m index acc hm
  cases hs : mapArrayStep m cl brk o index acc with
  | next n =>
    apply runSpec_iff_allAt.mpr
    intro N
    simpa only [hs, StepSpecAt] using hall N
  | unsupported _ => trivial
  | done v n => simpa only [hs, StepSpecAt] using hall 0
  | uncaught v n => simpa only [hs, StepSpecAt] using hall 0
  | stuck msg => simpa only [hs, StepSpecAt] using hall 0

#print axioms mapArrayStep_more
#print axioms mapArrayStep_spec
end Checker.Soundness.Typed
