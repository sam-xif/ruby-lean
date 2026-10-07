import Books.TypeSoundness.Judgment.RunWith
import Books.TypeSoundness.Judgment.Context
import Books.TypeSoundness.Conformance.Closure.LocalFacts

/-! Mutable local facts are an expression input/output index, separate from lexical
scope and monotone declarations. A result origin is checked before assignment records it. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

def FlowPost (facts : LocalFacts) (current : Bool) (v : Value) (m : Machine) : Prop :=
  LocalFactsOk facts m ∧ (current = true → CurrentProc m v)

theorem FlowPost.reCtl {facts : LocalFacts} {current : Bool} {v : Value} {m : Machine}
    (h : FlowPost facts current v m) (c : Ctl) (k : List Kont) :
    FlowPost facts current v (reCtl m c k) :=
  ⟨h.1.ext (Ext_toReCtl m c k), fun hc => (h.2 hc).ext (Ext_toReCtl m c k)⟩

def SemFlow (κ : Ctx) (Γ : Env) (I : Ty) (facts : LocalFacts)
    (e : Checker.Expr) (τ : Ty) (current : Bool)
    (κ' : Ctx) (Γ' : Env) (I' : Ty) (out : LocalFacts) : Prop :=
  ∀ m, StateOk κ Γ I m → LocalFactsOk facts m →
    RunWith m (evalFrom m e) Γ' τ κ' I' (FlowPost out current)

theorem SemFlow.erase {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {e : Checker.Expr}
    {current : Bool} {out : LocalFacts}
    (h : SemFlow κ Γ I .unknown e τ current κ' Γ' I' out) :
    SemSafeCtxA κ Γ I e τ κ' Γ' I' :=
  fun m hm => (h m hm (.unknown m)).erase

/-- An ordinary certified expression loses origins and the exact slot domain. The
shared framing contract retains already bound slots even through unknown effects. -/
theorem SemFlow.embed {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {e : Checker.Expr}
    (facts : LocalFacts) (h : SemSafeCtxA κ Γ I e τ κ' Γ' I') :
    SemFlow κ Γ I facts e τ false κ' Γ' I' facts.afterEffect := by
  intro m hm hf
  exact (h m hm).withPost
    (fun _ _ hr => ⟨hf.afterEffect hm.frameInRange.2 hr.1, by intro h; cases h⟩)

theorem SemFlow.leaf {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {e : Checker.Expr}
    {facts out : LocalFacts} {current : Bool}
    (h : ∀ m, StateOk κ Γ I m → LocalFactsOk facts m → ∃ n v,
      Interp.stepFn (evalFrom m e) = .next (deliverA (.val v) n []) ∧
      ResultOk m Γ' τ (.val v) n κ' I' ∧ FlowPost out current v n) :
    SemFlow κ Γ I facts e τ current κ' Γ' I' out := by
  intro m hm hf
  obtain ⟨n, v, hs, hr, hp⟩ := h m hm hf
  exact RunWith.step (answerPoint_evalFrom _ _) hs
    (RunWith.answer (fun _ _ c k hp => hp.reCtl c k) ⟨hr, fun _ he => by cases he; exact hp⟩)

theorem SemFlow.intLit {κ : Ctx} {Γ : Env} {I : Ty} (facts : LocalFacts) (n : Int) :
    SemFlow κ Γ I facts (.int n) .int false κ Γ I facts := by
  apply SemFlow.leaf
  intro m hm hf
  exact ⟨m, .int n, rfl, ⟨.refl m, by simp [AnsOk, denM, isIntV], fun _ _ => hm⟩,
    hf, by intro h; cases h⟩

theorem SemFlow.var {κ : Ctx} {Γ : Env} {I τ : Ty} {x : String} (facts : LocalFacts)
    (hg : envGet? Γ x = some τ) (ha : isAliasTy τ = false) :
    SemFlow κ Γ I facts (.var .lvar x) τ (facts.currentProcs.contains x) κ Γ I facts := by
  apply SemFlow.leaf
  intro m hm hf
  exact ⟨m, m.getLocal x, stepFn_var m x,
    ⟨.refl m, denM_getLocal hm hg ha, fun _ _ => hm⟩,
    hf, fun hx => hf.currentProcs x (by simpa using hx)⟩

#print axioms SemFlow.erase
#print axioms SemFlow.var
end Checker.Soundness.Typed
