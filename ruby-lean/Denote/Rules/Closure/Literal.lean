import Denote.Sem.Closure.Value
import Denote.Judgment.Context

/-! Actual lambda/proc literal execution. The absence premise is consumed at lookup,
so a user-defined Kernel selector cannot silently create a certified closure. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private theorem literal_unshadowed {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) {name : String} (hn : name ∈ shadowableNames)
    (hf : nameFreeN κ name = true) :
    (match Interp.methodOn m.heap (classOf m.heap m.currentFrame.self) name with
      | some (_, md) => md.builtin.isNone && !md.undefined
      | none => false) = false := by
  cases hl : Interp.methodOn m.heap (classOf m.heap m.currentFrame.self) name with
  | none => rfl
  | some p =>
    obtain ⟨owner, md⟩ := p
    have hh := hm.nameFree name hn _ (List.mem_cons_self) owner md hl
    rcases hh with hb | hu | hn
    · cases he : md.builtin <;> simp_all
    · simp [hu]
    · rw [hf] at hn; cases hn

/-- The literal's body is captured without evaluation, with full lambda/proc metadata.
This is a semantic step, not yet a callable type or an admitted judgment. -/
theorem closure_literal_step {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) (lam : Bool)
    (hf : nameFreeN κ (if lam then "lambda" else "proc") = true)
    (ps : List Ratchet.Param) (ls : List String) (body : Ratchet.Expr) :
    Interp.stepFn (evalFrom m (.send none (if lam then "lambda" else "proc") []
      (some (.block ps ls body)))) =
    .next (deliverA (.val (.ref m.heap.objs.size))
      (reifiedMachine m (toRubyParams ps) ls (toRuby body) lam) []) := by
  have hs := literal_unshadowed hm (name := if lam then "lambda" else "proc")
    (by cases lam <;> simp [shadowableNames]) hf
  cases hl : Interp.methodOn m.heap (classOf m.heap m.currentFrame.self)
      (if lam then "lambda" else "proc") with
  | none =>
    cases lam <;>
      change Interp.finishSend _ m.currentFrame.self .implicit _ [] (.lit _ _ _) [] = _
    all_goals
      simp only [Bool.false_eq_true, ↓reduceIte] at hl
      simp only [Interp.finishSend, evalFrom, Bool.false_eq_true, ↓reduceIte, hl]
      rfl
  | some p =>
    obtain ⟨owner, md⟩ := p
    have hb : (md.builtin.isNone && !md.undefined) = false := by simpa only [hl] using hs
    cases lam <;>
      change Interp.finishSend _ m.currentFrame.self .implicit _ [] (.lit _ _ _) [] = _
    all_goals
      simp only [Bool.false_eq_true, ↓reduceIte] at hl
      simp only [Interp.finishSend, evalFrom, Bool.false_eq_true, ↓reduceIte, hl, hb]
      rfl

/-- Full output conformance plus the exact code/capture descriptor at the fresh value. -/
theorem closure_literal_result {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) (lam : Bool)
    (hf : nameFreeN κ (if lam then "lambda" else "proc") = true)
    (ps : List Ratchet.Param) (ls : List String) (body : Ratchet.Expr) :
    ∃ n, Interp.stepFn (evalFrom m (.send none (if lam then "lambda" else "proc") []
        (some (.block ps ls body)))) = .next n ∧
      StateOk κ Γ I n ∧ Framed m n ∧
      procClosure? n.heap (.ref m.heap.objs.size) =
        some (reifiedClosure m (toRubyParams ps) ls (toRuby body) lam) := by
  refine ⟨_, closure_literal_step hm lam hf ps ls body,
    StateOk_deliverA (reified_state hm _ _ _ _), ?_, reified_payload m _ _ _ _⟩
  exact (Framed.of_ext (reified_ext hm _ _ _ _)).trans (Framed_reCtl _ _ _)

/-- Sorbet 0.6.13405 infers T.proc.returns(Integer) for lambda { 1 } (clink 200).
This semantic value contract additionally retains exact code and live capture types;
call safety still requires its own body/activation/return proof. -/
theorem SemSafeCtxA.closureLiteral {κ : Ctx} {Γ : Env} {I : Ty} (code : ClosureCode)
    (hf : nameFreeN κ (if code.lam then "lambda" else "proc") = true) :
    SemSafeCtxA κ Γ I (.send none (if code.lam then "lambda" else "proc") []
      (some (.block code.params code.locals code.body)))
      (.clos code (envToSpine Γ) (κ.selfTy.getD .never)) κ Γ I := by
  apply SemSafeCtxA.leaf
  intro m hm
  exact ⟨_, _, closure_literal_step hm code.lam hf code.params code.locals code.body,
    Framed.of_ext (reified_ext hm _ _ _ _), reified_den hm code,
    fun _ _ => reified_state hm _ _ _ _⟩

#print axioms SemSafeCtxA.closureLiteral
#print axioms closure_literal_step
#print axioms closure_literal_result

/-- Creating a literal cannot raise a type error, even when its uncalled body could. -/
theorem closure_literal_safe {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) (lam : Bool)
    (hf : nameFreeN κ (if lam then "lambda" else "proc") = true)
    (ps : List Ratchet.Param) (ls : List String) (body : Ratchet.Expr) :
    StuckFree m (.send none (if lam then "lambda" else "proc") [] (some (.block ps ls body))) := by
  have h : RunSpec m (evalFrom m (.send none (if lam then "lambda" else "proc") []
      (some (.block ps ls body)))) Γ .any κ I := by
    apply RunSpec.step rfl (closure_literal_step hm lam hf ps ls body)
    exact RunSpec.answer ⟨Framed.of_ext (reified_ext hm _ _ _ _),
      by simp [AnsOk, denM], fun _ _ => reified_state hm _ _ _ _⟩
  exact h.1

#print axioms closure_literal_safe
end Ratchet.Denote.Typed
