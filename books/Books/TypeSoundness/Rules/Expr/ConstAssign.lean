import Books.TypeSoundness.Conformance.Heap.ConstAddState
import Books.TypeSoundness.Conformance.Instance.ClassHookDispatch
import Books.TypeSoundness.Conformance.Class.ClassGuards
import Books.TypeSoundness.Judgment.Context
import Books.TypeSoundness.Rules.Class.ClassConstant

/-! Top-level `N = e` with a non-class value: Object's table gains `N`, Object's native
const_added runs, and the assignment yields the value. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem nonClass_of_den {τ : Ty} {m : Machine} {v : Value} (hc : constValTyB τ = true)
    (hv : denM τ m v) : ConstAdd.NonClassVal m.heap v := by
  intro o ho
  subst ho
  have hp : ∀ c, (m.heap.get o).payload ≠ .cls c := by
    intro c hpc
    cases τ <;> simp [constValTyB] at hc <;>
      simp [denM, isIntV, isBoolV, isNilV, isSymV, isFltV, arrElems?, hshEntries?, hpc] at hv
  refine ⟨?_, ?_⟩
  · unfold Heap.classPayload?
    split
    · rename_i c h; exact absurd h (hp c)
    · rfl
  · apply Nat.lt_of_not_le
    intro hle
    have hd := get_oob m.heap hle
    have hdp : (default : Object).payload = .none := rfl
    cases τ <;> simp [constValTyB] at hc <;>
      simp [denM, isIntV, isBoolV, isNilV, isSymV, isFltV, arrElems?, hshEntries?, hd, hdp] at hv <;>
      cases hv

theorem SemSafeCtxA.casgnTop {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {n : String}
    {e : Checker.Expr} (h : SemSafeCtxA κ Γ I e τ κ' Γ' I') (hg : casgnTopB κ' Γ' I' τ n = true) :
    SemSafeCtxA κ Γ I (.casgn n e) τ (constAddCtx κ' n τ) Γ' I' := by
  simp only [casgnTopB, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨hcv, hτfo⟩, hloc⟩, hrf⟩, ha, hrm, hfr, hrc, hst, hbt, hcls, hco, hgl, hres, hcolon⟩ := hg
  have hIfo : FirstOrder I' = true := by
    simp only [reframeTypesB, Bool.and_eq_true] at hrf; exact hrf.1.1.1
  have hΓ : ∀ p ∈ Γ', FirstOrder (stripAlias p.2) = true := fun p hp =>
    List.all_eq_true.mp hloc p hp
  intro m hm
  apply RunSpec.step (answerPoint_evalFrom _ _)
    (show Interp.stepFn (evalFrom m (.casgn n e)) = .next (pushK [.casgnK n] (evalFrom m e)) from rfl)
  apply (h m hm).bindSpec hm.rootClean (by intro c hc; simp at hc; subst hc; rfl)
  intro a n0 hr
  cases a with
  | esc j =>
    apply RunSpec.step (by rfl)
      (show Interp.stepFn (deliverA (.esc j) n0 [.casgnK n]) = .next (deliverA (.esc j) n0 []) from by
        cases j <;> rfl)
    exact RunSpec.answer ⟨hr.1, hr.2.1, fun _ hv => by cases hv⟩
  | val v =>
    let B := reCtl n0 (.value v) []
    have hBs : StateOk κ' Γ' I' B := StateOk_reCtl (hr.2.2 v rfl) _ _
    have hBd : denM τ B v := denM_reCtl.mpr hr.2.1
    have hmain := hBs.runtime hrm
    have hO := hmain.classLive
    have hfresh := ConstAdd.fresh_of_global hBs.globalConsts hgl
    have hnc := nonClass_of_den hcv hBd
    have hc := hBs.core.classReady.chains
    have hb := hBs.core.basicSelf
    let H := constSetIn B.heap Boot.objectId n v
    let A : Machine := { B with heap := H, kont := [.newK v] }
    have hname : Interp.nameConstant (constSetIn B.heap Boot.objectId n v) Boot.objectId n v =
        .ok (constSetIn B.heap Boot.objectId n v) := by
      cases v with
      | ref o =>
        have hp : (constSetIn B.heap Boot.objectId n (.ref o)).classPayload? o = none := by
          unfold Heap.classPayload?
          rw [ConstAdd.get_nonclass (hnc o rfl).1]
          have := (hnc o rfl).1
          unfold Heap.classPayload? at this
          exact this
        simp [Interp.nameConstant, hp]
      | _ => rfl
    have h1 : Interp.stepFn (deliverA (.val v) n0 [.casgnK n]) =
        .next { A with ctl := .send (.ref Boot.objectId) .reflective "const_added" [.sym n] none [] } := by
      change Interp.assignConstant B B.lexicalNamespace n v = _
      have hl : B.lexicalNamespace = Boot.objectId := by
        simp only [Machine.lexicalNamespace, hmain.cref, List.headD_nil]
      rw [hl]
      simp only [Interp.assignConstant, hmain.unfrozen, Bool.false_eq_true, ↓reduceIte, hname,
        Interp.callConstAdded, hmain.phase]
      congr 1
      simp only [A, H, hmain.phase]
      congr 1
    apply RunSpec.step (by rfl) h1
    have hmA := ConstAdd.mainReady hmain hO hfresh hnc
    obtain hs | ⟨msg, hs⟩ := stepFn_class_hook (m := A) (arg := .sym n)
      (by simp [classHookNames] : ("const_added", "Module#const_added") ∈ classHookNames)
      hmA.classHooks (RubyCore.Proof.chainsIn_constSetIn hc) hmA.classLive
    · apply RunSpec.step (show answerPoint _ = none from rfl) hs
      apply RunSpec.step (show answerPoint _ = none from rfl)
        (show Interp.stepFn { A with ctl := .value .nil } =
          .next (deliverA (.val v) { B with heap := H } []) from rfl)
      have hfr' : Framed B (deliverA (.val v) { B with heap := H } []) :=
        ConstAdd.framed hc hb hO hfresh hnc rfl rfl rfl rfl (fun h => h)
      exact RunSpec.answer ⟨hr.1.trans ((Framed_reCtl n0 _ []).trans hfr'),
        (ConstAdd.dataPres hc hb hO hfresh hnc).denM hτfo hBd,
        fun _ _ => ConstAdd.state hBs hrm hcls hco hfr hrc hst hbt ha hgl hres hcolon hnc hBd
          hτfo hΓ hIfo⟩
    · exact RunSpec.unsupported (show answerPoint _ = none from rfl) hs

theorem SemSafeCtxA.constRead {κ : Ctx} {Γ : Env} {I τ : Ty} {n : String}
    (hc : constGet? κ n = some τ) : SemSafeCtxA κ Γ I (.const n) τ κ Γ I := by
  apply SemSafeCtxA.leaf
  intro m hm
  obtain ⟨v, hr, hv⟩ := hm.consts n τ hc
  refine ⟨m, v, ?_, .refl m, ?_, fun _ _ => hm⟩
  · have hr' : Interp.lexicalConstant (evalFrom m (.const n)) n = some v := hr
    change (match Interp.lexicalConstant (evalFrom m (.const n)) n with
      | some v => StepResult.next (Interp.withCtl (evalFrom m (.const n)) (.value v))
      | none => _) = _
    rw [hr']
    rfl
  · exact hv

#print axioms nonClass_of_den
#print axioms SemSafeCtxA.casgnTop
#print axioms SemSafeCtxA.constRead
end Checker.Soundness.Typed
