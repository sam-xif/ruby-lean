import Denote.Judgment.Context

/-! Instance-body reads at an arbitrary annotated context. No declaration is admitted
here: class installation, constructor effects, and dispatch still need their own proofs. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem denSpineFrom_get {m : Machine} {g : String → Value} {I τ : Ty} {x : String}
    {seen : List String} (h : denSpineFrom seen I m g) (hx : x ∉ seen)
    (hg : ivarGet? I x = some τ) : denM τ m (g x) := by
  induction I generalizing seen with
  | ivarCons y σ rest _ ih =>
    simp only [denSpineFrom] at h
    simp only [ivarGet?] at hg
    split at hg
    · rename_i heq
      have heq : y = x := beq_iff_eq.mp heq
      subst y
      cases Option.some.inj hg
      exact h.1.resolve_left hx
    · rename_i hne
      exact ih h.2 (by simpa [List.mem_cons, beq_iff_eq] using And.intro (Ne.symm (by
        simpa only [beq_iff_eq] using hne)) hx) hg
  | _ => simp [ivarGet?] at hg

theorem selfSpine_read {m : Machine} {I : Ty} {closed : Bool}
    (h : SelfSpineOk I m closed) (x : String) :
    denM ((ivarGet? I x).getD (if closed then .nilT else .any)) m
      (ivarOf m.heap m.currentFrame.self x) := by
  cases hg : ivarGet? I x with
  | none =>
    cases hc : closed with
    | false => simp [denM]
    | true => simp only [↓reduceIte, Option.getD_none]; rw [h.2 x hg hc]; simp [denM, isNilV]
  | some τ => exact denSpineFrom_get h.1 (by simp) hg

theorem stepFn_ivarRead (m : Machine) (x : String) :
    Interp.stepFn (evalFrom m (.var .ivar x)) =
      .next (deliverA (.val (ivarOf m.heap m.currentFrame.self x)) m []) := by
  change (match m.currentFrame.self with
    | .ref o => StepResult.next (deliverA (.val
        (((m.heap.get o).ivars.find? (fun p : String × Value => p.1 == x)).map
          (fun p : String × Value => p.2) |>.getD .nil)) m [])
    | _ => StepResult.next (deliverA (.val .nil) m [])) = _
  cases m.currentFrame.self <;> simp only [ivarOf] <;> try rfl
  rename_i o
  cases (m.heap.get o).ivars.find? (·.1 == x) <;> rfl

theorem SemSafeCtxA.ivarRead {κ : Ctx} {Γ : Env} {I : Ty} {x : String} :
    SemSafeCtxA κ Γ I (.var .ivar x) (κ.ivarReadTy I x) κ Γ I := by
  apply SemSafeCtxA.leaf
  intro m hm
  exact ⟨m, ivarOf m.heap m.currentFrame.self x, stepFn_ivarRead m x, .refl m,
    by simpa only [AnsOk, Ctx.ivarReadTy] using selfSpine_read hm.selfSpine x, fun _ _ => hm⟩

theorem SemSafeCtxA.selfRead {κ : Ctx} {Γ : Env} {I τ : Ty}
    (hs : κ.selfTy = some τ) : SemSafeCtxA κ Γ I .self' τ κ Γ I := by
  apply SemSafeCtxA.leaf
  intro m hm
  exact ⟨m, m.currentFrame.self, rfl, .refl m,
    by simpa only [AnsOk, SelfTyOk, hs] using hm.selfTy, fun _ _ => hm⟩

/-- A void/ignored result does not waive safety or the outgoing state obligations. -/
theorem SemSafeCtxA.ignoreResult {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {e : Ratchet.Expr}
    (h : SemSafeCtxA κ Γ I e τ κ' Γ' I') : SemSafeCtxA κ Γ I e .any κ' Γ' I' :=
  h.weaken (fun _ _ hm _ => ⟨hm, by simp [denM]⟩)

#print axioms SemSafeCtxA.ivarRead
#print axioms SemSafeCtxA.selfRead
#print axioms SemSafeCtxA.ignoreResult
end Ratchet.Denote.Typed
