import Denote.Sem.Heap.ScalarState
import Denote.Rules.Primitive.PrimitiveAlloc
import Denote.Rules.Instance.InstanceRead
import Denote.Sem.Class.ClassGuards

/-! Ordinary field replacement within a homogeneous scalar domain. A frozen receiver
raises the real FrozenError, whose ancestry the boot conformance gate checks. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem scalar_write_run {κ : Ctx} {Γ : Env} {I ρ : Ty} {m : Machine}
    {o : ObjId} {x : String} {v : Value} (hm : StateOk κ Γ I m) (ht : ReframeFO κ I)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) (hρ : FirstOrder ρ = true)
    (hs : m.currentFrame.self = .ref o) (hv : denM ρ m v)
    (hρs : scalarWriteB ρ = true) (hold : denM ρ m (ivarOf m.heap (.ref o) x))
    (he : ScalarEq (ivarOf m.heap (.ref o) x) v) :
    RunSpec m (deliverA (.val v) m [.asgnK .ivar x]) Γ ρ κ I := by
  let n := deliverA (.val v) m []
  have hn : StateOk κ Γ I n := StateOk_reCtl hm _ []
  have hs' : n.currentFrame.self = .ref o := hs
  apply RunSpec.rebase (middle := n) ?_ (Framed_reCtl m _ [])
  apply RunSpec.of_stepSpec (by rfl)
  simp only [Interp.stepFn, deliverA, Answer.ctl, Interp.applyKont]
  change StepSpec n Γ ρ (match m.currentFrame.self with | .ref o => _ | _ => _) κ I
  rw [hs]
  cases hfrozen : (m.heap.get o).frozen with
  | false =>
    simp only [hfrozen, Bool.false_eq_true, ↓reduceIte]
    have hfr := Framed.bindIvar_scalar (m := n) hs' (hn.selfLive o hs') he
    have hn' := hn.bindIvar_scalar ht hΓ hs' he hfrozen
    have hv' := hfr.firstOrder ρ hρ v ((denM_heap_only (m₁ := m) (m₂ := n) hρ rfl).mp hv)
    exact (stepSpec_value hn' (by simp only [Interp.bindIvar, hs']; rfl) hv').rebase hfr
  | true =>
    have hne : (m.heap.get o).ivars ≠ [] := by
      intro hnil
      have hn : ivarOf m.heap (.ref o) x = .nil := by simp [ivarOf, hnil]
      rw [hn] at hold
      cases ρ <;> simp_all [scalarWriteB, denM, isIntV, isFltV, isSymV]
    exact absurd (hm.frozenFields o hfrozen) hne

/-- Sorbet 0.6.13405 accepts 074's Integer replacement, also Float/Symbol variants, and
rejects String replacement and a nullable Integer arithmetic domain (clink 186).
Boolean replacement needs weaker retained observations: TrueClass distinguishes true. -/
theorem SemSafeCtxA.scalarIvarAsgn {κ κ' : Ctx} {Γ Γ' : Env} {I I' ρ : Ty}
    {cn x : String} {e : Ratchet.Expr}
    (he : SemSafeCtxA κ Γ I e ρ κ' Γ' I')
    (hs : κ'.selfTy = some (.inst cn I')) (hx : ivarGet? I' x = some ρ)
    (hρ : scalarWriteB ρ = true) (ht : reframeTypesB κ' I' = true)
    (hΓ : localTypesB Γ' = true) :
    SemSafeCtxA κ Γ I (.vasgn .ivar x e) ρ κ' Γ' I' := by
  intro m hm
  apply RunSpec.step (by rfl)
    (show Interp.stepFn _ = .next (pushK [.asgnK .ivar x] (evalFrom m e)) from rfl)
  apply (he m hm).bindSpec hm.rootClean
    (by intro k hk; simp only [List.mem_singleton] at hk; subst hk; rfl)
  intro a n hr
  cases a with
  | val v =>
    have hn := hr.2.2 v rfl
    have hself : denM (.inst cn I') n n.currentFrame.self := by
      simpa only [SelfTyOk, hs] using hn.selfTy
    have href : ∃ o, n.currentFrame.self = .ref o := by
      cases hv : n.currentFrame.self <;> first
        | exact ⟨_, rfl⟩
        | (cases hn : classNamed? n.heap cn <;> simp [denM, isExactInst, hv, hn] at hself)
    obtain ⟨o, ho⟩ := href
    have hold : denM ρ n (ivarOf n.heap (.ref o) x) := by
      simpa only [ho] using denSpineFrom_get hn.selfSpine.1 (by simp) hx
    have hfo : FirstOrder ρ = true := by cases ρ <;> cases hρ <;> rfl
    exact (scalar_write_run hn (reframeTypesB_sound ht) (List.all_eq_true.mp hΓ) hfo ho hr.2.1
      hρ hold (scalarWriteB_values hρ hold hr.2.1)).rebase hr.1
  | esc j =>
    apply RunSpec.step (by rfl)
      (show Interp.stepFn _ = .next (deliverA (.esc j) n []) from by
        cases j <;> simp [Interp.stepFn, deliverA, Answer.ctl, Interp.unwind, Interp.withCtl])
    exact RunSpec.answer ⟨hr.1, hr.2.1, fun _ h => by cases h⟩

#print axioms scalar_write_run
#print axioms SemSafeCtxA.scalarIvarAsgn
end Ratchet.Denote.Typed
