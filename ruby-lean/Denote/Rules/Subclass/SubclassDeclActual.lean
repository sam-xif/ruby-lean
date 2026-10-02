import Denote.Rules.Subclass.SubclassActualRun
import Denote.Rules.Primitive.Primitive
import Denote.Sem.Class.ClassReach
import Denote.Sem.Class.ClassGuards
import Ratchet.Guards.SubclassRule

/-! The subclassDecl provider: the superclass expression evaluates to a declared,
plainly allocatable class; the actual subclass entry runs from its delivery. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemSafeCtxA.subclassDecl {κ κ₁ κb : Ctx} {Γ Γ₁ Γb : Env} {I I₁ Ib τ : Ty}
    {c : Cls} {name : String} {super body : Ratchet.Expr}
    (hs : SemSafeCtxA κ Γ I super (.clsOf c.name) κ₁ Γ₁ I₁) (hc : c ∈ κ₁.classes)
    (hb : SemSafeCtxA (subclassHeaderCtx (classBodyCtx κ₁ name) name c.name) [] .ivar0 body τ κb Γb Ib)
    (hg : subclassRuleB κ₁ κb Γ₁ I₁ τ name c.name = true) :
    SemSafeCtxA κ Γ I (.class' name (some super) body) τ (returnScopeCtx κ₁ κb) Γ₁ I₁ := by
  simp only [subclassRuleB, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    List.contains_iff_mem, Option.isNone_iff_eq_none] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ht, hΓ⟩, hτ⟩, ⟨ha, hr, hf, hw, hcl, hq, hco⟩⟩, htab⟩, hnative⟩, hfresh⟩, hne⟩,
    hreach⟩, halloc⟩, hquiet⟩, hnew⟩, hframe⟩, hplain⟩ := hg
  intro m hm
  apply RunSpec.step (answerPoint_evalFrom _ _)
    (show Interp.stepFn _ = .next (pushK [.classDefK name (toRuby body)] (evalFrom m super)) from rfl)
  apply (hs m hm).bindSpec hm.rootClean (by intro k hk; simp at hk; subst hk; rfl)
  intro a n hn
  cases a with
  | esc j =>
    apply RunSpec.step (by rfl)
      (show Interp.stepFn _ = .next (deliverA (.esc j) n []) from by cases j <;> rfl)
    exact RunSpec.answer ⟨hn.1, hn.2.1, fun _ hv => by cases hv⟩
  | val v =>
    have hn' := hn.2.2 v rfl
    have hv : isClassRefNamed n.heap v c.name = true := by simpa [AnsOk, denM] using hn.2.1
    unfold isClassRefNamed at hv
    cases hp : classNamed? n.heap c.name with
    | none => rw [hp] at hv; cases hv
    | some p =>
      cases v with
      | ref o =>
        rw [hp] at hv
        have ho : p = o := by simpa using hv
        subst ho
        exact (subclass_actual_runSpec hn' (reframeTypesB_sound ht) ha hr hf hw hcl hq
          (fun x => (constGet?_empty hco x).trans
            (constGet?_empty (κ := returnScopeCtx κ₁ κb) hco x).symm)
          (List.all_eq_true.mp hΓ) hτ (plainClassTablesB_sound htab)
          (classNativeFrameB_to_semB hnative) hfresh hne hquiet hplain hc hp halloc hnew
          (subclassHeaderFrameB_sound hframe) (hn'.classReach hreach) hb).rebase hn.1
      | _ => rw [hp] at hv; cases hv

#print axioms SemSafeCtxA.subclassDecl
end Ratchet.Denote.Typed
