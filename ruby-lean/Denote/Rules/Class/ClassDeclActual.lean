import Denote.Rules.Class.ClassRunActual
import Denote.Sem.Class.ClassReach
import Denote.Sem.Class.ClassGuards

/-! The classDecl provider over the actual registration/callback semantics. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemSafeCtxA.classDecl {κ κb : Ctx} {Γ Γb : Env} {I Ib τ : Ty}
    {name : String} {body : Ratchet.Expr}
    (hb : SemSafeCtxA (classHeaderCtx (classBodyCtx κ name) name) [] .ivar0 body τ κb Γb Ib)
    (hg : classRuleB κ κb Γ I τ name = true) :
    SemSafeCtxA κ Γ I (.class' name none body) τ (returnScopeCtx κ κb) Γ I := by
  simp only [classRuleB, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ht, hΓ⟩, hτ⟩, ha, hr, hf, hin, hw, hcl, hq, hco⟩,
    htab⟩, hnative⟩, hfresh⟩, hne⟩, hnew⟩, hquiet⟩, hplain⟩, hframe⟩, hreach⟩ := hg
  intro m hm
  exact class_actual_runSpec hm (reframeTypesB_sound ht) ha hr hf hin hw hcl hq
    (fun x => (constGet?_empty hco x).trans
      (constGet?_empty (κ := returnScopeCtx κ κb) hco x).symm)
    (List.all_eq_true.mp hΓ) hτ (plainClassTablesB_sound htab)
    (classNativeFrameB_to_semB hnative) hfresh hne hnew hquiet hplain hframe
    (hm.classReach hreach) hb

#print axioms SemSafeCtxA.classDecl
end Ratchet.Denote.Typed
