import Ratchet.Guards.ModuleGuards
import Denote.Rules.Module.ModuleRunActual
import Denote.Sem.Class.ClassReach
import Denote.Sem.Class.ClassGuards

/-! The moduleDecl provider over the actual registration/const_added semantics. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

/-- Sorbet 0.6.13405 accepts fresh module scopes and rejects reading an outer local
from them (clink 195). It reports NilClass for a module expression ending in 7;
CRuby 4.0.5 returns 7. Retain the proved body result, never Sorbet's erased result. -/
theorem SemSafeCtxA.moduleDecl {κ κb : Ctx} {Γ Γb : Env} {I Ib τ : Ty}
    {name : String} {body : Ratchet.Expr}
    (hb : SemSafeCtxA (moduleHeaderCtx (moduleBodyCtx κ name) name) [] .ivar0 body τ κb Γb Ib)
    (hg : moduleRuleB κ κb Γ I τ name = true) :
    SemSafeCtxA κ Γ I (.module' name body) τ (returnScopeCtx κ κb) Γ I := by
  simp only [moduleRuleB, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ht, hΓ⟩, hτ⟩, ha, hr, hf, hw, hcl, hq, hco⟩,
    htab⟩, hnative⟩, hfresh⟩, hne⟩, hplain⟩, hframe⟩, hreach⟩ := hg
  intro m hm
  exact module_actual_runSpec hm (reframeTypesB_sound ht) ha hr hf hw hcl hq
    (fun x => (constGet?_empty hco x).trans
      (constGet?_empty (κ := returnScopeCtx κ κb) hco x).symm)
    (List.all_eq_true.mp hΓ) hτ (plainClassTablesB_sound htab)
    (classNativeFrameB_to_semB hnative) hfresh hne hplain hframe (hm.classReach hreach) hb

#print axioms SemSafeCtxA.moduleDecl
end Ratchet.Denote.Typed
