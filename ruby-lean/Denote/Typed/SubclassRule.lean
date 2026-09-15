import Ratchet.SubclassRule
import Denote.Typed.SubclassExpr
import Denote.Sem.NativeGuards

/-! Class/body-generic semantic rule with only syntax/type side conditions. It is not yet
a DJudge constructor: inherited annotation-body cache checking still precedes admission. -/
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
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ht, hΓ⟩, hτ⟩, ⟨ha, hr, hf, hw, hcl, hq, hco⟩⟩, htab⟩, hnative⟩, hfresh⟩, hne⟩, hbase⟩, halloc⟩, hquiet⟩, hnew⟩, hframe⟩, hplain⟩ := hg
  exact hs.subclassVia hc (reframeTypesB_sound ht) ha hr hf hw hcl hq
    (fun x => (constGet?_empty hco x).trans (constGet?_empty (κ := returnScopeCtx κ₁ κb) hco x).symm)
    (List.all_eq_true.mp hΓ) hτ htab (classNativeFrameB_to_semB hnative) hfresh hne hbase halloc
    (classNativeQuietB_sound hquiet) hnew hframe hplain hb

#print axioms SemSafeCtxA.subclassDecl
end Ratchet.Denote.Typed
