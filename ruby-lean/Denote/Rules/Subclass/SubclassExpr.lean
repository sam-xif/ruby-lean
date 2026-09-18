import Denote.Rules.Subclass.SubclassRun
import Denote.Sem.Class.ClassGuards

/-! The superclass is evaluated normally, with its outgoing context and locals threaded
into class creation. A checked body runs under the published subclass header, not under
the caller or a predeclared signature table. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemSafeCtxA.subclassVia {κ κ₁ κb : Ctx} {Γ Γ₁ Γb : Env} {I I₁ Ib τ : Ty}
    {c : Cls} {name : String} {super body : Ratchet.Expr}
    (hsuper : SemSafeCtxA κ Γ I super (.clsOf c.name) κ₁ Γ₁ I₁)
    (hc : c ∈ κ₁.classes)
    (ht : ReframeFO (returnScopeCtx κ₁ κb) I₁) (ha : κ₁.asms = [])
    (hr : κ₁.scope.runtimeMain = true) (hf : κ₁.frame = none)
    (hw : κb.pos.mainWorld = true) (hcl : κ₁.scope.runtimeClass = none)
    (hq : κb.scope.runtimeClass = some name)
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ₁ κb) x)
    (hΓ : ∀ p ∈ Γ₁, FirstOrder (stripAlias p.2) = true) (hτ : FirstOrder τ = true)
    (htables : plainClassTablesB κ₁ = true) (hnative : FreshClass.nativeFrameB κ₁ name = true)
    (hfresh : freshClassNameB κ₁ name = true) (hne : name.isEmpty = false)
    (hbase : subclassBaseFrameB κ₁ c.name = true)
    (halloc : c.name ∈ κ₁.pos.plainAlloc) (hquiet : FreshClass.NativeQuiet name "new")
    (hnew : smroGet? κ₁.classes c.name "new" = none)
    (hframe : subclassHeaderFrameB κ₁.classes name c.name = true)
    (hplain : unqualifiedClassB name = true)
    (hb : SemSafeCtxA (subclassHeaderCtx (classBodyCtx κ₁ name) name c.name) [] .ivar0 body τ κb Γb Ib) :
    SemSafeCtxA κ Γ I (.class' name (some super) body) τ (returnScopeCtx κ₁ κb) Γ₁ I₁ := by
  intro m hm
  apply RunSpec.step (by rfl)
    (show Interp.stepFn _ = .next (pushK [.classDefK name (toRuby body)] (evalFrom m super)) from rfl)
  apply (hsuper m hm).bindSpec (by intro k hk tag; simp only [List.mem_singleton] at hk; subst k; simp)
  intro a n result
  cases a with
  | val v =>
    have hn := result.2.2 v rfl
    obtain ⟨parent, hp, _⟩ := hn.classes c hc
    have hv : v = .ref parent := by
      have typed := result.2.1
      cases v <;> simp_all [AnsOk, denM, isClassRefNamed]
    subst v
    exact (Subclass.resolved_runSpec hn ht ha hr hf hw hcl hq hk hΓ hτ
      (plainClassTablesB_sound htables) hnative hfresh hne hc hp hbase halloc hquiet hnew hframe hplain hb).rebase result.1
  | esc j =>
    apply RunSpec.step (by rfl)
      (show Interp.stepFn _ = .next (deliverA (.esc j) n []) from by cases j <;> rfl)
    exact RunSpec.answer ⟨result.1, result.2.1, fun _ hv => by cases hv⟩

#print axioms SemSafeCtxA.subclassVia
end Ratchet.Denote.Typed
