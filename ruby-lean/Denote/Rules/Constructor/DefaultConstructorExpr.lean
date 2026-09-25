import Denote.Rules.Constructor.DefaultConstructor
import Denote.Rules.Expr.Send
import Denote.Sem.Class.ClassGuards

/-! Default construction uses the real builtin allocator. Receiver and argument evaluation
thread the full context; absence and allocation guards are checked at the final context. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemSafeCtxA.newDefault {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ : Ty}
    {c : Cls} {recv : Ratchet.Expr} {args : List Ratchet.Expr}
    (hr : SemSafeCtxA κ Γ I recv (.clsOf c.name) κ₁ Γ₁ I₁)
    (ha : SemAllCtxA κ₁ Γ₁ I₁ args [] κ₂ Γ₂ I₂)
    (hs : explicitReceiverB recv = true) (hc : c ∈ κ₂.classes)
    (hnew : smroGet? κ₂.classes c.name "new" = none) (halloc : c.name ∈ κ₂.pos.plainAlloc)
    (hprefix : noDeclaredSelectorB κ₂.classes c.name "initialize" = true)
    (hroot : rootInitFreeB κ₂.defs = true) :
    SemSafeCtxA κ Γ I (.send (some recv) "new" args none) (.inst c.name .ivar0) κ₂ Γ₂ I₂ := by
  apply hr.sendVia ha (explicitReceiverB_sound hs) rfl (by simp)
  intro m hm hk recv hv args hargs
  have he : args = [] := by simpa using denAll_length hargs
  subst args
  obtain ⟨k, hn, _⟩ := hm.classes c hc
  have he : recv = .ref k := by cases recv <;> simp_all [denM, isClassRefNamed]
  rw [he]
  exact declared_default_constructor hm hc hn halloc hnew hprefix hroot hk

#print axioms SemSafeCtxA.newDefault
end Ratchet.Denote.Typed
