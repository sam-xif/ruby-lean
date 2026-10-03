import Denote.Rules.Expr.BranchNarrow

/-! A send whose receiver is a union-typed local. The value is in one arm, so the send is
typed once per arm (each arm resolving the message its own way) and the results joined.
No machine step is taken: this is union elimination on the receiver's binding. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemSafeCtxA.sendUnion {κ κ' : Ctx} {Γ Γ₁ Γ₂ : Env} {I I' : Ty} {x name : String}
    {σ₁ σ₂ τ₁ τ₂ : Ty} {args : List Ratchet.Expr} {blk : Option Ratchet.Expr}
    (hx : envGet? Γ x = some (.union σ₁ σ₂))
    (ha₁ : isAliasTy σ₁ = false) (ha₂ : isAliasTy σ₂ = false)
    (h₁ : SemSafeCtxA κ (envSet Γ x σ₁) I (.send (some (.var .lvar x)) name args blk) τ₁ κ' Γ₁ I')
    (h₂ : SemSafeCtxA κ (envSet Γ x σ₂) I (.send (some (.var .lvar x)) name args blk) τ₂ κ' Γ₂ I') :
    SemSafeCtxA κ Γ I (.send (some (.var .lvar x)) name args blk) (joinT τ₁ τ₂) κ'
      (joinEnv Γ₁ Γ₂) I' := by
  intro m hm
  have hv : denM (.union σ₁ σ₂) m (m.getLocal x) := (hm.env.1 x _ hx).1
  simp only [denM] at hv
  rcases hv with hv | hv
  · exact (h₁.weaken (fun _ _ hm hd => ⟨StateOk_joinEnv true hm, denM_joinT_left hd⟩)) m
      { hm with env := envOk_refine hm.env hx hv ha₁ }
  · exact (h₂.weaken (fun _ _ hm hd => ⟨StateOk_joinEnv false hm, denM_joinT_right hd⟩)) m
      { hm with env := envOk_refine hm.env hx hv ha₂ }

#print axioms SemSafeCtxA.sendUnion
end Ratchet.Denote.Typed
