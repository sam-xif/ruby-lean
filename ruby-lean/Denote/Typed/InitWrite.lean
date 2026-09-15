import Denote.Typed.InitExpr
import Denote.Sem.WriteStable

/-! Discharge every value-sensitive write obligation from executable type guards.
No special Integer environment and no empty-constant/block assumptions are needed.
-/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem InitState.bindIvar {anchor : Heap} {κ : Ctx} {Γ : Env} {I ρ : Ty}
    {m : Machine} {x : String} {v : Value} (hm : InitState anchor κ Γ I m)
    (hv : denM ρ m v) (ht : WriteTypes κ Γ I x ρ) :
    InitState anchor κ Γ (ivarSet I x ρ) (Interp.bindIvar m x v) ∧
      denM ρ (Interp.bindIvar m x v) v := by
  obtain ⟨o, ho, hfresh, hlive, hfrozen⟩ := hm.fresh
  have hv' := denM_writeStable (x := x) (v := v) ht.value hv
  have henv : EnvOk Γ (Interp.bindIvar m x v) := env_bindIvar hm.typed.env (by
    intro y τ hy
    obtain ⟨z, hz⟩ := envGet?_mem hy
    exact denM_writeStable (ht.locals (z, τ) hz) (hm.typed.env.1 y τ hy).1)
  have hspine : SelfSpineOk (ivarSet I x ρ) (Interp.bindIvar m x v) κ.scope.closedIvars :=
    selfSpine_bindIvar ho hlive hm.typed.selfSpine hv' (by
      intro y τ hne hy
      have hd := denSpineFrom_get hm.typed.selfSpine.1 (by simp) hy
      rw [ho] at hd
      exact denM_writeStable (ht.fields y τ hne hy) hd)
  have hc (y : String) (τ : Ty) (hy : envGet? κ.consts y = some τ) : IvarStable τ = true := by
    obtain ⟨z, hz⟩ := envGet?_mem hy
    exact ht.consts (z, τ) hz
  have hw := bindIvar_ivarOnly m x v
  have hlookup (k : ObjId) (name : String) :
      constLookupFrom (Interp.bindIvar m x v).heap k name = constLookupFrom m.heap k name := by
    simp only [constLookupFrom, hw.classPayload, hw.ancestors_eq]
  have hresolve (name : String) :
      constResolveAt (Interp.bindIvar m x v) name = constResolveAt m name := by
    simp only [constResolveAt, bindIvar_currentFrame, hw.constOwn_eq, hlookup]
  refine ⟨⟨StateOk_bindIvar hm.typed x v henv hspine ?_ ?_ ?_ ?_,
    hm.growth.bindIvar ho hfresh x v, ?_⟩, hv'⟩
  · cases hb : κ.blockTy with
    | none => simpa only [BlockTyOk, hb, bindIvar_currentFrame] using hm.typed.blockTy
    | some τ =>
      obtain ⟨w, hb', hd⟩ := (show ∃ w, m.currentFrame.blk = some w ∧ denM τ m w by
        simpa only [BlockTyOk, hb] using hm.typed.blockTy)
      exact ⟨w, by simpa only [bindIvar_currentFrame] using hb', denM_writeStable (ht.block τ hb) hd⟩
  · cases hs : κ.selfTy with
    | none => trivial
    | some τ =>
      have hd : denM τ m m.currentFrame.self := by simpa only [SelfTyOk, hs] using hm.typed.selfTy
      simpa only [SelfTyOk, hs, bindIvar_currentFrame] using denM_writeStable (x := x) (v := v) (ht.self τ hs) hd
  · intro name τ hn
    obtain ⟨path, hp⟩ := constGet?_entry hn
    obtain ⟨w, hw, hd⟩ := hm.typed.consts name τ hn
    exact ⟨w, by rw [hresolve]; exact hw, denM_writeStable (hc path τ hp) hd⟩
  · intro owner name τ k hn hk w hfound
    rw [bindIvar_classNamed] at hk
    rw [hlookup] at hfound
    exact denM_writeStable (hc _ τ hn) (hm.typed.constPaths owner name τ k hn hk w hfound)
  · exact ⟨o, by simpa only [bindIvar_currentFrame] using ho, hfresh,
      by simpa only [bindIvar_size] using hlive, by simpa only [hw.frozen] using hfrozen⟩

theorem SemInitA.ivarAsgnChecked {κ κ' : Ctx} {Γ Γ' : Env} {I I' ρ : Ty}
    {x : String} {e : Ratchet.Expr} (he : SemInitA κ Γ I e ρ κ' Γ' I')
    (hw : writeTypesB κ' Γ' I' x ρ = true) :
    SemInitA κ Γ I (.vasgn .ivar x e) ρ κ' Γ' (ivarSet I' x ρ) :=
  he.ivarAsgn (fun _ _ _ hm hv => hm.bindIvar hv (writeTypesB_sound hw))

#print axioms InitState.bindIvar
#print axioms SemInitA.ivarAsgnChecked
end Ratchet.Denote.Typed
