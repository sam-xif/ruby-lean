import Denote.Rules.Instance.InstanceImplicit
import Denote.Sem.Class.ClassGuards
import Denote.Sem.Names.NativeGuards

/-! The vcallMethodSig provider: a bare-name call to a declared instance method of self. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemSafeCtxA.vcallMethodSig {κ : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {c : Cls} {d : Defn}
    (hs : κ.selfTy = some (.inst c.name Ib)) (hc : c ∈ κ.classes) (hd : d ∈ c.methods)
    (hn : d.name ≠ "initialize") (hname : directCallNameB d.name = true) (hp : d.params = [])
    (hret : FirstOrder τ = true) (hself : FirstOrder Ib = true)
    (hb : SemSafeCtxA (instanceBodyCtx κ ⟨c.name, c.name, d.name, false⟩ Ib) [] Ib d.body τ
      (instanceBodyCtx κ ⟨c.name, c.name, d.name, false⟩ Ib) Γb Ib)
    (hg : instanceCallB κ Γ I = true) :
    SemSafeCtxA κ Γ I (.vcall d.name) τ κ Γ I := by
  simp only [instanceCallB, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨ht, hΓ⟩, hw⟩, hasms, hco⟩ := hg
  exact SemSafeCtxA.instanceVcall hs hc hd hn (directCallNameB_sound hname) hp hret hself hb
    (reframeTypesB_sound ht) hasms (callWorldB_sound hw)
    (fun x => (constGet?_empty (κ := instanceBodyCtx κ ⟨c.name, c.name, d.name, false⟩ Ib) hco x).trans
      (constGet?_empty hco x).symm) (List.all_eq_true.mp hΓ)

#print axioms SemSafeCtxA.vcallMethodSig
end Ratchet.Denote.Typed
