import Denote.Rules.Method.MethodDefine
import Denote.Judgment.MethodRules

/-! Installation does not execute a body. Admission nevertheless requires its uniform
signature-domain proof, including for an uncalled method (Sorbet, clinks 236–237). -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open Ratchet Ratchet.Denote

theorem SemSafeCtxA.defBlock {κ : Ctx} {Γ Γm : Env} {I τ br : Ty} {d : Defn}
    {ps : List SigParam} {bs : List Ty}
    (_hp : d.params = ps.map (fun p => Param.req p.1))
    (_hps : ps.all (fun p => FirstOrder p.2 && !isAliasTy p.2) = true)
    (_hbs : bs.all (fun σ => FirstOrder σ && !isAliasTy σ) = true)
    (_hbr : FirstOrder br = true) (_hτ : FirstOrder τ = true)
    (_hb : SemMethodBody (topDeclCtx κ d) I ⟨"Object", "Object", d.name, false⟩ bs br ps d.body τ Γm)
    (hruntime : κ.scope.runtimeMain = true) (hclasses : topDeclClassesB κ d.name = true)
    (hself : κ.selfTy = none) (hblock : κ.blockTy = none) (hconst : κ.consts = [])
    (hasms : κ.asms = []) (hI : FirstOrder I = true)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hfresh : ∀ old ∈ κ.defs, old.name ≠ d.name)
    (hmiss : "method_missing" ≠ d.name) (hquiet : "method_added" ≠ d.name) :
    SemSafeCtxA κ Γ I (.def' d.name d.params d.body) .sym (topDeclCtx κ d) Γ I :=
  top_definition hruntime hclasses hself hblock hconst hasms hI hΓ hfresh hmiss hquiet

#print axioms SemSafeCtxA.defBlock
end Ratchet.Denote.Typed
