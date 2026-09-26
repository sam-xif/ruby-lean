import Denote.Rules.Method.MethodDefine
import Denote.Judgment.MethodFlowRules

/-! A named-&b definition requires its all-code signature-domain body proof before
installation, even if uncalled. Installation itself uses the existing real transition. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open Ratchet Ratchet.Denote

theorem SemSafeCtxA.defBoundBlock {κ : Ctx} {Γ : Env} {I τ br : Ty} {d : Defn}
    {localName : String} {bs : List Ty} {callback : Bool} {Γm : ClosureCode → Env} {out : CallbackFacts}
    (_hp : d.params = [.block (some localName)])
    (_hbs : bs.all (fun σ => FirstOrder σ && !isAliasTy σ) = true)
    (_hbr : FirstOrder br = true) (_hτ : FirstOrder τ = true)
    (_hb : ∀ code, SemMethodFlowBody (topDeclCtx κ d) I ⟨"Object", "Object", d.name, false⟩ bs br
      [(localName, .clos code .ivar0 .never)] ⟨[localName]⟩ d.body τ callback (Γm code) out)
    (hruntime : κ.scope.runtimeMain = true) (hclasses : topDeclClassesB κ d.name = true)
    (hself : κ.selfTy = none) (hblock : κ.blockTy = none) (hconst : κ.consts = [])
    (hasms : κ.asms = []) (hI : FirstOrder I = true)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hfresh : ∀ old ∈ κ.defs, old.name ≠ d.name)
    (hmiss : "method_missing" ≠ d.name) (hquiet : "method_added" ≠ d.name) :
    SemSafeCtxA κ Γ I (.def' d.name d.params d.body) .sym (topDeclCtx κ d) Γ I :=
  top_definition hruntime hclasses hself hblock hconst hasms hI hΓ hfresh hmiss hquiet

#print axioms SemSafeCtxA.defBoundBlock
end Ratchet.Denote.Typed
