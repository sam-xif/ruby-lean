import Books.TypeSoundness.Rules.Method.BodySource

/-! Registry-facing source call rule. Both the uniform method and actual callback
premises are interpreted by the same family; no raw derivation crosses this boundary. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open Checker Checker.Soundness

theorem SemSafeCtxA.DFlow.callBlock {κ : Ctx} {Γ Γm Γb : Env} {I τ br : Ty} {decl : Defn}
    {facts : LocalFacts} {ps : List SigParam} {locals names : List String} {body : Expr}
    (hm : SemMethodBody κ I ⟨"Object", "Object", decl.name, false⟩ (ps.map (·.2)) br [] decl.body τ Γm)
    (hp : decl.params = []) (hd : decl ∈ κ.defs) (ht : FirstOrder τ = true) (hr : FirstOrder br = true)
    (hmain : closureMainB κ I = true) (hin : activationEnvB (ps ++ blockLocals locals ++ Γ) = true)
    (hout : activationReturnB Γb = true) (hfix : closureReturnEnv (ps.map (·.1) ++ locals) names Γ Γb = Γ)
    (hn : facts.captureNames? (withoutNames (ps.map (·.1) ++ locals) Γb) = some names)
    (hs : (paramEqAll (ps.map (fun p => Param.req p.1)) (ps.map (fun p => Param.req p.1)) && exprEq body body) = true)
    (hb : SemSafeCtxA (closureBodyCtx κ) (ps ++ blockLocals locals ++ Γ) I body br (closureBodyCtx κ) Γb I) :
    SemFlow κ Γ I facts (.send none decl.name []
      (some (.block (ps.map (fun p => Param.req p.1)) locals body))) τ false κ Γ I .unknown :=
  hm.callBlock
    { code := ⟨ps.map (fun p => Param.req p.1), locals, body, false, hs⟩
      params := ps, ret := br, names := names, out := Γb, required := rfl,
      main := hmain, returnFO := hr, inputTypes := hin, outputTypes := hout,
      fixed := hfix, body := hb }
    rfl rfl hp hd ht rfl hn

#print axioms SemSafeCtxA.DFlow.callBlock
end Checker.Soundness.Typed
