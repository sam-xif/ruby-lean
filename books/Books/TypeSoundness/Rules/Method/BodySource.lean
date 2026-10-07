import Books.TypeSoundness.Rules.Method.BodyDispatch
import Books.TypeSoundness.Judgment.MethodRules
import Books.TypeSoundness.Rules.Closure.FlowCall

/-! Source-level implicit calls with a literal block. Local facts identify captures;
the declaration's uniform body proof and the checked actual callback justify dispatch. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

/-- Sorbet 0.6.13405 accepts Integer arithmetic/captured-write blocks at a declared
Integer→Integer signature and rejects a String result (7005; clink 238). Parameter names
and captures may differ at each call. Dispatch follows the model, including user `new`;
Sorbet instead applies its constructor rule to that special-name probe (7035). -/
theorem SemMethodBody.callBlock {κ : Ctx} {Γ Γm : Env} {I τ br : Ty} {ps : List Ty}
    {decl : Defn} {facts : LocalFacts}
    (hbody : SemMethodBody κ I ⟨"Object", "Object", decl.name, false⟩ ps br [] decl.body τ Γm)
    (cb : CheckedCallback κ Γ I) (hargs : cb.params.map (·.2) = ps) (hret : cb.ret = br)
    (hp : decl.params = []) (hd : decl ∈ κ.defs) (ht : FirstOrder τ = true)
    (hlam : cb.code.lam = false)
    (hn : facts.captureNames? (withoutNames (cb.params.map (·.1) ++ cb.code.locals) cb.out) = some cb.names) :
    SemFlow κ Γ I facts (.send none decl.name [] (some (.block cb.code.params cb.code.locals cb.code.body)))
      τ false κ Γ I .unknown := by
  intro m hm hf
  let e := Checker.Expr.send none decl.name [] (some (.block cb.code.params cb.code.locals cb.code.body))
  let start := evalFrom m e
  have hdslots := captureNames_sound (hf.ext (Ext_toReCtl m (.eval (toRuby e)) [])) hn
  have hs := (hbody cb hargs hret).topFinishBlock
    (StateOk_reCtl hm (.eval (toRuby e)) []) rfl ht hp hd hlam hdslots
  apply RunSpec.withPost ?_ (fun _ n _ => ⟨.unknown n, by intro h; cases h⟩)
  apply RunSpec.rebase (middle := start) ?_ (Framed_reCtl _ _ [])
  apply RunSpec.of_stepSpec (by rfl)
  simp only [Interp.stepFn, Interp.evalExpr, evalFrom, toRuby, toRubyOpt, toRubyList]
  split <;> first | contradiction | exact hs

#print axioms SemMethodBody.callBlock
end Checker.Soundness.Typed
