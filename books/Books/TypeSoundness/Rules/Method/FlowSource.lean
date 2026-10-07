import Books.TypeSoundness.Rules.Method.FlowDispatch
import Books.TypeSoundness.Judgment.MethodFlowRules
import Books.TypeSoundness.Rules.Closure.FlowCall

/-! Uniform &b bodies compose with actual literal block code and capture ownership.
The source rule resolves the installed method and restores full caller conformance. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

/-- Sorbet 0.6.13405 accepts rung 095's named &b and Integer→Integer block, including
renamed block parameters and stable captured writes (clinks 240–243). Copying the binding
does not change its callable signature; overwriting it with nil invalidates calls (7003). -/
theorem SemMethodFlowBody.callBoundBlock {κ : Ctx} {Γ : Env} {I τ br : Ty} {ps : List Ty}
    {decl : Defn} {facts : LocalFacts} {localName : String} {callback : Bool}
    {Γm : ClosureCode → Env} {out : CallbackFacts}
    (hbody : ∀ code, SemMethodFlowBody κ I ⟨"Object", "Object", decl.name, false⟩ ps br
      [(localName, .clos code .ivar0 .never)] ⟨[localName]⟩ decl.body τ callback (Γm code) out)
    (cb : CheckedCallback κ Γ I) (hargs : cb.params.map (·.2) = ps) (hret : cb.ret = br)
    (hp : decl.params = [.block (some localName)]) (hd : decl ∈ κ.defs) (ht : FirstOrder τ = true)
    (hlam : cb.code.lam = false)
    (hn : facts.captureNames? (withoutNames (cb.params.map (·.1) ++ cb.code.locals) cb.out) = some cb.names) :
    SemFlow κ Γ I facts (.send none decl.name [] (some (.block cb.code.params cb.code.locals cb.code.body)))
      τ false κ Γ I .unknown := by
  intro m hm hf
  let e := Checker.Expr.send none decl.name [] (some (.block cb.code.params cb.code.locals cb.code.body))
  let start := evalFrom m e
  have hdslots := captureNames_sound (hf.ext (Ext_toReCtl m (.eval (toRuby e)) [])) hn
  have hs := (hbody cb.code cb hargs hret).topFinishBlock
    (StateOk_reCtl hm (.eval (toRuby e)) []) rfl ht hp hd hlam hdslots
  apply RunSpec.withPost ?_ (fun _ n _ => ⟨.unknown n, by intro h; cases h⟩)
  apply RunSpec.rebase (middle := start) ?_ (Framed_reCtl _ _ [])
  apply RunSpec.of_stepSpec (by rfl)
  simp only [Interp.stepFn, Interp.evalExpr, evalFrom, toRuby, toRubyOpt, toRubyList]
  split <;> first | contradiction | exact hs

#print axioms SemMethodFlowBody.callBoundBlock
end Checker.Soundness.Typed
