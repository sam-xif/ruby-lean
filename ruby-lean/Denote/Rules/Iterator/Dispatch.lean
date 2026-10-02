import Denote.Rules.Iterator.Start

/-! Native each consumes the guarded lookup miss and an actual reified block.
Array payload conformance excludes singleton dispatch classes; a reserved each name
withdraws native readiness even though the receiver still has an Array type. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem invoke_array_each {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {o bo : ObjId} {xs : Array Value} {cl : Closure}
    (hm : StateOk κ Γ I m) (hx : (m.heap.get o).payload = .arr xs)
    (hb : (m.heap.get bo).payload = .proc cl) (hf : nameFreeN κ "each" = true)
    (site : SendSite) :
    Interp.invoke m (.ref o) site "each" [] (some (.ref bo)) [] =
      Interp.startIter m (.ref o) "each" cl [] (.arrayEach o 0) [] (.ref o) := by
  obtain ⟨owner, md, hl, hbid, hu, hv, hpre, hs⟩ := each_lookup hm.primitiveDispatch hf
  have hc := hm.arrayPayload o xs hx
  have hlook : lookup m.heap (.ref o) "each" = some (owner, md) := by
    rw [lookup_eq_methodOn, hc]; exact hl
  have hvis : Interp.visError? m (.ref o) site md "each" = none := by
    cases site <;> simp [Interp.visError?, hv]
  rw [Interp.invoke.eq_def]
  simp only [show ("each" == "send" || "each" == "public_send" || "each" == "__send__") = false from rfl,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte, hx]
  simp only [Interp.invoke.invokeDispatch, hlook, hu, hpre, Bool.false_eq_true, ↓reduceIte, hc,
    Interp.crubyResolvedShadow, Option.any, hbid, hs, hvis, Interp.appendKwHash, List.isEmpty]
  simp [Interp.nativeIteratorBid, Interp.nativeDupBid, Interp.nativeCloneBid, Interp.requireBid,
    Interp.enumBid, Interp.procCallBid, Interp.arrayMapBid, Interp.callNativeIterator,
    Interp.tryIterator, hb, hx, Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
    Builtins.toAryDefer?, Builtins.strCmpDefer?, Builtins.strCmpTwin?]
  have h1 : ("Array#each".splitOn "#").getLast?.getD "" = "each" := by decide +kernel
  have h2 : "Array#each" ∉ Builtins.dupBids := by decide
  have h3 : "Array#each" ∉ Builtins.cloneBids := by decide
  simp only [h1, h2, h3, ↓reduceIte]

theorem typed_each_invoke {κ : Ctx} {Γ Γb : Env} {I σ ρ : Ty} {m : Machine}
    {cl : Closure} {name : String} {names : List String} {body : Ratchet.Expr} {o bo : ObjId}
    (hm : StateOk κ Γ I m) (hk : m.kont = [])
    (hproc : (m.heap.get bo).payload = .proc cl) (hf : nameFreeN κ "each" = true)
    (hc : cl.captured = some (m.stack.headD 0))
    (hd : CaptureSlots names (withoutNames ([name] ++ cl.locals) Γb) m)
    (hv : denM (.arrayOf σ) m (.ref o))
    (hmain : closureMainB κ I = true) (hσ : FirstOrder σ = true)
    (hp : cl.params = [.req name]) (he : cl.body = toRuby body)
    (henum : cl.enumYield = none) (hfor : cl.forTargets = none)
    (hin : activationEnvB ([(name, σ)] ++ blockLocals cl.locals ++ Γ) = true)
    (hout : activationReturnB Γb = true)
    (hfix : closureReturnEnv ([name] ++ cl.locals) names Γ Γb = Γ)
    (hb : SemSafeCtxA (closureBodyCtx κ) ([(name, σ)] ++ blockLocals cl.locals ++ Γ) I
      body ρ (closureBodyCtx κ) Γb I) (site : SendSite) :
    StepSpec m Γ (.arrayOf σ) (Interp.invoke m (.ref o) site "each" [] (some (.ref bo)) []) κ I := by
  obtain ⟨o', xs, heq, hx, _⟩ := array_payload hv
  cases heq
  rw [invoke_array_each hm hx hproc hf site]
  exact typed_each_start hm hk hc hd hv hmain hσ hp he henum hfor hin hout hfix hb

#print axioms invoke_array_each
#print axioms typed_each_invoke
end Ratchet.Denote.Typed
