import Books.TypeSoundness.Rules.Iterator.MapStart

/-! Native map/collect consume guarded method resolution, including public visibility
and absence of overrides/undef. Array payload conformance supplies the dispatch class. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem invoke_array_map {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {o bo : ObjId} {xs : Array Value} {cl : Closure} {mname : String}
    (hm : StateOk κ Γ I m) (hx : (m.heap.get o).payload = .arr xs)
    (hb : (m.heap.get bo).payload = .proc cl) (hf : nameFreeN κ mname = true)
    (hn : mname = "map" ∨ mname = "collect") (site : SendSite) :
    Interp.invoke m (.ref o) site mname [] (some (.ref bo)) [] =
      Interp.startIter m (.ref o) mname cl [] (.arrayMap o 0) [] .nil := by
  have hrow : (Boot.arrayId, mname, "Array#" ++ mname) ∈ dispatchMethods := by
    rcases hn with rfl | rfl <;> simp [dispatchMethods]
  obtain ⟨owner, md, hl, hbid, hu, hv, hp, hs⟩ := dispatch_lookup hm.primitiveDispatch hrow hf
  have hc := hm.arrayPayload o xs hx
  have hlook : lookup m.heap (.ref o) mname = some (owner, md) := by
    rw [lookup_eq_methodOn, hc]; exact hl
  have hvis : Interp.visError? m (.ref o) site md mname = none := by
    cases site <;> simp [Interp.visError?, hv]
  have hns : (mname == "send" || mname == "public_send" || mname == "__send__") = false := by
    rcases hn with rfl | rfl <;> rfl
  have hproc : Interp.procCallBid ("Array#" ++ mname) = false := by
    rcases hn with rfl | rfl <;> rfl
  have hmap : Interp.arrayMapBid ("Array#" ++ mname) = true := by
    rcases hn with rfl | rfl <;> rfl
  rw [Interp.invoke.eq_def]
  simp only [hns, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hx]
  simp only [Interp.invoke.invokeDispatch, hlook, hu, hp, Bool.false_eq_true, ↓reduceIte,
    hc, hs, hvis, hbid, hproc, hmap, Interp.callArrayMapBuiltin, List.length_nil,
    List.isEmpty_nil, Nat.add_zero, bne_self_eq_false, ↓reduceIte, hb, hx]
  rcases hn with rfl | rfl <;>
    simp [Interp.crubyResolvedShadow, hs, Interp.nativeDupBid, Interp.nativeCloneBid,
      Interp.requireBid, Interp.enumBid, Interp.nativeIteratorBid, Interp.callArrayMapBuiltin,
      Interp.appendKwHash, hb, hx, Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
      Builtins.toAryDefer?, Builtins.strCmpDefer?, Builtins.strCmpTwin?, Interp.procCallBid,
      Interp.arrayMapBid, hbid, Builtins.dupBids, Builtins.cloneBids]

theorem typed_map_invoke {κ : Ctx} {Γ Γb : Env} {I σ ρ : Ty} {m : Machine}
    {cl : Closure} {name mname : String} {names : List String} {body : Checker.Expr} {o bo : ObjId}
    (hm : StateOk κ Γ I m) (hk : m.kont = [])
    (hproc : (m.heap.get bo).payload = .proc cl) (hf : nameFreeN κ mname = true)
    (hn : mname = "map" ∨ mname = "collect")
    (hc : cl.captured = some (m.stack.headD 0))
    (hd : CaptureSlots names (withoutNames ([name] ++ cl.locals) Γb) m)
    (hv : denM (.arrayOf σ) m (.ref o))
    (hmain : closureMainB κ I = true) (hσ : FirstOrder σ = true) (hρ : FirstOrder ρ = true)
    (hp : cl.params = [.req name]) (he : cl.body = toRuby body)
    (henum : cl.enumYield = none) (hfor : cl.forTargets = none)
    (hin : activationEnvB ([(name, σ)] ++ blockLocals cl.locals ++ Γ) = true)
    (hout : activationReturnB Γb = true)
    (hfix : closureReturnEnv ([name] ++ cl.locals) names Γ Γb = Γ)
    (hb : SemSafeCtxA (closureBodyCtx κ) ([(name, σ)] ++ blockLocals cl.locals ++ Γ) I
      body ρ (closureBodyCtx κ) Γb I) (site : SendSite) :
    StepSpec m Γ (.arrayOf ρ) (Interp.invoke m (.ref o) site mname [] (some (.ref bo)) []) κ I := by
  obtain ⟨o', xs, heq, hx, _⟩ := array_payload hv
  cases heq
  rw [invoke_array_map hm hx hproc hf hn site]
  exact typed_map_start hm hk hc hd hv hmain hσ hρ hp he henum hfor hin hout hfix hb

#print axioms invoke_array_map
#print axioms typed_map_invoke
end Checker.Soundness.Typed
