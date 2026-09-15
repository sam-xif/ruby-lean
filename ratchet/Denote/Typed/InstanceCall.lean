import Denote.Typed.InstanceCallEntry
import Denote.Typed.MainReturn
import Denote.Typed.InstanceRun

/-! Complete instance calls from the ordinary top-level caller world. The actual lookup,
annotated binding/body, and frame return are composed; constructor payload remains explicit. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem checked_instance_call_from_main {κ : Ctx} {Γ : Env} {I Ib : Ty} {m : Machine}
    {c : Cls} {d : Defn} {recv : Value} {args : List Value}
    (body : CheckedBody (instanceBodyCtx κ ⟨c.name, c.name, d.name⟩ Ib) Ib d)
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hc : c ∈ κ.classes) (hd : d ∈ c.methods)
    (hr : κ.scope.runtimeMain = true) (hw : κ.pos.mainWorld = true)
    (hcl : κ.scope.runtimeClass = none) (hkont : m.kont = [])
    (hi : FirstOrder Ib = true) (hv : denM (.inst c.name Ib) m recv)
    (hlen : args.length = body.params.length) (hargs : DenAll (body.params.map (·.2)) m args)
    (hk : ∀ x, constGet? (instanceBodyCtx κ ⟨c.name, c.name, d.name⟩ Ib) x = constGet? κ x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hp : ∀ o, recv = .ref o → (m.heap.get o).payload = .none) (hn : d.name ≠ "initialize") :
    ∃ next, Interp.finishSend m recv .explicit d.name args .none = .next next ∧
      RunSpec m next Γ body.ret κ I :=
  instance_method_run body.paramShape body.paramsFO body.returnFO (checked_body_context body)
    hm ht ha hc hd hr hw hcl hkont hi hv hlen hargs hk hΓ (fun o ho => Or.inl (hp o ho)) hn

#print axioms checked_instance_call_from_main
end Ratchet.Denote.Typed
