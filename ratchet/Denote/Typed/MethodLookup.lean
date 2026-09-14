import Denote.Typed.MethodChecked
import Denote.Typed.MethodResolve

/-! Apply a stored body artifact through the semantic installed-method contract. -/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

/-- Ordinary top-level dispatch uses the installed table and the stored body derivation.
All physical-frame facts now come from conformance at the requested runtime scope. -/
theorem checked_top_call {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {decl : Defn}
    {args : List Value}
    (c : CheckedBody (κ.withFrame (some ⟨"Object", "Object", decl.name⟩)) I decl)
    (hm : StateOk κ Γ I m) (hd : decl ∈ κ.defs)
    (ht : ReframeFO κ I) (ha : κ.asms = []) (hc : κ.consts = [])
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hkont : m.kont = []) (hlen : args.length = c.params.length)
    (hargs : DenAll (c.params.map (·.2)) m args)
    (hruntime : κ.scope.runtimeMain = true) (hblock : κ.blockTy = none) :
    ∃ next, Interp.finishSend m m.currentFrame.self .implicit decl.name args .none = .next next ∧
      RunSpec m next Γ c.ret κ I :=
  top_method_runSpec c.paramShape c.paramsFO c.returnFO (checked_body_context c)
    hm hd ht ha hc hΓ hkont hlen hargs hruntime hblock

#print axioms checked_top_call
end Ratchet.Denote.Typed
