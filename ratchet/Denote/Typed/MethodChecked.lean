import Ratchet.MethodCheck
import Denote.Typed.Bridge
import Denote.Typed.MethodState

/-! The checked body artifact carries its declared signature through the registry into the
real method boundary. No call-site body inference or signature-as-proof assumption. -/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem checked_body_context {κ : Ctx} {I : Ty} {decl : Defn}
    (c : CheckedBody κ I decl) :
    SemSafeCtxA κ c.params I decl.body c.ret κ c.out I := djudge_context c.judged

theorem checked_body_rubyParams {κ : Ctx} {I : Ty} {decl : Defn}
    (c : CheckedBody κ I decl) :
    toRubyParams decl.params = (c.params.map (·.1)).map RubyCore.Param.req := by
  rw [c.paramShape]
  exact toRubyParams_required c.params

/-- Consume an already checked body. The remaining hypotheses concern the actual method
and caller state, not the body certificate or its derivation. -/
theorem checked_method_runSpec {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {md : MethodDef} {decl : Defn} {args : List Value} {fr : Option Ratchet.Frame}
    (c : CheckedBody (κ.withFrame fr) I decl)
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hkont : m.kont = []) (hp : md.params = toRubyParams decl.params)
    (hcap : md.capturedFrame = none) (hdecl : md.declared = []) (hbody : md.body = toRuby decl.body)
    (hlen : args.length = c.params.length) (hargs : DenAll (c.params.map (·.2)) m args)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hscope : frameScope (requiredFrame m.currentFrame.self decl.name md (c.params.map (·.1)) args) =
      frameScope m.currentFrame)
    (hk : ∀ x, constGet? (κ.withFrame fr) x = constGet? κ x)
    (hframe : FrameOk fr
      (pushMethodFrame m (requiredFrame m.currentFrame.self decl.name md (c.params.map (·.1)) args))) :
    ∃ next, Interp.enterUserMethod m m.currentFrame.self decl.name md args none = .next next ∧
      RunSpec m next Γ c.ret κ I :=
  required_method_runSpec hm ht ha hkont (hp.trans (checked_body_rubyParams c)) hcap hdecl hbody
    hlen hargs c.paramsFO c.returnFO hΓ hscope hk hframe (checked_body_context c)

#print axioms checked_body_context
#print axioms checked_method_runSpec
end Ratchet.Denote.Typed
