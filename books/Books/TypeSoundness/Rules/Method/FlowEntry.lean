import Books.TypeSoundness.Rules.Method.BoundEntry
import Books.TypeSoundness.Rules.Method.Flow

/-! The actual &b entry supplies one callback alias; a general flow-typed method
body consumes it and returns through the existing complete caller contract. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem SemMethodFlow.callBound {κ : Ctx} {Γ Γm : Env} {I τ : Ty}
    {cb : CheckedCallback κ Γ I} {m : Machine} {cl : Closure} {o : ObjId}
    {e : Checker.Expr} {name localName : String} {md : MethodDef}
    {callback : Bool} {out : CallbackFacts}
    (hbody : SemMethodFlow cb ⟨"Object", "Object", name, false⟩
      [(localName, .clos cb.code .ivar0 .never)] ⟨[localName]⟩ e τ callback Γm out)
    (hm : StateOk κ Γ I m) (hk : m.kont = []) (ht : FirstOrder τ = true)
    (hp : md.params = [.block (some localName)]) (he : md.body = toRuby e)
    (howner : md.definee.getD md.owner = m.currentFrame.defmod) (hcref : md.cref = m.currentFrame.cref)
    (hsuper : md.superName = none) (hcapture : md.capturedFrame = none) (hdeclared : md.declared = [])
    (hfromBlock : md.fromBlock = false) (hfor : md.forTargets = none)
    (hc : cl.captured = some (m.stack.headD 0))
    (hd : CaptureSlots cb.names (withoutNames (cb.params.map (·.1) ++ cl.locals) cb.out) m)
    (hproc : (m.heap.get o).payload = .proc cl) (hcode : ClosureMatches cb.code cl)
    (hclass : classOf m.heap (.ref o) = Boot.procId) :
    StepSpec m Γ τ (Interp.enterUserMethod m m.currentFrame.self name md [] (some (.ref o))) κ I := by
  rw [enterUserMethod_boundBlock m _ name md localName _ hp hcapture hdeclared hfromBlock hfor]
  have active := MethodActivation.enterBound hm name localName md howner hcref hsuper hc hd hproc hcode
  have receiver := boundBlock_receiver m m.currentFrame.self name localName md (.ref o) hclass
  have run := hbody m _ active (by
    intro x hx
    have hx' : x = localName := List.mem_singleton.mp hx
    subst x
    exact receiver)
  have done := run.erase.methodReturn hm.frameInRange active.originUncaptured active.method.frameInRange
    active.uncaptured active.fresh active.framed ht m.frames.size hm.headAlias hm.rootClean
  simpa only [StepSpec, Interp.withKont, pushK, evalFrom, pushMethodFrame, hk, he,
    List.nil_append, Option.getD_some] using done

#print axioms SemMethodFlow.callBound
end Checker.Soundness.Typed
