import Books.TypeSoundness.Rules.Method.BodyEntry
import Books.TypeSoundness.Rules.Method.BodyBoundCall

/-! Ordinary explicit &b binding. The interpreter binds the actual block value in
the fresh method frame after predeclaration; no extra capture edge is introduced. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem classifyFull_boundBlock (localName : String) :
    Interp.classifyFull [.block (some localName)] =
      some ⟨[], [], none, [], [], none, some localName, []⟩ := by
  simp [Interp.classifyFull]

theorem enterUserMethod_boundBlock (m : Machine) (recv : Value) (name : String)
    (md : MethodDef) (localName : String) (blk : Option Value)
    (hp : md.params = [.block (some localName)])
    (hc : md.capturedFrame = none) (hd : md.declared = [])
    (hblock : md.fromBlock = false) (hfor : md.forTargets = none) :
    Interp.enterUserMethod m recv name md [] blk =
      .next (Interp.withKont (pushMethodFrame m
        (requiredBlockFrame recv name md [localName] [blk.getD .nil] blk))
        (.eval md.body) (.frameK m.frames.size)) := by
  unfold Interp.enterUserMethod
  rw [hp, classifyFull_boundBlock]
  simp [Interp.appendKwHash, hc, hd, hblock, hfor, requiredBlockFrame, requiredFrame, pushMethodFrame,
    Machine.localFrameId, Machine.localFrameId.go,
    Interp.withKont, Interp.withCtl, hp, Machine.setLocal, Machine.setLocal.owner,
    Array.getD_eq_getD_getElem?, Array.setIfInBounds, Array.set_push]

theorem requiredBlockFrame_getLocal (m : Machine) (recv : Value) (name : String)
    (md : MethodDef) (names : List String) (args : List Value) (blk : Option Value) (x : String) :
    (pushMethodFrame m (requiredBlockFrame recv name md names args blk)).getLocal x =
      (((names.zip args).find? (·.1 == x)).map (·.2)).getD .nil := by
  simp only [Machine.getLocal, Machine.getLocal.go, Machine.localFrameId, Machine.localFrameId.go,
    pushMethodFrame, requiredBlockFrame, requiredFrame]
  simp [Array.getD_eq_getD_getElem?]
  cases (names.zip args).find? (·.1 == x) <;> rfl

theorem MethodActivation.enterBound {κ : Ctx} {Γ : Env} {I : Ty}
    {cb : CheckedCallback κ Γ I} {m : Machine} {cl : Closure} {o : ObjId}
    (hm : StateOk κ Γ I m) (name localName : String) (md : MethodDef)
    (howner : md.definee.getD md.owner = m.currentFrame.defmod) (hcref : md.cref = m.currentFrame.cref)
    (hsuper : md.superName = none)
    (hc : cl.captured = some (m.stack.headD 0))
    (hd : CaptureSlots cb.names (withoutNames (cb.params.map (·.1) ++ cl.locals) cb.out) m)
    (hproc : (m.heap.get o).payload = .proc cl) (hcode : ClosureMatches cb.code cl) :
    MethodActivation cb ⟨"Object", "Object", name, false⟩ [(localName, .clos cb.code .ivar0 .never)] m
      (pushMethodFrame m (requiredBlockFrame m.currentFrame.self name md
        [localName] [.ref o] (some (.ref o)))) := by
  apply MethodActivation.enterBindings hm name md [localName] [.ref o] ?_
    howner hcref hsuper hc hd hproc hcode
  constructor
  · intro x τ hx
    by_cases he : localName == x
    · have ht : τ = .clos cb.code .ivar0 .never := by simpa [envGet?, he] using hx.symm
      subst τ
      have hn : localName = x := eq_of_beq he
      subst x
      constructor
      · rw [requiredBlockFrame_getLocal]
        simp only [List.zip_cons_cons, List.zip_nil_left, List.find?, beq_self_eq_true,
          Option.map_some, Option.getD_some, stripAlias, denM]
        exact ⟨cl, by simp only [procClosure?, pushMethodFrame, hproc],
          hcode, by simp [denSpineFrom], Or.inl trivial, Or.inl ⟨trivial, trivial⟩⟩
      · intro y ρ h; cases h
    · simp [envGet?, he] at hx
  · intro x hx
    rw [requiredBlockFrame_getLocal]
    by_cases hn : localName == x
    · simp [envGet?, hn] at hx
    · simp [hn]

theorem boundBlock_receiver (m : Machine) (recv : Value) (name localName : String)
    (md : MethodDef) (v : Value) (hk : classOf m.heap v = Boot.procId) :
    let entry := pushMethodFrame m (requiredBlockFrame recv name md [localName] [v] (some v))
    MethodCallbackReceiver entry (entry.getLocal localName) := by
  dsimp only
  rw [requiredBlockFrame_getLocal]
  simp only [List.zip_cons_cons, List.zip_nil_left, List.find?, beq_self_eq_true,
    Option.map_some, Option.getD_some]
  exact ⟨by rw [currentFrame_pushMethodFrame]; rfl, hk⟩

/-- Actual &b entry, local receiver evaluation, argument effects, native dispatch,
checked callback execution and method return, retaining full caller conformance. -/
theorem bound_callback_method_call {κ : Ctx} {Γ Γm : Env} {I σ : Ty}
    {cb : CheckedCallback κ Γ I} {m : Machine} {cl : Closure} {o : ObjId}
    {arg : Checker.Expr} {name localName selector param : String} {md : MethodDef}
    (he : SemMethod cb ⟨"Object", "Object", name, false⟩
      [(localName, .clos cb.code .ivar0 .never)] arg σ Γm)
    (hparam : cb.params = [(param, σ)]) (ht : activationReturnB Γm = true)
    (hplain : plainArgB arg = true) (hfree : nameFreeN κ selector = true)
    (hselector : procCallNameB selector = true)
    (hm : StateOk κ Γ I m) (hk : m.kont = [])
    (hp : md.params = [.block (some localName)])
    (hbody : md.body = toRuby (.send (some (.var .lvar localName)) selector [arg] none))
    (howner : md.definee.getD md.owner = m.currentFrame.defmod) (hcref : md.cref = m.currentFrame.cref)
    (hsuper : md.superName = none) (hcapture : md.capturedFrame = none) (hdeclared : md.declared = [])
    (hfromBlock : md.fromBlock = false) (hfor : md.forTargets = none)
    (hc : cl.captured = some (m.stack.headD 0))
    (hd : CaptureSlots cb.names (withoutNames (cb.params.map (·.1) ++ cl.locals) cb.out) m)
    (hproc : (m.heap.get o).payload = .proc cl) (hcode : ClosureMatches cb.code cl)
    (hclass : classOf m.heap (.ref o) = Boot.procId) :
    StepSpec m Γ cb.ret (Interp.enterUserMethod m m.currentFrame.self name md [] (some (.ref o))) κ I := by
  rw [enterUserMethod_boundBlock m _ name md localName _ hp hcapture hdeclared hfromBlock hfor]
  have active := MethodActivation.enterBound hm name localName md howner hcref hsuper hc hd hproc hcode
  have receiver := boundBlock_receiver m m.currentFrame.self name localName md (.ref o) hclass
  have run := bound_callback_call_run active receiver he hparam ht hplain hfree hselector
  have done := run.methodReturn hm.frameInRange active.originUncaptured active.method.frameInRange
    active.uncaptured active.fresh active.framed cb.returnFO m.frames.size hm.headAlias hm.rootClean
  simpa only [StepSpec, Interp.withKont, pushK, evalFrom, pushMethodFrame, hk, hbody,
    List.nil_append, Option.getD_some]
    using done

#print axioms enterUserMethod_boundBlock
#print axioms MethodActivation.enterBound
#print axioms boundBlock_receiver
#print axioms bound_callback_method_call
end Checker.Soundness.Typed
