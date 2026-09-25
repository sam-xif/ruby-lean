import Denote.Rules.Singleton.SingletonInstall
import Denote.Rules.Instance.InstanceDispatch

/-! Actual singleton lookup and required-argument dispatch after installation. Low-level
frontness premises are discharged by the class site's retained metaclass contract. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem finishSend_singleton_installed {m : Machine} {k e : ObjId} {name : String}
    {ps : List RubyCore.Param} {body : RubyCore.Expr} {args : List Value} {site : SendSite}
    (he : (m.heap.get k).eigen = some e) (hf : classFrontB m.heap e = true)
    (hp : m.preludeMode = false) (hn : DirectSendName name) :
    Interp.finishSend (installSingleton m e name ps body) (.ref k) site name args .none =
      Interp.enterUserMethod (installSingleton m e name ps body) (.ref k) name
        (definedSingleton m e ps body) args none := by
  apply invoke_direct_userMethod hn (installSingleton_lookup he hf) rfl rfl hp
  · simp [Interp.visError?, definedSingleton]
  · obtain ⟨rest, ha⟩ := classFrontB_sound hf
    change Interp.crubyShadow (defineMethod m.heap e name _)
      ((ancestors (defineMethod m.heap e name _) (classOf (defineMethod m.heap e name _) (.ref k))).takeWhile _) _ = _
    rw [Proof.classOf_defineMethod, Proof.ancestors_defineMethod]
    simp [classOf, he, ha, Interp.crubyShadow]
    rfl

theorem singleton_installed_required {m : Machine} {k e : ObjId} {name : String}
    {body : RubyCore.Expr} {names : List String} {args : List Value} {site : SendSite}
    (he : (m.heap.get k).eigen = some e) (hf : classFrontB m.heap e = true)
    (hp : m.preludeMode = false) (hn : DirectSendName name) (ha : args.length = names.length) :
    let md := definedSingleton m e (names.map RubyCore.Param.req) body
    let installed := installSingleton m e name (names.map RubyCore.Param.req) body
    Interp.finishSend installed (.ref k) site name args .none =
      .next (Interp.withKont (pushMethodFrame installed (requiredFrame (.ref k) name md names args))
        (.eval body) (.frameK installed.frames.size)) := by
  dsimp only
  rw [finishSend_singleton_installed he hf hp hn]
  exact enterUserMethod_required _ _ _ _ _ _ rfl rfl rfl ha

/-- Full incoming conformance justifies actual lookup and entry; no physical lookup or
metaclass-front premise is supplied by an emitter or caller. Body safety is still separate. -/
theorem scoped_singleton_required {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {cn name : String}
    {body : RubyCore.Expr} {names : List String} {args : List Value} {site : SendSite}
    (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeClass = some cn)
    (ht : κ.selfTy = some (.clsOf cn))
    (hc : m.ctl = .eval (.defs .self' name (names.map RubyCore.Param.req) body))
    (hn : DirectSendName name) (ha : args.length = names.length) :
    ∃ k e, classNamed? m.heap cn = some k ∧
      let md := definedSingleton m e (names.map RubyCore.Param.req) body
      let installed := installSingleton m e name (names.map RubyCore.Param.req) body
      Interp.stepFn m = .next (Interp.withCtl installed (.value (.sym name))) ∧
      SingletonMethodCode k e md ∧
      lookup installed.heap (.ref k) name = some (e, md) ∧
      Interp.finishSend installed (.ref k) site name args .none =
        .next (Interp.withKont (pushMethodFrame installed (requiredFrame (.ref k) name md names args))
          (.eval body) (.frameK installed.frames.size)) := by
  obtain ⟨k, e, hk, _, he, hs, hcode, _, _⟩ := scoped_singleton_install hm hr ht hc
  obtain ⟨j, hsit⟩ := hm.classSites.of_scope hr
  have hj : j = k := Option.some.inj (hsit.named.symm.trans hk)
  subst j
  have hf := hsit.eigen_front he
  exact ⟨k, e, hk, hs, hcode, installSingleton_lookup he hf,
    singleton_installed_required he hf hcode.fromPrelude hn ha⟩

#print axioms finishSend_singleton_installed
#print axioms singleton_installed_required
#print axioms scoped_singleton_required
end Ratchet.Denote.Typed
