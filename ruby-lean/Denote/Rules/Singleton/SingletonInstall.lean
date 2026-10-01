import Denote.Sem.Singleton.SingletonCode
import Denote.Sem.Instance.MethodInstall
import Denote.Rules.Class.ClassEntry
import Denote.Rules.Method.MethodResolve

/-! The real def-self step uses the class site's already cached eigenclass. No body is
executed here, and installed code is not an annotated-body certificate. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

def definedSingleton (m : Machine) (owner : ObjId) (ps : List RubyCore.Param)
    (body : RubyCore.Expr) : MethodDef :=
  { params := ps, body, owner, cref := m.currentFrame.cref, fromPrelude := m.preludeMode }

def installSingleton (m : Machine) (owner : ObjId) (name : String)
    (ps : List RubyCore.Param) (body : RubyCore.Expr) : Machine :=
  { m with heap := defineMethod m.heap owner name (definedSingleton m owner ps body) }

private theorem rooted_payload {h : Heap} {e : ObjId} (hc : CoreOk h)
    (hr : (ancestors h e).contains Boot.basicObjectId = true) :
    (h.classPayload? e).isSome = true := by
  cases hp : h.classPayload? e with
  | some cp => rfl
  | none =>
    have he : e = Boot.basicObjectId := by
      simpa [ancestors, ancestors.go, hp, eq_comm] using hr
    subst e
    have hn := hc.rootNames.named "BasicObject" Boot.basicObjectId (by simp [rootNameIds])
    unfold classNamed? at hn
    split at hn
    · split at hn
      · cases hn; simp_all
      · cases hn
    · cases hn

theorem step_defs_cached {m : Machine} {k e : ObjId} {name : String}
    {ps : List RubyCore.Param} {body : RubyCore.Expr}
    (hc : m.ctl = .eval (.defs .self' name ps body))
    (hs : m.currentFrame.self = .ref k) (he : (m.heap.get k).eigen = some e) :
    Interp.stepFn m = .next (Interp.withCtl (installSingleton m e name ps body) (.value (.sym name))) := by
  have hm : Interp.eigenclassOf m k = (e, m) := Proof.Judgment.eigenclassOf_go_some he
  simp only [Interp.stepFn, hc]
  change (match m.currentFrame.self with
    | .ref o => let (owner, n) := Interp.eigenclassOf m o
                StepResult.next (Interp.withCtl (installSingleton n owner name ps body) (.value (.sym name)))
    | _ => .unsupported "singleton def on an immediate") = _
  simp only [hs, hm]

theorem definedSingleton_code {m : Machine} {cn : String} {k e : ObjId}
    (h : ClassScopeAt cn k m) (ps : List RubyCore.Param) (body : RubyCore.Expr) :
    SingletonMethodCode k e (definedSingleton m e ps body) :=
  ⟨⟨rfl, h.cref, rfl, rfl, rfl, rfl, h.phase⟩, rfl⟩

theorem installSingleton_framed (m : Machine) (e : ObjId) (name : String)
    (ps : List RubyCore.Param) (body : RubyCore.Expr) :
    Framed m (installSingleton m e name ps body) := Framed_defineMethod m e name _

theorem installSingleton_own {m : Machine} {e : ObjId} {name : String}
    {ps : List RubyCore.Param} {body : RubyCore.Expr}
    (he : (m.heap.classPayload? e).isSome = true) :
    ((installSingleton m e name ps body).heap.classPayload? e).bind
      (fun cp => (cp.methods.find? (·.1 == name)).map (·.2)) =
        some (definedSingleton m e ps body) := ownMethod_defineMethod_self _ _ _ _ he

theorem installSingleton_lookup {m : Machine} {k e : ObjId} {name : String}
    {ps : List RubyCore.Param} {body : RubyCore.Expr}
    (he : (m.heap.get k).eigen = some e) (hf : classFrontB m.heap e = true) :
    lookup (installSingleton m e name ps body).heap (.ref k) name =
      some (e, definedSingleton m e ps body) := by
  obtain ⟨rest, ha⟩ := classFrontB_sound hf
  apply lookup_own_first (rest := rest)
  · change ancestors (defineMethod m.heap e name _) (classOf (defineMethod m.heap e name _) (.ref k)) = _
    rw [Proof.classOf_defineMethod, Proof.ancestors_defineMethod]
    simpa only [classOf, he] using ha
  · apply installSingleton_own
    cases hp : m.heap.classPayload? e <;> simp_all [classFrontB]

/-- Full incoming conformance supplies both the lexical class and the cached metaclass.
The result records the physical step and data/frame preservation, not outgoing StateOk. -/
theorem scoped_singleton_install {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {cn name : String}
    {ps : List RubyCore.Param} {body : RubyCore.Expr}
    (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeClass = some cn)
    (ht : κ.selfTy = some (.clsOf cn)) (hc : m.ctl = .eval (.defs .self' name ps body)) :
    ∃ k e, classNamed? m.heap cn = some k ∧ m.currentFrame.self = .ref k ∧
      (m.heap.get k).eigen = some e ∧
      Interp.stepFn m = .next (Interp.withCtl (installSingleton m e name ps body) (.value (.sym name))) ∧
      SingletonMethodCode k e (definedSingleton m e ps body) ∧
      Framed m (installSingleton m e name ps body) ∧
      ((installSingleton m e name ps body).heap.classPayload? e).bind
        (fun cp => (cp.methods.find? (·.1 == name)).map (·.2)) =
          some (definedSingleton m e ps body) := by
  obtain ⟨k, ready⟩ := hm.classRuntime cn hr
  obtain ⟨j, site⟩ := hm.classSites.of_scope hr
  have hj : j = k := Option.some.inj (site.named.symm.trans ready.named)
  subst j
  obtain ⟨e, he, hroot, _⟩ := site.metaclass
  have hs : m.currentFrame.self = .ref k := by
    have hv := hm.selfTy
    simp only [SelfTyOk, ht] at hv
    rw [denM] at hv
    cases hs : m.currentFrame.self <;> simp_all [isClassRefNamed, ready.named]
  exact ⟨k, e, ready.named, hs, he, step_defs_cached hc hs he,
    definedSingleton_code ready ps body, installSingleton_framed m e name ps body,
    installSingleton_own (rooted_payload hm.core hroot)⟩

#print axioms scoped_singleton_install
#print axioms installSingleton_lookup
end Ratchet.Denote.Typed
