import Denote.Sem.Singleton.SingletonCode
import Denote.Sem.Instance.MethodInstall
import Denote.Rules.Class.ClassEntry
import Denote.Rules.Method.MethodResolve

/-! The real def-self step uses the class site's already cached eigenclass. No body is
executed here, and installed code is not an annotated-body certificate. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

/-- The interpreter's def-self record; visibility normalization is a no-op on an attached
metaclass, and the lexical defmod is recorded as definee. -/
def definedSingleton (m : Machine) (owner : ObjId) (ps : List RubyCore.Param)
    (body : RubyCore.Expr) : MethodDef :=
  { params := ps, body, owner, definee := some m.currentFrame.defmod, cref := m.currentFrame.cref,
    fromPrelude := m.preludeMode || m.currentFrame.libraryOrigin }

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

/-- The real def-self step: install on the cached metaclass, then queue the native
singleton_method_added hook on the attached class (after the install). -/
theorem step_defs_cached {m : Machine} {k e : ObjId} {name : String}
    {ps : List RubyCore.Param} {body : RubyCore.Expr}
    (hc : m.ctl = .eval (.defs .self' name ps body))
    (hs : m.currentFrame.self = .ref k) (he : (m.heap.get k).eigen = some e)
    (hp : m.preludeMode = false) (hw : frozenMethodReceiver? m.heap e = none)
    (ha : (m.heap.classPayload? e).bind (·.attached) = some k) :
    Interp.stepFn m = .next { installSingleton m e name ps body with
      ctl := .send (.ref k) .reflective "singleton_method_added" [.sym name] none [],
      kont := .methodEditsK [] (.sym name) :: m.kont } := by
  have hm : Interp.eigenclassOf m k = (e, m) := Proof.Judgment.eigenclassOf_go_some he
  have hnorm : Interp.normalizeDefinitionVisibility m.heap e name (definedSingleton m e ps body) =
      definedSingleton m e ps body := by
    simp [Interp.normalizeDefinitionVisibility, ha]
  have ha' : ((defineMethod m.heap e name (definedSingleton m e ps body)).classPayload? e).bind
      (·.attached) = some k := by rw [attached_defineMethod]; exact ha
  have hstep : Interp.stepFn m =
      Interp.runMethodEdits m [MethodEdit.define e name (definedSingleton m e ps body)] (.sym name) := by
    simp only [Interp.stepFn, hc]
    simp only [Interp.evalExpr, hs, hm]
    rfl
  rw [hstep]
  simp only [Interp.runMethodEdits, hw, hnorm]
  simp only [Interp.finishMethodEdit, hp, ha', Option.isSome_some, Option.getD_some,
    installSingleton, Bool.false_or, String.isEmpty, ↓reduceIte]
  rfl

theorem definedSingleton_code {m : Machine} {cn : String} {k e : ObjId}
    (h : ClassScopeAt cn k m) (ps : List RubyCore.Param) (body : RubyCore.Expr) :
    SingletonMethodCode k e (definedSingleton m e ps body) :=
  ⟨rfl, h.cref, rfl, rfl, rfl, rfl, by simp [definedSingleton, h.phase, h.origin], rfl, rfl, rfl,
    by simp [definedSingleton, h.owner], rfl, rfl⟩

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
  · rfl

/-- Full incoming conformance supplies both the lexical class and the cached metaclass.
The result records the physical step and data/frame preservation, not outgoing StateOk. -/
theorem scoped_singleton_install {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {cn name : String}
    {ps : List RubyCore.Param} {body : RubyCore.Expr}
    (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeClass = some cn)
    (ht : κ.selfTy = some (.clsOf cn)) (hc : m.ctl = .eval (.defs .self' name ps body)) :
    ∃ k e, classNamed? m.heap cn = some k ∧ m.currentFrame.self = .ref k ∧
      (m.heap.get k).eigen = some e ∧
      Interp.stepFn m = .next { installSingleton m e name ps body with
        ctl := .send (.ref k) .reflective "singleton_method_added" [.sym name] none [],
        kont := .methodEditsK [] (.sym name) :: m.kont } ∧
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
  obtain ⟨e', he', hatt, hfz⟩ := site.metaAttached
  rw [he] at he'; cases he'
  have hw : frozenMethodReceiver? m.heap e = none := by
    simp [frozenMethodReceiver?, hatt, hfz, ready.unfrozen]
  have hs : m.currentFrame.self = .ref k := by
    have hv := hm.selfTy
    simp only [SelfTyOk, ht] at hv
    rw [denM] at hv
    cases hs : m.currentFrame.self <;> simp_all [isClassRefNamed, ready.named]
  exact ⟨k, e, ready.named, hs, he, step_defs_cached hc hs he ready.phase hw hatt,
    definedSingleton_code ready ps body, installSingleton_framed m e name ps body,
    installSingleton_own (rooted_payload hm.core hroot)⟩

#print axioms scoped_singleton_install
#print axioms installSingleton_lookup
end Ratchet.Denote.Typed
