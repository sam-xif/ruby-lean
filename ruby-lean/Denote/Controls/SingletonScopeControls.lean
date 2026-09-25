import Denote.Rules.Singleton.SingletonEntry
import Denote.Controls.SingletonInstallControls

/-! Metaclass constant fallback is independent of ordinary lexical-class agreement. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.SingletonScopeControls
open RubyCore Ratchet Ratchet.Denote
open SingletonInstallControls (entry k e)

#guard constFallbackB bootMachine.heap (classOf bootMachine.heap (.ref Boot.objectId))
#guard constFallbackB entry.heap e

private def hidden : Heap := constSetIn entry.heap e "IOError" (.int 99)
private def activation : Machine :=
  pushMethodFrame { entry with heap := hidden }
    { self := .ref k, defmod := e, cref := [k, Boot.objectId], kind := .method }

-- These ordinary-site facts survive, but the actual singleton activation sees 99 where
-- the global table has no binding. This is a contract witness, not an admitted program.
#guard metaReadyB hidden k && classFrontB hidden (classOf hidden (.ref k)) &&
  (hidden.get (classOf hidden (.ref k))).eigen.isNone &&
  (instanceConstResolve hidden k "IOError").isNone &&
  (constLookup hidden "IOError").isNone &&
  (constResolveAt activation "IOError").any (·.identEq (.int 99)) && !constFallbackB hidden e

theorem recorded_scope {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {c : Cls} {d : Defn}
    (hm : StateOk κ Γ I m) (hc : c ∈ κ.classes) (hd : d ∈ c.smethods)
    (hp : m.preludeMode = false)
    (names : List String) (args : List Value) :
    ∃ k e md, classNamed? m.heap c.name = some k ∧ SingletonMethodCode k e md ∧
      SingletonScopeAt c.name k e
        (pushMethodFrame m (requiredFrame (.ref k) d.name md names args)) ∧
      ConstScopeOk (pushMethodFrame m (requiredFrame (.ref k) d.name md names args)) := by
  obtain ⟨k, hk, _, rows⟩ := hm.classes c hc
  obtain ⟨e, md, he, _, _, _, _, _, code⟩ := rows d hd
  have site := hm.classSites.at_class hc hk
  have scope := singleton_required_scope (name := d.name) names args hk site.live he code hp
  exact ⟨k, e, md, hk, code, scope, scope.constScope site⟩

-- A caller can resume after a nested body that allocates or changes method tables.
-- Post-body sites justify constants; cached-owner identity must come from framing.
theorem nested_return {κ : Ctx} {cn name : String} {k e : ObjId} {m n : Machine}
    {md : MethodDef} {f : RubyCore.Frame} (names : List String) (args : List Value)
    (site : InstanceSite κ cn k m.heap) (he : (m.heap.get k).eigen = some e)
    (code : SingletonMethodCode k e md) (hp : m.preludeMode = false)
    (hc : f.captured = none)
    (h : Framed (pushMethodFrame
      (pushMethodFrame m (requiredFrame (.ref k) name md names args)) f) n)
    (hn : n.preludeMode = false) (post : InstanceSite κ cn k n.heap) :
    SingletonScopeAt cn k e (popMethodFrame n) ∧ ConstScopeOk (popMethodFrame n) := by
  have scope := singleton_required_scope (name := name) names args site.named site.live he code hp
  have restored := singleton_pop_scope scope (by simp [FrameInRange, pushMethodFrame]) hc h hn
  exact ⟨restored, restored.constScope post⟩

theorem hidden_meta_not_site {κ : Ctx} {h : Heap} {cn name : String} {k owner : ObjId} {v : Value}
    (he : classOf h (.ref k) = owner) (hn : constLookup h name = none)
    (hv : constLookupFrom h owner name = some v) : ¬ InstanceSite κ cn k h := by
  intro site
  have hf := site.metaConstants name hn
  rw [he, hv] at hf
  cases hf

#print axioms hidden_meta_not_site
#print axioms recorded_scope
#print axioms nested_return

end Ratchet.Denote.Typed.SingletonScopeControls
