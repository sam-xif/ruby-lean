import Denote.Sem.Singleton.SingletonScope
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
    (names : List String) (args : List Value) :
    ∃ k e md, classNamed? m.heap c.name = some k ∧ SingletonMethodCode k e md ∧
      ConstScopeOk (pushMethodFrame m (requiredFrame (.ref k) d.name md names args)) := by
  obtain ⟨k, hk, _, rows⟩ := hm.classes c hc
  obtain ⟨e, md, he, _, _, _, _, _, code⟩ := rows d hd
  refine ⟨k, e, md, hk, code, ?_⟩
  apply InstanceSite.singleton_constScope
    (m := pushMethodFrame m (requiredFrame (.ref k) d.name md names args))
    (hm.classSites.at_class hc hk)
  · rw [currentFrame_pushMethodFrame]
    exact code.cref
  · rw [currentFrame_pushMethodFrame]
    change md.owner = classOf m.heap (.ref k)
    simp only [code.owner, classOf, he]

theorem hidden_meta_not_site {κ : Ctx} {h : Heap} {cn name : String} {k owner : ObjId} {v : Value}
    (he : classOf h (.ref k) = owner) (hn : constLookup h name = none)
    (hv : constLookupFrom h owner name = some v) : ¬ InstanceSite κ cn k h := by
  intro site
  have hf := site.metaConstants name hn
  rw [he, hv] at hf
  cases hf

#print axioms hidden_meta_not_site
#print axioms recorded_scope

end Ratchet.Denote.Typed.SingletonScopeControls
