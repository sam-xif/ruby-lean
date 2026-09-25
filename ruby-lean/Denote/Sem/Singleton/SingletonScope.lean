import Denote.Sem.Core.State

/-! Singleton activations retain lexical class cref but use its metaclass as defmod.
The two constant phases therefore need separate retained heap facts. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

theorem InstanceSite.singleton_constScope {κ : Ctx} {cn : String} {k : ObjId} {m : Machine}
    (site : InstanceSite κ cn k m.heap)
    (hcref : m.currentFrame.cref = [k, Boot.objectId])
    (howner : m.currentFrame.defmod = classOf m.heap (.ref k)) : ConstScopeOk m := by
  intro name
  have hglobal : constOwn m.heap Boot.objectId name = constLookup m.heap name := by
    unfold constOwn constLookup
    cases m.heap.classPayload? Boot.objectId <;> rfl
  rw [constResolveAt, hcref, howner]
  cases hk : constOwn m.heap k name with
  | some v =>
    have hs := site.constants name
    simpa [instanceConstResolve, List.firstM, hk] using hs
  | none =>
    cases hg : constLookup m.heap name with
    | some v => simp [List.firstM, hk, hglobal, hg]
    | none =>
      have hf := site.metaConstants name hg
      simp [List.firstM, hk, hglobal, hg, hf]
      rfl

#print axioms InstanceSite.singleton_constScope
end Ratchet.Denote
