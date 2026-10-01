import Denote.Sem.Module.ModuleNames
import Denote.Sem.Module.ModuleFrame

/-! A fresh module's lexical constant scope has no inherited tail. Old fallback walks
survive global registration; the metaclass's Module fallback remains a separate premise. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshModule
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment

variable {h : Heap} {name : String}
local notation "h₁" => freshModHeap h Boot.objectId name name

theorem const_own_old_other (ho : Boot.objectId < h.objs.size)
    {k : ObjId} (hk : k < h.objs.size) {cn : String} (hn : cn ≠ name) :
    constOwn h₁ k cn = constOwn h k cn := by
  rw [constOwn_old_fresh ho hk]
  exact constOwn_constSetIn_ne h Boot.objectId k name cn _ (Or.inr hn)

theorem const_from_eq_firstM (g : Heap) (k : ObjId) (cn : String) :
    constLookupFrom g k cn = (ancestors g k).firstM (fun j => constOwn g j cn) := by
  unfold constLookupFrom
  apply firstM_congr
  intro j _
  cases hp : g.classPayload? j <;> simp [constOwn, hp]

theorem const_from_old_other (hc : ChainsIn h) (hs : Saturated h)
    {k : ObjId} (hk : k < h.objs.size) {cn : String} (hn : cn ≠ name) :
    constLookupFrom h₁ k cn = constLookupFrom h k cn := by
  rw [const_from_eq_firstM, const_from_eq_firstM, ancestors_old_fresh hc hs hk]
  exact firstM_congr (fun j hj => const_own_old_other hc.boot.2.2.2.2
    (ClsGrow.ancestors_mem_lt hc hk j hj) hn)

theorem const_from_fresh (cn : String) : constLookupFrom h₁ h.objs.size cn = none := by
  simp [const_from_eq_firstM, ancestors_fresh_k, List.firstM, constOwn_fresh_k]
  rfl

theorem const_from_eigen_other (hc : ChainsIn h) (hs : Saturated h)
    {cn : String} (hn : cn ≠ name) :
    constLookupFrom h₁ (h.objs.size + 1) cn = constLookupFrom h Boot.moduleId cn := by
  rw [const_from_eq_firstM, const_from_eq_firstM, ancestors_fresh_e hc hs]
  simp only [List.firstM, constOwn_fresh_e]
  exact firstM_congr (fun j hj => const_own_old_other hc.boot.2.2.2.2
    (ClsGrow.ancestors_mem_lt hc hc.boot.2.1 j hj) hn)

theorem fallback_old {k : ObjId} (hc : ChainsIn h) (hs : Saturated h)
    (ho : (h.classPayload? Boot.objectId).isSome = true) (hk : k < h.objs.size)
    (hp : ConstFallback h k) : ConstFallback h₁ k := by
  intro cn hn
  have hne : cn ≠ name := by intro he; subst cn; rw [const_self ho] at hn; cases hn
  rw [const_from_old_other hc hs hk hne]
  exact hp cn ((const_other hc.boot.2.2.2.2 hne).symm.trans hn)

theorem fallback_fresh_meta (hc : ChainsIn h) (hs : Saturated h)
    (ho : (h.classPayload? Boot.objectId).isSome = true)
    (hp : ConstFallback h Boot.moduleId) : ConstFallback h₁ (h.objs.size + 1) := by
  intro cn hn
  have hne : cn ≠ name := by intro he; subst cn; rw [const_self ho] at hn; cases hn
  rw [const_from_eigen_other hc hs hne]
  exact hp cn ((const_other hc.boot.2.2.2.2 hne).symm.trans hn)

theorem instance_constants_fresh (cn : String) :
    instanceConstResolve h₁ h.objs.size cn = constLookup h₁ cn := by
  simp only [instanceConstResolve, List.firstM, constOwn_fresh_k, const_from_fresh]
  rw [const_eq_own]
  cases constOwn h₁ Boot.objectId cn <;> rfl

theorem const_scope {m : Machine} {body : RubyCore.Expr}
    (hcref : m.currentFrame.cref = [Boot.objectId]) :
    ConstScopeOk (freshModMachine m Boot.objectId m.currentFrame.cref name name body) := by
  intro cn
  rw [constResolveAt, current_frame]
  simpa only [freshModFrame, hcref, freshModMachine, instanceConstResolve] using
    instance_constants_fresh (h := m.heap) (name := name) cn

#print axioms fallback_old
#print axioms const_scope
end Ratchet.Denote.FreshModule
