import Books.TypeSoundness.Conformance.Module.ModuleScopeActual
import Books.TypeSoundness.Conformance.Class.ClassConstScopeActual

/-! Constant resolution in the actual module body: the module's own table and ancestry
are empty, so lexical lookup takes the module-only Object fallback. -/
set_option autoImplicit false
namespace Checker.Soundness.FreshModuleActual
open RubyCore Checker RubyCore.Proof RubyCore.Proof.Judgment
variable {m : Machine} {name : String}
local notation "h₁" => heap m name

theorem const_own_fresh (hd : m.lexicalNamespace < m.heap.objs.size) (cn : String) :
    constOwn h₁ m.heap.objs.size cn = none := by
  simp [constOwn, Heap.classPayload?, get_module hd, namedObject, modPayload]

theorem const_from_module (hc : ChainsIn m.heap) (hd : m.lexicalNamespace < m.heap.objs.size)
    (cn : String) : constLookupFrom h₁ m.heap.objs.size cn = none := by
  rw [FreshClassActual.const_from_eq_firstM, ancestors_module hc hd]
  simp only [List.firstM, const_own_fresh hd]
  rfl

theorem const_from_eigen_other (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (htop : m.lexicalNamespace = Boot.objectId) {cn : String} (hn : cn ≠ name) :
    constLookupFrom h₁ (m.heap.objs.size + 1) cn = constLookupFrom m.heap Boot.moduleId cn := by
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ hc.boot.2.2.2.2
  rw [FreshClassActual.const_from_eq_firstM, FreshClassActual.const_from_eq_firstM,
    ancestors_eigen hc hs hd]
  have hf : constOwn h₁ (m.heap.objs.size + 1) cn = none := by
    simp [constOwn, Heap.classPayload?, get_eigen, attachedModuleEigen]
  simp only [List.firstM, hf]
  exact firstM_congr (fun j hj => constOwn_other htop hc.boot.2.2.2.2
    (ClsGrow.ancestors_mem_lt hc hc.boot.2.1 j hj) hn)

theorem fallback_fresh_meta (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hp : ConstFallback m.heap Boot.moduleId) : ConstFallback h₁ (m.heap.objs.size + 1) := by
  intro cn hn
  have hne : cn ≠ name := by intro he; subst cn; rw [const_self htop ho] at hn; cases hn
  rw [const_from_eigen_other hc hs htop hne]
  exact hp cn ((const_other htop hc.boot.2.2.2.2 hne).symm.trans hn)

theorem main_constants (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hp : ∀ cn, constLookupFrom m.heap Boot.objectId cn = constLookup m.heap cn) :
    ∀ cn, constLookupFrom h₁ Boot.objectId cn = constLookup h₁ cn := by
  intro cn
  by_cases hn : cn = name
  · subst cn
    have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ hc.chains.boot.2.2.2.2
    have hown : constOwn h₁ Boot.objectId name = some (.ref m.heap.objs.size) := by
      rw [← Subclass.const_eq_own]; exact const_self htop ho
    rw [FreshClassActual.const_from_eq_firstM, ancestors_old hc.chains hs hd hc.chains.boot.2.2.2.2,
      hc.objectChain, const_self htop ho]
    simp only [List.firstM, hown]
    rfl
  · rw [const_from_old_other hc.chains hs htop hc.chains.boot.2.2.2.2 hn,
      const_other htop hc.chains.boot.2.2.2.2 hn]
    exact hp cn

theorem instance_constants_fresh (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hp : ∀ cn, constLookupFrom m.heap Boot.objectId cn = constLookup m.heap cn) :
    ∀ cn, instanceConstResolve h₁ m.heap.objs.size cn = constLookup h₁ cn := by
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ hc.chains.boot.2.2.2.2
  intro cn
  simp only [instanceConstResolve, List.firstM, const_own_fresh hd,
    const_from_module hc.chains hd, main_constants hc hs htop ho hp]
  simp [Heap.classPayload?, get_module hd, namedObject, modPayload]
  rfl

theorem const_scope {body : RubyCore.Expr} (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (hm : MainReady m) (hp : ConstScopeOk m) : ConstScopeOk (machine m name body) := by
  have htop : m.lexicalNamespace = Boot.objectId := by
    simp only [Machine.lexicalNamespace, hm.cref, List.headD_nil]
  have hconst (cn : String) : constLookupFrom m.heap Boot.objectId cn = constLookup m.heap cn := by
    rw [← constResolveAt_top hm.cref]; exact hp cn
  intro cn
  simp only [constResolveAt, Interp.lexicalConstant, Machine.lexicalNamespace,
    current_frame, freshModFrame, hm.cref, List.headD_cons]
  change instanceConstResolve (heap m name) m.heap.objs.size cn = constLookup (heap m name) cn
  exact instance_constants_fresh hc hs htop hm.classLive hconst cn

#print axioms instance_constants_fresh
#print axioms const_scope
#print axioms fallback_fresh_meta
end Checker.Soundness.FreshModuleActual
