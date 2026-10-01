import Denote.Sem.Class.ClassScopeActual

/-! Repair the existing constant-resolution argument for the real singleton cref.
The new class's empty own table falls through to Object's retained ancestor lookup. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClassActual
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment
variable {m : Machine} {name : String} {e : ObjId}
local notation "h₁" => heap m name e

theorem const_from_eq_firstM (g : Heap) (k : ObjId) (cn : String) :
    constLookupFrom g k cn = (ancestors g k).firstM (fun j => constOwn g j cn) := by
  unfold constLookupFrom
  apply firstM_congr
  intro j _
  cases hp : g.classPayload? j <;> simp [constOwn, hp]

theorem const_own_fresh (hd : m.lexicalNamespace < m.heap.objs.size) (cn : String) :
    constOwn h₁ m.heap.objs.size cn = none := by
  simp [constOwn, Heap.classPayload?, get_class hd, namedObject, freshClassPayload]

theorem const_from_class (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) (cn : String) :
    constLookupFrom h₁ m.heap.objs.size cn = constLookupFrom h₁ Boot.objectId cn := by
  rw [const_from_eq_firstM, const_from_eq_firstM, ancestors_class hc hs hd,
    ancestors_old hc hs hd hc.boot.2.2.2.2]
  simp only [List.firstM, const_own_fresh hd]
  rfl

theorem const_from_eigen_other (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (htop : m.lexicalNamespace = Boot.objectId) (hep : e < m.heap.objs.size)
    {cn : String} (hn : cn ≠ name) :
    constLookupFrom h₁ (m.heap.objs.size + 1) cn = constLookupFrom m.heap e cn := by
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ hc.boot.2.2.2.2
  rw [const_from_eq_firstM, const_from_eq_firstM, ancestors_eigen hc hs hd hep]
  have hf : constOwn h₁ (m.heap.objs.size + 1) cn = none := by
    simp [constOwn, Heap.classPayload?, get_eigen, attachedClassEigen]
  simp only [List.firstM, hf]
  exact firstM_congr (fun j hj => constOwn_other htop hc.boot.2.2.2.2 (ClsGrow.ancestors_mem_lt hc hep j hj) hn)

theorem fallback_fresh_meta (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true) (hep : e < m.heap.objs.size)
    (hp : ConstFallback m.heap e) : ConstFallback h₁ (m.heap.objs.size + 1) := by
  intro cn hn
  have hne : cn ≠ name := by intro he; subst cn; rw [const_self htop ho] at hn; cases hn
  rw [const_from_eigen_other hc hs htop hep hne]
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
    rw [const_from_eq_firstM, ancestors_old hc.chains hs hd hc.chains.boot.2.2.2.2,
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
    const_from_class hc.chains hs hd, main_constants hc hs htop ho hp]
  cases hr : constLookup h₁ cn <;>
    (simp [Heap.classPayload?, get_class hd, namedObject, freshClassPayload]; rfl)

theorem const_scope {body : RubyCore.Expr} (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (hm : MainReady m) (hp : ConstScopeOk m) : ConstScopeOk (machine m name e body) := by
  have htop : m.lexicalNamespace = Boot.objectId := by
    simp only [Machine.lexicalNamespace, hm.cref, List.headD_nil]
  have hconst (cn : String) : constLookupFrom m.heap Boot.objectId cn = constLookup m.heap cn := by
    rw [← constResolveAt_top hm.cref]; exact hp cn
  intro cn
  simp only [constResolveAt, Interp.lexicalConstant, Machine.lexicalNamespace,
    current_frame, freshModFrame, hm.cref, List.headD_cons]
  change instanceConstResolve (heap m name e) m.heap.objs.size cn = constLookup (heap m name e) cn
  exact instance_constants_fresh hc hs htop hm.classLive hconst cn

#print axioms main_constants
#print axioms instance_constants_fresh
#print axioms const_scope
#print axioms fallback_fresh_meta
end Ratchet.Denote.FreshClassActual
