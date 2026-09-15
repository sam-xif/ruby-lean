import Denote.Sem.ClassTablesFrame
import Denote.Sem.SubclassConstants

/-! Preserve first-order constant and nested-class claims through arbitrary subclass
registration. Table framing prevents a new name from activating unsupported old claims. -/
set_option autoImplicit false
namespace Ratchet.Denote.Subclass
open RubyCore Ratchet

variable {κ : Ctx} {m n : Machine} {name q : String} {parent eParent : ObjId}

theorem constants (ho : Boot.objectId < m.heap.objs.size)
    (hn : constOwn m.heap Boot.objectId name = none)
    (hh : n.heap = heap m.heap Boot.objectId name q parent eParent)
    (hd : DataPres m.heap n.heap) (hs : ConstScopeOk m) (hs' : ConstScopeOk n)
    (hf : ∀ cn τ, constGet? κ cn = some τ → FirstOrder τ = true)
    (hp : ConstsOk κ m) : ConstsOk κ n := by
  intro cn τ ht
  obtain ⟨v, hv, hty⟩ := hp cn τ ht
  have hne : cn ≠ name := by
    intro he; subst cn
    rw [hs, const_eq_own, hn] at hv
    cases hv
  refine ⟨v, ?_, hd.denM (hf cn τ ht) hty⟩
  rw [hs', hh, const_other ho hne, ← hs]
  exact hv

theorem paths (hc : Proof.ChainsIn m.heap) (hs : Proof.Saturated m.heap)
    (hn : constOwn m.heap Boot.objectId name = none)
    (hh : n.heap = heap m.heap Boot.objectId name q parent eParent)
    (hd : DataPres m.heap n.heap) (hf : ClassTablesFrame κ name m)
    (hp : ConstPathsOk κ m) : ConstPathsOk κ n := by
  intro owner cn τ k ht hk v hv
  obtain ⟨hfo, hne, j, hj⟩ := hf.paths owner cn τ ht
  have hj' := named (q := q) (parent := parent) (eParent := eParent) hc.boot.2.2.2.2 hn hj
  rw [← hh] at hj'
  have heq : j = k := Option.some.inj (hj'.symm.trans hk)
  subst k
  rw [hh, const_from_old_other hc hs (named_live hj) hne] at hv
  exact hd.denM hfo (hp owner cn τ j ht hj v hv)

theorem nested (hc : Proof.ChainsIn m.heap) (hs : Proof.Saturated m.heap)
    (hn : constOwn m.heap Boot.objectId name = none)
    (hh : n.heap = heap m.heap Boot.objectId name q parent eParent)
    (hd : DataPres m.heap n.heap) (hf : ClassTablesFrame κ name m)
    (hp : NestedClassesOk κ.classes m) : NestedClassesOk κ.classes n := by
  intro owner cn c ht k v hk hv
  obtain ⟨hne, j, hj⟩ := hf.nested owner cn c ht
  have hj' := named (q := q) (parent := parent) (eParent := eParent) hc.boot.2.2.2.2 hn hj
  rw [← hh] at hj'
  have heq : j = k := Option.some.inj (hj'.symm.trans hk)
  subst k
  rw [hh, const_from_old_other hc hs (named_live hj) hne] at hv
  have hv₀ : denM (.clsOf (owner ++ "::" ++ cn)) m v := by
    simpa only [denM] using hp owner cn c ht j v hj hv
  simpa only [denM] using hd.denM rfl hv₀

#print axioms constants
#print axioms paths
#print axioms nested
end Ratchet.Denote.Subclass
