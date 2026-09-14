import Denote.Sem.ClassConstants
import Denote.Sem.ClassCore

/-! Constant-table framing for fresh class registration. Qualified claims need an already
resolved owner and a leaf name untouched by registration; otherwise formerly conditional
claims may become active. These are explicit input obligations, not assumed postconditions. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

structure ClassTablesFrame (κ : Ctx) (name : String) (m : Machine) : Prop where
  consts : ∀ cn τ, constGet? κ cn = some τ → FirstOrder τ = true
  paths : ∀ owner cn τ, envGet? κ.consts (constKeyIn owner cn) = some τ →
    FirstOrder τ = true ∧ cn ≠ name ∧ ∃ k, classNamed? m.heap owner = some k
  nested : ∀ owner cn c, clsGet? κ.classes (owner ++ "::" ++ cn) = some c →
    cn ≠ name ∧ ∃ k, classNamed? m.heap owner = some k

theorem ClassTablesFrame.heap {κ : Ctx} {name : String} {m n : Machine}
    (h : ClassTablesFrame κ name m) (hh : n.heap = m.heap) : ClassTablesFrame κ name n :=
  ⟨h.consts, by simpa only [hh] using h.paths, by simpa only [hh] using h.nested⟩

theorem ClassTablesFrame.empty {κ : Ctx} {name : String} {m : Machine}
    (hc : κ.consts = []) (hk : κ.classes = []) : ClassTablesFrame κ name m := by
  refine ⟨?_, ?_, ?_⟩
  · intro cn τ ht
    simp only [constGet?, constPaths] at ht
    cases he : κ.frame <;> simp [he, hc, envGet?] at ht
  · intro owner cn τ ht; simp [hc, envGet?] at ht
  · intro owner cn c ht; simp [hk, clsGet?] at ht

namespace FreshClass
open RubyCore.Proof.Judgment (freshClsHeap)
variable {κ : Ctx} {m n : Machine} {name : String} {e : ObjId}

theorem constants (ho : Boot.objectId < m.heap.objs.size)
    (hn : constOwn m.heap Boot.objectId name = none)
    (hh : n.heap = freshClsHeap m.heap Boot.objectId name name e)
    (hd : DataPres m.heap n.heap) (hs : ConstScopeOk m) (hs' : ConstScopeOk n)
    (hf : ∀ cn τ, constGet? κ cn = some τ → FirstOrder τ = true)
    (hp : ConstsOk κ m) : ConstsOk κ n := by
  intro cn τ ht
  obtain ⟨v, hv, hty⟩ := hp cn τ ht
  have hne : cn ≠ name := by
    intro he; subst cn
    rw [hs, constLookup_eq_own, hn] at hv
    cases hv
  refine ⟨v, ?_, hd.denM (hf cn τ ht) hty⟩
  rw [hs', hh, const_other ho hne, ← hs]
  exact hv

theorem paths (hc : Proof.ChainsIn m.heap) (hs : Proof.Saturated m.heap)
    (hn : constOwn m.heap Boot.objectId name = none)
    (hh : n.heap = freshClsHeap m.heap Boot.objectId name name e)
    (hd : DataPres m.heap n.heap) (hf : ClassTablesFrame κ name m)
    (hp : ConstPathsOk κ m) : ConstPathsOk κ n := by
  intro owner cn τ k ht hk v hv
  obtain ⟨hfo, hne, j, hj⟩ := hf.paths owner cn τ ht
  have hj' := named (e := e) hc.boot.2.2.2.2 hn hj
  rw [← hh] at hj'
  have heq : j = k := Option.some.inj (hj'.symm.trans hk)
  subst k
  rw [hh, const_from_old_other hc hs (named_live hj) hne] at hv
  exact hd.denM hfo (hp owner cn τ j ht hj v hv)

theorem nested (hc : Proof.ChainsIn m.heap) (hs : Proof.Saturated m.heap)
    (hn : constOwn m.heap Boot.objectId name = none)
    (hh : n.heap = freshClsHeap m.heap Boot.objectId name name e)
    (hd : DataPres m.heap n.heap) (hf : ClassTablesFrame κ name m)
    (hp : NestedClassesOk κ.classes m) : NestedClassesOk κ.classes n := by
  intro owner cn c ht k v hk hv
  obtain ⟨hne, j, hj⟩ := hf.nested owner cn c ht
  have hj' := named (e := e) hc.boot.2.2.2.2 hn hj
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
end FreshClass
end Ratchet.Denote
