import Denote.Sem.ClassFrame

/-! An empty fresh class scope adds no shadowing. The newly registered name is a separate
case; other constants retain both lexical and inherited resolution from the main scope. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap freshClsMachine freshModFrame)

variable {h : Heap} {name : String} {e : ObjId}
local notation "h₁" => freshClsHeap h Boot.objectId name name e

theorem const_self (ho : (h.classPayload? Boot.objectId).isSome = true) :
    constOwn h₁ Boot.objectId name = some (.ref h.objs.size) := by
  have hl := lt_size_of_classPayload ho
  rw [Proof.Judgment.constOwn_old_freshC hl hl]
  exact Proof.Judgment.constOwn_constSetIn_self ho hl

theorem const_own_old_other (ho : Boot.objectId < h.objs.size) {k : ObjId}
    (hk : k < h.objs.size) {cn : String} (hn : cn ≠ name) :
    constOwn h₁ k cn = constOwn h k cn := by
  rw [Proof.Judgment.constOwn_old_freshC ho hk]
  exact Proof.constOwn_constSetIn_ne h Boot.objectId k name cn _ (Or.inr hn)

theorem const_from_eq_firstM (heap : Heap) (k : ObjId) (cn : String) :
    constLookupFrom heap k cn = (ancestors heap k).firstM (fun j => constOwn heap j cn) := by
  unfold constLookupFrom
  apply Proof.Judgment.firstM_congr
  intro j _
  cases hp : heap.classPayload? j <;> simp [constOwn, hp]

theorem const_from_old_other (hc : Proof.ChainsIn h) (hs : Proof.Saturated h)
    {k : ObjId} (hk : k < h.objs.size) {cn : String} (hn : cn ≠ name) :
    constLookupFrom h₁ k cn = constLookupFrom h k cn := by
  rw [const_from_eq_firstM, const_from_eq_firstM, Proof.Judgment.ancestors_old_freshC hc hs hk]
  exact Proof.Judgment.firstM_congr (fun j hj =>
    const_own_old_other hc.boot.2.2.2.2 (Proof.ClsGrow.ancestors_mem_lt hc hk j hj) hn)

theorem const_from_class_other (hc : Proof.ChainsIn h) (hs : Proof.Saturated h)
    {cn : String} (hn : cn ≠ name) :
    constLookupFrom h₁ h.objs.size cn = constLookupFrom h Boot.objectId cn := by
  rw [const_from_eq_firstM, const_from_eq_firstM, Proof.Judgment.ancestors_freshC_k hc hs]
  simp only [List.firstM, Proof.Judgment.constOwn_freshC_k]
  exact Proof.Judgment.firstM_congr (fun j hj => const_own_old_other hc.boot.2.2.2.2
    (Proof.ClsGrow.ancestors_mem_lt hc hc.boot.2.2.2.2 j hj) hn)

variable {m : Machine} {body : RubyCore.Expr}
local notation "entry" => freshClsMachine m Boot.objectId m.currentFrame.cref name name e body

theorem const_scope (hc : Proof.ChainsIn m.heap) (hs : Proof.Saturated m.heap)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hcref : m.currentFrame.cref = [Boot.objectId]) (howner : m.currentFrame.defmod = Boot.objectId)
    (hscope : ConstScopeOk m) : ConstScopeOk entry := by
  intro cn
  rw [constResolveAt, current_frame]
  change (((m.heap.objs.size :: m.currentFrame.cref).firstM
    (fun j => constOwn (entry).heap j cn)).orElse
    (fun _ => constLookupFrom (entry).heap m.heap.objs.size cn)) = _
  rw [hcref]
  dsimp only [freshClsMachine]
  by_cases hn : cn = name
  · subst cn
    have hreg := const_self (name := name) (e := e) ho
    change (([m.heap.objs.size, Boot.objectId].firstM (fun j =>
      constOwn (freshClsHeap m.heap Boot.objectId name name e) j name)).orElse _) = _
    simp only [List.firstM, Proof.Judgment.constOwn_freshC_k, hreg]
    exact (constLookup_eq_own _ name).trans hreg |>.symm
  · have hp := hscope cn
    rw [constResolveAt, hcref, howner] at hp
    have hnone (v : Option Value) : (none <|> v) = v := by cases v <;> rfl
    simpa only [List.firstM, Proof.Judgment.constOwn_freshC_k,
      const_own_old_other hc.boot.2.2.2.2 hc.boot.2.2.2.2 hn,
      const_from_class_other hc hs hn, const_other hc.boot.2.2.2.2 hn,
      hnone] using hp

#print axioms const_from_class_other
#print axioms const_scope
end Ratchet.Denote.FreshClass
