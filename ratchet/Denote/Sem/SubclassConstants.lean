import Denote.Sem.SubclassFrame

/-! Fresh subclass scopes read their own empty table, then Object, then inherited
constants. Parent/global agreement is a retained scope fact, not implied by ancestry. -/
set_option autoImplicit false
namespace Ratchet.Denote.Subclass
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment

variable {h : Heap} {name q : String} {parent eParent : ObjId}
local notation "h₁" => heap h Boot.objectId name q parent eParent

theorem const_own_self (ho : (h.classPayload? Boot.objectId).isSome = true) :
    constOwn h₁ Boot.objectId name = some (.ref h.objs.size) := by
  rw [← const_eq_own]; exact const_self ho

theorem const_own_old_other {k : ObjId} (hk : k < h.objs.size) {cn : String} (hn : cn ≠ name) :
    constOwn h₁ k cn = constOwn h k cn := by
  rw [constOwn_old hk]
  exact constOwn_constSetIn_ne h Boot.objectId k name cn _ (Or.inr hn)

theorem const_own_fresh (cn : String) : constOwn h₁ h.objs.size cn = none := by
  simp [constOwn, Heap.classPayload?, get_class, classObjE, classObj]

theorem const_from_eq_firstM (g : Heap) (k : ObjId) (cn : String) :
    constLookupFrom g k cn = (ancestors g k).firstM (fun j => constOwn g j cn) := by
  unfold constLookupFrom
  apply firstM_congr
  intro j _
  cases hp : g.classPayload? j <;> simp [constOwn, hp]

theorem const_from_old_other (hc : ChainsIn h) (hs : Saturated h)
    {k : ObjId} (hk : k < h.objs.size) {cn : String} (hn : cn ≠ name) :
    constLookupFrom h₁ k cn = constLookupFrom h k cn := by
  rw [const_from_eq_firstM, const_from_eq_firstM, ancestors_old hc hs hk]
  exact firstM_congr (fun j hj => const_own_old_other (ClsGrow.ancestors_mem_lt hc hk j hj) hn)

theorem const_from_class_other (hc : ChainsIn h) (hs : Saturated h)
    (hp : parent < h.objs.size) {cn : String} (hn : cn ≠ name) :
    constLookupFrom h₁ h.objs.size cn = constLookupFrom h parent cn := by
  rw [const_from_eq_firstM, const_from_eq_firstM, ancestors_class hc hs hp]
  simp only [List.firstM, const_own_fresh]
  exact firstM_congr (fun j hj => const_own_old_other (ClsGrow.ancestors_mem_lt hc hp j hj) hn)

/-- A retained instance scope cannot reveal an inherited constant absent globally. -/
theorem fallback_of_instance {k : ObjId}
    (hp : ∀ cn, instanceConstResolve h k cn = constLookup h cn) (cn : String) :
    (constLookup h cn).orElse (fun _ => constLookupFrom h k cn) = constLookup h cn := by
  cases hg : constLookup h cn with
  | some v => rfl
  | none =>
    have ho : constOwn h Boot.objectId cn = none := by rwa [const_eq_own] at hg
    have he := hp cn
    rw [instanceConstResolve, hg] at he
    cases hk : constOwn h k cn with
    | none => simpa [List.firstM, hk, ho, show (failure : Option Value) = none from rfl] using he
    | some v => simp only [List.firstM, hk] at he; cases he

theorem fallback_of_main {m : Machine} (hcref : m.currentFrame.cref = [Boot.objectId])
    (howner : m.currentFrame.defmod = Boot.objectId) (hscope : ConstScopeOk m) (cn : String) :
    (constLookup m.heap cn).orElse (fun _ => constLookupFrom m.heap Boot.objectId cn) = constLookup m.heap cn := by
  have hp := hscope cn
  rw [constResolveAt, hcref, howner] at hp
  have hfail (v : Option Value) : (v <|> failure) = v := by cases v <;> rfl
  simpa only [List.firstM, hfail, const_eq_own] using hp

theorem instance_constants_fresh (hc : ChainsIn h) (hs : Saturated h)
    (ho : (h.classPayload? Boot.objectId).isSome = true) (hp : parent < h.objs.size)
    (hparent : ∀ cn, (constLookup h cn).orElse (fun _ => constLookupFrom h parent cn) = constLookup h cn) :
    ∀ cn, instanceConstResolve h₁ h.objs.size cn = constLookup h₁ cn := by
  intro cn
  by_cases hn : cn = name
  · subst cn
    simp only [instanceConstResolve, List.firstM, const_own_fresh, const_own_self ho, const_self ho]
    rfl
  · simp only [instanceConstResolve, List.firstM, const_own_fresh,
      const_own_old_other hc.boot.2.2.2.2 hn, const_from_class_other hc hs hp hn,
      const_other hc.boot.2.2.2.2 hn]
    have hnone (v : Option Value) : (none <|> v) = v := by cases v <;> rfl
    have hfail (v : Option Value) : (v <|> failure) = v := by cases v <;> rfl
    simpa only [const_eq_own, hnone, hfail] using hparent cn

theorem const_scope {m : Machine} {body : RubyCore.Expr}
    (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true) (hp : parent < m.heap.objs.size)
    (hcref : m.currentFrame.cref = [Boot.objectId])
    (hparent : ∀ cn, (constLookup m.heap cn).orElse (fun _ => constLookupFrom m.heap parent cn) =
      constLookup m.heap cn) :
    ConstScopeOk (machine m Boot.objectId m.currentFrame.cref name q parent eParent body) := by
  intro cn
  rw [constResolveAt, current_frame]
  simpa only [freshModFrame, hcref, machine, instanceConstResolve] using
    instance_constants_fresh (name := name) (q := q) (eParent := eParent) hc hs ho hp hparent cn

#print axioms const_from_class_other
#print axioms fallback_of_instance
#print axioms instance_constants_fresh
#print axioms const_scope
end Ratchet.Denote.Subclass
