import Denote.Sem.Class.ClassData
import Denote.Sem.Core.Framed
import RubyCore.Proof.Judgment.ModFresh

/-! First-order data across actual fresh top-level module allocation. The model's heap
composite is reused only for its operational facts, without an older typing judgment.
Module ancestry is an explicit heap premise, retained separately by CoreOk. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshModule
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment

variable {h : Heap} {name : String}
local notation "h₁" => freshModHeap h Boot.objectId name name

theorem fields {o : ObjId} (ho : o < h.objs.size) :
    ((h₁).get o).ivars = (h.get o).ivars ∧ ((h₁).get o).klass = (h.get o).klass ∧
      ((h₁).get o).eigen = (h.get o).eigen ∧ ((h₁).get o).frozen = (h.get o).frozen := by
  rw [freshModHeap_get_old ho]
  exact get_constSetIn_fields h Boot.objectId name _ o

theorem classPayload_old_isSome {k : ObjId} (hk : k < h.objs.size) :
    ((h₁).classPayload? k).isSome = (h.classPayload? k).isSome := by
  unfold Heap.classPayload?
  rw [freshModHeap_get_old hk]
  exact classPayload?_isSome_constSetIn h Boot.objectId k name _

theorem classPayload_live {k : ObjId} (hk : (h.classPayload? k).isSome = true) :
    ((h₁).classPayload? k).isSome = true :=
  (classPayload_old_isSome (lt_size_of_classPayload hk)).trans hk

theorem classOf_old {o : ObjId} (ho : o < h.objs.size) :
    classOf h₁ (.ref o) = classOf h (.ref o) := by
  simp only [classOf, (fields ho).2.1, (fields ho).2.2.1]

theorem get_old_nonclass {o : ObjId} (ho : o < h.objs.size)
    (hp : h.classPayload? o = none) : (h₁).get o = h.get o := by
  rw [freshModHeap_get_old ho]
  by_cases he : o = Boot.objectId
  · subst o; simp only [hmidOf, constSetIn, hp]
  · exact Static.get_constSetIn_ne h Boot.objectId o name _ he

/-- No non-class payload is created or changed, including beyond the old heap. -/
theorem get_nonclass {o : ObjId} (hp : (h₁).classPayload? o = none) : (h₁).get o = h.get o := by
  by_cases hl : o < h.objs.size
  · have hp₀ : h.classPayload? o = none := by
      have hh := classPayload_old_isSome (name := name) hl
      rw [hp] at hh
      cases he : h.classPayload? o <;> simp_all
    exact get_old_nonclass hl hp₀
  · by_cases hk : o = h.objs.size
    · subst o; rw [freshModHeap_cp_k] at hp; cases hp
    · by_cases he : o = h.objs.size + 1
      · subst o; rw [freshModHeap_cp_e] at hp; cases hp
      · have hout := Nat.le_of_not_lt (not_lt_add_two hl hk he)
        rw [get_oob h (Nat.le_of_not_lt hl), get_oob _ (by rw [freshModHeap_size]; exact hout)]

theorem const_eq_own (g : Heap) (cn : String) :
    constLookup g cn = constOwn g Boot.objectId cn := by
  cases hp : g.classPayload? Boot.objectId <;> simp [constLookup, constOwn, hp]

theorem const_other (ho : Boot.objectId < h.objs.size) {cn : String} (hn : cn ≠ name) :
    constLookup h₁ cn = constLookup h cn := by
  rw [const_eq_own, const_eq_own, constOwn_old_fresh ho ho]
  exact constOwn_constSetIn_ne h Boot.objectId Boot.objectId name cn _ (Or.inr hn)

theorem named (ho : Boot.objectId < h.objs.size) (hf : constOwn h Boot.objectId name = none)
    {cn : String} {k : ObjId} (hk : classNamed? h cn = some k) : classNamed? h₁ cn = some k := by
  have hcn : cn ≠ name := by
    intro he; subst cn
    simp only [classNamed?, const_eq_own, hf] at hk; cases hk
  unfold classNamed? at hk ⊢
  rw [const_other ho hcn]
  cases hl : constLookup h cn with
  | none => simp only [hl] at hk; cases hk
  | some v =>
    cases v <;> try (simp only [hl] at hk; cases hk)
    rename_i o
    simp only [hl] at hk ⊢
    split at hk
    · rename_i hp
      simp only [classPayload_live hp, ite_true]; exact hk
    · cases hk

theorem named_new (ho : Boot.objectId < h.objs.size)
    (hp : (h.classPayload? Boot.objectId).isSome = true) :
    classNamed? h₁ name = some h.objs.size := by
  unfold classNamed?
  rw [const_eq_own, constOwn_old_fresh ho ho, constOwn_constSetIn_self hp ho]
  simp only [freshModHeap_cp_k, Option.isSome_some, ite_true]

theorem fresh_basic (hc : ClassReady h) (hs : Saturated h)
    (hb : ancestors h Boot.basicObjectId = [Boot.basicObjectId])
    (hm : (ancestors h Boot.moduleId).contains Boot.basicObjectId = true)
    {o : ObjId} (ho : h.objs.size ≤ o) : isA h₁ (.ref o) Boot.basicObjectId = true := by
  by_cases hk : o = h.objs.size
  · subst o
    rw [isA, classOf_fresh_k, ancestors_fresh_e hc.chains hs]
    simp only [List.contains_cons, hm, Bool.or_true]
  · by_cases he : o = h.objs.size + 1
    · subst o
      rw [isA, classOf_fresh_e, ancestors_old_fresh hc.chains hs hc.chains.boot.1]
      exact hc.classBasic
    · have hout := Nat.le_of_not_lt (not_lt_add_two (Nat.not_lt_of_ge ho) hk he)
      have hl := Nat.lt_of_le_of_lt (by decide : Boot.basicObjectId ≤ Boot.objectId)
        hc.chains.boot.2.2.2.2
      rw [isA, classOf_oob _ (by rw [freshModHeap_size]; exact hout),
        ancestors_old_fresh hc.chains hs hl, hb]
      rfl

theorem dataPres (hc : ClassReady h) (hs : Saturated h)
    (hb : ancestors h Boot.basicObjectId = [Boot.basicObjectId])
    (hf : constOwn h Boot.objectId name = none)
    (hm : (ancestors h Boot.moduleId).contains Boot.basicObjectId = true) : DataPres h h₁ :=
  dataPres_of_class_growth hc.chains hb (by rw [freshModHeap_size]; exact Nat.le_add_right _ _)
    (fun o ho => ⟨(fields ho).1, (fields ho).2.1, (fields ho).2.2.1⟩)
    (fun _ ho hp => get_old_nonclass ho hp) (fun _ hk => ancestors_old_fresh hc.chains hs hk)
    (fun _ ho => fresh_basic hc hs hb hm ho) (fun _ _ hk => named hc.chains.boot.2.2.2.2 hf hk)

/-- Caller framing after balancing the module-body frame; the body itself is not run here. -/
theorem framed {κ : Ctx} {Γ : Env} {I : Ty} {m n : Machine}
    (hm : StateOk κ Γ I m) (hf : constOwn m.heap Boot.objectId name = none)
    (hh : n.heap = freshModHeap m.heap Boot.objectId name name)
    (hs : n.stack = m.stack) (hfr : FramePres m n)
    (hphase : n.preludeMode = m.preludeMode := by rfl) : Framed m n := by
  have hd : DataPres m.heap n.heap := by
    rw [hh]
    exact dataPres hm.core.classReady hm.sat hm.core.basicSelf hf hm.core.moduleBasic
  exact ⟨hs, fun k hk => by rw [hh]; exact classPayload_live hk,
    hd.nominal, fun _ ht _ hv => hd.denM ht hv, hfr,
    .of_unchanged (by rw [hh, freshModHeap_size]; exact Nat.le_add_right _ _)
      (fun o ho => by funext x; simp only [hh, ivarOf, (fields ho).1])
      (fun _ ht _ hv => hd.denM ht hv),
    (fun o ho e he => by rw [hh, (fields ho).2.2.1]; exact he), (by
      rw [hh]
      exact .of_nonclass (fun _ ho hp => get_old_nonclass ho hp)), hphase⟩

#print axioms dataPres
#print axioms framed
end Ratchet.Denote.FreshModule
