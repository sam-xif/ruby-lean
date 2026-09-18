import Denote.Sem.Class.ClassData
import Denote.Sem.Subclass.MetaReadyClass
import Denote.Sem.Core.Framed

/-! Old first-order data across fresh top-level subclass registration. The parent is
arbitrary; the new metaclass's BasicObject ancestry comes from its retained parent site. -/
set_option autoImplicit false
namespace Ratchet.Denote.Subclass
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment

variable {h : Heap} {name q : String} {parent eParent : ObjId}
local notation "h₁" => heap h Boot.objectId name q parent eParent

theorem classPayload_live {k : ObjId} (hk : (h.classPayload? k).isSome = true) :
    ((h₁).classPayload? k).isSome = true := by
  unfold Heap.classPayload?
  rw [get_old (lt_size_of_classPayload hk)]
  exact (classPayload?_isSome_constSetIn h Boot.objectId k name _).trans hk

theorem get_old_nonclass {o : ObjId} (ho : o < h.objs.size)
    (hp : h.classPayload? o = none) : (h₁).get o = h.get o := by
  rw [get_old ho]
  by_cases he : o = Boot.objectId
  · subst o; simp only [hmidOf, constSetIn, hp]
  · exact Static.get_constSetIn_ne h Boot.objectId o name _ he

theorem get_nonclass {o : ObjId} (hp : (h₁).classPayload? o = none) : (h₁).get o = h.get o := by
  by_cases hl : o < h.objs.size
  · have hp₀ : h.classPayload? o = none := by
      have hh := classPayload_old_isSome (d := Boot.objectId) (name := name) (q := q)
        (parent := parent) (eParent := eParent) hl
      rw [hp] at hh
      cases he : h.classPayload? o <;> simp_all
    exact get_old_nonclass hl hp₀
  · by_cases hk : o = h.objs.size
    · subst o; simp only [Heap.classPayload?, get_class, classObjE] at hp; contradiction
    · by_cases he : o = h.objs.size + 1
      · subst o; simp only [Heap.classPayload?, get_eigen, eigObjC] at hp; contradiction
      · have hout := Nat.le_of_not_lt (not_lt_add_two hl hk he)
        rw [get_oob h (Nat.le_of_not_lt hl), get_oob _ (by rw [size]; exact hout)]

theorem const_eq_own (g : Heap) (cn : String) :
    constLookup g cn = constOwn g Boot.objectId cn := by
  cases hp : g.classPayload? Boot.objectId <;> simp [constLookup, constOwn, hp]

theorem const_other (ho : Boot.objectId < h.objs.size) {cn : String} (hn : cn ≠ name) :
    constLookup h₁ cn = constLookup h cn := by
  rw [const_eq_own, const_eq_own]
  unfold constOwn
  rw [grow.payloadOld (by rwa [hmid_size])]
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

theorem fresh_basic (hc : ClassReady h) (hs : Saturated h)
    (hb : ancestors h Boot.basicObjectId = [Boot.basicObjectId])
    (hep : eParent < h.objs.size) (hr : (ancestors h eParent).contains Boot.basicObjectId = true)
    {o : ObjId} (ho : h.objs.size ≤ o) : isA h₁ (.ref o) Boot.basicObjectId = true := by
  by_cases hk : o = h.objs.size
  · subst o
    simp only [isA, classOf, get_class, classObjE]
    rw [ancestors_eigen hc.chains hs hep]
    simp only [List.contains_cons, hr, Bool.or_true]
  · by_cases he : o = h.objs.size + 1
    · subst o
      simp only [isA, classOf, get_eigen, eigObjC]
      rw [ancestors_old hc.chains hs hc.chains.boot.1]; exact hc.classBasic
    · have hout := Nat.le_of_not_lt (not_lt_add_two (Nat.not_lt_of_ge ho) hk he)
      have hl := Nat.lt_of_le_of_lt (by decide : Boot.basicObjectId ≤ Boot.objectId)
        hc.chains.boot.2.2.2.2
      rw [isA, classOf_oob _ (by rw [size]; exact hout), ancestors_old hc.chains hs hl, hb]
      rfl

theorem dataPres (hc : ClassReady h) (hs : Saturated h)
    (hb : ancestors h Boot.basicObjectId = [Boot.basicObjectId])
    (hf : constOwn h Boot.objectId name = none) (hep : eParent < h.objs.size)
    (hr : (ancestors h eParent).contains Boot.basicObjectId = true) : DataPres h h₁ :=
  dataPres_of_class_growth hc.chains hb (by rw [size]; exact Nat.le_add_right _ _)
    (fun o ho => ⟨(fields ho).1, (fields ho).2.1, (fields ho).2.2.1⟩)
    (fun _ ho hp => get_old_nonclass ho hp) (fun _ hk => ancestors_old hc.chains hs hk)
    (fun _ ho => fresh_basic hc hs hb hep hr ho) (fun _ _ hk => named hc.chains.boot.2.2.2.2 hf hk)

/-- Caller framing after balancing the class-body frame. The heap part preserves every
first-order type and old object's field observations, not just the constructed class. -/
theorem framed {κ : Ctx} {Γ : Env} {I : Ty} {m n : Machine} {c : Cls}
    (hm : StateOk κ Γ I m) (hc : c ∈ κ.classes) (hp : classNamed? m.heap c.name = some parent)
    (hf : constOwn m.heap Boot.objectId name = none)
    (he : (m.heap.get parent).eigen = some eParent)
    (hh : n.heap = heap m.heap Boot.objectId name name parent eParent)
    (hs : n.stack = m.stack) (hfr : FramePres m n) : Framed m n := by
  obtain ⟨ep, he', hr, _⟩ := hm.classSites.metaclass hc hp
  rw [he] at he'; cases he'
  have hl := hm.core.classReady.constRefs c.name parent (classNamed_constOwn hp)
  have hd : DataPres m.heap n.heap := by
    rw [hh]
    exact dataPres hm.core.classReady hm.sat hm.core.basicSelf hf
      (hm.core.classReady.chains.eigen parent hl eParent he) hr
  exact ⟨hs, fun k hk => by rw [hh]; exact classPayload_live hk,
    hd.nominal, fun _ ht _ hv => hd.denM ht hv, hfr,
    .of_unchanged (by rw [hh, size]; exact Nat.le_add_right _ _)
      (fun o ho => by funext x; simp only [hh, ivarOf, (fields ho).1])
      (fun _ ht _ hv => hd.denM ht hv)⟩

#print axioms dataPres
#print axioms framed
end Ratchet.Denote.Subclass
