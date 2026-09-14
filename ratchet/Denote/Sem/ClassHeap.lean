import Denote.Sem.Framed
import Denote.Sem.DataPres
import RubyCore.Proof.Judgment.ClsFresh

/-! Old data across a fresh top-level class declaration. The constant table changes and
two class payloads appear, so neither `Ext` nor `InitGrow` describes this heap change.
Old names are preserved only when they already denote classes; absence is not preserved. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap)

variable {h : Heap} {name : String} {e : ObjId}
local notation "h₁" => freshClsHeap h Boot.objectId name name e

theorem fields {o : ObjId} (ho : o < h.objs.size) :
    ((h₁).get o).ivars = (h.get o).ivars ∧ ((h₁).get o).klass = (h.get o).klass ∧
      ((h₁).get o).eigen = (h.get o).eigen ∧ ((h₁).get o).frozen = (h.get o).frozen := by
  rw [Proof.Judgment.freshClsHeap_get_old ho]
  exact Proof.get_constSetIn_fields h Boot.objectId name (.ref h.objs.size) o

theorem classPayload_live {k : ObjId} (hk : (h.classPayload? k).isSome = true) :
    ((h₁).classPayload? k).isSome = true := by
  have hl := lt_size_of_classPayload hk
  unfold Heap.classPayload?
  rw [Proof.Judgment.freshClsHeap_get_old hl]
  exact (Proof.classPayload?_isSome_constSetIn h Boot.objectId k name _).trans hk

theorem classPayload_old_isSome {k : ObjId} (hk : k < h.objs.size) :
    ((h₁).classPayload? k).isSome = (h.classPayload? k).isSome := by
  unfold Heap.classPayload?
  rw [Proof.Judgment.freshClsHeap_get_old hk]
  exact Proof.classPayload?_isSome_constSetIn h Boot.objectId k name _

theorem get_old_nonclass {o : ObjId} (ho : o < h.objs.size)
    (hp : h.classPayload? o = none) : (h₁).get o = h.get o := by
  rw [Proof.Judgment.freshClsHeap_get_old ho]
  by_cases he : o = Boot.objectId
  · subst o
    simp only [Proof.Judgment.hmidOf, constSetIn, hp]
  · exact Proof.Static.get_constSetIn_ne h Boot.objectId o name _ he

theorem payload_nonclass {o : ObjId} (ho : o < h.objs.size)
    (hp : h.classPayload? o = none) : ((h₁).get o).payload = (h.get o).payload := by
  rw [get_old_nonclass ho hp]

/-- No non-class object is created or changed, including beyond the heap's end. -/
theorem get_nonclass {o : ObjId} (hp : (h₁).classPayload? o = none) :
    (h₁).get o = h.get o := by
  by_cases hl : o < h.objs.size
  · have hp₀ : h.classPayload? o = none := by
      have hh := classPayload_old_isSome (name := name) (e := e) hl
      rw [hp] at hh
      cases hx : h.classPayload? o <;> simp_all
    exact get_old_nonclass hl hp₀
  · by_cases hk : o = h.objs.size
    · subst o; rw [Proof.Judgment.freshClsHeap_cp_k] at hp; contradiction
    · by_cases he' : o = h.objs.size + 1
      · subst o; rw [Proof.Judgment.freshClsHeap_cp_e] at hp; contradiction
      · have hout := Nat.le_of_not_lt (Proof.Judgment.not_lt_add_two hl hk he')
        rw [get_oob h (Nat.le_of_not_lt hl),
          get_oob _ (by rw [Proof.Judgment.freshClsHeap_size]; exact hout)]

theorem array {v : Value} {xs : Array Value} (hv : arrElems? h v = some xs) :
    arrElems? h₁ v = some xs := by
  cases v with
  | ref o =>
    have hl := lt_of_arrElems? hv
    have hp : h.classPayload? o = none := by
      unfold Heap.classPayload?
      cases he : (h.get o).payload <;> simp_all [arrElems?]
    rw [arrElems?, payload_nonclass hl hp]
    exact hv
  | _ => exact absurd hv (by simp [arrElems?])

theorem hash {v : Value} {es : Array (Value × Value)} (hv : hshEntries? h v = some es) :
    hshEntries? h₁ v = some es := by
  cases v with
  | ref o =>
    have hl := lt_of_hshEntries? hv
    have hp : h.classPayload? o = none := by
      unfold Heap.classPayload?
      cases he : (h.get o).payload <;> simp_all [hshEntries?]
    rw [hshEntries?, payload_nonclass hl hp]
    exact hv
  | _ => exact absurd hv (by simp [hshEntries?])

theorem constLookup_eq_own (heap : Heap) (cn : String) :
    constLookup heap cn = constOwn heap Boot.objectId cn := by
  cases he : heap.classPayload? Boot.objectId <;> simp [constLookup, constOwn, he]

theorem const_other (ho : Boot.objectId < h.objs.size) {cn : String} (hn : cn ≠ name) :
    constLookup h₁ cn = constLookup h cn := by
  rw [constLookup_eq_own, constLookup_eq_own,
    Proof.Judgment.constOwn_old_freshC ho ho]
  exact Proof.constOwn_constSetIn_ne h Boot.objectId Boot.objectId name cn _ (Or.inr hn)

theorem named (ho : Boot.objectId < h.objs.size)
    (hn : constOwn h Boot.objectId name = none) {cn : String} {k : ObjId}
    (hk : classNamed? h cn = some k) : classNamed? h₁ cn = some k := by
  have hcn : cn ≠ name := by
    intro he; subst cn
    simp only [classNamed?, constLookup_eq_own, hn] at hk
    cases hk
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
      simp only [classPayload_live hp, ite_true]
      exact hk
    · cases hk

theorem classOf_old {o : ObjId} (ho : o < h.objs.size) :
    classOf h₁ (.ref o) = classOf h (.ref o) := by
  simp only [classOf, (fields (name := name) (e := e) ho).2.1,
    (fields (name := name) (e := e) ho).2.2.1]

theorem fresh_basic (hc : ClassReady h) (hs : Proof.Saturated h)
    (hb : ancestors h Boot.basicObjectId = [Boot.basicObjectId])
    (he : (h.get Boot.objectId).eigen = some e) {o : ObjId} (ho : h.objs.size ≤ o) :
    isA h₁ (.ref o) Boot.basicObjectId = true := by
  have hel := hc.chains.eigen _ hc.chains.boot.2.2.2.2 _ he
  by_cases hk : o = h.objs.size
  · subst o
    rw [isA, Proof.Judgment.classOf_freshC_k,
      Proof.Judgment.ancestors_freshC_e hc.chains hs hel]
    obtain ⟨e', he', hbasic⟩ := hc.objectEigen
    rw [he] at he'; cases he'
    simp only [List.contains_cons, hbasic, Bool.or_true]
  · by_cases hek : o = h.objs.size + 1
    · subst o
      rw [isA, Proof.Judgment.classOf_freshC_e,
        Proof.Judgment.ancestors_old_freshC hc.chains hs hc.chains.boot.1]
      exact hc.classBasic
    · have hl : Boot.basicObjectId < h.objs.size :=
        Nat.lt_of_le_of_lt (by decide : Boot.basicObjectId ≤ Boot.objectId) hc.chains.boot.2.2.2.2
      have hout : h.objs.size + 2 ≤ o := Nat.le_of_not_lt
        (Proof.Judgment.not_lt_add_two (Nat.not_lt_of_ge ho) hk hek)
      rw [isA, classOf_oob _ (by rw [Proof.Judgment.freshClsHeap_size]; exact hout),
        Proof.Judgment.ancestors_old_freshC hc.chains hs hl, hb]
      rfl

theorem isA_of_bound (hc : Proof.ChainsIn h) (hs : Proof.Saturated h) {v : Value} {k : ObjId}
    (hl : classOf h v < h.objs.size) (he : classOf h₁ v = classOf h v)
    (hv : isA h v k = true) : isA h₁ v k = true := by
  rw [isA, he, Proof.Judgment.ancestors_old_freshC hc hs hl]
  exact hv

theorem isA_mono (hc : ClassReady h) (hs : Proof.Saturated h)
    (hb : ancestors h Boot.basicObjectId = [Boot.basicObjectId])
    (he : (h.get Boot.objectId).eigen = some e) {v : Value} {k : ObjId}
    (hv : isA h v k = true) : isA h₁ v k = true := by
  cases v with
  | ref o =>
    by_cases ho : o < h.objs.size
    · exact isA_of_bound hc.chains hs (Proof.ClsGrow.classOf_lt hc.chains ho) (classOf_old ho) hv
    · have hl := Nat.le_of_not_lt ho
      have hk : k = Boot.basicObjectId := by
        simpa only [isA, classOf_oob h hl, hb, List.contains_cons, List.contains_nil,
          Bool.or_false, beq_iff_eq] using hv
      subst k
      exact fresh_basic hc hs hb he hl
  | bool b =>
    cases b <;> exact isA_of_bound hc.chains hs
      (Nat.lt_of_le_of_lt (by simp only [classOf]; decide) hc.chains.boot.2.2.2.1) rfl hv
  | _ =>
    exact isA_of_bound hc.chains hs
      (Nat.lt_of_le_of_lt (by simp only [classOf]; decide) hc.chains.boot.2.2.2.1) rfl hv

theorem nominal (hc : ClassReady h) (hs : Proof.Saturated h)
    (hb : ancestors h Boot.basicObjectId = [Boot.basicObjectId])
    (hn : constOwn h Boot.objectId name = none)
    (he : (h.get Boot.objectId).eigen = some e) {v : Value} {cn : String}
    (hv : isAName h v cn = true) : isAName h₁ v cn = true := by
  unfold isAName at hv ⊢
  cases hk : classNamed? h cn with
  | none => rw [hk] at hv; cases hv
  | some k =>
    rw [named hc.chains.boot.2.2.2.2 hn hk]
    rw [hk] at hv
    exact isA_mono hc hs hb he hv

theorem exactInst (ho : Boot.objectId < h.objs.size)
    (hn : constOwn h Boot.objectId name = none) {v : Value} {cn : String}
    (hv : isExactInst h v cn = true) :
    isExactInst h₁ v cn = true ∧ ivarOf h₁ v = ivarOf h v := by
  unfold isExactInst at hv ⊢
  cases hk : classNamed? h cn with
  | none => rw [hk] at hv; cases v <;> simp_all
  | some k =>
    rw [hk] at hv
    rw [named ho hn hk]
    cases v with
    | ref o =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv ⊢
      obtain ⟨⟨hl, he⟩, hkl⟩ := hv
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · rw [Proof.Judgment.freshClsHeap_size]
        exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hl)
      · rw [(fields hl).2.2.1]; exact he
      · rw [(fields hl).2.1]; exact hkl
      · funext x; simp only [ivarOf, (fields (name := name) (e := e) hl).1]
    | _ => simp_all

theorem dataPres (hc : ClassReady h) (hs : Proof.Saturated h)
    (hb : ancestors h Boot.basicObjectId = [Boot.basicObjectId])
    (hn : constOwn h Boot.objectId name = none)
    (he : (h.get Boot.objectId).eigen = some e) : DataPres h h₁ :=
  ⟨fun _ _ hv => nominal hc hs hb hn he hv,
    fun _ _ hk => named hc.chains.boot.2.2.2.2 hn hk,
    fun _ _ hv => exactInst hc.chains.boot.2.2.2.2 hn hv,
    fun _ _ hv => array hv, fun _ _ hv => hash hv⟩

#print axioms named
#print axioms dataPres
end Ratchet.Denote.FreshClass

namespace Ratchet.Denote
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap)

/-- The same readiness invariant survives both allocations and constant registration. -/
theorem ClassReady.freshClass {h : Heap} {d : ObjId} {name q : String} {e : ObjId}
    (hc : ClassReady h) (hsat : Proof.Saturated h) (hd : d < h.objs.size)
    (he : (h.get Boot.objectId).eigen = some e) :
    ClassReady (freshClsHeap h d name q e) := by
  have ho := hc.chains.boot.2.2.2.2
  have hel := hc.chains.eigen _ ho _ he
  refine ⟨Proof.Judgment.chainsIn_freshC hc.chains hd hel, ⟨e, ?_, ?_⟩, ?_⟩
  · rw [Proof.Judgment.freshClsHeap_get_old ho,
      (Proof.get_constSetIn_fields h d name (.ref h.objs.size) Boot.objectId).2.2.1]
    exact he
  · rw [Proof.Judgment.ancestors_old_freshC hc.chains hsat hel]
    obtain ⟨e', he', hb⟩ := hc.objectEigen
    rw [he] at he'; cases he'; exact hb
  · rw [Proof.Judgment.ancestors_old_freshC hc.chains hsat hc.chains.boot.1]
    exact hc.classBasic

/-- Restore frame balance separately: this is the heap half of class publication. -/
theorem Framed.of_freshClass {κ : Ctx} {Γ : Env} {I : Ty} {m n : Machine}
    {name : String} {e : ObjId} (hm : StateOk κ Γ I m)
    (hn : constOwn m.heap Boot.objectId name = none)
    (he : (m.heap.get Boot.objectId).eigen = some e)
    (hh : n.heap = Proof.Judgment.freshClsHeap m.heap Boot.objectId name name e)
    (hs : n.stack = m.stack) (hf : FramePres m n) : Framed m n := by
  have hp : DataPres m.heap n.heap := by
    rw [hh]; exact FreshClass.dataPres hm.core.classReady hm.sat hm.core.basicSelf hn he
  exact ⟨hs, fun k hk => by rw [hh]; exact FreshClass.classPayload_live hk,
    hp.nominal, fun _ ht _ hv => hp.denM ht hv, hf⟩

#print axioms Framed.of_freshClass
end Ratchet.Denote
