import Denote.Sem.IvarMutation
import Denote.Sem.DataPres

/-! Constructor publication preserves the heap that existed *before allocation*.
Unlike `Ext`, this relation permits initialized ivars on fresh objects and says nothing
about frames. Old objects and dispatch stay fixed. Dangling references are not assumed
absent: `freshBasic` preserves their nominal types, and exact instance types require liveness.
-/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

structure InitGrow (h h' : Heap) : Prop where
  size : h.objs.size ≤ h'.objs.size
  get : ∀ o, o < h.objs.size → h'.get o = h.get o
  payload : ∀ k, h'.classPayload? k = h.classPayload? k
  ancestors : ∀ k, RubyCore.ancestors h' k = RubyCore.ancestors h k
  freshBasic : ∀ o, h.objs.size ≤ o → ∀ k,
    (RubyCore.ancestors h Boot.basicObjectId).contains k = true →
    (RubyCore.ancestors h' (classOf h' (.ref o))).contains k = true

theorem Ext.initGrow {m n : Machine} (he : Ext m n) : InitGrow m.heap n.heap :=
  ⟨he.size, he.get, he.payload, he.ancestors, he.freshBasic⟩

theorem InitGrow.refl (h : Heap) : InitGrow h h where
  size := Nat.le_refl _
  get := fun _ _ => rfl
  payload := fun _ => rfl
  ancestors := fun _ => rfl
  freshBasic := fun o ho k hk => by rw [classOf_oob h ho]; exact hk

theorem InitGrow.trans {h h' h'' : Heap} (ha : InitGrow h h') (hb : InitGrow h' h'') :
    InitGrow h h'' where
  size := Nat.le_trans ha.size hb.size
  get := fun o ho => by rw [hb.get o (Nat.lt_of_lt_of_le ho ha.size), ha.get o ho]
  payload := fun k => by rw [hb.payload k, ha.payload k]
  ancestors := fun k => by rw [hb.ancestors k, ha.ancestors k]
  freshBasic := fun o ho k hk => by
    by_cases hc : o < h'.objs.size
    · simpa only [classOf, hb.get o hc, hb.ancestors] using ha.freshBasic o ho k hk
    · exact hb.freshBasic o (Nat.le_of_not_lt hc) k (by rw [ha.ancestors]; exact hk)

theorem InitGrow.classNamed?_eq {h h' : Heap} (hg : InitGrow h h') (cn : String) :
    classNamed? h' cn = classNamed? h cn := by
  have hc : constLookup h' cn = constLookup h cn := by simp only [constLookup, hg.payload]
  simp only [classNamed?, hc]
  cases constLookup h cn with
  | none => rfl
  | some v => cases v <;> simp [hg.payload]

theorem InitGrow.isA_mono {h h' : Heap} (hg : InitGrow h h') {v : Value} {k : ObjId}
    (hv : isA h v k = true) : isA h' v k = true := by
  cases v with
  | ref o =>
    rcases Nat.lt_or_ge o h.objs.size with ho | ho
    · simpa only [isA, classOf, hg.get o ho, hg.ancestors] using hv
    · exact hg.freshBasic o ho k (by rwa [isA, classOf_oob h ho] at hv)
  | int _ | flt _ | sym _ | nil => simpa only [isA, classOf, hg.ancestors] using hv
  | bool b => cases b <;> simpa only [isA, classOf, hg.ancestors] using hv

theorem InitGrow.isAName_mono {h h' : Heap} (hg : InitGrow h h') {v : Value} {cn : String}
    (hv : isAName h v cn = true) : isAName h' v cn = true := by
  unfold isAName at hv ⊢
  rw [hg.classNamed?_eq]
  cases hc : classNamed? h cn with
  | none => rw [hc] at hv; cases hv
  | some k => rw [hc] at hv; exact hg.isA_mono hv

/-- Only a previously live instance requires ivar agreement. Fresh ivars are unrestricted. -/
theorem InitGrow.exactInst_data {h h' : Heap} (hg : InitGrow h h') {v : Value} {cn : String}
    (hv : isExactInst h v cn = true) :
    isExactInst h' v cn = true ∧ ivarOf h' v = ivarOf h v := by
  unfold isExactInst at hv ⊢
  rw [hg.classNamed?_eq]
  cases hc : classNamed? h cn with
  | none => rw [hc] at hv; cases v <;> simp_all
  | some k =>
    rw [hc] at hv
    cases v with
    | ref o =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv ⊢
      obtain ⟨⟨ho, he⟩, hk⟩ := hv
      refine ⟨⟨⟨Nat.lt_of_lt_of_le ho hg.size, ?_⟩, ?_⟩, ?_⟩
      · rw [hg.get o ho]; exact he
      · rw [hg.get o ho]; exact hk
      · funext x; simp only [ivarOf, hg.get o ho]
    | _ => simp_all

theorem InitGrow.arrElems?_eq {h h' : Heap} (hg : InitGrow h h') {v : Value} {xs : Array Value}
    (hv : arrElems? h v = some xs) : arrElems? h' v = some xs := by
  cases v with
  | ref o => rw [arrElems?, hg.get o (lt_of_arrElems? hv)]; exact hv
  | _ => exact absurd hv (by simp [arrElems?])

theorem InitGrow.hshEntries?_eq {h h' : Heap} (hg : InitGrow h h') {v : Value}
    {es : Array (Value × Value)} (hv : hshEntries? h v = some es) :
    hshEntries? h' v = some es := by
  cases v with
  | ref o => rw [hshEntries?, hg.get o (lt_of_hshEntries? hv)]; exact hv
  | _ => exact absurd hv (by simp [hshEntries?])

/-- The anchor is unchanged across writes, including several writes to the same new object. -/
theorem InitGrow.bindIvar {h : Heap} {m : Machine} (hg : InitGrow h m.heap)
    {o : ObjId} (hs : m.currentFrame.self = .ref o) (ho : h.objs.size ≤ o)
    (x : String) (v : Value) : InitGrow h (Interp.bindIvar m x v).heap := by
  have hi := bindIvar_ivarOnly m x v
  refine ⟨by rw [hi.size]; exact hg.size, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have hko : k ≠ o := Nat.ne_of_lt (Nat.lt_of_lt_of_le hk ho)
    rw [bindIvar_get_other hs hko, hg.get k hk]
  · intro k; rw [hi.classPayload k, hg.payload k]
  · intro k; rw [hi.ancestors_eq k, hg.ancestors k]
  · intro k hk c hc
    rw [hi.classOf_eq, hi.ancestors_eq]
    exact hg.freshBasic k hk c hc

/-- No frame assumptions: first-order types inspect only old, successfully resolved data. -/
theorem InitGrow.dataPres {h h' : Heap} (hg : InitGrow h h') : DataPres h h' :=
  ⟨fun _ _ hv => hg.isAName_mono hv,
    fun cn _ hk => by rw [hg.classNamed?_eq cn]; exact hk,
    fun _ _ hv => hg.exactInst_data hv,
    fun _ _ hv => hg.arrElems?_eq hv, fun _ _ hv => hg.hshEntries?_eq hv⟩

theorem InitGrow.denM_aux {m n : Machine} (hg : InitGrow m.heap n.heap) :
    ∀ τ : Ty, FirstOrder τ = true →
    (∀ v, denM τ m v → denM τ n v) ∧
    (∀ seen g, denSpineFrom seen τ m g → denSpineFrom seen τ n g) :=
  hg.dataPres.denM_aux

theorem InitGrow.denM {m n : Machine} (hg : InitGrow m.heap n.heap) {τ : Ty}
    (hf : FirstOrder τ = true) {v : Value} (hv : denM τ m v) : denM τ n v :=
  (hg.denM_aux τ hf).1 v hv

/-- Publish only after restoring caller frame balance and isolation. This recovers the
unchanged full frame contract; it does not grant that contract inside the initializer. -/
theorem Framed.of_initGrow {m n : Machine} (hg : InitGrow m.heap n.heap)
    (hs : n.stack = m.stack) (hf : FramePres m n) : Framed m n :=
  ⟨hs, fun k hk => by rw [hg.payload k]; exact hk, fun _ _ hv => hg.isAName_mono hv,
    fun _ ht _ hv => hg.denM ht hv, hf,
    .of_unchanged hg.size (fun o ho => by funext x; simp only [ivarOf, hg.get o ho])
      (fun _ ht _ hv => hg.denM ht hv)⟩

#print axioms InitGrow.bindIvar
#print axioms InitGrow.denM
#print axioms Framed.of_initGrow
end Ratchet.Denote
