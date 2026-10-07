import Books.Metatheory.Heap.HeapFacts

/-! Recursive display names have two obligations beyond preservation of class
payloads: all followed references exist, and both fuel-bounded walks have
stabilized. These hypotheses exclude the counterexample in DriftControls. -/
namespace RubyCore.Proof

structure NamesOk (h : Heap) : Prop where
  classOf : ∀ k cp, h.classPayload? k = some cp → classOf h (.ref k) < h.objs.size
  attached : ∀ k cp o, h.classPayload? k = some cp → cp.attached = some o →
    o < h.objs.size ∧ (h.get o).klass < h.objs.size
  paths : ∀ k, classPath.go h (h.objs.size + 1) k = classPath.go h h.objs.size k
  names : ∀ k, className.go h (h.objs.size + 1) k = className.go h h.objs.size k

theorem NamesOk.nonempty {h : Heap} (hn : NamesOk h) : 0 < h.objs.size := by
  by_cases hz : 0 < h.objs.size
  · exact hz
  exfalso
  have hs : h.objs.size = 0 := Nat.eq_zero_of_not_pos hz
  have hp := classPayload?_oob h 0 (by omega)
  have hh := hn.paths 0
  simp only [hs, classPath.go, hp] at hh
  exact (by decide : ("Object" : String) ≠ "#<Class:0x0000000000000000>") hh

/-- Finite certificate for the reads and fuel equalities in `NamesOk`. -/
def namesOkB (h : Heap) : Bool :=
  0 < h.objs.size && (List.range h.objs.size).all fun k =>
    (h.classPayload? k).all (fun cp =>
      classOf h (.ref k) < h.objs.size && cp.attached.all (fun o =>
        o < h.objs.size && (h.get o).klass < h.objs.size)) &&
    classPath.go h (h.objs.size + 1) k == classPath.go h h.objs.size k &&
    className.go h (h.objs.size + 1) k == className.go h h.objs.size k

theorem namesOkB_sound {h : Heap} (hb : namesOkB h = true) : NamesOk h := by
  simp only [namesOkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, beq_iff_eq] at hb
  have fields (k : ObjId) (hk : k < h.objs.size) := (hb.2 k hk).1.1
  have old (k : ObjId) (cp : ClassPayload) (hcp : h.classPayload? k = some cp) :
      k < h.objs.size := by
    by_cases hk : k < h.objs.size
    · exact hk
    · rw [classPayload?_oob h k hk] at hcp; contradiction
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k cp hcp
    have hh := fields k (old k cp hcp)
    simp only [hcp, Option.all_some, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1
  · intro k cp o hcp ha
    have hh := fields k (old k cp hcp)
    simp only [hcp, Option.all_some, Bool.and_eq_true, decide_eq_true_eq] at hh
    simpa [ha] using hh.2
  · intro k
    by_cases hk : k < h.objs.size
    · exact (hb.2 k hk).1.2
    · obtain ⟨n, hs⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hb.1)
      simp [hs, classPath.go, classPayload?_oob h k hk]
  · intro k
    by_cases hk : k < h.objs.size
    · exact (hb.2 k hk).2
    · obtain ⟨n, hs⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hb.1)
      simp [hs, className.go, classPayload?_oob h k hk]

theorem NamesOk.congr {h h' : Heap} (hn : NamesOk h)
    (hs : h'.objs.size = h.objs.size)
    (hp : ∀ k, (h'.classPayload? k).map nameFields = (h.classPayload? k).map nameFields)
    (hk : ∀ k, (h'.get k).klass = (h.get k).klass)
    (he : ∀ k, (h'.get k).eigen = (h.get k).eigen) : NamesOk h' := by
  have hco (k) : RubyCore.classOf h' (.ref k) = RubyCore.classOf h (.ref k) := by
    simp only [RubyCore.classOf, hk, he]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k cp hcp
    have fields := hp k
    rw [hcp] at fields
    cases hcp0 : h.classPayload? k with
    | none => simp [hcp0] at fields
    | some cp0 => simpa only [hco, hs] using hn.classOf k cp0 hcp0
  · intro k cp o hcp ha
    have fields := hp k
    rw [hcp] at fields
    cases hcp0 : h.classPayload? k with
    | none => simp [hcp0] at fields
    | some cp0 =>
      simp only [hcp0, Option.map_some, Option.some.injEq, nameFields, Prod.mk.injEq] at fields
      simpa only [hk, hs] using hn.attached k cp0 o hcp0 (fields.2.2 ▸ ha)
  · intro k
    simpa only [hs, classPath_go_congr hp hk he] using hn.paths k
  · intro k
    simpa only [hs, className_go_congr hp hk he hs] using hn.names k

theorem IvarOnly.namesOk {h h' : Heap} (hi : IvarOnly h h') (hn : NamesOk h) : NamesOk h' :=
  hn.congr hi.size (fun k => by rw [hi.classPayload k]) hi.klass hi.eigen

theorem namesOk_defineMethod {h : Heap} (hn : NamesOk h) (cls : ObjId)
    (name : String) (md : MethodDef) : NamesOk (defineMethod h cls name md) :=
  hn.congr (objs_size_defineMethod h cls name md)
    (fun k => nameFields_defineMethod h cls k name md)
    (fun k => (get_defineMethod_fields h cls name md k).2.1)
    (fun k => (get_defineMethod_fields h cls name md k).2.2.1)

theorem namesOk_constSetIn {h : Heap} (hn : NamesOk h) (cls : ObjId)
    (name : String) (v : Value) : NamesOk (constSetIn h cls name v) :=
  hn.congr (objs_size_constSetIn h cls name v)
    (fun k => nameFields_constSetIn h cls k name v)
    (fun k => (get_constSetIn_fields h cls name v k).2.1)
    (fun k => (get_constSetIn_fields h cls name v k).2.2.1)

theorem classPath_go_ge {h : Heap} (hs : NamesOk h) {fuel : Nat}
    (hf : h.objs.size + 1 ≤ fuel) (k : ObjId) :
    classPath.go h fuel k = classPath.go h (h.objs.size + 1) k := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hf
  clear hf
  induction d generalizing k with
  | zero => rfl
  | succ d ih =>
    have step : ∀ j, classPath.go h (h.objs.size + 1 + d) j = classPath.go h h.objs.size j :=
      fun j => (ih j).trans (hs.paths j)
    show classPath.go h (h.objs.size + 1 + d + 1) k = _
    simp only [classPath.go, step]

theorem className_go_ge {h : Heap} (hs : NamesOk h) {fuel : Nat}
    (hf : h.objs.size + 1 ≤ fuel) (k : ObjId) :
    className.go h fuel k = className.go h (h.objs.size + 1) k := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hf
  clear hf
  induction d generalizing k with
  | zero => rfl
  | succ d ih =>
    have step : ∀ j, className.go h (h.objs.size + 1 + d) j = className.go h h.objs.size j :=
      fun j => (ih j).trans (hs.names j)
    show className.go h (h.objs.size + 1 + d + 1) k = _
    simp only [className.go, step]

section Growth
variable {h h' : Heap}
    (hsize : h.objs.size ≤ h'.objs.size)
    (hget : ∀ o, o < h.objs.size → h'.get o = h.get o)
    (hn : NamesOk h)

include hget in
theorem name_payload_old {k : ObjId} (hk : k < h.objs.size) :
    h'.classPayload? k = h.classPayload? k := by
  simp only [Heap.classPayload?, hget k hk]

include hget hn in
theorem classPath_go_old (fuel : Nat) (k : ObjId) (hk : k < h.objs.size) :
    classPath.go h' fuel k = classPath.go h fuel k := by
  induction fuel generalizing k with
  | zero => rfl
  | succ fuel ih =>
    simp only [classPath.go, name_payload_old hget hk, hget k hk, classOf]
    cases hp : h.classPayload? k with
    | none => rfl
    | some cp =>
      have hb := hn.classOf k cp hp
      simp only [classOf] at hb
      simp only [ih _ hb]

include hsize hget hn in
theorem classPath_old {k : ObjId} (hk : k < h.objs.size) : classPath h' k = classPath h k := by
  unfold classPath
  rw [classPath_go_old hget hn _ k hk, classPath_go_ge hn (by omega)]

include hsize hget hn in
theorem className_go_old (fuel : Nat) (k : ObjId) (hk : k < h.objs.size) :
    className.go h' fuel k = className.go h fuel k := by
  induction fuel generalizing k with
  | zero => rfl
  | succ fuel ih =>
    simp only [className.go, name_payload_old hget hk]
    cases hp : h.classPayload? k with
    | none => rfl
    | some cp =>
      simp only
      cases ha : cp.attached with
      | none => exact classPath_old hsize hget hn hk
      | some o =>
        obtain ⟨ho, hklass⟩ := hn.attached k cp o hp ha
        simp only [name_payload_old hget ho, hget o ho, ih o ho, ih _ hklass]

include hsize hget hn in
theorem className_old {k : ObjId} (hk : k < h.objs.size) : className h' k = className h k := by
  unfold className
  rw [className_go_old hsize hget hn _ k hk, className_go_ge hn (by omega)]

include hsize hget hn in
theorem className_plainGrow (hp : ∀ k, h'.classPayload? k = h.classPayload? k) (k : ObjId) :
    className h' k = className h k := by
  by_cases hk : k < h.objs.size
  · exact className_old hsize hget hn hk
  · simp [className, className.go, hp, classPayload?_oob h k hk]

include hsize hget hn in
theorem namesOk_plainGrow (hp : ∀ k, h'.classPayload? k = h.classPayload? k) : NamesOk h' := by
  have hpos : 0 < h'.objs.size := Nat.lt_of_lt_of_le hn.nonempty hsize
  have lift_bound {k : ObjId} (hk : k < h.objs.size) : k < h'.objs.size :=
    Nat.lt_of_lt_of_le hk hsize
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k cp hcp
    rw [hp] at hcp
    have hk : k < h.objs.size := by
      by_cases hk : k < h.objs.size
      · exact hk
      · rw [classPayload?_oob h k hk] at hcp
        contradiction
    simpa only [classOf, hget k hk] using lift_bound (hn.classOf k cp hcp)
  · intro k cp o hcp ha
    rw [hp] at hcp
    obtain ⟨ho, hklass⟩ := hn.attached k cp o hcp ha
    exact ⟨lift_bound ho, by rw [hget o ho]; exact lift_bound hklass⟩
  · intro k
    by_cases hk : k < h.objs.size
    · rw [classPath_go_old hget hn _ k hk, classPath_go_old hget hn _ k hk]
      by_cases hz : h'.objs.size = h.objs.size
      · rw [hz]; exact hn.paths k
      · rw [classPath_go_ge hn (fuel := h'.objs.size + 1) (by omega),
          classPath_go_ge hn (fuel := h'.objs.size) (by omega)]
    · obtain ⟨n, hs⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hpos)
      simp only [hs, classPath.go, hp, classPayload?_oob h k hk]
  · intro k
    by_cases hk : k < h.objs.size
    · rw [className_go_old hsize hget hn _ k hk, className_go_old hsize hget hn _ k hk]
      by_cases hz : h'.objs.size = h.objs.size
      · rw [hz]; exact hn.names k
      · rw [className_go_ge hn (fuel := h'.objs.size + 1) (by omega),
          className_go_ge hn (fuel := h'.objs.size) (by omega)]
    · obtain ⟨n, hs⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hpos)
      simp only [hs, className.go, hp, classPayload?_oob h k hk]

include hsize hget hn in
/-- New named, unattached class objects have immediate display names. Old name
walks remain bounded by the original live graph. -/
theorem namesOk_namedGrow
    (hf : ∀ k, h.objs.size ≤ k → ∀ cp, h'.classPayload? k = some cp →
      cp.attached = none ∧ cp.name.isEmpty = false ∧
        RubyCore.classOf h' (.ref k) < h'.objs.size) : NamesOk h' := by
  have hpos := Nat.lt_of_lt_of_le hn.nonempty hsize
  have lift_bound {k : ObjId} (hk : k < h.objs.size) : k < h'.objs.size :=
    Nat.lt_of_lt_of_le hk hsize
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k cp hcp
    by_cases hk : k < h.objs.size
    · rw [name_payload_old hget hk] at hcp
      simpa only [RubyCore.classOf, hget k hk] using lift_bound (hn.classOf k cp hcp)
    · exact (hf k (Nat.le_of_not_lt hk) cp hcp).2.2
  · intro k cp o hcp ha
    by_cases hk : k < h.objs.size
    · rw [name_payload_old hget hk] at hcp
      obtain ⟨ho, hklass⟩ := hn.attached k cp o hcp ha
      exact ⟨lift_bound ho, by rw [hget o ho]; exact lift_bound hklass⟩
    · rw [(hf k (Nat.le_of_not_lt hk) cp hcp).1] at ha; contradiction
  · intro k
    by_cases hk : k < h.objs.size
    · rw [classPath_go_old hget hn _ k hk, classPath_go_old hget hn _ k hk]
      by_cases hz : h'.objs.size = h.objs.size
      · rw [hz]; exact hn.paths k
      · rw [classPath_go_ge hn (fuel := h'.objs.size + 1) (by omega),
          classPath_go_ge hn (fuel := h'.objs.size) (by omega)]
    · obtain ⟨n, hs⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hpos)
      cases hp : h'.classPayload? k with
      | none => simp [hs, classPath.go, hp]
      | some cp => simp [hs, classPath.go, hp, (hf k (Nat.le_of_not_lt hk) cp hp).2.1]
  · intro k
    by_cases hk : k < h.objs.size
    · rw [className_go_old hsize hget hn _ k hk, className_go_old hsize hget hn _ k hk]
      by_cases hz : h'.objs.size = h.objs.size
      · rw [hz]; exact hn.names k
      · rw [className_go_ge hn (fuel := h'.objs.size + 1) (by omega),
          className_go_ge hn (fuel := h'.objs.size) (by omega)]
    · obtain ⟨n, hs⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hpos)
      cases hp : h'.classPayload? k with
      | none => simp [hs, className.go, hp]
      | some cp => simp [hs, className.go, hp, (hf k (Nat.le_of_not_lt hk) cp hp).1]

#print axioms namesOk_namedGrow

end Growth
end RubyCore.Proof
