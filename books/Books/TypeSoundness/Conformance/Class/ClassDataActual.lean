import Books.TypeSoundness.Conformance.Class.ClassReadyActual
import Books.TypeSoundness.Conformance.Class.ClassData
import Books.TypeSoundness.Conformance.Core.Framed

/-! Repair Subclass.dataPres's producers for the actual two-allocation heap.
The existing first-order type induction is reused unchanged. -/
set_option autoImplicit false
namespace Checker.Soundness.FreshClassActual
open RubyCore Checker RubyCore.Proof RubyCore.Proof.Judgment
variable {p : ObjId}

variable {m : Machine} {name : String} {e : ObjId}
local notation "h₁" => heap m name e p

theorem ancestors_class (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) (hp : p < m.heap.objs.size) :
    ancestors h₁ m.heap.objs.size = m.heap.objs.size :: ancestors m.heap p := by
  have he := ancestors_new_head (h := constSetIn m.heap m.lexicalNamespace name (.ref m.heap.objs.size))
    (h' := h₁) (k := m.heap.objs.size) (parent := p) (grow hd)
    (chainsIn_hmid hc) (saturated_hmid hs)
    (by rw [hmid_size, size]; omega) (by rw [hmid_size]; exact Nat.le_refl _)
    (by rw [hmid_size]; exact hp) (by
      intro f
      rw [ancestors.go.eq_def]
      simp [Heap.classPayload?, get_class hd, namedObject, freshClassPayload])
  rw [ancestors_constSetIn] at he
  exact he

theorem ancestors_eigen (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) (hep : e < m.heap.objs.size) :
    ancestors h₁ (m.heap.objs.size + 1) = (m.heap.objs.size + 1) :: ancestors m.heap e := by
  have he := ancestors_new_head (h := constSetIn m.heap m.lexicalNamespace name (.ref m.heap.objs.size))
    (h' := h₁) (k := m.heap.objs.size + 1) (parent := e) (grow hd)
    (chainsIn_hmid hc) (saturated_hmid hs)
    (by rw [hmid_size, size]; omega) (by rw [hmid_size]; omega)
    (by rw [hmid_size]; exact hep) (by
      intro f
      rw [ancestors.go.eq_def]
      simp [Heap.classPayload?, get_eigen, attachedClassEigen])
  rw [ancestors_constSetIn] at he
  exact he

theorem get_old_nonclass {o : ObjId} (hd : m.lexicalNamespace < m.heap.objs.size)
    (ho : o < m.heap.objs.size) (hp : m.heap.classPayload? o = none) :
    (h₁).get o = m.heap.get o := by
  rw [get_old hd ho]
  by_cases he : o = m.lexicalNamespace
  · subst o; simp only [constSetIn, hp]
  · exact Static.get_constSetIn_ne m.heap m.lexicalNamespace o name _ he

theorem get_nonclass {o : ObjId} (hd : m.lexicalNamespace < m.heap.objs.size)
    (hp : (h₁).classPayload? o = none) : (h₁).get o = m.heap.get o := by
  by_cases hl : o < m.heap.objs.size
  · have hp₀ : m.heap.classPayload? o = none := by
      have hh := classPayload_live (name := name) (e := e) (p := p) hd hl
      rw [hp] at hh
      cases he : m.heap.classPayload? o <;> simp_all
    exact get_old_nonclass hd hl hp₀
  · by_cases hk : o = m.heap.objs.size
    · subst o; simp only [Heap.classPayload?, get_class hd, namedObject] at hp; cases hp
    · by_cases he : o = m.heap.objs.size + 1
      · subst o; simp only [Heap.classPayload?, get_eigen, attachedClassEigen] at hp; cases hp
      · have hout := Nat.le_of_not_lt (not_lt_add_two hl hk he)
        rw [get_oob m.heap (Nat.le_of_not_lt hl), get_oob _ (by rw [size m name e]; exact hout)]

theorem fresh_basic (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size)
    (hb : ancestors m.heap Boot.basicObjectId = [Boot.basicObjectId])
    (hep : e < m.heap.objs.size) (hr : (ancestors m.heap e).contains Boot.basicObjectId = true)
    {o : ObjId} (ho : m.heap.objs.size ≤ o) : isA h₁ (.ref o) Boot.basicObjectId = true := by
  by_cases hk : o = m.heap.objs.size
  · subst o
    simp only [isA, classOf, get_class hd]
    rw [ancestors_eigen hc.chains hs hd hep]
    simp only [List.contains_cons, hr, Bool.or_true]
  · by_cases he : o = m.heap.objs.size + 1
    · subst o
      simp only [isA, classOf, get_eigen, attachedClassEigen]
      rw [ancestors_old hc.chains hs hd hc.chains.boot.1]; exact hc.classBasic
    · have hout := Nat.le_of_not_lt (not_lt_add_two (Nat.not_lt_of_ge ho) hk he)
      have hl := Nat.lt_of_le_of_lt (by decide : Boot.basicObjectId ≤ Boot.objectId) hc.chains.boot.2.2.2.2
      rw [isA, classOf_oob _ (by rw [size m name e]; exact hout), ancestors_old hc.chains hs hd hl, hb]
      rfl

theorem dataPres (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (hb : ancestors m.heap Boot.basicObjectId = [Boot.basicObjectId])
    (htop : m.lexicalNamespace = Boot.objectId) (hf : constOwn m.heap Boot.objectId name = none)
    (hep : e < m.heap.objs.size) (hr : (ancestors m.heap e).contains Boot.basicObjectId = true) :
    DataPres m.heap h₁ := by
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ hc.chains.boot.2.2.2.2
  exact dataPres_of_class_growth hc.chains hb (by rw [size m name e]; exact Nat.le_add_right _ _)
    (fun o ho => ⟨(fields_old hd ho).1, (fields_old hd ho).2.1, (fields_old hd ho).2.2.1⟩)
    (fun _ ho hp => get_old_nonclass hd ho hp) (fun _ hk => ancestors_old hc.chains hs hd hk)
    (fun _ ho => fresh_basic hc hs hd hb hep hr ho)
    (fun _ _ hk => named_old htop hc.chains.boot.2.2.2.2 hf hk)

/-- The original caller-framing argument after balancing the body frame. -/
theorem framed {κ : Ctx} {Γ : Env} {I : Ty} {n : Machine}
    (hm : StateOk κ Γ I m) (htop : m.lexicalNamespace = Boot.objectId)
    (hf : constOwn m.heap Boot.objectId name = none)
    (hep : e < m.heap.objs.size) (hr : (ancestors m.heap e).contains Boot.basicObjectId = true)
    (hh : n.heap = h₁)
    (hs : n.stack = m.stack) (hfr : FramePres m n)
    (hphase : n.preludeMode = m.preludeMode := by rfl)
    (hroot : RootClean m → RootClean n := by exact id) : Framed m n := by
  have hc := hm.core.classReady
  have ho := hc.chains.boot.2.2.2.2
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ ho
  have hp : DataPres m.heap n.heap := by
    rw [hh]
    exact dataPres hc hm.sat hm.core.basicSelf htop hf hep hr
  exact ⟨hs, fun k hk => by rw [hh]; exact (classPayload_live hd (lt_size_of_classPayload hk)).trans hk,
    hp.nominal, fun _ ht _ hv => hp.denM ht hv, hfr,
    .of_unchanged (by rw [hh, size m name e]; exact Nat.le_add_right _ _)
      (fun o ho => by funext x; simp only [hh, ivarOf, (fields_old hd ho).1])
      (fun _ ht _ hv => hp.denM ht hv),
    (fun o ho e' he' => by rw [hh, (fields_old hd ho).2.2.1]; exact he'),
    (by rw [hh]; exact .of_nonclass (fun _ ho hp => get_old_nonclass hd ho hp)), hphase, hroot⟩

#print axioms ancestors_eigen
#print axioms dataPres
#print axioms framed
end Checker.Soundness.FreshClassActual
