import Denote.Sem.SubclassHeap
import Denote.Sem.MetaReadyClass
import Denote.Typed.ClassEntry

/-! Actual subclass entry with a resolved superclass. Cached metaclass readiness is an
explicit premise, not inferred from the instance ancestor chain or a method annotation. -/
set_option autoImplicit false
namespace Ratchet.Denote.Subclass
open RubyCore RubyCore.Interp RubyCore.Proof RubyCore.Proof.Judgment

theorem eigenclass_classObj {m : Machine} {k parent eParent : ObjId} {q : String}
    (hg : m.heap.get k = classObj q parent) (hn : anyToS m.heap k = q)
    (he : (m.heap.get parent).eigen = some eParent) (hp : 0 < m.heap.objs.size) :
    eigenclassOf m k = (m.heap.objs.size,
      { m with heap := attachEigen (m.heap.alloc (eigObjC q eParent)).2 k m.heap.objs.size }) := by
  obtain ⟨n, hn'⟩ : ∃ n, m.heap.objs.size = n + 1 :=
    ⟨m.heap.objs.size - 1, (Nat.succ_pred_eq_of_pos hp).symm⟩
  change eigenclassOf.go m k (m.heap.objs.size + 1) = _
  rw [hn']
  unfold eigenclassOf.go
  rw [hg]
  simp only [classObj]
  rw [show eigenclassOf.go m parent (n + 1) = (eParent, m) from eigenclassOf_go_some he]
  simp only [eigObjC, hn, attachEigen]
  rw [← hn']
  rfl

theorem enter_fresh {m : Machine} {name q : String} {parent eParent : ObjId} {body : RubyCore.Expr}
    (hm : constOwn m.heap m.currentFrame.defmod name = none)
    (hd : m.currentFrame.defmod < m.heap.objs.size) (hp : parent < m.heap.objs.size)
    (he : (m.heap.get parent).eigen = some eParent)
    (hq : (if m.currentFrame.defmod == Boot.objectId then name
      else className m.heap m.currentFrame.defmod ++ "::" ++ name) = q)
    (hn : q.isEmpty = false) :
    enterClassBody m name false (some parent) body =
      .next (machine m m.currentFrame.defmod m.currentFrame.cref name q parent eParent body) := by
  have hqq : (if m.currentFrame.defmod == Boot.objectId then name
      else s!"{className m.heap m.currentFrame.defmod}::{name}") = q := by
    rw [← hq]; split <;> rfl
  have hg : (constSetIn (m.heap.alloc (classObj q parent)).2 m.currentFrame.defmod name
      (.ref m.heap.objs.size)).get m.heap.objs.size = classObj q parent := by
    rw [Static.get_constSetIn_ne _ _ _ _ _ (Nat.ne_of_lt hd).symm]
    exact objs_getD_push_self _ _
  have hc : className (constSetIn (m.heap.alloc (classObj q parent)).2
      m.currentFrame.defmod name (.ref m.heap.objs.size)) m.heap.objs.size = q := by
    unfold className Heap.classPayload?
    rw [hg]
    simp only [classObj, hn, Bool.false_eq_true, ↓reduceIte]
  have hany : anyToS (constSetIn (m.heap.alloc (classObj q parent)).2
      m.currentFrame.defmod name (.ref m.heap.objs.size)) m.heap.objs.size = q := by
    unfold anyToS Heap.classPayload?
    rw [hg]
    exact hc
  have hsz : (constSetIn (m.heap.alloc (classObj q parent)).2 m.currentFrame.defmod name
      (.ref m.heap.objs.size)).objs.size = m.heap.objs.size + 1 := by
    rw [objs_size_constSetIn]; simp [Heap.alloc]
  have he' : ((constSetIn (m.heap.alloc (classObj q parent)).2 m.currentFrame.defmod name
      (.ref m.heap.objs.size)).get parent).eigen = some eParent := by
    rw [(get_constSetIn_fields (m.heap.alloc (classObj q parent)).2 m.currentFrame.defmod
      name (.ref m.heap.objs.size) parent).2.2.1]
    change ((m.heap.objs.push (classObj q parent)).getD parent default).eigen = some eParent
    rw [objs_getD_push_lt _ _ _ hp]; exact he
  have hpos : 0 < (constSetIn (m.heap.alloc (classObj q parent)).2 m.currentFrame.defmod name
      (.ref m.heap.objs.size)).objs.size := by rw [hsz]; omega
  simp only [enterClassBody, hm, hqq, Bool.false_eq_true, ↓reduceIte, Option.getD_some]
  simp only [show ∀ ob : Object, (m.heap.alloc ob).1 = m.heap.objs.size from fun _ => rfl]
  simp only [classObj, eigObjC] at hg hany he' ⊢
  rw [eigenclass_classObj (m := { m with heap := (constSetIn (m.heap.alloc (classObj q parent)).2
    m.currentFrame.defmod name (.ref m.heap.objs.size)) }) hg hany he' hpos]
  change StepResult.next (withKont
    { m with
      heap := attachEigen ((constSetIn (m.heap.alloc (classObj q parent)).2
        m.currentFrame.defmod name (.ref m.heap.objs.size)).alloc (eigObjC q eParent)).2
        m.heap.objs.size (constSetIn (m.heap.alloc (classObj q parent)).2
          m.currentFrame.defmod name (.ref m.heap.objs.size)).objs.size,
      frames := m.frames.push (freshModFrame m.heap.objs.size m.currentFrame.cref),
      stack := m.frames.size :: m.stack } (.eval body) (.frameK m.frames.size)) = _
  rw [heap_machine _ _ _ _ _ _ hd]
  rfl

/-- The real superclass continuation checks that the resolved value is a non-module
class before using the fresh entry path. The enclosing continuation is retained. -/
theorem step_resolved {m : Machine} {name q : String} {parent eParent : ObjId}
    {cp : ClassPayload} {body : RubyCore.Expr} {rest : List Kont}
    (hctl : m.ctl = .value (.ref parent)) (hkont : m.kont = .classDefK name body :: rest)
    (hcp : m.heap.classPayload? parent = some cp) (hmod : cp.isModule = false)
    (hm : constOwn m.heap m.currentFrame.defmod name = none)
    (hd : m.currentFrame.defmod < m.heap.objs.size) (hp : parent < m.heap.objs.size)
    (he : (m.heap.get parent).eigen = some eParent)
    (hq : (if m.currentFrame.defmod == Boot.objectId then name
      else className m.heap m.currentFrame.defmod ++ "::" ++ name) = q)
    (hn : q.isEmpty = false) :
    stepFn m = .next (machine { m with kont := rest } m.currentFrame.defmod m.currentFrame.cref
      name q parent eParent body) := by
  simp only [stepFn, hctl, applyKont, hkont, hcp, hmod, Bool.false_eq_true, ↓reduceIte]
  simpa only [hctl, Machine.currentFrame] using
    enter_fresh (m := { m with kont := rest }) (body := body) hm hd hp he hq hn

/-- Actual entry preserves bounded dispatch edges, constant-reference liveness and
both walk saturations. Full StateOk and the annotation-checked body remain separate. -/
theorem enter_fresh_ready {m : Machine} {name q : String} {parent eParent : ObjId}
    {body : RubyCore.Expr} (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (hm : constOwn m.heap m.currentFrame.defmod name = none)
    (hd : m.currentFrame.defmod < m.heap.objs.size) (hp : parent < m.heap.objs.size)
    (he : (m.heap.get parent).eigen = some eParent)
    (hq : (if m.currentFrame.defmod == Boot.objectId then name
      else className m.heap m.currentFrame.defmod ++ "::" ++ name) = q)
    (hn : q.isEmpty = false) :
    ∃ n, enterClassBody m name false (some parent) body = .next n ∧
      ClassReady n.heap ∧ Saturated n.heap := by
  have hep := hc.chains.eigen parent hp eParent he
  exact ⟨_, enter_fresh hm hd hp he hq hn, hc.subclass hs hp hep,
    saturated hc.chains hs hp hep⟩

/-- Declared-parent conformance supplies the cached metaclass; no physical-cache premise
is left for a certificate to assert. The newly created site is ready for further subclasses.
This is still entry readiness, not full StateOk or a checked class body. -/
theorem enter_declared_fresh {κ : Ratchet.Ctx} {Γ : Ratchet.Env} {I : Ratchet.Ty}
    {m : Machine} {c : Ratchet.Cls} {parent : ObjId} {name q : String} {body : RubyCore.Expr}
    (hm : StateOk κ Γ I m) (hc : c ∈ κ.classes) (hp : classNamed? m.heap c.name = some parent)
    (hf : constOwn m.heap m.currentFrame.defmod name = none)
    (hd : m.currentFrame.defmod < m.heap.objs.size)
    (hq : (if m.currentFrame.defmod == Boot.objectId then name
      else className m.heap m.currentFrame.defmod ++ "::" ++ name) = q)
    (hn : q.isEmpty = false) :
    ∃ n, enterClassBody m name false (some parent) body = .next n ∧
      ClassReady n.heap ∧ Saturated n.heap ∧ MetaReady n.heap m.heap.objs.size := by
  obtain ⟨ep, he, hb, _⟩ := hm.classSites.metaclass hc hp
  have hl := hm.core.classReady.constRefs c.name parent (classNamed_constOwn hp)
  have hep := hm.core.classReady.chains.eigen parent hl ep he
  exact ⟨_, enter_fresh hf hd hl he hq hn, hm.core.classReady.subclass hm.sat hl hep,
    saturated hm.core.classReady.chains hm.sat hl hep, meta_fresh hm.core.classReady.chains hm.sat hep hb⟩

#print axioms enter_fresh
#print axioms step_resolved
#print axioms enter_fresh_ready
#print axioms enter_declared_fresh
end Ratchet.Denote.Subclass
