import RubyCore.Proof.Judgment.ClsFresh

/-! The model's two-allocation subclass heap when the parent's metaclass is cached.
The superclass and its metaclass are independent parameters; Object is only a specialization. -/
set_option autoImplicit false
namespace Ratchet.Denote.Subclass
open RubyCore RubyCore.Proof RubyCore.Proof.Judgment

@[reducible] def classObj (q : String) (parent : ObjId) : Object :=
  { klass := Boot.classId,
    payload := .cls { superclass := some parent, name := q, isModule := false } }

@[reducible] def classObjE (q : String) (parent e : ObjId) : Object :=
  { classObj q parent with eigen := some e }

def heap (h : Heap) (d : ObjId) (name q : String) (parent eParent : ObjId) : Heap :=
  ⟨(((hmidOf h d name).objs.push (classObj q parent)).push (eigObjC q eParent)).set!
    h.objs.size (classObjE q parent (h.objs.size + 1))⟩

def machine (m : Machine) (d : ObjId) (cref : List ObjId) (name q : String)
    (parent eParent : ObjId) (body : RubyCore.Expr) : Machine :=
  { m with
    heap := heap m.heap d name q parent eParent,
    frames := m.frames.push (freshModFrame m.heap.objs.size cref),
    stack := m.frames.size :: m.stack, kont := .frameK m.frames.size :: m.kont, ctl := .eval body }

theorem heap_object (h : Heap) (d : ObjId) (name q : String) (e : ObjId) :
    heap h d name q Boot.objectId e = freshClsHeap h d name q e := rfl

theorem machine_object (m : Machine) (d : ObjId) (cref : List ObjId) (name q : String)
    (e : ObjId) (body : RubyCore.Expr) :
    machine m d cref name q Boot.objectId e body = freshClsMachine m d cref name q e body := rfl

theorem size {h : Heap} {d parent eParent : ObjId} {name q : String} :
    (heap h d name q parent eParent).objs.size = h.objs.size + 2 := by
  simp [heap, Array.set!, Array.size_setIfInBounds, Array.size_push, hmid_size]

theorem get_old {h : Heap} {d parent eParent o : ObjId} {name q : String}
    (ho : o < h.objs.size) :
    (heap h d name q parent eParent).get o = (hmidOf h d name).get o := by
  show ((((hmidOf h d name).objs.push (classObj q parent)).push (eigObjC q eParent)).set!
    h.objs.size _).getD o default = (hmidOf h d name).objs.getD o default
  rw [objs_getD_set!_ne _ _ _ _ (Nat.ne_of_lt ho),
    objs_getD_push_lt _ _ o (by rw [Array.size_push, hmid_size]; exact Nat.lt_succ_of_lt ho),
    objs_getD_push_lt _ _ o (by rw [hmid_size]; exact ho)]

theorem get_class {h : Heap} {d parent eParent : ObjId} {name q : String} :
    (heap h d name q parent eParent).get h.objs.size = classObjE q parent (h.objs.size + 1) := by
  show ((((hmidOf h d name).objs.push (classObj q parent)).push (eigObjC q eParent)).set!
    h.objs.size _).getD h.objs.size default = _
  rw [objs_getD_set!_self _ _ _ (by rw [Array.size_push, Array.size_push, hmid_size]; omega)]

theorem fields {h : Heap} {d parent eParent o : ObjId} {name q : String}
    (ho : o < h.objs.size) :
    ((heap h d name q parent eParent).get o).ivars = (h.get o).ivars ∧
      ((heap h d name q parent eParent).get o).klass = (h.get o).klass ∧
      ((heap h d name q parent eParent).get o).eigen = (h.get o).eigen ∧
      ((heap h d name q parent eParent).get o).frozen = (h.get o).frozen := by
  rw [get_old ho]
  exact get_constSetIn_fields h d name (.ref h.objs.size) o

theorem get_eigen {h : Heap} {d parent eParent : ObjId} {name q : String} :
    (heap h d name q parent eParent).get (h.objs.size + 1) = eigObjC q eParent := by
  show ((((hmidOf h d name).objs.push (classObj q parent)).push (eigObjC q eParent)).set!
    h.objs.size _).getD (h.objs.size + 1) default = _
  rw [objs_getD_set!_ne _ _ _ _ (by omega),
    show h.objs.size + 1 = ((hmidOf h d name).objs.push (classObj q parent)).size by
      rw [Array.size_push, hmid_size], objs_getD_push_self]

theorem cp_oob {h : Heap} {d parent eParent o : ObjId} {name q : String}
    (ho : h.objs.size + 2 ≤ o) : (heap h d name q parent eParent).classPayload? o = none :=
  classPayload?_oob _ _ (by rw [size]; exact Nat.not_lt.mpr ho)

theorem classPayload_old_isSome {h : Heap} {d parent eParent k : ObjId} {name q : String}
    (hk : k < h.objs.size) :
    ((heap h d name q parent eParent).classPayload? k).isSome = (h.classPayload? k).isSome := by
  unfold Heap.classPayload?
  rw [get_old hk]
  exact classPayload?_isSome_constSetIn h d k name _

theorem classOf_old {h : Heap} {d parent eParent o : ObjId} {name q : String}
    (ho : o < h.objs.size) :
    classOf (heap h d name q parent eParent) (.ref o) = classOf h (.ref o) := by
  simp only [classOf, (fields ho).2.1, (fields ho).2.2.1]

theorem classOf_class {h : Heap} {d parent eParent : ObjId} {name q : String} :
    classOf (heap h d name q parent eParent) (.ref h.objs.size) = h.objs.size + 1 := by
  simp only [classOf, get_class, classObjE]

theorem classOf_eigen {h : Heap} {d parent eParent : ObjId} {name q : String} :
    classOf (heap h d name q parent eParent) (.ref (h.objs.size + 1)) = Boot.classId := by
  simp only [classOf, get_eigen, eigObjC]

theorem className_class {h : Heap} {d parent eParent : ObjId} {name q : String}
    (hq : q.isEmpty = false) : className (heap h d name q parent eParent) h.objs.size = q := by
  simp only [className, Heap.classPayload?, get_class, classObjE, hq, Bool.false_eq_true, ↓reduceIte]

theorem className_eigen {h : Heap} {d parent eParent : ObjId} {name q : String} :
    className (heap h d name q parent eParent) (h.objs.size + 1) = "#<Class:" ++ q ++ ">" := by
  simp only [className, Heap.classPayload?, get_eigen, eigObjC]
  change (if ("#<Class:" ++ q ++ ">").isEmpty then _ else _) = _
  rw [if_neg (by
    simp only [String.isEmpty_iff]
    intro he
    have hl := congrArg String.length he
    simp [String.length_append] at hl)]

/-- Factor alloc/register/alloc/attach into the same heap used by the semantic proofs. -/
theorem heap_machine (h : Heap) (d : ObjId) (name q : String) (parent eParent : ObjId)
    (hd : d < h.objs.size) :
    attachEigen ((constSetIn (h.alloc (classObj q parent)).2 d name (.ref h.objs.size)).alloc
      (eigObjC q eParent)).2 h.objs.size
      (constSetIn (h.alloc (classObj q parent)).2 d name (.ref h.objs.size)).objs.size =
      heap h d name q parent eParent := by
  unfold attachEigen
  rw [constSetIn_alloc_comm _ _ _ _ _ hd]
  have hsz : ((hmidOf h d name).alloc (classObj q parent)).2.objs.size = h.objs.size + 1 := by
    change ((hmidOf h d name).objs.push (classObj q parent)).size = _
    rw [Array.size_push, hmid_size]
  have hget : (((hmidOf h d name).alloc (classObj q parent)).2.alloc
      (eigObjC q eParent)).2.get h.objs.size = classObj q parent := by
    change (((hmidOf h d name).objs.push (classObj q parent)).push (eigObjC q eParent)).getD
      h.objs.size default = _
    rw [objs_getD_push_lt _ _ h.objs.size (by rw [Array.size_push, hmid_size]; omega),
      show h.objs.size = (hmidOf h d name).objs.size from (hmid_size h d name).symm,
      objs_getD_push_self]
  rw [hget, hsz]
  rfl

#print axioms heap_machine
end Ratchet.Denote.Subclass
