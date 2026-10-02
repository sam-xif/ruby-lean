import Denote.Sem.Class.ClassRegistration
import Denote.Sem.Class.ClassGrowth

/-! The actual named class and attached metaclass, factored over the existing
registration heap. Retain the old read/growth proof strategy with current metadata. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClassActual
open RubyCore RubyCore.Interp RubyCore.Proof RubyCore.Proof.Judgment

def namedObject (h : Heap) (name : String) (p : ObjId := Boot.objectId) : Object :=
  { klass := Boot.classId, revision := 1,
    payload := .cls { freshClassPayload h p with name, namePermanent := true } }

variable {p : ObjId}

theorem registered_get {m : Machine} {name : String}
    (hd : m.lexicalNamespace < m.heap.objs.size) :
    (freshClassRegistered m name p).get m.heap.objs.size =
      { klass := Boot.classId, payload := .cls (freshClassPayload m.heap p) } := by
  unfold freshClassRegistered
  rw [Static.get_constSetIn_ne _ _ _ _ _ (Ne.symm (Nat.ne_of_lt hd))]
  exact objs_getD_push_self _ _

theorem named_size (m : Machine) (name : String) :
    (freshClassNamed m name p).objs.size = m.heap.objs.size + 1 := by
  simp only [freshClassNamed, freshClassRegistered, Heap.setClassPayload,
    Heap.set, Array.size_set!, objs_size_constSetIn, Heap.alloc, Array.size_push]

theorem named_get {m : Machine} {name : String}
    (hd : m.lexicalNamespace < m.heap.objs.size) :
    (freshClassNamed m name p).get m.heap.objs.size = namedObject m.heap name p := by
  have hs : (freshClassRegistered m name p).objs.size = m.heap.objs.size + 1 := by
    simp only [freshClassRegistered, objs_size_constSetIn, Heap.alloc, Array.size_push]
  have hl : m.heap.objs.size < (freshClassRegistered m name p).objs.size := by omega
  unfold freshClassNamed Heap.setClassPayload Heap.set
  change (Array.set! _ m.heap.objs.size _).getD m.heap.objs.size default = _
  rw [objs_getD_set!_self _ _ _ hl]
  rw [registered_get hd]
  rfl

theorem named_get_old {m : Machine} {name : String} {o : ObjId}
    (hd : m.lexicalNamespace < m.heap.objs.size) (ho : o < m.heap.objs.size) :
    (freshClassNamed m name p).get o =
      (constSetIn m.heap m.lexicalNamespace name (.ref m.heap.objs.size)).get o := by
  unfold freshClassNamed Heap.setClassPayload Heap.set
  change (Array.set! _ m.heap.objs.size _).getD o default = _
  rw [objs_getD_set!_ne _ _ _ _ (Nat.ne_of_lt ho)]
  change (freshClassRegistered m name p).get o = _
  unfold freshClassRegistered
  rw [constSetIn_alloc_comm _ _ _ _ _ hd]
  apply objs_getD_push_lt
  simpa only [objs_size_constSetIn] using ho

/-- The cached superclass branch of the existing eigenclassOf_clsObj argument,
with the actual named payload and revision retained. -/
theorem eigenclassOf_named {m : Machine} {o e : ObjId} {name : String} {h : Heap}
    (hg : m.heap.get o = namedObject h name p)
    (he : (m.heap.get p).eigen = some e) (hp : 0 < m.heap.objs.size) :
    eigenclassOf m o =
      (m.heap.objs.size, { m with
        heap := attachEigen (m.heap.alloc (attachedClassEigen o e)).2 o m.heap.objs.size }) := by
  obtain ⟨n, hn⟩ : ∃ n, m.heap.objs.size = n + 1 :=
    ⟨m.heap.objs.size - 1, (Nat.succ_pred_eq_of_pos hp).symm⟩
  show eigenclassOf.go m o (m.heap.objs.size + 1) = _
  rw [hn]
  unfold eigenclassOf.go
  rw [hg]
  simp only [namedObject, freshClassPayload]
  rw [show eigenclassOf.go m p (n + 1) = (e, m) from eigenclassOf_go_some he]
  simp only [attachedClassEigen, attachEigen]
  rw [← hn]
  rfl

def heap (m : Machine) (name : String) (e : ObjId) (p : ObjId := Boot.objectId) : Heap :=
  attachEigen ((freshClassNamed m name p).alloc
    (attachedClassEigen m.heap.objs.size e)).2 m.heap.objs.size
    (freshClassNamed m name p).objs.size

theorem size (m : Machine) (name : String) (e : ObjId) :
    (heap m name e p).objs.size = m.heap.objs.size + 2 := by
  simp only [heap, attachEigen, Heap.set, Array.size_set!, Heap.alloc,
    Array.size_push, named_size]

theorem get_old {m : Machine} {name : String} {e o : ObjId}
    (hd : m.lexicalNamespace < m.heap.objs.size) (ho : o < m.heap.objs.size) :
    (heap m name e p).get o =
      (constSetIn m.heap m.lexicalNamespace name (.ref m.heap.objs.size)).get o := by
  unfold heap attachEigen Heap.set
  change (Array.set! _ m.heap.objs.size _).getD o default = _
  rw [objs_getD_set!_ne _ _ _ _ (Nat.ne_of_lt ho)]
  change ((freshClassNamed m name p).objs.push _).getD o default = _
  rw [objs_getD_push_lt (freshClassNamed m name p).objs _ o
    (by rw [named_size]; exact Nat.lt_succ_of_lt ho)]
  exact named_get_old hd ho

theorem get_class {m : Machine} {name : String} {e : ObjId}
    (hd : m.lexicalNamespace < m.heap.objs.size) :
    (heap m name e p).get m.heap.objs.size =
      { namedObject m.heap name p with eigen := some (m.heap.objs.size + 1), revision := 2 } := by
  have hg : ((freshClassNamed m name p).alloc (attachedClassEigen m.heap.objs.size e)).2.get
      m.heap.objs.size = namedObject m.heap name p := by
    change ((freshClassNamed m name p).objs.push _).getD m.heap.objs.size default = _
    rw [objs_getD_push_lt (freshClassNamed m name p).objs _ _ (by rw [named_size]; omega)]
    exact named_get hd
  unfold heap attachEigen Heap.set
  change (Array.set! _ m.heap.objs.size _).getD m.heap.objs.size default = _
  rw [objs_getD_set!_self _ _ _ (by simp only [Heap.alloc, Array.size_push, named_size]; omega)]
  rw [hg, named_size]
  rfl

theorem get_eigen (m : Machine) (name : String) (e : ObjId) :
    (heap m name e p).get (m.heap.objs.size + 1) = attachedClassEigen m.heap.objs.size e := by
  have hg := objs_getD_push_self (freshClassNamed m name p).objs (attachedClassEigen m.heap.objs.size e)
  simp only [named_size] at hg
  unfold heap attachEigen Heap.set
  change (Array.set! _ m.heap.objs.size _).getD (m.heap.objs.size + 1) default = _
  rw [objs_getD_set!_ne _ _ _ _ (by omega)]
  exact hg

theorem grow {m : Machine} {name : String} {e : ObjId}
    (hd : m.lexicalNamespace < m.heap.objs.size) :
    ClsGrow (constSetIn m.heap m.lexicalNamespace name (.ref m.heap.objs.size)) (heap m name e p) :=
  ⟨by rw [objs_size_constSetIn, size]; omega,
    fun _ ho => get_old hd (by simpa only [objs_size_constSetIn] using ho)⟩

theorem eigenclassOf_realized {m : Machine} {name : String} {e : ObjId}
    (hd : m.lexicalNamespace < m.heap.objs.size)
    (ho : p < m.heap.objs.size) (he : (m.heap.get p).eigen = some e) :
    eigenclassOf { m with heap := freshClassNamed m name p } m.heap.objs.size =
      (m.heap.objs.size + 1, { m with heap := heap m name e p }) := by
  have hcache : ((freshClassNamed m name p).get p).eigen = some e := by
    rw [named_get_old hd ho]
    exact (get_constSetIn_fields m.heap m.lexicalNamespace name (.ref m.heap.objs.size)
      p).2.2.1.trans he
  have hr := eigenclassOf_named (m := { m with heap := freshClassNamed m name p })
    (named_get hd) hcache (by rw [named_size]; omega)
  simpa only [named_size, heap] using hr

theorem fresh_cases {m : Machine} {name : String} {e o : ObjId}
    (ho : m.heap.objs.size ≤ o) (hl : o < (heap m name e p).objs.size) :
    o = m.heap.objs.size ∨ o = m.heap.objs.size + 1 := by
  have hb : o < m.heap.objs.size + 2 := size m name e ▸ hl
  rcases Nat.eq_or_lt_of_le ho with he | he
  · exact Or.inl he.symm
  · exact Or.inr (Nat.le_antisymm (Nat.le_of_lt_succ hb) he)

theorem chainsIn {m : Machine} {name : String} {e : ObjId}
    (hc : ChainsIn m.heap) (hd : m.lexicalNamespace < m.heap.objs.size)
    (he : e < m.heap.objs.size) (hp : p < m.heap.objs.size) : ChainsIn (heap m name e p) := by
  apply chainsIn_of_clsGrow (grow hd) (chainsIn_hmid hc)
  · intro o ho hl
    rw [hmid_size] at ho
    rcases fresh_cases ho hl with rfl | rfl
    all_goals
      simp only [get_class hd, get_eigen, namedObject, attachedClassEigen, size]
      exact Nat.lt_of_lt_of_le hc.boot.1 (by omega)
  · intro o ho hl e' he'
    rw [hmid_size] at ho
    rcases fresh_cases ho hl with rfl | rfl
    · rw [get_class hd] at he'
      have heq : m.heap.objs.size + 1 = e' := Option.some.inj he'
      subst e'
      rw [size]; exact Nat.lt_succ_self _
    · rw [get_eigen] at he'; cases he'
  · intro o cp ho hl hp
    rw [hmid_size] at ho
    rcases fresh_cases ho hl with rfl | rfl
    · simp only [Heap.classPayload?, get_class hd, namedObject] at hp
      cases hp
      exact ⟨fun s hs => by cases hs; rw [size]; exact Nat.lt_of_lt_of_le hp (Nat.le_add_right _ _),
        fun _ hi => False.elim (List.not_mem_nil hi), fun _ hi => False.elim (List.not_mem_nil hi)⟩
    · simp only [Heap.classPayload?, get_eigen, attachedClassEigen] at hp
      cases hp
      exact ⟨fun s hs => by cases hs; rw [size]; exact Nat.lt_of_lt_of_le he (Nat.le_add_right _ _),
        fun _ hi => False.elim (List.not_mem_nil hi), fun _ hi => False.elim (List.not_mem_nil hi)⟩

theorem saturated {m : Machine} {name : String} {e : ObjId}
    (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) (he : e < m.heap.objs.size)
    (hp : p < m.heap.objs.size) :
    Saturated (heap m name e p) := by
  apply saturated_of_clsGrow_heads (grow hd) (chainsIn_hmid hc) (saturated_hmid hs)
    (by rw [hmid_size, size]; exact Nat.le_refl _)
  · intro k hk hl f
    rw [hmid_size] at hk
    rcases fresh_cases hk hl with rfl | rfl
    all_goals
      rw [modAncestors.go.eq_def]
      simp [Heap.classPayload?, get_class hd, get_eigen, namedObject, freshClassPayload, attachedClassEigen]
  · intro k hk hl
    rw [hmid_size] at hk
    rcases fresh_cases hk hl with rfl | rfl
    · refine ⟨p, by rw [hmid_size]; exact hp, ?_⟩
      intro f
      rw [ancestors.go.eq_def]
      simp [Heap.classPayload?, get_class hd, namedObject, freshClassPayload]
    · refine ⟨e, by rwa [hmid_size], ?_⟩
      intro f
      rw [ancestors.go.eq_def]
      simp [Heap.classPayload?, get_eigen, attachedClassEigen]

theorem ancestors_old {m : Machine} {name : String} {e k : ObjId}
    (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) (hk : k < m.heap.objs.size) :
    ancestors (heap m name e p) k = ancestors m.heap k := by
  rw [ClsGrow.ancestors_old (grow hd) (chainsIn_hmid hc) (saturated_hmid hs)
    (by rw [hmid_size]; exact hk)]
  exact ancestors_constSetIn m.heap m.lexicalNamespace k name _

theorem fields_old {m : Machine} {name : String} {e k : ObjId}
    (hd : m.lexicalNamespace < m.heap.objs.size) (hk : k < m.heap.objs.size) :
    ((heap m name e p).get k).ivars = (m.heap.get k).ivars ∧
    ((heap m name e p).get k).klass = (m.heap.get k).klass ∧
    ((heap m name e p).get k).eigen = (m.heap.get k).eigen ∧
    ((heap m name e p).get k).frozen = (m.heap.get k).frozen := by
  rw [get_old hd hk]
  exact get_constSetIn_fields m.heap m.lexicalNamespace name (.ref m.heap.objs.size) k

theorem methods_old {m : Machine} {name : String} {e k : ObjId}
    (hd : m.lexicalNamespace < m.heap.objs.size) (hk : k < m.heap.objs.size) :
    ((heap m name e p).classPayload? k).map ClassPayload.methods =
      (m.heap.classPayload? k).map ClassPayload.methods := by
  rw [(grow hd).payloadOld (by rw [hmid_size]; exact hk), methods_constSetIn]

theorem classOf_old {m : Machine} {name : String} {e k : ObjId}
    (hd : m.lexicalNamespace < m.heap.objs.size) (hk : k < m.heap.objs.size) :
    classOf (heap m name e p) (.ref k) = classOf m.heap (.ref k) := by
  simp only [classOf, (fields_old hd hk).2.1, (fields_old hd hk).2.2.1]

theorem classPayload_live {m : Machine} {name : String} {e k : ObjId}
    (hd : m.lexicalNamespace < m.heap.objs.size) (hk : k < m.heap.objs.size) :
    ((heap m name e p).classPayload? k).isSome = (m.heap.classPayload? k).isSome := by
  rw [(grow hd).payloadOld (by rw [hmid_size]; exact hk)]
  exact classPayload?_isSome_constSetIn m.heap m.lexicalNamespace k name _

theorem allocator_ready {m : Machine} {name : String} {e : ObjId}
    (hd : m.lexicalNamespace < m.heap.objs.size) (hf : objectClassFlagsB m.heap p = true) :
    plainAllocationReadyB (heap m name e p) m.heap.objs.size = true := by
  simp only [plainAllocationReadyB, Heap.classPayload?, get_class hd, namedObject, Option.any]
  exact freshClassPayload_ready hf

theorem classHooksQuietB_eq {m : Machine} {name : String} {e : ObjId}
    (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) :
    classHooksQuietB (heap m name e p) = classHooksQuietB m.heap := by
  have ho := hc.boot.2.2.2.2
  have hco := ClsGrow.classOf_lt hc ho
  apply classHooksQuietB_congr
    (by simp only [objectCallbackPrefix, classOf_old hd ho, ancestors_old hc hs hd hco])
  intro selector k hk
  have hl : k < m.heap.objs.size :=
    ancestors_mem_lt hc hco k ((List.takeWhile_sublist (· != Boot.objectId)).subset hk)
  have hm := methods_old (name := name) (e := e) (p := p) hd hl
  cases ha : (heap m name e p).classPayload? k <;>
    cases hb : m.heap.classPayload? k <;>
    simp_all only [Option.map, Option.bind, Option.some.injEq] <;> cases hm

theorem stepFn_fresh {m : Machine} {name : String} {body : RubyCore.Expr} {e : ObjId}
    (hm : MainReady m) (hn : constOwn m.heap Boot.objectId name = none)
    (he : (m.heap.get Boot.objectId).eigen = some e) :
    stepFn { m with ctl := .eval (.class' name none body) } =
      .next { m with
        heap := heap m name e Boot.objectId,
        ctl := .send (.ref Boot.objectId) .reflective "const_added" [.sym name] none [],
        kont := .constClassK m.heap.objs.size (some Boot.objectId) name body :: m.kont } := by
  have ho : Boot.objectId < m.heap.objs.size :=
    Nat.lt_trans (by decide : Boot.objectId < Boot.mainId) hm.live
  have hd : m.lexicalNamespace < m.heap.objs.size := by
    simpa only [Machine.lexicalNamespace, hm.cref, List.headD_nil] using ho
  let start := { m with ctl := .eval (.class' name none body) }
  have hr := eigenclassOf_realized (m := start) (name := name) hd ho he
  have hnamed : freshClassNamed start name = freshClassNamed m name Boot.objectId := rfl
  simp only [hnamed] at hr
  rw [stepFn_class_registered hm hn]
  change callConstAdded _ Boot.objectId name = _
  rw [hr]
  simp only [callConstAdded, start, hm.phase, Bool.false_eq_true, ↓reduceIte]
  rfl

#print axioms named_get
#print axioms eigenclassOf_named
#print axioms grow
#print axioms eigenclassOf_realized
#print axioms chainsIn
#print axioms saturated
#print axioms ancestors_old
#print axioms methods_old
#print axioms allocator_ready
#print axioms classHooksQuietB_eq
#print axioms stepFn_fresh
end Ratchet.Denote.FreshClassActual
