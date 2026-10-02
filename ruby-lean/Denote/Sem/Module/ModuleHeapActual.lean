import Denote.Sem.Class.ClassHeapActual
import RubyCore.Proof.Judgment.ModFresh

/-! The actual named module and its attached metaclass (superclass Module), mirroring
FreshClassActual over the model's freshModuleRegistered/evalExpr_module_fresh. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshModuleActual
open RubyCore RubyCore.Interp RubyCore.Proof RubyCore.Proof.Judgment

def modPayload (name : String) : ClassPayload :=
  { superclass := none, name, isModule := true, namePermanent := true }

def namedObject (name : String) : Object :=
  { klass := Boot.moduleId, revision := 1, payload := .cls (modPayload name) }

def named (m : Machine) (name : String) : Heap :=
  (freshModuleRegistered m name).setClassPayload m.heap.objs.size (modPayload name)

theorem registered_size (m : Machine) (name : String) :
    (freshModuleRegistered m name).objs.size = m.heap.objs.size + 1 := by
  simp only [freshModuleRegistered, objs_size_constSetIn, Heap.alloc, Array.size_push]

theorem named_size (m : Machine) (name : String) :
    (named m name).objs.size = m.heap.objs.size + 1 := by
  simp only [named, Heap.setClassPayload, Heap.set, Array.size_set!, registered_size]

theorem registered_get {m : Machine} {name : String}
    (hd : m.lexicalNamespace < m.heap.objs.size) :
    (freshModuleRegistered m name).get m.heap.objs.size = modObj "" := by
  unfold freshModuleRegistered
  rw [Static.get_constSetIn_ne _ _ _ _ _ (Ne.symm (Nat.ne_of_lt hd))]
  exact objs_getD_push_self _ _

theorem registered_payload {m : Machine} {name : String}
    (hd : m.lexicalNamespace < m.heap.objs.size) :
    (freshModuleRegistered m name).classPayload? m.heap.objs.size =
      some { superclass := none, name := "", isModule := true } := by
  simp only [Heap.classPayload?, registered_get hd]

theorem named_get {m : Machine} {name : String}
    (hd : m.lexicalNamespace < m.heap.objs.size) :
    (named m name).get m.heap.objs.size = namedObject name := by
  have hl : m.heap.objs.size < (freshModuleRegistered m name).objs.size := by
    rw [registered_size]; omega
  unfold named Heap.setClassPayload Heap.set
  change (Array.set! _ m.heap.objs.size _).getD m.heap.objs.size default = _
  rw [objs_getD_set!_self _ _ _ hl, registered_get hd]
  rfl

theorem named_get_old {m : Machine} {name : String} {o : ObjId}
    (hd : m.lexicalNamespace < m.heap.objs.size) (ho : o < m.heap.objs.size) :
    (named m name).get o =
      (constSetIn m.heap m.lexicalNamespace name (.ref m.heap.objs.size)).get o := by
  unfold named Heap.setClassPayload Heap.set
  change (Array.set! _ m.heap.objs.size _).getD o default = _
  rw [objs_getD_set!_ne _ _ _ _ (Nat.ne_of_lt ho)]
  change (freshModuleRegistered m name).get o = _
  unfold freshModuleRegistered
  rw [constSetIn_alloc_comm _ _ _ _ _ hd]
  apply objs_getD_push_lt
  simpa only [objs_size_constSetIn] using ho

theorem registered_named {m : Machine} {name : String}
    (hc : m.currentFrame.cref = []) (hd : Boot.objectId < m.heap.objs.size) :
    nameConstant (freshModuleRegistered m name) m.lexicalNamespace name
      (.ref m.heap.objs.size) = .ok (named m name) := by
  have hl : m.lexicalNamespace = Boot.objectId := by simp [Machine.lexicalNamespace, hc]
  have hp := registered_payload (m := m) (name := name) (hl ▸ hd)
  rw [hl]
  exact nameConstant_empty_class hp rfl rfl

theorem eigenclassOf_named {mm : Machine} {o : ObjId} {name : String}
    (hg : mm.heap.get o = namedObject name) :
    eigenclassOf mm o =
      (mm.heap.objs.size, { mm with
        heap := attachEigen (mm.heap.alloc (attachedModuleEigen o)).2 o mm.heap.objs.size }) := by
  show eigenclassOf.go mm o (mm.heap.objs.size + 1) = _
  unfold eigenclassOf.go
  rw [hg]
  rfl

def heap (m : Machine) (name : String) : Heap :=
  attachEigen ((named m name).alloc (attachedModuleEigen m.heap.objs.size)).2 m.heap.objs.size
    (named m name).objs.size

theorem size (m : Machine) (name : String) :
    (heap m name).objs.size = m.heap.objs.size + 2 := by
  simp only [heap, attachEigen, Heap.set, Array.size_set!, Heap.alloc, Array.size_push, named_size]

theorem get_old {m : Machine} {name : String} {o : ObjId}
    (hd : m.lexicalNamespace < m.heap.objs.size) (ho : o < m.heap.objs.size) :
    (heap m name).get o =
      (constSetIn m.heap m.lexicalNamespace name (.ref m.heap.objs.size)).get o := by
  unfold heap attachEigen Heap.set
  change (Array.set! _ m.heap.objs.size _).getD o default = _
  rw [objs_getD_set!_ne _ _ _ _ (Nat.ne_of_lt ho)]
  change ((named m name).objs.push _).getD o default = _
  rw [objs_getD_push_lt (named m name).objs _ o (by rw [named_size]; exact Nat.lt_succ_of_lt ho)]
  exact named_get_old hd ho

theorem get_module {m : Machine} {name : String}
    (hd : m.lexicalNamespace < m.heap.objs.size) :
    (heap m name).get m.heap.objs.size =
      { namedObject name with eigen := some (m.heap.objs.size + 1), revision := 2 } := by
  have hg : ((named m name).alloc (attachedModuleEigen m.heap.objs.size)).2.get
      m.heap.objs.size = namedObject name := by
    change ((named m name).objs.push _).getD m.heap.objs.size default = _
    rw [objs_getD_push_lt (named m name).objs _ _ (by rw [named_size]; omega)]
    exact named_get hd
  unfold heap attachEigen Heap.set
  change (Array.set! _ m.heap.objs.size _).getD m.heap.objs.size default = _
  rw [objs_getD_set!_self _ _ _ (by simp only [Heap.alloc, Array.size_push, named_size]; omega)]
  rw [hg, named_size]
  rfl

theorem get_eigen (m : Machine) (name : String) :
    (heap m name).get (m.heap.objs.size + 1) = attachedModuleEigen m.heap.objs.size := by
  have hg := objs_getD_push_self (named m name).objs (attachedModuleEigen m.heap.objs.size)
  simp only [named_size] at hg
  unfold heap attachEigen Heap.set
  change (Array.set! _ m.heap.objs.size _).getD (m.heap.objs.size + 1) default = _
  rw [objs_getD_set!_ne _ _ _ _ (by omega)]
  exact hg

theorem grow {m : Machine} {name : String}
    (hd : m.lexicalNamespace < m.heap.objs.size) :
    ClsGrow (constSetIn m.heap m.lexicalNamespace name (.ref m.heap.objs.size)) (heap m name) :=
  ⟨by rw [objs_size_constSetIn, size]; omega,
    fun _ ho => get_old hd (by simpa only [objs_size_constSetIn] using ho)⟩

theorem fresh_cases {m : Machine} {name : String} {o : ObjId}
    (ho : m.heap.objs.size ≤ o) (hl : o < (heap m name).objs.size) :
    o = m.heap.objs.size ∨ o = m.heap.objs.size + 1 := by
  have hb : o < m.heap.objs.size + 2 := size m name ▸ hl
  rcases Nat.eq_or_lt_of_le ho with he | he
  · exact Or.inl he.symm
  · exact Or.inr (Nat.le_antisymm (Nat.le_of_lt_succ hb) he)

theorem eigenclassOf_realized {m : Machine} {name : String}
    (hd : m.lexicalNamespace < m.heap.objs.size) :
    eigenclassOf { m with heap := named m name } m.heap.objs.size =
      (m.heap.objs.size + 1, { m with heap := heap m name }) := by
  have hr := eigenclassOf_named (mm := { m with heap := named m name }) (named_get hd)
  simpa only [named_size, heap] using hr

theorem chainsIn {m : Machine} {name : String}
    (hc : ChainsIn m.heap) (hd : m.lexicalNamespace < m.heap.objs.size) :
    ChainsIn (heap m name) := by
  apply chainsIn_of_clsGrow (grow hd) (chainsIn_hmid hc)
  · intro o ho hl
    rw [hmid_size] at ho
    rcases fresh_cases ho hl with rfl | rfl
    all_goals
      simp only [get_module hd, get_eigen, namedObject, attachedModuleEigen, size]
      first
        | exact Nat.lt_of_lt_of_le hc.boot.1 (by omega)
        | exact Nat.lt_of_lt_of_le hc.boot.2.1 (by omega)
  · intro o ho hl e' he'
    rw [hmid_size] at ho
    rcases fresh_cases ho hl with rfl | rfl
    · rw [get_module hd] at he'
      have heq : m.heap.objs.size + 1 = e' := Option.some.inj he'
      subst e'
      rw [size]; exact Nat.lt_succ_self _
    · rw [get_eigen] at he'; cases he'
  · intro o cp ho hl hp
    rw [hmid_size] at ho
    rcases fresh_cases ho hl with rfl | rfl
    · simp only [Heap.classPayload?, get_module hd, namedObject, modPayload] at hp
      cases hp
      exact ⟨fun s hs => (by cases hs),
        fun _ hi => False.elim (List.not_mem_nil hi), fun _ hi => False.elim (List.not_mem_nil hi)⟩
    · simp only [Heap.classPayload?, get_eigen, attachedModuleEigen] at hp
      cases hp
      exact ⟨fun s hs => by cases hs; rw [size]; exact Nat.lt_of_lt_of_le hc.boot.2.1 (Nat.le_add_right _ _),
        fun _ hi => False.elim (List.not_mem_nil hi), fun _ hi => False.elim (List.not_mem_nil hi)⟩

theorem saturated {m : Machine} {name : String}
    (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) :
    Saturated (heap m name) := by
  apply saturated_of_clsGrow_roots (grow hd) (chainsIn_hmid hc) (saturated_hmid hs)
    (by rw [hmid_size, size]; exact Nat.le_refl _)
  · intro k hk hl f
    rw [hmid_size] at hk
    rcases fresh_cases hk hl with rfl | rfl
    all_goals
      rw [modAncestors.go.eq_def]
      simp [Heap.classPayload?, get_module hd, get_eigen, namedObject, modPayload, attachedModuleEigen]
  · intro k hk hl
    rw [hmid_size] at hk
    rcases fresh_cases hk hl with rfl | rfl
    · left
      intro f
      rw [ancestors.go.eq_def]
      simp [Heap.classPayload?, get_module hd, namedObject, modPayload]
    · right
      refine ⟨Boot.moduleId, by rw [hmid_size]; exact hc.boot.2.1, ?_⟩
      intro f
      rw [ancestors.go.eq_def]
      simp [Heap.classPayload?, get_eigen, attachedModuleEigen]

theorem ancestors_old {m : Machine} {name : String} {k : ObjId}
    (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) (hk : k < m.heap.objs.size) :
    ancestors (heap m name) k = ancestors m.heap k := by
  rw [ClsGrow.ancestors_old (grow hd) (chainsIn_hmid hc) (saturated_hmid hs)
    (by rw [hmid_size]; exact hk)]
  exact ancestors_constSetIn m.heap m.lexicalNamespace k name _

theorem fields_old {m : Machine} {name : String} {k : ObjId}
    (hd : m.lexicalNamespace < m.heap.objs.size) (hk : k < m.heap.objs.size) :
    ((heap m name).get k).ivars = (m.heap.get k).ivars ∧
    ((heap m name).get k).klass = (m.heap.get k).klass ∧
    ((heap m name).get k).eigen = (m.heap.get k).eigen ∧
    ((heap m name).get k).frozen = (m.heap.get k).frozen := by
  rw [get_old hd hk]
  exact get_constSetIn_fields m.heap m.lexicalNamespace name (.ref m.heap.objs.size) k

theorem methods_old {m : Machine} {name : String} {k : ObjId}
    (hd : m.lexicalNamespace < m.heap.objs.size) (hk : k < m.heap.objs.size) :
    ((heap m name).classPayload? k).map ClassPayload.methods =
      (m.heap.classPayload? k).map ClassPayload.methods := by
  rw [(grow hd).payloadOld (by rw [hmid_size]; exact hk), methods_constSetIn]

theorem classOf_old {m : Machine} {name : String} {k : ObjId}
    (hd : m.lexicalNamespace < m.heap.objs.size) (hk : k < m.heap.objs.size) :
    classOf (heap m name) (.ref k) = classOf m.heap (.ref k) := by
  simp only [classOf, (fields_old hd hk).2.1, (fields_old hd hk).2.2.1]

theorem classPayload_live {m : Machine} {name : String} {k : ObjId}
    (hd : m.lexicalNamespace < m.heap.objs.size) (hk : k < m.heap.objs.size) :
    ((heap m name).classPayload? k).isSome = (m.heap.classPayload? k).isSome := by
  rw [(grow hd).payloadOld (by rw [hmid_size]; exact hk)]
  exact classPayload?_isSome_constSetIn m.heap m.lexicalNamespace k name _

theorem classHooksQuietB_eq {m : Machine} {name : String}
    (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) :
    classHooksQuietB (heap m name) = classHooksQuietB m.heap := by
  have ho := hc.boot.2.2.2.2
  have hco := ClsGrow.classOf_lt hc ho
  apply classHooksQuietB_congr
    (by simp only [objectCallbackPrefix, classOf_old hd ho, ancestors_old hc hs hd hco])
  intro selector k hk
  have hl : k < m.heap.objs.size :=
    ancestors_mem_lt hc hco k ((List.takeWhile_sublist (· != Boot.objectId)).subset hk)
  have hm := methods_old (name := name)  hd hl
  cases ha : (heap m name).classPayload? k <;>
    cases hb : m.heap.classPayload? k <;>
    simp_all only [Option.map, Option.bind, Option.some.injEq] <;> cases hm

theorem stepFn_fresh {m : Machine} {name : String} {body : RubyCore.Expr}
    (hm : MainReady m) (hn : constOwn m.heap Boot.objectId name = none) :
    stepFn { m with ctl := .eval (.module' name body) } =
      .next { m with
        heap := heap m name,
        ctl := .send (.ref Boot.objectId) .reflective "const_added" [.sym name] none [],
        kont := .constClassK m.heap.objs.size none name body :: m.kont } := by
  have ho : Boot.objectId < m.heap.objs.size :=
    Nat.lt_trans (by decide : Boot.objectId < Boot.mainId) hm.live
  let start := { m with ctl := .eval (.module' name body) }
  have hc : start.currentFrame.cref = [] := hm.cref
  have hl : start.lexicalNamespace = Boot.objectId := by simp [Machine.lexicalNamespace, hc]
  have hd : m.lexicalNamespace < m.heap.objs.size := by
    simpa only [Machine.lexicalNamespace, hm.cref, List.headD_nil] using ho
  have he := evalExpr_module_fresh (m := start) (body := body)
    (by simpa only [hl] using hn) (by simpa only [hl] using hm.unfrozen) (registered_named hc ho)
  change evalExpr start (.module' name body) = _
  have hnamed : named start name = named m name := rfl
  simp only [hl, beq_self_eq_true, ↓reduceIte, hnamed, start] at he
  rw [he]
  have hr := eigenclassOf_realized (m := start) (name := name) hd
  simp only [hnamed] at hr
  rw [hr]
  simp only [callConstAdded, start, hm.phase, Bool.false_eq_true, ↓reduceIte]
  rfl

#print axioms named_get
#print axioms get_module
#print axioms stepFn_fresh
end Ratchet.Denote.FreshModuleActual
