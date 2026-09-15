import Denote.Sem.SubclassHeap
import Denote.Sem.MetaReadyClass
import Denote.Sem.SubclassCore
import Denote.Sem.SubclassMethods
import Denote.Sem.SubclassBases
import Denote.Sem.SubclassDeclared
import Denote.Sem.SubclassNameEntry
import Denote.Sem.SubclassSites
import Denote.Sem.ClassNative
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

/-- Top-level subclass entry preserves all incoming first-order data. Its metaclass
ancestry is recovered from the parent site, independently of method/body annotations. -/
theorem enter_declared_data {κ : Ratchet.Ctx} {Γ : Ratchet.Env} {I : Ratchet.Ty}
    {m : Machine} {c : Ratchet.Cls} {parent : ObjId} {name : String} {body : RubyCore.Expr}
    (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true)
    (hc : c ∈ κ.classes) (hp : classNamed? m.heap c.name = some parent)
    (hf : constOwn m.heap Boot.objectId name = none) (hn : name.isEmpty = false) :
    ∃ n, enterClassBody m name false (some parent) body = .next n ∧ DataPres m.heap n.heap := by
  obtain ⟨ep, he, hb, _⟩ := hm.classSites.metaclass hc hp
  have hl := hm.core.classReady.constRefs c.name parent (classNamed_constOwn hp)
  have hep := hm.core.classReady.chains.eigen parent hl ep he
  have howner := (hm.runtime hr).owner
  refine ⟨machine m Boot.objectId m.currentFrame.cref name name parent ep body, ?_, ?_⟩
  · simpa only [howner] using enter_fresh (m := m) (q := name) (body := body)
      (by simpa only [howner] using hf)
      (by simpa only [howner] using hm.core.classReady.chains.boot.2.2.2.2) hl he
      (by simp only [howner, beq_self_eq_true, ite_true]) hn
  · exact dataPres hm.core.classReady hm.sat hm.core.basicSelf hf hep hb

theorem enter_declared_queries {κ : Ratchet.Ctx} {Γ : Ratchet.Env} {I : Ratchet.Ty}
    {m : Machine} {c : Ratchet.Cls} {parent : ObjId} {name : String} {body : RubyCore.Expr}
    (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true)
    (hc : c ∈ κ.classes) (hp : classNamed? m.heap c.name = some parent)
    (hf : constOwn m.heap Boot.objectId name = none) (hn : name.isEmpty = false)
    (hq : FreshClass.NativeFrame κ name) :
    ∃ n, enterClassBody m name false (some parent) body = .next n ∧
      QueryOk κ n ∧ ClsQueryOk κ n ∧ NilQueryOk κ n ∧
      primitiveDispatchB n.heap (Ratchet.nameFreeN κ) = true ∧ primitiveErrorsB n.heap = true := by
  obtain ⟨ep, he, _, _⟩ := hm.classSites.metaclass hc hp
  have hl := hm.core.classReady.constRefs c.name parent (classNamed_constOwn hp)
  have hch := hm.core.classReady.chains
  have hep := hch.eigen parent hl ep he
  have howner := (hm.runtime hr).owner
  have hcp : (m.heap.classPayload? parent).isSome = true := by
    simpa using congrArg Option.isSome (hm.declCls c hc parent hp).2.2.2.1
  refine ⟨machine m Boot.objectId m.currentFrame.cref name name parent ep body, ?_,
    query hch hm.sat hl hep hn hq.query rfl hm.query,
    clsQuery hch hm.sat hcp he hn hq.clsQuery rfl hm.clsQuery,
    nilQuery hch hm.sat hl hep hn hq.nilQuery rfl hm.nilQuery,
    (primitiveDispatch hch hm.sat _).trans hm.primitiveDispatch,
    (primitiveErrors hch hm.sat).trans hm.primitiveErrors⟩
  simpa only [howner] using enter_fresh (m := m) (q := name) (body := body)
    (by simpa only [howner] using hf) (by simpa only [howner] using hch.boot.2.2.2.2) hl he
    (by simp only [howner, beq_self_eq_true, ite_true]) hn

/-- Actual top-level registration preserves core/payload and installed-code conformance,
and publishes a unique fresh name. This does not check or execute the new class body. -/
theorem enter_declared_core {κ : Ratchet.Ctx} {Γ : Ratchet.Env} {I : Ratchet.Ty}
    {m : Machine} {c : Ratchet.Cls} {parent : ObjId} {name : String} {body : RubyCore.Expr}
    (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true)
    (hc : c ∈ κ.classes) (hp : classNamed? m.heap c.name = some parent)
    (hf : constOwn m.heap Boot.objectId name = none) (hn : name.isEmpty = false) :
    ∃ n, enterClassBody m name false (some parent) body = .next n ∧
      CoreOk n.heap ∧ StringPayloadOk n.heap ∧ ArrayPayloadOk n.heap ∧ HashPayloadOk n.heap ∧
      ClassesOk κ.classes n ∧ DefsOk κ.defs n ∧ MethodsExact κ n ∧
      classNamed? n.heap name = some m.heap.objs.size ∧
      (∀ cn, classNamed? n.heap cn = some m.heap.objs.size → cn = name) := by
  obtain ⟨ep, he, _, _⟩ := hm.classSites.metaclass hc hp
  have hl := hm.core.classReady.constRefs c.name parent (classNamed_constOwn hp)
  have hch := hm.core.classReady.chains
  have hep := hch.eigen parent hl ep he
  have ho := hch.boot.2.2.2.2
  have howner := (hm.runtime hr).owner
  refine ⟨machine m Boot.objectId m.currentFrame.cref name name parent ep body, ?_,
    core hm.core hm.sat (hm.runtime hr).classLive hf hl hep,
    stringPayload hch hm.stringPayload, arrayPayload hm.arrayPayload,
    hashPayload hm.hashPayload, classes ho hf rfl hm.classes, defs rfl hm.defs,
    methodsExact rfl hm.exact, named_fresh (hm.runtime hr).classLive,
    fun _ hk => named_fresh_only hm.core.classReady.constRefs ho hk⟩
  simpa only [howner] using enter_fresh (m := m) (q := name) (body := body)
    (by simpa only [howner] using hf) (by simpa only [howner] using ho) hl he
    (by simp only [howner, beq_self_eq_true, ite_true]) hn

/-- Preserve existing declaration/ancestry tables at actual entry. The static base frame
and retained class sites discharge both fresh-head obligations from incoming conformance. -/
theorem enter_declared_tables {κ : Ratchet.Ctx} {Γ : Ratchet.Env} {I : Ratchet.Ty}
    {m : Machine} {c : Ratchet.Cls} {parent : ObjId} {name : String} {body : RubyCore.Expr}
    (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true)
    (hc : c ∈ κ.classes) (hp : classNamed? m.heap c.name = some parent)
    (hf : constOwn m.heap Boot.objectId name = none) (hn : name.isEmpty = false)
    (hb : Ratchet.subclassBaseFrameB κ c.name = true) :
    ∃ n, enterClassBody m name false (some parent) body = .next n ∧
      BaseChainsOk κ n ∧ DeclClassOk κ n ∧ ClassOwnNames κ.classes n.heap ∧ ClassChains κ.classes n.heap := by
  obtain ⟨ep, he, _, hsep⟩ := hm.classSites.metaclass hc hp
  have hl := named_live hp
  have hch := hm.core.classReady.chains
  have hep := hch.eigen parent hl ep he
  have ho := hch.boot.2.2.2.2
  have howner := (hm.runtime hr).owner
  refine ⟨machine m Boot.objectId m.currentFrame.cref name name parent ep body, ?_,
    baseChains hm.core.classReady hm.sat (hm.runtime hr).classLive hf hl hep
      (fun _ _ hbase hneg => hm.subclass_parent_separate hc hp hb hbase hneg) hsep rfl hm.baseChains,
    declared hch hm.sat (hm.runtime hr).classLive hf rfl hm.classes hm.declCls,
    ownNames ho hf hm.classes hm.ownNames, classChains hm.core.classReady hm.sat hf hm.classes hm.classChains⟩
  simpa only [howner] using enter_fresh (m := m) (q := name) (body := body)
    (by simpa only [howner] using hf) (by simpa only [howner] using ho) hl he
    (by simp only [howner, beq_self_eq_true, ite_true]) hn

/-- The new class-body frame and its name-based dispatch contract come from allocation
and retained parent-class facts, independently of the new body's annotations or syntax. -/
theorem enter_declared_frame {κ : Ratchet.Ctx} {Γ : Ratchet.Env} {I : Ratchet.Ty}
    {m : Machine} {c : Ratchet.Cls} {parent : ObjId} {name : String} {body : RubyCore.Expr}
    (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true)
    (hc : c ∈ κ.classes) (hp : classNamed? m.heap c.name = some parent)
    (hf : constOwn m.heap Boot.objectId name = none) (hn : name.isEmpty = false) :
    ∃ n, enterClassBody m name false (some parent) body = .next n ∧ NameFreeOk κ n ∧
      FrameInRange n ∧ EnvOk [] n ∧ SelfSpineOk .ivar0 n ∧ FrameOk none n ∧
      BlockTyOk none n ∧ SelfTyOk (some (.clsOf name)) n ∧ SelfLive n ∧ RootUncaptured n := by
  have site := hm.classSites.at_class hc hp
  obtain ⟨ep, he, _, _⟩ := site.metaclass
  have hch := hm.core.classReady.chains
  have hep := hch.eigen parent site.live ep he
  have howner := (hm.runtime hr).owner
  have hnames : NamesAt (Ratchet.nameFreeN κ) m.heap ep := by
    simpa only [classOf, he] using site.classNames
  refine ⟨machine m Boot.objectId m.currentFrame.cref name name parent ep body, ?_,
    nameFree hch hm.sat hep hnames hm.nameFree, frame_in_range, env_empty, spine_empty,
    frame_ok, block_none, self_type (hm.runtime hr).classLive, self_live, uncaptured⟩
  simpa only [howner] using enter_fresh (m := m) (q := name) (body := body)
    (by simpa only [howner] using hf) (by simpa only [howner] using hch.boot.2.2.2.2) site.live he
    (by simp only [howner, beq_self_eq_true, ite_true]) hn

/-- Retained parent constants, hooks and dispatch facts establish the new lexical scope
and class site; registration also preserves every previously declared site. -/
theorem enter_declared_sites {κ : Ratchet.Ctx} {Γ : Ratchet.Env} {I : Ratchet.Ty}
    {m : Machine} {c : Ratchet.Cls} {parent : ObjId} {name : String} {body : RubyCore.Expr}
    (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true)
    (hc : c ∈ κ.classes) (hp : classNamed? m.heap c.name = some parent)
    (hf : constOwn m.heap Boot.objectId name = none) (hn : name.isEmpty = false) :
    ∃ n, enterClassBody m name false (some parent) body = .next n ∧ ConstScopeOk n ∧
      ClassScopeReady name n ∧ ClassSitesOk (Ratchet.classBodyCtx κ name) n.heap := by
  have site := hm.classSites.at_class hc hp
  obtain ⟨ep, he, hb, _⟩ := site.metaclass
  have hch := hm.core.classReady.chains
  have ready := hm.runtime hr
  have hconst := fallback_of_instance site.constants
  have hnames : NamesAt (Ratchet.nameFreeN κ) m.heap ep := by
    simpa only [classOf, he] using site.classNames
  refine ⟨machine m Boot.objectId m.currentFrame.cref name name parent ep body, ?_,
    const_scope hch hm.sat ready.classLive site.live ready.cref hconst,
    scope_ready hch hm.sat ready.classLive site.live he site.hook ready.cref ready.phase, ?_⟩
  · simpa only [ready.owner] using enter_fresh (m := m) (q := name) (body := body)
      (by simpa only [ready.owner] using hf)
      (by simpa only [ready.owner] using hch.boot.2.2.2.2) site.live he
      (by simp only [ready.owner, beq_self_eq_true, ite_true]) hn
  · intro cn hcn
    change cn ∈ κ.classes.map (·.name) ++ [name] at hcn
    rcases List.mem_append.mp hcn with hcn | hcn
    · obtain ⟨k, old⟩ := hm.classSites cn (List.mem_append_left _ hcn)
      exact ⟨k, instanceSite_old old hch hm.sat ready.classLive hf⟩
    · have heq := List.mem_singleton.mp hcn
      subst cn
      exact ⟨m.heap.objs.size, instanceSite hch hm.sat ready.classLive site.live he hb site.hook
        hconst site.names hnames⟩

#print axioms enter_declared_sites
#print axioms enter_declared_frame
#print axioms enter_declared_tables
#print axioms enter_declared_core
#print axioms enter_fresh
#print axioms step_resolved
#print axioms enter_fresh_ready
#print axioms enter_declared_fresh
#print axioms enter_declared_data
#print axioms enter_declared_queries
end Ratchet.Denote.Subclass
