import Denote.Sem.Subclass.SubclassActualHeader

/-! A declared parent class supplies the facts Object supplies for a plain class:
its instance site, metaclass and constant agreement after the fresh registration. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClassActual
open RubyCore Ratchet RubyCore.Proof

/-- A front class with no prepends resolves its own constants first. -/
theorem instanceConstResolve_class {h : Heap} {k : ObjId} (hf : classFrontB h k = true)
    (hmod : (h.classPayload? k).any (·.isModule) = false) (cn : String) :
    instanceConstResolve h k cn = constLookupFrom h k cn := by
  obtain ⟨rest, ha⟩ := classFrontB_sound hf
  have hfrom := const_from_eq_firstM h k cn
  rw [ha] at hfrom
  unfold instanceConstResolve
  rw [hfrom]
  simp only [List.firstM, hmod, Bool.false_eq_true, ite_false]
  cases constOwn h k cn <;> cases List.firstM (fun j => constOwn h j cn) rest <;> rfl

variable {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {c : Cls} {p e : ObjId}

theorem ParentFacts.of_declared (hm : StateOk κ Γ I m) (hc : c ∈ κ.classes)
    (hp : classNamed? m.heap c.name = some p) (he : (m.heap.get p).eigen = some e)
    (hkind : c.isModule = false) :
    ParentFacts κ m.heap p e := by
  have site := hm.classSites.at_class hc hp
  have hclass := hm.declCls c hc p hp
  have hlive : (m.heap.classPayload? p).isSome = true := by
    simpa using congrArg Option.isSome hclass.2.2.2.1
  obtain ⟨e', he', hb, hsep⟩ := site.metaclass
  rw [he] at he'; cases he'
  have hco : classOf m.heap (.ref p) = e := by simp only [classOf, he]
  refine ⟨site.live, hlive, he, site.metaclass, site.hook, site.names, hco ▸ site.classNames,
    hco ▸ site.metaConstants, site.singletonHook, fun base ch hbase => ⟨?_, hsep base ch hbase⟩, ?_⟩
  rotate_left
  · have hi := site.inheritedHook
    have hm := hclass.2.2.2.1
    rw [hkind] at hm
    have hmod : (m.heap.classPayload? p).any (·.isModule) = false := by
      cases hq : m.heap.classPayload? p <;> simp_all
    simpa only [inheritedHookQuietB, hmod, Bool.false_or] using hi
  intro heq
  have hlt := Nat.lt_of_le_of_lt (builtinBase_bound hbase).1
    (Nat.lt_trans (by decide : Boot.procId < Boot.yielderId) site.afterBuiltins)
  exact (Nat.ne_of_lt hlt) heq.symm

/-- The parent's constant walk agrees with toplevel lookup after registration. -/
theorem parent_constants {name : String} (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true)
    (hc : c ∈ κ.classes) (hp : classNamed? m.heap c.name = some p)
    (hn : constOwn m.heap Boot.objectId name = none)
    (hreach : Boot.objectId ∈ ancestors m.heap p ∨ (m.heap.classPayload? p).any (·.isModule) = true)
    (hkind : c.isModule = false) :
    ∀ cn, constLookupFrom (heap m name e p) p cn = constLookup (heap m name e p) cn := by
  have site := hm.classSites.at_class hc hp
  have hmain := hm.runtime hr
  have htop : m.lexicalNamespace = Boot.objectId := by
    simp only [Machine.lexicalNamespace, hmain.cref, List.headD_nil]
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ hm.core.classReady.chains.boot.2.2.2.2
  have hconst (cn : String) : constLookupFrom m.heap Boot.objectId cn = constLookup m.heap cn := by
    rw [← constResolveAt_top hmain.cref]; exact hm.constScope cn
  have hold := instance_constants_old (e := e) (p := p) site hm.core.classReady hm.sat htop
    hmain.classLive hn hconst hreach
  have hmod : (m.heap.classPayload? p).any (·.isModule) = false := by
    have h := (hm.declCls c hc p hp).2.2.2.1
    rw [hkind] at h
    cases hq : m.heap.classPayload? p <;> simp_all
  intro cn
  rw [← instanceConstResolve_class (by rw [classFront_old hd site.live]; exact site.front)
    (by rw [metadata_any_old hd site.live (·.isModule) (fun _ => rfl)]; exact hmod) cn]
  exact hold cn

#print axioms instanceConstResolve_class
#print axioms ParentFacts.of_declared
#print axioms parent_constants

theorem headerSub {name : String} {body : RubyCore.Expr} (hm : StateOk κ Γ I m)
    (hr : κ.scope.runtimeMain = true) (hf : κ.frame = none) (ha : κ.asms = [])
    (ht : ClassTablesFrame κ name m) (hq : FreshClass.NativeFrame κ name)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false)
    (hc : c ∈ κ.classes) (hp : classNamed? m.heap c.name = some p)
    (halloc : c.name ∈ κ.pos.plainAlloc) (he : (m.heap.get p).eigen = some e)
    (hreach : ∀ cn ∈ κ.classes.map (·.name), ∀ k, InstanceSite κ cn k m.heap →
      Boot.objectId ∈ ancestors m.heap k ∨ (m.heap.classPayload? k).any (·.isModule) = true)
    (hquiet : classNativeQuietB name "new" = true) (hplain : unqualifiedClassB name = true)
    (hframe : SubclassHeaderFrame κ.classes name c.name)
    (hnew : smroGet? κ.classes c.name "new" = none) :
    StateOk (subclassHeaderCtx (classBodyCtx κ name) name c.name) [] .ivar0
      (machine m name e body p) := by
  have hmain := hm.runtime hr
  have htop : m.lexicalNamespace = Boot.objectId := by
    simp only [Machine.lexicalNamespace, hmain.cref, List.headD_nil]
  have hd : m.lexicalNamespace < m.heap.objs.size :=
    htop ▸ lt_size_of_classPayload hmain.classLive
  have hkind := hm.ordinary_decl hc halloc
  obtain ⟨k, hk, hpa⟩ := hm.allocators c.name halloc
  have heq := Option.some.inj (hp.symm.trans hk)
  subst k
  have site := hm.classSites.at_class hc hp
  have hs := stateAt (body := body) hm hr hf ha ht hq hn hne (ParentFacts.of_declared hm hc hp he hkind)
    (parent_constants hm hr hc hp hn (hreach c.name (List.mem_map_of_mem hc) p site) hkind) hreach
  exact StateOk_publish_empty_class (c := subclassHeader name c.name) hs rfl rfl rfl hplain
    (declared_headerSub (κ := κ) hm hr hc hp hpa he hn hne hquiet hnew hframe rfl)
    ⟨_, named_fresh htop hmain.classLive, plainSub hm.core.classReady hm.sat hd hpa⟩
    (ownNames_headerSub (κ := κ) hm hr hn)
    (classChains_headerSub (κ := κ) hm hr hc hp hkind hpa.live hn hframe)

#print axioms headerSub
end Ratchet.Denote.FreshClassActual
