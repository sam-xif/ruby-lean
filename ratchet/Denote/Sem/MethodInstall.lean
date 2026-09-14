import Denote.Sem.MethodHeap
import Denote.Sem.Reframe

/-! Conformance after installing a method. Positive tables must describe what was
installed; negative-name facts are retained only away from the written name.
-/

set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

theorem MethodsExact_defineMethod {κ : Ctx} {m : Machine} {cls : ObjId}
    {name : String} {md : MethodDef} (hm : MethodsExact κ m) (hn : nameFreeN κ name = false) :
    MethodsExact κ { m with heap := defineMethod m.heap cls name md } := by
  intro k cp hp n md' hmem
  change (defineMethod m.heap cls name md).classPayload? k = some cp at hp
  unfold defineMethod at hp
  split at hp
  · rename_i c hc
    by_cases hk : k = cls
    · subst k
      have hb : cls < m.heap.objs.size := lt_size_of_classPayload (by rw [hc]; rfl)
      simp only [Heap.classPayload?, Heap.setClassPayload, Heap.get, Heap.set,
        Proof.objs_getD_set!_self _ _ _ hb, Option.some.injEq] at hp
      subst cp
      simp only [List.mem_cons, List.mem_filter, Prod.mk.injEq] at hmem
      rcases hmem with ⟨he, _⟩ | ⟨he, _⟩
      · exact Or.inr (Or.inr (he ▸ hn))
      · exact hm cls c hc n md' he
    · have he : (m.heap.setClassPayload cls
          { c with methods := (name, md) :: c.methods.filter (·.1 != name) }).classPayload? k =
          m.heap.classPayload? k := by
        simp only [Heap.classPayload?, Heap.setClassPayload, Heap.get, Heap.set,
          Proof.objs_getD_set!_ne _ _ _ _ hk]
      rw [he] at hp
      exact hm k cp hp n md' hmem
  · exact hm k cp hp n md' hmem

theorem ownMethod_defineMethod_ne (h : Heap) (cls k : ObjId) (name n : String)
    (md : MethodDef) (hn : n ≠ name) :
    ((defineMethod h cls name md).classPayload? k).bind
        (fun cp => (cp.methods.find? (·.1 == n)).map (·.2)) =
      (h.classPayload? k).bind (fun cp => (cp.methods.find? (·.1 == n)).map (·.2)) := by
  have he := Proof.methods_find_defineMethod h cls k name n md hn
  cases hp : (defineMethod h cls name md).classPayload? k <;>
    cases hq : h.classPayload? k <;> simp_all

theorem ownMethod_defineMethod_self (h : Heap) (cls : ObjId) (name : String)
    (md : MethodDef) (hc : (h.classPayload? cls).isSome = true) :
    ((defineMethod h cls name md).classPayload? cls).bind
      (fun cp => (cp.methods.find? (·.1 == name)).map (·.2)) = some md := by
  have he := Proof.methods_find_defineMethod_self h cls name md hc
  cases hp : (defineMethod h cls name md).classPayload? cls <;> simp_all

/-- The installed syntax table contains the new body and all differently named old
bodies. Repeated names need replacement semantics, not the legacy table's plain cons. -/
theorem DefsOk_defineMethod {D : DefTable} {m : Machine} {d : Defn} {md : MethodDef}
    (hm : DefsOk D m) (hc : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : ∀ old ∈ D, old.name ≠ d.name)
    (hp : md.params = toRubyParams d.params) (hb : md.body = toRuby d.body)
    (hu : md.undefined = false) (hcode : TopMethodCode md) :
    DefsOk (d :: D) { m with heap := defineMethod m.heap Boot.objectId d.name md } := by
  intro old ho
  simp only [List.mem_cons] at ho
  rcases ho with he | ho
  · subst old
    exact ⟨md, ownMethod_defineMethod_self m.heap Boot.objectId d.name md hc, hp, hb, hu, hcode⟩
  · obtain ⟨prev, hfind, hparams, hbody, hundef, hprev⟩ := hm old ho
    exact ⟨prev, (ownMethod_defineMethod_ne m.heap Boot.objectId Boot.objectId
      d.name old.name md (hn old ho)).trans hfind, hparams, hbody, hundef, hprev⟩

theorem MainReady.methodWrite {m : Machine} (h : MainReady m) (cls : ObjId)
    (name : String) (md : MethodDef) (hq : "method_added" ≠ name) :
    MainReady { m with heap := defineMethod m.heap cls name md } := by
  have hmain : (defineMethod m.heap cls name md).get Boot.mainId = m.heap.get Boot.mainId := by
    by_cases he : Boot.mainId = cls
    · subst cls
      have hc : m.heap.classPayload? Boot.mainId = none := by
        simp only [Heap.classPayload?, h.payload]
      simp only [defineMethod, hc]
    · exact heap_get_defineMethod_ne he
  refine ⟨h.self, h.owner, h.cref, h.captured, h.phase,
    by simpa only [Proof.objs_size_defineMethod] using h.live,
    by rw [hmain]; exact h.payload, ?_, ?_, ?_, ?_⟩
  · simpa only [Proof.classOf_defineMethod, Proof.ancestors_defineMethod] using h.chain
  · simpa only [isAName_defineMethod] using h.object
  · simpa only [Proof.classPayload?_isSome_defineMethod] using h.classLive
  · simpa only [objectHookQuietB, Proof.lookup_defineMethod _ _ _ _ _ _ hq
      (Proof.classOf_defineMethod ..)] using h.hook

/-- Common state transport. The positive method/class tables are the installation
rule's obligations; all data, scope, and negative dispatch facts are derived here.
`method_missing` needs a stronger query contract before it can be rewritten. -/
theorem StateOk_methodWrite_tables {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {cls : ObjId}
    {name : String} {md : MethodDef} {C : CTable} {D : DefTable}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) (ha : κ.asms = [])
    (hn : nameFreeN κ name = false) (hmiss : "method_missing" ≠ name)
    (hquiet : "method_added" ≠ name)
    (hclasses : ClassesOk C { m with heap := defineMethod m.heap cls name md })
    (hdefs : DefsOk D { m with heap := defineMethod m.heap cls name md })
    (hnested : NestedClassesOk C { m with heap := defineMethod m.heap cls name md })
    (hdecl : DeclClassOk { κ with pos := { κ.pos with classes := C } }
      { m with heap := defineMethod m.heap cls name md }) :
    StateOk { κ with pos := { κ.pos with classes := C, defs := D } } Γ I
      { m with heap := defineMethod m.heap cls name md } := by
  let n : Machine := { m with heap := defineMethod m.heap cls name md }
  have hcf : n.currentFrame = m.currentFrame := rfl
  have hget (x : String) : n.getLocal x = m.getLocal x := by
    have hgo : ∀ fuel fid, Machine.getLocal.go n x fid fuel = Machine.getLocal.go m x fid fuel := by
      intro fuel
      induction fuel with
      | zero => intro fid; rfl
      | succ fuel ih =>
        intro fid
        simp only [Machine.getLocal.go, n]
        split
        · rfl
        · split
          · exact ih _
          · rfl
    exact hgo _ _
  have hden (τ : Ty) (ht : FirstOrder τ = true) (v : Value) :
      denM τ m v → denM τ n v := (denM_defineMethod ht rfl).mp
  have hne (x : String) (hx : nameFreeN κ x = true) : x ≠ name := by
    intro he; subst x; rw [hn] at hx; cases hx
  have hl (v : Value) (x : String) (hx : x ≠ name) : lookup n.heap v x = lookup m.heap v x :=
    Proof.lookup_defineMethod _ _ _ _ _ _ hx (Proof.classOf_defineMethod ..)
  have hmo (k : ObjId) (x : String) (hx : x ≠ name) :
      Interp.methodOn n.heap k x = Interp.methodOn m.heap k x :=
    methodOn_defineMethod _ _ _ _ _ _ hx
  have hco (v : Value) : classOf n.heap v = classOf m.heap v := Proof.classOf_defineMethod ..
  have hresolve (x : String) : constResolveAt n x = constResolveAt m x := by
    simp only [constResolveAt, hcf, n, Proof.constOwn_defineMethod, Proof.constLookupFrom_defineMethod]
  have hivar : ivarOf n.heap n.currentFrame.self = ivarOf m.heap m.currentFrame.self := by
    rw [hcf]; exact ivarOf_defineMethod ..
  refine {
    runtime := fun hr => (hm.runtime hr).methodWrite cls name md hquiet
    sat := Proof.Saturated_defineMethod hm.sat _ _ _
    primitiveDispatch := (primitiveDispatchB_defineMethod hn).trans hm.primitiveDispatch
    primitiveErrors := (primitiveErrorsB_defineMethod ..).trans hm.primitiveErrors
    stringPayload := hm.stringPayload.defineMethod
    arrayPayload := hm.arrayPayload.defineMethod
    hashPayload := hm.hashPayload.defineMethod
    core := hm.core.defineMethod
    frameInRange := hm.frameInRange
    env := ?_
    selfSpine := ?_
    classes := hclasses
    defs := hdefs
    asms := by change AsmsOk κ.asms n; simp [AsmsOk, ha]
    frame := ?_
    closures := trivial
    blockTy := ?_
    selfTy := ?_
    consts := ?_
    constPaths := ?_
    nested := hnested
    privConsts := trivial
    constScope := ?_
    exact := MethodsExact_defineMethod hm.exact hn
    nameFree := ?_
    bareFree := ?_
    missFree := ?_
    query := ?_
    clsQuery := ?_
    declCls := hdecl
    baseChains := ?_
    nilQuery := ?_
    selfLive := ?_ }
  · change EnvOk Γ n
    refine ⟨fun x τ hx => ?_, ?_⟩
    · obtain ⟨hd, halias⟩ := hm.env.1 x τ hx
      obtain ⟨z, hz⟩ := envGet?_mem hx
      have ht' : FirstOrder (stripAlias τ) = true := hΓ (z, τ) hz
      simp only [hget]
      exact ⟨hden _ ht' _ hd, halias⟩
    · intro x hx
      rw [hget]
      exact hm.env.2 x hx
  · change denSpine I n _ ∧ _
    rw [hivar]
    exact ⟨(denM_defineMethod_aux (m := m) (n := n) rfl I ht.spine).2 [] _ |>.mp hm.selfSpine.1,
      hm.selfSpine.2⟩
  · change FrameOk κ.frame n
    cases hf : κ.frame with
    | none => simpa only [FrameOk, hf, hcf] using hm.frame
    | some fr => simpa only [FrameOk, hf, hcf, n, isAName_defineMethod] using hm.frame
  · change BlockTyOk κ.blockTy n
    cases hb : κ.blockTy with
    | none => simpa only [BlockTyOk, hb, hcf] using hm.blockTy
    | some τ =>
      obtain ⟨v, hv, hd⟩ := (show ∃ v, m.currentFrame.blk = some v ∧ denM τ m v by
        simpa only [BlockTyOk, hb] using hm.blockTy)
      exact ⟨v, hv, hden _ (ht.block τ hb) _ hd⟩
  · change SelfTyOk κ.selfTy n
    cases hs : κ.selfTy with
    | none => trivial
    | some τ =>
      change denM τ n n.currentFrame.self
      rw [hcf]
      exact hden _ (ht.self τ hs) _ (by simpa only [SelfTyOk, hs] using hm.selfTy)
  · intro x τ hx
    obtain ⟨v, hv, hd⟩ := hm.consts x τ hx
    exact ⟨v, (hresolve x).trans hv, hden _ (ht.consts x τ hx) _ hd⟩
  · intro owner x τ k hx hk v hv
    change classNamed? n.heap owner = some k at hk
    change constLookupFrom n.heap k x = some v at hv
    simp only [n, classNamed?_defineMethod] at hk
    simp only [n, Proof.constLookupFrom_defineMethod] at hv
    exact hden _ (ht.paths _ τ hx) _ (hm.constPaths owner x τ k hx hk v hv)
  · intro x
    exact (hresolve x).trans ((hm.constScope x).trans (constLookup_defineMethod ..).symm)
  · intro x hx k hk o md' hfound
    by_cases he : x = name
    · exact Or.inr (Or.inr (he ▸ hn))
    · rw [hmo _ _ he] at hfound
      change k ∈ nameFreeSites n at hk
      exact hm.nameFree x hx k (by simpa only [nameFreeSites, hcf, hco] using hk) o md' hfound
  · intro x hx hfree hself
    change lookup n.heap n.currentFrame.self x = none
    rw [hcf, hl _ _ (hne x hfree)]
    exact hm.bareFree x hx hfree hself
  · intro hfree hself o md' hfound
    change Interp.methodOn n.heap (classOf n.heap n.currentFrame.self) "method_missing" = _ at hfound
    rw [hcf, hco, hmo _ _ hmiss] at hfound
    exact hm.missFree hfree hself o md' hfound
  · intro x bid hx hfree k
    have he := hne x hfree
    simpa only [QueryOk, methodOn_defineMethod _ _ _ _ _ _ he,
      methodOn_defineMethod _ _ _ _ _ _ hmiss, Proof.ancestors_defineMethod,
      crubyShadow_defineMethod] using hm.query x bid hx hfree k
  · intro x bid hx hfree o hp
    have he := hne x hfree
    simp only [ClassQuerySite, Proof.classPayload?_isSome_defineMethod,
      Proof.classOf_defineMethod] at hp
    simpa only [Proof.classOf_defineMethod, methodOn_defineMethod _ _ _ _ _ _ he,
      methodOn_defineMethod _ _ _ _ _ _ hmiss, Proof.ancestors_defineMethod,
      crubyShadow_defineMethod] using hm.clsQuery x bid hx hfree o hp
  · change BaseChainsOk κ n
    simpa only [BaseChainsOk, n, classNamed?_defineMethod, Proof.ancestors_defineMethod]
      using hm.baseChains
  · intro hfree k
    have he := hne "nil?" hfree
    simpa only [methodOn_defineMethod _ _ _ _ _ _ he,
      methodOn_defineMethod _ _ _ _ _ _ hmiss, Proof.ancestors_defineMethod,
      crubyShadow_defineMethod] using hm.nilQuery hfree k
  · change SelfLive n
    simpa only [SelfLive, hcf, n, Proof.objs_size_defineMethod] using hm.selfLive

/-- Backward-compatible specialization: a top-level definition changes only the def table.
The class/nested tables still describe the same declarations. -/
theorem StateOk_methodWrite {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {cls : ObjId}
    {name : String} {md : MethodDef} {D : DefTable}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) (ha : κ.asms = [])
    (hn : nameFreeN κ name = false) (hmiss : "method_missing" ≠ name)
    (hquiet : "method_added" ≠ name)
    (hclasses : ClassesOk κ.classes { m with heap := defineMethod m.heap cls name md })
    (hdefs : DefsOk D { m with heap := defineMethod m.heap cls name md })
    (hdecl : DeclClassOk κ { m with heap := defineMethod m.heap cls name md }) :
    StateOk { κ with pos := { κ.pos with defs := D } } Γ I
      { m with heap := defineMethod m.heap cls name md } :=
  StateOk_methodWrite_tables hm ht hΓ ha hn hmiss hquiet hclasses hdefs
    (by simpa only [NestedClassesOk, isClassRefNamed, classNamed?_defineMethod,
      Proof.constLookupFrom_defineMethod] using hm.nested) hdecl

/-- Full conformance for the top-level method slice (no program class declarations).
This discharges the positive-table premises of `StateOk_methodWrite` as well. It says
nothing about the body's annotation: that separate proof is consumed by call safety. -/
theorem StateOk_defineTopMethod {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {d : Defn} {md : MethodDef}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (ha : κ.asms = []) (hclasses : κ.classes = [])
    (hn : nameFreeN κ d.name = false) (hmiss : "method_missing" ≠ d.name)
    (hquiet : "method_added" ≠ d.name)
    (hc : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hfresh : ∀ old ∈ κ.defs, old.name ≠ d.name)
    (hp : md.params = toRubyParams d.params) (hb : md.body = toRuby d.body)
    (hu : md.undefined = false) (hcode : TopMethodCode md) :
    StateOk { κ with pos := { κ.pos with defs := d :: κ.defs } } Γ I
      { m with heap := defineMethod m.heap Boot.objectId d.name md } :=
  StateOk_methodWrite hm ht hΓ ha hn hmiss hquiet
    (by simp [ClassesOk, hclasses])
    (DefsOk_defineMethod hm.defs hc hfresh hp hb hu hcode)
    (by simp [DeclClassOk, hclasses])

/-- Reserving a method name weakens absence facts; it does not install a method or
add a positive signature. Thus it cannot authorize a call before its definition. -/
theorem StateOk_reserveName {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) (name : String) :
    StateOk { κ with neg := { κ.neg with declared := name :: κ.declared } } Γ I m := by
  let κ' : Ctx := { κ with neg := { κ.neg with declared := name :: κ.declared } }
  have hfree (x : String) (hx : nameFreeN κ' x = true) : nameFreeN κ x = true := by
    change (!κ.negUnpinned && !(name :: κ.declared).contains x) = true at hx
    simp only [List.contains_cons, Bool.not_or, Bool.and_eq_true] at hx
    simpa only [nameFreeN, Bool.and_eq_true] using ⟨hx.1, hx.2.2⟩
  have hneg (x : String) (hx : nameFreeN κ x = false) : nameFreeN κ' x = false := by
    cases hn : nameFreeN κ' x with
    | false => rfl
    | true => have he := hfree x hn; rw [hx] at he; cases he
  refine { hm with
    primitiveDispatch := ?_
    exact := fun k cp hp n md hmem =>
      (hm.exact k cp hp n md hmem).imp id (Or.imp id (hneg n))
    nameFree := fun n hn k hk o md hl =>
      (hm.nameFree n hn k hk o md hl).imp id (Or.imp id (hneg n))
    bareFree := fun n hn hf hs => hm.bareFree n hn (hfree n hf) hs
    missFree := fun hf hs => hm.missFree (hfree _ hf) hs
    query := fun n bid hn hf => hm.query n bid hn (hfree n hf)
    clsQuery := fun n bid hn hf => hm.clsQuery n bid hn (hfree n hf)
    nilQuery := fun hf => hm.nilQuery (hfree _ hf) }
  apply List.all_eq_true.mpr
  intro row hr
  obtain ⟨k, x, bid⟩ := row
  have hp := List.all_eq_true.mp hm.primitiveDispatch (k, x, bid) hr
  by_cases hf : nameFreeN κ' x = true
  · have ho := hfree x hf
    simp only [κ'] at hf
    simpa only [hf, ho, Bool.not_true, Bool.false_or] using hp
  · have hn : nameFreeN κ' x = false := Bool.eq_false_iff.mpr hf
    simp only [κ'] at hn
    simp only [hn, Bool.not_false, Bool.true_or]

#print axioms MethodsExact_defineMethod
#print axioms DefsOk_defineMethod
#print axioms StateOk_methodWrite
#print axioms StateOk_methodWrite_tables
#print axioms StateOk_defineTopMethod
#print axioms StateOk_reserveName
end Ratchet.Denote
