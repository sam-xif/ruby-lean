import Denote.Sem.Transport
import RubyCore.Proof.HeapFacts

/-! What a method-table write preserves. It is not an allocation (`Ext` pins the
whole class payload). First-order denotations inspect data, not method bodies.+-/

set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

theorem heap_get_defineMethod_ne {h : Heap} {cls o : ObjId} {name : String}
    {md : MethodDef} (hne : o ≠ cls) :
    (defineMethod h cls name md).get o = h.get o := by
  unfold defineMethod
  split
  · unfold Heap.setClassPayload Heap.get Heap.set
    rw [Proof.objs_getD_set!_ne _ _ _ _ hne]
  · rfl

/-- Every object field except payload is retained, even at the definee. -/
theorem get_defineMethod_data (h : Heap) (cls o : ObjId) (name : String) (md : MethodDef) :
    { (defineMethod h cls name md).get o with payload := .none } =
      { h.get o with payload := .none } := by
  by_cases ho : o = cls
  · subst o
    unfold defineMethod
    split
    · simp only [Heap.setClassPayload, Heap.get, Heap.set]
      by_cases hb : cls < h.objs.size
      · rw [Proof.objs_getD_set!_self _ _ _ hb]
      · rw [Proof.objs_getD_set!_oob _ _ _ hb]
    · rfl
  · rw [heap_get_defineMethod_ne ho]

theorem constLookup_defineMethod (h : Heap) (cls : ObjId) (name n : String) (md : MethodDef) :
    constLookup (defineMethod h cls name md) n = constLookup h n := by
  have hco (h : Heap) : constLookup h n = constOwn h Boot.objectId n := by
    cases hc : h.classPayload? Boot.objectId <;> simp [constLookup, constOwn, hc]
  rw [hco, hco, Proof.constOwn_defineMethod]

theorem classNamed?_defineMethod (h : Heap) (cls : ObjId) (name n : String) (md : MethodDef) :
    classNamed? (defineMethod h cls name md) n = classNamed? h n := by
  simp only [classNamed?, constLookup_defineMethod, Proof.classPayload?_isSome_defineMethod]

theorem isAName_defineMethod (h : Heap) (cls : ObjId) (name n : String)
    (md : MethodDef) (v : Value) :
    isAName (defineMethod h cls name md) v n = isAName h v n := by
  simp only [isAName, classNamed?_defineMethod, isA, Proof.classOf_defineMethod,
    Proof.ancestors_defineMethod]

theorem isExactInst_defineMethod (h : Heap) (cls : ObjId) (name n : String)
    (md : MethodDef) (v : Value) :
    isExactInst (defineMethod h cls name md) v n = isExactInst h v n := by
  have hk (o : ObjId) : ((defineMethod h cls name md).get o).klass = (h.get o).klass := by
    simpa only using congrArg Object.klass (get_defineMethod_data h cls o name md)
  have he (o : ObjId) : ((defineMethod h cls name md).get o).eigen = (h.get o).eigen := by
    simpa only using congrArg Object.eigen (get_defineMethod_data h cls o name md)
  simp only [isExactInst, classNamed?_defineMethod, Proof.objs_size_defineMethod]
  cases classNamed? h n <;> cases v <;> simp_all only

theorem ivarOf_defineMethod (h : Heap) (cls : ObjId) (name : String) (md : MethodDef)
    (v : Value) : ivarOf (defineMethod h cls name md) v = ivarOf h v := by
  have hi (o : ObjId) : ((defineMethod h cls name md).get o).ivars = (h.get o).ivars := by
    simpa only using congrArg Object.ivars (get_defineMethod_data h cls o name md)
  funext x
  cases v <;> simp only [ivarOf, hi]

/-- Only a class payload can change, and it remains a class payload. -/
theorem payloadProbe_defineMethod {α : Type} (probe : Payload → α)
    (hc : ∀ c d : ClassPayload, probe (.cls c) = probe (.cls d))
    (h : Heap) (cls o : ObjId) (name : String) (md : MethodDef) :
    probe ((defineMethod h cls name md).get o).payload = probe (h.get o).payload := by
  by_cases ho : o = cls
  · subst o
    unfold defineMethod
    split
    · rename_i c hcp
      have hb : cls < h.objs.size := by
        by_cases hn : cls < h.objs.size
        · exact hn
        · rw [Proof.classPayload?_oob h cls hn] at hcp; cases hcp
      have hp : (h.get cls).payload = .cls c := by
        unfold Heap.classPayload? at hcp
        split at hcp <;> simp_all
      simp only [Heap.setClassPayload, Heap.get, Heap.set]
      rw [Proof.objs_getD_set!_self _ _ _ hb]
      change probe (.cls _) = probe (h.get cls).payload
      rw [hp]
      exact hc _ _
    · rfl
  · rw [heap_get_defineMethod_ne ho]

theorem arrElems?_defineMethod (h : Heap) (cls : ObjId) (name : String)
    (md : MethodDef) (v : Value) :
    arrElems? (defineMethod h cls name md) v = arrElems? h v := by
  cases v <;> try rfl
  exact payloadProbe_defineMethod (fun p => match p with | .arr xs => some xs | _ => none)
    (fun _ _ => rfl) h cls _ name md

theorem hshEntries?_defineMethod (h : Heap) (cls : ObjId) (name : String)
    (md : MethodDef) (v : Value) :
    hshEntries? (defineMethod h cls name md) v = hshEntries? h v := by
  cases v <;> try rfl
  exact payloadProbe_defineMethod (fun p => match p with | .hsh xs => some xs | _ => none)
    (fun _ _ => rfl) h cls _ name md

theorem denM_defineMethod_aux {m n : Machine} {cls : ObjId} {name : String} {md : MethodDef}
    (hh : n.heap = defineMethod m.heap cls name md) : ∀ τ : Ty, FirstOrder τ = true →
    (∀ v, denM τ m v ↔ denM τ n v) ∧
    (∀ seen g, denSpineFrom seen τ m g ↔ denSpineFrom seen τ n g) := by
  intro τ
  induction τ with
  | int | bool | nilT | sym | float | any | never | ivar0 =>
    intro _; exact ⟨fun _ => by simp [denM], fun _ _ => by simp [denSpineFrom]⟩
  | cls cn =>
    intro _
    exact ⟨fun _ => by simp only [denM, hh, isAName_defineMethod],
      fun _ _ => by simp [denSpineFrom]⟩
  | clsOf cn =>
    intro _
    exact ⟨fun _ => by simp only [denM, isClassRefNamed, hh, classNamed?_defineMethod],
      fun _ _ => by simp [denSpineFrom]⟩
  | nilable τ ih =>
    intro hf
    exact ⟨fun _ => by simp only [denM]; exact or_congr_right ((ih hf).1 _),
      fun _ _ => by simp [denSpineFrom]⟩
  | union σ τ ihσ ihτ =>
    intro hf
    simp only [FirstOrder, Bool.and_eq_true] at hf
    exact ⟨fun _ => by simp only [denM]; exact or_congr ((ihσ hf.1).1 _) ((ihτ hf.2).1 _),
      fun _ _ => by simp [denSpineFrom]⟩
  | sameAs x τ ih =>
    intro hf
    exact ⟨fun _ => by simp only [denM]; exact (ih hf).1 _,
      fun _ _ => by simp [denSpineFrom]⟩
  | arrayOf τ ih =>
    intro hf
    refine ⟨fun v => ?_, fun _ _ => by simp [denSpineFrom]⟩
    simp only [denM, hh, arrElems?_defineMethod]
    exact exists_congr fun xs => and_congr_right fun _ =>
      forall_congr' fun x => imp_congr_right fun _ => (ih hf).1 x
  | hashOf k w ihk ihw =>
    intro hf
    simp only [FirstOrder, Bool.and_eq_true] at hf
    refine ⟨fun v => ?_, fun _ _ => by simp [denSpineFrom]⟩
    simp only [denM, hh, hshEntries?_defineMethod]
    exact exists_congr fun es => and_congr_right fun _ =>
      forall_congr' fun p => imp_congr_right fun _ =>
        and_congr ((ihk hf.1).1 p.1) ((ihw hf.2).1 p.2)
  | inst cn I ih =>
    intro hf
    refine ⟨fun v => ?_, fun _ _ => by simp [denSpineFrom]⟩
    simp only [denM, hh, isExactInst_defineMethod, ivarOf_defineMethod]
    exact and_congr_right fun _ => (ih hf).2 [] _
  | ivarCons x σ rest ihσ ihrest =>
    intro hf
    simp only [FirstOrder, Bool.and_eq_true] at hf
    refine ⟨fun _ => by simp [denM], fun seen g => ?_⟩
    simp only [denSpineFrom]
    exact and_congr (or_congr_right ((ihσ hf.1).1 (g x))) ((ihrest hf.2).2 (x :: seen) g)
  | arrow0 r _ => intro hf; simp [FirstOrder] at hf
  | arrowCons p rest _ _ => intro hf; simp [FirstOrder] at hf
  | clos i cap st _ _ => intro hf; simp [FirstOrder] at hf

theorem denM_defineMethod {τ : Ty} {m n : Machine} {cls : ObjId} {name : String}
    {md : MethodDef} {v : Value} (ht : FirstOrder τ = true)
    (hh : n.heap = defineMethod m.heap cls name md) : denM τ m v ↔ denM τ n v :=
  (denM_defineMethod_aux hh τ ht).1 v

theorem Framed_defineMethod (m : Machine) (cls : ObjId) (name : String) (md : MethodDef) :
    Framed m { m with heap := defineMethod m.heap cls name md } :=
  ⟨rfl, fun k hk => by simpa only [Proof.classPayload?_isSome_defineMethod] using hk,
   fun v cn hv => by simpa only [isAName_defineMethod] using hv,
   fun τ ht v hv => (denM_defineMethod ht rfl).mp hv, FramePres.of_eq rfl rfl⟩

theorem methodOn_eq_go (h : Heap) (k : ObjId) (name : String) :
    Interp.methodOn h k name = lookup.go h name (ancestors h k) := by
  unfold Interp.methodOn
  induction ancestors h k with
  | nil => rfl
  | cons c rest ih =>
    rw [List.firstM, lookup.go]
    cases hp : h.classPayload? c with
    | none => simp [ih]
    | some cp =>
      simp only
      cases hm : cp.methods.find? (·.1 == name) with
      | none => simp [ih]
      | some pair => simp

theorem methodOn_defineMethod (h : Heap) (cls k : ObjId) (name n : String)
    (md : MethodDef) (hn : n ≠ name) :
    Interp.methodOn (defineMethod h cls name md) k n = Interp.methodOn h k n := by
  rw [methodOn_eq_go, methodOn_eq_go, Proof.ancestors_defineMethod,
    Proof.lookup_go_defineMethod h cls name n md hn]

theorem crubyShadow_defineMethod (h : Heap) (cls : ObjId) (name n : String)
    (md : MethodDef) (chain : List ObjId) :
    Interp.crubyShadow (defineMethod h cls name md) chain n = Interp.crubyShadow h chain n := by
  simp only [Interp.crubyShadow, Proof.className_defineMethod]

theorem primitiveDispatchB_defineMethod {h : Heap} {cls : ObjId} {name : String}
    {md : MethodDef} {free : String → Bool} (hn : free name = false) :
    primitiveDispatchB (defineMethod h cls name md) free = primitiveDispatchB h free := by
  unfold primitiveDispatchB
  congr 1
  funext row
  obtain ⟨k, n, bid⟩ := row
  by_cases he : n = name
  · subst n; simp [hn]
  · simp only [methodOn_defineMethod h cls k name n md he,
      Proof.ancestors_defineMethod, crubyShadow_defineMethod]

theorem primitiveErrorsB_defineMethod (h : Heap) (cls : ObjId) (name : String) (md : MethodDef) :
    primitiveErrorsB (defineMethod h cls name md) = primitiveErrorsB h := by
  unfold primitiveErrorsB
  congr 1
  funext k
  simp only [primitiveErrorB, Proof.ancestors_defineMethod]

theorem StringPayloadOk.defineMethod {h : Heap} {cls : ObjId} {name : String}
    {md : MethodDef} (hs : StringPayloadOk h) : StringPayloadOk (defineMethod h cls name md) := by
  intro o ho
  rw [Proof.classOf_defineMethod] at ho
  obtain ⟨s, hp⟩ := hs o ho
  have hx := payloadProbe_defineMethod
    (fun p => match p with | .str s => some s | _ => none) (fun _ _ => rfl) h cls o name md
  rw [hp] at hx
  cases hn : ((RubyCore.defineMethod h cls name md).get o).payload <;> simp_all

theorem ArrayPayloadOk.defineMethod {h : Heap} {cls : ObjId} {name : String}
    {md : MethodDef} (hs : ArrayPayloadOk h) : ArrayPayloadOk (defineMethod h cls name md) := by
  intro o xs hp
  have hx := payloadProbe_defineMethod
    (fun p => match p with | .arr xs => some xs | _ => none) (fun _ _ => rfl) h cls o name md
  rw [hp] at hx
  rw [Proof.classOf_defineMethod]
  cases hn : (h.get o).payload <;> simp_all
  exact hs o _ hn

theorem HashPayloadOk.defineMethod {h : Heap} {cls : ObjId} {name : String}
    {md : MethodDef} (hs : HashPayloadOk h) : HashPayloadOk (defineMethod h cls name md) := by
  intro o xs hp
  have hx := payloadProbe_defineMethod
    (fun p => match p with | .hsh xs => some xs | _ => none) (fun _ _ => rfl) h cls o name md
  rw [hp] at hx
  have hd : ((RubyCore.defineMethod h cls name md).get o).hashDflt = (h.get o).hashDflt := by
    simpa only using congrArg Object.hashDflt (get_defineMethod_data h cls o name md)
  rw [Proof.classOf_defineMethod, hd]
  cases hn : (h.get o).payload <;> simp_all
  exact hs o _ hn

theorem CoreOk.defineMethod {h : Heap} {cls : ObjId} {name : String}
    {md : MethodDef} (hc : CoreOk h) : CoreOk (defineMethod h cls name md) where
  classReady := hc.classReady.defineMethod
  basicSelf := by simpa only [Proof.ancestors_defineMethod] using hc.basicSelf
  stringNamed := by simpa only [classNamed?_defineMethod] using hc.stringNamed
  stringSelf := by simpa only [Proof.ancestors_defineMethod] using hc.stringSelf
  stringBasic := by simpa only [Proof.ancestors_defineMethod] using hc.stringBasic
  regexpNamed := by simpa only [classNamed?_defineMethod] using hc.regexpNamed
  regexpSelf := by simpa only [Proof.ancestors_defineMethod] using hc.regexpSelf
  regexpBasic := by simpa only [Proof.ancestors_defineMethod] using hc.regexpBasic
  procBasic := by simpa only [Proof.ancestors_defineMethod] using hc.procBasic
  arrayBasic := by simpa only [Proof.ancestors_defineMethod] using hc.arrayBasic
  hashBasic := by simpa only [Proof.ancestors_defineMethod] using hc.hashBasic
  coreNamed := by
    simpa only [constLookup_defineMethod, Proof.classPayload?_isSome_defineMethod]
      using hc.coreNamed

#print axioms denM_defineMethod
#print axioms Framed_defineMethod
#print axioms primitiveDispatchB_defineMethod

end Ratchet.Denote
