import Books.TypeSoundness.Conformance.Heap.WriteState
import Books.TypeSoundness.Conformance.Class.ClassMetadataActual
import Books.TypeSoundness.Conformance.Class.ClassData
import Books.TypeSoundness.Conformance.Subclass.SubclassData

/-! A fresh top-level constant bound to a non-class value. Only Object's own constant
table changes: dispatch, ancestry, class names and object data are untouched, and every
class-name resolution agrees because the new value is not a class. -/
set_option autoImplicit false
namespace Checker.Soundness.ConstAdd
open RubyCore Checker RubyCore.Proof

/-- The value names no class, and a reference is live. -/
def NonClassVal (h : Heap) (v : Value) : Prop :=
  ∀ o, v = .ref o → h.classPayload? o = none ∧ o < h.objs.size

variable {h : Heap} {n : String} {v : Value}
local notation "H" => constSetIn h Boot.objectId n v

theorem size : (H).objs.size = h.objs.size := objs_size_constSetIn h _ n v

theorem fields (o : ObjId) :
    ((H).get o).ivars = (h.get o).ivars ∧ ((H).get o).klass = (h.get o).klass ∧
    ((H).get o).eigen = (h.get o).eigen ∧ ((H).get o).frozen = (h.get o).frozen :=
  get_constSetIn_fields h _ n v o

theorem anc (k : ObjId) : ancestors H k = ancestors h k := ancestors_constSetIn h _ k n v

theorem classOf_eq (w : Value) : classOf H w = classOf h w := RubyCore.Proof.Static.classOf_constSetIn h _ n v w

theorem metaEq {α : Type} (f : ClassPayload → α)
    (hf : ∀ cp, f { cp with consts := (n, v) :: cp.consts.filter (·.1 != n) } = f cp) (k : ObjId) :
    ((H).classPayload? k).map f = (h.classPayload? k).map f :=
  FreshClassActual.metadata_constSetIn h _ k n v f hf

theorem isSome_eq (k : ObjId) : ((H).classPayload? k).isSome = (h.classPayload? k).isSome :=
  classPayload?_isSome_constSetIn h _ k n v

theorem methodOn_eq (k : ObjId) (name : String) :
    Interp.methodOn H k name = Interp.methodOn h k name := by
  simp only [Interp.methodOn, anc]
  exact lookup_go_constSetIn h _ n v name _

theorem lookup_eq (w : Value) (name : String) : lookup H w name = lookup h w name := by
  rw [lookup_eq_methodOn, lookup_eq_methodOn, classOf_eq, methodOn_eq]

theorem shadow_eq (ks : List ObjId) (name : String) :
    Interp.crubyShadow H ks name = Interp.crubyShadow h ks name :=
  RubyCore.Proof.crubyShadow_constSetIn ks name

theorem get_ne {o : ObjId} (ho : o ≠ Boot.objectId) : (H).get o = h.get o :=
  RubyCore.Proof.Static.get_constSetIn_ne h _ o n v ho

theorem lookup_self (hO : (h.classPayload? Boot.objectId).isSome = true) :
    constLookup H n = some v := by
  rw [Subclass.const_eq_own]
  exact RubyCore.Proof.Judgment.constOwn_constSetIn_self hO (lt_size_of_classPayload hO)

theorem lookup_ne {cn : String} (hne : cn ≠ n) : constLookup H cn = constLookup h cn := by
  rw [Subclass.const_eq_own, Subclass.const_eq_own]
  exact constOwn_constSetIn_ne h _ _ n cn v (Or.inr hne)

theorem from_ne {k : ObjId} {cn : String} (hne : cn ≠ n) :
    constLookupFrom H k cn = constLookupFrom h k cn :=
  constLookupFrom_constSetIn_ne h _ k n cn v hne

theorem named_eq (hO : (h.classPayload? Boot.objectId).isSome = true)
    (hfresh : constLookup h n = none) (hv : NonClassVal h v) (cn : String) :
    classNamed? H cn = classNamed? h cn := by
  by_cases hc : cn = n
  · subst hc
    simp only [classNamed?, lookup_self hO, hfresh]
    cases v with
    | ref o => simp [isSome_eq, (hv o rfl).1]
    | _ => rfl
  · simp only [classNamed?, lookup_ne hc, isSome_eq]

#print axioms named_eq

theorem get_nonclass {o : ObjId} (hp : h.classPayload? o = none) : (H).get o = h.get o := by
  by_cases ho : o = Boot.objectId
  · subst ho
    unfold constSetIn; rw [hp]
  · exact get_ne ho

theorem dataPres (hc : Proof.ChainsIn h) (hb : ancestors h Boot.basicObjectId = [Boot.basicObjectId])
    (hO : (h.classPayload? Boot.objectId).isSome = true) (hfresh : constLookup h n = none)
    (hv : NonClassVal h v) : DataPres h H :=
  dataPres_of_class_growth hc hb (by rw [size]; exact Nat.le_refl _)
    (fun o _ => ⟨(fields o).1, (fields o).2.1, (fields o).2.2.1⟩)
    (fun _ _ hp => get_nonclass hp) (fun k _ => anc k)
    (fun o ho => by
      rw [isA, classOf_oob _ (by rw [size]; exact ho), anc, hb]; rfl)
    (fun cn k hk => (named_eq hO hfresh hv cn).trans hk)

/-- Machine framing across the write: frames/stack fixed, data preserved. -/
theorem framed {m n' : Machine} (hc : Proof.ChainsIn m.heap)
    (hb : ancestors m.heap Boot.basicObjectId = [Boot.basicObjectId])
    (hO : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hfresh : constLookup m.heap n = none) (hv : NonClassVal m.heap v)
    (hh : n'.heap = constSetIn m.heap Boot.objectId n v) (hs : n'.stack = m.stack)
    (hfr : n'.frames = m.frames) (hphase : n'.preludeMode = m.preludeMode)
    (hroot : RootClean m → RootClean n') : Framed m n' := by
  have hp : DataPres m.heap n'.heap := by rw [hh]; exact dataPres hc hb hO hfresh hv
  exact ⟨hs, fun k hk => by rw [hh, isSome_eq]; exact hk,
    hp.nominal, fun _ ht _ hv => hp.denM ht hv, .of_eq hs hfr,
    .of_unchanged (by rw [hh, size]; exact Nat.le_refl _)
      (fun o _ => by funext x; simp only [hh, ivarOf, (fields o).1])
      (fun _ ht _ hv => hp.denM ht hv),
    (fun o _ e' he' => by rw [hh, (fields o).2.2.1]; exact he'),
    (by rw [hh]; exact .of_nonclass (fun _ _ hp => get_nonclass hp)), hphase, hroot⟩

#print axioms framed

theorem bindEq {α : Type} (f : ClassPayload → Option α)
    (hf : ∀ cp, f { cp with consts := (n, v) :: cp.consts.filter (·.1 != n) } = f cp) (k : ObjId) :
    ((H).classPayload? k).bind f = (h.classPayload? k).bind f := by
  have hk := metaEq (n := n) (v := v) (h := h) f hf k
  cases ha : (H).classPayload? k <;> cases hb : h.classPayload? k <;> simp_all

theorem anyEq (f : ClassPayload → Bool)
    (hf : ∀ cp, f { cp with consts := (n, v) :: cp.consts.filter (·.1 != n) } = f cp) (k : ObjId) :
    ((H).classPayload? k).any f = (h.classPayload? k).any f := by
  have hk := metaEq (n := n) (v := v) (h := h) f hf k
  cases ha : (H).classPayload? k <;> cases hb : h.classPayload? k <;> simp_all

section State
variable (hO : (h.classPayload? Boot.objectId).isSome = true) (hfresh : constLookup h n = none)
  (hv : NonClassVal h v)
include hO hfresh hv

theorem isAName_eq (w : Value) (cn : String) : isAName H w cn = isAName h w cn := by
  simp only [isAName, named_eq hO hfresh hv, isA, classOf_eq, anc]

theorem isExactInst_eq (w : Value) (cn : String) : isExactInst H w cn = isExactInst h w cn := by
  simp only [isExactInst, named_eq hO hfresh hv]
  cases classNamed? h cn <;> cases w <;> simp only [size, (fields _).2.1, (fields _).2.2.1]

end State

theorem mainReady {m : Machine} (hm : MainReady m)
    (hO : (m.heap.classPayload? Boot.objectId).isSome = true) (hfresh : constLookup m.heap n = none)
    (hv : NonClassVal m.heap v) : MainReady { m with heap := constSetIn m.heap Boot.objectId n v } := by
  have hmain : Boot.mainId ≠ Boot.objectId := by decide
  refine ⟨hm.self, hm.owner, hm.cref, hm.captured, hm.phase,
    by simpa only [size] using hm.live,
    by simpa only [get_ne hmain] using hm.payload,
    by simpa only [classOf_eq, anc] using hm.chain,
    by simpa only [isAName_eq hO hfresh hv] using hm.object,
    by simpa only [isSome_eq] using hm.classLive,
    by simpa only [objectHookQuietB, definitionHookQuietB, lookup_eq] using hm.hook,
    by simpa only [bindEq (·.attached) (fun _ => rfl)] using hm.detached,
    by simpa only [(fields _).2.2.2] using hm.unfrozen, hm.origin, ?_, ?_, ?_, hm.defFrame, ?_⟩
  · have hk := metaEq (n := n) (v := v) (h := m.heap) ClassPayload.methods (fun _ => rfl)
    simpa only [mainOwnNamesB, ownMethods, classOf_eq, hk] using hm.mainNames
  · rw [show classHooksQuietB (constSetIn m.heap Boot.objectId n v) = classHooksQuietB m.heap from
      classHooksQuietB_congr (by simp only [objectCallbackPrefix, classOf_eq, anc])
        (fun name k _ => bindEq (fun cp => (cp.methods.find? (·.1 == name)).map (·.2)) (fun _ => rfl) k)]
    exact hm.classHooks
  · simpa only [objectClassFlagsB, anyEq (fun cp => cp.ancestryReady && !cp.allocatorUnavailable)
      (fun _ => rfl)] using hm.classFlags
  · rw [singletonHooksQuietB_congr (h := m.heap)
      (by simp only [singletonHookSites, classOf_eq])
      (fun k _ => anc k) (fun _ _ j _ =>
        bindEq (fun cp => (cp.methods.find? (·.1 == singletonHookName)).map (·.2)) (fun _ => rfl) j)]
    exact hm.singletonHooks

#print axioms mainReady
end Checker.Soundness.ConstAdd
