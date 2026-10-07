import Books.TypeSoundness.Conformance.Names.OwnNames
import Books.Metatheory.Heap.HeapFacts

/-! Fresh top-level classes dispatch const_added and inherited on Object before
body entry. Their first own entries must be native no-ops above Object. -/
set_option autoImplicit false
namespace Checker.Soundness
open RubyCore

def classHookNames : List (String × String) :=
  [("const_added", "Module#const_added"), ("inherited", "Class#inherited")]

def objectCallbackPrefix (h : Heap) : List ObjId :=
  (ancestors h (classOf h (.ref Boot.objectId))).takeWhile (· != Boot.objectId)

def firstOwnMethod (h : Heap) (chain : List ObjId) (name : String) : Option MethodDef :=
  chain.findSome? fun k => (h.classPayload? k).bind fun cp =>
    (cp.methods.find? (·.1 == name)).map (·.2)

def classHooksQuietB (h : Heap) : Bool :=
  classHookNames.all fun (name, bid) =>
    (firstOwnMethod h (objectCallbackPrefix h) name).any fun md =>
      !md.undefined && !md.visibilityOnly && md.builtin == some bid

/-- Keep writes outside the callback prefix, or preserve both callback selectors. -/
def ClassHookWriteOk (h : Heap) (cls : ObjId) (name : String) : Prop :=
  cls ∉ objectCallbackPrefix h ∨ name ∉ classHookNames.map (·.1)

theorem ClassHookWriteOk.object (h : Heap) (name : String) :
    ClassHookWriteOk h Boot.objectId name := by
  apply Or.inl
  suffices ∀ xs : List ObjId, Boot.objectId ∉ xs.takeWhile (· != Boot.objectId) from
    this _
  intro xs
  induction xs with
  | nil => simp
  | cons k xs ih =>
    by_cases he : k = Boot.objectId
    · subst k; simp [List.takeWhile]
    · simp only [List.takeWhile, bne_iff_ne.mpr he, List.mem_cons, not_or]
      exact ⟨Ne.symm he, ih⟩

theorem firstOwnMethod_congr {h h' : Heap} {chain : List ObjId} {name : String}
    (hf : ∀ k ∈ chain, (h'.classPayload? k).bind
      (fun cp => (cp.methods.find? (·.1 == name)).map (·.2)) =
      (h.classPayload? k).bind (fun cp => (cp.methods.find? (·.1 == name)).map (·.2))) :
    firstOwnMethod h' chain name = firstOwnMethod h chain name := by
  induction chain with
  | nil => rfl
  | cons k rest ih =>
    have ht := ih (fun j hj => hf j (by simp [hj]))
    simp only [firstOwnMethod, List.findSome?_cons] at ht ⊢
    rw [hf k (by simp), ht]

theorem classHooksQuietB_congr {h h' : Heap}
    (hp : objectCallbackPrefix h' = objectCallbackPrefix h)
    (hf : ∀ name k, k ∈ objectCallbackPrefix h →
      (h'.classPayload? k).bind (fun cp => (cp.methods.find? (·.1 == name)).map (·.2)) =
      (h.classPayload? k).bind (fun cp => (cp.methods.find? (·.1 == name)).map (·.2))) :
    classHooksQuietB h' = classHooksQuietB h := by
  have he (name : String) := firstOwnMethod_congr (hf name)
  simp only [classHooksQuietB, hp, he]

theorem classHooksQuietB_defineMethod {h : Heap} {cls : ObjId} {name : String}
    {md : MethodDef} (hw : ClassHookWriteOk h cls name) :
    classHooksQuietB (defineMethod h cls name md) = classHooksQuietB h := by
  have hp : objectCallbackPrefix (defineMethod h cls name md) = objectCallbackPrefix h := by
    simp only [objectCallbackPrefix, Proof.classOf_defineMethod, Proof.ancestors_defineMethod]
  unfold classHooksQuietB
  rw [hp]
  have he (p : String × String) (hm : p ∈ classHookNames) : firstOwnMethod (defineMethod h cls name md) (objectCallbackPrefix h) p.1 =
      firstOwnMethod h (objectCallbackPrefix h) p.1 := by
    apply firstOwnMethod_congr
    intro k hk
    rcases hw with hcls | hn
    · have hne : k ≠ cls := by intro he; exact hcls (he ▸ hk)
      unfold defineMethod
      split
      · simp only [Heap.setClassPayload, Heap.classPayload?, Heap.get, Heap.set]
        rw [Proof.objs_getD_set!_ne _ _ _ _ hne]
      · rfl
    · have hne : p.1 ≠ name := by
        intro he
        exact hn (he ▸ List.mem_map.mpr ⟨p, hm, rfl⟩)
      have row (g : Heap) :
          (g.classPayload? k).bind (fun cp => (cp.methods.find? (·.1 == p.1)).map (·.2)) =
          ((g.classPayload? k).map (fun cp => (cp.methods.find? (·.1 == p.1), cp.isModule))).bind
            (fun pair => pair.1.map (·.2)) := by
        cases g.classPayload? k <;> rfl
      rw [row, row, Proof.lookupFields_defineMethod _ _ _ _ _ _ hne]
  simp only [classHookNames, List.all_cons, List.all_nil]
  rw [he ("const_added", "Module#const_added") (by simp [classHookNames]),
    he ("inherited", "Class#inherited") (by simp [classHookNames])]

/-- A non-forwarding first own entry resolves under the interpreter's fuel.
Earlier empty tables consume fuel, including classes without payloads. -/
theorem firstOwnMethod_lookup_go {h : Heap} {chain rest : List ObjId}
    {name : String} {md : MethodDef} {fuel : Nat}
    (hf : firstOwnMethod h chain name = some md) (hv : md.visibilityOnly = false)
    (hlen : chain.length ≤ fuel) :
    ∃ owner, lookupInChain.go h name fuel (chain ++ rest) false = some (owner, md) := by
  induction chain generalizing fuel with
  | nil => simp [firstOwnMethod] at hf
  | cons k chain ih =>
    cases fuel with
    | zero => simp at hlen
    | succ fuel =>
      have ht : chain.length ≤ fuel := by simpa using hlen
      cases hc : h.classPayload? k with
      | none =>
        have htail : firstOwnMethod h chain name = some md := by
          simpa [firstOwnMethod, List.findSome?_cons, hc] using hf
        simpa only [List.cons_append, lookupInChain.go, hc] using ih htail ht
      | some cp =>
        cases he : cp.methods.find? (·.1 == name) with
        | none =>
          have htail : firstOwnMethod h chain name = some md := by
            simpa [firstOwnMethod, List.findSome?_cons, hc, he] using hf
          simpa only [List.cons_append, lookupInChain.go, hc, he] using ih htail ht
        | some p =>
          have hm : p.2 = md := by
            simpa [firstOwnMethod, List.findSome?_cons, hc, he] using hf
          refine ⟨k, ?_⟩
          simp only [List.cons_append, lookupInChain.go, hc, he, hm, hv,
            Bool.not_false, ↓reduceIte]

theorem classHooksQuietB_lookup {h : Heap} (hq : classHooksQuietB h = true)
    (hc : Proof.ChainsIn h) {name bid : String} (hn : (name, bid) ∈ classHookNames) :
    ∃ owner md, lookup h (.ref Boot.objectId) name = some (owner, md) ∧
      md.undefined = false ∧ md.builtin = some bid := by
  have hh := List.all_eq_true.mp hq (name, bid) hn
  cases hf : firstOwnMethod h (objectCallbackPrefix h) name with
  | none => simp only [hf, Option.any] at hh; cases hh
  | some md =>
    simp only [hf, Option.any, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hh
    have hlen := congrArg List.length (List.takeWhile_append_dropWhile
      (l := ancestors h (classOf h (.ref Boot.objectId))) (p := (· != Boot.objectId)))
    simp only [List.length_append] at hlen
    have hb := Proof.ancestors_length_bound hc (classOf h (.ref Boot.objectId))
    obtain ⟨owner, he⟩ := firstOwnMethod_lookup_go
      (rest := (ancestors h (classOf h (.ref Boot.objectId))).dropWhile (· != Boot.objectId))
      (fuel := 2 * h.objs.size + 2) hf hh.1.2 (by unfold objectCallbackPrefix; omega)
    refine ⟨owner, md, ?_, hh.1.1, hh.2⟩
    simpa only [lookup, lookupInChain, objectCallbackPrefix, List.takeWhile_append_dropWhile] using he

#print axioms firstOwnMethod_lookup_go
#print axioms classHooksQuietB_lookup
#print axioms ClassHookWriteOk.object
#print axioms classHooksQuietB_defineMethod
end Checker.Soundness
