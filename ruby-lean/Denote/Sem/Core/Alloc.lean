import Denote.Sem.Core.Transport

/-!
# `Denote/Sem/Core/Alloc.lean` — the allocating step, as an `Ext`

The semantic ratchet's first three rungs were the same two `stepFn` steps
(`Denote/Rules/Lit.lean`); the fourth, `Judge.strLit`, is not, and the difference is one
line of `RubyCore/Interp.lean`:

```
| .str s =>
  -- string literals allocate a fresh unfrozen String [V]
  let (v, m) := Builtins.allocStr m s
  .next (withCtl m (.value v))
```

So a string literal's post-machine is its pre-machine **with one object pushed**, and every
`StateOk` component has to be re-established there rather than transported for free. That
work is done: `Denote/Ty/Grow.lean`'s `denM_ext` and `Denote/Sem/Core/State.lean`'s `StateOk_ext`
transport across any `Ext`. What is left, and what this file is, is the *producer*: the proof
that `Builtins.allocStr`'s push **is** an `Ext`.

Two of the six clauses are the ones with content, and both are about ids the old heap did not
have:

* `payload` has to hold at the fresh id too. It does, in opposite ways on the two sides: the
  old heap answers `none` because nothing is there (`Heap.get` past the end is `default`,
  whose payload is `.none`), and the new heap answers `none` because a String is not a class.
  This is `RubyCore.Proof.plainGrow_alloc`'s argument, and the reason `Ext` demands a
  *non-class* allocation without saying so in a clause.
* `freshBasic` is where `CoreOk` is spent, and it is the clause that exists because
  `Heap.get` is total. At the old heap the value `.ref n` (for `n` the fresh id) is a dangling
  reference reading as `default`, whose `klass` is `0` — `Boot.basicObjectId`. So a local
  typed `.cls "BasicObject"` holding a dangling reference is, at that heap, correctly typed;
  after the push the same value is a `String`, and the type has to stay true. It does, because
  a `String` is a `BasicObject`, and that is exactly `CoreOk.stringBasic`. `CoreOk.basicSelf`
  is what reduces "any class the dangling read was an instance of" to that single case.

`sat` (the `Saturated` component of `StateOk`) is spent here too, on the `ancestors` clause:
the walk is fuel-bounded by `h.objs.size + 1`, so the push moves the fuel, and
`RubyCore.Proof.ancestors_congr_grow` is what says the walk is nevertheless unmoved.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## Pushing one object -/

/-- The heap with one object appended — `Heap.alloc`'s second component, named. -/
def pushHeap (h : Heap) (obj : Object) : Heap := ⟨h.objs.push obj⟩

@[simp] theorem pushHeap_size (h : Heap) (obj : Object) :
    (pushHeap h obj).objs.size = h.objs.size + 1 := by simp [pushHeap]

theorem pushHeap_get_lt (h : Heap) (obj : Object) {o : ObjId} (ho : o < h.objs.size) :
    (pushHeap h obj).get o = h.get o := by
  simp only [pushHeap, Heap.get, Array.getD_eq_getD_getElem?, Array.getElem?_push,
    if_neg (Nat.ne_of_lt ho)]

theorem pushHeap_get_self (h : Heap) (obj : Object) :
    (pushHeap h obj).get h.objs.size = obj := by
  simp [pushHeap, Heap.get, Array.getD_eq_getD_getElem?]

theorem pushHeap_get_gt (h : Heap) (obj : Object) {o : ObjId} (ho : h.objs.size < o) :
    (pushHeap h obj).get o = default :=
  get_oob _ (by simp only [pushHeap_size]; omega)

/-- **The class table is unmoved by a non-class allocation**, at every id including the fresh
one. -/
theorem pushHeap_classPayload (h : Heap) (obj : Object) (hnc : ∀ c, obj.payload ≠ .cls c)
    (k : ObjId) : (pushHeap h obj).classPayload? k = h.classPayload? k := by
  rcases Nat.lt_trichotomy k h.objs.size with hk | hk | hk
  · simp only [Heap.classPayload?, pushHeap_get_lt h obj hk]
  · subst hk
    simp only [Heap.classPayload?, pushHeap_get_self, get_oob h (Nat.le_refl _)]
    cases hp : obj.payload with
    | cls c => exact absurd hp (hnc c)
    | _ => rfl
  · simp only [Heap.classPayload?, pushHeap_get_gt h obj hk, get_oob h (Nat.le_of_lt hk)]

theorem stringPayloadOk_push {h : Heap} {obj : Object} (hp : StringPayloadOk h)
    (ho : obj.eigen.getD obj.klass = Boot.stringId → ∃ s, obj.payload = .str s) :
    StringPayloadOk (pushHeap h obj) := by
  intro o hc
  rcases Nat.lt_trichotomy o h.objs.size with hl | he | hg
  · rw [show classOf (pushHeap h obj) (.ref o) = classOf h (.ref o) by
      simp only [classOf, pushHeap_get_lt h obj hl]] at hc
    simpa only [pushHeap_get_lt h obj hl] using hp o hc
  · subst he
    rw [classOf, pushHeap_get_self] at hc
    rw [pushHeap_get_self]
    apply ho
    cases heigen : obj.eigen <;> simpa [heigen] using hc
  · simp only [classOf, pushHeap_get_gt h obj hg] at hc
    cases hc

theorem arrayPayloadOk_push {h : Heap} {obj : Object} (hp : ArrayPayloadOk h)
    (ho : ∀ xs, obj.payload = .arr xs → obj.eigen.getD obj.klass = Boot.arrayId) :
    ArrayPayloadOk (pushHeap h obj) := by
  intro o xs hx
  rcases Nat.lt_trichotomy o h.objs.size with hl | he | hg
  · simp only [pushHeap_get_lt h obj hl] at hx
    simpa only [classOf, pushHeap_get_lt h obj hl] using hp o xs hx
  · subst he
    rw [pushHeap_get_self] at hx
    have hc := ho xs hx
    simp only [classOf, pushHeap_get_self]
    cases heigen : obj.eigen <;> simpa [heigen] using hc
  · rw [pushHeap_get_gt h obj hg] at hx
    cases hx

theorem hashPayloadOk_push {h : Heap} {obj : Object} (hp : HashPayloadOk h)
    (ho : ∀ xs, obj.payload = .hsh xs →
      obj.eigen.getD obj.klass = Boot.hashId ∧ hashDefaultNilB obj.hashDflt = true) :
    HashPayloadOk (pushHeap h obj) := by
  intro o xs hx
  rcases Nat.lt_trichotomy o h.objs.size with hl | he | hg
  · simp only [pushHeap_get_lt h obj hl] at hx
    simpa only [classOf, pushHeap_get_lt h obj hl] using hp o xs hx
  · subst he
    rw [pushHeap_get_self] at hx
    obtain ⟨hc, hd⟩ := ho xs hx
    simp only [classOf, pushHeap_get_self]
    refine ⟨?_, hd⟩
    cases heigen : obj.eigen <;> simpa [heigen] using hc
  · rw [pushHeap_get_gt h obj hg] at hx
    cases hx

/-! ## The producer -/

/-- **A non-class, ivar-less allocation of a `BasicObject` descendant is an `Ext`.**

The three hypotheses are the three things `Ext`'s fresh-id clauses ask of the pushed object,
and each is `rfl`-shaped at a literal: it is not a class, it has no instance variables, and
its class is a descendant of `BasicObject`. The two hypotheses on the *heap* — `Saturated`
and `CoreOk.basicSelf` — are the `StateOk` components a rung spends here. -/
theorem ext_push {m : Machine} (obj : Object)
    (hsat : Proof.Saturated m.heap)
    (hbasic : ancestors m.heap Boot.basicObjectId = [Boot.basicObjectId])
    (hnc : ∀ c, obj.payload ≠ .cls c)
    (hiv : obj.ivars = [])
    (heig : obj.eigen = none)
    (hklass : (ancestors m.heap obj.klass).contains Boot.basicObjectId = true) :
    Ext m { m with heap := pushHeap m.heap obj } := by
  have hpay : ∀ k, (pushHeap m.heap obj).classPayload? k = m.heap.classPayload? k :=
    pushHeap_classPayload m.heap obj hnc
  have hshape : Proof.ShapeAgree m.heap (pushHeap m.heap obj) := fun k => by rw [hpay k]
  have hsize : m.heap.objs.size ≤ (pushHeap m.heap obj).objs.size := by simp
  have hanc : ∀ k, ancestors (pushHeap m.heap obj) k = ancestors m.heap k :=
    Proof.ancestors_congr_grow hshape hsize hsat
  refine ⟨rfl, rfl, hsize, ?_, hpay, hanc, ?_, ?_, ?_⟩
  · intro o ho; exact pushHeap_get_lt m.heap obj ho
  · intro o ho
    rcases Nat.eq_or_lt_of_le ho with he | he
    · rw [← he, pushHeap_get_self]; exact hiv
    · rw [pushHeap_get_gt m.heap obj he]; rfl
  · intro o ho k hk
    -- `hbasic` collapses the hypothesis: the only class a dangling reference is an instance
    -- of is `BasicObject` itself.
    have hk0 : k = Boot.basicObjectId := by
      rw [hbasic] at hk; simpa using hk
    subst hk0
    rcases Nat.eq_or_lt_of_le ho with he | he
    · show (ancestors (pushHeap m.heap obj) _).contains _ = true
      rw [← he]
      simp only [classOf, pushHeap_get_self, heig, hanc]
      exact hklass
    · show (ancestors (pushHeap m.heap obj) _).contains _ = true
      rw [classOf_oob (pushHeap m.heap obj) (by simp only [pushHeap_size]; omega), hanc,
        hbasic]
      rfl

  · intro hch
    have hkl : obj.klass < m.heap.objs.size := by
      by_cases hout : obj.klass < m.heap.objs.size
      · exact hout
      apply False.elim
      have hp := Proof.classPayload?_oob m.heap obj.klass hout
      have ha : ancestors m.heap obj.klass = [obj.klass] := by
        simp [ancestors, ancestors.go, hp]
      have he : Boot.basicObjectId = obj.klass := by simpa only [ha, List.contains_cons,
        List.contains_nil, Bool.or_false, beq_iff_eq] using hklass
      have hb : Boot.basicObjectId < m.heap.objs.size :=
        Nat.lt_of_le_of_lt (by decide : Boot.basicObjectId ≤ Boot.objectId) hch.boot.2.2.2.2
      exact hout (he ▸ hb)
    exact Proof.chainsIn_push hch hkl heig (fun cp hp => False.elim (hnc cp hp))

#print axioms ext_push

end Ratchet.Denote
