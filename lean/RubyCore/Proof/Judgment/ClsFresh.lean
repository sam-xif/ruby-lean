import RubyCore.Proof.Judgment.ModFresh

/-!
# J53 — the fresh-class composite (`classM`'s allocating branch)

`ModFresh`'s sibling at `isModule = false`. `enterClassBody`'s miss path for a
`class name` (no explicit superclass) performs the same four writes as the
module's — allocate the class object (`k := h₀.size`), register it as a
constant of the definee, allocate its eigenclass (`e := h₀.size + 1`), set the
class's `eigen` field — with two differences that this file is entirely about:

* the class object's payload carries `superclass := some Boot.objectId`, so the
  fresh chain is **not** a singleton: `ancestors k = k :: ancestors h₀ Object`;
* the eigenclass superclasses **`Object`'s own eigenclass** `eO` (realized at
  boot since J53's groundwork), so `eigenclassOf` is a pure read up the chain —
  no extra allocation — and `ancestors e = e :: ancestors h₀ eO`.

Everything `hmid`-level (the `constSetIn` suite) and everything `ClsGrow`-generic
is reused from `ModFresh` verbatim; the fresh-id facts are re-proved at the class
literals. `ModOffChains` at the fresh class is **false** (it sits on its own
chain before `Object`) and deliberately absent: the `classM` frame clause
(`inFreshClass`) does not carry it, and the fresh class is never a `ModOwner`
witness (`isModule = false`), which is what keeps every `ModuleNameOk`/
`ClassNameOk` transport witness-old.
-/

namespace RubyCore
namespace Proof
namespace Judgment

open Interp
open RubyCore.Types
open RubyCore.Judgment
open RubyCore.Proof.Static

set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

/-- The class object the fresh path allocates. -/
@[reducible] def clsObj (q : String) : Object :=
  { klass := Boot.classId,
    payload := .cls { superclass := some Boot.objectId, name := q, isModule := false } }

/-- Its eigenclass: superclasses `Object`'s own eigenclass `eO`, so inherited
    class methods resolve. -/
@[reducible] def eigObjC (q : String) (eO : ObjId) : Object :=
  { klass := Boot.classId,
    payload := .cls { superclass := some eO,
                      name := "#<Class:" ++ q ++ ">", isModule := false } }

/-- The class object once its eigenclass is realized. -/
@[reducible] def clsObjE (q : String) (e : ObjId) : Object :=
  { clsObj q with eigen := some e }

/-! ## The composite, factored over `hmid` -/

/-- The composite heap: two pushes and a fresh-id `set!` over `hmid`, exactly
    `freshModHeap`'s spelling at the class literals. -/
def freshClsHeap (h₀ : Heap) (d : ObjId) (name q : String) (eO : ObjId) : Heap :=
  ⟨(((hmidOf h₀ d name).objs.push (clsObj q)).push (eigObjC q eO)).set!
      h₀.objs.size (clsObjE q (h₀.objs.size + 1))⟩

/-- **The factoring**: the machine's alloc → register → alloc → eigen-set order
    equals the factored composite. -/
theorem freshClsHeap_machine (h₀ : Heap) (d : ObjId) (name q : String) (eO : ObjId)
    (hdlt : d < h₀.objs.size) :
    ((constSetIn (h₀.alloc (clsObj q)).2 d name (.ref h₀.objs.size)).alloc
        (eigObjC q eO)).2.set h₀.objs.size
      { ((constSetIn (h₀.alloc (clsObj q)).2 d name (.ref h₀.objs.size)).alloc
          (eigObjC q eO)).2.get h₀.objs.size with
        eigen := some (constSetIn (h₀.alloc (clsObj q)).2 d name
          (.ref h₀.objs.size)).objs.size } =
      freshClsHeap h₀ d name q eO := by
  rw [constSetIn_alloc_comm _ _ _ _ _ hdlt]
  show (((hmidOf h₀ d name).alloc (clsObj q)).2.alloc (eigObjC q eO)).2.set h₀.objs.size
      { (((hmidOf h₀ d name).alloc (clsObj q)).2.alloc (eigObjC q eO)).2.get h₀.objs.size with
        eigen := some ((hmidOf h₀ d name).alloc (clsObj q)).2.objs.size } =
    freshClsHeap h₀ d name q eO
  have hsz2 : ((hmidOf h₀ d name).alloc (clsObj q)).2.objs.size
      = h₀.objs.size + 1 := by
    show ((hmidOf h₀ d name).objs.push (clsObj q)).size = _
    rw [Array.size_push, hmid_size]
  have hgetk : (((hmidOf h₀ d name).alloc (clsObj q)).2.alloc (eigObjC q eO)).2.get
      h₀.objs.size = clsObj q := by
    show (((hmidOf h₀ d name).objs.push (clsObj q)).push (eigObjC q eO)).getD
        h₀.objs.size default = clsObj q
    rw [objs_getD_push_lt _ _ h₀.objs.size (by rw [Array.size_push, hmid_size]; omega),
      show h₀.objs.size = (hmidOf h₀ d name).objs.size from (hmid_size h₀ d name).symm,
      objs_getD_push_self]
  rw [hgetk, hsz2]
  rfl

/-! ## The step, reduced -/

/-- The successor machine (the frame is `freshModFrame`, payload-independent). -/
def freshClsMachine (m : Machine) (d : ObjId) (cref₀ : List ObjId)
    (name q : String) (eO : ObjId) (body : Expr) : Machine :=
  { m with
    heap := freshClsHeap m.heap d name q eO,
    frames := m.frames.push (freshModFrame m.heap.objs.size cref₀),
    stack := m.frames.size :: m.stack,
    kont := .frameK m.frames.size :: m.kont,
    ctl := .eval body }

theorem h2C_get_k {m : Machine} {name q : String}
    (hdlt : m.currentFrame.defmod < m.heap.objs.size) :
    (constSetIn (m.heap.alloc (clsObj q)).2 m.currentFrame.defmod name
      (.ref m.heap.objs.size)).get m.heap.objs.size = clsObj q := by
  rw [get_constSetIn_ne _ _ _ _ _ (fun hEq => absurd hEq.symm (Nat.ne_of_lt hdlt))]
  show (m.heap.objs.push (clsObj q)).getD m.heap.objs.size default = clsObj q
  exact objs_getD_push_self _ _

/-- `eigenclassOf.go` at an already-realized eigenclass is a pure read. -/
theorem eigenclassOf_go_some {m : Machine} {o e : ObjId} {f : Nat}
    (he : (m.heap.get o).eigen = some e) :
    eigenclassOf.go m o (f + 1) = (e, m) := by
  unfold eigenclassOf.go
  rw [he]

/-- `eigenclassOf` at the just-allocated class: the eigen is `none`, the
    superclass is `Object`, whose eigenclass is realized (`heO`) — so the
    metaclass parent is a pure read and one eigenclass is allocated and
    attached. -/
theorem eigenclassOf_clsObj {mm : Machine} {o eO : ObjId} {q : String}
    (hget : mm.heap.get o = clsObj q)
    (hany : anyToS mm.heap o = q)
    (heO : (mm.heap.get Boot.objectId).eigen = some eO)
    (hpos : 0 < mm.heap.objs.size) :
    eigenclassOf mm o =
      (mm.heap.objs.size,
       { mm with heap := (attachEigen (mm.heap.alloc (eigObjC q eO)).2 o
          mm.heap.objs.size) }) := by
  obtain ⟨n, hn⟩ : ∃ n, mm.heap.objs.size = n + 1 :=
    ⟨mm.heap.objs.size - 1, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  show eigenclassOf.go mm o (mm.heap.objs.size + 1) = _
  rw [hn]
  unfold eigenclassOf.go
  rw [hget]
  simp only [clsObj]
  rw [show eigenclassOf.go mm Boot.objectId (n + 1) = (eO, mm) from
    eigenclassOf_go_some heO]
  simp only [eigObjC, hany, attachEigen]
  rw [← hn]
  rfl

set_option maxHeartbeats 4000000 in
/-- The fresh path of `evalExpr` on a superclass-free `class'`, reduced to the
    explicit machine (J53). `heO0` is the boot groundwork: `Object`'s eigenclass
    is realized, so the metaclass walk reads it instead of allocating. -/
theorem evalExpr_class_fresh {m : Machine} {name q : String} {eO : ObjId} {body : Expr}
    (hmiss : constOwn m.heap m.currentFrame.defmod name = none)
    (hdlt : m.currentFrame.defmod < m.heap.objs.size)
    (hobj : Boot.objectId < m.heap.objs.size)
    (heO0 : (m.heap.get Boot.objectId).eigen = some eO)
    (hq : (if m.currentFrame.defmod == Boot.objectId then name
           else className m.heap m.currentFrame.defmod ++ "::" ++ name) = q)
    (hqne : ¬ q.isEmpty = true) :
    evalExpr m (.class' name none body) =
      .next (freshClsMachine m m.currentFrame.defmod m.currentFrame.cref
        name q eO body) := by
  have hqq : (if m.currentFrame.defmod == Boot.objectId then name
      else s!"{className m.heap m.currentFrame.defmod}::{name}") = q := by
    rw [← hq]
    split <;> rfl
  have hg2k := h2C_get_k (m := m) (name := name) (q := q) hdlt
  have hcls2 : className (constSetIn (m.heap.alloc (clsObj q)).2
      m.currentFrame.defmod name (.ref m.heap.objs.size)) m.heap.objs.size = q := by
    unfold className Heap.classPayload?
    rw [hg2k]
    show (if q.isEmpty then _ else q) = q
    rw [if_neg hqne]
  have hany : anyToS (constSetIn (m.heap.alloc (clsObj q)).2
      m.currentFrame.defmod name (.ref m.heap.objs.size)) m.heap.objs.size = q := by
    unfold anyToS Heap.classPayload?
    rw [hg2k]
    exact hcls2
  have hsz2 : (constSetIn (m.heap.alloc (clsObj q)).2 m.currentFrame.defmod name
      (.ref m.heap.objs.size)).objs.size = m.heap.objs.size + 1 := by
    rw [objs_size_constSetIn]
    simp [Heap.alloc]
  -- `Object`'s eigen at the mid heap: the write and the push both pin it
  have heO2 : ((constSetIn (m.heap.alloc (clsObj q)).2 m.currentFrame.defmod name
      (.ref m.heap.objs.size)).get Boot.objectId).eigen = some eO := by
    rw [(get_constSetIn_fields (m.heap.alloc (clsObj q)).2 m.currentFrame.defmod
      name (.ref m.heap.objs.size) Boot.objectId).2.2.1]
    show ((m.heap.objs.push (clsObj q)).getD Boot.objectId default).eigen = some eO
    rw [objs_getD_push_lt _ _ _ hobj]
    exact heO0
  have hpos2 : 0 < (constSetIn (m.heap.alloc (clsObj q)).2 m.currentFrame.defmod name
      (.ref m.heap.objs.size)).objs.size := by
    rw [hsz2]
    exact Nat.succ_pos _
  simp only [evalExpr, enterClassBody, hmiss, hqq, if_true, Bool.false_eq_true,
    if_false, Option.getD_none]
  simp only [show ∀ ob : Object, (m.heap.alloc ob).1 = m.heap.objs.size from fun _ => rfl]
  simp only [clsObj, eigObjC] at hg2k hany heO2 ⊢
  rw [eigenclassOf_clsObj
    (mm := { m with heap := (constSetIn (m.heap.alloc (clsObj q)).2
      m.currentFrame.defmod name (.ref m.heap.objs.size)) }) hg2k hany heO2 hpos2]
  show StepResult.next (withKont
      { m with
        heap := (attachEigen ((constSetIn (m.heap.alloc (clsObj q)).2
            m.currentFrame.defmod name (.ref m.heap.objs.size)).alloc (eigObjC q eO)).2
          m.heap.objs.size
          (constSetIn (m.heap.alloc (clsObj q)).2 m.currentFrame.defmod name
            (.ref m.heap.objs.size)).objs.size),
        frames := m.frames.push (freshModFrame m.heap.objs.size m.currentFrame.cref),
        stack := m.frames.size :: m.stack }
      (.eval body) (.frameK m.frames.size)) =
    StepResult.next (freshClsMachine m m.currentFrame.defmod m.currentFrame.cref
      name q eO body)
  rw [show (attachEigen ((constSetIn (m.heap.alloc (clsObj q)).2
      m.currentFrame.defmod name (.ref m.heap.objs.size)).alloc (eigObjC q eO)).2
      m.heap.objs.size
      (constSetIn (m.heap.alloc (clsObj q)).2 m.currentFrame.defmod name
        (.ref m.heap.objs.size)).objs.size)
      = freshClsHeap m.heap m.currentFrame.defmod name q eO
    from freshClsHeap_machine m.heap m.currentFrame.defmod name q eO hdlt]
  rfl

/-! ## Reading the composite -/

section Reads

variable {h₀ : Heap} {d : ObjId} {name q : String} {eO : ObjId}

theorem freshClsHeap_size :
    (freshClsHeap h₀ d name q eO).objs.size = h₀.objs.size + 2 := by
  show ((((hmidOf h₀ d name).objs.push (clsObj q)).push (eigObjC q eO)).set! _ _).size = _
  simp [Array.set!, Array.size_setIfInBounds, Array.size_push, hmid_size,
    show ((hmidOf h₀ d name).objs.size = h₀.objs.size) from hmid_size h₀ d name]

theorem freshClsHeap_get_old {o : ObjId} (ho : o < h₀.objs.size) :
    (freshClsHeap h₀ d name q eO).get o = (hmidOf h₀ d name).get o := by
  show ((((hmidOf h₀ d name).objs.push (clsObj q)).push (eigObjC q eO)).set!
      h₀.objs.size _).getD o default = (hmidOf h₀ d name).objs.getD o default
  rw [objs_getD_set!_ne _ _ _ _ (Nat.ne_of_lt ho),
    objs_getD_push_lt _ _ o (by rw [Array.size_push, hmid_size]; exact Nat.lt_succ_of_lt ho),
    objs_getD_push_lt _ _ o (by rw [hmid_size]; exact ho)]

theorem freshClsHeap_get_k :
    (freshClsHeap h₀ d name q eO).get h₀.objs.size = clsObjE q (h₀.objs.size + 1) := by
  show ((((hmidOf h₀ d name).objs.push (clsObj q)).push (eigObjC q eO)).set!
      h₀.objs.size _).getD h₀.objs.size default = _
  rw [objs_getD_set!_self _ _ _
    (by rw [Array.size_push, Array.size_push, hmid_size]; omega)]

theorem freshClsHeap_get_e :
    (freshClsHeap h₀ d name q eO).get (h₀.objs.size + 1) = eigObjC q eO := by
  show ((((hmidOf h₀ d name).objs.push (clsObj q)).push (eigObjC q eO)).set!
      h₀.objs.size _).getD (h₀.objs.size + 1) default = _
  rw [objs_getD_set!_ne _ _ _ _ (by omega),
    show h₀.objs.size + 1 = ((hmidOf h₀ d name).objs.push (clsObj q)).size by
      rw [Array.size_push, hmid_size],
    objs_getD_push_self]

/-- The J43 relation, delivered: old ids read as in `hmid`. -/
theorem clsGrow_hmid_freshC : ClsGrow (hmidOf h₀ d name) (freshClsHeap h₀ d name q eO) :=
  ⟨by rw [freshClsHeap_size, hmid_size]; omega,
   fun o ho => freshClsHeap_get_old (by rwa [hmid_size h₀ d name] at ho)⟩

theorem freshClsHeap_cp_k :
    (freshClsHeap h₀ d name q eO).classPayload? h₀.objs.size =
      some { superclass := some Boot.objectId, name := q, isModule := false } := by
  unfold Heap.classPayload?
  rw [freshClsHeap_get_k]

theorem freshClsHeap_cp_e :
    (freshClsHeap h₀ d name q eO).classPayload? (h₀.objs.size + 1) =
      some { superclass := some eO,
             name := "#<Class:" ++ q ++ ">", isModule := false } := by
  unfold Heap.classPayload?
  rw [freshClsHeap_get_e]

theorem freshClsHeap_cp_oob {o : ObjId} (ho : h₀.objs.size + 2 ≤ o) :
    (freshClsHeap h₀ d name q eO).classPayload? o = none := by
  apply classPayload?_oob
  rw [freshClsHeap_size]
  exact Nat.not_lt.mpr ho

end Reads

/-! ## Chains at the composite -/

section Chains

variable {h₀ : Heap} {d : ObjId} {name q : String} {eO : ObjId}

theorem freshClsHeap_modanc_go_k (f : Nat) :
    modAncestors.go (freshClsHeap h₀ d name q eO) h₀.objs.size (f + 1)
      = [h₀.objs.size] := by
  rw [modAncestors.go.eq_def]
  rw [freshClsHeap_cp_k]
  simp

theorem freshClsHeap_modanc_go_e (f : Nat) :
    modAncestors.go (freshClsHeap h₀ d name q eO) (h₀.objs.size + 1) (f + 1)
      = [h₀.objs.size + 1] := by
  rw [modAncestors.go.eq_def]
  rw [freshClsHeap_cp_e]
  simp

theorem freshClsHeap_anc_go_k (f : Nat) :
    ancestors.go (freshClsHeap h₀ d name q eO) h₀.objs.size (f + 1)
      = h₀.objs.size ::
        ancestors.go (freshClsHeap h₀ d name q eO) Boot.objectId f := by
  rw [ancestors.go.eq_def]
  rw [freshClsHeap_cp_k]
  simp

theorem freshClsHeap_anc_go_e (f : Nat) :
    ancestors.go (freshClsHeap h₀ d name q eO) (h₀.objs.size + 1) (f + 1)
      = (h₀.objs.size + 1) ::
        ancestors.go (freshClsHeap h₀ d name q eO) eO f := by
  rw [ancestors.go.eq_def]
  rw [freshClsHeap_cp_e]
  simp

/-- `Saturated` at the composite: old walks are `hmid`'s (fuel-lifted); both
    fresh chains step once into an *old* id, so both branches are the module
    version's eigenclass argument. `heOlt` bounds the eigen parent. -/
theorem saturated_freshC (hch : ChainsIn h₀) (hsat : Saturated h₀)
    (hdlt : d < h₀.objs.size) (heOlt : eO < h₀.objs.size) :
    Saturated (freshClsHeap h₀ d name q eO) := by
  have hchm : ChainsIn (hmidOf h₀ d name) := chainsIn_hmid hch
  have hsm : Saturated (hmidOf h₀ d name) := saturated_hmid hsat
  have hg : ClsGrow (hmidOf h₀ d name) (freshClsHeap h₀ d name q eO) :=
    clsGrow_hmid_freshC
  have hszH : (freshClsHeap h₀ d name q eO).objs.size = h₀.objs.size + 2 :=
    freshClsHeap_size
  have hszm : (hmidOf h₀ d name).objs.size = h₀.objs.size :=
    hmid_size h₀ d name
  have hb1 : (hmidOf h₀ d name).objs.size + 1 ≤ h₀.objs.size + 2 + 1 := by
    rw [hszm]; exact Nat.add_le_add_left (show (1:Nat) ≤ 3 by decide) _
  have hb2 : (hmidOf h₀ d name).objs.size + 1 ≤ h₀.objs.size + 2 := by
    rw [hszm]; exact Nat.add_le_add_left (show (1:Nat) ≤ 2 by decide) _
  have hb3 : (hmidOf h₀ d name).objs.size + 1 ≤ h₀.objs.size + 1 := by
    rw [hszm]; exact Nat.le_refl _
  constructor
  · intro mo
    rw [hszH]
    by_cases hmo : mo < h₀.objs.size
    · have hold : ∀ f, modAncestors.go (freshClsHeap h₀ d name q eO) mo f
          = modAncestors.go (hmidOf h₀ d name) mo f :=
        fun f => ClsGrow.modAncestors_go_old hg hchm f mo (hszm ▸ hmo)
      have hL := (hold _).trans (modAncestors_go_ge hsm.1 hb1 mo)
      have hR := (hold _).trans (modAncestors_go_ge hsm.1 hb2 mo)
      exact hL.trans hR.symm
    · by_cases hk : mo = h₀.objs.size
      · subst hk
        exact (freshClsHeap_modanc_go_k (h₀.objs.size + 2)).trans
          (freshClsHeap_modanc_go_k (h₀.objs.size + 1)).symm
      · by_cases he : mo = h₀.objs.size + 1
        · subst he
          exact (freshClsHeap_modanc_go_e (h₀.objs.size + 2)).trans
            (freshClsHeap_modanc_go_e (h₀.objs.size + 1)).symm
        · have hoob : ¬ mo < (freshClsHeap h₀ d name q eO).objs.size := by
            rw [hszH]
            exact not_lt_add_two hmo hk he
          exact (modanc_go_oob hoob (h₀.objs.size + 2)).trans
            (modanc_go_oob hoob (h₀.objs.size + 1)).symm
  · intro k'
    rw [hszH]
    by_cases hmo : k' < h₀.objs.size
    · have hold : ∀ f, ancestors.go (freshClsHeap h₀ d name q eO) k' f
          = ancestors.go (hmidOf h₀ d name) k' f :=
        fun f => ClsGrow.ancestors_go_old hg hchm hsm f k' (hszm ▸ hmo)
      have hL := (hold _).trans (ancestors_go_ge hsm.2 hb1 k')
      have hR := (hold _).trans (ancestors_go_ge hsm.2 hb2 k')
      exact hL.trans hR.symm
    · by_cases hk : k' = h₀.objs.size
      · subst hk
        have hcb : Boot.objectId < h₀.objs.size := hch.boot.2.2.2.2
        have hold : ∀ f, ancestors.go (freshClsHeap h₀ d name q eO) Boot.objectId f
            = ancestors.go (hmidOf h₀ d name) Boot.objectId f :=
          fun f => ClsGrow.ancestors_go_old hg hchm hsm f Boot.objectId
            (hszm ▸ hcb)
        have hT1 := (hold (h₀.objs.size + 2)).trans (ancestors_go_ge hsm.2 hb2 Boot.objectId)
        have hT2 := (hold (h₀.objs.size + 1)).trans (ancestors_go_ge hsm.2 hb3 Boot.objectId)
        rw [freshClsHeap_anc_go_k (h₀.objs.size + 2),
          freshClsHeap_anc_go_k (h₀.objs.size + 1), hT1, hT2]
      · by_cases he : k' = h₀.objs.size + 1
        · subst he
          have hold : ∀ f, ancestors.go (freshClsHeap h₀ d name q eO) eO f
              = ancestors.go (hmidOf h₀ d name) eO f :=
            fun f => ClsGrow.ancestors_go_old hg hchm hsm f eO
              (hszm ▸ heOlt)
          have hT1 := (hold (h₀.objs.size + 2)).trans (ancestors_go_ge hsm.2 hb2 eO)
          have hT2 := (hold (h₀.objs.size + 1)).trans (ancestors_go_ge hsm.2 hb3 eO)
          rw [freshClsHeap_anc_go_e (h₀.objs.size + 2),
            freshClsHeap_anc_go_e (h₀.objs.size + 1), hT1, hT2]
        · have hoob : ¬ k' < (freshClsHeap h₀ d name q eO).objs.size := by
            rw [hszH]
            exact not_lt_add_two hmo hk he
          exact (anc_go_oob hoob (h₀.objs.size + 2)).trans
            (anc_go_oob hoob (h₀.objs.size + 1)).symm

/-- `ChainsIn` at the composite: old edges are `hmid`'s; the fresh class's edge
    is `Object`, the eigenclass's is `eO`, both old. -/
theorem chainsIn_freshC (hch : ChainsIn h₀) (hdlt : d < h₀.objs.size)
    (heOlt : eO < h₀.objs.size) :
    ChainsIn (freshClsHeap h₀ d name q eO) := by
  have hchm : ChainsIn (hmidOf h₀ d name) := chainsIn_hmid hch
  have hszH : (freshClsHeap h₀ d name q eO).objs.size = h₀.objs.size + 2 :=
    freshClsHeap_size
  have hszm : (hmidOf h₀ d name).objs.size = h₀.objs.size := hmid_size h₀ d name
  have hbound : ∀ x, x < h₀.objs.size → x < (freshClsHeap h₀ d name q eO).objs.size := by
    intro x hx; rw [hszH]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hx)
  refine ⟨⟨hbound _ hch.boot.1, hbound _ hch.boot.2.1, hbound _ hch.boot.2.2.1,
    hbound _ hch.boot.2.2.2.1, hbound _ hch.boot.2.2.2.2⟩,
    fun o hlt => ?_, fun o hlt e' he' => ?_, fun o cp hlt hcp => ?_⟩
  · by_cases ho : o < h₀.objs.size
    · rw [freshClsHeap_get_old ho, (get_constSetIn_fields h₀ d name _ o).2.1]
      exact hbound _ (hch.klass o ho)
    · by_cases hk : o = h₀.objs.size
      · subst hk; rw [freshClsHeap_get_k]; exact hbound _ hch.boot.1
      · by_cases he2 : o = h₀.objs.size + 1
        · subst he2; rw [freshClsHeap_get_e]; exact hbound _ hch.boot.1
        · exact absurd hlt (by rw [hszH]; exact not_lt_add_two ho hk he2)
  · by_cases ho : o < h₀.objs.size
    · rw [freshClsHeap_get_old ho, (get_constSetIn_fields h₀ d name _ o).2.2.1] at he'
      exact hbound _ (hch.eigen o ho e' he')
    · by_cases hk : o = h₀.objs.size
      · subst hk
        rw [freshClsHeap_get_k] at he'
        cases he'
        rw [hszH]
        exact Nat.lt_succ_self _
      · by_cases he2 : o = h₀.objs.size + 1
        · subst he2
          rw [freshClsHeap_get_e] at he'
          cases he'
        · exact absurd hlt (by rw [hszH]; exact not_lt_add_two ho hk he2)
  · by_cases ho : o < h₀.objs.size
    · have hcpm : (hmidOf h₀ d name).classPayload? o = some cp := by
        unfold Heap.classPayload? at hcp ⊢
        rw [freshClsHeap_get_old ho] at hcp
        exact hcp
      have hsh := shape_constSetIn h₀ d o name (Value.ref h₀.objs.size)
      rw [show constSetIn h₀ d name (Value.ref h₀.objs.size) = hmidOf h₀ d name
        from rfl, hcpm] at hsh
      cases hcp0 : h₀.classPayload? o with
      | none => rw [hcp0] at hsh; simp at hsh
      | some cp0 =>
        rw [hcp0] at hsh
        simp only [Option.map_some, Option.some.injEq] at hsh
        have hpre : cp.prepends = cp0.prepends := congrArg Prod.fst hsh
        have hinc : cp.includes = cp0.includes := congrArg (Prod.fst ∘ Prod.snd) hsh
        have hsup : cp.superclass = cp0.superclass :=
          congrArg (Prod.snd ∘ Prod.snd) hsh
        obtain ⟨hsup0, hinc0, hpre0⟩ := hch.chain o cp0 ho hcp0
        exact ⟨fun s hs => hbound _ (hsup0 s (hsup ▸ hs)),
          fun i hi => hbound _ (hinc0 i (hinc ▸ hi)),
          fun p hp => hbound _ (hpre0 p (hpre ▸ hp))⟩
    · by_cases hk : o = h₀.objs.size
      · subst hk
        rw [freshClsHeap_cp_k] at hcp
        cases hcp
        refine ⟨fun s hs => ?_, fun i hi => ?_, fun p hp => ?_⟩
        · simp only [Option.some.injEq] at hs
          subst hs
          exact hbound _ hch.boot.2.2.2.2
        · exact absurd hi (by simp)
        · exact absurd hp (by simp)
      · by_cases he2 : o = h₀.objs.size + 1
        · subst he2
          rw [freshClsHeap_cp_e] at hcp
          cases hcp
          refine ⟨fun s hs => ?_, fun i hi => ?_, fun p hp => ?_⟩
          · simp only [Option.some.injEq] at hs
            subst hs
            exact hbound _ heOlt
          · exact absurd hi (by simp)
          · exact absurd hp (by simp)
        · rw [freshClsHeap_cp_oob (Nat.le_of_not_lt
            (fun hlt2 => not_lt_add_two ho hk he2 hlt2))] at hcp
          cases hcp

/-! ## Whole-chain reads -/

theorem ancestors_old_freshC (hch : ChainsIn h₀) (hsat : Saturated h₀)
    {o : ObjId} (ho : o < h₀.objs.size) :
    ancestors (freshClsHeap h₀ d name q eO) o = ancestors h₀ o := by
  have hchm : ChainsIn (hmidOf h₀ d name) := chainsIn_hmid hch
  have hsm : Saturated (hmidOf h₀ d name) := saturated_hmid hsat
  rw [ClsGrow.ancestors_old clsGrow_hmid_freshC hchm hsm
    (by rw [hmid_size]; exact ho)]
  exact ancestors_constSetIn h₀ d o name _

/-- The fresh class's chain: itself, then `Object`'s old chain. -/
theorem ancestors_freshC_k (hch : ChainsIn h₀) (hsat : Saturated h₀) :
    ancestors (freshClsHeap h₀ d name q eO) h₀.objs.size
      = h₀.objs.size :: ancestors h₀ Boot.objectId := by
  have hchm : ChainsIn (hmidOf h₀ d name) := chainsIn_hmid hch
  have hsm : Saturated (hmidOf h₀ d name) := saturated_hmid hsat
  have hcb : Boot.objectId < h₀.objs.size := hch.boot.2.2.2.2
  unfold ancestors
  rw [show (freshClsHeap h₀ d name q eO).objs.size + 1 = (h₀.objs.size + 2) + 1 from
    by rw [freshClsHeap_size]]
  rw [freshClsHeap_anc_go_k (h₀.objs.size + 2)]
  rw [ClsGrow.ancestors_go_old clsGrow_hmid_freshC hchm hsm _ Boot.objectId
    (by rw [hmid_size]; exact hcb)]
  rw [ancestors_go_ge hsm.2 (by
    rw [hmid_size]
    exact Nat.add_le_add_left (show (1:Nat) ≤ 2 by decide) _) Boot.objectId]
  have hgo := ClsGrow.ancestors_go_mem_lt hchm ((hmidOf h₀ d name).objs.size + 1)
    Boot.objectId (by rw [hmid_size]; exact hcb)
  have hne : ∀ x ∈ ancestors.go (hmidOf h₀ d name) Boot.objectId
      ((hmidOf h₀ d name).objs.size + 1), x ≠ h₀.objs.size := by
    intro x hx hEq
    have := hgo x hx
    rw [hmid_size] at this
    subst hEq
    exact Nat.lt_irrefl _ this
  show List.foldl _ [] (_ :: _) = _
  rw [show List.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []
      (h₀.objs.size :: ancestors.go (hmidOf h₀ d name) Boot.objectId
        ((hmidOf h₀ d name).objs.size + 1))
      = List.foldl _ ([h₀.objs.size])
        (ancestors.go (hmidOf h₀ d name) Boot.objectId
          ((hmidOf h₀ d name).objs.size + 1)) from rfl]
  rw [show ([h₀.objs.size] : List ObjId) = h₀.objs.size :: [] from rfl]
  rw [foldl_dedup_cons hne [] (by simp)]
  congr 1
  have : ancestors (hmidOf h₀ d name) Boot.objectId = ancestors h₀ Boot.objectId :=
    ancestors_constSetIn h₀ d Boot.objectId name _
  unfold ancestors at this
  rw [← hmid_size h₀ d name] at this ⊢
  exact this

/-- The fresh eigenclass's chain: itself, then `eO`'s old chain. -/
theorem ancestors_freshC_e (hch : ChainsIn h₀) (hsat : Saturated h₀)
    (heOlt : eO < h₀.objs.size) :
    ancestors (freshClsHeap h₀ d name q eO) (h₀.objs.size + 1)
      = (h₀.objs.size + 1) :: ancestors h₀ eO := by
  have hchm : ChainsIn (hmidOf h₀ d name) := chainsIn_hmid hch
  have hsm : Saturated (hmidOf h₀ d name) := saturated_hmid hsat
  unfold ancestors
  rw [show (freshClsHeap h₀ d name q eO).objs.size + 1 = (h₀.objs.size + 2) + 1 from
    by rw [freshClsHeap_size]]
  rw [freshClsHeap_anc_go_e (h₀.objs.size + 2)]
  rw [ClsGrow.ancestors_go_old clsGrow_hmid_freshC hchm hsm _ eO
    (by rw [hmid_size]; exact heOlt)]
  rw [ancestors_go_ge hsm.2 (by
    rw [hmid_size]
    exact Nat.add_le_add_left (show (1:Nat) ≤ 2 by decide) _) eO]
  have hgo := ClsGrow.ancestors_go_mem_lt hchm ((hmidOf h₀ d name).objs.size + 1)
    eO (by rw [hmid_size]; exact heOlt)
  have hne : ∀ x ∈ ancestors.go (hmidOf h₀ d name) eO
      ((hmidOf h₀ d name).objs.size + 1), x ≠ h₀.objs.size + 1 := by
    intro x hx hEq
    have := hgo x hx
    rw [hmid_size] at this
    subst hEq
    exact Nat.not_lt.mpr (Nat.le_succ _) this
  show List.foldl _ [] (_ :: _) = _
  rw [show List.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []
      ((h₀.objs.size + 1) :: ancestors.go (hmidOf h₀ d name) eO
        ((hmidOf h₀ d name).objs.size + 1))
      = List.foldl _ ([h₀.objs.size + 1])
        (ancestors.go (hmidOf h₀ d name) eO
          ((hmidOf h₀ d name).objs.size + 1)) from rfl]
  rw [show ([h₀.objs.size + 1] : List ObjId) = (h₀.objs.size + 1) :: [] from rfl]
  rw [foldl_dedup_cons hne [] (by simp)]
  congr 1
  have : ancestors (hmidOf h₀ d name) eO = ancestors h₀ eO :=
    ancestors_constSetIn h₀ d eO name _
  unfold ancestors at this
  rw [← hmid_size h₀ d name] at this ⊢
  exact this

theorem classOf_freshC_k :
    classOf (freshClsHeap h₀ d name q eO) (.ref h₀.objs.size) = h₀.objs.size + 1 := by
  have h1 : classOf (freshClsHeap h₀ d name q eO) (.ref h₀.objs.size)
      = match ((freshClsHeap h₀ d name q eO).get h₀.objs.size).eigen with
        | some e => e
        | none => ((freshClsHeap h₀ d name q eO).get h₀.objs.size).klass := rfl
  rw [h1, freshClsHeap_get_k]

theorem classOf_freshC_e :
    classOf (freshClsHeap h₀ d name q eO) (.ref (h₀.objs.size + 1)) = Boot.classId := by
  have h1 : classOf (freshClsHeap h₀ d name q eO) (.ref (h₀.objs.size + 1))
      = match ((freshClsHeap h₀ d name q eO).get (h₀.objs.size + 1)).eigen with
        | some e => e
        | none => ((freshClsHeap h₀ d name q eO).get (h₀.objs.size + 1)).klass := rfl
  rw [h1, freshClsHeap_get_e]

end Chains

/-! ## The predicate layer at the composite -/

section PredsC

variable {h₀ : Heap} {d : ObjId} {name q : String} {eO : ObjId}

theorem freshClsHeap_cp_old (hdlt : d < h₀.objs.size) {o : ObjId}
    (ho : o < h₀.objs.size) :
    (freshClsHeap h₀ d name q eO).classPayload? o
      = (hmidOf h₀ d name).classPayload? o := by
  unfold Heap.classPayload?
  rw [freshClsHeap_get_old ho]

theorem className_old_freshC (hdlt : d < h₀.objs.size) {o : ObjId}
    (ho : o < h₀.objs.size) :
    className (freshClsHeap h₀ d name q eO) o = className h₀ o := by
  unfold className
  rw [freshClsHeap_cp_old hdlt ho]
  rw [show (hmidOf h₀ d name).classPayload? o = ((hmidOf h₀ d name).classPayload? o)
    from rfl]
  have := clsName_constSetIn h₀ d o name (Value.ref h₀.objs.size)
  cases hcp : h₀.classPayload? o with
  | none =>
    rw [hcp] at this
    cases hcp2 : (hmidOf h₀ d name).classPayload? o with
    | none => rfl
    | some c2 => rw [hcp2] at this; exact absurd this (by simp)
  | some c =>
    rw [hcp] at this
    cases hcp2 : (hmidOf h₀ d name).classPayload? o with
    | none => rw [hcp2] at this; exact absurd this (by simp)
    | some c2 =>
      rw [hcp2] at this
      simp only [Option.map_some, Option.some.injEq] at this
      have hpair := Prod.ext_iff.mp this
      dsimp only
      rw [show c2.name = c.name from hpair.1,
        show c2.isModule = c.isModule from hpair.2]

theorem className_freshC_k (hqne : ¬ q.isEmpty = true) :
    className (freshClsHeap h₀ d name q eO) h₀.objs.size = q := by
  unfold className
  rw [freshClsHeap_cp_k]
  show (if q.isEmpty then _ else q) = q
  rw [if_neg hqne]

theorem className_freshC_e :
    className (freshClsHeap h₀ d name q eO) (h₀.objs.size + 1)
      = "#<Class:" ++ q ++ ">" := by
  unfold className
  rw [freshClsHeap_cp_e]
  show (if ("#<Class:" ++ q ++ ">").isEmpty then _ else _) = _
  rw [if_neg (by
    simp only [String.isEmpty_iff]
    intro hq
    have h1 := congrArg String.length hq
    simp [String.length_append] at h1)]

/-- A `lookup.go` miss means every table on the walked list misses — the
    converse of `lookupGo_none_of_hookfree`, for reading `NoHook`'s per-value
    clause back into per-table facts along `Object`'s eigenclass chain. -/
theorem lookup_go_none_inv {h : Heap} {nn : String} :
    ∀ l : List ObjId, lookup.go h nn l = none →
      ∀ j ∈ l, ∀ cp, h.classPayload? j = some cp →
        cp.methods.find? (·.1 == nn) = none := by
  intro l
  induction l with
  | nil => intro _ j hj; exact absurd hj (by simp)
  | cons a rest ih =>
    intro hgo j hj cp hcp
    unfold lookup.go at hgo
    rcases List.mem_cons.mp hj with rfl | hjr
    · rw [hcp] at hgo
      dsimp only at hgo
      cases hfind : cp.methods.find? (·.1 == nn) with
      | none => rfl
      | some p =>
        rw [hfind] at hgo
        cases p
        exact absurd hgo (by simp)
    · cases hcpa : h.classPayload? a with
      | none =>
        rw [hcpa] at hgo
        exact ih hgo j hjr cp hcp
      | some ca =>
        rw [hcpa] at hgo
        dsimp only at hgo
        cases hfind : ca.methods.find? (·.1 == nn) with
        | none =>
          rw [hfind] at hgo
          exact ih hgo j hjr cp hcp
        | some p =>
          rw [hfind] at hgo
          cases p
          exact absurd hgo (by simp)

/-- `NoHook` at the composite. The fresh class's dispatch walk is its
    eigenclass's chain — `e :: ancestors h₀ eO` — whose tail's hook-freeness is
    `NoHook`'s per-value clause **at `Object` itself** read back per-table
    (`Object`'s dispatch walk *is* `ancestors h₀ eO`, since its eigenclass is
    realized). -/
theorem noHook_freshC (hh : NoHook h₀) (hch : ChainsIn h₀) (hsat : Saturated h₀)
    (hdlt : d < h₀.objs.size)
    (heO0 : (h₀.get Boot.objectId).eigen = some eO) :
    NoHook (freshClsHeap h₀ d name q eO) := by
  have heOlt : eO < h₀.objs.size :=
    hch.eigen Boot.objectId hch.boot.2.2.2.2 eO heO0
  have hhm : NoHook (hmidOf h₀ d name) := noHook_constSetIn hh
  have hchm : ChainsIn (hmidOf h₀ d name) := chainsIn_hmid hch
  have hsm : Saturated (hmidOf h₀ d name) := saturated_hmid hsat
  have hg : ClsGrow (hmidOf h₀ d name) (freshClsHeap h₀ d name q eO) :=
    clsGrow_hmid_freshC
  -- `Object`'s dispatch walk at h₀ is its eigenclass's chain
  have hclsOfObj : classOf h₀ (.ref Boot.objectId) = eO := by
    have h1 : classOf h₀ (.ref Boot.objectId)
        = match (h₀.get Boot.objectId).eigen with
          | some e => e
          | none => (h₀.get Boot.objectId).klass := rfl
    rw [h1, heO0]
  -- per-table hook-freeness along `ancestors h₀ eO`, from the per-value clause
  have hancEO : ∀ j ∈ ancestors h₀ eO,
      ∀ cp, h₀.classPayload? j = some cp →
      ∀ n ∈ hookFreeNames, cp.methods.find? (·.1 == n) = none := by
    intro j hj cp hcp n hn
    have hlk := hh.2.1 Boot.objectId hh.1 n hn
    unfold lookup at hlk
    rw [hclsOfObj] at hlk
    exact lookup_go_none_inv _ hlk j hj cp hcp
  -- ... transported to the composite
  have hancEOH : ∀ j ∈ ancestors h₀ eO,
      ∀ cp, (freshClsHeap h₀ d name q eO).classPayload? j = some cp →
      ∀ n ∈ hookFreeNames, cp.methods.find? (·.1 == n) = none := by
    intro j hj cp hcp n hn
    have hjlt : j < h₀.objs.size := ClsGrow.ancestors_mem_lt hch heOlt j hj
    rw [freshClsHeap_cp_old hdlt hjlt] at hcp
    have hms := methods_constSetIn h₀ d j name (Value.ref h₀.objs.size)
    cases hcp0 : h₀.classPayload? j with
    | none => rw [hcp0] at hms; rw [hcp] at hms; exact absurd hms (by simp)
    | some cp0 =>
      rw [hcp0, hcp] at hms
      simp only [Option.map_some, Option.some.injEq] at hms
      rw [hms]
      exact hancEO j hj cp0 hcp0 n hn
  -- hook-free tables along `Class`'s chain, at the composite (as in ModFresh)
  have hanc3 : ∀ j ∈ ancestors (freshClsHeap h₀ d name q eO) Boot.classId,
      ∀ cp, (freshClsHeap h₀ d name q eO).classPayload? j = some cp →
      ∀ n ∈ hookFreeNames, cp.methods.find? (·.1 == n) = none := by
    intro j hj cp hcp n hn
    rw [ancestors_old_freshC hch hsat hch.boot.1] at hj
    have hjlt : j < h₀.objs.size := ClsGrow.ancestors_mem_lt hch hch.boot.1 j hj
    rw [freshClsHeap_cp_old hdlt hjlt] at hcp
    have hms := methods_constSetIn h₀ d j name (Value.ref h₀.objs.size)
    cases hcp0 : h₀.classPayload? j with
    | none => rw [hcp0] at hms; rw [hcp] at hms; exact absurd hms (by simp)
    | some cp0 =>
      rw [hcp0, hcp] at hms
      simp only [Option.map_some, Option.some.injEq] at hms
      rw [hms]
      exact hh.2.2 j hj cp0 hcp0 n hn
  refine ⟨?_, fun k hk n hn => ?_, hanc3⟩
  · rw [freshClsHeap_cp_old hdlt hch.boot.2.2.2.2]
    rw [classPayload?_isSome_constSetIn]
    exact hh.1
  · by_cases hko : k < h₀.objs.size
    · unfold lookup
      rw [ClsGrow.classOf_old hg hchm (by rw [hmid_size]; exact hko),
        ClsGrow.ancestors_old hg hchm hsm
          (ClsGrow.classOf_lt hchm (by rw [hmid_size]; exact hko)),
        ClsGrow.lookup_go_old hg _
          (ClsGrow.ancestors_mem_lt hchm
            (ClsGrow.classOf_lt hchm (by rw [hmid_size]; exact hko)))]
      have := hhm.2.1 k (by
        rw [freshClsHeap_cp_old hdlt hko] at hk
        exact hk) n hn
      unfold lookup at this
      exact this
    · by_cases hkk : k = h₀.objs.size
      · subst hkk
        unfold lookup
        rw [classOf_freshC_k, ancestors_freshC_e hch hsat heOlt]
        have hstep : lookup.go (freshClsHeap h₀ d name q eO) n
            ((h₀.objs.size + 1) :: ancestors h₀ eO)
            = lookup.go (freshClsHeap h₀ d name q eO) n (ancestors h₀ eO) := by
          rw [lookup.go.eq_def]
          simp only []
          rw [freshClsHeap_cp_e]
          simp
        rw [hstep]
        refine lookupGo_none_of_hookfree _ (fun j hj cp hcp => ?_)
        exact hancEOH j hj cp hcp n hn
      · by_cases hke : k = h₀.objs.size + 1
        · subst hke
          unfold lookup
          rw [classOf_freshC_e, ancestors_old_freshC hch hsat hch.boot.1]
          refine lookupGo_none_of_hookfree _ (fun j hj cp hcp => ?_)
          exact hanc3 j (by rw [ancestors_old_freshC hch hsat hch.boot.1]; exact hj)
            cp hcp n hn
        · rw [freshClsHeap_cp_oob (Nat.le_of_not_lt
            (fun hlt2 => not_lt_add_two hko hkk hke hlt2))] at hk
          exact absurd hk (by simp)

theorem litClsOk_freshC (hs : LitClsOk h₀) (hdlt : d < h₀.objs.size)
    (hch : ChainsIn h₀) : LitClsOk (freshClsHeap h₀ d name q eO) := by
  have hlt : ∀ x, (h₀.classPayload? x).isSome = true → x < h₀.objs.size :=
    fun x hx => classPayload?_isSome_lt hx
  have hsm : LitClsOk (hmidOf h₀ d name) := litClsOk_constSetIn hs
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩⟩
  · rw [freshClsHeap_cp_old hdlt (hlt _ hs.1.1)]; exact hsm.1.1
  · rw [show className (freshClsHeap h₀ d name q eO) Boot.stringId
      = className h₀ Boot.stringId from
        className_old_freshC hdlt (hlt _ hs.1.1)]
    exact hs.1.2
  · rw [freshClsHeap_cp_old hdlt (hlt _ hs.2.1.1)]; exact hsm.2.1.1
  · rw [className_old_freshC hdlt (hlt _ hs.2.1.1)]; exact hs.2.1.2
  · rw [freshClsHeap_cp_old hdlt (hlt _ hs.2.2.1)]; exact hsm.2.2.1
  · rw [freshClsHeap_cp_old hdlt (hlt _ hs.2.2.2.1)]; exact hsm.2.2.2.1
  · rw [freshClsHeap_cp_old hdlt (hlt _ hs.2.2.2.2.1)]; exact hsm.2.2.2.2.1
  · rw [show className (freshClsHeap h₀ d name q eO) Boot.regexpId
      = className h₀ Boot.regexpId from
        className_old_freshC hdlt (hlt _ hs.2.2.2.2.1)]
    exact hs.2.2.2.2.2

theorem constOwn_freshC_k {n : String} :
    constOwn (freshClsHeap h₀ d name q eO) h₀.objs.size n = none := by
  unfold constOwn
  rw [freshClsHeap_cp_k]
  rfl

theorem constOwn_freshC_e {n : String} :
    constOwn (freshClsHeap h₀ d name q eO) (h₀.objs.size + 1) n = none := by
  unfold constOwn
  rw [freshClsHeap_cp_e]
  rfl

theorem constOwn_old_freshC (hdlt : d < h₀.objs.size) {o : ObjId}
    (ho : o < h₀.objs.size) {n : String} :
    constOwn (freshClsHeap h₀ d name q eO) o n = constOwn (hmidOf h₀ d name) o n := by
  unfold constOwn
  rw [freshClsHeap_cp_old hdlt ho]

/-- `NoShadowBefore` lifts from `hmid` to the composite at any old class. -/
theorem noShadowBefore_freshC (hch : ChainsIn h₀) (hsat : Saturated h₀)
    {k' : ObjId} (hk' : k' < h₀.objs.size)
    (hn : NoShadowBefore (hmidOf h₀ d name) k') :
    NoShadowBefore (freshClsHeap h₀ d name q eO) k' := by
  have hchm : ChainsIn (hmidOf h₀ d name) := chainsIn_hmid hch
  have hsm : Saturated (hmidOf h₀ d name) := saturated_hmid hsat
  have hg : ClsGrow (hmidOf h₀ d name) (freshClsHeap h₀ d name q eO) :=
    clsGrow_hmid_freshC
  have hszm := hmid_size h₀ d name
  have hanc : ancestors (freshClsHeap h₀ d name q eO) k'
      = ancestors (hmidOf h₀ d name) k' :=
    ClsGrow.ancestors_old hg hchm hsm (by rw [hszm]; exact hk')
  refine ⟨by rw [hanc]; exact hn.1, ?_⟩
  rw [hanc]
  intro j hj cp hcp
  have hjm : j ∈ ancestors (hmidOf h₀ d name) k' := by
    have := List.takeWhile_sublist (l := ancestors (hmidOf h₀ d name) k')
      (p := (· != Boot.objectId))
    exact this.mem hj
  have hjlt : j < (hmidOf h₀ d name).objs.size :=
    ClsGrow.ancestors_mem_lt hchm (by rw [hszm]; exact hk') j hjm
  rw [hg.payloadOld hjlt] at hcp
  exact hn.2 j hj cp hcp

/-- `ClassOk` at the composite. -/
theorem classOk_freshC (hch : ChainsIn h₀) (hsat : Saturated h₀)
    (hdlt : d < h₀.objs.size)
    (hcm : ClassOk (hmidOf h₀ d name))
    (hqne : ¬ q.isEmpty = true)
    (hqrd : ∀ n ∈ Types.readableClasses, n ≠ q)
    (hqe : ∀ n ∈ Types.readableClasses, n ≠ "#<Class:" ++ q ++ ">") :
    ClassOk (freshClsHeap h₀ d name q eO) := by
  have hchm : ChainsIn (hmidOf h₀ d name) := chainsIn_hmid hch
  have hsm : Saturated (hmidOf h₀ d name) := saturated_hmid hsat
  have hg : ClsGrow (hmidOf h₀ d name) (freshClsHeap h₀ d name q eO) :=
    clsGrow_hmid_freshC
  have hszm := hmid_size h₀ d name
  have hobj : Boot.objectId < (hmidOf h₀ d name).objs.size := by
    rw [hszm]; exact hch.boot.2.2.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ClsGrow.className_old hg hobj]
    exact hcm.1
  · exact noShadowBefore_freshC hch hsat hch.boot.2.2.2.2 hcm.2.1
  · intro n hn
    obtain ⟨kn, cp, h1, h2, h4, h5, hrx, hmt, hsole, hreop⟩ := hcm.2.2.1 n hn
    have hknlt : kn < (hmidOf h₀ d name).objs.size :=
      classPayload?_isSome_lt (by rw [h2]; simp)
    refine ⟨kn, cp,
      by rw [ClsGrow.constOwn_old hg hobj]; exact h1,
      by rw [hg.payloadOld hknlt]; exact h2,
      by rw [ClsGrow.className_old hg hknlt]; exact h4,
      ?_, hrx, hmt, ?_, ?_⟩
    · intro j hji hjn
      by_cases hjo : j < h₀.objs.size
      · refine h5 j ?_ ?_
        · rw [← hg.payloadOld (by rw [hszm]; exact hjo)]; exact hji
        · rw [← ClsGrow.className_old hg (by rw [hszm]; exact hjo)]; exact hjn
      · by_cases hjk : j = h₀.objs.size
        · subst hjk
          rw [className_freshC_k hqne] at hjn
          exact absurd hjn.symm (hqrd n hn)
        · by_cases hje : j = h₀.objs.size + 1
          · subst hje
            rw [className_freshC_e] at hjn
            exact absurd hjn.symm (hqe n hn)
          · rw [freshClsHeap_cp_oob (Nat.le_of_not_lt
              (fun hlt2 => not_lt_add_two hjo hjk hje hlt2))] at hji
            exact absurd hji (by simp)
    · intro j hji hjo
      by_cases hjlt : j < h₀.objs.size
      · rw [ClsGrow.constOwn_old hg (by rw [hszm]; exact hjlt)]
        refine hsole j ?_ hjo
        rw [← hg.payloadOld (by rw [hszm]; exact hjlt)]; exact hji
      · by_cases hjk : j = h₀.objs.size
        · subst hjk; exact constOwn_freshC_k
        · by_cases hje : j = h₀.objs.size + 1
          · subst hje; exact constOwn_freshC_e
          · rw [freshClsHeap_cp_oob (Nat.le_of_not_lt
              (fun hlt2 => not_lt_add_two hjlt hjk hje hlt2))] at hji
            exact absurd hji (by simp)
    · intro hmem
      obtain ⟨hmod, hhd, hns⟩ := hreop hmem
      refine ⟨hmod, ?_, noShadowBefore_freshC hch hsat (by rw [← hszm]; exact hknlt) hns⟩
      rw [ClsGrow.ancestors_old hg hchm hsm hknlt]
      exact hhd
  · intro o cp hcp
    by_cases ho : o < h₀.objs.size
    · rw [hg.payloadOld (by rw [hszm]; exact ho)] at hcp
      exact hcm.2.2.2 o cp hcp
    · by_cases hk : o = h₀.objs.size
      · subst hk
        rw [freshClsHeap_cp_k] at hcp
        cases hcp
        exact Bool.eq_false_iff.mpr hqne
      · by_cases he2 : o = h₀.objs.size + 1
        · subst he2
          rw [freshClsHeap_cp_e] at hcp
          cases hcp
          refine Bool.eq_false_iff.mpr ?_
          show ¬ ("#<Class:" ++ q ++ ">").isEmpty = true
          simp only [String.isEmpty_iff]
          intro hq
          have h1 := congrArg String.length hq
          simp [String.length_append] at h1
        · rw [freshClsHeap_cp_oob (Nat.le_of_not_lt
            (fun hlt2 => not_lt_add_two ho hk he2 hlt2))] at hcp
          cases hcp

end PredsC

/-! ## `DeclsOkJ` at the composite -/

section TableC

variable {h₀ : Heap} {d : ObjId} {name q : String} {eO : ObjId}

/-- `TyClass` at the composite lands at an old id, given the name is keyed
    fresh. -/
theorem tyClass_freshC_old (hch : ChainsIn h₀) (hdlt : d < h₀.objs.size)
    (hqne : ¬ q.isEmpty = true) {τ : Ty} {k : ObjId}
    (hkeys : ∀ c ∈ tyClassNames τ, KeyFresh q c)
    (hnee : tyClassNames τ ≠ [])
    (ht : TyClass (freshClsHeap h₀ d name q eO) τ k) :
    k < h₀.objs.size → TyClass (hmidOf h₀ d name) τ k := by
  intro hko
  have hpin : ∀ o, o < h₀.objs.size →
      (freshClsHeap h₀ d name q eO).classPayload? o
        = (hmidOf h₀ d name).classPayload? o :=
    fun o ho => freshClsHeap_cp_old hdlt ho
  have hcn : ∀ o, o < h₀.objs.size →
      className (freshClsHeap h₀ d name q eO) o = className (hmidOf h₀ d name) o := by
    intro o ho
    unfold className
    rw [hpin o ho]
  cases τ with
  | cls n => exact ⟨(hpin k hko) ▸ ht.1, (hcn k hko) ▸ ht.2⟩
  | arrayOf e => exact absurd (rfl : tyClassNames (Ty.arrayOf e) = []) hnee
  | clsOf n =>
    obtain ⟨o, hcp, hnm2, hk⟩ := ht
    by_cases ho : o < h₀.objs.size
    · refine ⟨o, (hpin o ho) ▸ hcp, (hcn o ho) ▸ hnm2, ?_⟩
      rw [hk]
      have h1 : classOf (freshClsHeap h₀ d name q eO) (.ref o)
          = match ((freshClsHeap h₀ d name q eO).get o).eigen with
            | some e => e
            | none => ((freshClsHeap h₀ d name q eO).get o).klass := rfl
      have h2 : classOf (hmidOf h₀ d name) (.ref o)
          = match ((hmidOf h₀ d name).get o).eigen with
            | some e => e
            | none => ((hmidOf h₀ d name).get o).klass := rfl
      rw [h1, h2, freshClsHeap_get_old ho]
    · exact absurd (rfl : tyClassNames (Ty.clsOf n) = []) hnee
  | any => exact ht.elim
  | nilable _ => exact ht.elim
  | int => exact ht
  | float => exact ht
  | bool => exact ht
  | nilT => exact ht
  | sym => exact ht
  | arrow0 _ => exact ht.elim
  | arrowCons _ _ => exact ht.elim
  | union _ _ => exact ht.elim

/-- Off the old bounds, a fresh-keyed `TyClass` collapses to the ground arms. -/
theorem tyClass_freshC_ground (hqne : ¬ q.isEmpty = true) {τ : Ty} {k : ObjId}
    (hkeys : ∀ c ∈ tyClassNames τ, KeyFresh q c)
    (hnee : tyClassNames τ ≠ [])
    (hko : ¬ k < h₀.objs.size)
    (ht : TyClass (freshClsHeap h₀ d name q eO) τ k) :
    TyClass (hmidOf h₀ d name) τ k := by
  cases τ with
  | cls n =>
    exfalso
    obtain ⟨hps, hcn⟩ := ht
    by_cases hgr : groundClassNames.contains n
    · refine hnee ?_
      show (if groundClassNames.contains n = true then ([] : List String) else [n]) = []
      rw [if_pos hgr]
    · have hn : n ∈ tyClassNames (Ty.cls n) := by
        show n ∈ (if groundClassNames.contains n = true then ([] : List String) else [n])
        rw [if_neg hgr]
        simp
      by_cases hkk : k = h₀.objs.size
      · subst hkk
        rw [className_freshC_k hqne] at hcn
        exact (hkeys n hn).1 hcn.symm
      · by_cases hke : k = h₀.objs.size + 1
        · subst hke
          rw [className_freshC_e] at hcn
          exact keyFresh_ne_ename (hkeys n hn) hcn.symm
        · rw [freshClsHeap_cp_oob (Nat.le_of_not_lt
            (fun hlt2 => not_lt_add_two hko hkk hke hlt2))] at hps
          exact absurd hps (by simp)
  | arrayOf e => exact absurd (rfl : tyClassNames (Ty.arrayOf e) = []) hnee
  | clsOf n => exact absurd (rfl : tyClassNames (Ty.clsOf n) = []) hnee
  | any => exact ht.elim
  | nilable _ => exact ht.elim
  | int => exact ht
  | float => exact ht
  | bool => exact ht
  | nilT => exact ht
  | sym => exact ht
  | arrow0 _ => exact ht.elim
  | arrowCons _ _ => exact ht.elim
  | union _ _ => exact ht.elim

/-- `ResolvesAt` lifts from `hmid` to the composite at an old class. -/
theorem resolvesAt_freshC (hch : ChainsIn h₀) (hsat : Saturated h₀)
    {k : ObjId} (hk : k < h₀.objs.size) {mname bid : String}
    (hr : ResolvesAt (hmidOf h₀ d name) k mname bid) :
    ResolvesAt (freshClsHeap h₀ d name q eO) k mname bid := by
  have hchm : ChainsIn (hmidOf h₀ d name) := chainsIn_hmid hch
  have hsm : Saturated (hmidOf h₀ d name) := saturated_hmid hsat
  have hg : ClsGrow (hmidOf h₀ d name) (freshClsHeap h₀ d name q eO) :=
    clsGrow_hmid_freshC
  have hkm : k < (hmidOf h₀ d name).objs.size := by rw [hmid_size]; exact hk
  obtain ⟨owner, md, hl, hb, hu, hv2, hp, hsh⟩ := hr
  refine ⟨owner, md, by rw [ClsGrow.lookupIn_old hg hchm hsm hkm]; exact hl,
    hb, hu, hv2, hp, ?_⟩
  rw [ClsGrow.ancestors_old hg hchm hsm hkm]
  rw [ClsGrow.crubyShadow_old hg _ (fun j hj =>
    ClsGrow.ancestors_mem_lt hchm hkm j ((List.takeWhile_sublist _).mem hj))]
  exact hsh

theorem resolvesUser_freshC (hch : ChainsIn h₀) (hsat : Saturated h₀)
    (hdlt : d < h₀.objs.size)
    {k : ObjId} (hk : k < h₀.objs.size) {mname : String} {md : MethodDef}
    (hr : ResolvesUser (hmidOf h₀ d name) k mname md) :
    ResolvesUser (freshClsHeap h₀ d name q eO) k mname md := by
  have hchm : ChainsIn (hmidOf h₀ d name) := chainsIn_hmid hch
  have hsm : Saturated (hmidOf h₀ d name) := saturated_hmid hsat
  have hg : ClsGrow (hmidOf h₀ d name) (freshClsHeap h₀ d name q eO) :=
    clsGrow_hmid_freshC
  have hkm : k < (hmidOf h₀ d name).objs.size := by rw [hmid_size]; exact hk
  obtain ⟨owner, hl, hb, hu, hv2, hps, hdc, hcf, hown, hsh, hcref, hchain⟩ := hr
  have hownlt : md.owner < (hmidOf h₀ d name).objs.size :=
    classPayload?_isSome_lt hown
  refine ⟨owner, by rw [ClsGrow.lookupIn_old hg hchm hsm hkm]; exact hl,
    hb, hu, hv2, hps, hdc, hcf,
    by rw [hg.classPayload?_isSome_old hownlt]; exact hown, ?_, hcref,
    by rw [ClsGrow.ancestors_old hg hchm hsm hkm]; exact hchain⟩
  cases hmd : md.fromPrelude with
  | true =>
    simp only [hmd, if_true] at hsh ⊢
    rw [show crubyShadow (freshClsHeap h₀ d name q eO) [] mname
        = crubyShadow (hmidOf h₀ d name) [] mname from rfl]
    exact hsh
  | false =>
    simp only [hmd, Bool.false_eq_true, if_false] at hsh ⊢
    rw [ClsGrow.ancestors_old hg hchm hsm hkm]
    rw [ClsGrow.crubyShadow_old hg _ (fun j hj =>
      ClsGrow.ancestors_mem_lt hchm hkm j ((List.takeWhile_sublist _).mem hj))]
    exact hsh

/-- `EntryOkJ` at the composite. -/
theorem entryOkJ_freshC (hch : ChainsIn h₀) (hsat : Saturated h₀)
    (hdlt : d < h₀.objs.size) (hqne : ¬ q.isEmpty = true)
    (hcO : ClassOk (hmidOf h₀ d name)) (hnoO : NoHook (hmidOf h₀ d name))
    {A : SemAxioms} {D : Decls} {τr : Ty} {mname : String} {dd : MethodDecl}
    (hkeys : ∀ c ∈ tyClassNames τr, KeyFresh q c)
    (hnee : tyClassNames τr ≠ [])
    (he : EntryOkJ A D (hmidOf h₀ d name) τr mname dd) :
    EntryOkJ A D (freshClsHeap h₀ d name q eO) τr mname dd := by
  have hchm : ChainsIn (hmidOf h₀ d name) := chainsIn_hmid hch
  have hsm : Saturated (hmidOf h₀ d name) := saturated_hmid hsat
  have hg : ClsGrow (hmidOf h₀ d name) (freshClsHeap h₀ d name q eO) :=
    clsGrow_hmid_freshC
  rcases he with ⟨bid, hres, hconf⟩ | ⟨md, c, hkey, hres, hown, hconf⟩ |
    ⟨hτ, hmn, hdp, hdr, hdb, hmiss⟩
  · refine Or.inl ⟨bid, fun k hk => ?_, hconf⟩
    by_cases hko : k < h₀.objs.size
    · exact resolvesAt_freshC hch hsat hko
        (hres k (tyClass_freshC_old hch hdlt hqne hkeys hnee hk hko))
    · exfalso
      obtain ⟨owner, md, hl, -⟩ :=
        hres k (tyClass_freshC_ground hqne hkeys hnee hko hk)
      rw [lookupIn_oob (by rw [hmid_size]; exact hko)] at hl
      exact absurd hl.symm (by simp)
  · refine Or.inr (Or.inl ⟨md, c, hkey, fun k hk => ?_, ?_, hconf⟩)
    · by_cases hko : k < h₀.objs.size
      · exact resolvesUser_freshC hch hsat hdlt hko
          (hres k (tyClass_freshC_old hch hdlt hqne hkeys hnee hk hko))
      · exfalso
        obtain ⟨owner, hl, -⟩ :=
          hres k (tyClass_freshC_ground hqne hkeys hnee hko hk)
        rw [lookupIn_oob (by rw [hmid_size]; exact hko)] at hl
        exact absurd hl.symm (by simp)
    · have hownlt : md.owner < (hmidOf h₀ d name).objs.size := by
        by_cases hb : md.owner < (hmidOf h₀ d name).objs.size
        · exact hb
        · exfalso
          have hcobj : c = "Object" := by
            rw [← hown]
            unfold className
            rw [classPayload?_oob _ _ hb]
          have hty : TyClass (hmidOf h₀ d name) τr Boot.objectId := by
            rcases hkey with rfl | ⟨⟨e, rfl⟩, rfl⟩
            · exact ⟨hnoO.1, by rw [hcO.1, hcobj]⟩
            · exact absurd (rfl : tyClassNames (Ty.arrayOf e) = []) hnee
          obtain ⟨owner', -, -, -, -, -, -, -, hown', -⟩ := hres Boot.objectId hty
          exact hb (classPayload?_isSome_lt hown')
      rw [ClsGrow.className_old hg hownlt]
      exact hown
  · refine Or.inr (Or.inr ⟨hτ, hmn, hdp, hdr, hdb, fun k hk => ?_⟩)
    subst hτ
    by_cases hko : k < h₀.objs.size
    · have := hmiss k (tyClass_freshC_old hch hdlt hqne hkeys hnee hk hko)
      unfold MissesAt at this ⊢
      rw [ClsGrow.lookupIn_old hg hchm hsm (by rw [hmid_size]; exact hko)]
      exact this
    · by_cases hkk : k = h₀.objs.size
      · subst hkk
        obtain ⟨hps, hcn⟩ := hk
        rw [className_freshC_k hqne] at hcn
        exact absurd hcn.symm (hkeys "Array" (by
          show "Array" ∈ (if groundClassNames.contains "Array" = true
            then ([] : List String) else ["Array"])
          rw [if_neg (by decide)]
          simp)).1
      · by_cases hke : k = h₀.objs.size + 1
        · subst hke
          obtain ⟨hps, hcn⟩ := hk
          rw [className_freshC_e] at hcn
          exact absurd hcn.symm (keyFresh_ne_ename (hkeys "Array" (by
            show "Array" ∈ (if groundClassNames.contains "Array" = true
              then ([] : List String) else ["Array"])
            rw [if_neg (by decide)]
            simp)))
        · unfold MissesAt
          exact lookupIn_oob (by
            rw [freshClsHeap_size]
            exact fun hlt2 => not_lt_add_two hko hkk hke hlt2) mname

theorem constOk_freshC (hch : ChainsIn h₀) (hsat : Saturated h₀)
    (hdlt : d < h₀.objs.size) {n : String} {τ : Ty}
    (hc : ConstOk (hmidOf h₀ d name) n τ) :
    ConstOk (freshClsHeap h₀ d name q eO) n τ := by
  have hchm : ChainsIn (hmidOf h₀ d name) := chainsIn_hmid hch
  have hsm : Saturated (hmidOf h₀ d name) := saturated_hmid hsat
  have hg : ClsGrow (hmidOf h₀ d name) (freshClsHeap h₀ d name q eO) :=
    clsGrow_hmid_freshC
  have hobj : Boot.objectId < (hmidOf h₀ d name).objs.size := by
    rw [hmid_size]; exact hch.boot.2.2.2.2
  obtain ⟨v, hv, hty, hsole⟩ := hc
  refine ⟨v, by rw [ClsGrow.constOwn_old hg hobj]; exact hv,
    ClsGrow.valueTy_old hg hchm hty, fun j hj hjo => ?_⟩
  by_cases hjlt : j < h₀.objs.size
  · rw [ClsGrow.constOwn_old hg (by rw [hmid_size]; exact hjlt)]
    refine hsole j ?_ hjo
    rw [← hg.payloadOld (by rw [hmid_size]; exact hjlt)]; exact hj
  · by_cases hjk : j = h₀.objs.size
    · subst hjk; exact constOwn_freshC_k
    · by_cases hje : j = h₀.objs.size + 1
      · subst hje; exact constOwn_freshC_e
      · rw [freshClsHeap_cp_oob (Nat.le_of_not_lt
          (fun hlt2 => not_lt_add_two hjlt hjk hje hlt2))] at hj
        exact absurd hj (by simp)

theorem ivarOk_freshC (hch : ChainsIn h₀) (hsat : Saturated h₀)
    (hdlt : d < h₀.objs.size) {c x : String} {τ : Ty}
    (hi : IvarOk (hmidOf h₀ d name) c x τ) :
    IvarOk (freshClsHeap h₀ d name q eO) c x τ := by
  have hchm : ChainsIn (hmidOf h₀ d name) := chainsIn_hmid hch
  have hg : ClsGrow (hmidOf h₀ d name) (freshClsHeap h₀ d name q eO) :=
    clsGrow_hmid_freshC
  intro o ho hcn v hfind
  by_cases holt : o < h₀.objs.size
  · have hom : o < (hmidOf h₀ d name).objs.size := by rw [hmid_size]; exact holt
    rw [freshClsHeap_get_old holt] at hcn hfind
    have hklt : ((hmidOf h₀ d name).get o).klass < (hmidOf h₀ d name).objs.size :=
      hchm.klass o hom
    rw [ClsGrow.className_old hg hklt] at hcn
    exact ClsGrow.valueTy_old hg hchm (hi o hom hcn v hfind)
  · by_cases hok : o = h₀.objs.size
    · subst hok
      rw [freshClsHeap_get_k] at hfind
      exact absurd hfind (by simp)
    · by_cases hoe : o = h₀.objs.size + 1
      · subst hoe
        rw [freshClsHeap_get_e] at hfind
        exact absurd hfind (by simp)
      · rw [freshClsHeap_size] at ho
        exact absurd ho (not_lt_add_two holt hok hoe)

theorem scopedConstOk_freshC (hch : ChainsIn h₀) (hsat : Saturated h₀)
    (hdlt : d < h₀.objs.size) (hqne : ¬ q.isEmpty = true)
    {c n : String} {τ : Ty} (hkc : KeyFresh q c)
    (hs : ScopedConstOk (hmidOf h₀ d name) c n τ) :
    ScopedConstOk (freshClsHeap h₀ d name q eO) c n τ := by
  have hchm : ChainsIn (hmidOf h₀ d name) := chainsIn_hmid hch
  have hsm : Saturated (hmidOf h₀ d name) := saturated_hmid hsat
  have hg : ClsGrow (hmidOf h₀ d name) (freshClsHeap h₀ d name q eO) :=
    clsGrow_hmid_freshC
  intro o ho hcn
  by_cases holt : o < h₀.objs.size
  · have hom : o < (hmidOf h₀ d name).objs.size := by rw [hmid_size]; exact holt
    rw [hg.payloadOld hom] at ho
    rw [ClsGrow.className_old hg hom] at hcn
    obtain ⟨hpriv, v, hv, hty⟩ := hs o ho hcn
    have hanc : ancestors (freshClsHeap h₀ d name q eO) o
        = ancestors (hmidOf h₀ d name) o :=
      ClsGrow.ancestors_old hg hchm hsm hom
    refine ⟨?_, v, ?_, ClsGrow.valueTy_old hg hchm hty⟩
    · rw [hanc]
      refine List.all_eq_true.mpr (fun a ha => ?_)
      have halt : a < (hmidOf h₀ d name).objs.size :=
        ClsGrow.ancestors_mem_lt hchm hom a ha
      rw [hg.payloadOld halt]
      exact List.all_eq_true.mp hpriv a ha
    · rw [ClsGrow.constLookupFrom_old hg hchm hsm hom]
      exact hv
  · by_cases hok : o = h₀.objs.size
    · subst hok
      rw [className_freshC_k hqne] at hcn
      exact absurd hcn.symm hkc.1
    · by_cases hoe : o = h₀.objs.size + 1
      · subst hoe
        rw [className_freshC_e] at hcn
        exact absurd hcn.symm (keyFresh_ne_ename hkc)
      · rw [freshClsHeap_cp_oob (Nat.le_of_not_lt
          (fun hlt2 => not_lt_add_two holt hok hoe hlt2))] at ho
        exact absurd ho (by simp)

theorem superOk_freshC (hch : ChainsIn h₀) (hsat : Saturated h₀)
    (hdlt : d < h₀.objs.size) (hqne : ¬ q.isEmpty = true)
    (heOlt : eO < h₀.objs.size)
    {c mname : String} {dd : MethodDecl} (hkc : KeyFresh q c)
    (hs : SuperOk (hmidOf h₀ d name) c mname dd) :
    SuperOk (freshClsHeap h₀ d name q eO) c mname dd := by
  have hchm : ChainsIn (hmidOf h₀ d name) := chainsIn_hmid hch
  have hsm : Saturated (hmidOf h₀ d name) := saturated_hmid hsat
  have hg : ClsGrow (hmidOf h₀ d name) (freshClsHeap h₀ d name q eO) :=
    clsGrow_hmid_freshC
  intro k dm hdm hdc hmem
  have hdmo : dm < h₀.objs.size := by
    by_cases h1 : dm < h₀.objs.size
    · exact h1
    · exfalso
      by_cases h2 : dm = h₀.objs.size
      · subst h2
        rw [className_freshC_k hqne] at hdc
        exact hkc.1 hdc.symm
      · by_cases h3 : dm = h₀.objs.size + 1
        · subst h3
          rw [className_freshC_e] at hdc
          exact keyFresh_ne_ename hkc hdc.symm
        · rw [freshClsHeap_cp_oob (Nat.le_of_not_lt
            (fun hlt2 => not_lt_add_two h1 h2 h3 hlt2))] at hdm
          exact absurd hdm (by simp)
  have hdmm : dm < (hmidOf h₀ d name).objs.size := by rw [hmid_size]; exact hdmo
  by_cases hko : k < h₀.objs.size
  · have hkm : k < (hmidOf h₀ d name).objs.size := by rw [hmid_size]; exact hko
    have hanc : ancestors (freshClsHeap h₀ d name q eO) k
        = ancestors (hmidOf h₀ d name) k :=
      ClsGrow.ancestors_old hg hchm hsm hkm
    obtain ⟨owner, md, bid, hsf, hb, hcf⟩ := hs k dm
      (by rw [← hg.payloadOld hdmm]; exact hdm)
      (by rw [← ClsGrow.className_old hg hdmm]; exact hdc)
      (by rw [← hanc]; exact hmem)
    refine ⟨owner, md, bid, ?_, hb, hcf⟩
    unfold superFound at hsf ⊢
    rw [hanc]
    rw [firstM_congr (fun j hj => by
      have hjo : j < h₀.objs.size := by
        rw [← hmid_size h₀ d name]
        refine ClsGrow.ancestors_mem_lt hchm hkm j ?_
        exact (((List.drop_sublist 1 (List.dropWhile (· != dm)
            (ancestors (hmidOf h₀ d name) k))).trans
          (List.dropWhile_sublist (· != dm))).mem hj)
      rw [freshClsHeap_cp_old hdlt hjo])]
    exact hsf
  · by_cases hkk : k = h₀.objs.size
    · -- the fresh class: its chain is itself, then `Object`'s old chain
      subst hkk
      rw [ancestors_freshC_k hch hsat] at hmem
      rcases List.mem_cons.mp hmem with hEq | hmem2
      · exact absurd hdmo (by rw [hEq]; exact Nat.lt_irrefl _)
      · have hob : Boot.objectId < h₀.objs.size := hch.boot.2.2.2.2
        have hobm : Boot.objectId < (hmidOf h₀ d name).objs.size := by
          rw [hmid_size]; exact hob
        have hancO : ancestors (hmidOf h₀ d name) Boot.objectId
            = ancestors h₀ Boot.objectId :=
          ancestors_constSetIn h₀ d Boot.objectId name _
        obtain ⟨owner, md, bid, hsf, hb, hcf⟩ := hs Boot.objectId dm
          (by rw [← hg.payloadOld hdmm]; exact hdm)
          (by rw [← ClsGrow.className_old hg hdmm]; exact hdc)
          (by rw [hancO]; exact hmem2)
        refine ⟨owner, md, bid, ?_, hb, hcf⟩
        unfold superFound at hsf ⊢
        rw [ancestors_freshC_k hch hsat]
        rw [List.dropWhile_cons_of_pos (by
          simp only [bne_iff_ne, ne_eq]
          intro h1
          exact absurd hdmo (by rw [← h1]; exact Nat.lt_irrefl _))]
        rw [show ancestors h₀ Boot.objectId
            = ancestors (hmidOf h₀ d name) Boot.objectId from hancO.symm]
        rw [firstM_congr (fun j hj => by
          have hjo : j < h₀.objs.size := by
            rw [← hmid_size h₀ d name]
            refine ClsGrow.ancestors_mem_lt hchm hobm j ?_
            exact (((List.drop_sublist 1 (List.dropWhile (· != dm)
                (ancestors (hmidOf h₀ d name) Boot.objectId))).trans
              (List.dropWhile_sublist (· != dm))).mem hj)
          rw [freshClsHeap_cp_old hdlt hjo])]
        exact hsf
    · by_cases hke : k = h₀.objs.size + 1
      · -- the fresh eigenclass: itself, then `eO`'s old chain
        subst hke
        rw [ancestors_freshC_e hch hsat heOlt] at hmem
        rcases List.mem_cons.mp hmem with hEq | hmem2
        · exact absurd hdmo (by rw [hEq]; exact Nat.not_lt.mpr (Nat.le_add_right _ 1))
        · have heOm : eO < (hmidOf h₀ d name).objs.size := by
            rw [hmid_size]; exact heOlt
          have hancE : ancestors (hmidOf h₀ d name) eO = ancestors h₀ eO :=
            ancestors_constSetIn h₀ d eO name _
          obtain ⟨owner, md, bid, hsf, hb, hcf⟩ := hs eO dm
            (by rw [← hg.payloadOld hdmm]; exact hdm)
            (by rw [← ClsGrow.className_old hg hdmm]; exact hdc)
            (by rw [hancE]; exact hmem2)
          refine ⟨owner, md, bid, ?_, hb, hcf⟩
          unfold superFound at hsf ⊢
          rw [ancestors_freshC_e hch hsat heOlt]
          rw [List.dropWhile_cons_of_pos (by
            simp only [bne_iff_ne, ne_eq]
            intro h1
            exact absurd hdmo (by rw [← h1]
                                  exact Nat.not_lt.mpr (Nat.le_add_right _ 1)))]
          rw [show ancestors h₀ eO
              = ancestors (hmidOf h₀ d name) eO from hancE.symm]
          rw [firstM_congr (fun j hj => by
            have hjo : j < h₀.objs.size := by
              rw [← hmid_size h₀ d name]
              refine ClsGrow.ancestors_mem_lt hchm heOm j ?_
              exact (((List.drop_sublist 1 (List.dropWhile (· != dm)
                  (ancestors (hmidOf h₀ d name) eO))).trans
                (List.dropWhile_sublist (· != dm))).mem hj)
            rw [freshClsHeap_cp_old hdlt hjo])]
          exact hsf
      · rw [show ancestors (freshClsHeap h₀ d name q eO) k = [k] from by
          unfold ancestors
          rw [anc_go_oob (by
            rw [freshClsHeap_size]
            exact fun hlt2 => not_lt_add_two hko hkk hke hlt2)]
          rfl] at hmem
        have hEq : dm = k := List.mem_singleton.mp hmem
        exact absurd hdmo (by rw [hEq]; exact hko)

/-- `ModOffChains` lifts from `hmid` to the composite at an old id: both fresh
    chains reach `Object` only through *old* `Object`-reaching chains, whose
    pre-`Object` segments the old fact already clears. -/
theorem modOffChains_freshC_old (hch : ChainsIn h₀) (hsat : Saturated h₀)
    (hdlt : d < h₀.objs.size) (heOlt : eO < h₀.objs.size)
    {o : ObjId} (ho : o < h₀.objs.size)
    (hoff : ModOffChains (hmidOf h₀ d name) o) :
    ModOffChains (freshClsHeap h₀ d name q eO) o := by
  have hchm : ChainsIn (hmidOf h₀ d name) := chainsIn_hmid hch
  have hsm : Saturated (hmidOf h₀ d name) := saturated_hmid hsat
  have hg : ClsGrow (hmidOf h₀ d name) (freshClsHeap h₀ d name q eO) :=
    clsGrow_hmid_freshC
  have hancO : ancestors (hmidOf h₀ d name) Boot.objectId
      = ancestors h₀ Boot.objectId := ancestors_constSetIn h₀ d Boot.objectId name _
  have hancE : ancestors (hmidOf h₀ d name) eO
      = ancestors h₀ eO := ancestors_constSetIn h₀ d eO name _
  intro k' hmem
  by_cases hko : k' < h₀.objs.size
  · have hkm : k' < (hmidOf h₀ d name).objs.size := by rw [hmid_size]; exact hko
    rw [ClsGrow.ancestors_old hg hchm hsm hkm] at hmem ⊢
    exact hoff k' hmem
  · by_cases hkk : k' = h₀.objs.size
    · subst hkk
      rw [ancestors_freshC_k hch hsat] at hmem ⊢
      have hobjm : Boot.objectId ∈ ancestors h₀ Boot.objectId := by
        rcases List.mem_cons.mp hmem with hEq | hm2
        · exact absurd hEq (Nat.ne_of_lt hch.boot.2.2.2.2)
        · exact hm2
      rw [List.takeWhile_cons_of_pos (by
        simp only [bne_iff_ne, ne_eq]
        intro h1
        exact absurd h1 (Ne.symm (Nat.ne_of_lt hch.boot.2.2.2.2)))]
      intro hmm
      rcases List.mem_cons.mp hmm with hEq | hm2
      · rw [hEq] at ho
        exact Nat.lt_irrefl _ ho
      · have := hoff Boot.objectId (by rw [hancO]; exact hobjm)
        rw [hancO] at this
        exact this hm2
    · by_cases hke : k' = h₀.objs.size + 1
      · subst hke
        rw [ancestors_freshC_e hch hsat heOlt] at hmem ⊢
        have hobjm : Boot.objectId ∈ ancestors h₀ eO := by
          rcases List.mem_cons.mp hmem with hEq | hm2
          · exfalso
            have hb := hch.boot.2.2.2.2
            rw [hEq] at hb
            exact Nat.not_lt.mpr (Nat.le_add_right _ 1) hb
          · exact hm2
        rw [List.takeWhile_cons_of_pos (by
          simp only [bne_iff_ne, ne_eq]
          intro h1
          have := hch.boot.2.2.2.2
          rw [← h1] at this
          exact Nat.not_lt.mpr (Nat.le_add_right _ 1) this)]
        intro hmm
        rcases List.mem_cons.mp hmm with hEq | hm2
        · rw [hEq] at ho
          exact Nat.not_lt.mpr (Nat.le_add_right _ 1) ho
        · have := hoff eO (by rw [hancE]; exact hobjm)
          rw [hancE] at this
          exact this hm2
      · rw [show ancestors (freshClsHeap h₀ d name q eO) k' = [k'] from by
          unfold ancestors
          rw [anc_go_oob (by
            rw [freshClsHeap_size]
            exact fun hlt2 => not_lt_add_two hko hkk hke hlt2)]
          rfl] at hmem
        have hEq := List.mem_singleton.mp hmem
        exact absurd (by rw [← hEq]; exact hch.boot.2.2.2.2 : k' < h₀.objs.size)
          hko

/-- `ModOwner` at the class composite lands at an old id **unconditionally**:
    the fresh class and its eigenclass are not modules. -/
theorem modOwner_freshC_old (hch : ChainsIn h₀) (hsat : Saturated h₀)
    (hdlt : d < h₀.objs.size)
    {owner : String} {o : ObjId}
    (hmo : ModOwner (freshClsHeap h₀ d name q eO) owner o) :
    o < h₀.objs.size ∧ ModOwner (hmidOf h₀ d name) owner o := by
  have hchm : ChainsIn (hmidOf h₀ d name) := chainsIn_hmid hch
  have hsm : Saturated (hmidOf h₀ d name) := saturated_hmid hsat
  have hg : ClsGrow (hmidOf h₀ d name) (freshClsHeap h₀ d name q eO) :=
    clsGrow_hmid_freshC
  rcases hmo with ⟨h1, h2⟩ | ⟨cp, hcp, hism, hnm, heig, hoff⟩
  · exact ⟨h2 ▸ hch.boot.2.2.2.2, Or.inl ⟨h1, h2⟩⟩
  · by_cases ho : o < h₀.objs.size
    · have hom : o < (hmidOf h₀ d name).objs.size := by rw [hmid_size]; exact ho
      refine ⟨ho, Or.inr ⟨cp, by rw [← hg.payloadOld hom]; exact hcp, hism, hnm, ?_, ?_⟩⟩
      · rw [← hg.get o hom]
        rw [freshClsHeap_get_old ho] at heig ⊢
        exact heig
      · intro k' hmem
        have hkb : k' < (hmidOf h₀ d name).objs.size := by
          by_cases hkb : k' < (hmidOf h₀ d name).objs.size
          · exact hkb
          · exfalso
            have : ancestors (hmidOf h₀ d name) k' = [k'] := by
              unfold ancestors
              rw [anc_go_oob hkb]
              rfl
            rw [this] at hmem
            have hEq := List.mem_singleton.mp hmem
            rw [hmid_size] at hkb
            exact hkb (by rw [← hEq]; exact hch.boot.2.2.2.2)
        have hkm : Boot.objectId ∈ ancestors (freshClsHeap h₀ d name q eO) k' := by
          rw [ClsGrow.ancestors_old hg hchm hsm hkb]; exact hmem
        have := hoff k' hkm
        rw [ClsGrow.ancestors_old hg hchm hsm hkb] at this
        exact this
    · exfalso
      by_cases hok : o = h₀.objs.size
      · subst hok
        rw [freshClsHeap_cp_k] at hcp
        cases hcp
        exact Bool.noConfusion hism
      · by_cases hoe : o = h₀.objs.size + 1
        · subst hoe
          rw [freshClsHeap_cp_e] at hcp
          cases hcp
          exact Bool.noConfusion hism
        · rw [freshClsHeap_cp_oob (Nat.le_of_not_lt
            (fun hlt2 => not_lt_add_two ho hok hoe hlt2))] at hcp
          exact absurd hcp.symm (by simp)

/-- `ModuleNameOk` at the class composite, for a pair the write cannot hit:
    either the names differ, or the pair's owner is not the definee's name. The
    fresh ids are never `ModOwner` witnesses, so every witness is old. -/
theorem moduleNameOkC_fresh (hch : ChainsIn h₀) (hsat : Saturated h₀)
    (hdlt : d < h₀.objs.size) (hqne : ¬ q.isEmpty = true)
    (heOlt : eO < h₀.objs.size)
    (hcls0 : ClassOk h₀)
    {owner nm ownerD : String}
    (hdn : className h₀ d = ownerD)
    (hcase : nm ≠ name ∨ owner ≠ ownerD)
    (hmo : ModuleNameOk h₀ owner nm) :
    ModuleNameOk (freshClsHeap h₀ d name q eO) owner nm := by
  intro o ho
  obtain ⟨holt, hom⟩ := modOwner_freshC_old hch hsat hdlt ho
  have hod : o ≠ d ∨ nm ≠ name := by
    rcases hcase with hnn | hown
    · exact Or.inr hnn
    · left
      intro hEq
      apply hown
      rcases hom with ⟨h1, h2⟩ | ⟨cp, hcp, hism, hnm, heig, hoff⟩
      · rw [h1, ← hdn, ← hEq, h2]
        exact hcls0.1.symm
      · have hnmm := clsName_constSetIn h₀ d o name (Value.ref h₀.objs.size)
        rw [show (hmidOf h₀ d name).classPayload? o = (constSetIn h₀ d name
          (Value.ref h₀.objs.size)).classPayload? o from rfl] at hcp
        rw [hcp] at hnmm
        cases hcp0 : h₀.classPayload? o with
        | none => rw [hcp0] at hnmm; exact absurd hnmm.symm (by simp)
        | some cp0 =>
          rw [hcp0] at hnmm
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hnmm
          rw [← hdn, ← hEq]
          unfold className
          rw [hcp0]
          show owner = (if cp0.name.isEmpty = true then _ else cp0.name)
          rw [if_neg (by rw [hcls0.2.2.2 o cp0 hcp0]; exact Bool.false_ne_true)]
          rw [← hnmm.1]
          exact hnm.symm
  have hoo : ModOwner h₀ owner o := by
    rcases hom with ⟨h1, h2⟩ | ⟨cp, hcp, hism, hnm, heig, hoff⟩
    · exact Or.inl ⟨h1, h2⟩
    · have hcpn := clsName_constSetIn h₀ d o name (Value.ref h₀.objs.size)
      rw [show (hmidOf h₀ d name).classPayload? o
          = (constSetIn h₀ d name (Value.ref h₀.objs.size)).classPayload? o from rfl,
        hcp] at hcpn
      cases hcp0 : h₀.classPayload? o with
      | none => rw [hcp0] at hcpn; exact absurd hcpn (by simp)
      | some cp0 =>
        rw [hcp0] at hcpn
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hcpn
        refine Or.inr ⟨cp0, hcp0, by rw [← hcpn.2]; exact hism,
          by rw [← hcpn.1]; exact hnm, ?_, fun k' hmem => ?_⟩
        · rw [← (get_constSetIn_fields h₀ d name (Value.ref h₀.objs.size) o).2.2.1]
          exact heig
        · have := hoff k' (by rw [ancestors_constSetIn]; exact hmem)
          rw [ancestors_constSetIn] at this
          exact this
  have homm : o < (hmidOf h₀ d name).objs.size := by rw [hmid_size]; exact holt
  have hg : ClsGrow (hmidOf h₀ d name) (freshClsHeap h₀ d name q eO) :=
    clsGrow_hmid_freshC
  have hcoeq : constOwn (freshClsHeap h₀ d name q eO) o nm = constOwn h₀ o nm := by
    rw [ClsGrow.constOwn_old hg homm]
    show constOwn (constSetIn h₀ d name (Value.ref h₀.objs.size)) o nm = _
    rcases hod with hone | hnn
    · exact constOwn_constSetIn_ne h₀ d o name nm _ (Or.inl (by exact hone))
    · exact constOwn_constSetIn_ne h₀ d o name nm _ (Or.inr hnn)
  rcases hmo o hoo with hnone | ⟨kk, cp, hco, hcp, hism, hqn, heig, hoff, hlt⟩
  · left; rw [hcoeq]; exact hnone
  · right
    have hcpH : (freshClsHeap h₀ d name q eO).classPayload? kk
        = (hmidOf h₀ d name).classPayload? kk := by
      unfold Heap.classPayload?; rw [freshClsHeap_get_old hlt]
    have hnmm := clsName_constSetIn h₀ d kk name (Value.ref h₀.objs.size)
    rw [hcp] at hnmm
    cases hcp1 : (hmidOf h₀ d name).classPayload? kk with
    | none =>
      rw [show (hmidOf h₀ d name).classPayload? kk = (constSetIn h₀ d name
        (Value.ref h₀.objs.size)).classPayload? kk from rfl] at hcp1
      rw [hcp1] at hnmm
      exact absurd hnmm.symm (by simp)
    | some cp1 =>
      rw [show (hmidOf h₀ d name).classPayload? kk = (constSetIn h₀ d name
        (Value.ref h₀.objs.size)).classPayload? kk from rfl] at hcp1
      rw [hcp1] at hnmm
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hnmm
      refine ⟨kk, cp1, by rw [hcoeq]; exact hco, by rw [hcpH]; exact hcp1,
        by rw [hnmm.2]; exact hism, by rw [hnmm.1]; exact hqn, ?_, ?_, ?_⟩
      · rw [show ((freshClsHeap h₀ d name q eO).get kk).eigen
            = ((hmidOf h₀ d name).get kk).eigen from by rw [freshClsHeap_get_old hlt]]
        rw [(get_constSetIn_fields h₀ d name (Value.ref h₀.objs.size) kk).2.2.1]
        exact heig
      · exact modOffChains_freshC_old hch hsat hdlt heOlt hlt
          (modOffChains_constSetIn hoff)
      · rw [freshClsHeap_size]
        exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hlt)

/-- `ClassNameOk` at the class composite, for a pair the write cannot hit. -/
theorem classNameOkC_fresh (hch : ChainsIn h₀) (hsat : Saturated h₀)
    (hdlt : d < h₀.objs.size) (hqne : ¬ q.isEmpty = true)
    (hcls0 : ClassOk h₀)
    {owner nm ownerD : String}
    (hdn : className h₀ d = ownerD)
    (hcase : nm ≠ name ∨ owner ≠ ownerD)
    (hmo : ClassNameOk h₀ owner nm) :
    ClassNameOk (freshClsHeap h₀ d name q eO) owner nm := by
  intro o ho
  obtain ⟨holt, hom⟩ := modOwner_freshC_old hch hsat hdlt ho
  have hod : o ≠ d ∨ nm ≠ name := by
    rcases hcase with hnn | hown
    · exact Or.inr hnn
    · left
      intro hEq
      apply hown
      rcases hom with ⟨h1, h2⟩ | ⟨cp, hcp, hism, hnm, heig, hoff⟩
      · rw [h1, ← hdn, ← hEq, h2]
        exact hcls0.1.symm
      · have hnmm := clsName_constSetIn h₀ d o name (Value.ref h₀.objs.size)
        rw [show (hmidOf h₀ d name).classPayload? o = (constSetIn h₀ d name
          (Value.ref h₀.objs.size)).classPayload? o from rfl] at hcp
        rw [hcp] at hnmm
        cases hcp0 : h₀.classPayload? o with
        | none => rw [hcp0] at hnmm; exact absurd hnmm.symm (by simp)
        | some cp0 =>
          rw [hcp0] at hnmm
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hnmm
          rw [← hdn, ← hEq]
          unfold className
          rw [hcp0]
          show owner = (if cp0.name.isEmpty = true then _ else cp0.name)
          rw [if_neg (by rw [hcls0.2.2.2 o cp0 hcp0]; exact Bool.false_ne_true)]
          rw [← hnmm.1]
          exact hnm.symm
  have hoo : ModOwner h₀ owner o := by
    rcases hom with ⟨h1, h2⟩ | ⟨cp, hcp, hism, hnm, heig, hoff⟩
    · exact Or.inl ⟨h1, h2⟩
    · have hcpn := clsName_constSetIn h₀ d o name (Value.ref h₀.objs.size)
      rw [show (hmidOf h₀ d name).classPayload? o
          = (constSetIn h₀ d name (Value.ref h₀.objs.size)).classPayload? o from rfl,
        hcp] at hcpn
      cases hcp0 : h₀.classPayload? o with
      | none => rw [hcp0] at hcpn; exact absurd hcpn (by simp)
      | some cp0 =>
        rw [hcp0] at hcpn
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hcpn
        refine Or.inr ⟨cp0, hcp0, by rw [← hcpn.2]; exact hism,
          by rw [← hcpn.1]; exact hnm, ?_, fun k' hmem => ?_⟩
        · rw [← (get_constSetIn_fields h₀ d name (Value.ref h₀.objs.size) o).2.2.1]
          exact heig
        · have := hoff k' (by rw [ancestors_constSetIn]; exact hmem)
          rw [ancestors_constSetIn] at this
          exact this
  have homm : o < (hmidOf h₀ d name).objs.size := by rw [hmid_size]; exact holt
  have hg : ClsGrow (hmidOf h₀ d name) (freshClsHeap h₀ d name q eO) :=
    clsGrow_hmid_freshC
  have hcoeq : constOwn (freshClsHeap h₀ d name q eO) o nm = constOwn h₀ o nm := by
    rw [ClsGrow.constOwn_old hg homm]
    show constOwn (constSetIn h₀ d name (Value.ref h₀.objs.size)) o nm = _
    rcases hod with hone | hnn
    · exact constOwn_constSetIn_ne h₀ d o name nm _ (Or.inl (by exact hone))
    · exact constOwn_constSetIn_ne h₀ d o name nm _ (Or.inr hnn)
  rcases hmo o hoo with hnone | ⟨kk, cp, hco, hcp, hism, hqn, heig, hlt⟩
  · left; rw [hcoeq]; exact hnone
  · right
    have hcpH : (freshClsHeap h₀ d name q eO).classPayload? kk
        = (hmidOf h₀ d name).classPayload? kk := by
      unfold Heap.classPayload?; rw [freshClsHeap_get_old hlt]
    have hnmm := clsName_constSetIn h₀ d kk name (Value.ref h₀.objs.size)
    rw [hcp] at hnmm
    cases hcp1 : (hmidOf h₀ d name).classPayload? kk with
    | none =>
      rw [show (hmidOf h₀ d name).classPayload? kk = (constSetIn h₀ d name
        (Value.ref h₀.objs.size)).classPayload? kk from rfl] at hcp1
      rw [hcp1] at hnmm
      exact absurd hnmm.symm (by simp)
    | some cp1 =>
      rw [show (hmidOf h₀ d name).classPayload? kk = (constSetIn h₀ d name
        (Value.ref h₀.objs.size)).classPayload? kk from rfl] at hcp1
      rw [hcp1] at hnmm
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hnmm
      refine ⟨kk, cp1, by rw [hcoeq]; exact hco, by rw [hcpH]; exact hcp1,
        by rw [hnmm.2]; exact hism, by rw [hnmm.1]; exact hqn, ?_, ?_⟩
      · rw [show ((freshClsHeap h₀ d name q eO).get kk).eigen
            = ((hmidOf h₀ d name).get kk).eigen from by rw [freshClsHeap_get_old hlt]]
        rw [(get_constSetIn_fields h₀ d name (Value.ref h₀.objs.size) kk).2.2.1]
        exact heig
      · rw [freshClsHeap_size]
        exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hlt)

/-- `ClassNameOk` at the class composite, for **the written pair**: the write is
    the hit, and its facts are the fresh class's literals. -/
theorem classNameOk_name_freshC (hch : ChainsIn h₀) (hsat : Saturated h₀)
    (hdlt : d < h₀.objs.size) (hqne : ¬ q.isEmpty = true)
    (hcls0 : ClassOk h₀)
    {owner owner' : String}
    (hdo : (h₀.classPayload? d).isSome = true)
    (hdn : className h₀ d = owner)
    (hqq : q = RubyCore.Types.qualifyMod owner name)
    (hqow : q ≠ owner')
    (hmo : ClassNameOk h₀ owner' name) :
    ClassNameOk (freshClsHeap h₀ d name q eO) owner' name := by
  have hchm : ChainsIn (hmidOf h₀ d name) := chainsIn_hmid hch
  have hsm : Saturated (hmidOf h₀ d name) := saturated_hmid hsat
  have hg : ClsGrow (hmidOf h₀ d name) (freshClsHeap h₀ d name q eO) :=
    clsGrow_hmid_freshC
  intro o ho
  -- fresh ids are not modules, so `o` is old
  have holt : o < h₀.objs.size := by
    rcases ho with ⟨h1, h2⟩ | ⟨cp, hcp, hism, hnm, heig, hoff⟩
    · exact h2 ▸ hch.boot.2.2.2.2
    · by_cases h1 : o < h₀.objs.size
      · exact h1
      · exfalso
        by_cases h2 : o = h₀.objs.size
        · subst h2
          rw [freshClsHeap_cp_k] at hcp
          cases hcp
          exact Bool.noConfusion hism
        · by_cases h3 : o = h₀.objs.size + 1
          · subst h3
            rw [freshClsHeap_cp_e] at hcp
            cases hcp
            exact Bool.noConfusion hism
          · rw [freshClsHeap_cp_oob (Nat.le_of_not_lt
              (fun hlt2 => not_lt_add_two h1 h2 h3 hlt2))] at hcp
            exact absurd hcp.symm (by simp)
  by_cases hod : o = d
  · -- the write's own hit; the pair's owner is pinned to the definee's name
    have howeq : owner' = owner := by
      rcases ho with ⟨h1, h2⟩ | ⟨cp, hcp, hism, hnm, heig, hoff⟩
      · have hdobj : d = Boot.objectId := by rw [← hod, h2]
        rw [h1, ← hdn, hdobj]
        exact hcls0.1.symm
      · rw [← hnm, ← hdn]
        rw [hod] at hcp
        rw [freshClsHeap_cp_old hdlt hdlt] at hcp
        have hnmm := clsName_constSetIn h₀ d d name (Value.ref h₀.objs.size)
        rw [hcp] at hnmm
        cases hcp0 : h₀.classPayload? d with
        | none => rw [hcp0] at hdo; exact absurd hdo (by simp)
        | some cp0 =>
          rw [hcp0] at hnmm
          simp only [Option.map_some, Option.some.injEq] at hnmm
          have hnm0 : cp.name = cp0.name := congrArg Prod.fst hnmm
          unfold className
          rw [hcp0]
          show cp.name = (if cp0.name.isEmpty = true then _ else cp0.name)
          rw [if_neg (by
            rw [hcls0.2.2.2 d cp0 hcp0]
            exact Bool.false_ne_true)]
          exact hnm0
    rw [howeq] at hqow ⊢
    right
    refine ⟨h₀.objs.size,
      { superclass := some Boot.objectId, name := q, isModule := false },
      ?_, freshClsHeap_cp_k, rfl, hqq, ?_, ?_⟩
    · rw [show constOwn (freshClsHeap h₀ d name q eO) o name
          = constOwn (hmidOf h₀ d name) o name from by
        unfold constOwn
        rw [freshClsHeap_cp_old hdlt holt]]
      rw [hod]
      exact constOwn_constSetIn_self hdo hdlt
    · rw [freshClsHeap_get_k]
      rfl
    · rw [freshClsHeap_size]
      exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)
  · -- some other owner-named object: the old fact, values pinned (`o ≠ d`)
    have homm : o < (hmidOf h₀ d name).objs.size := by rw [hmid_size]; exact holt
    have hoo : ModOwner h₀ owner' o := by
      rcases ho with ⟨h1, h2⟩ | ⟨cp, hcp, hism, hnm, heig, hoff⟩
      · exact Or.inl ⟨h1, h2⟩
      · rw [freshClsHeap_cp_old hdlt holt] at hcp
        have hcpn := payload_constSetIn_ne h₀ d name (Value.ref h₀.objs.size) o hod
        have hcp0 : h₀.classPayload? o = some cp := by
          unfold Heap.classPayload? at hcp ⊢
          rw [← hcpn]
          exact hcp
        refine Or.inr ⟨cp, hcp0, hism, hnm, ?_, ?_⟩
        · rw [← (get_constSetIn_fields h₀ d name (Value.ref h₀.objs.size) o).2.2.1]
          rw [freshClsHeap_get_old holt] at heig
          exact heig
        · intro k' hmem
          have hkb : k' < h₀.objs.size := by
            by_cases hkb : k' < h₀.objs.size
            · exact hkb
            · exfalso
              have hanc : ancestors h₀ k' = [k'] := by
                unfold ancestors
                rw [anc_go_oob hkb]
                rfl
              rw [hanc] at hmem
              have hEq := List.mem_singleton.mp hmem
              exact hkb (by rw [← hEq]; exact hch.boot.2.2.2.2)
          have hkm : k' < (hmidOf h₀ d name).objs.size := by
            rw [hmid_size]; exact hkb
          have := hoff k' (by
            rw [ClsGrow.ancestors_old hg hchm hsm hkm,
              ancestors_constSetIn h₀ d k' name]
            exact hmem)
          rw [ClsGrow.ancestors_old hg hchm hsm hkm,
            ancestors_constSetIn h₀ d k' name] at this
          exact this
    rcases hmo o hoo with hnone | ⟨kk, cp, hco, hcp, hism, hqn, heig, hlt⟩
    · left
      rw [ClsGrow.constOwn_old hg homm]
      rw [constOwn_constSetIn_ne h₀ d o name name (Value.ref h₀.objs.size) (Or.inl hod)]
      exact hnone
    · right
      have hkkm : kk < (hmidOf h₀ d name).objs.size := by rw [hmid_size]; exact hlt
      have hnmm := clsName_constSetIn h₀ d kk name (Value.ref h₀.objs.size)
      rw [hcp] at hnmm
      obtain ⟨cp2, hcp2⟩ : ∃ cp2, (hmidOf h₀ d name).classPayload? kk = some cp2 := by
        cases hx : (hmidOf h₀ d name).classPayload? kk with
        | none => rw [hx] at hnmm; exact absurd hnmm.symm (by simp)
        | some c2 => exact ⟨c2, rfl⟩
      rw [hcp2] at hnmm
      simp only [Option.map_some, Option.some.injEq] at hnmm
      refine ⟨kk, cp2, ?_,
        by rw [hg.payloadOld hkkm]; exact hcp2,
        by rw [show cp2.isModule = cp.isModule from congrArg Prod.snd hnmm]
           exact hism,
        by rw [show cp2.name = cp.name from congrArg Prod.fst hnmm]
           exact hqn, ?_, ?_⟩
      · rw [ClsGrow.constOwn_old hg homm]
        rw [constOwn_constSetIn_ne h₀ d o name name (Value.ref h₀.objs.size) (Or.inl hod)]
        exact hco
      · have he1 : ((freshClsHeap h₀ d name q eO).get kk).eigen
            = ((hmidOf h₀ d name).get kk).eigen :=
          congrArg Object.eigen (hg.get kk hkkm)
        have he2 : ((hmidOf h₀ d name).get kk).eigen = (h₀.get kk).eigen :=
          (get_constSetIn_fields h₀ d name (Value.ref h₀.objs.size) kk).2.2.1
        rw [he1, he2]
        exact heig
      · rw [freshClsHeap_size]
        exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hlt)

/-- **The table invariant at the class composite** — every clause assembled. -/
theorem declsOkJC_fresh {A : SemAxioms} {D : Decls}
    (hch : ChainsIn h₀) (hsat : Saturated h₀) (hdlt : d < h₀.objs.size)
    (hqne : ¬ q.isEmpty = true)
    (heOlt : eO < h₀.objs.size)
    (hcls0 : ClassOk h₀)
    (hcO : ClassOk (hmidOf h₀ d name)) (hnoO : NoHook (hmidOf h₀ d name))
    (htab : DeclsOkJ A D h₀)
    (hct : constTy? D name = none)
    (hsct : ∀ cn, scopedConstTy? D cn name = none)
    (hdfr : declClsFresh D q name = true)
    {owner : String}
    (hdo : (h₀.classPayload? d).isSome = true)
    (hdn : className h₀ d = owner)
    (hqq : q = RubyCore.Types.qualifyMod owner name)
    -- the write must not hit a declared *module* pair of the same owner
    (hmodg : ∀ pr ∈ D.modules, ¬(pr.1 = owner ∧ pr.2 = name)) :
    DeclsOkJ A D (freshClsHeap h₀ d name q eO) := by
  obtain ⟨hkR, hkI, hkS, hkP, hkM, hkC⟩ := declClsFresh_sound hdfr
  have hmidsuite := constSetIn_rowsAndConstsJ
    (v := Value.ref h₀.objs.size) (j := d) htab hct hsct
  refine ⟨?_, ?_, ?_, ?_, ?_, htab.2.2.2.2.2.1, htab.2.2.2.2.2.2.1,
    htab.2.2.2.2.2.2.2.1, ?_, ?_⟩
  · intro τr mname dd hf
    obtain ⟨hnee, hkeys⟩ := declFor_keys hf
    exact entryOkJ_freshC hch hsat hdlt hqne hcO hnoO
      (fun c hc => by obtain ⟨rs, hrs⟩ := hkeys c hc; exact hkR (c, rs) hrs)
      hnee (hmidsuite.1 τr mname dd hf)
  · exact fun n τ hn => constOk_freshC hch hsat hdlt (hmidsuite.2.1 n τ hn)
  · exact fun c x τ hn => ivarOk_freshC hch hsat hdlt (hmidsuite.2.2.1 c x τ hn)
  · intro c n τ hn
    refine scopedConstOk_freshC hch hsat hdlt hqne ?_ (hmidsuite.2.2.2.1 c n τ hn)
    have hn' := hn
    unfold scopedConstTy? at hn'
    cases hfind : D.scopedConsts.find? (·.1 == (c, n)) with
    | none => rw [hfind] at hn'; exact absurd hn' (by simp)
    | some e =>
      have hmem := List.mem_of_find?_eq_some hfind
      have hp := List.find?_some hfind
      simp only [beq_iff_eq] at hp
      have := hkS e hmem
      rw [hp] at this
      exact this
  · intro c n dd hn
    refine superOk_freshC hch hsat hdlt hqne heOlt ?_ (hmidsuite.2.2.2.2 c n dd hn)
    have hn' := hn
    unfold superDecl? at hn'
    cases hfind : D.supers.find? (·.1 == (c, n)) with
    | none => rw [hfind] at hn'; exact absurd hn' (by simp)
    | some e =>
      have hmem := List.mem_of_find?_eq_some hfind
      have hp := List.find?_some hfind
      simp only [beq_iff_eq] at hp
      have := hkP e hmem
      rw [hp] at this
      exact this
  · -- the modules clause: fresh ids are never witnesses; the write is barred
    -- from every declared module pair by the rule's collision guard.
    intro pr hpr
    by_cases hnm : pr.2 = name
    · refine moduleNameOkC_fresh hch hsat hdlt hqne heOlt hcls0 hdn
        (Or.inr ?_) (htab.2.2.2.2.2.2.2.2.1 pr hpr)
      intro hEq
      exact hmodg pr hpr ⟨hEq, hnm⟩
    · exact moduleNameOkC_fresh hch hsat hdlt hqne heOlt hcls0 hdn
        (Or.inl hnm) (htab.2.2.2.2.2.2.2.2.1 pr hpr)
  · -- the classes clause: the written pair is the hit; the rest transport.
    intro pr hpr
    have hkey := hkC pr hpr
    by_cases hnm : pr.2 = name
    · have hown : pr.1 ≠ q := by
        rcases hkey.1 with h | h
        · exact h
        · exact absurd hnm h
      rw [hnm]
      exact classNameOk_name_freshC hch hsat hdlt hqne hcls0 hdo hdn hqq
        (Ne.symm hown) (hnm ▸ htab.2.2.2.2.2.2.2.2.2 pr hpr)
    · exact classNameOkC_fresh hch hsat hdlt hqne hcls0 hdn
        (Or.inl hnm) (htab.2.2.2.2.2.2.2.2.2 pr hpr)

end TableC

end Judgment
end Proof
end RubyCore
