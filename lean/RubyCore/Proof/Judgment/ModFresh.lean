import RubyCore.Proof.Judgment.Konts
import RubyCore.Proof.Judgment.ClsInv

/-!
# J48 — the fresh-module composite (`module'`'s allocating branch)

`enterClassBody`'s miss path performs, in order: allocate the module object
(`k := h₀.size`), register it as a constant of the definee (`constSetIn` at the
*old* id `d`), allocate its eigenclass (`e := h₀.size + 1`, eagerly — the fact
J44c carries from birth), set the module's `eigen` field (a write at the fresh
`k`), and push the class-body frame.

Proof strategy (the J43c note, cashed): the register-write **commutes** with the
allocations (`constSetIn_alloc_comm` — a push and a set at an in-bounds index
touch different slots), so the composite factors as *two pushes and one
fresh-id set over* `hmid := constSetIn h₀ d name (.ref k)`. `ClsGrow hmid h₄`
is then structural, the J43d–f congruence stack transports everything old
across it, the J41 `constSetIn` suite carries `h₀ → hmid`, and the fresh ids'
facts are literals of the two objects.
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

/-- The module object the fresh path allocates. -/
@[reducible] def modObj (q : String) : Object :=
  { klass := Boot.moduleId,
    payload := .cls { superclass := none, name := q, isModule := true } }

/-- Its eigenclass (allocated eagerly; the machine names it by `anyToS`, which
    for a class object with a nonempty name is that name). -/
@[reducible] def eigObj (q : String) : Object :=
  { klass := Boot.classId,
    payload := .cls { superclass := some Boot.classId,
                      name := "#<Class:" ++ q ++ ">", isModule := false } }

/-- The module object once its eigenclass is realized. -/
@[reducible] def modObjE (q : String) (e : ObjId) : Object :=
  { modObj q with eigen := some e }

/-! ## Array facts -/

theorem objs_getD_push_lt (a : Array Object) (x : Object) (o : Nat)
    (ho : o < a.size) : (a.push x).getD o default = a.getD o default := by
  simp only [Array.getD]
  rw [dif_pos (by rw [Array.size_push]; omega), dif_pos ho]
  exact Array.getElem_push_lt ho

theorem objs_getD_push_self (a : Array Object) (x : Object) :
    (a.push x).getD a.size default = x := by
  simp only [Array.getD]
  rw [dif_pos (by rw [Array.size_push]; omega)]
  simp

/-- A push and a `set!` at an in-bounds index touch different slots. -/
theorem push_set!_comm (a : Array Object) (x : Object) (i : Nat) (y : Object)
    (hi : i < a.size) : (a.push x).set! i y = (a.set! i y).push x := by
  apply Array.ext
  · simp [Array.set!]
  · intro j hj₁ hj₂
    simp only [Array.set!] at hj₁ hj₂ ⊢
    have hj : j < a.size + 1 := by
      simpa [Array.size_setIfInBounds, Array.size_push] using hj₁
    rw [Array.getElem_setIfInBounds (by simpa [Array.size_push] using hj),
      Array.getElem_push (h := hj₂)]
    by_cases hji : i = j
    · subst hji
      rw [if_pos rfl, dif_pos (by simpa [Array.size_setIfInBounds] using hi),
        Array.getElem_setIfInBounds hi, if_pos rfl]
    · rw [if_neg hji]
      by_cases hjs : j < a.size
      · rw [dif_pos (by simpa [Array.size_setIfInBounds] using hjs),
          Array.getElem_setIfInBounds hjs, if_neg hji,
          Array.getElem_push (h := by simpa [Array.size_push] using hj), dif_pos hjs]
      · rw [dif_neg (by simpa [Array.size_setIfInBounds] using hjs),
          Array.getElem_push (h := by simpa [Array.size_push] using hj), dif_neg hjs]

/-- `constSetIn` at an old id commutes past an allocation. -/
theorem constSetIn_alloc_comm (h : Heap) (obj : Object) (d : ObjId)
    (name : String) (v : Value) (hdlt : d < h.objs.size) :
    constSetIn (h.alloc obj).2 d name v = ((constSetIn h d name v).alloc obj).2 := by
  have hget : (h.alloc obj).2.get d = h.get d := by
    show (h.objs.push obj).getD d default = h.objs.getD d default
    exact objs_getD_push_lt h.objs obj d hdlt
  have hcp : (h.alloc obj).2.classPayload? d = h.classPayload? d := by
    unfold Heap.classPayload?
    rw [hget]
  unfold constSetIn
  rw [hcp]
  cases hc : h.classPayload? d with
  | none => rfl
  | some c =>
    unfold Heap.setClassPayload Heap.set
    rw [hget]
    show (⟨((h.objs.push obj).set! d _)⟩ : Heap) = ⟨(h.objs.set! d _).push obj⟩
    rw [push_set!_comm h.objs obj d _ hdlt]

/-! ## The composite, factored over `hmid` -/

/-- The register-write, factored to the front. -/
@[reducible] def hmidOf (h₀ : Heap) (d : ObjId) (name : String) : Heap :=
  constSetIn h₀ d name (.ref h₀.objs.size)

theorem hmid_size (h₀ : Heap) (d : ObjId) (name : String) :
    (hmidOf h₀ d name).objs.size = h₀.objs.size := objs_size_constSetIn h₀ d name _

/-- The composite heap, in the factored spelling the transports read: two
    pushes and a fresh-id `set!` over `hmid`. `freshModHeap_machine` ties it to
    the order the machine actually computes in. -/
def freshModHeap (h₀ : Heap) (d : ObjId) (name q : String) : Heap :=
  ⟨(((hmidOf h₀ d name).objs.push (modObj q)).push (eigObj q)).set!
      h₀.objs.size (modObjE q (h₀.objs.size + 1))⟩

/-- **The factoring**: the machine's alloc → register → alloc → eigen-set order
    equals the factored composite. -/
theorem freshModHeap_machine (h₀ : Heap) (d : ObjId) (name q : String)
    (hdlt : d < h₀.objs.size) :
    ((constSetIn (h₀.alloc (modObj q)).2 d name (.ref h₀.objs.size)).alloc
        (eigObj q)).2.set h₀.objs.size
      { ((constSetIn (h₀.alloc (modObj q)).2 d name (.ref h₀.objs.size)).alloc
          (eigObj q)).2.get h₀.objs.size with
        eigen := some (constSetIn (h₀.alloc (modObj q)).2 d name
          (.ref h₀.objs.size)).objs.size } =
      freshModHeap h₀ d name q := by
  rw [constSetIn_alloc_comm _ _ _ _ _ hdlt]
  show (((hmidOf h₀ d name).alloc (modObj q)).2.alloc (eigObj q)).2.set h₀.objs.size
      { (((hmidOf h₀ d name).alloc (modObj q)).2.alloc (eigObj q)).2.get h₀.objs.size with
        eigen := some ((hmidOf h₀ d name).alloc (modObj q)).2.objs.size } =
    freshModHeap h₀ d name q
  have hsz2 : ((hmidOf h₀ d name).alloc (modObj q)).2.objs.size
      = h₀.objs.size + 1 := by
    show ((hmidOf h₀ d name).objs.push (modObj q)).size = _
    rw [Array.size_push, hmid_size]
  have hgetk : (((hmidOf h₀ d name).alloc (modObj q)).2.alloc (eigObj q)).2.get
      h₀.objs.size = modObj q := by
    show (((hmidOf h₀ d name).objs.push (modObj q)).push (eigObj q)).getD
        h₀.objs.size default = modObj q
    rw [objs_getD_push_lt _ _ h₀.objs.size (by rw [Array.size_push, hmid_size]; omega),
      show h₀.objs.size = (hmidOf h₀ d name).objs.size from (hmid_size h₀ d name).symm,
      objs_getD_push_self]
  rw [hgetk, hsz2]
  rfl

/-! ## The step, reduced -/

/-- The frame the fresh path pushes. -/
def freshModFrame (k : ObjId) (cref₀ : List ObjId) : Frame :=
  { self := .ref k, defmod := k, kind := .classBody, cref := k :: cref₀ }

/-- The successor machine, whole. -/
def freshModMachine (m : Machine) (name q : String) (body : Expr) : Machine :=
  { m with
    heap := freshModHeap m.heap m.currentFrame.defmod name q,
    frames := m.frames.push (freshModFrame m.heap.objs.size m.currentFrame.cref),
    stack := m.frames.size :: m.stack,
    kont := .frameK m.frames.size :: m.kont,
    ctl := .eval body }

theorem h2_get_k {m : Machine} {name q : String}
    (hdlt : m.currentFrame.defmod < m.heap.objs.size) :
    (constSetIn (m.heap.alloc (modObj q)).2 m.currentFrame.defmod name
      (.ref m.heap.objs.size)).get m.heap.objs.size = modObj q := by
  rw [get_constSetIn_ne _ _ _ _ _ (fun hEq => absurd hEq.symm (Nat.ne_of_lt hdlt))]
  show (m.heap.objs.push (modObj q)).getD m.heap.objs.size default = modObj q
  exact objs_getD_push_self _ _

/-- Attach an eigenclass id to an object in place. -/
def attachEigen (h : Heap) (o e : ObjId) : Heap :=
  h.set o { h.get o with eigen := some e }

/-- `eigenclassOf` at the just-allocated module: one unfold — the eigen is
    `none`, the superclass is `none`, so the metaclass parent is `Class` and one
    eigenclass is allocated and attached. -/
theorem eigenclassOf_modObj {mm : Machine} {o : ObjId} {q : String}
    (hget : mm.heap.get o = modObj q)
    (hany : anyToS mm.heap o = q) :
    eigenclassOf mm o =
      (mm.heap.objs.size,
       { mm with heap := (attachEigen (mm.heap.alloc (eigObj q)).2 o mm.heap.objs.size) }) := by
  show eigenclassOf.go mm o (mm.heap.objs.size + 1) = _
  unfold eigenclassOf.go
  rw [hget]
  simp only [modObj, eigObj, hany, attachEigen]
  rfl

set_option maxHeartbeats 4000000 in
/-- The fresh path of `evalExpr` on `module'`, reduced to the explicit machine.
    `hq` ties the machine's qualified-name computation to the rule's spelling. -/
theorem evalExpr_module_fresh {m : Machine} {name q : String} {body : Expr}
    (hmiss : constOwn m.heap m.currentFrame.defmod name = none)
    (hdlt : m.currentFrame.defmod < m.heap.objs.size)
    (hq : (if m.currentFrame.defmod == Boot.objectId then name
           else className m.heap m.currentFrame.defmod ++ "::" ++ name) = q)
    (hqne : ¬ q.isEmpty = true) :
    evalExpr m (.module' name body) =
      .next (freshModMachine m name q body) := by
  have hqq : (if m.currentFrame.defmod == Boot.objectId then name
      else s!"{className m.heap m.currentFrame.defmod}::{name}") = q := by
    rw [← hq]
    split <;> rfl
  have hg2k := h2_get_k (m := m) (name := name) (q := q) hdlt
  have hcls2 : className (constSetIn (m.heap.alloc (modObj q)).2
      m.currentFrame.defmod name (.ref m.heap.objs.size)) m.heap.objs.size = q := by
    unfold className Heap.classPayload?
    rw [hg2k]
    show (if q.isEmpty then _ else q) = q
    rw [if_neg hqne]
  have hany : anyToS (constSetIn (m.heap.alloc (modObj q)).2
      m.currentFrame.defmod name (.ref m.heap.objs.size)) m.heap.objs.size = q := by
    unfold anyToS Heap.classPayload?
    rw [hg2k]
    exact hcls2
  have hsz2 : (constSetIn (m.heap.alloc (modObj q)).2 m.currentFrame.defmod name
      (.ref m.heap.objs.size)).objs.size = m.heap.objs.size + 1 := by
    rw [objs_size_constSetIn]
    simp [Heap.alloc]
  simp only [evalExpr, enterClassBody, hmiss, hqq, if_true]
  simp only [show ∀ ob : Object, (m.heap.alloc ob).1 = m.heap.objs.size from fun _ => rfl]
  simp only [modObj, eigObj] at hg2k hany ⊢
  rw [eigenclassOf_modObj
    (mm := { m with heap := (constSetIn (m.heap.alloc (modObj q)).2
      m.currentFrame.defmod name (.ref m.heap.objs.size)) }) hg2k hany]
  show StepResult.next (withKont
      { m with
        heap := (attachEigen ((constSetIn (m.heap.alloc (modObj q)).2
            m.currentFrame.defmod name (.ref m.heap.objs.size)).alloc (eigObj q)).2
          m.heap.objs.size
          (constSetIn (m.heap.alloc (modObj q)).2 m.currentFrame.defmod name
            (.ref m.heap.objs.size)).objs.size),
        frames := m.frames.push (freshModFrame m.heap.objs.size m.currentFrame.cref),
        stack := m.frames.size :: m.stack }
      (.eval body) (.frameK m.frames.size)) =
    StepResult.next (freshModMachine m name q body)
  rw [show (attachEigen ((constSetIn (m.heap.alloc (modObj q)).2
      m.currentFrame.defmod name (.ref m.heap.objs.size)).alloc (eigObj q)).2
      m.heap.objs.size
      (constSetIn (m.heap.alloc (modObj q)).2 m.currentFrame.defmod name
        (.ref m.heap.objs.size)).objs.size)
      = freshModHeap m.heap m.currentFrame.defmod name q
    from freshModHeap_machine m.heap m.currentFrame.defmod name q hdlt]
  rfl

/-! ## Reading the composite -/

section Reads

variable {h₀ : Heap} {d : ObjId} {name q : String}

theorem freshModHeap_size :
    (freshModHeap h₀ d name q).objs.size = h₀.objs.size + 2 := by
  show ((((hmidOf h₀ d name).objs.push (modObj q)).push (eigObj q)).set! _ _).size = _
  simp [Array.set!, Array.size_setIfInBounds, Array.size_push, hmid_size,
    show ((hmidOf h₀ d name).objs.size = h₀.objs.size) from hmid_size h₀ d name]

theorem freshModHeap_get_old {o : ObjId} (ho : o < h₀.objs.size) :
    (freshModHeap h₀ d name q).get o = (hmidOf h₀ d name).get o := by
  show ((((hmidOf h₀ d name).objs.push (modObj q)).push (eigObj q)).set!
      h₀.objs.size _).getD o default = (hmidOf h₀ d name).objs.getD o default
  rw [objs_getD_set!_ne _ _ _ _ (Nat.ne_of_lt ho),
    objs_getD_push_lt _ _ o (by rw [Array.size_push, hmid_size]; exact Nat.lt_succ_of_lt ho),
    objs_getD_push_lt _ _ o (by rw [hmid_size]; exact ho)]

theorem freshModHeap_get_k :
    (freshModHeap h₀ d name q).get h₀.objs.size = modObjE q (h₀.objs.size + 1) := by
  show ((((hmidOf h₀ d name).objs.push (modObj q)).push (eigObj q)).set!
      h₀.objs.size _).getD h₀.objs.size default = _
  rw [objs_getD_set!_self _ _ _
    (by rw [Array.size_push, Array.size_push, hmid_size]; omega)]

theorem freshModHeap_get_e :
    (freshModHeap h₀ d name q).get (h₀.objs.size + 1) = eigObj q := by
  show ((((hmidOf h₀ d name).objs.push (modObj q)).push (eigObj q)).set!
      h₀.objs.size _).getD (h₀.objs.size + 1) default = _
  rw [objs_getD_set!_ne _ _ _ _ (by omega),
    show h₀.objs.size + 1 = ((hmidOf h₀ d name).objs.push (modObj q)).size by
      rw [Array.size_push, hmid_size],
    objs_getD_push_self]

/-- The J43 relation, delivered: old ids read as in `hmid`. -/
theorem clsGrow_hmid_fresh : ClsGrow (hmidOf h₀ d name) (freshModHeap h₀ d name q) :=
  ⟨by rw [freshModHeap_size, hmid_size]; omega,
   fun o ho => freshModHeap_get_old (by rwa [hmid_size h₀ d name] at ho)⟩

theorem freshModHeap_cp_k :
    (freshModHeap h₀ d name q).classPayload? h₀.objs.size =
      some { superclass := none, name := q, isModule := true } := by
  unfold Heap.classPayload?
  rw [freshModHeap_get_k]

theorem freshModHeap_cp_e :
    (freshModHeap h₀ d name q).classPayload? (h₀.objs.size + 1) =
      some { superclass := some Boot.classId,
             name := "#<Class:" ++ q ++ ">", isModule := false } := by
  unfold Heap.classPayload?
  rw [freshModHeap_get_e]

theorem freshModHeap_cp_oob {o : ObjId} (ho : h₀.objs.size + 2 ≤ o) :
    (freshModHeap h₀ d name q).classPayload? o = none := by
  apply classPayload?_oob
  rw [freshModHeap_size]
  exact Nat.not_lt.mpr ho

end Reads

/-! ## Chains at the composite -/

section Chains

variable {h₀ : Heap} {d : ObjId} {name q : String}

theorem freshModHeap_modanc_go_k (f : Nat) :
    modAncestors.go (freshModHeap h₀ d name q) h₀.objs.size (f + 1)
      = [h₀.objs.size] := by
  rw [modAncestors.go.eq_def]
  rw [freshModHeap_cp_k]
  simp

theorem freshModHeap_modanc_go_e (f : Nat) :
    modAncestors.go (freshModHeap h₀ d name q) (h₀.objs.size + 1) (f + 1)
      = [h₀.objs.size + 1] := by
  rw [modAncestors.go.eq_def]
  rw [freshModHeap_cp_e]
  simp

theorem freshModHeap_anc_go_k (f : Nat) :
    ancestors.go (freshModHeap h₀ d name q) h₀.objs.size (f + 1)
      = [h₀.objs.size] := by
  rw [ancestors.go.eq_def]
  rw [freshModHeap_cp_k]
  simp

theorem freshModHeap_anc_go_e (f : Nat) :
    ancestors.go (freshModHeap h₀ d name q) (h₀.objs.size + 1) (f + 1)
      = (h₀.objs.size + 1) ::
        ancestors.go (freshModHeap h₀ d name q) Boot.classId f := by
  rw [ancestors.go.eq_def]
  rw [freshModHeap_cp_e]
  simp

theorem modanc_go_oob {h : Heap} {o : ObjId} (ho : ¬ o < h.objs.size) (f : Nat) :
    modAncestors.go h o (f + 1) = [o] := by
  rw [modAncestors.go.eq_def]
  rw [classPayload?_oob h o ho]

theorem anc_go_oob {h : Heap} {o : ObjId} (ho : ¬ o < h.objs.size) (f : Nat) :
    ancestors.go h o (f + 1) = [o] := by
  rw [ancestors.go.eq_def]
  rw [classPayload?_oob h o ho]

theorem not_lt_add_two {a s : Nat} (h1 : ¬ a < s) (h2 : a ≠ s) (h3 : a ≠ s + 1) :
    ¬ a < s + 2 := by
  intro h4
  rcases Nat.eq_or_lt_of_le (Nat.le_of_not_lt h1) with h | h
  · exact h2 h.symm
  · rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt h) with h7 | h7
    · exact h3 h7.symm
    · exact Nat.not_lt.mpr (Nat.succ_le_of_lt h7) (by simpa using h4)

theorem chainsIn_hmid (hch : ChainsIn h₀) : ChainsIn (hmidOf h₀ d name) :=
  chainsIn_constSetIn hch

theorem saturated_hmid (hsat : Saturated h₀) : Saturated (hmidOf h₀ d name) :=
  saturated_constSetIn hsat

/-- `Saturated` at the composite: old walks are `hmid`'s (fuel-lifted), fresh
    walks are literals. -/
theorem saturated_fresh (hch : ChainsIn h₀) (hsat : Saturated h₀)
    (hdlt : d < h₀.objs.size) :
    Saturated (freshModHeap h₀ d name q) := by
  have hchm : ChainsIn (hmidOf h₀ d name) := chainsIn_hmid hch
  have hsm : Saturated (hmidOf h₀ d name) := saturated_hmid hsat
  have hg : ClsGrow (hmidOf h₀ d name) (freshModHeap h₀ d name q) :=
    clsGrow_hmid_fresh
  have hszH : (freshModHeap h₀ d name q).objs.size = h₀.objs.size + 2 :=
    freshModHeap_size
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
    · have hold : ∀ f, modAncestors.go (freshModHeap h₀ d name q) mo f
          = modAncestors.go (hmidOf h₀ d name) mo f :=
        fun f => ClsGrow.modAncestors_go_old hg hchm f mo (hszm ▸ hmo)
      have hL := (hold _).trans (modAncestors_go_ge hsm.1 hb1 mo)
      have hR := (hold _).trans (modAncestors_go_ge hsm.1 hb2 mo)
      exact hL.trans hR.symm
    · by_cases hk : mo = h₀.objs.size
      · subst hk
        exact (freshModHeap_modanc_go_k (h₀.objs.size + 2)).trans
          (freshModHeap_modanc_go_k (h₀.objs.size + 1)).symm
      · by_cases he : mo = h₀.objs.size + 1
        · subst he
          exact (freshModHeap_modanc_go_e (h₀.objs.size + 2)).trans
            (freshModHeap_modanc_go_e (h₀.objs.size + 1)).symm
        · have hoob : ¬ mo < (freshModHeap h₀ d name q).objs.size := by
            rw [hszH]
            exact not_lt_add_two hmo hk he
          exact (modanc_go_oob hoob (h₀.objs.size + 2)).trans
            (modanc_go_oob hoob (h₀.objs.size + 1)).symm
  · intro k'
    rw [hszH]
    by_cases hmo : k' < h₀.objs.size
    · have hold : ∀ f, ancestors.go (freshModHeap h₀ d name q) k' f
          = ancestors.go (hmidOf h₀ d name) k' f :=
        fun f => ClsGrow.ancestors_go_old hg hchm hsm f k' (hszm ▸ hmo)
      have hL := (hold _).trans (ancestors_go_ge hsm.2 hb1 k')
      have hR := (hold _).trans (ancestors_go_ge hsm.2 hb2 k')
      exact hL.trans hR.symm
    · by_cases hk : k' = h₀.objs.size
      · subst hk
        exact (freshModHeap_anc_go_k (h₀.objs.size + 2)).trans
          (freshModHeap_anc_go_k (h₀.objs.size + 1)).symm
      · by_cases he : k' = h₀.objs.size + 1
        · subst he
          have hcb : Boot.classId < h₀.objs.size := hch.boot.1
          have hold : ∀ f, ancestors.go (freshModHeap h₀ d name q) Boot.classId f
              = ancestors.go (hmidOf h₀ d name) Boot.classId f :=
            fun f => ClsGrow.ancestors_go_old hg hchm hsm f Boot.classId
              (hszm ▸ hcb)
          have hT1 := (hold (h₀.objs.size + 2)).trans (ancestors_go_ge hsm.2 hb2 Boot.classId)
          have hT2 := (hold (h₀.objs.size + 1)).trans (ancestors_go_ge hsm.2 hb3 Boot.classId)
          rw [freshModHeap_anc_go_e (h₀.objs.size + 2),
            freshModHeap_anc_go_e (h₀.objs.size + 1), hT1, hT2]
        · have hoob : ¬ k' < (freshModHeap h₀ d name q).objs.size := by
            rw [hszH]
            exact not_lt_add_two hmo hk he
          exact (anc_go_oob hoob (h₀.objs.size + 2)).trans
            (anc_go_oob hoob (h₀.objs.size + 1)).symm

/-- `ChainsIn` at the composite: old edges are `hmid`'s, fresh edges are boot
    ids and the fresh eigenclass. -/
theorem chainsIn_fresh (hch : ChainsIn h₀) (hdlt : d < h₀.objs.size) :
    ChainsIn (freshModHeap h₀ d name q) := by
  have hchm : ChainsIn (hmidOf h₀ d name) := chainsIn_hmid hch
  have hszH : (freshModHeap h₀ d name q).objs.size = h₀.objs.size + 2 :=
    freshModHeap_size
  have hszm : (hmidOf h₀ d name).objs.size = h₀.objs.size := hmid_size h₀ d name
  have hbound : ∀ x, x < h₀.objs.size → x < (freshModHeap h₀ d name q).objs.size := by
    intro x hx; rw [hszH]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hx)
  refine ⟨⟨hbound _ hch.boot.1, hbound _ hch.boot.2.1, hbound _ hch.boot.2.2.1,
    hbound _ hch.boot.2.2.2.1, hbound _ hch.boot.2.2.2.2⟩,
    fun o hlt => ?_, fun o hlt e' he' => ?_, fun o cp hlt hcp => ?_⟩
  · by_cases ho : o < h₀.objs.size
    · rw [freshModHeap_get_old ho, (get_constSetIn_fields h₀ d name _ o).2.1]
      exact hbound _ (hch.klass o ho)
    · by_cases hk : o = h₀.objs.size
      · subst hk; rw [freshModHeap_get_k]; exact hbound _ hch.boot.2.1
      · by_cases he2 : o = h₀.objs.size + 1
        · subst he2; rw [freshModHeap_get_e]; exact hbound _ hch.boot.1
        · exact absurd hlt (by rw [hszH]; exact not_lt_add_two ho hk he2)
  · by_cases ho : o < h₀.objs.size
    · rw [freshModHeap_get_old ho, (get_constSetIn_fields h₀ d name _ o).2.2.1] at he'
      exact hbound _ (hch.eigen o ho e' he')
    · by_cases hk : o = h₀.objs.size
      · subst hk
        rw [freshModHeap_get_k] at he'
        cases he'
        rw [hszH]
        exact Nat.lt_succ_self _
      · by_cases he2 : o = h₀.objs.size + 1
        · subst he2
          rw [freshModHeap_get_e] at he'
          cases he'
        · exact absurd hlt (by rw [hszH]; exact not_lt_add_two ho hk he2)
  · by_cases ho : o < h₀.objs.size
    · have hcpm : (hmidOf h₀ d name).classPayload? o = some cp := by
        unfold Heap.classPayload? at hcp ⊢
        rw [freshModHeap_get_old ho] at hcp
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
        rw [freshModHeap_cp_k] at hcp
        cases hcp
        refine ⟨fun s hs => ?_, fun i hi => ?_, fun p hp => ?_⟩
        · exact absurd hs (by simp)
        · exact absurd hi (by simp)
        · exact absurd hp (by simp)
      · by_cases he2 : o = h₀.objs.size + 1
        · subst he2
          rw [freshModHeap_cp_e] at hcp
          cases hcp
          refine ⟨fun s hs => ?_, fun i hi => ?_, fun p hp => ?_⟩
          · simp only [Option.some.injEq] at hs
            subst hs
            exact hbound _ hch.boot.1
          · exact absurd hi (by simp)
          · exact absurd hp (by simp)
        · rw [freshModHeap_cp_oob (Nat.le_of_not_lt
            (fun hlt2 => not_lt_add_two ho hk he2 hlt2))] at hcp
          cases hcp

/-! ## Whole-chain reads -/

/-- The dedup fold peels a head no later element repeats. -/
theorem foldl_dedup_cons {L : List ObjId} {a : ObjId} (ha : ∀ x ∈ L, x ≠ a) :
    ∀ acc : List ObjId, a ∉ acc →
      L.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) (a :: acc)
        = a :: L.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) acc := by
  induction L with
  | nil => intro acc _; rfl
  | cons x xs ih =>
    intro acc hacc
    simp only [List.foldl]
    have hxa : x ≠ a := ha x (by simp)
    have hct : (a :: acc).contains x = acc.contains x := by
      simp [List.contains_cons, hxa]
    rw [hct]
    by_cases hc : acc.contains x
    · rw [if_pos hc, if_pos hc]
      exact ih (fun y hy => ha y (by simp [hy])) acc hacc
    · rw [if_neg hc, if_neg hc]
      rw [show a :: acc ++ [x] = a :: (acc ++ [x]) from rfl]
      exact ih (fun y hy => ha y (by simp [hy]))
        (acc ++ [x]) (by
          intro hmem
          rcases List.mem_append.mp hmem with h1 | h1
          · exact hacc h1
          · exact hxa (List.mem_singleton.mp h1).symm)

theorem ancestors_fresh_k :
    ancestors (freshModHeap h₀ d name q) h₀.objs.size = [h₀.objs.size] := by
  unfold ancestors
  rw [show (freshModHeap h₀ d name q).objs.size + 1 = (h₀.objs.size + 2) + 1 from
    by rw [freshModHeap_size]]
  rw [freshModHeap_anc_go_k]
  rfl

theorem ancestors_old_fresh (hch : ChainsIn h₀) (hsat : Saturated h₀)
    {o : ObjId} (ho : o < h₀.objs.size) :
    ancestors (freshModHeap h₀ d name q) o = ancestors h₀ o := by
  have hchm : ChainsIn (hmidOf h₀ d name) := chainsIn_hmid hch
  have hsm : Saturated (hmidOf h₀ d name) := saturated_hmid hsat
  rw [ClsGrow.ancestors_old clsGrow_hmid_fresh hchm hsm
    (by rw [hmid_size]; exact ho)]
  exact ancestors_constSetIn h₀ d o name _

theorem ancestors_fresh_e (hch : ChainsIn h₀) (hsat : Saturated h₀) :
    ancestors (freshModHeap h₀ d name q) (h₀.objs.size + 1)
      = (h₀.objs.size + 1) :: ancestors h₀ Boot.classId := by
  have hchm : ChainsIn (hmidOf h₀ d name) := chainsIn_hmid hch
  have hsm : Saturated (hmidOf h₀ d name) := saturated_hmid hsat
  have hcb : Boot.classId < h₀.objs.size := hch.boot.1
  unfold ancestors
  rw [show (freshModHeap h₀ d name q).objs.size + 1 = (h₀.objs.size + 2) + 1 from
    by rw [freshModHeap_size]]
  rw [freshModHeap_anc_go_e (h₀.objs.size + 2)]
  rw [ClsGrow.ancestors_go_old clsGrow_hmid_fresh hchm hsm _ Boot.classId
    (by rw [hmid_size]; exact hcb)]
  rw [ancestors_go_ge hsm.2 (by
    rw [hmid_size]
    exact Nat.add_le_add_left (show (1:Nat) ≤ 2 by decide) _) Boot.classId]
  have hgo := ClsGrow.ancestors_go_mem_lt hchm ((hmidOf h₀ d name).objs.size + 1)
    Boot.classId (by rw [hmid_size]; exact hcb)
  have hne : ∀ x ∈ ancestors.go (hmidOf h₀ d name) Boot.classId
      ((hmidOf h₀ d name).objs.size + 1), x ≠ h₀.objs.size + 1 := by
    intro x hx hEq
    have := hgo x hx
    rw [hmid_size] at this
    subst hEq
    exact Nat.not_lt.mpr (Nat.le_succ _) this
  show List.foldl _ [] (_ :: _) = _
  rw [show List.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []
      ((h₀.objs.size + 1) :: ancestors.go (hmidOf h₀ d name) Boot.classId
        ((hmidOf h₀ d name).objs.size + 1))
      = List.foldl _ ([h₀.objs.size + 1])
        (ancestors.go (hmidOf h₀ d name) Boot.classId
          ((hmidOf h₀ d name).objs.size + 1)) from rfl]
  rw [show ([h₀.objs.size + 1] : List ObjId) = (h₀.objs.size + 1) :: [] from rfl]
  rw [foldl_dedup_cons hne [] (by simp)]
  congr 1
  -- the tail's dedup is `ancestors hmid classId`, which `constSetIn` pins to h₀'s
  have : ancestors (hmidOf h₀ d name) Boot.classId = ancestors h₀ Boot.classId :=
    ancestors_constSetIn h₀ d Boot.classId name _
  unfold ancestors at this
  rw [← hmid_size h₀ d name] at this ⊢
  exact this

theorem classOf_fresh_k :
    classOf (freshModHeap h₀ d name q) (.ref h₀.objs.size) = h₀.objs.size + 1 := by
  have h1 : classOf (freshModHeap h₀ d name q) (.ref h₀.objs.size)
      = match ((freshModHeap h₀ d name q).get h₀.objs.size).eigen with
        | some e => e
        | none => ((freshModHeap h₀ d name q).get h₀.objs.size).klass := rfl
  rw [h1, freshModHeap_get_k]

theorem classOf_fresh_e :
    classOf (freshModHeap h₀ d name q) (.ref (h₀.objs.size + 1)) = Boot.classId := by
  have h1 : classOf (freshModHeap h₀ d name q) (.ref (h₀.objs.size + 1))
      = match ((freshModHeap h₀ d name q).get (h₀.objs.size + 1)).eigen with
        | some e => e
        | none => ((freshModHeap h₀ d name q).get (h₀.objs.size + 1)).klass := rfl
  rw [h1, freshModHeap_get_e]

end Chains

/-! ## The predicate layer at the composite -/

section Preds

variable {h₀ : Heap} {d : ObjId} {name q : String}

theorem freshModHeap_cp_old (hdlt : d < h₀.objs.size) {o : ObjId}
    (ho : o < h₀.objs.size) :
    (freshModHeap h₀ d name q).classPayload? o
      = (hmidOf h₀ d name).classPayload? o := by
  unfold Heap.classPayload?
  rw [freshModHeap_get_old ho]

theorem className_old_fresh (hdlt : d < h₀.objs.size) {o : ObjId}
    (ho : o < h₀.objs.size) :
    className (freshModHeap h₀ d name q) o = className h₀ o := by
  unfold className
  rw [freshModHeap_cp_old hdlt ho]
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

theorem className_fresh_k (hqne : ¬ q.isEmpty = true) :
    className (freshModHeap h₀ d name q) h₀.objs.size = q := by
  unfold className
  rw [freshModHeap_cp_k]
  show (if q.isEmpty then _ else q) = q
  rw [if_neg hqne]

theorem className_fresh_e :
    className (freshModHeap h₀ d name q) (h₀.objs.size + 1)
      = "#<Class:" ++ q ++ ">" := by
  unfold className
  rw [freshModHeap_cp_e]
  show (if ("#<Class:" ++ q ++ ">").isEmpty then _ else _) = _
  rw [if_neg (by
    simp only [String.isEmpty_iff]
    intro hq
    have h1 := congrArg String.length hq
    simp [String.length_append] at h1)]

/-- A hook-free walk answers `none`. -/
theorem lookupGo_none_of_hookfree {h : Heap} {nn : String} :
    ∀ l : List ObjId,
      (∀ j ∈ l, ∀ cp, h.classPayload? j = some cp →
        cp.methods.find? (·.1 == nn) = none) →
      lookup.go h nn l = none := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons j rest ih =>
    intro hall
    unfold lookup.go
    cases hcp : h.classPayload? j with
    | none => exact ih (fun j' hj' => hall j' (List.mem_cons_of_mem _ hj'))
    | some c =>
      dsimp only
      rw [hall j (by simp) c hcp]
      exact ih (fun j' hj' => hall j' (List.mem_cons_of_mem _ hj'))

/-- `NoHook` at the composite. -/
theorem noHook_fresh (hh : NoHook h₀) (hch : ChainsIn h₀) (hsat : Saturated h₀)
    (hdlt : d < h₀.objs.size) :
    NoHook (freshModHeap h₀ d name q) := by
  have hhm : NoHook (hmidOf h₀ d name) := noHook_constSetIn hh
  have hchm : ChainsIn (hmidOf h₀ d name) := chainsIn_hmid hch
  have hsm : Saturated (hmidOf h₀ d name) := saturated_hmid hsat
  have hg : ClsGrow (hmidOf h₀ d name) (freshModHeap h₀ d name q) :=
    clsGrow_hmid_fresh
  -- hook-free tables along `Class`'s chain, at the composite (clause 3 first —
  -- clauses 2's fresh cases read it)
  have hanc3 : ∀ j ∈ ancestors (freshModHeap h₀ d name q) Boot.classId,
      ∀ cp, (freshModHeap h₀ d name q).classPayload? j = some cp →
      ∀ n ∈ hookFreeNames, cp.methods.find? (·.1 == n) = none := by
    intro j hj cp hcp n hn
    rw [ancestors_old_fresh hch hsat hch.boot.1] at hj
    have hjlt : j < h₀.objs.size := ClsGrow.ancestors_mem_lt hch hch.boot.1 j hj
    rw [freshModHeap_cp_old hdlt hjlt] at hcp
    have hms := methods_constSetIn h₀ d j name (Value.ref h₀.objs.size)
    cases hcp0 : h₀.classPayload? j with
    | none => rw [hcp0] at hms; rw [hcp] at hms; exact absurd hms (by simp)
    | some cp0 =>
      rw [hcp0, hcp] at hms
      simp only [Option.map_some, Option.some.injEq] at hms
      rw [hms]
      exact hh.2.2 j hj cp0 hcp0 n hn
  refine ⟨?_, fun k hk n hn => ?_, hanc3⟩
  · rw [freshModHeap_cp_old hdlt hch.boot.2.2.2.2]
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
        rw [freshModHeap_cp_old hdlt hko] at hk
        exact hk) n hn
      unfold lookup at this
      exact this
    · by_cases hkk : k = h₀.objs.size
      · subst hkk
        unfold lookup
        rw [classOf_fresh_k, ancestors_fresh_e hch hsat]
        have hstep : lookup.go (freshModHeap h₀ d name q) n
            ((h₀.objs.size + 1) :: ancestors h₀ Boot.classId)
            = lookup.go (freshModHeap h₀ d name q) n (ancestors h₀ Boot.classId) := by
          rw [lookup.go.eq_def]
          simp only []
          rw [freshModHeap_cp_e]
          simp
        rw [hstep]
        refine lookupGo_none_of_hookfree _ (fun j hj cp hcp => ?_)
        exact hanc3 j (by rw [ancestors_old_fresh hch hsat hch.boot.1]; exact hj)
          cp hcp n hn
      · by_cases hke : k = h₀.objs.size + 1
        · subst hke
          unfold lookup
          rw [classOf_fresh_e, ancestors_old_fresh hch hsat hch.boot.1]
          refine lookupGo_none_of_hookfree _ (fun j hj cp hcp => ?_)
          exact hanc3 j (by rw [ancestors_old_fresh hch hsat hch.boot.1]; exact hj)
            cp hcp n hn
        · rw [freshModHeap_cp_oob (Nat.le_of_not_lt
            (fun hlt2 => not_lt_add_two hko hkk hke hlt2))] at hk
          exact absurd hk (by simp)

theorem litClsOk_fresh (hs : LitClsOk h₀) (hdlt : d < h₀.objs.size)
    (hch : ChainsIn h₀) : LitClsOk (freshModHeap h₀ d name q) := by
  have hlt : ∀ x, (h₀.classPayload? x).isSome = true → x < h₀.objs.size :=
    fun x hx => classPayload?_isSome_lt hx
  have hsm : LitClsOk (hmidOf h₀ d name) := litClsOk_constSetIn hs
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [freshModHeap_cp_old hdlt (hlt _ hs.1.1)]; exact hsm.1.1
  · rw [show className (freshModHeap h₀ d name q) Boot.stringId
      = className h₀ Boot.stringId from
        className_old_fresh hdlt (hlt _ hs.1.1)]
    exact hs.1.2
  · rw [freshModHeap_cp_old hdlt (hlt _ hs.2.1.1)]; exact hsm.2.1.1
  · rw [className_old_fresh hdlt (hlt _ hs.2.1.1)]; exact hs.2.1.2
  · rw [freshModHeap_cp_old hdlt (hlt _ hs.2.2.1)]; exact hsm.2.2.1
  · rw [freshModHeap_cp_old hdlt (hlt _ hs.2.2.2)]; exact hsm.2.2.2

theorem constOwn_fresh_k {n : String} :
    constOwn (freshModHeap h₀ d name q) h₀.objs.size n = none := by
  unfold constOwn
  rw [freshModHeap_cp_k]
  rfl

theorem constOwn_fresh_e {n : String} :
    constOwn (freshModHeap h₀ d name q) (h₀.objs.size + 1) n = none := by
  unfold constOwn
  rw [freshModHeap_cp_e]
  rfl

theorem constOwn_old_fresh (hdlt : d < h₀.objs.size) {o : ObjId}
    (ho : o < h₀.objs.size) {n : String} :
    constOwn (freshModHeap h₀ d name q) o n = constOwn (hmidOf h₀ d name) o n := by
  unfold constOwn
  rw [freshModHeap_cp_old hdlt ho]

/-- `NoShadowBefore` survives a constant write at an id off the shadowing
    segments (the module-target variant of `noShadowBefore_constSetIn_obj`). -/
theorem noShadowBefore_constSetIn_off {h : Heap} {dd k : ObjId} {nm : String}
    {v : Value} (hoff : ModOffChains h dd) (hn : NoShadowBefore h k) :
    NoShadowBefore (constSetIn h dd nm v) k := by
  refine ⟨by rw [ancestors_constSetIn]; exact hn.1, ?_⟩
  rw [ancestors_constSetIn]
  intro i hi cp hcp
  by_cases hid : i = dd
  · subst hid
    exact absurd hi (hoff k hn.1)
  · have hpay := payload_constSetIn_ne h dd nm v i hid
    have hcp0 : h.classPayload? i = some cp := by
      unfold Heap.classPayload? at hcp ⊢
      rw [← hpay]
      exact hcp
    exact hn.2 i hi cp hcp0

/-- `ClassOk` survives a constant write of a fresh, unreadable name at an id
    off the shadowing segments — the `_obj` lemma's argument with the
    `takeWhile`-membership refutation swapped for `ModOffChains`. -/
theorem classOk_constSetIn_off {h : Heap} {dd : ObjId} {nm : String} {v : Value}
    (hdo : dd ≠ Boot.objectId) (hoff : ModOffChains h dd)
    (hnr : nm ∉ Types.readableClasses)
    (hc : ClassOk h) : ClassOk (constSetIn h dd nm v) := by
  refine ⟨by rw [className_constSetIn]; exact hc.1,
    noShadowBefore_constSetIn_off hoff hc.2.1, ?_, fun o cp hcp => ?_⟩
  · intro n hn
    obtain ⟨k, cp, h1, h2, h4, h5, hrx, hmt, hsole, hreop⟩ := hc.2.2.1 n hn
    have hps := classPayload?_isSome_constSetIn h dd k nm v
    cases hk2 : (constSetIn h dd nm v).classPayload? k with
    | none => rw [hk2, h2] at hps; exact absurd hps (by simp)
    | some cp' =>
      have hname := clsName_constSetIn h dd k nm v
      rw [hk2, h2] at hname
      simp only [Option.map_some, Option.some.injEq] at hname
      have hpair := Prod.ext_iff.mp hname
      refine ⟨k, cp',
        by rw [constOwn_constSetIn_ne h dd Boot.objectId nm n v
          (Or.inr (fun hq => hnr (hq ▸ hn)))]; exact h1,
        hk2, by rw [className_constSetIn]; exact h4,
        fun i hi hin => ?_, hrx, hmt, fun i hi hio => ?_, fun hmem => ?_⟩
      · refine h5 i ?_ ?_
        · rw [← classPayload?_isSome_constSetIn h dd i nm v]; exact hi
        · rw [← className_constSetIn h dd i nm v]; exact hin
      · by_cases hidd : i = dd
        · subst hidd
          have hpsi : (h.classPayload? i).isSome = true := by
            rw [← classPayload?_isSome_constSetIn h i i nm v]
            exact hi
          have hold := hsole i hpsi hio
          have hcs := consts_find_constSetIn h i i nm n v (fun hq => hnr (hq ▸ hn))
          unfold constOwn at hold ⊢
          cases hicp : (constSetIn h i nm v).classPayload? i with
          | none => rfl
          | some cpi =>
            cases hicp0 : h.classPayload? i with
            | none => rw [hicp0] at hpsi; exact absurd hpsi (by simp)
            | some cpi0 =>
              rw [hicp, hicp0] at hcs
              simp only [Option.map_some, Option.some.injEq] at hcs
              rw [hicp0] at hold
              simp only [Option.bind_some] at hold ⊢
              rw [hcs]
              exact hold
        · rw [constOwn_constSetIn_ne h dd i nm n v (Or.inr (fun hq => hnr (hq ▸ hn)))]
          refine hsole i ?_ hio
          rw [← classPayload?_isSome_constSetIn h dd i nm v]; exact hi
      · obtain ⟨hmod, hhd, hns⟩ := hreop hmem
        exact ⟨by rw [show cp'.isModule = cp.isModule from congrArg Prod.snd hname]
                  exact hmod,
          by rw [ancestors_constSetIn]; exact hhd,
          noShadowBefore_constSetIn_off hoff hns⟩
  · have hnm2 := clsName_constSetIn h dd o nm v
    rw [hcp] at hnm2
    cases h2 : h.classPayload? o with
    | none => rw [h2] at hnm2; exact absurd hnm2 (by simp)
    | some cp0 =>
      rw [h2] at hnm2
      simp only [Option.map_some, Option.some.injEq] at hnm2
      rw [show cp.name = cp0.name from congrArg Prod.fst hnm2]
      exact hc.2.2.2 o cp0 h2

end Preds

end Judgment
end Proof
end RubyCore
