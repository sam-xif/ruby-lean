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

end Judgment
end Proof
end RubyCore
