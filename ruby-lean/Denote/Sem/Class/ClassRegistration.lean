import Denote.Sem.Core.Ready
import RubyCore.Proof.Judgment.ClsFresh

/-! Repair the registration/naming part of fresh class entry using the model's
existing operational lemma. Callback execution and body conformance follow later. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore RubyCore.Interp RubyCore.Proof RubyCore.Proof.Judgment

def freshClassPayload (h : Heap) (p : ObjId := Boot.objectId) : ClassPayload :=
  { superclass := some p, name := "", isModule := false,
    ancestryReady := (h.classPayload? p).all (·.ancestryReady),
    allocatorUnavailable := (h.classPayload? p).any (·.allocatorUnavailable) }

theorem freshClassPayload_ready {h : Heap} {p : ObjId} (hf : objectClassFlagsB h p = true) :
    allocationReadyB (freshClassPayload h p) = true := by
  cases hp : h.classPayload? p with
  | none => simp [objectClassFlagsB, hp] at hf
  | some cp =>
    simp only [objectClassFlagsB, hp, Option.any, Bool.and_eq_true,
      Bool.not_eq_true'] at hf
    simp [allocationReadyB, freshClassPayload, hp, hf.1, hf.2]

theorem freshClassRegistered_payload {m : Machine} {name : String} {p : ObjId}
    (hd : m.lexicalNamespace < m.heap.objs.size) :
    (freshClassRegistered m name p).classPayload? m.heap.objs.size =
      some (freshClassPayload m.heap p) := by
  unfold freshClassRegistered
  rw [constSetIn_alloc_comm _ _ _ _ _ hd]
  have hz := objs_size_constSetIn m.heap m.lexicalNamespace name (.ref m.heap.objs.size)
  have hg := objs_getD_push_self
    (constSetIn m.heap m.lexicalNamespace name (.ref m.heap.objs.size)).objs
    ({ klass := Boot.classId, payload := .cls (freshClassPayload m.heap p) } : Object)
  simp only [hz] at hg
  have hget : ((constSetIn m.heap m.lexicalNamespace name (.ref m.heap.objs.size)).alloc
      ({ klass := Boot.classId, payload := .cls (freshClassPayload m.heap p) } : Object)).2.get
      m.heap.objs.size = { klass := Boot.classId, payload := .cls (freshClassPayload m.heap p) } := hg
  change (match (((constSetIn m.heap m.lexicalNamespace name (.ref m.heap.objs.size)).alloc
    ({ klass := Boot.classId, payload := .cls (freshClassPayload m.heap p) } : Object)).2.get
    m.heap.objs.size).payload with | .cls cp => some cp | _ => none) = _
  rw [hget]

theorem nameConstant_empty_class {h : Heap} {k : ObjId} {cp : ClassPayload} {name : String}
    (hp : h.classPayload? k = some cp) (hn : cp.name = "") (hc : cp.consts = []) :
    nameConstant h Boot.objectId name (.ref k) =
      .ok (h.setClassPayload k { cp with name, namePermanent := true }) := by
  simp [nameConstant, hp, hn, setNamespacePath, setNamespacePath.go, hc]
  rfl

def freshClassNamed (m : Machine) (name : String) (p : ObjId := Boot.objectId) : Heap :=
  (freshClassRegistered m name p).setClassPayload m.heap.objs.size
    { freshClassPayload m.heap p with name, namePermanent := true }

theorem freshClassNamed_payload {m : Machine} {name : String} {p : ObjId} :
    (freshClassNamed m name p).classPayload? m.heap.objs.size =
      some { freshClassPayload m.heap p with name, namePermanent := true } := by
  have hs : (freshClassRegistered m name p).objs.size = m.heap.objs.size + 1 := by
    simp only [freshClassRegistered, objs_size_constSetIn, Heap.alloc, Array.size_push]
  have hl : m.heap.objs.size < (freshClassRegistered m name p).objs.size := by omega
  simp only [freshClassNamed, Heap.classPayload?, Heap.setClassPayload, Heap.get, Heap.set]
  rw [objs_getD_set!_self _ _ _ hl]

theorem freshClassNamed_ready {m : Machine} {name : String} {p : ObjId}
    (hf : objectClassFlagsB m.heap p = true) :
    plainAllocationReadyB (freshClassNamed m name p) m.heap.objs.size = true := by
  simp only [plainAllocationReadyB, freshClassNamed_payload, Option.any]
  exact freshClassPayload_ready hf

theorem freshClassRegistered_named {m : Machine} {name : String} {p : ObjId}
    (hc : m.currentFrame.cref = []) (hd : Boot.objectId < m.heap.objs.size) :
    nameConstant (freshClassRegistered m name p) m.lexicalNamespace name
      (.ref m.heap.objs.size) = .ok (freshClassNamed m name p) := by
  have hl : m.lexicalNamespace = Boot.objectId := by simp [Machine.lexicalNamespace, hc]
  have hp := freshClassRegistered_payload (m := m) (name := name) (p := p) (hl ▸ hd)
  rw [hl]
  exact nameConstant_empty_class hp rfl rfl

/-- Actual first successor: naming and metaclass realization precede the queued hook. -/
theorem stepFn_class_registered {m : Machine} {name : String} {body : RubyCore.Expr}
    (hm : MainReady m) (hn : constOwn m.heap Boot.objectId name = none) :
    stepFn { m with ctl := .eval (.class' name none body) } =
      let start := { m with ctl := .eval (.class' name none body) }
      let next := (eigenclassOf { start with heap := freshClassNamed m name } m.heap.objs.size).2
      callConstAdded { next with
        kont := .constClassK m.heap.objs.size (some Boot.objectId) name body :: next.kont }
        Boot.objectId name := by
  let start := { m with ctl := .eval (.class' name none body) }
  have hc : start.currentFrame.cref = [] := hm.cref
  have hl : start.lexicalNamespace = Boot.objectId := by simp [Machine.lexicalNamespace, hc]
  have hd : Boot.objectId < start.heap.objs.size :=
    Nat.lt_trans (by decide : Boot.objectId < Boot.mainId) hm.live
  have he := evalExpr_class_fresh (m := start) (body := body)
    (by simpa only [hl] using hn) (by simpa only [hl] using hm.unfrozen)
    (freshClassRegistered_named hc hd)
  change evalExpr start (.class' name none body) = _
  have hnamed : freshClassNamed start name = freshClassNamed m name := rfl
  simpa only [hl, beq_self_eq_true, ↓reduceIte, hnamed, start] using he

#print axioms freshClassRegistered_named
#print axioms freshClassNamed_ready
#print axioms stepFn_class_registered
end Ratchet.Denote
