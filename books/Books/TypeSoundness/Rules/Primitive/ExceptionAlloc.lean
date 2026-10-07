import Books.TypeSoundness.Rules.Primitive.PrimitiveStep

/-! Runtime exceptions allocate a String message and an exception object. Native
initialization is an observable call, proved separately from allocation. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

def errorMessageMachine (m : Machine) (msg : String) : Machine :=
  { m with heap := pushHeap m.heap (strObj msg false) }

def errorObjectMachine (m : Machine) (cls : ObjId) (msg : String)
    (value : Value) (revision : Nat := 0) : Machine :=
  let n := errorMessageMachine m msg
  { n with heap := pushHeap n.heap { klass := cls, payload := .exc value, revision } }

theorem errorObject_ext {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) (cls : ObjId) (msg : String) (value : Value) (revision : Nat)
    (hb : (ancestors m.heap cls).contains Boot.basicObjectId = true) :
    Ext m (errorObjectMachine m cls msg value revision) := by
  have h₁ : Ext m (errorMessageMachine m msg) :=
    ext_push (strObj msg false) hm.sat hm.core.basicSelf
      (by intro c h; cases h) rfl rfl hm.core.stringBasic
  apply h₁.trans
  exact ext_push _ (Proof.Saturated_grow h₁.shapeAgree h₁.size hm.sat)
    (by rw [h₁.ancestors]; exact hm.core.basicSelf)
    (by intro c h; cases h) rfl rfl (by rw [h₁.ancestors]; exact hb)

theorem invoke_exception_init {m : Machine} {o owner : ObjId} {message : Value} {md : MethodDef}
    (ho : (m.heap.get o).payload = .exc .nil)
    (hl : lookup m.heap (.ref o) "initialize" = some (owner, md))
    (hb : md.builtin = some "Exception#initialize") (hu : md.undefined = false)
    (hp : md.fromPrelude = false)
    (hs : Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap (.ref o))).takeWhile (· != owner)) "initialize" = none) :
    Interp.invoke m (.ref o) .reflective "initialize" [message] none [] =
      builtinStep (Builtins.run "Exception#initialize" (.ref o) [message] m) := by
  rw [Interp.invoke.eq_def]
  simp only [hl, Option.isNone, Bool.and_false, Bool.false_eq_true, ↓reduceIte, ho]
  simp only [Interp.invoke.invokeDispatch, hl, hu, hp, Interp.crubyResolvedShadow,
    hb, Option.any, show ["Class#new", "Module#new", "Class#allocate"].contains "Exception#initialize" = false from rfl,
    Bool.false_eq_true, ↓reduceIte, hs, Interp.visError?]
  simp only [show "Exception#initialize".startsWith "Main#" = false from by decide +kernel,
    show Interp.nativeDupBid "Exception#initialize" = false from by decide +kernel,
    show Interp.nativeCloneBid "Exception#initialize" = false from by decide +kernel,
    Bool.false_eq_true, ↓reduceIte]
  change Interp.callCoreInitialize m "Exception#initialize" (.ref o) [message] none [] = _
  simp only [Interp.callCoreInitialize, Interp.appendKwHash, List.isEmpty, ↓reduceIte]
  cases Builtins.run "Exception#initialize" (.ref o) [message] m <;> rfl

theorem errorObject_initialize (m : Machine) (cls : ObjId) (msg : String) :
    Builtins.run "Exception#initialize" (.ref (m.heap.objs.size + 1)) [.ref m.heap.objs.size]
      (errorObjectMachine m cls msg .nil) =
    .ok (.ref (m.heap.objs.size + 1)) (errorObjectMachine m cls msg (.ref m.heap.objs.size) 1) := by
  let n := errorObjectMachine m cls msg .nil
  have hexc : (n.heap.get (m.heap.objs.size + 1)) = { klass := cls, payload := .exc .nil } := by
    simpa only [n, errorObjectMachine, errorMessageMachine, pushHeap_size] using
      pushHeap_get_self (pushHeap m.heap (strObj msg false)) { klass := cls, payload := .exc .nil }
  have hmsg : n.heap.get m.heap.objs.size = strObj msg false := by
    rw [show n.heap = pushHeap (pushHeap m.heap (strObj msg false))
      { klass := cls, payload := .exc .nil } from rfl,
      pushHeap_get_lt _ _ (by simp), pushHeap_get_self]
  change Builtins.run _ _ _ n = _
  simp only [Builtins.run, List.any_cons, List.any_nil, Builtins.unrepresentableByteStr,
    Builtins.strPayload?, Builtins.isBinaryStr, hexc, hmsg, strObj, Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  simp only [show ("Exception#initialize".endsWith "#==" || "Exception#initialize".endsWith "#eql?" ||
    "Exception#initialize".endsWith "#!=" || Builtins.pureEqualityBids.contains "Exception#initialize") = false from by decide +kernel,
    Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  change Builtins.runModules "Exception#initialize" (.ref (m.heap.objs.size + 1)) [.ref m.heap.objs.size] n = _
  simp only [Builtins.runModules, hexc]
  change BRes.ok _ { n with heap := n.heap.set (m.heap.objs.size + 1) { klass := cls, payload := .exc (.ref m.heap.objs.size) } } = _
  simp only [Heap.set, hexc]
  simp [n, errorObjectMachine, errorMessageMachine, pushHeap, Array.setIfInBounds, Array.set_push]

theorem errorObject_answer {κ : Ctx} {Γ : Env} {I τ : Ty} {m : Machine} {cls : ObjId}
    (hm : StateOk κ Γ I m) (hcls : cls ∈ primitiveErrorClasses)
    (msg : String) (value : Value) (revision : Nat) :
    RunSpec m (deliverA (.esc (.raiseJ (.ref (m.heap.objs.size + 1))))
      (errorObjectMachine m cls msg value revision) []) Γ τ κ I := by
  have hp := List.all_eq_true.mp hm.primitiveErrors cls hcls
  simp only [primitiveErrorB, Bool.and_eq_true, Bool.not_eq_true'] at hp
  have he := errorObject_ext hm cls msg value revision hp.1.1.1
  have hc : classOf (errorObjectMachine m cls msg value revision).heap
      (.ref (m.heap.objs.size + 1)) = cls := by
    have hget : (errorObjectMachine m cls msg value revision).heap.get (m.heap.objs.size + 1) =
        { klass := cls, payload := .exc value, revision } := by
      simpa only [errorObjectMachine, errorMessageMachine, pushHeap_size] using
        pushHeap_get_self (pushHeap m.heap (strObj msg false)) { klass := cls, payload := .exc value, revision }
    simp [classOf, hget]
  apply RunSpec.answer
  refine ⟨Framed.of_ext he, ?_, fun _ hv => by cases hv⟩
  simp only [AnsOk, EscOk, Semantics.isTypeError, Semantics.typeErrorFamily, List.any_cons,
    List.any_nil, isA, hc, he.ancestors, hp.1.1.2, hp.1.2, hp.2, Bool.false_or]

theorem runSpec_zeroDivisionError {κ : Ctx} {Γ : Env} {I τ : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) (hk : m.kont = []) (msg : String) :
    RunSpec m (Interp.raiseErr m Boot.zeroDivisionErrorId msg) Γ τ κ I := by
  let cls := Boot.zeroDivisionErrorId
  let inst := Value.ref (m.heap.objs.size + 1)
  let message := Value.ref m.heap.objs.size
  let n₀ := errorObjectMachine m cls msg .nil
  let n₁ := errorObjectMachine m cls msg message 1
  let start := reCtl n₀ (.send inst .reflective "initialize" [message] none []) [.raiseNewK inst]
  let middle := reCtl n₁ (.value inst) [.raiseNewK inst]
  have hp := List.all_eq_true.mp hm.primitiveErrors cls
    (by simp [cls, primitiveErrorClasses])
  simp only [primitiveErrorB, Bool.and_eq_true, Bool.not_eq_true'] at hp
  have he := errorObject_ext hm cls msg .nil 0 hp.1.1.1
  have hi : primitiveInitB start.heap = true := by
    change primitiveInitB n₀.heap = true
    rw [primitiveInitB_ext he hm.names hm.core.classReady.chains]
    exact hm.primitiveInit
  obtain ⟨owner, md, hl, hb, hu, hpre, hs⟩ := primitiveInit_lookup hi
    (k := cls) (by simp [cls, primitiveInitClasses])
  have ho : start.heap.get (m.heap.objs.size + 1) =
      { klass := cls, payload := .exc .nil } := by
    simpa only [start, n₀, reCtl, errorObjectMachine, errorMessageMachine, pushHeap_size] using
      pushHeap_get_self (pushHeap m.heap (strObj msg false)) { klass := cls, payload := .exc .nil }
  have hc : classOf start.heap inst = cls := by simp [inst, classOf, ho]
  have hcall : Interp.invoke start inst .reflective "initialize" [message] none [] =
      builtinStep (Builtins.run "Exception#initialize" inst [message] start) :=
    invoke_exception_init (by rw [ho]) (by rw [lookup_eq_methodOn, hc]; exact hl)
      hb hu hpre (by change Interp.crubyShadow start.heap ((ancestors start.heap (classOf start.heap inst)).takeWhile (· != owner)) "initialize" = none; rw [hc]; exact hs)
  have hinit : Builtins.run "Exception#initialize" inst [message] start =
      .ok inst (reCtl n₁ (.send inst .reflective "initialize" [message] none []) [.raiseNewK inst]) :=
    errorObject_initialize (reCtl m (.send inst .reflective "initialize" [message] none []) [.raiseNewK inst]) cls msg
  have hstep : Interp.stepFn start = .next middle := by
    change Interp.invoke start inst .reflective "initialize" [message] none [] = _
    rw [hcall, hinit]
    rfl
  have hraise : Interp.stepFn middle = .next (deliverA (.esc (.raiseJ inst)) n₁ []) := rfl
  have hout : RunSpec m (deliverA (.esc (.raiseJ inst)) n₁ []) Γ τ κ I :=
    errorObject_answer hm (by simp [cls, primitiveErrorClasses]) msg message 1
  have hrun := RunSpec.step (by rfl : answerPoint start = none) hstep
    (RunSpec.step (by rfl : answerPoint middle = none) hraise hout)
  simpa [Interp.raiseErr, Builtins.allocStr, Builtins.allocStrEnc, Heap.alloc,
      cls, start, n₀, inst, message, errorObjectMachine, errorMessageMachine, pushHeap,
      strObj, reCtl, hk, Boot.zeroDivisionErrorId, Boot.nameErrorId, Boot.noMethodErrorId, Boot.keyErrorId] using hrun

#print axioms errorObject_ext
#print axioms invoke_exception_init
#print axioms runSpec_zeroDivisionError
#print axioms errorObject_initialize
end Checker.Soundness.Typed
