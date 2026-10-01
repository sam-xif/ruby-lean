import Denote.Rules.Closure.Entry
import Denote.Sem.Closure.Reify
import Denote.Rules.Primitive.PrimitiveStep

/-! Native Symbol conversion and its real required/rest activation (model L275).
Sorbet 0.6.13405 types map(&:to_s) as Array[String] and checks the forwarded
method's domain/arity (7003/7004). These are semantic entry lemmas, not admission
rules: the callback has no captured locals and allocates its rest Array. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

def symbolBody (name : String) : Ratchet.Expr :=
  .send (some (.var .lvar "__recv")) name [.splat (some (.var .lvar "__rest"))] none

def symbolClosure (name : String) : Closure :=
  { params := [.req "__recv", .rest (some "__rest")], locals := [],
    body := toRuby (symbolBody name), captured := none, home := 0, lam := true }

def symbolAllocated (m : Machine) (name : String) : Machine :=
  { m with heap := pushHeap m.heap { klass := Boot.procId, payload := .proc (symbolClosure name) } }

theorem symbol_to_proc_run (m : Machine) (name : String) :
    Builtins.run "Symbol#to_proc" (.sym name) [] m =
      .ok (.ref m.heap.objs.size) (symbolAllocated m name) := rfl

theorem symbolAllocated_payload (m : Machine) (name : String) :
    ((symbolAllocated m name).heap.get m.heap.objs.size).payload = .proc (symbolClosure name) := by
  simp [symbolAllocated, pushHeap_get_self]

theorem symbolAllocated_class (m : Machine) (name : String) :
    classOf (symbolAllocated m name).heap (.ref m.heap.objs.size) = Boot.procId := by
  simp [symbolAllocated, classOf, pushHeap_get_self]

theorem symbolAllocated_ext {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) (name : String) : Ext m (symbolAllocated m name) :=
  ext_push _ hm.sat hm.core.basicSelf (by intro c h; cases h) rfl rfl hm.core.procBasic

theorem symbolAllocated_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) (name : String) : StateOk κ Γ I (symbolAllocated m name) :=
  StateOk_ext hm (symbolAllocated_ext hm name)
    (stringPayloadOk_push hm.stringPayload (by simp [Boot.procId, Boot.stringId]))
    (arrayPayloadOk_push hm.arrayPayload (by intro xs h; cases h))
    (hashPayloadOk_push hm.hashPayload (by intro xs h; cases h)) rfl

/-- Native readiness comes from guarded conformance, never from the Symbol value.
    Reserving to_proc withdraws this fact, just as reserving call does for Procs. -/
theorem invoke_symbol_to_proc {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) (hf : nameFreeN κ "to_proc" = true)
    (name : String) (site : SendSite) :
    Interp.invoke m (.sym name) site "to_proc" [] none [] =
      .next (Interp.withCtl (symbolAllocated m name) (.value (.ref m.heap.objs.size))) := by
  obtain ⟨owner, md, hl, hb, hu, hv, hp, hs⟩ :=
    dispatch_lookup (k := Boot.symbolId) (bid := "Symbol#to_proc")
      hm.primitiveDispatch (by simp [dispatchMethods]) hf
  rw [invoke_plain (by rfl) (by intro o h; cases h)]
  rw [invokeDispatch_builtin (bid := "Symbol#to_proc") (owner := owner) (md := md)
    (by simpa only [lookup_eq_methodOn, classOf] using hl)
    hb hu hv hp (by simpa only [classOf] using hs) (by rfl) (by rfl), symbol_to_proc_run]

theorem coerceBlockPass_symbol {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) (hf : nameFreeN κ "to_proc" = true)
    (call : BlockPassCall) (name : String) :
    Interp.coerceBlockPass m call (.sym name) = .next
      (Interp.withKont (symbolAllocated m name) (.value (.ref m.heap.objs.size))
        (.blkConvertK call (.sym name) (.converted true))) := by
  obtain ⟨owner, md, hl, _, hu, _⟩ :=
    dispatch_lookup (k := Boot.symbolId) (bid := "Symbol#to_proc")
      hm.primitiveDispatch (by simp [dispatchMethods]) hf
  have hl' : lookup m.heap (.sym name) "to_proc" = some (owner, md) := by
    simpa only [lookup_eq_methodOn, classOf] using hl
  simp only [Interp.coerceBlockPass, Value.identEq, Interp.blockPassProc, Bool.false_eq_true,
    ↓reduceIte, Interp.blockPassMethod, hl', Option.bind_some, hu]
  have hm' : StateOk κ Γ I
      (Interp.withKont m m.ctl (.blkConvertK call (.sym name) (.converted true))) :=
    StateOk_reCtl hm _ _
  rw [invoke_symbol_to_proc hm' hf]
  rfl

theorem resumeBlockPass_symbol (m : Machine) (call : BlockPassCall) (name : String) :
    Interp.resumeBlockPass (symbolAllocated m name) call (.sym name) (.converted true)
      (.ref m.heap.objs.size) = Interp.invoke (symbolAllocated m name) call.recv call.site
        call.name call.args (some (.ref m.heap.objs.size)) call.kw := by
  simp only [Interp.resumeBlockPass, Interp.blockPassProc, symbolAllocated_payload, ↓reduceIte]

/-- The rest Array is a real allocation even when no arguments remain. -/
def symbolRest (m : Machine) (args : List Value) : Machine :=
  (Builtins.allocArr m args.toArray).2

def symbolEntry (m : Machine) (name : String) (recv : Value) (args : List Value) : Machine :=
  let n := symbolRest m args
  pushMethodFrame n (requiredClosureFrame n (symbolClosure name)
    ["__recv", "__rest"] [recv, .ref m.heap.objs.size])

theorem callClosure_symbol (m : Machine) (name : String) (recv : Value)
    (args : List Value) (brk : Option FrameId) :
    Interp.callClosure m (symbolClosure name) (recv :: args) brk = .next
      (Interp.withKont (symbolEntry m name recv args) (.eval (toRuby (symbolBody name)))
        (.blkFrameK m.frames.size true brk (symbolClosure name) (recv :: args))) := by
  have hp : Interp.classifySimple (symbolClosure name).params =
      some ⟨["__recv"], some "__rest", [], none⟩ := rfl
  unfold Interp.callClosure
  rw [hp]
  simp [symbolClosure, symbolEntry,
    symbolRest, requiredClosureFrame, pushMethodFrame, Interp.withKont, Builtins.allocArr,
    Heap.alloc, List.getD, Nat.max_eq_right (Nat.zero_le _)]

theorem symbolRest_payload (m : Machine) (args : List Value) :
    ((symbolRest m args).heap.get m.heap.objs.size).payload = .arr args.toArray := by
  exact congrArg Object.payload (pushHeap_get_self m.heap _)

theorem symbolRest_ext {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) (args : List Value) : Ext m (symbolRest m args) :=
  ext_push _ hm.sat hm.core.basicSelf (by intro c h; cases h) rfl rfl hm.core.arrayBasic

theorem symbolRest_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) (args : List Value) : StateOk κ Γ I (symbolRest m args) :=
  StateOk_ext hm (symbolRest_ext hm args)
    (stringPayloadOk_push hm.stringPayload (by simp [Boot.arrayId, Boot.stringId]))
    (arrayPayloadOk_push hm.arrayPayload (by intro xs h; cases h; rfl))
    (hashPayloadOk_push hm.hashPayload (by intro xs h; cases h)) rfl

theorem symbolEntry_getLocal (m : Machine) (name : String) (recv : Value)
    (args : List Value) (x : String) :
    (symbolEntry m name recv args).getLocal x =
      if "__recv" == x then recv else if "__rest" == x then .ref m.heap.objs.size else .nil := by
  rw [symbolEntry, requiredClosureFrame_getLocal _ _ _ _ _ _ .none]
  cases hrecv : ("__recv" == x) <;> cases hrest : ("__rest" == x) <;>
    simp [symbolClosure, closLocal, frameLocal?, List.find?, hrecv, hrest]

#print axioms coerceBlockPass_symbol
#print axioms callClosure_symbol
#print axioms symbolRest_state
#print axioms symbolEntry_getLocal
end Ratchet.Denote.Typed
