import Books.TypeSoundness.Rules.Iterator.FlowMap
import Books.TypeSoundness.Conformance.Core.Boot

/-! Checked Integer→String bodies exercise allocation on every iteration. Source
pilots include both selectors; dispatch controls reject overrides, undef and private
entries while preserving the meaning of a reserved name. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.TypedMapControls
open RubyCore Checker Checker.Soundness

private def body : Checker.Expr := .send (some (.var .lvar "n")) "to_s" [] none
private def closure (m : Machine) : Closure :=
  { params := [.req "n"], locals := [], body := toRuby body,
    captured := some ((popMethodFrame m).stack.headD 0),
    home := Interp.returnTarget (popMethodFrame m), lam := false }

private theorem body_typed (Γ : Env) : SemSafeCtxA (closureBodyCtx ctx0) (("n", .int) :: Γ)
    .ivar0 body (.cls "String") (closureBodyCtx ctx0) (("n", .int) :: Γ) .ivar0 :=
  (SemSafeCtxA.var rfl rfl).prim .nil .intToS rfl (by intro h; cases h)

/-- Earlier String results remain typed while later iterations allocate more Strings. -/
theorem string_results {m : Machine} {o : ObjId}
    (hm : StateOk ctx0 [] .ivar0 (popMethodFrame m))
    (hv : denM (.arrayOf .int) (popMethodFrame m) (.ref o))
    (brk : FrameId) (index : Nat) (acc : List Value)
    (ha : ∀ v ∈ acc, denM (.cls "String") (popMethodFrame m) v) :
    StepSpec (popMethodFrame m) [] (.arrayOf (.cls "String"))
      (mapArrayStep m (closure m) brk o index acc) ctx0 .ivar0 :=
  typed_map_step (cl := closure m) (name := "n") (body := body) (Γb := [("n", .int)])
    (names := []) hm rfl (by intro x τ hx; cases hx) hv
    rfl rfl rfl rfl rfl rfl rfl rfl (body_typed []) brk index acc ha

/-- Parameter shadowing must restore the caller's nil type, independently of output elements. -/
theorem shadowed_caller {m : Machine} {o : ObjId}
    (hm : StateOk ctx0 [("n", .nilT)] .ivar0 (popMethodFrame m))
    (hv : denM (.arrayOf .int) (popMethodFrame m) (.ref o)) (brk : FrameId) (index : Nat) :
    StepSpec (popMethodFrame m) [("n", .nilT)] (.arrayOf (.cls "String"))
      (mapArrayStep m (closure m) brk o index []) ctx0 .ivar0 :=
  typed_map_step (cl := closure m) (name := "n") (body := body)
    (Γb := [("n", .int), ("n", .nilT)]) (names := []) hm rfl (by intro x τ hx; cases hx) hv
    rfl rfl rfl rfl rfl rfl rfl rfl (body_typed [("n", .nilT)]) brk index [] (by simp)

private def program (mname : String) : Checker.Expr :=
  .send (some (.array [.int 1, .int 2, .int 3])) mname [] (some (.block [.req "n"] [] body))

/-- Exact 092 source and its collect spelling, through actual dispatch and block allocation. -/
theorem source (mname : String) (hn : (mname == "map" || mname == "collect") = true) :
    SemSafeCtxA ctx0 [] .ivar0 (program mname) (.arrayOf (.cls "String")) ctx0 [] .ivar0 := by
  apply SemFlow.erase
  exact SemFlow.map (names := [])
    (SemFlow.embed .unknown (SemSafeCtxA.arrayLit
      (.cons SemSafeCtxA.intLit (.cons SemSafeCtxA.intLit (.cons SemSafeCtxA.intLit .nil rfl) rfl) rfl) rfl))
    hn rfl rfl rfl rfl rfl rfl rfl rfl (body_typed [])

theorem source_boot (hb : bootOkB = true) :
    RunSpec bootMachine (evalFrom bootMachine (program "map")) []
      (.arrayOf (.cls "String")) ctx0 .ivar0 :=
  source "map" rfl bootMachine (stateOk_boot hb)

private def arrayId : ObjId := bootMachine.heap.objs.size
private def caller : Machine := (Builtins.allocArr bootMachine #[.int 1, .int 2]).2
private def active : Machine := pushMethodFrame caller (mapFrame caller arrayId "map")
private def changed (xs : Array Value) : Machine :=
  { active with heap := active.heap.set arrayId { active.heap.get arrayId with payload := .arr xs } }

-- Replacement/append are read live. Shrink returns the accumulated result, not the receiver.
#guard match mapArrayStep (changed #[.int 1, .int 7, .int 3]) (closure active)
    caller.frames.size arrayId 1 [] with
  | .next n => (n.getLocal "n").identEq (.int 7)
  | _ => false
#guard match mapArrayStep (changed #[.int 1, .int 7, .int 3]) (closure active)
    caller.frames.size arrayId 2 [] with
  | .next n => (n.getLocal "n").identEq (.int 3)
  | _ => false
#guard match mapArrayStep (changed #[]) (closure active) caller.frames.size arrayId 1 [.int 9] with
  | .next n => match Interp.run 5 n with
    | .value (.ref o) out => o != arrayId && out.stack == caller.stack &&
        match (out.heap.get o).payload with
        | .arr xs => xs.size == 1 && (xs[0]!).identEq (.int 9)
        | _ => false
    | _ => false
  | _ => false

private def replacement : MethodDef := { owner := Boot.arrayId, params := [], body := .int 7 }
private def methodChange (mname : String) (md : MethodDef) : Heap :=
  defineMethod caller.heap Boot.arrayId mname md

#guard primitiveDispatchB caller.heap (nameFreeN ctx0)
#guard !primitiveDispatchB (methodChange "map" replacement) (nameFreeN ctx0)
#guard !primitiveDispatchB (methodChange "collect" replacement) (nameFreeN ctx0)
#guard !primitiveDispatchB (methodChange "map" { replacement with undefined := true }) (nameFreeN ctx0)
#guard !primitiveDispatchB (methodChange "map"
    { replacement with builtin := some "Array#map", visibility := .priv }) (nameFreeN ctx0)
#guard primitiveDispatchB (methodChange "map" replacement)
  (fun name => name != "map" && nameFreeN ctx0 name)
#guard arrayPayloadB (methodChange "map" replacement)

#print axioms string_results
#print axioms shadowed_caller
#print axioms source
#print axioms source_boot
end Checker.Soundness.Typed.TypedMapControls
