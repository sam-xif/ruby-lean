import RubyCore.Proof.RootFrameCalls

/-! Framing native dispatch helpers before ordinary sends. -/
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 600000
namespace RubyCore.Proof.Root
open Builtins Interp

attribute [rootFrameLem] newStop_rootFrame enumNext_rootFrame

@[rootFrameLem] theorem symOrStr_fun_frame (K : List Kont) (m : Machine) :
    symOrStr (pushRootK K m) = symOrStr m := by funext v; rfl
@[rootFrameLem] theorem procClosure_fun_frame (K : List Kont) (m : Machine) :
    procClosure? (pushRootK K m) = procClosure? m := by funext v; rfl
@[rootFrameLem] theorem constructResult_frame (K : List Kont) (hK : ContextFree K)
    (r : BRes) : constructResult (bRootPush K r) = rootFrameR K (constructResult r) := by
  cases r <;> simp (disch := assumption) only [constructResult, bRootPush, rootFrameLem]

@[rootFrameLem] theorem missingReason_update_frame (K : List Kont) (m : Machine) (r : MissingReason) :
    ({ pushRootK K m with missingReason := r } : Machine) =
      pushRootK K { m with missingReason := r } := rfl

open Lean Meta Elab Tactic in
elab "root_unwrap" : tactic => withMainContext do
  let wrapped (e : Lean.Expr) : Bool :=
    e.isAppOfArity ``bRootPush 2 ||
    (e.isAppOfArity ``Option.map 4 && (e.getAppArgs[2]!).isAppOf ``rootFrameR) ||
    (e.isAppOfArity ``Except.mapError 5 && (e.getAppArgs[3]!).isAppOf ``rootFrameR)
  let some (_, lhs, _) := (← getMainTarget).consumeMData.eq? | throwError "not equality"
  let some mat ← Meta.matchMatcherApp? lhs.consumeMData
    | throwError "not a result matcher"
  let some app := mat.discrs.findSome? (fun d => d.find? wrapped)
    | throwError "no framed discriminant"
  let result ← PrettyPrinter.delab app.getAppArgs.back!
  evalTactic (← `(tactic| focus
    cases hresult : $result <;>
      try simp_all only
        [rootFrameLem, bRootPush, Option.map_some, Option.map_none, Option.orElse, Except.mapError, if_true, if_false]))

open Lean Meta Elab Tactic in
elab "root_struct" : tactic => withMainContext do
  let some (_, lhs, _) := (← getMainTarget).consumeMData.eq? | throwError "not equality"
  let some app := lhs.find? fun e => e.isAppOfArity ``pushRootK 2
    | throwError "no framed machine"
  let machine ← PrettyPrinter.delab app.getAppArgs[1]!
  evalTactic (← `(tactic| solve | cases hactive : ($machine).activeEnumerator <;>
    simp_all [pushRootK, rootFrameR, withKont, List.append_assoc]))

open Lean Meta Elab Tactic in
elab "root_machine_ite" : tactic => withMainContext do
  let some (_, lhs, _) := (← getMainTarget).consumeMData.eq? | throwError "not equality"
  let some e := lhs.find? fun e => e.isIte && (e.getArg! 0 5).isConstOf ``Machine
    | throwError "no conditional machine"
  let condition ← PrettyPrinter.delab (e.getArg! 1 5)
  evalTactic (← `(tactic| by_cases hbranch : $condition <;> simp only [hbranch, if_true, if_false, Bool.false_eq_true, Bool.true_eq_false]))

syntax "root_native_walk" ident ident : tactic
macro_rules
  | `(tactic| root_native_walk $K $hK) => do
    let m := Lean.mkIdent `m
    `(tactic|
    repeat' (first
      | with_reducible rfl
      | root_progress (dsimp only)
      | root_progress (simp (maxSteps := 800000) (disch := assumption) only
          [rootFrameLem, Option.map_some, Option.map_none, Option.orElse,
            if_true, if_false, Bool.false_eq_true, Bool.true_eq_false, Machine.lexicalNamespace, moduleHook])
      | root_back $K $hK
      | root_unwrap
      | root_split
      | root_machine_ite
      | root_struct
      | root_progress (simp_all only
          [rootFrameLem, Option.map_some, Option.map_none, Option.orElse,
            if_true, if_false, Bool.false_eq_true, Bool.true_eq_false])))

@[rootFrameLem] theorem resetEnumerator_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (o : ObjId) :
    resetEnumerator (pushRootK K m) o = pushRootK K (resetEnumerator m o) := by
  unfold resetEnumerator
  simpa only [frameEnumState_default] using setEnumState_rootFrame K m o {}

@[rootFrameLem] theorem resetEnumerator_heap_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (h : Heap) (o : ObjId) :
    resetEnumerator { pushRootK K m with heap := h } o =
      pushRootK K (resetEnumerator { m with heap := h } o) :=
  resetEnumerator_frame K hK { m with heap := h } o

@[rootFrameLem] theorem macroVisibility_frame (K : List Kont) (m : Machine) (target : ObjId) :
    (pushRootK K m).macroVisibility target = m.macroVisibility target := by
  simp only [Machine.macroVisibility, Machine.currentDefinitionFrame, rootFrameLem]

@[rootFrameLem] theorem setDefinitionVisibility_frame (K : List Kont) (m : Machine) (vis : Visibility) :
    (pushRootK K m).setDefinitionVisibility vis = pushRootK K (m.setDefinitionVisibility vis) := by
  simp only [Machine.setDefinitionVisibility, rootFrameLem]
  split <;> rfl

@[rootFrameLem] theorem allocEnumerator_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (data : EnumData) (klass := Boot.enumeratorId) :
    allocEnumerator (pushRootK K m) data klass = ((allocEnumerator m data klass).1, pushRootK K (allocEnumerator m data klass).2) := by
  have hLock := hK.hashLockFree
  unfold allocEnumerator
  root_native_walk K hK

@[rootFrameLem] theorem enumStop_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (original : Value) :
    enumStop (pushRootK K m) original = rootFrameR K (enumStop m original) := by
  have hLock := hK.hashLockFree
  unfold enumStop
  root_native_walk K hK

@[rootFrameLem] theorem stepParamBinding_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (pending : List (Param × Value)) (body : Expr) :
    stepParamBinding (pushRootK K m) pending body = rootFrameR K (stepParamBinding m pending body) := by
  have hLock := hK.hashLockFree
  unfold stepParamBinding
  root_native_walk K hK

@[rootFrameLem] theorem callStringPlusBuiltin_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (args : List Value)
    (kw : List (Value × Value)) :
    callStringPlusBuiltin (pushRootK K m) recv args kw = rootFrameR K (callStringPlusBuiltin m recv args kw) := by
  have hLock := hK.hashLockFree
  unfold callStringPlusBuiltin
  root_native_walk K hK

def enumInitializeView (m : Machine) (o : ObjId) (bid : String) (args : List Value)
    (blk : Option Value) : StepResult :=
  if (m.heap.get o).frozen then raiseFrozen m (.ref o) else
  if (enumState m o).caller.isSome then .unsupported "reinitializing a running Enumerator" else
  let obj := m.heap.get o
  if bid == "Enumerator#initialize" then
    match blk with
    | none => .next (raiseErr m Boot.argumentErrorId "tried to create Proc object without a block")
    | some block =>
      if args.length > 1 then enumArity m args.length "0..1" else
      match enumSizeValue m (args.headD .nil) with
      | .error r => r
      | .ok size =>
        let (go, h) := m.heap.alloc { klass := Boot.generatorId, payload := .generator (some block) }
        let data : EnumData := { recv := .ref go, size }
        let h := h.set o { obj with payload := .enumerator (some data) }
        .next (withCtl (resetEnumerator { m with heap := h } o) (.value (.ref o)))
  else if bid == "Enumerator::Generator#initialize" then
    let block := match args with | [v] => some v | [] => blk | _ => none
    if args.length > 1 then enumArity m args.length "0..1" else
    match block with
    | none => .next (raiseErr m Boot.localJumpErrorId "no block given")
    | some (.ref p) => match (m.heap.get p).payload with
      | .proc _ => .next { m with heap := m.heap.set o { obj with payload := .generator (some (.ref p)) }, ctl := .value (.ref o) }
      | _ => .unsupported "Generator initializer requires a Proc"
    | _ => .unsupported "Generator initializer requires a Proc"
  else
    if !args.isEmpty then enumArity m args.length "0" else
    match blk with
    | none => .next (raiseErr m Boot.localJumpErrorId "no block given")
    | some block => .next { m with heap := m.heap.set o { obj with payload := .yielder (some block) none }, ctl := .value (.ref o) }

@[rootFrameLem] theorem enumInitialize_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (o : ObjId) (bid : String) (args : List Value)
    (blk : Option Value) :
    enumInitialize (pushRootK K m) o bid args blk = rootFrameR K (enumInitialize m o bid args blk) := by
  have hLock := hK.hashLockFree
  change enumInitializeView (pushRootK K m) o bid args blk = rootFrameR K (enumInitializeView m o bid args blk)
  unfold enumInitializeView
  cases hs : enumSizeValue m (args.headD .nil) <;>
    simp (disch := assumption) only [rootFrameLem, hs, Except.mapError]
  all_goals root_native_walk K hK

@[rootFrameLem] theorem enumAllocate_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (klass : ObjId) :
    enumAllocate (pushRootK K m) klass = ((enumAllocate m klass).1, pushRootK K (enumAllocate m klass).2) := by
  have hLock := hK.hashLockFree
  unfold enumAllocate
  root_native_walk K hK

@[rootFrameLem] theorem enumState_feed_frame (K : List Kont) (m : Machine) (o : ObjId) :
    (enumState (pushRootK K m) o).feed = (enumState m o).feed := by
  rw [enumState_rootFrame]; rfl

@[rootFrameLem] theorem enumState_finished_frame (K : List Kont) (m : Machine) (o : ObjId) :
    (enumState (pushRootK K m) o).finished = (enumState m o).finished := by
  rw [enumState_rootFrame]; rfl

@[rootFrameLem] theorem enumState_lookahead_frame (K : List Kont) (m : Machine) (o : ObjId) :
    (enumState (pushRootK K m) o).lookahead = (enumState m o).lookahead := by
  rw [enumState_rootFrame]; rfl

@[rootFrameLem] theorem enumState_peek_frame (K : List Kont) (m : Machine) (o : ObjId) :
    (enumState (pushRootK K m) o).peek = (enumState m o).peek := by
  rw [enumState_rootFrame]; rfl

@[rootFrameLem] theorem enumState_values_frame (K : List Kont) (m : Machine) (o : ObjId) :
    (enumState (pushRootK K m) o).values = (enumState m o).values := by
  rw [enumState_rootFrame]; rfl

@[rootFrameLem] theorem enumState_feed_update_frame (K : List Kont) (m : Machine)
    (o : ObjId) (v : Option Value) :
    setEnumState (pushRootK K m) o { enumState (pushRootK K m) o with feed := v } =
      pushRootK K (setEnumState m o { enumState m o with feed := v }) := by
  rw [enumState_rootFrame]
  exact setEnumState_rootFrame K m o { enumState m o with feed := v }

#print axioms resetEnumerator_frame
#print axioms enumInitialize_frame
end RubyCore.Proof.Root
