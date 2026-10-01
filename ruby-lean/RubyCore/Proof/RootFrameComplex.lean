import RubyCore.Proof.RootFrameNumbers

/-! Complex actions frame compositionally before their state is supplied.
The relation also covers a captured Machine read by `get`: its observations
are framed before the remainder of the action is compared. -/
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace RubyCore.Proof.Root
open Builtins

def CRel {α : Type} (K : List Kont) (left right : ComplexM α) : Prop :=
  ∀ m, left (pushRootK K m) = cRootPush K (right m)

theorem CRel.pure {α : Type} (K : List Kont) (a : α) : CRel K (pure a) (pure a) := fun _ => rfl

theorem CRel.throw {α : Type} (K : List Kont) (left right : BRes)
    (h : left = bRootPush K right) :
    CRel K (throw left : ComplexM α) (throw right) := by
  intro m
  change Except.error left = Except.error (bRootPush K right)
  rw [h]

theorem CRel.bind {α β : Type} (K : List Kont) (x y : ComplexM α)
    (f g : α → ComplexM β) (hx : CRel K x y) (hf : ∀ a, CRel K (f a) (g a)) :
    CRel K (x >>= f) (y >>= g) := by
  intro m
  change (x (pushRootK K m) >>= fun (a, s) => f a s) =
    cRootPush K (y m >>= fun (a, s) => g a s)
  rw [hx m]
  cases y m with
  | error r => rfl
  | ok p => exact hf p.1 p.2

theorem CRel.throwBind {α β : Type} (K : List Kont) (left right : BRes)
    (f g : α → ComplexM β) (h : left = bRootPush K right) :
    CRel K ((MonadExcept.throw left : ComplexM α) >>= f) ((MonadExcept.throw right : ComplexM α) >>= g) := by
  intro m
  change Except.error left = Except.error (bRootPush K right)
  rw [h]

theorem CRel.pureBind {α β : Type} (K : List Kont) (a : α)
    (f g : α → ComplexM β) (hf : CRel K (f a) (g a)) :
    CRel K (Pure.pure a >>= f) (Pure.pure a >>= g) := hf

theorem CRel.getBind {α : Type} (K : List Kont) (f g : Machine → ComplexM α)
    (hf : ∀ m, CRel K (f (pushRootK K m)) (g m)) :
    CRel K (get >>= f) (get >>= g) := fun m => hf m m

theorem CRel.rat (K : List Kont) (n d : Int) : CRel K (complexRat n d) (complexRat n d) :=
  fun m => complexRat_frame K m n d

theorem CRel.ite {α : Type} (K : List Kont) (p : Prop) [Decidable p]
    (a b c d : ComplexM α) (hab : CRel K a b) (hcd : CRel K c d) :
    CRel K (if p then a else c) (if p then b else d) := by
  by_cases h : p <;> simp only [h, ite_true, ite_false] <;> assumption

open Lean Elab Tactic in
elab "crel_atom" : tactic => withMainContext do
  let target ← getMainTarget
  unless target.isAppOfArity ``CRel 4 do throwError "not an action relation"
  let action := target.getAppArgs[2]!.headBeta
  if action.isIte then
    evalTactic (← `(tactic| apply CRel.ite))
    return
  let .const head _ := action.getAppFn | throwError "not an atomic action"
  if head == ``Pure.pure || head == ``StateT.pure then
    evalTactic (← `(tactic| exact CRel.pure _ _))
  else if head == ``Bind.bind || head == ``StateT.bind then
    let firstAction := action.getAppArgs[action.getAppArgs.size - 2]!
    let firstHead := firstAction.getAppFn
    if firstHead.isConstOf ``MonadStateOf.get || firstHead.isConstOf ``getThe ||
        firstHead.isConstOf ``MonadState.get || firstHead.isConstOf ``StateT.get then
      evalTactic (← `(tactic| apply CRel.getBind))
    else if firstHead.isConstOf ``MonadExcept.throw || firstHead.isConstOf ``throwThe then
      evalTactic (← `(tactic| apply CRel.throwBind; rfl))
    else
      evalTactic (← `(tactic| apply CRel.bind))
  else if head == ``complexRat then
    evalTactic (← `(tactic| exact CRel.rat _ _ _))
  else if head == ``MonadExcept.throw || head == ``throwThe then
    evalTactic (← `(tactic| apply CRel.throw; rfl))
  else throwError "unrecognized action {head}"

open Lean Elab Tactic in
elab "crel_intro" : tactic => withMainContext do
  unless (← getMainTarget).isForall do throwError "not a binder"
  evalTactic (← `(tactic| intro _))

open Lean Meta Elab Tactic in
elab "crel_split" : tactic => withMainContext do
  let target ← getMainTarget
  unless target.isAppOfArity ``CRel 4 do throwError "not an action relation"
  let e := target.getAppArgs[2]!
  if e.isIte || e.isDIte then
    let (yes, no) ← (← getMainGoal).byCases (e.getArg! 1 5)
    let yes ← simpIfTarget yes.mvarId (useNewSemantics := true)
    let no ← simpIfTarget no.mvarId (useNewSemantics := true)
    replaceMainGoal [yes, no]
    evalTactic (← `(tactic| all_goals try simp_all only [ite_true, ite_false, dite_true, dite_false]))
  else
    let some _ ← Meta.matchMatcherApp? e | throwError "not a matcher"
    replaceMainGoal (← Meta.Split.splitMatch (← getMainGoal) e)

syntax "crel_walk" : tactic
macro_rules
  | `(tactic| crel_walk) => `(tactic|
      repeat' ((try simp only [rootFrameLem, ite_true, ite_false, dite_true, dite_false,
          Bool.false_eq_true, Bool.true_eq_false, String.reduceEq]) <;>
        first | contradiction | crel_atom | crel_split | crel_intro))

private def scalarTail (h : Heap) (op : String) (a b : Value) : ComplexM Value := do
  match a, b with
  | .int x, .int y =>
    match op with
    | "+" => return .int (x + y)
    | "-" => return .int (x - y)
    | "*" => return .int (x * y)
    | _ => complexRat x y
  | _, _ =>
    match exactFraction? h a, exactFraction? h b with
    | some (n, d), some (x, y) =>
      match op with
      | "+" => complexRat (n * (y : Int) + x * (d : Int)) (d * y)
      | "-" => complexRat (n * (y : Int) - x * (d : Int)) (d * y)
      | "*" => complexRat (n * x) (d * y)
      | _ => complexRat (n * (y : Int)) ((d : Int) * x)
    | _, _ =>
      let x := realFloat h a; let y := realFloat h b
      if x.isNaN || x.isInf || y.isNaN || y.isInf then
        throw (.unsupported "Complex arithmetic with non-finite components")
      return .flt (if op == "+" then x + y else if op == "-" then x - y
        else if op == "*" then x * y else x / y)

private theorem scalarTail_rel (K : List Kont) (h : Heap) (op : String) (a b : Value) :
    CRel K (scalarTail h op a b) (scalarTail h op a b) := by
  unfold scalarTail
  crel_walk

private def scalarCheckedTail (h : Heap) (op : String) (a b : Value) : ComplexM Value := do
  if (rationalPayload? h b).isSome && (num? a).isSome &&
      programOverridden h ["coerce"] Boot.rationalId then
    throw (.unsupported "Complex component arithmetic through Rational#coerce override")
  scalarTail h op a b

private theorem scalarCheckedTail_rel (K : List Kont) (h : Heap) (op : String) (a b : Value) :
    CRel K (scalarCheckedTail h op a b) (scalarCheckedTail h op a b) := by
  unfold scalarCheckedTail
  split
  · apply CRel.throwBind; rfl
  · exact scalarTail_rel K h op a b

private def scalarHead (h : Heap) (op : String) (a b : Value)
    (tail : ComplexM Value) : ComplexM Value := do
  unless nativeReal h a && nativeReal h b do
    throw (.unsupported "Complex arithmetic with custom numeric components")
  let owner := className h (realClassOf h a)
  if op != "quo" then
    unless (lookup h a op).any (fun (_, md) => !md.undefined && md.builtin == some (owner ++ "#" ++ op)) do
      throw (.unsupported "Complex arithmetic through an overridden component operator")
  else if programOverridden h ["quo", "/", "to_r"] (classOf h a) then
    throw (.unsupported "Complex quotient through overridden numeric conversion")
  if op == "+" then
    if a.identEq (.int 0) then return b
    if b.identEq (.int 0) then return a
  if op == "-" && b.identEq (.int 0) then return a
  if op == "*" then
    if b.identEq (.int 1) then return a
    match a with
    | .int n =>
      if b.identEq (.int 0) then return .int 0
      if n == 1 then return b
    | _ => pure ()
  tail

private theorem scalarHead_rel (K : List Kont) (h : Heap) (op : String) (a b : Value)
    (tail : ComplexM Value) (ht : CRel K tail tail) :
    CRel K (scalarHead h op a b tail) (scalarHead h op a b tail) := by
  unfold scalarHead
  repeat' ((try simp only [rootFrameLem, ite_true, ite_false, dite_true, dite_false,
      Bool.false_eq_true, Bool.true_eq_false, String.reduceEq]) <;>
    first | exact ht | contradiction | crel_atom | crel_split | crel_intro)

private theorem scalar_rel (K : List Kont) (op : String) (a b : Value) :
    CRel K (complexScalar op a b) (complexScalar op a b) := by
  change CRel K (get >>= fun m => scalarHead m.heap op a b (scalarCheckedTail m.heap op a b))
    (get >>= fun m => scalarHead m.heap op a b (scalarCheckedTail m.heap op a b))
  apply CRel.getBind
  intro m
  exact scalarHead_rel K m.heap op a b _ (scalarCheckedTail_rel K m.heap op a b)

@[rootFrameLem] theorem complexScalar_frame (K : List Kont) (m : Machine) (op : String) (a b : Value) :
    complexScalar op a b (pushRootK K m) = cRootPush K (complexScalar op a b m) := scalar_rel K op a b m

attribute [rootFrameLem] scalar_rel

@[rootFrameLem] theorem CRel.alloc (K : List Kont) (r i : Value) :
    CRel K (complexAlloc r i) (complexAlloc r i) := fun m => complexAlloc_frame K m r i

@[rootFrameLem] theorem CRel.negate (K : List Kont) (v : Value) :
    CRel K (complexNegate v) (complexNegate v) := fun m => complexNegate_frame K m v

@[rootFrameLem] theorem CRel.result (K : List Kont) (r i : Value) (canonical : Bool) :
    CRel K (complexResult r i canonical) (complexResult r i canonical) := by
  unfold complexResult
  apply CRel.getBind
  intro m
  exact CRel.alloc K _ _

@[rootFrameLem] theorem CRel.binary (K : List Kont) (op : String) (r i other : Value) :
    CRel K (complexBinary op r i other) (complexBinary op r i other) := by
  unfold complexBinary
  repeat' ((try dsimp only) <;> (try simp_all only [rootFrameLem, ite_true, ite_false, dite_true, dite_false,
      Bool.false_eq_true, Bool.true_eq_false, String.reduceEq]) <;>
    first | exact scalar_rel _ _ _ _ | exact CRel.result _ _ _ _ |
      contradiction | crel_atom | crel_split | crel_intro)

@[rootFrameLem] theorem CRel.constructor (K : List Kont) (args : List Value) :
    CRel K (complexConstructor args) (complexConstructor args) := by
  unfold complexConstructor
  repeat' ((try dsimp only) <;> (try simp_all only [rootFrameLem, ite_true, ite_false, dite_true, dite_false,
      Bool.false_eq_true, Bool.true_eq_false, String.reduceEq]) <;>
    first | exact CRel.binary _ _ _ _ _ | exact CRel.alloc _ _ _ |
      contradiction | crel_atom | crel_split | crel_intro)

theorem finishComplex_frame (K : List Kont) (m : Machine) (action : ComplexM Value)
    (h : CRel K action action) :
    finishComplex (pushRootK K m) action = bRootPush K (finishComplex m action) := by
  unfold finishComplex
  change (match action (pushRootK K m) with | .ok (v, n) => BRes.ok v n | .error r => r) =
    bRootPush K (match action m with | .ok (v, n) => BRes.ok v n | .error r => r)
  rw [h m]
  cases action m <;> rfl

@[rootFrameLem] theorem CRel.coerceAlloc (K : List Kont) (b recv : Value) :
    CRel K (do
      let x ← complexAlloc b (.int 0)
      let m ← get
      let (v, m) := allocArr m #[x, recv]
      set m
      return v) (do
      let x ← complexAlloc b (.int 0)
      let m ← get
      let (v, m) := allocArr m #[x, recv]
      set m
      return v) := by
  apply CRel.bind
  · exact CRel.alloc K _ _
  · intro x
    apply CRel.getBind
    intro m _
    rfl

attribute [rootFrameLem] finishComplex_frame CRel.bind CRel.pure

@[rootFrameLem] theorem runComplex_frame (K : List Kont) (m : Machine)
    (bid : String) (recv : Value) (args : List Value) (hLock : HashLockFree K) :
    runComplex bid recv args (pushRootK K m) = bRootPush K (runComplex bid recv args m) := by
  rw [runComplex.eq_def, runComplex.eq_def]
  root_simp
  root_arms
  all_goals root_hof
  · apply finishComplex_frame
    crel_walk

#print axioms complexScalar_frame
#print axioms CRel.binary
#print axioms CRel.constructor
#print axioms runComplex_frame
end RubyCore.Proof.Root
