import RubyCore.Proof.RootFrameReflect
import RubyCore.Proof.RootFrameBuiltins

/-! Root-execution framing for method and class entry. -/
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace RubyCore.Proof.Root
open Builtins Interp

open Lean Meta Elab Tactic in
elab "root_progress" "(" t:tacticSeq ")" : tactic => do
  let before ← (← getGoals).mapM fun g => g.getType
  evalTactic t
  let after ← (← getGoals).mapM fun g => g.getType
  if before == after then throwError "no progress"

syntax "root_back" ident ident : tactic
open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| root_back $K:ident $hK:ident) => withMainContext do
    let target := (← getMainTarget).consumeMData
    let some (_, _, rhs) := target.eq? | throwError "not an equality"
    let rhs := rhs.consumeMData
    if rhs.isAppOfArity ``StepResult.next 1 then
      evalTactic (← `(tactic| apply congrArg StepResult.next; root_back $K $hK))
    else if rhs.isAppOfArity ``Option.some 2 then
      evalTactic (← `(tactic| apply congrArg some; root_back $K $hK))
    else
      unless rhs.isAppOfArity ``rootFrameR 2 || rhs.isAppOfArity ``pushRootK 2 do
        throwError "not a framed result"
      let .const fn _ := rhs.getAppArgs[1]!.getAppFn | throwError "not a named operation"
      let .str _ name := fn | throwError "not a named operation"
      let lemma := mkIdent (Name.str `RubyCore.Proof.Root
        (if fn == ``List.foldl then "foldSetLocal_frame" else name ++ "_frame"))
      let m := mkIdent `m
      evalTactic (← `(tactic|
        (first | rw [← $lemma $K $hK] | rw [← $lemma $K]) <;>
          (congr 1 <;> (first | root_back $K $hK |
            (solve | cases henum : ($m).activeEnumerator <;> simp_all [pushRootK])))))

open Lean Meta Elab Tactic in
elab "root_split" : tactic => withMainContext do
  let some (_, lhs, _) := (← getMainTarget).consumeMData.eq? | throwError "not an equality"
  let lhs := lhs.consumeMData
  if lhs.isIte || lhs.isDIte then
    let (yes, no) ← (← getMainGoal).byCases (lhs.getArg! 1 5)
    replaceMainGoal [← simpIfTarget yes.mvarId (useNewSemantics := true),
      ← simpIfTarget no.mvarId (useNewSemantics := true)]
  else
    let some _ ← Meta.matchMatcherApp? lhs | throwError "not a matcher"
    replaceMainGoal (← Meta.Split.splitMatch (← getMainGoal) lhs)

syntax "root_dispatch_walk" ident ident : tactic
macro_rules
  | `(tactic| root_dispatch_walk $K $hK) => do
    let m := Lean.mkIdent `m
    `(tactic|
    repeat' (first | with_reducible rfl | root_progress (dsimp only) |
      root_progress (simp only [← pushRootK_setHeap $K $m]) |
      root_progress (simp (maxSteps := 800000) (disch := assumption) only [rootFrameLem, Option.map_some, Option.map_none, Except.mapError,
        Machine.lexicalNamespace, moduleHook]) |
      root_back $K $hK | root_split |
      (solve | cases henum : ($m).activeEnumerator <;>
        simp_all [pushRootK, rootFrameR, withKont, List.append_assoc])))

theorem foldMachine_frame {α : Type} (K : List Kont) (f : Machine → α → Machine)
    (hf : ∀ m a, f (pushRootK K m) a = pushRootK K (f m a)) :
    ∀ l m, List.foldl f (pushRootK K m) l = pushRootK K (List.foldl f m l)
  | [], _ => rfl
  | a :: rest, m => by
    simp only [List.foldl_cons, hf]
    exact foldMachine_frame K f hf rest (f m a)

@[rootFrameLem] theorem foldSetLocal_frame (K : List Kont) (l : List (String × Value))
    (m : Machine) :
    l.foldl (fun m p => m.setLocal p.1 p.2) (pushRootK K m) =
      pushRootK K (l.foldl (fun m p => m.setLocal p.1 p.2) m) :=
  foldMachine_frame K _ (fun m p => setLocal_frame K m p.1 p.2) l m

@[rootFrameLem] theorem eigenclassOf_heap_frame (K : List Kont) (m : Machine)
    (h : Heap) (o : ObjId) :
    eigenclassOf { pushRootK K m with heap := h } o =
      ((eigenclassOf { m with heap := h } o).1,
        pushRootK K (eigenclassOf { m with heap := h } o).2) :=
  eigenclassOf_frame K { m with heap := h } o

@[rootFrameLem] theorem foldHashPairs_frame (K : List Kont) (m : Machine)
    (acc : List (List Value)) (xs : List (Value × Value)) :
    xs.foldl (fun x kv =>
      (x.1 ++ [[(allocArr x.2 #[kv.1, kv.2]).1]], (allocArr x.2 #[kv.1, kv.2]).2))
        (acc, pushRootK K m) =
      ((xs.foldl (fun x kv =>
        (x.1 ++ [[(allocArr x.2 #[kv.1, kv.2]).1]], (allocArr x.2 #[kv.1, kv.2]).2)) (acc, m)).1,
       pushRootK K ((xs.foldl (fun x kv =>
        (x.1 ++ [[(allocArr x.2 #[kv.1, kv.2]).1]], (allocArr x.2 #[kv.1, kv.2]).2)) (acc, m)).2)) := by
  apply foldPair_frame K
  intro m acc kv
  simp only [rootFrameLem]

/-! Proof-only method-entry stages. Their composition is definitionally the runtime operation. -/
def methodFrame (m : Machine) (recv : Value) (mname : String) (md : MethodDef)
    (args : List Value) (blk : Option Value)
    (localsA localsB predeclared : List (String × Value))
    (pending : List (Param × Value)) (optOmitted kwOmitted : List (String × Expr)) : StepResult :=
    let frameBlk := match md.capturedFrame with
      | some cf => (m.frames.getD cf default).blk
      | none => blk
    let frame : Frame :=
      { self := recv, locals := localsA ++ predeclared,
        localAlias := if md.forTargets.isSome then md.capturedFrame else none,
        defmod := md.definee.getD md.owner, methodOwner := some md.owner,
        definitionFrame := md.definitionFrame,
        kind := .method, blk := frameBlk, callBlk := blk,
        meth := md.superName.getD mname, superScope := md.superScope,
        runParams := md.params, runFromDM := md.fromBlock,
        cref := md.cref, captured := md.capturedFrame, libraryOrigin := md.fromPrelude }
    let fid := m.frames.size
    let m := { m with frames := m.frames.push frame, stack := fid :: m.stack }
    let boundary := if md.fromBlock then Kont.dmFrameK fid md.body else .frameK fid
    let m := { m with kont := boundary :: m.kont }
    let m := if pending.isEmpty then m else { m with kont := .paramBindK pending md.body :: m.kont }
    -- Defaults complete by delivering a value to the pending binding phase.
    let body := if pending.isEmpty then md.body else Expr.nil
    if let some targets := md.forTargets then
      startForBindings m targets md.forMultiple args md.body else
    -- positional-opt defaults first, then keyword defaults (Ruby order [V]).
    match optOmitted ++ kwOmitted with
    | [] =>
      let m := localsB.foldl (fun m (nv : String × Value) => m.setLocal nv.1 nv.2) m
      .next (withCtl m (.eval body))
    | (n0, d0) :: more =>
      .next (withKont m (.eval d0) (.optDefK n0 more localsB body))

@[rootFrameLem] theorem methodFrame_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (mname : String) (md : MethodDef)
    (args : List Value) (blk : Option Value) (localsA localsB predeclared : List (String × Value))
    (pending : List (Param × Value)) (optOmitted kwOmitted : List (String × Expr)) :
    methodFrame (pushRootK K m) recv mname md args blk localsA localsB predeclared pending optOmitted kwOmitted =
      rootFrameR K (methodFrame m recv mname md args blk localsA localsB predeclared pending optOmitted kwOmitted) := by
  unfold methodFrame
  simp only [rootFrameLem]
  cases ht : md.forTargets with
  | some targets =>
    simp only [ht]
    rw [← startForBindings_frame K]
    congr 1
    cases he : m.activeEnumerator <;> cases hp : pending.isEmpty <;>
      simp [pushRootK, he, hp]
  | none =>
    simp only [ht]
    cases hd : optOmitted ++ kwOmitted with
    | nil =>
      simp only [hd, rootFrameLem]
      apply congrArg StepResult.next
      rw [← withCtl_frame]
      congr 1
      rw [← foldSetLocal_frame]
      congr 1
      cases he : m.activeEnumerator <;> cases hp : pending.isEmpty <;>
        simp [pushRootK, he, hp]
    | cons p ps =>
      simp only [hd, rootFrameLem]
      apply congrArg StepResult.next
      rw [← withKont_frame]
      congr 1
      cases he : m.activeEnumerator <;> cases hp : pending.isEmpty <;>
        simp [pushRootK, he, hp]


def methodParams (m : Machine) (recv : Value) (mname : String) (md : MethodDef)
    (args : List Value) (blk : Option Value)
    (kw : List (Value × Value)) (fp : FullParams) (leftover : List (Value × Value)) : StepResult :=
  let np := fp.pre.length; let nopt := fp.opt.length; let npost := fp.post.length
  let n := args.length
    let preVals := args.take np
    let postVals := args.drop (n - npost)
    let middle := (args.drop np).take (n - npost - np)
    let filled := min nopt middle.length
    let optFilled := ((fp.opt.take filled).map (·.1)).zip (middle.take filled)
    let optOmitted := fp.opt.drop filled           -- (name, default-expr), eval in-frame
    let restVals := middle.drop filled
    -- keyword partition: provided bind directly; omitted-with-default via optDefK.
    let kwProvided := fp.keys.filterMap (fun (kn, _) => (kwLookup kw kn).map (fun v => (kn, v)))
    let kwOmitted := fp.keys.filterMap (fun (kn, d?) =>
      if (kwLookup kw kn).isNone then d?.map (fun d => (kn, d)) else none)
    -- Phase A: pre + filled optionals + provided keywords (visible to defaults).
    let localsA := fp.pre.zip preVals ++ optFilled ++ kwProvided
    -- Phase B (bound AFTER defaults [V]): rest, post, block, kwrest.
    let (restBinding, m) := match fp.rest? with
      | some r => let (rv, m) := Builtins.allocArr m restVals.toArray; ([(r, rv)], m)
      | none => ([], m)
    let (kwrestBinding, m) := match fp.kwrest? with
      | some (some kr) => let (hv, m) := Builtins.allocHsh m leftover.toArray; ([(kr, hv)], m)
      | _ => ([], m)
    let localsB := restBinding ++ fp.post.zip postVals ++
      (match fp.block? with | some b => [(b, blk.getD .nil)] | none => []) ++ kwrestBinding
    -- Capture raw destructuring slots now, but expand only after all defaults.
    -- Names inside them are nil during defaults, including define_method captures.
    let pending := fp.destrs.map fun (sn, subs) =>
      (Param.destr subs, (((localsA ++ localsB).find? (·.1 == sn)).map (·.2)).getD .nil)
    let destrNames := fp.destrs.flatMap fun (_, subs) => destructureNames subs (destrDepth subs + 1)
    let notSynth : (String × Value) → Bool := fun b => !(fp.destrs.any (·.1 == b.1))
    let localsA := localsA.filter notSynth
    let localsB := localsB.filter notSynth
    -- Pre-declare every formal that is bound *later* (`localsB` after defaults,
    -- and the omitted defaults themselves) as nil in this frame, so the
    -- `setLocal` calls below resolve here rather than walking a `capturedFrame`
    -- chain into the enclosing scope and clobbering a same-named outer local
    -- (only reachable for `define_method` bodies, L64; harmless otherwise —
    -- an unbound local reads as nil either way).
    -- ...and, for the same reason, every name the *body* binds itself: a
    -- `define_method` block's block-locals (L125/C35). Ordinary `def`s carry an
    -- empty list here.
    let predeclared := destrNames.map (fun n => (n, Value.nil)) ++ localsB.map (fun b => (b.1, Value.nil)) ++
      (optOmitted ++ kwOmitted).map (fun d => (d.1, Value.nil)) ++
      md.declared.map (fun n => (n, Value.nil))
    -- `blk`: an ordinary method sees its caller's block. A `define_method` body
    -- is a *block*, so `block_given?`/`yield` inside it refer to the block of the
    -- scope it was defined in, not the call [V] (test_method_204) — while an
    -- explicit `&b` param still binds the *call*'s block (bound in `localsB`).
    methodFrame m recv mname md args blk localsA localsB predeclared pending optOmitted kwOmitted


@[rootFrameLem] theorem methodParams_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (mname : String) (md : MethodDef)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value)) (fp : FullParams) (leftover : List (Value × Value)) :
    methodParams (pushRootK K m) recv mname md args blk kw fp leftover =
      rootFrameR K (methodParams m recv mname md args blk kw fp leftover) := by
  have hLock := hK.hashLockFree
  unfold methodParams
  cases hr : fp.rest? <;> cases hk : fp.kwrest? with
  | none => simp (disch := assumption) only [rootFrameLem, hr, hk]
  | some kr => cases kr <;> simp (disch := assumption) only [rootFrameLem, hr, hk]

def methodArity (m : Machine) (recv : Value) (mname : String) (md : MethodDef)
    (args : List Value) (blk : Option Value)
    (kw : List (Value × Value)) (fp : FullParams) (hasKw : Bool) : StepResult :=
  let np := fp.pre.length; let nopt := fp.opt.length; let npost := fp.post.length
  let n := args.length
  let required := np + npost
  let arityOk := match fp.rest? with
    | some _ => n ≥ required
    | none => n ≥ required && n ≤ required + nopt
  if !arityOk then
    let expected := match fp.rest? with
      | some _ => s!"{required}+"
      | none => if nopt == 0 then toString required else s!"{required}..{required + nopt}"
    -- CRuby appends *all* required keywords (those without a default) to the arity
    -- error, e.g. `(given 1, expected 0; required keywords: a, b)` — even ones the
    -- caller supplied, since the positional-arity check fires before keywords are
    -- bound (kwargs/004: `c:` is listed though `c: 3` was passed). Names are *bare*
    -- here (no leading `:`), unlike the standalone "missing keyword: :a" message.
    let reqKeys := fp.keys.filterMap (fun (kn, d?) => if d?.isNone then some kn else none)
    let kwSuffix := if reqKeys.isEmpty then ""
      else s!"; required keyword{if reqKeys.length == 1 then "" else "s"}: " ++
           String.intercalate ", " reqKeys
    .next (raiseErr m Boot.argumentErrorId
      s!"wrong number of arguments (given {n}, expected {expected}{kwSuffix})")
  else
    -- keyword validation (missing required / unknown, byte-exact ArgumentError [V]).
    let missing := fp.keys.filterMap (fun (kn, d?) =>
      if (kwLookup kw kn).isNone && d?.isNone then some kn else none)
    let keyNames := fp.keys.map (·.1)
    let leftover := kw.filter (fun p => match p.1 with | .sym s => !keyNames.contains s | _ => true)
    if hasKw && !missing.isEmpty then
      .next (raiseErr m Boot.argumentErrorId
        s!"missing keyword{if missing.length == 1 then "" else "s"}: {kwNameList missing}")
    else if hasKw && fp.kwrest?.isNone && !leftover.isEmpty then
      let names := leftover.filterMap (fun p => match p.1 with | .sym s => some s | _ => none)
      .next (raiseErr m Boot.argumentErrorId
        s!"unknown keyword{if names.length == 1 then "" else "s"}: {kwNameList names}")
    else
    -- positional distribution: pre from the front, post from the back, optionals
    -- fill the leftmost middle args, a `*rest` absorbs the surplus (artifact 02 §3).
    methodParams m recv mname md args blk kw fp leftover


@[rootFrameLem] theorem methodArity_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (mname : String) (md : MethodDef)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value)) (fp : FullParams) (hasKw : Bool) :
    methodArity (pushRootK K m) recv mname md args blk kw fp hasKw =
      rootFrameR K (methodArity m recv mname md args blk kw fp hasKw) := by
  have hLock := hK.hashLockFree
  unfold methodArity
  root_dispatch_walk K hK

def methodView (m : Machine) (recv : Value) (mname : String) (md : MethodDef)
    (args : List Value) (blk : Option Value)
    (kw : List (Value × Value)) : StepResult :=
  let fp? := classifyFull md.params
  if fp?.isNone then
    .unsupported "non-canonical method parameter shape"
  else
  let fp := fp?.getD ⟨[], [], none, [], [], none, none, []⟩
  let hasKw := !fp.keys.isEmpty || fp.kwrest?.isSome
  -- Ruby-3 separation: a callee without keyword params receives a keyword bundle
  -- as one trailing positional Hash (empty vanishes) [V].
  let (args, m) := if hasKw then (args, m) else appendKwHash m args kw
  methodArity m recv mname md args blk kw fp hasKw


@[rootFrameLem] theorem methodView_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (mname : String) (md : MethodDef)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value)) :
    methodView (pushRootK K m) recv mname md args blk kw =
      rootFrameR K (methodView m recv mname md args blk kw) := by
  have hLock := hK.hashLockFree
  unfold methodView
  dsimp only
  split
  · rfl
  · split <;> simp (disch := assumption) only [rootFrameLem]

@[rootFrameLem] theorem enterUserMethod_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (mname : String) (md : MethodDef)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value) := []) :
    enterUserMethod (pushRootK K m) recv mname md args blk kw = rootFrameR K (enterUserMethod m recv mname md args blk kw) := by
  have hLock := hK.hashLockFree
  change methodView (pushRootK K m) recv mname md args blk kw =
    rootFrameR K (methodView m recv mname md args blk kw)
  exact methodView_frame K hK m recv mname md args blk kw


end RubyCore.Proof.Root
