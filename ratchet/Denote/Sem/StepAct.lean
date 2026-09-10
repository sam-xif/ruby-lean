import Denote.Sem.StepSupport

/-!
# `Denote/Sem/StepAct.lean` — `enterUserMethod`, through a **mirror gated by `rfl`**

Stage 2's hardest helper, and the one three previous attempts parked
(`notes.md` §`enterUserMethod` wants hand-splitting: 4M heartbeats, then 60M / 26 minutes, then
every closer in `_eq` form — none of them finished). The diagnosis there was right about the
symptom (`split` on a 135-line body with ten branch points outruns any closer list) and wrong
about the remedy: hand-transcribing the ~7 conditions does not work either, and the reason is
worth the file.

## Why hand-splitting the conditions does not work — the nineteenth stall point

`Interp.enterUserMethod` threads the machine through **nine** `let`s. Any tactic that touches the
body zeta-expands them, and the machine terms then appear *once per use of the name*:

* the activation frame push produces a **flat record literal whose nine fields are each a
  projection of the pre-push machine**, so the pre-push machine — itself a nest of
  `allocArr`/`allocHsh`/`destructureBind` — is written out nine times;
* which is why the post-`dsimp` hypothesis is ~1200 printed lines for a 135-line function.

Two mechanical consequences, both measured here:

1. **A goal-side peel cannot recover the intermediate machine.** `{ mid with frames :=
   mid.frames.push fr, … }` puts `?mid` under a projection in every field, which is the same
   unification failure `MCap.push_trans_eq` hit (clink 62).
2. **`generalize … at h` cannot name it either.** Pure subterms generalize fine
   (`List.take … args` did), but every machine-producing subterm here is guarded by a `match`,
   and a hand-written `match` elaborates to a *fresh matcher constant* — defeq to the model's,
   not syntactically equal — so `generalize` abstracts **nothing** and reports no error. That
   silent no-op is the trap; the symptom is a hypothesis that looks unchanged.

## The remedy: mirror the function with its stages **named**, and gate the mirror with `rfl`

`enterUM` below is `Interp.enterUserMethod` transcribed with its five machine-touching stages
pulled out as `Act.restBind`/`kwrestBind`/`destrBind`/`actPush`/`actLocals`. `enterUM_eq` proves
the transcription **is** the model's function — by `rfl`, i.e. checked by the kernel, so a
transcription error is a build failure and not a fidelity gap. The mirror is not a second
semantics; it is the same term with five subterms given names.

With the stages named, every machine in the walk is an *argument of a named callee*
(`Act.actPush mid fr`), so the goal determines it first-order and the peels compose exactly as
`Step.withCtl'` already did. **The walk is then 18 seconds**, against three previous
non-terminating attempts, and the closer list is six lines.

The transferable rule, and it is the same shape as clink 62's: *put the arm's shape where
unification can see it*. There it meant moving a shape into a `rfl` hypothesis; here it means
giving a `let`-chain's stages names — and where the model inlines them, mirroring the function
and paying one `rfl` for the fidelity.

**Reusable beyond this function**: `finishSend`, `startArgs`, `tryIterator` and `evalExpr` are
let-chains of the same kind, and the same gate applies to each.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Ratchet.Denote

open RubyCore

namespace Act

/-- The rest-parameter binding: one array allocation, or nothing. -/
def restBind (m : Machine) (r? : Option String) (restVals : List Value) :
    List (String × Value) × Machine :=
  match r? with
  | some r => let (rv, m) := Builtins.allocArr m restVals.toArray; ([(r, rv)], m)
  | none => ([], m)

/-- The `**kwrest` binding: one hash allocation, or nothing. -/
def kwrestBind (m : Machine) (kr? : Option (Option String))
    (leftover : List (Value × Value)) : List (String × Value) × Machine :=
  match kr? with
  | some (some kr) => let (hv, m) := Builtins.allocHsh m leftover.toArray; ([(kr, hv)], m)
  | _ => ([], m)

/-- The destructuring-parameter fold. -/
def destrBind (m : Machine) (destrs : List (String × List RubyCore.Param))
    (locals : List (String × Value)) : List (String × Value) × Machine :=
  destrs.foldl (fun (acc, m) (sn, subs) =>
    let dv := (locals.find? (·.1 == sn)).map (·.2) |>.getD .nil
    let (bs, m) := Interp.destructureBind m subs dv (Interp.destrDepth subs + 1)
    (acc ++ bs, m)) ([], m)

/-- The activation push: the method frame, then the `frameK` boundary. -/
def actPush (m : Machine) (fr : RubyCore.Frame) : Machine :=
  let fid := m.frames.size
  let m := { m with frames := m.frames.push fr, stack := fid :: m.stack }
  { m with kont := .frameK fid :: m.kont }

/-- The phase-B `setLocal` walk. -/
def actLocals (m : Machine) (localsB : List (String × Value)) : Machine :=
  localsB.foldl (fun m (nv : String × Value) => m.setLocal nv.1 nv.2) m

end Act

/-- **`Interp.enterUserMethod`, transcribed with its five machine-touching stages named.** -/
def enterUM (m : Machine) (recv : Value) (mname : String) (md : MethodDef)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value) := []) : StepResult :=
  let fp? := Interp.classifyFull md.params
  if fp?.isNone then
    .unsupported "unmodeled param kind (forwarding/destructuring)"
  else
  let fp := fp?.getD ⟨[], [], none, [], [], none, none, []⟩
  let hasKw := !fp.keys.isEmpty || fp.kwrest?.isSome
  let (args, m) := if hasKw then (args, m) else Interp.appendKwHash m args kw
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
    let reqKeys := fp.keys.filterMap (fun (kn, d?) => if d?.isNone then some kn else none)
    let kwSuffix := if reqKeys.isEmpty then ""
      else s!"; required keyword{if reqKeys.length == 1 then "" else "s"}: " ++
           String.intercalate ", " reqKeys
    .next (Interp.raiseErr m Boot.argumentErrorId
      s!"wrong number of arguments (given {n}, expected {expected}{kwSuffix})")
  else
    let missing := fp.keys.filterMap (fun (kn, d?) =>
      if (Interp.kwLookup kw kn).isNone && d?.isNone then some kn else none)
    let keyNames := fp.keys.map (·.1)
    let leftover := kw.filter (fun p => match p.1 with | .sym s => !keyNames.contains s | _ => true)
    if hasKw && !missing.isEmpty then
      .next (Interp.raiseErr m Boot.argumentErrorId
        s!"missing keyword{if missing.length == 1 then "" else "s"}: {Interp.kwNameList missing}")
    else if hasKw && fp.kwrest?.isNone && !leftover.isEmpty then
      let names := leftover.filterMap (fun p => match p.1 with | .sym s => some s | _ => none)
      .next (Interp.raiseErr m Boot.argumentErrorId
        s!"unknown keyword{if names.length == 1 then "" else "s"}: {Interp.kwNameList names}")
    else
    let preVals := args.take np
    let postVals := args.drop (n - npost)
    let middle := (args.drop np).take (n - npost - np)
    let filled := min nopt middle.length
    let optFilled := ((fp.opt.take filled).map (·.1)).zip (middle.take filled)
    let optOmitted := fp.opt.drop filled
    let restVals := middle.drop filled
    let kwProvided := fp.keys.filterMap (fun (kn, _) => (Interp.kwLookup kw kn).map (fun v => (kn, v)))
    let kwOmitted := fp.keys.filterMap (fun (kn, d?) =>
      if (Interp.kwLookup kw kn).isNone then d?.map (fun d => (kn, d)) else none)
    let localsA := fp.pre.zip preVals ++ optFilled ++ kwProvided
    let (restBinding, m) := Act.restBind m fp.rest? restVals
    let (kwrestBinding, m) := Act.kwrestBind m fp.kwrest? leftover
    let localsB := restBinding ++ fp.post.zip postVals ++
      (match fp.block? with | some b => [(b, blk.getD .nil)] | none => []) ++ kwrestBinding
    let (destrB, m) := Act.destrBind m fp.destrs (localsA ++ localsB)
    let notSynth : (String × Value) → Bool := fun b => !(fp.destrs.any (·.1 == b.1))
    let localsA := localsA.filter notSynth ++ destrB
    let localsB := localsB.filter notSynth
    let predeclared := localsB.map (fun b => (b.1, Value.nil)) ++
      (optOmitted ++ kwOmitted).map (fun d => (d.1, Value.nil)) ++
      md.declared.map (fun n => (n, Value.nil))
    let frameBlk := match md.capturedFrame with
      | some cf => (m.frames.getD cf default).blk
      | none => blk
    let frame : RubyCore.Frame :=
      { self := recv, locals := localsA ++ predeclared, defmod := md.owner,
        kind := .method, blk := frameBlk, callBlk := blk,
        meth := md.superName.getD mname,
        runParams := md.params, runFromDM := md.capturedFrame.isSome,
        cref := md.cref, captured := md.capturedFrame }
    let m := Act.actPush m frame
    match optOmitted ++ kwOmitted with
    | [] => .next (Interp.withCtl (Act.actLocals m localsB) (.eval md.body))
    | (n0, d0) :: more =>
      .next (Interp.withKont m (.eval d0) (.optDefK n0 more localsB md.body))

set_option maxHeartbeats 4000000 in
/-- **The gate**: the transcription is the model's function, checked by the kernel. -/
theorem enterUM_eq (m : Machine) (recv : Value) (mname : String) (md : MethodDef)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value)) :
    Interp.enterUserMethod m recv mname md args blk kw = enterUM m recv mname md args blk kw :=
  rfl

#print axioms enterUM_eq

/-! ## The five stages, one `Step`/`PreAct` lemma each -/

theorem PreAct.restBind {b : FrameId} {m mid : Machine} (p : PreAct b m mid)
    (r? : Option String) (rv : List Value) : PreAct b m (Act.restBind mid r? rv).2 := by
  unfold Act.restBind
  split
  · exact p.allocArr _
  · exact p

theorem PreAct.kwrestBind {b : FrameId} {m mid : Machine} (p : PreAct b m mid)
    (kr? : Option (Option String)) (lo : List (Value × Value)) :
    PreAct b m (Act.kwrestBind mid kr? lo).2 := by
  unfold Act.kwrestBind
  split
  · exact p.allocHsh _
  · exact p

theorem PreAct.destrBind {b : FrameId} {m mid : Machine} (p : PreAct b m mid)
    (destrs : List (String × List RubyCore.Param)) (locals : List (String × Value)) :
    PreAct b m (Act.destrBind mid destrs locals).2 := by
  unfold Act.destrBind
  refine PreAct.foldPair' _ ?_ _ _ p
  intro q a hq
  exact PreAct.destructureBind _ q.2 _ _ hq

theorem Step.actLocals {b : FrameId} {m mid : Machine} (s : Step b m mid)
    (localsB : List (String × Value)) : Step b m (Act.actLocals mid localsB) := by
  unfold Act.actLocals
  exact Step.foldM' _ (fun m2 nv h2 => Step.setLocal h2 nv.1 nv.2) _ s

theorem Step.actPush {b : FrameId} {m mid : Machine} (p : PreAct b m mid)
    {k : ObjId} {n : String} {md : MethodDef} (hmd : methodIn m.heap k n = some md)
    (fr : RubyCore.Frame) (hfr : fr.captured = md.capturedFrame) :
    Step b m (Act.actPush mid fr) := by
  unfold Act.actPush
  exact Step.frameOnly' (Step.push_meth' p.1 fr (p.2.1 k n md hmd) hfr) rfl rfl rfl

/-! ## The walk -/

set_option maxHeartbeats 1000000 in
theorem Step.enterUM {b : FrameId} {m m' : Machine} (h : StepInv b m)
    (recv : Value) (mname : String) {k : ObjId} {n : String} {md : MethodDef}
    (hmd : methodIn m.heap k n = some md)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value))
    (hstep : enterUM m recv mname md args blk kw = .next m') : Step b m m' := by
  rw [_root_.Ratchet.Denote.enterUM] at hstep
  dsimp only at hstep
  cases hfp : Interp.classifyFull md.params with
  | none => rw [hfp] at hstep; simp at hstep
  | some fp =>
    rw [hfp] at hstep
    simp only [Option.isNone_some, Bool.false_eq_true, if_false, Option.getD_some] at hstep
    by_cases hkw : (!fp.keys.isEmpty || fp.kwrest?.isSome) = true
    · simp only [if_pos hkw] at hstep
      have hpre : PreAct b m m := PreAct.refl h
      repeat (any_goals (first
        | (cases hstep; exact Step.raiseErr' hpre.1 _ _)
        | (cases hstep
           refine Step.withCtl' ?_ _
           refine Step.actLocals ?_ _
           refine Step.actPush ?_ hmd _ rfl
           refine PreAct.destrBind ?_ _ _
           refine PreAct.kwrestBind ?_ _ _
           refine PreAct.restBind ?_ _ _
           exact hpre)
        | (cases hstep
           refine Step.withKont' ?_ _ _
           refine Step.actPush ?_ hmd _ rfl
           refine PreAct.destrBind ?_ _ _
           refine PreAct.kwrestBind ?_ _ _
           refine PreAct.restBind ?_ _ _
           exact hpre)
        | split at hstep))
    · simp only [if_neg hkw] at hstep
      have hpre : PreAct b m (Interp.appendKwHash m args kw).2 :=
        (PreAct.refl h).appendKwHash _ _
      repeat (any_goals (first
        | (cases hstep; exact Step.raiseErr' hpre.1 _ _)
        | (cases hstep
           refine Step.withCtl' ?_ _
           refine Step.actLocals ?_ _
           refine Step.actPush ?_ hmd _ rfl
           refine PreAct.destrBind ?_ _ _
           refine PreAct.kwrestBind ?_ _ _
           refine PreAct.restBind ?_ _ _
           exact hpre)
        | (cases hstep
           refine Step.withKont' ?_ _ _
           refine Step.actPush ?_ hmd _ rfl
           refine PreAct.destrBind ?_ _ _
           refine PreAct.kwrestBind ?_ _ _
           refine PreAct.restBind ?_ _ _
           exact hpre)
        | split at hstep))

/-- **`Interp.enterUserMethod` itself**, through the gate. -/
theorem Step.enterUserMethod {b : FrameId} {m m' : Machine} (h : StepInv b m)
    (recv : Value) (mname : String) {k : ObjId} {n : String} {md : MethodDef}
    (hmd : methodIn m.heap k n = some md)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value))
    (hstep : Interp.enterUserMethod m recv mname md args blk kw = .next m') : Step b m m' :=
  Step.enterUM h recv mname hmd args blk kw (by rw [← enterUM_eq]; exact hstep)

#print axioms PreAct.destrBind
#print axioms Step.actPush
#print axioms Step.actLocals
#print axioms Step.enterUM
#print axioms Step.enterUserMethod

end Ratchet.Denote
