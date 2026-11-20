import Books.TypeSoundness.Checker.Audit.Derive

/-!
# Writing the traced judgments as source

`lake exe gen-audit-judgments > Books/TypeSoundness/Checker/Audit/Judgments.lean`
(`make` runs it before building the checker; the file is not committed)

`Derive.lean` computes, from each authoring judgment (`DJudge` and its
companions), a traced copy whose index records the rules a derivation used.
Computing it needs Lean's metaprogramming library, and a module that imports
that library makes every executable that imports the module link all of Lean.
`validate-one`, the checker as a program, would then be a hundred megabytes
natively and could not be built for the browser at all.

So the traced judgments are written out here as ordinary declarations:
`Judgments.lean` holds the mutual inductives and their erasure theorems
(`toRaw`), with proofs that use only built-in tactics. The checker imports that
file and not this one. `JudgmentsCheck.lean` re-derives every declaration with
the metaprogram and fails the build if the written-out file differs.
-/
open Lean Meta Elab Command
namespace Checker.Audit

/-- The two mutual groups, in dependency order: the initializer judgments, then
    the rest, whose constructors may have initializer premises. -/
def groups : List (List Name) :=
  let init := [``Checker.InitJudge, ``Checker.InitJudgeSeq, ``Checker.InitJudgeAll]
  [init, families.filter fun n => !init.contains n]

/-- `e` as source that elaborates back to `e`: every argument explicit, every
    name in full. -/
def source (e : Lean.Expr) : MetaM String := do
  withOptions (fun o => (((o.setBool `pp.explicit true).setBool `pp.fullNames true).setBool
      `pp.proofs true).setBool `pp.deepTerms false) do
    return (← ppExpr e).pretty 100000

/-- The traced families do not exist yet where this runs, so the printer cannot
    know that their first argument (the trace) is implicit, and writes them
    without the `@` that passing it explicitly needs. -/
def explicitTraced (text : String) : String := Id.run do
  let mut out := text
  for n in families do
    let name := toString (auditName n)
    for stop in [" ", ")"] do
      out := (out.splitOn (name ++ stop)).foldl (init := "") fun acc piece =>
        if acc.isEmpty then piece else acc ++ "@" ++ name ++ stop ++ piece
      -- undo a doubled `@` where the printer already wrote one
      out := out.replace ("@@" ++ name) ("@" ++ name)
  return out

/-- The `mutual … end` block declaring one group's traced inductives. -/
def inductiveBlock (group : List Name) : MetaM String := do
  let mut out := "mutual\n\n"
  for n in group do
    let info ← getConstInfoInduct n
    let ty := mkForall `used .implicit traceTy info.type
    out := out ++ s!"inductive {(auditName n).replacePrefix `Checker.Audit .anonymous} : {← source ty} where\n"
    for c in info.ctors do
      let ci ← getConstInfoCtor c
      let traced ← traceConstructor ci.type (ruleName c)
      out := out ++ s!"  | {c.componentsRev.head!} : {explicitTraced (← source traced)}\n"
    out := out ++ "\n"
  return out ++ "end\n\n"

/-- One case of an erasure proof: the raw constructor applied to the traced
    constructor's fields, with each judgment premise erased: by the induction
    hypothesis when it is in the same mutual group, by that family's `toRaw`
    otherwise. -/
def eraseCase (group : List Name) (raw : Name) : MetaM String := do
  let rawInfo ← getConstInfoCtor raw
  let domains : Array Lean.Expr ←
    forallTelescope rawInfo.type fun xs _ => xs.mapM fun x => inferType x
  let count := (← traceConstructor rawInfo.type (ruleName raw)).getForallArity
  let recursive := domains.filter fun d => d.getUsedConstants.any group.contains
  let fields := (List.range count).map (s!"x{·}")
  let ihs := (List.range recursive.size).map (s!"ih{·}")
  let mut args : Array String := #[]
  let mut cursor := 0
  let mut ih := 0
  for dom in domains do
    if dom.getUsedConstants.any families.contains then
      let premise := fields[cursor + 1]!
      cursor := cursor + 2
      if dom.getUsedConstants.any group.contains then
        args := args.push ihs[ih]!
        ih := ih + 1
      else
        let family := auditName dom.getAppFn.constName!
        args := args.push s!"({family}.toRaw {premise})"
    else
      args := args.push fields[cursor]!
      cursor := cursor + 1
  let binders := fields ++ ihs
  let intro := if binders.isEmpty then "" else s!"intro {" ".intercalate binders}\n    "
  return s!"  · {intro}exact @{raw} {" ".intercalate args.toList}\n"

/-- `n.toRaw`, the traced judgment erased to the authoring one. Computed from
    the authoring judgment alone, so it needs no traced declaration to exist. -/
def eraseTheorem (group : List Name) (raw : Name) : MetaM String := do
  let n := auditName raw
  let ii ← getConstInfoInduct raw
  let tracedTy := mkForall `used .implicit traceTy ii.type
  let typeText ← forallTelescope tracedTy fun xs _ => do
    let dom := mkAppN (mkConst n) xs
    withLocalDeclD `h dom fun h => do
      let ty ← mkForallFVars (xs.push h) (mkAppN (mkConst raw) (xs.extract 1 xs.size))
      return explicitTraced (← source (implicitBinders xs.size ty))
  let indices := (List.range ii.numIndices).map (s!"a{·}")
  let mut minors := 0
  for m in group do
    minors := minors + (← getConstInfoInduct m).ctors.length
  let mut text := s!"theorem _root_.{n}.toRaw : {typeText} := by\n"
  text := text ++ s!"  intro used {" ".intercalate indices} h\n"
  text := text ++ s!"  refine {n}.rec"
  for (m, i) in group.zipIdx do
    let as := (List.range (← getConstInfoInduct m).numIndices).map (s!"a{·}")
    text := text ++ s!" (motive_{i+1} := fun \{used} {" ".intercalate as} _ => {m} {" ".intercalate as})"
  text := text ++ " " ++ " ".intercalate (List.replicate minors "?_") ++ " h\n"
  for m in group do
    for c in (← getConstInfoInduct m).ctors do
      text := text ++ (← eraseCase group c)
  return text ++ "\n"

def header : String :=
"/-
GENERATED by `lake exe gen-audit-judgments` (Checker/Audit/Generate.lean) from the
authoring judgments in Checker/Judgment/. A build output, not committed: `make`
writes it before anything that imports it. Do not edit.

The traced judgments: each authoring judgment with an index recording the rules a
derivation used, and its erasure back to the authoring judgment (`toRaw`).
`JudgmentsCheck.lean` fails the build if this file differs from what the
metaprogram in `Derive.lean` computes.
-/
import Books.TypeSoundness.Checker.Judgment.DJudge

set_option autoImplicit false
set_option maxRecDepth 100000
-- The statements name their binders, as printed; the proofs reintroduce them.
set_option linter.unusedVariables false
namespace Checker.Audit

"

def generate : MetaM String := do
  let mut out := header
  for group in groups do
    out := out ++ (← inductiveBlock group)
  for group in groups do
    for raw in group do
      out := out ++ (← eraseTheorem group raw)
  return out ++ "end Checker.Audit\n"

end Checker.Audit

open Lean in
def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Books.TypeSoundness.Checker.Audit.Generate }] {}
  let ctx : Core.Context := { fileName := "<gen-audit-judgments>", fileMap := default }
  let (text, _) ← (Checker.Audit.generate.run' {} {}).toIO ctx { env }
  IO.print text
  return 0
