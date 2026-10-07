import Books.TypeSoundness.Registry.Family

/-! Build the semantic family from the canonical contract definitions supplied
by the active proof imports. Unavailable projections are False. Registration
refuses a constructor mentioning an unavailable projection, even in a premise;
no admitted rule can exploit an absent interpretation. -/
set_option autoImplicit false
open Lean Meta Elab Command
namespace Checker.Soundness.Typed

/-- Fixed contract names: proof availability never chooses a weaker target. -/
def dSemanticFields : List (Name × Name) :=
  [(``DFam.judge, `Checker.Soundness.Typed.SemSafeCtxA),
   (``DFam.all, `Checker.Soundness.Typed.SemAllCtxA),
   (``DFam.seq, `Checker.Soundness.Typed.SemSeqCtxA),
   (``DFam.pairs, `Checker.Soundness.Typed.SemPairsCtxA),
   (``DFam.recBody, `Checker.Soundness.Typed.SemRec),
   (``DFam.recArgs, `Checker.Soundness.Typed.SemRecAll),
   (``DFam.init, `Checker.Soundness.Typed.SemInitA),
   (``DFam.initSeq, `Checker.Soundness.Typed.SemInitSeqA),
   (``DFam.initAll, `Checker.Soundness.Typed.SemInitAllA),
   (``DFam.flow, `Checker.Soundness.Typed.SemFlow),
   (``DFam.flowSeq, `Checker.Soundness.Typed.SemFlowSeq),
   (``DFam.flowAll, `Checker.Soundness.Typed.SemFlowAll),
   (``DFam.method, `Checker.Soundness.Typed.SemMethodBody),
   (``DFam.methodAll, `Checker.Soundness.Typed.SemMethodBodyAll),
   (``DFam.methodSeq, `Checker.Soundness.Typed.SemMethodBodySeq),
   (``DFam.methodFlow, `Checker.Soundness.Typed.SemMethodFlowBody),
   (``DFam.methodFlowSeq, `Checker.Soundness.Typed.SemMethodFlowBodySeq)]

#guard dSemanticFields.map Prod.fst == dFamField.map Prod.snd

def buildDClinkTarget (target manifest : Name) (providers : List (Name × Name)) : CommandElabM Unit := do
  let env ← getEnv
  let mut fields : Array Lean.Expr := #[]
  let mut available : List Name := []
  for (field, contract) in providers do
    let ty := (← getConstInfo field).type
    let present := (env.find? contract).isSome
    let value ← liftTermElabM <| forallTelescope ty fun allArgs _ => do
      let args := allArgs.extract 1 allArgs.size
      let body := if !present then mkConst ``False else
        let order := if field == ``DFam.judge || field == ``DFam.all || field == ``DFam.seq then
          #[4, 0, 5, 1, 2, 6, 3, 7]
        else if field == ``DFam.pairs then #[5, 0, 6, 1, 2, 3, 7, 4, 8]
        else (List.range args.size).toArray
        mkAppN (mkConst contract) (order.map (args[·]!))
      mkLambdaFVars args body
    fields := fields.push value
    if present then available := available ++ [field]
  unless available.contains ``DFam.judge do
    throwError "build_dclink_target: SemSafeCtxA must be imported"
  let value ← liftTermElabM <| mkAppM ``DFam.mk fields
  liftCoreM <| addAndCompile (.defnDecl
    { name := target, levelParams := [], type := mkConst ``DFam,
      value, hints := .abbrev, safety := .safe })
  liftCoreM <| addAndCompile (.defnDecl
    { name := manifest, levelParams := [], type := mkConst ``String,
      value := mkStrLit (String.intercalate " " (available.map toString)),
      hints := .opaque, safety := .safe })

elab "build_dclink_target" : command =>
  buildDClinkTarget `Checker.Soundness.Typed.dsemFam
    `Checker.Soundness.Typed.dAvailableFamFields dSemanticFields
end Checker.Soundness.Typed
