import Denote.Clink.Family

/-! Build the semantic family from the canonical contract definitions supplied
by the active proof imports. Unavailable projections are False. Registration
refuses a constructor mentioning an unavailable projection, even in a premise;
no admitted rule can exploit an absent interpretation. -/
set_option autoImplicit false
open Lean Meta Elab Command
namespace Ratchet.Denote.Typed

/-- Fixed contract names: proof availability never chooses a weaker target. -/
def dSemanticFields : List (Name × Name) :=
  [(``DFam.judge, `Ratchet.Denote.Typed.SemSafeCtxA),
   (``DFam.all, `Ratchet.Denote.Typed.SemAllCtxA),
   (``DFam.seq, `Ratchet.Denote.Typed.SemSeqCtxA),
   (``DFam.pairs, `Ratchet.Denote.Typed.SemPairsCtxA),
   (``DFam.recBody, `Ratchet.Denote.Typed.SemRec),
   (``DFam.recArgs, `Ratchet.Denote.Typed.SemRecAll),
   (``DFam.init, `Ratchet.Denote.Typed.SemInitA),
   (``DFam.initSeq, `Ratchet.Denote.Typed.SemInitSeqA),
   (``DFam.initAll, `Ratchet.Denote.Typed.SemInitAllA),
   (``DFam.flow, `Ratchet.Denote.Typed.SemFlow),
   (``DFam.flowSeq, `Ratchet.Denote.Typed.SemFlowSeq),
   (``DFam.flowAll, `Ratchet.Denote.Typed.SemFlowAll),
   (``DFam.method, `Ratchet.Denote.Typed.SemMethodBody),
   (``DFam.methodAll, `Ratchet.Denote.Typed.SemMethodBodyAll),
   (``DFam.methodSeq, `Ratchet.Denote.Typed.SemMethodBodySeq),
   (``DFam.methodFlow, `Ratchet.Denote.Typed.SemMethodFlowBody),
   (``DFam.methodFlowSeq, `Ratchet.Denote.Typed.SemMethodFlowBodySeq)]

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
  buildDClinkTarget `Ratchet.Denote.Typed.dsemFam
    `Ratchet.Denote.Typed.dAvailableFamFields dSemanticFields
end Ratchet.Denote.Typed
