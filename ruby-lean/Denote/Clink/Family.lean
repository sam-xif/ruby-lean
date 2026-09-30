import Ratchet.Check.Check
import Denote.Clink.Form

/-! The complete authoring family, independent of semantic proof providers. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open Ratchet Lean

/-- All seventeen syntactic families, including local-flow and fresh-initializer premises. -/
structure DFam where
  judge : Env → Ratchet.Expr → Ty → Env → (κ : optParam Ctx ctx0) →
    (I : optParam Ty .ivar0) → optParam Ctx κ → optParam Ty I → Prop
  all : Env → List Ratchet.Expr → List Ty → Env → (κ : optParam Ctx ctx0) →
    (I : optParam Ty .ivar0) → optParam Ctx κ → optParam Ty I → Prop
  seq : Env → List Ratchet.Expr → Ty → Env → (κ : optParam Ctx ctx0) →
    (I : optParam Ty .ivar0) → optParam Ctx κ → optParam Ty I → Prop
  pairs : Env → List (Ratchet.Expr × Ratchet.Expr) → List Ty → List Ty → Env →
    (κ : optParam Ctx ctx0) → (I : optParam Ty .ivar0) → optParam Ctx κ → optParam Ty I → Prop
  recBody : Ctx → Ty → RecScope → Env → Ratchet.Expr → Ty → Env → Prop
  recArgs : Ctx → Ty → RecScope → Env → List Ratchet.Expr → List Ty → Env → Prop
  init : Ctx → Env → Ty → Ratchet.Expr → Ty → Ctx → Env → Ty → Prop
  initSeq : Ctx → Env → Ty → List Ratchet.Expr → Ty → Ctx → Env → Ty → Prop
  initAll : Ctx → Env → Ty → List Ratchet.Expr → List Ty → Ctx → Env → Ty → Prop
  flow : Ctx → Env → Ty → LocalFacts → Ratchet.Expr → Ty → Bool → Ctx → Env → Ty → LocalFacts → Prop
  flowSeq : Ctx → Env → Ty → LocalFacts → List Ratchet.Expr → Ty → Bool → Ctx → Env → Ty → LocalFacts → Prop
  flowAll : Ctx → Env → Ty → LocalFacts → List Ratchet.Expr → List Ty → Ctx → Env → Ty → LocalFacts → Prop
  method : Ctx → Ty → Frame → List Ty → Ty → Env → Ratchet.Expr → Ty → Env → Prop
  methodAll : Ctx → Ty → Frame → List Ty → Ty → Env → List Ratchet.Expr → List Ty → Env → Prop
  methodSeq : Ctx → Ty → Frame → List Ty → Ty → Env → List Ratchet.Expr → Ty → Env → Prop
  methodFlow : Ctx → Ty → Frame → List Ty → Ty → Env → CallbackFacts → Ratchet.Expr → Ty → Bool → Env → CallbackFacts → Prop
  methodFlowSeq : Ctx → Ty → Frame → List Ty → Ty → Env → CallbackFacts → List Ratchet.Expr → Ty → Bool → Env → CallbackFacts → Prop

/-- The syntactic reading: `Ratchet/Judgment/DJudge.lean`'s own relations. -/
def dsynFam : DFam where
  judge := @DJudge
  all := @DJudgeAll
  seq := @DJudgeSeq
  pairs := @DJudgePairs
  recBody := DJudgeRec
  recArgs := DJudgeRecAll
  init := InitJudge
  initSeq := InitJudgeSeq
  initAll := InitJudgeAll
  flow := DFlow
  flowSeq := DFlowSeq
  flowAll := DFlowAll
  method := DMethod
  methodAll := DMethodAll
  methodSeq := DMethodSeq
  methodFlow := DMethodFlow
  methodFlowSeq := DMethodFlowSeq

/-- All judgment heads must be abstracted, including those occurring only in premises. -/
def dFamField : List (Name × Name) := [(``Ratchet.DJudge, ``DFam.judge),
  (``Ratchet.DJudgeAll, ``DFam.all), (``Ratchet.DJudgeSeq, ``DFam.seq),
  (``Ratchet.DJudgePairs, ``DFam.pairs), (``Ratchet.DJudgeRec, ``DFam.recBody),
  (``Ratchet.DJudgeRecAll, ``DFam.recArgs), (``Ratchet.InitJudge, ``DFam.init),
  (``Ratchet.InitJudgeSeq, ``DFam.initSeq), (``Ratchet.InitJudgeAll, ``DFam.initAll),
  (``Ratchet.DFlow, ``DFam.flow), (``Ratchet.DFlowSeq, ``DFam.flowSeq), (``Ratchet.DFlowAll, ``DFam.flowAll),
  (``Ratchet.DMethod, ``DFam.method), (``Ratchet.DMethodAll, ``DFam.methodAll),
  (``Ratchet.DMethodSeq, ``DFam.methodSeq),
  (``Ratchet.DMethodFlow, ``DFam.methodFlow), (``Ratchet.DMethodFlowSeq, ``DFam.methodFlowSeq)]

/-- The judgment inductives. Frozen so a new family cannot bypass registration. -/
def dJudgmentInductives : List Name :=
  [``Ratchet.DJudge, ``Ratchet.DJudgeAll, ``Ratchet.DJudgeSeq, ``Ratchet.DJudgePairs,
    ``Ratchet.DJudgeRec, ``Ratchet.DJudgeRecAll, ``Ratchet.InitJudge, ``Ratchet.InitJudgeSeq,
    ``Ratchet.InitJudgeAll, ``Ratchet.DFlow, ``Ratchet.DFlowSeq, ``Ratchet.DFlowAll,
    ``Ratchet.DMethod, ``Ratchet.DMethodAll, ``Ratchet.DMethodSeq, ``Ratchet.DMethodFlow, ``Ratchet.DMethodFlowSeq]

/-- Judgment inductives `DFam` does **not** carry a field for. A rule whose premises reach
one of these cannot be registered: see `registerDClink`. -/
def dUncarriedJudgments : List Name :=
  dJudgmentInductives.filter fun n => !dFamField.any (fun (ind, _) => ind == n)

end Ratchet.Denote.Typed
