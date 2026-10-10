import Books.TypeSoundness.Checker.Check.Check
import Books.TypeSoundness.Registry.Form

/-! The complete authoring family, independent of semantic proof providers. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open Checker Lean

/-- All seventeen syntactic families, including local-flow and fresh-initializer premises. -/
structure DFam where
  judge : Env → Checker.Expr → Ty → Env → (κ : optParam Ctx ctx0) →
    (I : optParam Ty .ivar0) → optParam Ctx κ → optParam Ty I → Prop
  all : Env → List Checker.Expr → List Ty → Env → (κ : optParam Ctx ctx0) →
    (I : optParam Ty .ivar0) → optParam Ctx κ → optParam Ty I → Prop
  seq : Env → List Checker.Expr → Ty → Env → (κ : optParam Ctx ctx0) →
    (I : optParam Ty .ivar0) → optParam Ctx κ → optParam Ty I → Prop
  pairs : Env → List (Checker.Expr × Checker.Expr) → List Ty → List Ty → Env →
    (κ : optParam Ctx ctx0) → (I : optParam Ty .ivar0) → optParam Ctx κ → optParam Ty I → Prop
  recBody : Ctx → Ty → RecScope → Env → Checker.Expr → Ty → Env → Prop
  recArgs : Ctx → Ty → RecScope → Env → List Checker.Expr → List Ty → Env → Prop
  init : Ctx → Env → Ty → Checker.Expr → Ty → Ctx → Env → Ty → Prop
  initSeq : Ctx → Env → Ty → List Checker.Expr → Ty → Ctx → Env → Ty → Prop
  initAll : Ctx → Env → Ty → List Checker.Expr → List Ty → Ctx → Env → Ty → Prop
  flow : Ctx → Env → Ty → LocalFacts → Checker.Expr → Ty → Bool → Ctx → Env → Ty → LocalFacts → Prop
  flowSeq : Ctx → Env → Ty → LocalFacts → List Checker.Expr → Ty → Bool → Ctx → Env → Ty → LocalFacts → Prop
  flowAll : Ctx → Env → Ty → LocalFacts → List Checker.Expr → List Ty → Ctx → Env → Ty → LocalFacts → Prop
  method : Ctx → Ty → Frame → List Ty → Ty → Env → Checker.Expr → Ty → Env → Prop
  methodAll : Ctx → Ty → Frame → List Ty → Ty → Env → List Checker.Expr → List Ty → Env → Prop
  methodSeq : Ctx → Ty → Frame → List Ty → Ty → Env → List Checker.Expr → Ty → Env → Prop
  methodFlow : Ctx → Ty → Frame → List Ty → Ty → Env → CallbackFacts → Checker.Expr → Ty → Bool → Env → CallbackFacts → Prop
  methodFlowSeq : Ctx → Ty → Frame → List Ty → Ty → Env → CallbackFacts → List Checker.Expr → Ty → Bool → Env → CallbackFacts → Prop

/-- The syntactic reading: `Checker/Judgment/DJudge.lean`'s own relations. -/
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
def dFamField : List (Name × Name) := [(``Checker.DJudge, ``DFam.judge),
  (``Checker.DJudgeAll, ``DFam.all), (``Checker.DJudgeSeq, ``DFam.seq),
  (``Checker.DJudgePairs, ``DFam.pairs), (``Checker.DJudgeRec, ``DFam.recBody),
  (``Checker.DJudgeRecAll, ``DFam.recArgs), (``Checker.InitJudge, ``DFam.init),
  (``Checker.InitJudgeSeq, ``DFam.initSeq), (``Checker.InitJudgeAll, ``DFam.initAll),
  (``Checker.DFlow, ``DFam.flow), (``Checker.DFlowSeq, ``DFam.flowSeq), (``Checker.DFlowAll, ``DFam.flowAll),
  (``Checker.DMethod, ``DFam.method), (``Checker.DMethodAll, ``DFam.methodAll),
  (``Checker.DMethodSeq, ``DFam.methodSeq),
  (``Checker.DMethodFlow, ``DFam.methodFlow), (``Checker.DMethodFlowSeq, ``DFam.methodFlowSeq)]

/-- The judgment inductives. Frozen so a new family cannot bypass registration. -/
def dJudgmentInductives : List Name :=
  [``Checker.DJudge, ``Checker.DJudgeAll, ``Checker.DJudgeSeq, ``Checker.DJudgePairs,
    ``Checker.DJudgeRec, ``Checker.DJudgeRecAll, ``Checker.InitJudge, ``Checker.InitJudgeSeq,
    ``Checker.InitJudgeAll, ``Checker.DFlow, ``Checker.DFlowSeq, ``Checker.DFlowAll,
    ``Checker.DMethod, ``Checker.DMethodAll, ``Checker.DMethodSeq, ``Checker.DMethodFlow, ``Checker.DMethodFlowSeq]

/-- Judgment inductives `DFam` does **not** carry a field for. A rule whose premises reach
one of these cannot be registered: see `registerDClink`. -/
def dUncarriedJudgments : List Name :=
  dJudgmentInductives.filter fun n => !dFamField.any (fun (ind, _) => ind == n)

end Checker.Soundness.Typed
