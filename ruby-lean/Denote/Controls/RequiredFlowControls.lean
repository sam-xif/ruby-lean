import Denote.Rules.Closure.RequiredFlowCall
import Denote.Rules.Closure.FlowExpr
import Denote.Rules.Closure.FlowSequence

/-! Whole-source required-parameter calls: immediate receivers, argument-created captures,
and saved receivers whose old bindings are overwritten while evaluating arguments. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.RequiredFlowControls
open RubyCore Ratchet Ratchet.Denote

private def body : Ratchet.Expr := .send (some (.var .lvar "x")) "+" [.int 1] none
private def code : ClosureCode := ⟨[.req "x"], [], body, true, rfl⟩
private def literal : Ratchet.Expr := .send none "lambda" [] (some (.block code.params [] body))

private theorem body_typed (Γ : Env) : SemSafeCtxA (closureBodyCtx ctx0) (("x", .int) :: Γ)
    .ivar0 body .int (closureBodyCtx ctx0) (("x", .int) :: Γ) .ivar0 :=
  (SemSafeCtxA.var rfl rfl).prim (.cons SemSafeCtxA.intLit .nil rfl)
    .intAdd rfl (by intro h; cases h)

/-- The exact 088 source, starting without a physical-slot assumption. A hidden caller x
therefore remains nil when the Integer parameter's frame is popped. -/
theorem immediate : SemSafeCtxA ctx0 [] .ivar0 (.send (some literal) "call" [.int 2] none)
    .int ctx0 [] .ivar0 := by
  apply SemFlow.erase
  exact SemFlow.requiredCall (ps := [("x", .int)])
    (SemFlow.closureLiteral .unknown code rfl)
    (.cons (SemFlow.intLit .unknown 2) .nil rfl)
    (by intro σ h; simp only [List.map_cons, List.map_nil, List.mem_singleton] at h; cases h; rfl)
    rfl rfl rfl rfl rfl rfl rfl rfl (body_typed [])

private def fEnv : Env := [("f", .clos code .ivar0 .never)]
private def fFacts : LocalFacts := LocalFacts.unknown.write "f" true
private def afterFacts : LocalFacts := fFacts.write "f" false

private theorem store : SemFlow ctx0 [] .ivar0 .unknown (.vasgn .lvar "f" literal)
    (.clos code .ivar0 .never) true ctx0 fEnv .ivar0 fFacts :=
  SemFlow.vasgn (SemFlow.closureLiteral .unknown code rfl) rfl rfl rfl rfl

theorem overwritten_receiver : SemSafeCtxA ctx0 [] .ivar0
    (.seq [.vasgn .lvar "f" literal,
      .send (some (.var .lvar "f")) "call" [.vasgn .lvar "f" (.int 2)] none])
    .int ctx0 [("f", .int)] .ivar0 := by
  apply SemFlow.erase
  apply SemFlow.sequence
  apply SemFlowSeq.cons store
  apply SemFlowSeq.last
  exact SemFlow.requiredCall (ps := [("x", .int)]) (names := ["f", "f"])
    (SemFlow.var (κ := ctx0) (Γ := fEnv) (I := .ivar0) (x := "f") fFacts rfl rfl)
    (.cons (SemFlow.vasgn (x := "f") (SemFlow.intLit fFacts 2) rfl rfl rfl rfl) .nil rfl)
    (by intro σ h; simp only [List.map_cons, List.map_nil, List.mem_singleton] at h; cases h; rfl)
    rfl rfl rfl rfl rfl rfl rfl rfl (body_typed [("f", .int)])

private def liveBody : Ratchet.Expr :=
  .send (some (.var .lvar "x")) "+" [.var .lvar "y"] none
private def liveCode : ClosureCode := ⟨[.req "x"], [], liveBody, true, rfl⟩
private def liveLiteral : Ratchet.Expr :=
  .send none "lambda" [] (some (.block liveCode.params [] liveBody))

theorem argument_creates_capture : SemSafeCtxA ctx0 [] .ivar0
    (.send (some liveLiteral) "call" [.vasgn .lvar "y" (.int 2)] none)
    .int ctx0 [("y", .int)] .ivar0 := by
  apply SemFlow.erase
  apply SemFlow.requiredCall (ps := [("x", .int)]) (names := ["y"])
    (Γb := [("x", .int), ("y", .int)])
    (SemFlow.closureLiteral (κ := ctx0) (Γ := []) (I := .ivar0) .unknown liveCode rfl)
    (.cons (SemFlow.vasgn (x := "y") (SemFlow.intLit .unknown 2) rfl rfl rfl rfl) .nil rfl)
    (by intro σ h; simp only [List.map_cons, List.map_nil, List.mem_singleton] at h; cases h; rfl)
    rfl rfl rfl rfl rfl rfl rfl rfl
  exact (SemSafeCtxA.var rfl rfl).prim (.cons (SemSafeCtxA.var rfl rfl) .nil rfl)
    .intAdd rfl (by intro h; cases h)

private def twoCode : ClosureCode := ⟨[.req "x", .req "y"], [], body, true, rfl⟩
private def twoLiteral : Ratchet.Expr :=
  .send none "lambda" [] (some (.block twoCode.params [] body))
private def aFacts : LocalFacts := LocalFacts.unknown.write "a" false

/-- The first argument keeps its Integer value while the second changes that local to nil. -/
theorem earlier_argument_survives : SemSafeCtxA ctx0 [] .ivar0
    (.send (some twoLiteral) "call" [.vasgn .lvar "a" (.int 2), .vasgn .lvar "a" .nil] none)
    .int ctx0 [("a", .nilT)] .ivar0 := by
  apply SemFlow.erase
  exact SemFlow.requiredCall (ps := [("x", .int), ("y", .nilT)]) (names := ["a", "a"])
    (SemFlow.closureLiteral (κ := ctx0) (Γ := []) (I := .ivar0) .unknown twoCode rfl)
    (.cons (SemFlow.vasgn (x := "a") (SemFlow.intLit .unknown 2) rfl rfl rfl rfl)
      (.cons (SemFlow.vasgn (x := "a") (SemFlow.nilLit aFacts) rfl rfl rfl rfl) .nil rfl) rfl)
    (by intro σ h; simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
          or_false] at h; rcases h with h | h <;> cases h <;> rfl)
    rfl rfl rfl rfl rfl rfl rfl rfl (body_typed [("y", .nilT), ("a", .nilT)])

#guard afterFacts.currentProcs == []
#guard afterFacts.captureNames? [("f", .int)] == some ["f", "f"]

#print axioms immediate
#print axioms overwritten_receiver
#print axioms argument_creates_capture
#print axioms earlier_argument_survives
end Ratchet.Denote.Typed.RequiredFlowControls
