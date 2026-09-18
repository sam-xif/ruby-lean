import Denote.Rules.Class.ClassRules
import Denote.Rules.Expr.Sequence
import Denote.Sem.Core.Boot

/-! Pure guards agree with the physical dispatch checks; multiple fresh classes exercise
the table-frame route. None of these guard Bools substitutes for a method-body proof. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.ClassRuleControls
open RubyCore Ratchet Ratchet.Denote

#guard ["Object", "Class", "String", "Point", "FlagBox", "IOError", "#<Class:Class>"].all fun cn =>
  nativeQueryNames.all fun mn => nativeQueryFreeB cn mn == !crubyClassDefines cn mn
#guard !nativeQueryFreeB "Point" "unknown_query"
#guard ["Object", "Class", "String", "Point", "FlagBox", "IOError"].all fun cn =>
  classNativeFrameB ctx0 cn == FreshClass.nativeFrameB ctx0 cn
#guard (interceptedSendNames ++ singletonSendNames ++ ["getX", "answer", "fresh_method"]).all fun mn =>
  directCallNameB mn == directSendNameB mn
#guard !directCallNameB "call" && !directCallNameB "new" && !directCallNameB "sqrt"
#guard directCallNameB "answer"
#guard !explicitReceiverB .self'
#guard explicitReceiverB (.const "Box")

private def firstBody : Ctx := classHeaderCtx (classBodyCtx ctx0 "FirstBox") "FirstBox"
private def between : Ctx := returnScopeCtx ctx0 firstBody
private def secondBody : Ctx := classHeaderCtx (classBodyCtx between "SecondBox") "SecondBox"
private def finished : Ctx := returnScopeCtx between secondBody
private def program : Ratchet.Expr := .seq [
  .class' "FirstBox" none (.int 1), .class' "SecondBox" none (.int 2)]

#guard plainClassTablesB between
#guard plainClassTablesB finished
#guard !plainClassTablesB { ctx0 with pos := { ctx0.pos with classes := [classHeader "Outer::Inner"] } }
#guard !plainClassTablesB { ctx0 with pos := { ctx0.pos with consts := [("::X", .int)] } }
#guard !classRuleB between secondBody [] .ivar0 .int "FirstBox"
#guard !mainCallB (initializerBodyCtx between "FirstBox") [] .ivar0
#guard !reframeTypesB ctx0 (.arrow0 .int)

theorem two_classes : SemSafeCtxA ctx0 [] .ivar0 program .int finished [] .ivar0 := by
  have h₁ : SemSafeCtxA ctx0 [] .ivar0 (.class' "FirstBox" none (.int 1)) .int between [] .ivar0 :=
    SemSafeCtxA.classDecl (κb := firstBody) .intLit (by decide)
  have h₂ : SemSafeCtxA between [] .ivar0 (.class' "SecondBox" none (.int 2)) .int finished [] .ivar0 :=
    SemSafeCtxA.classDecl (κb := secondBody) .intLit (by decide)
  exact h₁.seq h₂

#guard match Interp.run 150 (evalFrom bootMachine program) with
  | .value (.int 2) n => (classNamed? n.heap "FirstBox").isSome &&
      (classNamed? n.heap "SecondBox").isSome &&
      classNamed? n.heap "FirstBox" != classNamed? n.heap "SecondBox"
  | _ => false

#print axioms two_classes
end Ratchet.Denote.Typed.ClassRuleControls
