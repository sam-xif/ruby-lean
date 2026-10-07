import Books.TypeSoundness.Rules.Closure.Literal
import Books.TypeSoundness.Denotation.DenB

/-! Exact callable metadata survives binding; capture types remain live and invalidate
on incompatible writes. These controls do not admit a callable judgment. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.ClosureValueControls
open RubyCore Checker Checker.Soundness

/-- The ordinary assignment rule now preserves the exact code-bearing result. -/
theorem stored_literal (code : ClosureCode) :
    SemSafeCtxA ctx0 [] .ivar0
      (.vasgn .lvar "f" (.send none (if code.lam then "lambda" else "proc") []
        (some (.block code.params code.locals code.body))))
      (.clos code .ivar0 .never) ctx0 [("f", .clos code .ivar0 .never)] .ivar0 :=
  SemSafeCtxA.vasgn (SemSafeCtxA.closureLiteral code (by cases h : code.lam <;> rfl))
    rfl rfl rfl

private def one : ClosureCode := ⟨[], [], .int 1, true, rfl⟩
private def same : ClosureCode := ⟨[], [], .int 1, true, by decide⟩
#guard decide (one = same)
#guard !decide (one = { one with lam := false })
#guard !decide (one = { one with locals := ["x"] })
#guard !(closureCode? [.opt "x" (.int 1)] [] (.int 1) true).isSome

private def recognizes (ps : List RubyCore.Param) (ls : List String)
    (body : RubyCore.Expr) (lam : Bool) : Bool :=
  closB (.clos one .ivar0 .never) (reifiedMachine bootMachine ps ls body lam)
    (.ref bootMachine.heap.objs.size)
#guard recognizes [] [] (.int 1) true
#guard !recognizes [.req "x"] [] (.int 1) true
#guard !recognizes [] ["x"] (.int 1) true
#guard !recognizes [] [] (.int 2) true
#guard !recognizes [] [] (.int 1) false

private def readX : ClosureCode := ⟨[], [], .var .lvar "x", true, rfl⟩
private def captureTy : Ty := .clos readX (.ivarCons "x" .int .ivar0) .never
private def captured : Machine := reifiedMachine (bootMachine.setLocal "x" (.int 1))
  [] [] (.var .lvar "x") true
#guard closB captureTy captured (.ref bootMachine.heap.objs.size)
#guard closB captureTy (captured.setLocal "x" (.int 2)) (.ref bootMachine.heap.objs.size)
#guard !closB captureTy (captured.setLocal "x" .nil) (.ref bootMachine.heap.objs.size)
#guard envGet? (killClosOver [("f", captureTy)] "x" .nilT) "f" = some .any

#print axioms stored_literal
end Checker.Soundness.Typed.ClosureValueControls
