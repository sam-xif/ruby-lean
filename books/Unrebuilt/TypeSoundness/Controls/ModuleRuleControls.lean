import Books.TypeSoundness.Rules.Module.ModuleRule
import Books.TypeSoundness.Rules.Singleton.SingletonRules
import Books.TypeSoundness.Rules.Class.ClassConstant
import Books.TypeSoundness.Rules.Expr.Sequence
import Books.TypeSoundness.Conformance.Core.Boot

/-! Whole module execution consumes a checked singleton body and retains its result.
These semantic pilots do not add a checker admission or trust Sorbet's untyped methods. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.ModuleRuleControls
open RubyCore Checker Checker.Soundness

private def header : Cls := moduleHeader "MeasuredModule"
private def entry : Ctx := moduleHeaderCtx (moduleBodyCtx ctx0 "MeasuredModule") "MeasuredModule"
private def decl (n : Int) : Defn := ⟨"foo", [], .int n⟩
private def installed (n : Int) : Ctx := singletonDeclCtx entry header (decl n)
private def finished (n : Int) : Ctx := returnScopeCtx ctx0 (installed n)
private def record (n : Int) : Cls := classWithSingleton header (decl n)
private def program (n : Int) : Checker.Expr := .seq [
  .module' "MeasuredModule" (.defs .self' "foo" [] (.int n)),
  .send (some (.const "MeasuredModule")) "foo" [] none]

theorem module_singleton (n : Int) :
    SemSafeCtxA ctx0 [] .ivar0 (program n) .int (finished n) [] .ivar0 := by
  have definition : SemSafeCtxA entry [] .ivar0 (.defs .self' "foo" [] (.int n))
      .sym (installed n) [] .ivar0 :=
    SemSafeCtxA.singletonDef (c := header) (d := decl n) (ps := []) rfl
      (by simp) rfl .intLit (List.mem_cons_self)
      (by change singletonRuleB entry [] .ivar0 header (decl 0) = true; decide)
  have mod : SemSafeCtxA ctx0 [] .ivar0 (.module' "MeasuredModule" (.defs .self' "foo" [] (.int n)))
      .sym (finished n) [] .ivar0 := SemSafeCtxA.moduleDecl definition
        (by change moduleRuleB ctx0 (installed 0) [] .ivar0 .sym "MeasuredModule" = true; decide)
  have call : SemSafeCtxA (finished n) [] .ivar0
      (.send (some (.const "MeasuredModule")) "foo" [] none) .int (finished n) [] .ivar0 :=
    SemSafeCtxA.callSingleton (c := record n) (d := decl n) (ps := [])
      (SemSafeCtxA.constClass (c := record n) (List.mem_cons_self))
      .nil (List.mem_cons_self)
      (List.mem_cons_self) (by change directCallNameB "foo" = true; decide) rfl (by simp) rfl .intLit
      (by change instanceCallB (finished 0) [] .ivar0 = true; decide)
  exact mod.seq call

theorem module_singleton_safe (hb : bootOkB = true) (n : Int) : StuckFree bootMachine (program n) :=
  (module_singleton n).closed (stateOk_boot hb)

theorem module_result (n : Int) : SemSafeCtxA ctx0 [] .ivar0 (.module' "MeasuredModule" (.int n))
    .int (returnScopeCtx ctx0 entry) [] .ivar0 := SemSafeCtxA.moduleDecl .intLit (by decide)

private def localProgram (outside inside : Int) : Checker.Expr := .seq [
  .vasgn .lvar "keep" (.int outside),
  .module' "MeasuredModule" (.vasgn .lvar "keep" (.int inside)),
  .var .lvar "keep"]

theorem separate_locals (outside inside : Int) :
    SemSafeCtxA ctx0 [] .ivar0 (localProgram outside inside) .int
      (returnScopeCtx ctx0 entry) [("keep", .int)] .ivar0 := by
  have caller : SemSafeCtxA ctx0 [] .ivar0 (.vasgn .lvar "keep" (.int outside))
      .int ctx0 [("keep", .int)] .ivar0 := SemSafeCtxA.intLit.vasgn rfl rfl rfl
  have body : SemSafeCtxA entry [] .ivar0 (.vasgn .lvar "keep" (.int inside))
      .int entry [("keep", .int)] .ivar0 := SemSafeCtxA.intLit.vasgn rfl rfl rfl
  have mod : SemSafeCtxA ctx0 [("keep", .int)] .ivar0
      (.module' "MeasuredModule" (.vasgn .lvar "keep" (.int inside)))
      .int (returnScopeCtx ctx0 entry) [("keep", .int)] .ivar0 :=
    SemSafeCtxA.moduleDecl body (by decide)
  exact SemSafeCtxA.sequence (.cons caller (.cons mod (.last (SemSafeCtxA.var rfl rfl))))

#guard match Interp.run 150 (evalFrom bootMachine (program 1)) with
  | .value (.int 1) _ => true
  | _ => false
#guard match Interp.run 100 (evalFrom bootMachine (.module' "MeasuredModule" (.int 7))) with
  | .value (.int 7) _ => true
  | _ => false
#guard match Interp.run 150 (evalFrom bootMachine (localProgram 3 7)) with
  | .value (.int 3) _ => true
  | _ => false

#guard !moduleRuleB (finished 1) entry [] .ivar0 .int "MeasuredModule"
#guard !moduleRuleB ctx0 entry [] .ivar0 (.arrow0 .int) "MeasuredModule"
#guard !(finished 1).pos.plainAlloc.contains "MeasuredModule"

#print axioms module_singleton
#print axioms module_singleton_safe
#print axioms module_result
#print axioms separate_locals
end Checker.Soundness.Typed.ModuleRuleControls
