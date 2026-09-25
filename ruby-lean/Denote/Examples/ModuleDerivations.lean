import Denote.Clink.Registry

/-! Independent whole-077 derivation, for every Integer singleton result. The body
proof is checked at installation and reused at the call, with no Sorbet premise. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.ModuleProgram
open RubyCore Ratchet Ratchet.Denote

def header : Cls := moduleHeader "M"
def entry : Ctx := moduleHeaderCtx (moduleBodyCtx ctx0 "M") "M"
def decl (n : Int) : Defn := ⟨"foo", [], .int n⟩
def installed (n : Int) : Ctx := singletonDeclCtx entry header (decl n)
def caller (n : Int) : Ctx := returnScopeCtx ctx0 (installed n)
def record (n : Int) : Cls := classWithSingleton header (decl n)
def program (n : Int) : Ratchet.Expr := .seq [
  .module' "M" (.defs .self' "foo" [] (.int n)),
  .send (some (.const "M")) "foo" [] none]

theorem full_deriv (n : Int) :
    (DJudgeC dclinks).judge [] (program n) .int [] ctx0 .ivar0 (caller n) .ivar0 := by
  intro F hF
  have definition : F.judge [] (.defs .self' "foo" [] (.int n)) .sym []
      entry .ivar0 (installed n) .ivar0 :=
    @hF DClink.singletonDef (by simp [dclinks]) entry [] [] .ivar0 .int header (decl n) []
      rfl (by simp) rfl (hF DClink.intLit (by simp [dclinks])) (List.mem_cons_self)
      (by change singletonRuleB entry [] .ivar0 header (decl 0) = true; decide)
  have mod : F.judge [] (.module' "M" (.defs .self' "foo" [] (.int n))) .sym []
      ctx0 .ivar0 (caller n) .ivar0 :=
    hF DClink.moduleDecl (by simp [dclinks]) definition
      (by change moduleRuleB ctx0 (installed 0) [] .ivar0 .sym "M" = true; decide)
  have call : F.judge [] (.send (some (.const "M")) "foo" [] none) .int []
      (caller n) .ivar0 :=
    @hF DClink.callSingleton (by simp [dclinks]) (caller n) (caller n) (caller n)
      [] [] [] [] .ivar0 .ivar0 .ivar0 .int (record n) (decl n) [] _ _
      (@hF DClink.constClass (by simp [dclinks]) (caller n) [] .ivar0 (record n)
        (List.mem_cons_self))
      (hF DClink.DJudgeAll.nil (by simp [dclinks]))
      (List.mem_cons_self) (List.mem_cons_self)
      (by change directCallNameB "foo" = true; decide) rfl (by simp) rfl
      (hF DClink.intLit (by simp [dclinks]))
      (by change instanceCallB (caller 0) [] .ivar0 = true; decide)
  exact hF DClink.seq (by simp [dclinks]) (hF DClink.DJudgeSeq.cons (by simp [dclinks])
    mod (hF DClink.DJudgeSeq.last (by simp [dclinks]) call))

#print axioms full_deriv
end Ratchet.Denote.Typed.ModuleProgram

namespace Ratchet.Denote.Typed
open Ratchet.Denote
def program_077_module_basic : Ratchet.Expr := ModuleProgram.program 1
theorem safe_077_module_basic (hb : bootOkB = true) :
    StuckFree bootMachine program_077_module_basic :=
  dregistry_safe (ModuleProgram.full_deriv 1) (stateOk_boot hb)
#guard match RubyCore.Interp.run 150 (evalFrom bootMachine program_077_module_basic) with
  | .value (.int 1) _ => true
  | _ => false
#print axioms safe_077_module_basic
end Ratchet.Denote.Typed
