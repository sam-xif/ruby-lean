import Books.TypeSoundness.Registry.Registry

/-! Independent whole-080 derivation, for every Integer returned by the first
singleton. The second body consumes its checked own-table code through a bare call. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.SingletonImplicitProgram
open RubyCore Checker Checker.Soundness

def value (n : Int) : Defn := ⟨"value", [], .int n⟩
def describe : Defn := ⟨"describe", [], .send (some (.vcall "value")) "*" [.int 2] none⟩
def header : Cls := moduleHeader "M"
def entry : Ctx := moduleHeaderCtx (moduleBodyCtx ctx0 "M") "M"
def withValue (n : Int) : Cls := classWithSingleton header (value n)
def afterValue (n : Int) : Ctx := singletonDeclCtx entry header (value n)
def fullClass (n : Int) : Cls := classWithSingleton (withValue n) describe
def installed (n : Int) : Ctx := singletonDeclCtx (afterValue n) (withValue n) describe
def caller (n : Int) : Ctx := returnScopeCtx ctx0 (installed n)
def program (n : Int) : Checker.Expr := .seq [
  .module' "M" (.seq [.defs .self' "value" [] (.int n),
    .defs .self' describe.name describe.params describe.body]),
  .send (some (.const "M")) "describe" [] none]

private theorem describe_deriv {κ : Ctx} (n : Int)
    (hs : κ.selfTy = some (.clsOf "M")) (hc : fullClass n ∈ κ.classes)
    (hf : nameFreeN κ "*" = true) (hg : instanceCallB κ [] .ivar0 = true) :
    (DJudgeC dclinks).judge [] describe.body .int [] κ .ivar0 := by
  intro F hF
  have hv : F.judge [] (.vcall "value") .int [] κ .ivar0 :=
    @hF DClink.callSingletonImplicit (by simp [dclinks]) κ κ [] [] [] .ivar0 .ivar0 .int
      (fullClass n) (value n) [] [] (.vcall "value") .vcall hs
      (hF DClink.DJudgeAll.nil (by simp [dclinks])) hc
      (List.mem_cons_of_mem _ (List.mem_cons_self))
      (by change directCallNameB "value" = true; decide) rfl (by simp) rfl
      (hF DClink.intLit (by simp [dclinks])) hg
  exact hF DClink.prim (by simp [dclinks]) hv
    (hF DClink.DJudgeAll.cons (by simp [dclinks]) (hF DClink.intLit (by simp [dclinks]))
      (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl) DPrim.intMul hf (by intro h; cases h)

theorem full_deriv (n : Int) :
    (DJudgeC dclinks).judge [] (program n) .int [] ctx0 .ivar0 (caller n) .ivar0 := by
  intro F hF
  have hv : F.judge [] (.defs .self' "value" [] (.int n)) .sym [] entry .ivar0 (afterValue n) .ivar0 :=
    @hF DClink.singletonDef (by simp [dclinks]) entry [] [] .ivar0 .int header (value n) []
      rfl (by simp) rfl (hF DClink.intLit (by simp [dclinks])) (List.mem_cons_self)
      (by change singletonRuleB entry [] .ivar0 header (value 0) = true; decide)
  have hd : F.judge [] (.defs .self' describe.name describe.params describe.body) .sym []
      (afterValue n) .ivar0 (installed n) .ivar0 :=
    @hF DClink.singletonDef (by simp [dclinks]) (afterValue n) [] [] .ivar0 .int
      (withValue n) describe [] rfl (by simp) rfl
      (describe_deriv n rfl (List.mem_cons_self)
        (by change nameFreeN (singletonBodyCtx (installed 0) "M" "describe") "*" = true; decide)
        (by change instanceCallB (singletonBodyCtx (installed 0) "M" "describe") [] .ivar0 = true; decide) F hF)
      (List.mem_cons_self)
      (by change singletonRuleB (afterValue 0) [] .ivar0 (withValue 0) describe = true; decide)
  have hm : F.judge [] (.module' "M" (.seq [.defs .self' "value" [] (.int n),
      .defs .self' describe.name describe.params describe.body])) .sym [] ctx0 .ivar0 (caller n) .ivar0 :=
    hF DClink.moduleDecl (by simp [dclinks])
      (hF DClink.seq (by simp [dclinks]) (hF DClink.DJudgeSeq.cons (by simp [dclinks]) hv
        (hF DClink.DJudgeSeq.last (by simp [dclinks]) hd)))
      (by change moduleRuleB ctx0 (installed 0) [] .ivar0 .sym "M" = true; decide)
  have hc : F.judge [] (.send (some (.const "M")) "describe" [] none) .int [] (caller n) .ivar0 :=
    @hF DClink.callSingleton (by simp [dclinks]) (caller n) (caller n) (caller n)
      [] [] [] [] .ivar0 .ivar0 .ivar0 .int (fullClass n) describe [] _ _
      (@hF DClink.constClass (by simp [dclinks]) (caller n) [] .ivar0 (fullClass n) (List.mem_cons_self))
      (hF DClink.DJudgeAll.nil (by simp [dclinks])) (List.mem_cons_self) (List.mem_cons_self)
      (by decide) rfl (by simp) rfl
      (describe_deriv n rfl (List.mem_cons_self)
        (by change nameFreeN (singletonBodyCtx (caller 0) "M" "describe") "*" = true; decide)
        (by change instanceCallB (singletonBodyCtx (caller 0) "M" "describe") [] .ivar0 = true; decide) F hF)
      (by change instanceCallB (caller 0) [] .ivar0 = true; decide)
  exact hF DClink.seq (by simp [dclinks]) (hF DClink.DJudgeSeq.cons (by simp [dclinks])
    hm (hF DClink.DJudgeSeq.last (by simp [dclinks]) hc))

#print axioms full_deriv
end Checker.Soundness.Typed.SingletonImplicitProgram

namespace Checker.Soundness.Typed
open Checker.Soundness
def program_080_module_method_calls_method : Checker.Expr := SingletonImplicitProgram.program 21
theorem safe_080_module_method_calls_method (hb : bootOkB = true) :
    StuckFree bootMachine program_080_module_method_calls_method :=
  dregistry_safe (SingletonImplicitProgram.full_deriv 21) (stateOk_boot hb)
#guard match RubyCore.Interp.run 300 (evalFrom bootMachine program_080_module_method_calls_method) with
  | .value (.int 42) _ => true
  | _ => false
#print axioms safe_080_module_method_calls_method
end Checker.Soundness.Typed
