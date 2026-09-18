import Denote.Clink.Registry
import Ratchet.Controls.RecursiveControls

/-! Worked 060: constructor-wise, so the proof-term audit sees exactly the rules used. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote
open Ratchet.RecursiveControl

private def factCtx : Ctx := topBodyCtx ctx0 decl
private def scope : RecScope := ⟨decl, params, .int⟩

private theorem fact_body_deriv : (DJudgeC dclinks).judge params body .int params
    factCtx .ivar0 factCtx .ivar0 := by
  intro F hF
  have hv : F.judge params n .int params factCtx .ivar0 factCtx .ivar0 :=
    hF DClink.var (by simp [dclinks]) rfl rfl
  have h1 : F.judge params (.int 1) .int params factCtx .ivar0 factCtx .ivar0 :=
    hF DClink.intLit (by simp [dclinks])
  have ha : F.all params [.int 1] [.int] params factCtx .ivar0 factCtx .ivar0 :=
    hF DClink.DJudgeAll.cons (by simp [dclinks]) h1
      (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl
  have hm : F.judge params smaller .int params factCtx .ivar0 factCtx .ivar0 :=
    hF DClink.prim (by simp [dclinks]) hv ha DPrim.intSub rfl (by intro; rfl)
  have hc : F.judge params (.send (some n) "<=" [.int 1] none) .bool params
      factCtx .ivar0 factCtx .ivar0 :=
    hF DClink.prim (by simp [dclinks]) hv ha DPrim.intLe rfl (by intro; rfl)
  have hrec : F.recBody factCtx .ivar0 scope params (.send none "fact" [smaller] none) .int params :=
    hF DClink.DJudgeRec.selfCall (by simp [dclinks])
      (hF DClink.DJudgeRecAll.cons (by simp [dclinks])
        (hF DClink.DJudgeRec.embed (by simp [dclinks]) hm)
        (hF DClink.DJudgeRecAll.nil (by simp [dclinks])) rfl)
      rfl (by simp [scope, params, FirstOrder, isAliasTy]) rfl
      (by change decl ∈ [decl]; simp) rfl rfl rfl rfl rfl rfl rfl
      (by simp [params, FirstOrder, stripAlias])
  have ht : F.recBody factCtx .ivar0 scope params
      (.send (some n) "*" [.send none "fact" [smaller] none] none) .int params :=
    hF DClink.DJudgeRec.prim (by simp [dclinks])
      (hF DClink.DJudgeRec.embed (by simp [dclinks]) hv)
      (hF DClink.DJudgeRecAll.cons (by simp [dclinks]) hrec
        (hF DClink.DJudgeRecAll.nil (by simp [dclinks])) rfl)
      DPrim.intMul rfl (by intro; rfl)
  exact hF DClink.recursive (by simp [dclinks]) (s := scope) rfl
    (hF DClink.DJudgeRec.if' (by simp [dclinks])
      (hF DClink.DJudgeRec.embed (by simp [dclinks]) hc)
      (hF DClink.DJudgeRec.embed (by simp [dclinks]) h1) ht)

def program_060_fun_recursive_factorial : Ratchet.Expr := program

theorem derivD_recursive_factorial : (DJudgeC dclinks).judge [] program_060_fun_recursive_factorial
    .int [] ctx0 .ivar0 (topDeclCtx ctx0 decl) .ivar0 := by
  intro F hF
  have hd : F.judge [] definition .sym [] ctx0 .ivar0 (topDeclCtx ctx0 decl) .ivar0 :=
    hF DClink.defDecl (by simp [dclinks]) rfl
      (by simp [params, FirstOrder, isAliasTy]) rfl (fact_body_deriv F hF)
      rfl rfl rfl rfl rfl rfl rfl (by simp) (by simp [ctx0, Ctx.defs]) (by decide) (by decide)
  have ha : F.all [] [.int 4] [.int] [] (topDeclCtx ctx0 decl) .ivar0 (topDeclCtx ctx0 decl) .ivar0 :=
    hF DClink.DJudgeAll.cons (by simp [dclinks])
      (hF DClink.intLit (by simp [dclinks]))
      (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl
  have hc : F.judge [] (.send none "fact" [.int 4] none) .int []
      (topDeclCtx ctx0 decl) .ivar0 (topDeclCtx ctx0 decl) .ivar0 :=
    hF DClink.callSig (by simp [dclinks]) (decl := decl) (ps := params) rfl
      (by simp [params, FirstOrder, isAliasTy]) rfl (fact_body_deriv F hF) ha
      (by change decl ∈ [decl]; simp) rfl rfl rfl rfl rfl rfl rfl (by simp)
  exact hF DClink.seq (by simp [dclinks])
    (hF DClink.DJudgeSeq.cons (by simp [dclinks]) hd
      (hF DClink.DJudgeSeq.last (by simp [dclinks]) hc))

theorem safe_060_fun_recursive_factorial (hb : bootOkB = true) :
    StuckFree bootMachine program_060_fun_recursive_factorial :=
  dregistry_safe derivD_recursive_factorial (stateOk_boot hb)

#print axioms safe_060_fun_recursive_factorial
end Ratchet.Denote.Typed
