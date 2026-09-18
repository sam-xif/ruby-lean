import Denote.Clink.Registry

/-! Constructor-wise method example for the independent proof-term coverage audit. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private def addDecl : Defn := ⟨"add", [.req "x", .req "y"],
  .send (some (.var .lvar "x")) "+" [.var .lvar "y"] none⟩
private def addParams : Env := [("x", .int), ("y", .int)]

private theorem add_body_deriv : (DJudgeC dclinks).judge addParams addDecl.body .int addParams
    (topBodyCtx ctx0 addDecl) .ivar0 (topBodyCtx ctx0 addDecl) .ivar0 := by
  intro F hF
  exact hF DClink.prim (by simp [dclinks])
    (hF DClink.var (by simp [dclinks]) rfl rfl)
    (hF DClink.DJudgeAll.cons (by simp [dclinks])
      (hF DClink.var (by simp [dclinks]) rfl rfl)
      (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl)
    DPrim.intAdd rfl (by intro; rfl)

def program_052_simple_fun : Ratchet.Expr :=
  .seq [.def' addDecl.name addDecl.params addDecl.body, .send none "add" [.int 1, .int 2] none]

theorem derivD_simple_fun : (DJudgeC dclinks).judge [] program_052_simple_fun .int []
    ctx0 .ivar0 (topDeclCtx ctx0 addDecl) .ivar0 := by
  intro F hF
  have hd : F.judge [] (.def' addDecl.name addDecl.params addDecl.body) .sym []
      ctx0 .ivar0 (topDeclCtx ctx0 addDecl) .ivar0 :=
    hF DClink.defDecl (by simp [dclinks]) rfl
      (by simp [addParams, FirstOrder, isAliasTy]) rfl (add_body_deriv F hF)
      rfl rfl rfl rfl rfl rfl rfl (by simp) (by simp [ctx0, Ctx.defs]) (by decide) (by decide)
  have ha : F.all [] [.int 1, .int 2] [.int, .int] []
      (topDeclCtx ctx0 addDecl) .ivar0 (topDeclCtx ctx0 addDecl) .ivar0 :=
    hF DClink.DJudgeAll.cons (by simp [dclinks])
      (hF DClink.intLit (by simp [dclinks]))
      (hF DClink.DJudgeAll.cons (by simp [dclinks])
        (hF DClink.intLit (by simp [dclinks]))
        (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl) rfl
  have hc : F.judge [] (.send none addDecl.name [.int 1, .int 2] none) .int []
      (topDeclCtx ctx0 addDecl) .ivar0 (topDeclCtx ctx0 addDecl) .ivar0 :=
    hF DClink.callSig (by simp [dclinks]) rfl
      (by simp [addParams, FirstOrder, isAliasTy]) rfl (add_body_deriv F hF) ha
      (by change addDecl ∈ [addDecl]; simp) rfl rfl rfl rfl rfl rfl rfl (by simp)
  exact hF DClink.seq (by simp [dclinks])
    (hF DClink.DJudgeSeq.cons (by simp [dclinks]) hd
      (hF DClink.DJudgeSeq.last (by simp [dclinks]) hc))

theorem safe_052_simple_fun (hb : bootOkB = true) : StuckFree bootMachine program_052_simple_fun :=
  dregistry_safe derivD_simple_fun (stateOk_boot hb)

#print axioms safe_052_simple_fun
end Ratchet.Denote.Typed
