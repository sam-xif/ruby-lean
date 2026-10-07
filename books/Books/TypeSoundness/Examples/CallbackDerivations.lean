import Books.TypeSoundness.Examples.Derivations

/-! Whole corpus programs through the arbitrary registry family. Definition proofs
are uniform in callback code; call proofs supply each actual body and capture facts. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

def twiceBody : Checker.Expr := .send (some (.yield' [.int 1])) "+" [.yield' [.int 2]] none
def twiceDecl : Defn := ⟨"twice", [], twiceBody⟩
def twiceCtx : Ctx := topDeclCtx ctx0 twiceDecl
def multiplyBlock : Checker.Expr := .send (some (.var .lvar "x")) "*" [.int 10] none
def program_094_yield_arith : Checker.Expr := .seq [
  .def' "twice" [] twiceBody, .send none "twice" [] (some (.block [.req "x"] [] multiplyBlock))]

private theorem methodInt {κ : Ctx} {fr : Frame} {Γ : Env} (n : Int) :
    (DJudgeC dclinks).method κ .ivar0 fr [.int] .int Γ (.int n) .int Γ := by
  intro F hF
  exact hF DClink.DMethod.ordinary (by simp [dclinks]) (fun _ => hF DClink.intLit (by simp [dclinks]))

private theorem methodVar {κ : Ctx} {fr : Frame} {Γ : Env} {x : String}
    (hg : envGet? Γ x = some .int) :
    (DJudgeC dclinks).method κ .ivar0 fr [.int] .int Γ (.var .lvar x) .int Γ := by
  intro F hF
  exact hF DClink.DMethod.ordinary (by simp [dclinks]) (fun _ => hF DClink.var (by simp [dclinks]) hg rfl)

private theorem methodYield {κ : Ctx} {fr : Frame} {Γ : Env} (n : Int)
    (ht : activationReturnB Γ = true) :
    (DJudgeC dclinks).method κ .ivar0 fr [.int] .int Γ (.yield' [.int n]) .int Γ := by
  intro F hF
  exact hF DClink.DMethod.yieldOne (by simp [dclinks]) (methodInt n F hF) ht rfl

theorem derivD_twiceBody : (DJudgeC dclinks).method twiceCtx .ivar0
    ⟨"Object", "Object", "twice", false⟩ [.int] .int [] twiceBody .int [] := by
  intro F hF
  exact hF DClink.DMethod.prim (by simp [dclinks]) (methodYield 1 rfl F hF)
    (hF DClink.DMethodAll.cons (by simp [dclinks]) (methodYield 2 rfl F hF)
      (hF DClink.DMethodAll.nil (by simp [dclinks])) rfl) .intAdd rfl (by intro h; cases h)

theorem derivD_yieldArith : (DJudgeC dclinks).judge [] program_094_yield_arith .int [] ctx0 .ivar0 twiceCtx .ivar0 := by
  intro F hF
  apply hF DClink.flow (by simp [dclinks])
  apply hF DClink.DFlow.sequence (by simp [dclinks])
  apply hF DClink.DFlowSeq.cons (by simp [dclinks])
  · apply hF DClink.DFlow.embed (by simp [dclinks])
    exact hF DClink.defBlock (by simp [dclinks]) (ps := []) rfl rfl rfl rfl rfl
      (derivD_twiceBody F hF) rfl rfl rfl rfl rfl rfl rfl
      (by intro p h; cases h) (by intro d h; cases h) (by decide) (by decide)
  · apply hF DClink.DFlowSeq.last (by simp [dclinks])
    exact hF DClink.DFlow.callBlock (by simp [dclinks]) (κ := twiceCtx) (decl := twiceDecl)
      (Γ := []) (Γb := [("x", .int)]) (I := .ivar0) (τ := .int) (br := .int)
      (facts := LocalFacts.unknown.afterEffect) (locals := []) (body := multiplyBlock) (ps := [("x", .int)]) (names := [])
      (derivD_twiceBody F hF) rfl (by exact List.Mem.head _) rfl rfl rfl rfl rfl rfl rfl rfl
      (hF DClink.prim (by simp [dclinks])
        (hF DClink.var (by simp [dclinks]) rfl rfl)
        (hF DClink.DJudgeAll.cons (by simp [dclinks]) (hF DClink.intLit (by simp [dclinks]))
          (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl)
        .intMul rfl (by intro h; cases h))

def mixedBody : Checker.Expr := .seq [.vasgn .lvar "total" .nil,
  .vasgn .lvar "total" (.yield' [.int 1]), .vasgn .lvar "result" (.yield' [.int 2]),
  .send (some (.var .lvar "total")) "+" [.var .lvar "result"] none]
def mixedDecl : Defn := ⟨"mixed", [], mixedBody⟩
def mixedCtx : Ctx := topDeclCtx ctx0 mixedDecl
def writeBlock : Checker.Expr := .vasgn .lvar "total"
  (.send (some (.var .lvar "total")) "+" [.var .lvar "x"] none)
def program_260_yield_local_and_captured_write : Checker.Expr := .seq [
  .def' "mixed" [] mixedBody, .vasgn .lvar "total" (.int 0),
  .send none "mixed" [] (some (.block [.req "x"] [] writeBlock)), .var .lvar "total"]

theorem derivD_mixedBody : (DJudgeC dclinks).method mixedCtx .ivar0
    ⟨"Object", "Object", "mixed", false⟩ [.int] .int [] mixedBody .int [("total", .int), ("result", .int)] := by
  intro F hF
  apply hF DClink.DMethod.sequence (by simp [dclinks])
  apply hF DClink.DMethodSeq.cons (by simp [dclinks])
  · exact hF DClink.DMethod.vasgn (by simp [dclinks])
      (hF DClink.DMethod.ordinary (by simp [dclinks]) (fun _ => hF DClink.nilLit (by simp [dclinks])))
      rfl rfl (fun _ => rfl) rfl
  · apply hF DClink.DMethodSeq.cons (by simp [dclinks])
    · exact hF DClink.DMethod.vasgn (by simp [dclinks]) (methodYield 1 rfl F hF) rfl rfl (fun _ => rfl) rfl
    · apply hF DClink.DMethodSeq.cons (by simp [dclinks])
      · exact hF DClink.DMethod.vasgn (by simp [dclinks]) (methodYield 2 rfl F hF) rfl rfl (fun _ => rfl) rfl
      · apply hF DClink.DMethodSeq.last (by simp [dclinks])
        exact hF DClink.DMethod.prim (by simp [dclinks]) (methodVar rfl F hF)
          (hF DClink.DMethodAll.cons (by simp [dclinks]) (methodVar rfl F hF)
            (hF DClink.DMethodAll.nil (by simp [dclinks])) rfl) .intAdd rfl (by intro h; cases h)

theorem derivD_mixedCapture : (DJudgeC dclinks).judge [] program_260_yield_local_and_captured_write
    .int [("total", .int)] ctx0 .ivar0 mixedCtx .ivar0 := by
  intro F hF
  apply hF DClink.flow (by simp [dclinks])
  apply hF DClink.DFlow.sequence (by simp [dclinks])
  apply hF DClink.DFlowSeq.cons (by simp [dclinks])
  · apply hF DClink.DFlow.embed (by simp [dclinks])
    exact hF DClink.defBlock (by simp [dclinks]) (ps := []) rfl rfl rfl rfl rfl
      (derivD_mixedBody F hF) rfl rfl rfl rfl rfl rfl rfl
      (by intro p h; cases h) (by intro d h; cases h) (by decide) (by decide)
  · apply hF DClink.DFlowSeq.cons (by simp [dclinks])
    · exact hF DClink.DFlow.vasgn (by simp [dclinks])
        (hF DClink.DFlow.intLit (by simp [dclinks]) _ 0) rfl rfl rfl rfl
    · apply hF DClink.DFlowSeq.cons (by simp [dclinks])
      · exact hF DClink.DFlow.callBlock (by simp [dclinks]) (κ := mixedCtx) (decl := mixedDecl)
          (Γ := [("total", .int)]) (Γb := [("x", .int), ("total", .int)]) (I := .ivar0) (τ := .int) (br := .int)
          (facts := LocalFacts.unknown.afterEffect.write "total" false)
          (locals := []) (body := writeBlock) (ps := [("x", .int)]) (names := ["total"])
          (derivD_mixedBody F hF) rfl (by exact List.Mem.head _) rfl rfl rfl rfl rfl rfl rfl rfl
          (hF DClink.vasgn (by simp [dclinks])
            (hF DClink.prim (by simp [dclinks]) (hF DClink.var (by simp [dclinks]) rfl rfl)
              (hF DClink.DJudgeAll.cons (by simp [dclinks]) (hF DClink.var (by simp [dclinks]) rfl rfl)
                (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl)
              .intAdd rfl (by intro h; cases h)) rfl rfl rfl)
      · exact hF DClink.DFlowSeq.last (by simp [dclinks]) (hF DClink.DFlow.var (by simp [dclinks]) _ rfl rfl)

theorem safe_094_yield_arith (hb : bootOkB = true) : StuckFree bootMachine program_094_yield_arith :=
  dregistry_safe derivD_yieldArith (stateOk_boot hb)
theorem safe_260_yield_local_and_captured_write (hb : bootOkB = true) :
    StuckFree bootMachine program_260_yield_local_and_captured_write :=
  dregistry_safe derivD_mixedCapture (stateOk_boot hb)

#print axioms safe_094_yield_arith
#print axioms safe_260_yield_local_and_captured_write
end Checker.Soundness.Typed
