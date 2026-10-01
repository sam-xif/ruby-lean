import Denote.Examples.Derivations

/-! 091 derives the exact receiver and block body through an arbitrary registry family. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

def program_091_block_each_int : Ratchet.Expr :=
  .send (some (.array [.int 1, .int 2, .int 3])) "each" []
    (some (.block [.req "x"] [] (.send (some (.var .lvar "x")) "+" [.int 1] none)))

theorem derivD_each : (DJudgeC dclinks).judge [] program_091_block_each_int (.arrayOf .int) [] := by
  intro F hF
  apply hF DClink.flow (by simp [dclinks])
  apply hF DClink.DFlow.each (by simp [dclinks]) (names := []) (Γb := [("x", .int)])
  · apply hF DClink.DFlow.embed (by simp [dclinks])
    exact hF DClink.arrayLit (by simp [dclinks])
      (hF DClink.DJudgeAll.cons (by simp [dclinks]) (hF DClink.intLit (by simp [dclinks]))
        (hF DClink.DJudgeAll.cons (by simp [dclinks]) (hF DClink.intLit (by simp [dclinks]))
          (hF DClink.DJudgeAll.cons (by simp [dclinks]) (hF DClink.intLit (by simp [dclinks]))
            (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl) rfl) rfl) rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hF DClink.prim (by simp [dclinks])
      (hF DClink.var (by simp [dclinks]) rfl rfl)
      (hF DClink.DJudgeAll.cons (by simp [dclinks])
        (hF DClink.intLit (by simp [dclinks])) (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl)
      .intAdd rfl (by intro h; cases h)

theorem safe_091_block_each_int (hb : bootOkB = true) :
    StuckFree bootMachine program_091_block_each_int :=
  dregistry_safe derivD_each (stateOk_boot hb)

#print axioms safe_091_block_each_int
end Ratchet.Denote.Typed
