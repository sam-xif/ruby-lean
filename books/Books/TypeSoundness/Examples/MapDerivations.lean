import Books.TypeSoundness.Examples.Derivations

/-! 092/093 derive the exact receivers and checked block bodies through an arbitrary registry family. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

def program_092_block_map_to_s : Checker.Expr :=
  .send (some (.array [.int 1, .int 2, .int 3])) "map" []
    (some (.block [.req "n"] [] (.send (some (.var .lvar "n")) "to_s" [] none)))

theorem derivD_map_to_s : (DJudgeC dclinks).judge [] program_092_block_map_to_s (.arrayOf (.cls "String")) [] := by
  intro F hF
  apply hF DClink.flow (by simp [dclinks])
  apply hF DClink.DFlow.map (by simp [dclinks]) (names := []) (Γb := [("n", .int)])
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
  · rfl
  · rfl
  · exact hF DClink.prim (by simp [dclinks])
      (hF DClink.var (by simp [dclinks]) rfl rfl)
      (hF DClink.DJudgeAll.nil (by simp [dclinks]))
      .intToS rfl (by intro h; cases h)

theorem safe_092_block_map_to_s (hb : bootOkB = true) :
    StuckFree bootMachine program_092_block_map_to_s :=
  dregistry_safe derivD_map_to_s (stateOk_boot hb)

def program_093_block_doend_with_block_local : Checker.Expr :=
  .send (some (.array [.int 1, .int 2])) "map" [] (some (.block [.req "x"] ["y"]
    (.seq [.vasgn .lvar "y" (.send (some (.var .lvar "x")) "*" [.int 2] none),
      .send (some (.var .lvar "y")) "+" [.int 1] none])))

theorem derivD_map_local : (DJudgeC dclinks).judge [] program_093_block_doend_with_block_local
    (.arrayOf .int) [] := by
  intro F hF
  apply hF DClink.flow (by simp [dclinks])
  apply hF DClink.DFlow.map (by simp [dclinks]) (names := []) (Γb := [("x", .int), ("y", .int)])
  · apply hF DClink.DFlow.embed (by simp [dclinks])
    exact hF DClink.arrayLit (by simp [dclinks])
      (hF DClink.DJudgeAll.cons (by simp [dclinks]) (hF DClink.intLit (by simp [dclinks]))
        (hF DClink.DJudgeAll.cons (by simp [dclinks]) (hF DClink.intLit (by simp [dclinks]))
          (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl) rfl) rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · apply hF DClink.seq (by simp [dclinks])
    apply hF DClink.DJudgeSeq.cons (by simp [dclinks])
    · exact hF DClink.vasgn (by simp [dclinks])
        (hF DClink.prim (by simp [dclinks]) (hF DClink.var (by simp [dclinks]) rfl rfl)
          (hF DClink.DJudgeAll.cons (by simp [dclinks]) (hF DClink.intLit (by simp [dclinks]))
            (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl)
          .intMul rfl (by intro h; cases h)) rfl rfl rfl
    · exact hF DClink.DJudgeSeq.last (by simp [dclinks])
        (hF DClink.prim (by simp [dclinks]) (hF DClink.var (by simp [dclinks]) rfl rfl)
          (hF DClink.DJudgeAll.cons (by simp [dclinks]) (hF DClink.intLit (by simp [dclinks]))
            (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl)
          .intAdd rfl (by intro h; cases h))

theorem safe_093_block_doend_with_block_local (hb : bootOkB = true) :
    StuckFree bootMachine program_093_block_doend_with_block_local :=
  dregistry_safe derivD_map_local (stateOk_boot hb)

#print axioms safe_092_block_map_to_s
#print axioms safe_093_block_doend_with_block_local
end Checker.Soundness.Typed
