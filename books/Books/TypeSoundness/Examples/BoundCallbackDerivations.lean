import Books.TypeSoundness.Examples.CallbackDerivations

/-! Exact corpus programs through arbitrary registry interpretations. Alias copies,
overwrites, native calls and a final yield exercise every method-flow constructor. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

def boundDirectBody : Checker.Expr := .send (some (.var .lvar "b")) "call" [.int 5] none
def boundDirectDecl : Defn := ⟨"run", [.block (some "b")], boundDirectBody⟩
def boundDirectCtx : Ctx := topDeclCtx ctx0 boundDirectDecl
def incrementBlock : Checker.Expr := .send (some (.var .lvar "x")) "+" [.int 1] none
def program_095_block_param_ampersand : Checker.Expr := .seq [
  .def' "run" [.block (some "b")] boundDirectBody,
  .send none "run" [] (some (.block [.req "x"] [] incrementBlock))]

theorem derivD_boundDirectBody (code : ClosureCode) :
    (DJudgeC dclinks).methodFlow boundDirectCtx .ivar0 ⟨"Object", "Object", "run", false⟩
      [.int] .int [("b", .clos code .ivar0 .never)] ⟨["b"]⟩ boundDirectBody .int false
      [("b", .clos code .ivar0 .never)] ⟨["b"]⟩ := by
  intro F hF
  exact hF DClink.DMethodFlow.call (by simp [dclinks])
    (hF DClink.DMethodFlow.var (by simp [dclinks]) rfl rfl)
    (hF DClink.DMethodFlow.intLit (by simp [dclinks])) rfl rfl rfl rfl

theorem derivD_boundDirect : (DJudgeC dclinks).judge [] program_095_block_param_ampersand
    .int [] ctx0 .ivar0 boundDirectCtx .ivar0 := by
  intro F hF
  apply hF DClink.flow (by simp [dclinks])
  apply hF DClink.DFlow.sequence (by simp [dclinks])
  apply hF DClink.DFlowSeq.cons (by simp [dclinks])
  · apply hF DClink.DFlow.embed (by simp [dclinks])
    exact hF DClink.defBoundBlock (by simp [dclinks]) rfl rfl rfl rfl
      (fun code => derivD_boundDirectBody code F hF) rfl rfl rfl rfl rfl rfl rfl
      (by intro p h; cases h) (by intro d h; cases h) (by decide) (by decide)
  · apply hF DClink.DFlowSeq.last (by simp [dclinks])
    exact hF DClink.DFlow.callBoundBlock (by simp [dclinks]) (κ := boundDirectCtx) (decl := boundDirectDecl)
      (Γ := []) (Γb := [("x", .int)]) (I := .ivar0) (τ := .int) (br := .int)
      (facts := LocalFacts.unknown.afterEffect) (locals := []) (body := incrementBlock)
      (ps := [("x", .int)]) (names := [])
      (fun code => derivD_boundDirectBody code F hF) rfl (by exact List.Mem.head _) rfl rfl rfl rfl rfl rfl rfl rfl
      (hF DClink.prim (by simp [dclinks]) (hF DClink.var (by simp [dclinks]) rfl rfl)
        (hF DClink.DJudgeAll.cons (by simp [dclinks]) (hF DClink.intLit (by simp [dclinks]))
          (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl) .intAdd rfl (by intro h; cases h))

def boundAliasBody : Checker.Expr := .seq [.vasgn .lvar "copy" (.var .lvar "b"),
  .vasgn .lvar "b" .nil, .send (some (.var .lvar "copy")) "call" [.int 5] none,
  .vasgn .lvar "copy" .nil, .yield' [.int 7]]
def boundAliasDecl : Defn := ⟨"run", [.block (some "b")], boundAliasBody⟩
def boundAliasCtx : Ctx := topDeclCtx ctx0 boundAliasDecl
def boundWriteBlock : Checker.Expr := .vasgn .lvar "total"
  (.send (some (.var .lvar "total")) "+" [.var .lvar "value"] none)
def program_261_bound_block_alias_and_yield : Checker.Expr := .seq [
  .def' "run" [.block (some "b")] boundAliasBody, .vasgn .lvar "total" (.int 0),
  .send none "run" [] (some (.block [.req "value"] [] boundWriteBlock)), .var .lvar "total"]

theorem derivD_boundAliasBody (code : ClosureCode) :
    (DJudgeC dclinks).methodFlow boundAliasCtx .ivar0 ⟨"Object", "Object", "run", false⟩
      [.int] .int [("b", .clos code .ivar0 .never)] ⟨["b"]⟩ boundAliasBody .int false
      [("b", .nilT), ("copy", .nilT)] .empty := by
  intro F hF
  apply hF DClink.DMethodFlow.sequence (by simp [dclinks])
  apply hF DClink.DMethodFlowSeq.cons (by simp [dclinks])
  · exact hF DClink.DMethodFlow.vasgn (by simp [dclinks])
      (hF DClink.DMethodFlow.var (by simp [dclinks]) rfl rfl) rfl rfl (fun _ => rfl) rfl
  · apply hF DClink.DMethodFlowSeq.cons (by simp [dclinks])
    · exact hF DClink.DMethodFlow.vasgn (by simp [dclinks])
        (hF DClink.DMethodFlow.nilLit (by simp [dclinks])) rfl rfl (fun _ => rfl) rfl
    · apply hF DClink.DMethodFlowSeq.cons (by simp [dclinks])
      · exact hF DClink.DMethodFlow.call (by simp [dclinks])
          (hF DClink.DMethodFlow.var (by simp [dclinks]) rfl rfl)
          (hF DClink.DMethodFlow.intLit (by simp [dclinks])) rfl rfl rfl rfl
      · apply hF DClink.DMethodFlowSeq.cons (by simp [dclinks])
        · exact hF DClink.DMethodFlow.vasgn (by simp [dclinks])
            (hF DClink.DMethodFlow.nilLit (by simp [dclinks])) rfl rfl (fun _ => rfl) rfl
        · apply hF DClink.DMethodFlowSeq.last (by simp [dclinks])
          apply hF DClink.DMethodFlow.embed (by simp [dclinks])
          exact hF DClink.DMethod.yieldOne (by simp [dclinks])
            (hF DClink.DMethod.ordinary (by simp [dclinks])
              (fun _ => hF DClink.intLit (by simp [dclinks]))) rfl rfl

theorem derivD_boundAlias : (DJudgeC dclinks).judge [] program_261_bound_block_alias_and_yield
    .int [("total", .int)] ctx0 .ivar0 boundAliasCtx .ivar0 := by
  intro F hF
  apply hF DClink.flow (by simp [dclinks])
  apply hF DClink.DFlow.sequence (by simp [dclinks])
  apply hF DClink.DFlowSeq.cons (by simp [dclinks])
  · apply hF DClink.DFlow.embed (by simp [dclinks])
    exact hF DClink.defBoundBlock (by simp [dclinks]) rfl rfl rfl rfl
      (fun code => derivD_boundAliasBody code F hF) rfl rfl rfl rfl rfl rfl rfl
      (by intro p h; cases h) (by intro d h; cases h) (by decide) (by decide)
  · apply hF DClink.DFlowSeq.cons (by simp [dclinks])
    · exact hF DClink.DFlow.vasgn (by simp [dclinks])
        (hF DClink.DFlow.intLit (by simp [dclinks]) _ 0) rfl rfl rfl rfl
    · apply hF DClink.DFlowSeq.cons (by simp [dclinks])
      · exact hF DClink.DFlow.callBoundBlock (by simp [dclinks]) (κ := boundAliasCtx) (decl := boundAliasDecl)
          (Γ := [("total", .int)]) (Γb := [("value", .int), ("total", .int)]) (I := .ivar0) (τ := .int) (br := .int)
          (facts := LocalFacts.unknown.afterEffect.write "total" false)
          (locals := []) (body := boundWriteBlock) (ps := [("value", .int)]) (names := ["total"])
          (fun code => derivD_boundAliasBody code F hF) rfl (by exact List.Mem.head _) rfl rfl rfl rfl rfl rfl rfl rfl
          (hF DClink.vasgn (by simp [dclinks])
            (hF DClink.prim (by simp [dclinks]) (hF DClink.var (by simp [dclinks]) rfl rfl)
              (hF DClink.DJudgeAll.cons (by simp [dclinks]) (hF DClink.var (by simp [dclinks]) rfl rfl)
                (hF DClink.DJudgeAll.nil (by simp [dclinks])) rfl)
              .intAdd rfl (by intro h; cases h)) rfl rfl rfl)
      · exact hF DClink.DFlowSeq.last (by simp [dclinks]) (hF DClink.DFlow.var (by simp [dclinks]) _ rfl rfl)

theorem safe_095_block_param_ampersand (hb : bootOkB = true) :
    StuckFree bootMachine program_095_block_param_ampersand :=
  dregistry_safe derivD_boundDirect (stateOk_boot hb)
theorem safe_261_bound_block_alias_and_yield (hb : bootOkB = true) :
    StuckFree bootMachine program_261_bound_block_alias_and_yield :=
  dregistry_safe derivD_boundAlias (stateOk_boot hb)

#print axioms safe_095_block_param_ampersand
#print axioms safe_261_bound_block_alias_and_yield
end Checker.Soundness.Typed
