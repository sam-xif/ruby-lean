import Denote.Typed.MethodDefine
import Denote.Typed.MethodCall
import Denote.Typed.MethodChecked
import Denote.Typed.Sequence

/-! Composed definition + call through the generic semantic rules. The single body artifact
is checked from annotations and reused. This does not claim `validateD` admission yet. -/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private def decl : Defn := ⟨"add", [.req "x", .req "y"],
  .send (some (.var .lvar "x")) "+" [.var .lvar "y"] none⟩
private def params : List SigParam := [("x", .int), ("y", .int)]
private def cert : Deriv := .defDecl "add" params .int
  (.prim (.var .lvar "x") "+" [.var .lvar "y"] .int .int)
private def checked : CheckedBody (topBodyCtx ctx0 decl) .ivar0 decl :=
  (checkMethodBody 100 (topBodyCtx ctx0 decl) .ivar0 decl cert).get (by decide)

private theorem body : SemSafeCtxA (topBodyCtx ctx0 decl) params .ivar0 decl.body .int
    (topBodyCtx ctx0 decl) params .ivar0 := checked_body_context checked

def addProgram (x y : Int) : Ratchet.Expr :=
  .seq [.def' decl.name decl.params decl.body, .send none "add" [.int x, .int y] none]

theorem add_program_sem (x y : Int) :
    SemSafeCtxA ctx0 [] .ivar0 (addProgram x y) .int (topDeclCtx ctx0 decl) [] .ivar0 := by
  have hd : SemSafeCtxA ctx0 [] .ivar0 (.def' decl.name decl.params decl.body) .sym
      (topDeclCtx ctx0 decl) [] .ivar0 :=
    SemSafeCtxA.defDecl rfl (by simp [params, FirstOrder, isAliasTy]) rfl body
      rfl rfl rfl rfl rfl rfl rfl (by simp) (by simp [ctx0, Ctx.defs]) (by decide) (by decide)
  have hc : SemSafeCtxA (topDeclCtx ctx0 decl) [] .ivar0
      (.send none decl.name [.int x, .int y] none) .int (topDeclCtx ctx0 decl) [] .ivar0 :=
    SemSafeCtxA.callSig rfl (by simp [params, FirstOrder, isAliasTy]) rfl body
      (.cons .intLit (.cons .intLit .nil rfl) rfl)
      (by change decl ∈ [decl]; simp) rfl rfl rfl rfl rfl rfl rfl (by simp)
  exact SemSafeCtxA.sequence (.cons hd (.last hc))

theorem add_program_safe (hb : bootOkB = true) (x y : Int) :
    StuckFree bootMachine (addProgram x y) := (add_program_sem x y).closed (stateOk_boot hb)

-- This remaining gate must flip only when the definition and call checker rules land.
#guard !validateD (addProgram 1 2) (.seq [cert, .callSig "add" [.intLit 1, .intLit 2] .int])
#print axioms add_program_sem
#print axioms add_program_safe
end Ratchet.Denote.Typed
