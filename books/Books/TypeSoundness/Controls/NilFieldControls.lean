import Books.TypeSoundness.Examples.NilFieldDerivations
import Books.TypeSoundness.Checker.Check.Check

/-! Unset reads require explicit allocation facts. Open annotations and uncalled bad
return annotations do not acquire nil facts from the absence of a listed field. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.NilFieldControls
open RubyCore Checker NilFieldProgram

def declHint (ret : Ty := .nilT) : Deriv :=
  .classDecl "Box" none (.defDecl "reveal" [] ret (.ivarRead "@secret" .nilT))
def newHint (cn : String := "Box") (I : Ty := fields "@secret") : Deriv :=
  .newInst cn [] (.inst cn I)
def useHint (cn : String := "Box") (I : Ty := fields "@secret") : Deriv :=
  .callMethodSig (newHint cn I) "reveal" [] .nilT

#guard validateD (program "@secret") (.seq [declHint, useHint])
#guard !validateD (declaration "@secret") (declHint .int)
#guard !validateD (program "@secret") (.seq [declHint .int, useHint])
#guard !validateD (program "@secret") (.seq [declHint, useHint "Box" .ivar0])
#guard !validateD (program "@secret")
  (.seq [declHint, useHint "Box" (.ivarCons "@secret" .int .ivar0)])

def openCtx : Ctx := instanceBodyCtx ctx0 ⟨"Box", "Box", "reveal", false⟩ .ivar0
#guard !(check fuelD [] (.var .ivar "@secret") (.ivarRead "@secret" .nilT) openCtx).isSome
#guard (check fuelD [] (.var .ivar "@secret") (.ivarRead "@secret" .any) openCtx).isSome
#guard nilFieldsB (nilFields ["@a", "@b", "@a"])
#guard !nilFieldsB (.ivarCons "@a" .nilT .int)
#guard !nilFieldsB (.ivarCons "@a" .any .ivar0)

def inherited : Checker.Expr := .seq [declaration "@secret",
  .class' "Child" (some (.const "Box")) (.def' "other" [] (.var .ivar "@other")),
  .send (some (.send (some (.const "Child")) "new" [] none)) "reveal" [] none]
def bothFields : Ty := nilFields ["@other", "@secret"]
#guard validateD inherited (.seq [declHint,
  .classDecl "Child" (some "Box") (.defDecl "other" [] .nilT (.ivarRead "@other" .nilT)),
  useHint "Child" bothFields])
#guard match Interp.run 200 (evalFrom bootMachine inherited) with
  | .value .nil _ => true
  | _ => false

-- A post-construction write cannot keep a receiver annotation claiming nil.
def writer : Checker.Expr := .class' "Box" none (.seq [
  .def' "reveal" [] (.var .ivar "@secret"),
  .def' "write" [] (.vasgn .ivar "@secret" (.int 1))])
#guard !validateD writer (.classDecl "Box" none (.seq [
  .defDecl "reveal" [] .nilT (.ivarRead "@secret" .nilT),
  .defDecl "write" [] .int (.ivarAsgn "@secret" (.intLit 1))]))

end Checker.Soundness.Typed.NilFieldControls
