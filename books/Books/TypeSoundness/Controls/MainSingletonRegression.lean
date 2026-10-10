import Books.TypeSoundness.Checker.Check.Check
import Books.TypeSoundness.Conformance.Core.Trans

/-! Main's native singleton inspect is distinct from Object#inspect. A top-level
Object definition does not replace it, so its annotation cannot type the call. -/
namespace Checker.Soundness
open RubyCore

private def mainInspectProgram : Checker.Expr := .seq [
  .def' "inspect" [] (.int 1),
  .send (some (.send none "inspect" [] none)) "+" [.int 1] none]

private def mainInspectCertificate : Checker.Deriv := .seq [
  .defDecl "inspect" [] .int (.intLit 1),
  .prim (.callSig "inspect" [] .int) "+" [.intLit 1] .int .int]

#guard !Checker.validateD mainInspectProgram mainInspectCertificate
#guard Semantics.typeStuck (Semantics.run 1000 (toRuby mainInspectProgram))

end Checker.Soundness
