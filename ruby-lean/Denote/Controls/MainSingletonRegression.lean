import Ratchet.Check.Check
import Denote.Sem.Core.Trans

/-! Main's native singleton inspect is distinct from Object#inspect. A top-level
Object definition does not replace it, so its annotation cannot type the call. -/
namespace Ratchet.Denote
open RubyCore

private def mainInspectProgram : Ratchet.Expr := .seq [
  .def' "inspect" [] (.int 1),
  .send (some (.send none "inspect" [] none)) "+" [.int 1] none]

private def mainInspectCertificate : Ratchet.Deriv := .seq [
  .defDecl "inspect" [] .int (.intLit 1),
  .prim (.callSig "inspect" [] .int) "+" [.intLit 1] .int .int]

#guard !Ratchet.validateD mainInspectProgram mainInspectCertificate
#guard Semantics.typeStuck (Semantics.run 1000 (toRuby mainInspectProgram))

end Ratchet.Denote
