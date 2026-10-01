import Denote.Rules.Method.MethodDefine
import Denote.Sem.Core.Boot
import Ratchet.Check.Check
/-! Open call-conformance countermodel: a native method in main's singleton
prefix wins ahead of an annotation-checked Object definition. callSig stays gated. -/
namespace Ratchet.Denote.Typed
open RubyCore Ratchet.Denote
private def shadowMain : Machine :=
  let k := classOf bootMachine.heap (.ref Boot.mainId)
  let md : MethodDef :=
    { params := [], body := .nil, owner := k, builtin := some "Module#method_added" }
  { bootMachine with heap := defineMethod bootMachine.heap k "bump" md }
#guard bootStateB shadowMain
#guard Semantics.typeStuck (Interp.run 100
  { shadowMain with ctl := .eval (.seq [.def' "bump" [] (.int 1),
      .send none "bump" [] .none]), kont := [] })
#guard Ratchet.validateDWith (fun _ => true)
  (.seq [.def' "bump" [] (.int 1), .send none "bump" [] none])
  (.seq [.defDecl "bump" [] .int (.intLit 1), .callSig "bump" [] .int])
end Ratchet.Denote.Typed
