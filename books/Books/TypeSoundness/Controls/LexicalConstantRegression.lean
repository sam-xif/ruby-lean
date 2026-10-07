import Books.TypeSoundness.Conformance.Core.Boot

/-! Lexical lookup must not follow a method's distinct definee. Modules retain
Object fallback even when Object is absent from their lexical scope/ancestors. -/
set_option autoImplicit false
namespace Checker.Soundness.LexicalConstantRegression
open RubyCore

private def poisoned : Machine :=
  { bootMachine with
    heap := constSetIn bootMachine.heap Boot.moduleId "LexicalOnlyProbe" (.int 99)
    frames := #[{ self := .ref Boot.integerId, defmod := Boot.moduleId, cref := [Boot.integerId], kind := .method }] }

#guard (constLookupFrom poisoned.heap Boot.moduleId "LexicalOnlyProbe").any (·.identEq (.int 99))
#guard (constResolveAt poisoned "LexicalOnlyProbe").isNone

private def moduleScope : Machine :=
  { bootMachine with
    heap := constSetIn bootMachine.heap Boot.objectId "LexicalOnlyProbe" (.int 7)
    frames := #[{ self := .ref Boot.kernelId, defmod := Boot.kernelId, cref := [Boot.kernelId], kind := .classBody }] }

#guard (constLookupFrom moduleScope.heap Boot.kernelId "LexicalOnlyProbe").isNone
#guard (constResolveAt moduleScope "LexicalOnlyProbe").any (·.identEq (.int 7))

end Checker.Soundness.LexicalConstantRegression
