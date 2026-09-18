import Denote.Rules.Method.MethodDispatch

/-! Real `def` → lookup → body → caller controls. These test the interpreter path;
they are not method admissions by the checker, whose body-proof obligation remains.
-/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

-- Identical parameter/body fields do not suffice to describe callable user code.
private def codeProbe : MethodDef :=
  { params := [.req "x"], body := .var .lvar "x", owner := Boot.objectId, cref := [Boot.objectId] }
example : TopMethodCode codeProbe := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
example : ¬ TopMethodCode { codeProbe with builtin := some "Integer#+" } := by
  intro h; cases h.builtin
example : ¬ TopMethodCode { codeProbe with capturedFrame := some 0 } := by
  intro h; cases h.captured
example : ¬ TopMethodCode { codeProbe with declared := ["x"] } := by
  intro h; cases h.declared
example : ¬ TopMethodCode { codeProbe with superName := some "other" } := by
  intro h; cases h.superName
example : ¬ TopMethodCode { codeProbe with fromPrelude := true } := by
  intro h; cases h.fromPrelude
example : ¬ TopMethodCode { codeProbe with cref := [] } := by
  intro h; cases h.cref

private def runControl (p : Ratchet.Expr) : Interp.RunResult :=
  Interp.run 200 (Machine.init (toRuby p))

private def identityDef (name : String) : Ratchet.Expr :=
  .def' name [.req "x"] (.var .lvar "x")

-- Found user entries shadow even reflective names, and the call really runs the body.
#guard (["identity", "send", "public_send", "__send__"] : List String).all fun name =>
  match runControl (.seq [identityDef name, .send none name [.int 7] none]) with
  | .value (.int 7) m => m.stack == [0]
  | _ => false

-- Two arguments, primitive dispatch inside the body, and restoration of caller locals.
#guard match runControl (.seq [
    .vasgn .lvar "x" (.int 90),
    .def' "add" [.req "x", .req "y"]
      (.send (some (.var .lvar "x")) "+" [.var .lvar "y"] none),
    .send none "add" [.int 1, .int 2] none]) with
  | .value (.int 3) m => Value.identEq (m.getLocal "x") (.int 90) && m.stack == [0]
  | _ => false

-- A successful call is not evidence for the broader nilable-Integer annotation.
-- DerivControls rejects this body at that annotation, even with only the first call.
private def annotationProbe (arg : Ratchet.Expr) : Ratchet.Expr := .seq [
  .def' "annotation_probe" [.req "x"]
    (.send (some (.var .lvar "x")) "+" [.int 1] none),
  .send none "annotation_probe" [arg] none]
#guard match runControl (annotationProbe (.int 1)) with
  | .value (.int 2) _ => true
  | _ => false
#guard Semantics.typeStuck (runControl (annotationProbe .nil))

-- Installation really makes a top-level definition private; literal self is a
-- separate Ruby call site, so use a local receiver to test the explicit-site failure.
#guard match runControl (.seq [identityDef "identity", .vasgn .lvar "receiver" .self',
    .send (some (.var .lvar "receiver")) "identity" [.int 7] none]) with
  | .uncaught exc m => Semantics.isTypeError m.heap exc
  | _ => false

-- A real singleton hook runs; omitting it would change this result from a Symbol to nil.
#guard match runControl (.seq [
    .vasgn .gvar "$hook" .nil,
    .defs (.const "Object") "method_added" [.req "name"]
      (.vasgn .gvar "$hook" (.var .lvar "name")),
    identityDef "identity", .var .gvar "$hook"]) with
  | .value (.sym "identity") _ => true
  | _ => false

-- An Object *instance* hook is shadowed by CRuby's Module no-op and must not run.
#guard match runControl (.seq [
    .vasgn .gvar "$hook" .nil,
    .def' "method_added" [.req "name"] (.vasgn .gvar "$hook" (.var .lvar "name")),
    identityDef "identity", .var .gvar "$hook"]) with
  | .value .nil _ => true
  | _ => false

end Ratchet.Denote.Typed
