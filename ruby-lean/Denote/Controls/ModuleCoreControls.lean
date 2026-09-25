import Denote.Rules.Module.ModuleEntry
import Denote.Sem.Module.ModuleHeader
import Denote.Sem.Core.Boot

/-! Core and old-table preservation at real module entry, plus the distinction between
the module's lexical constant scope and its singleton-method fallback. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.ModuleCoreControls
open RubyCore Ratchet Ratchet.Denote

private def echo : Defn := ⟨"echo", [], .str "old"⟩
private def token : Defn := ⟨"token", [], .int 9⟩
private def previous : CTable := [
  { moduleHeader "Earlier" with smethods := [token] },
  { classHeader "Depot" with smethods := [echo] }]
private def setup : Ratchet.Expr := .seq [
  .class' "Depot" none (.defs .self' echo.name echo.params echo.body),
  .module' "Earlier" (.defs .self' token.name token.params token.body)]

#guard moduleHeaderFrameB previous "Later"
#guard match Interp.run 200 (evalFrom bootMachine setup) with
  | .value _ m => coreOkB m.heap && classChainsB previous m.heap &&
    match Interp.stepFn (evalFrom m (.module' "Later" (.const "String"))) with
    | .next n => coreOkB n.heap &&
        classChainsB (moduleHeader "Later" :: previous) n.heap &&
        classOwnNamesB previous n.heap &&
        match Interp.run 100 n with
        | .value (.ref k) finished => k == Boot.stringId &&
          match Interp.run 100 (evalFrom finished (.array [
              .send (some (.const "Depot")) "echo" [] none,
              .send (some (.const "Earlier")) "token" [] none])) with
          | .value v result => match arrElems? result.heap v with
            | some xs => xs.size == 2 && match xs[0]?, xs[1]? with
              | some s, some (Value.int 9) => Builtins.strPayload? result.heap s == some "old"
              | _, _ => false
            | none => false
          | _ => false
        | _ => false
    | _ => false
  | _ => false

-- Core-only countermodel, not a full-StateOk or reachable-program witness. Bypassing
-- Module in Class's ancestry hides its constant from Object's retained metaclass fallback.
#guard match bootMachine.heap.classPayload? Boot.classId with
  | some cc =>
    let h := constSetIn (bootMachine.heap.setClassPayload Boot.classId
      { cc with superclass := some Boot.objectId }) Boot.moduleId "Hidden" (.int 99)
    coreOkB h && saturatedB h && !constFallbackB h Boot.moduleId &&
      match Interp.stepFn (evalFrom { bootMachine with heap := h }
          (.module' "Scope" (.defs .self' "read" [] (.const "Hidden")))) with
      | .next n => coreOkB n.heap && (constResolveAt n "Hidden").isNone &&
          !constFallbackB n.heap (classOf n.heap n.currentFrame.self) &&
          match Interp.run 100 n with
          | .value _ finished => match Interp.run 100
              (evalFrom finished (.send (some (.const "Scope")) "read" [] none)) with
            | .value (.int 99) _ => true
            | _ => false
          | _ => false
      | _ => false
  | none => false

end Ratchet.Denote.Typed.ModuleCoreControls
