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
      !moduleBaseB (nameFreeN ctx0) h &&
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

theorem hidden_module_not_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {name : String} {v : Value} (hg : constLookup m.heap name = none)
    (hf : constLookupFrom m.heap Boot.moduleId name = some v) : ¬ StateOk κ Γ I m := by
  intro hm
  have hh := hm.moduleBase.constants name hg
  rw [hf] at hh; cases hh

theorem unreserved_module_not_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {name : String} {owner : ObjId} {md : MethodDef}
    (hn : name ∈ shadowableNames) (hf : nameFreeN κ name = true)
    (hl : Interp.methodOn m.heap Boot.moduleId name = some (owner, md))
    (hb : md.builtin = none) (hu : md.undefined = false) : ¬ StateOk κ Γ I m := by
  intro hm
  have hh := hm.moduleBase.names name hn owner md hl
  simp only [hb, Option.isSome_none, hu, hf, Bool.false_eq_true, Bool.true_eq_false, or_self] at hh

private def hidden : MethodDef :=
  { owner := Boot.moduleId, params := [.req "unexpected"], body := .nil, fromPrelude := true }

#guard moduleBaseB (nameFreeN ctx0) bootMachine.heap
#guard let h := defineMethod bootMachine.heap Boot.moduleId "lambda" hidden
  !moduleBaseB (nameFreeN ctx0) h && moduleBaseB (nameFreeN (reserveNameCtx ctx0 "lambda")) h
#guard !moduleBaseB (nameFreeN ctx0) (defineMethod bootMachine.heap Boot.moduleId "method_added" hidden)

#guard match Interp.run 100 (evalFrom bootMachine (.module' "Parentless" .nil)) with
  | .value _ m => moduleBaseB (nameFreeN ctx0) m.heap &&
    match classNamed? m.heap "Parentless" with
    | some k => classFrontB m.heap k && definitionHookQuietB m.heap k &&
      namesAtB (nameFreeN ctx0) m.heap k &&
      namesAtB (nameFreeN ctx0) m.heap (classOf m.heap (.ref k)) &&
      constFallbackB m.heap (classOf m.heap (.ref k)) &&
      classFrontB m.heap (classOf m.heap (.ref k)) && metaReadyB m.heap k
    | none => false
  | _ => false

#print axioms hidden_module_not_state
#print axioms unreserved_module_not_state
end Ratchet.Denote.Typed.ModuleCoreControls
