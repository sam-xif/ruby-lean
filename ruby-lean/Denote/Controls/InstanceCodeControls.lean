import Denote.Rules.Instance.InstanceInstall
import Denote.Sem.Core.Boot

/-! Matching a method's parameters and body does not show that dispatch executes that
body. These are runtime metadata countermodels, not accepted source programs. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private def answerProgram : Ratchet.Expr := .send
  (some (.send (some (.send (some (.const "Point")) "new" [] none)) "answer" [] none))
  "+" [.int 1] none

private def pointWithAnswer : Option Machine :=
  match Interp.enterClassBody bootMachine "Point" false none (.def' "answer" [] (.int 1)) with
  | .next body => match Interp.run 100 body with
      | .value _ m => some m
      | _ => none
  | _ => none

private def matchesOldCode (md : MethodDef) : Bool :=
  md.params.isEmpty && !md.undefined && (match md.body with | .int 1 => true | _ => false)

#guard match pointWithAnswer with
  | some m => match Interp.run 100 (evalFrom m answerProgram) with
      | .value v _ => v.identEq (.int 2)
      | _ => false
  | none => false

-- The old ClassesOk code checks still match after changing only the builtin field.
-- The installed body says Integer; actual dispatch answers false, so adding one fails.
#guard match pointWithAnswer with
  | some m => match classNamed? m.heap "Point" with
      | some k => match Interp.methodOn m.heap k "answer" with
          | some (_, md) =>
              let fake := { md with builtin := some "Object#nil?" }
              let n := { m with heap := defineMethod m.heap k "answer" fake }
              matchesOldCode fake && !instanceMethodCodeB k "answer" fake &&
                instanceMethodCodeB k "answer" md &&
                Semantics.typeStuck (Interp.run 100 (evalFrom n answerProgram))
          | _ => false
      | none => false
  | none => false

-- Every metadata field is independently checked, while the old syntax checks still pass.
#guard match pointWithAnswer with
  | some m => match classNamed? m.heap "Point" with
      | some k => match Interp.methodOn m.heap k "answer" with
          | some (_, md) =>
              [{ md with owner := Boot.objectId }, { md with cref := [Boot.objectId] },
                { md with superName := some "other" }, { md with capturedFrame := some 0 },
                { md with declared := ["extra"] }, { md with fromPrelude := true },
                { md with visibility := .priv }].all
                  (fun bad => matchesOldCode bad && !instanceMethodCodeB k "answer" bad)
          | _ => false
      | none => false
  | none => false

-- The special initializer visibility is recorded rather than pretending it is public.
#guard match Interp.enterClassBody bootMachine "Point" false none (.def' "initialize" [] .nil) with
  | .next body => match Interp.run 100 body with
      | .value _ m => match classNamed? m.heap "Point" with
          | some k => (Interp.methodOn m.heap k "initialize").any
              (fun (_, md) => instanceMethodCodeB k "initialize" md && md.visibility == .priv)
          | none => false
      | _ => false
  | _ => false

end Ratchet.Denote.Typed
