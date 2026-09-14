import Denote.Sem.ClassDeclared
import Denote.Typed.ClassEntry
import Denote.Sanity

/-! Preserve old declarations, without pre-installing or certifying the new class's body.
In particular, an empty own-method table says nothing about inherited initialize. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem class_entry_declared {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {name : String} {body : Ratchet.Expr} (hm : StateOk κ Γ I m)
    (hr : κ.scope.runtimeMain = true)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false) :
    ∃ n, Interp.stepFn (evalFrom m (.class' name none body)) = .next n ∧ DeclClassOk κ n := by
  obtain ⟨e, he, hstep⟩ := stepFn_class_fresh hm hr hn hne
  exact ⟨_, hstep, FreshClass.declared hm.core.classReady.chains hm.sat
    (hm.runtime hr).classLive hn rfl hm.classes hm.declCls⟩

private def emptyClassFacts (m : Machine) (name : String) : Bool :=
  match classNamed? m.heap name with
  | none => false
  | some k =>
    let site := classOf m.heap (.ref k)
    (m.heap.classPayload? k).any (fun cp => !cp.isModule && cp.methods.isEmpty) &&
      k != Boot.classId && k != Boot.moduleId &&
      ((ancestors m.heap k).map (className m.heap) == [name, "Object", "Kernel", "BasicObject"]) &&
      (Interp.userInit? m.heap k).isNone &&
      match Interp.methodOn m.heap site "new" with
      | some (owner, md) => md.builtin == some "Class#new" && !md.undefined &&
          md.visibility == .pub && !md.fromPrelude &&
          (Interp.crubyShadow m.heap ((ancestors m.heap site).takeWhile (· != owner)) "new").isNone
      | none => (Interp.methodOn m.heap site "method_missing").all (fun (_, md) => md.builtin.isSome)

private def newAfterBody (body : Machine) : Interp.RunResult :=
  match Interp.run 100 body with
  | .value _ m => Interp.run 100 (evalFrom m (.send (some (.const "Point")) "new" [] none))
  | r => r

-- Existing-class case: create and finish Older, then enter Point. Old constructor
-- metadata, ancestry, and the absence of an initializer remain unchanged.
#guard match Interp.enterClassBody bootMachine "Older" false none .nil with
  | .next body => match Interp.run 100 body with
      | .value _ m => emptyClassFacts m "Older" &&
          match Interp.enterClassBody m "Point" false none .nil with
          | .next n => emptyClassFacts n "Older" && emptyClassFacts n "Point" &&
              classNamed? n.heap "Older" == classNamed? m.heap "Older" &&
              match newAfterBody n with
              | .value v result => isAName result.heap v "Point"
              | _ => false
          | _ => false
      | _ => false
  | _ => false

-- Refute extending the transport to a newly advertised no-initializer class. Its empty
-- own table does not erase Object#initialize; the constructor really finds the inherited body.
#guard
  let m := { bootMachine with
    heap := defineMethod bootMachine.heap Boot.objectId "initialize"
      { owner := Boot.objectId, params := [.req "x"], body := .var .lvar "x" } }
  (classNamed? m.heap "Point").isNone &&
    match Interp.enterClassBody m "Point" false none .nil with
    | .next n =>
        (n.heap.classPayload? n.currentFrame.defmod).any (·.methods.isEmpty) &&
        (Interp.userInit? n.heap n.currentFrame.defmod).any
          (fun md => md.owner == Boot.objectId && md.params.length == 1) &&
        !emptyClassFacts n "Point" &&
        match newAfterBody n with
        | .uncaught exc result => isAName result.heap exc "ArgumentError"
        | _ => false
    | _ => false

#print axioms class_entry_declared
end Ratchet.Denote.Typed
