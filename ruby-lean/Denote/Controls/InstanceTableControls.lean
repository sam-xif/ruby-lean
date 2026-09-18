import Denote.Rules.Instance.InstancePublish
import Denote.Sem.Core.Boot

/-! Class-table publication controls: unchanged owners may share method names, but aliases
of a written owner cannot keep stale body records. These are runtime conformance probes. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private def twoClasses : Ratchet.Expr := .seq [
  .class' "Point" none (.def' "answer" [] (.int 1)),
  .class' "Other" none (.def' "answer" [] (.int 2))]

private def callAnswer (cn : String) : Ratchet.Expr :=
  .send (some (.send (some (.const cn)) "new" [] none)) "answer" [] none

private def answerRow (m : Machine) (cn : String) (expected : Int) : Bool :=
  match classNamed? m.heap cn with
  | none => false
  | some k => ((m.heap.classPayload? k).bind
      (fun cp => (cp.methods.find? (·.1 == "answer")).map (·.2))).any fun md =>
        md.params.isEmpty && !md.undefined && instanceMethodCodeB k "answer" md &&
          (match md.body with | .int i => i == expected | _ => false)

-- Updating Point's answer leaves Other's same-name method and actual call unchanged.
#guard match Interp.run 200 (evalFrom bootMachine twoClasses) with
  | .value _ m => match classNamed? m.heap "Point", classNamed? m.heap "Other" with
      | some k, some other =>
          let n := { m with
            heap := defineMethod m.heap k "answer"
              { owner := k, params := [], body := .fls, cref := [k, Boot.objectId] } }
          k != other && answerRow m "Other" 2 && answerRow n "Other" 2 &&
            match Interp.run 100 (evalFrom n (callAnswer "Other")) with
            | .value v _ => v.identEq (.int 2)
            | _ => false
      | _, _ => false
  | _ => false

-- A different class *name* is not sufficient: Alias and Point share the written owner.
#guard match Interp.run 200 (evalFrom bootMachine twoClasses) with
  | .value _ m => match classNamed? m.heap "Point" with
      | some k =>
          let m := { m with heap := constSetIn m.heap Boot.objectId "Alias" (.ref k) }
          let n := { m with
            heap := defineMethod m.heap k "answer"
              { owner := k, params := [], body := .fls, cref := [k, Boot.objectId] } }
          classNamed? m.heap "Alias" == some k && answerRow m "Alias" 1 &&
            !answerRow n "Alias" 1 &&
            Semantics.typeStuck (Interp.run 100 (evalFrom n
              (.send (some (callAnswer "Alias")) "+" [.int 1] none)))
      | none => false
  | _ => false

-- Publication adds exactly the executed member; the remaining source body is not scanned.
private def pointHeader : Cls := ⟨"Point", none, [], [], false, [], [], []⟩
private def firstMember : Defn := ⟨"initialize", [], .nil⟩
private def secondMember : Defn := ⟨"getX", [], .int 1⟩
#guard (classWithMethod pointHeader firstMember).methods.map (·.name) == ["initialize"]
#guard (classWithMethod (classWithMethod pointHeader firstMember) secondMember).methods.map
  (·.name) == ["getX", "initialize"]

end Ratchet.Denote.Typed
