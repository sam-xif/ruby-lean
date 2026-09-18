import Denote.Rules.Subclass.SubclassEntry
import Denote.Sem.Core.Boot

/-! A retained instance chain does not constrain subclass-body self. The injected method
below probes old site/name/heap facts, not full old StateOk or an accepted unsafe program. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.SubclassNameControls
open RubyCore Ratchet Ratchet.Denote

private def setup : Ratchet.Expr := .class' "ScopeBase" none .nil
private def body : Ratchet.Expr := .send none "lambda" [] (some (.block [] [] (.int 1)))
private def hidden (ep : ObjId) : MethodDef :=
  { owner := ep, params := [.req "unexpected"], body := .nil, fromPrelude := true }

#guard match Interp.run 100 (evalFrom bootMachine setup) with
  | .value _ m => match classNamed? m.heap "ScopeBase" with
    | some parent => match Interp.enterClassBody m "ScopeChild" false (some parent) (toRuby body) with
      | .next n => nameFreeB n && match Interp.run 100 n with
        | .value v result => isAName result.heap v "Proc"
        | _ => false
      | _ => false
    | none => false
  | _ => false

#guard match Interp.run 100 (evalFrom bootMachine setup) with
  | .value _ m => match classNamed? m.heap "ScopeBase" with
    | some parent => match (m.heap.get parent).eigen with
      | some ep =>
        let h := defineMethod m.heap ep "lambda" (hidden ep)
        let n := { m with heap := h }
        nameFreeB n && methodsExactB ctx0 n && coreOkB h && saturatedB h &&
          classFrontB h parent && definitionHookQuietB h parent && metaReadyB h parent &&
          classChainsB [classHeader "ScopeBase"] h && classOwnNamesB [classHeader "ScopeBase"] h &&
          namesAtB (nameFreeN ctx0) h parent &&
          !namesAtB (nameFreeN ctx0) h (classOf h (.ref parent)) &&
          namesAtB (nameFreeN (reserveNameCtx ctx0 "lambda")) h (classOf h (.ref parent)) &&
          match Interp.enterClassBody n "ScopeChild" false (some parent) (toRuby body) with
          | .next entry => !nameFreeB entry && match Interp.run 100 entry with
            | .uncaught exc result => isAName result.heap exc "ArgumentError"
            | _ => false
          | _ => false
      | none => false
    | none => false
  | _ => false

-- The requirement is site-local, not heap-global: the real shim's T.proc stays legal.
#guard match classNamed? bootMachine.heap "T" with
  | some k => !namesAtB (nameFreeN ctx0) bootMachine.heap (classOf bootMachine.heap (.ref k))
  | none => false

theorem unreserved_metaclass_not_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {c : Cls} {k owner : ObjId} {name : String} {md : MethodDef}
    (hc : c ∈ κ.classes) (hk : classNamed? m.heap c.name = some k)
    (hn : name ∈ shadowableNames) (hf : nameFreeN κ name = true)
    (hl : Interp.methodOn m.heap (classOf m.heap (.ref k)) name = some (owner, md))
    (hb : md.builtin = none) (hu : md.undefined = false) : ¬ StateOk κ Γ I m := by
  intro hm
  have h := (hm.classSites.at_class hc hk).classNames name hn owner md hl
  simp only [hb, Option.isSome_none, hu, hf, Bool.false_eq_true, Bool.true_eq_false, or_self] at h

#print axioms unreserved_metaclass_not_state
end Ratchet.Denote.Typed.SubclassNameControls
