import Denote.Sem.ClassConstants
import Denote.Typed.ClassReturn
import Denote.Typed.ClassEntry
import Denote.Sanity

/-! Actual class scope and return controls, not acceptance of the still-gated class rung. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem class_entry_scope {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {name : String} {body : Ratchet.Expr} (hm : StateOk κ Γ I m)
    (hr : κ.scope.runtimeMain = true)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false) :
    ∃ n, Interp.stepFn (evalFrom m (.class' name none body)) = .next n ∧
      FrameInRange n ∧ EnvOk [] n ∧ SelfSpineOk .ivar0 n ∧
      FrameOk none n ∧ BlockTyOk none n ∧ SelfTyOk (some (.clsOf name)) n ∧
      SelfLive n ∧ RootUncaptured n ∧ ConstScopeOk n := by
  obtain ⟨e, he, hstep⟩ := stepFn_class_fresh hm hr hn hne
  have hmain := hm.runtime hr
  refine ⟨_, hstep, FreshClass.frame_in_range, FreshClass.env_empty, FreshClass.spine_empty,
    FreshClass.frame_ok, FreshClass.block_none, FreshClass.self_type hmain.classLive,
    FreshClass.self_live, FreshClass.uncaptured, ?_⟩
  exact FreshClass.const_scope hm.core.classReady.chains hm.sat hmain.classLive
    hmain.cref hmain.owner hm.constScope

#guard match Interp.enterClassBody (bootMachine.setLocal "x" (.int 7)) "Point" false none .nil with
  | .next n => (n.getLocal "x").identEq .nil && (ivarOf n.heap n.currentFrame.self "@x").identEq .nil &&
      isClassRefNamed n.heap n.currentFrame.self "Point" &&
      (constResolveAt n "Point").any (fun v => isClassRefNamed n.heap v "Point") &&
      (constResolveAt n "Integer").any (·.identEq (.ref Boot.integerId)) &&
      (constResolveAt n "Missing").isNone
  | _ => false

-- The body can use the same local name without changing the caller's binding.
#guard match Interp.enterClassBody (bootMachine.setLocal "x" (.int 7)) "Point" false none
    (.vasgn .lvar "x" (.int 9)) with
  | .next n => match Interp.run 100 n with
      | .value v n' => v.identEq (.int 9) && (n'.getLocal "x").identEq (.int 7) &&
          n'.stack == bootMachine.stack
      | _ => false
  | _ => false

-- Once a class owns a shadowing constant, empty-scope transport must not apply.
#guard match Interp.enterClassBody bootMachine "Point" false none .nil with
  | .next n =>
      let n' := { n with heap := constSetIn n.heap n.currentFrame.defmod "Integer" (.int 0) }
      (constResolveAt n' "Integer").any (·.identEq (.int 0)) &&
        (constLookup n'.heap "Integer").any (fun v => !v.identEq (.int 0))
  | _ => false

#print axioms class_entry_scope
end Ratchet.Denote.Typed
