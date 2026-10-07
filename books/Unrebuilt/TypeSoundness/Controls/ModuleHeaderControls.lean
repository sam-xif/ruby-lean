import Books.TypeSoundness.Conformance.Module.ModuleHeader
import Books.TypeSoundness.Rules.Module.ModuleEntry
import Books.TypeSoundness.Conformance.Core.Boot

/-! Module header conformance uses its real kind and own chain. This is metadata
publication, not full module-body admission or an allocator permission. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.ModuleHeaderControls
open RubyCore Checker Checker.Soundness

theorem module_header {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {name : String} {body : Checker.Expr} (hm : StateOk κ Γ I m)
    (hr : κ.scope.runtimeMain = true) (ht : moduleHeaderFrameB κ.classes name = true)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false) :
    ∃ n, Interp.stepFn (evalFrom m (.module' name body)) = .next n ∧
      DeclClassOk (moduleHeaderCtx κ name) n ∧ ClassChains (moduleHeader name :: κ.classes) n.heap :=
  ⟨_, stepFn_module_fresh hm hr hn hne,
    FreshModule.declared_header hm.core.classReady hm.sat (hm.runtime hr).classLive hn
      hm.classes hm.declCls (moduleHeaderFrameB_sound ht),
    FreshModule.classChains_header hm.core.classReady hm.sat (hm.runtime hr).classLive hn
      hm.classes hm.classChains (moduleHeaderFrameB_sound ht)⟩

theorem class_not_module_header {κ : Ctx} {m : Machine} {name : String} {k : ObjId}
    (hn : classNamed? m.heap name = some k)
    (hp : (m.heap.classPayload? k).map (·.isModule) = some false) :
    ¬ DeclClassOk (moduleHeaderCtx κ name) m := by
  intro hm
  have h := (hm (moduleHeader name) (by simp [moduleHeaderCtx, Ctx.classes]) k hn).2.2.2.1
  rw [hp] at h
  cases h

#guard match Interp.run 100 (evalFrom bootMachine (.module' "Marker" .nil)) with
  | .value _ m =>
    classChainsB [moduleHeader "Marker"] m.heap && !classChainsB [classHeader "Marker"] m.heap &&
      (instClsGet? [moduleHeader "Marker"] "Marker").isNone &&
      Semantics.typeStuck (Interp.run 100
        (evalFrom m (.send (some (.const "Marker")) "new" [] none)))
  | _ => false

#guard match Interp.run 100 (evalFrom bootMachine (.class' "Capsule" none .nil)) with
  | .value _ m =>
    classChainsB [classHeader "Capsule"] m.heap && !classChainsB [moduleHeader "Capsule"] m.heap
  | _ => false

#print axioms module_header
#print axioms class_not_module_header
end Checker.Soundness.Typed.ModuleHeaderControls
