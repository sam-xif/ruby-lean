import Denote.Rules.Class.ClassEntry
import Denote.Sem.Class.ClassBases
import Denote.Sem.Core.Boot

/-! The metaclass must not be one of the builtin value bases. These are heap-invariant
countermodels, not reachable Ruby programs or a new class-admission route. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem class_entry_bases {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {name : String} {body : Ratchet.Expr} (hm : StateOk κ Γ I m)
    (hr : κ.scope.runtimeMain = true)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false) :
    ∃ n, Interp.stepFn (evalFrom m (.class' name none body)) = .next n ∧ BaseChainsOk κ n := by
  obtain ⟨e, he, hstep⟩ := stepFn_class_fresh hm hr hn hne
  exact ⟨_, hstep, FreshClass.baseChains hm.core.classReady hm.sat (hm.runtime hr).classLive
    hn he rfl hm.baseChains⟩

#guard match Interp.enterClassBody bootMachine "Point" false none .nil with
  | .next n => baseChainsOkB n && classReadyB n.heap
  | _ => false

private def metaAsFloat : Machine :=
  let h := bootMachine.heap.set Boot.objectId
    { bootMachine.heap.get Boot.objectId with eigen := some Boot.floatId }
  let h := defineMethod h Boot.floatId "==="
    { owner := Boot.floatId, params := [], body := .nil, builtin := some "Module#===" }
  let h := defineMethod h Boot.floatId "to_s"
    { owner := Boot.floatId, params := [], body := .nil, builtin := some "Module#to_s" }
  { bootMachine with heap := h }

-- Before strengthening ClassReady, the complete boot conjunction passed this heap.
-- Keep the old readiness components and every other check explicit in the control.
#guard
  let m := metaAsFloat
  Proof.chainsInB m.heap && (ancestors m.heap Boot.floatId).contains Boot.basicObjectId &&
    (ancestors m.heap Boot.classId).contains Boot.basicObjectId && coreDataB m.heap &&
    saturatedB m.heap && frameOkB m && topScopeB m && methodsExactB ctx0 m &&
    nameFreeB m && missFreeB m && selfLiveB m && localsEmptyB m && queryOkB m && clsQueryOkB m &&
    baseChainsOkB m && nilQueryOkB m && primitiveDispatchB m.heap (nameFreeN ctx0) &&
    primitiveErrorsB m.heap && stringPayloadB m.heap && arrayPayloadB m.heap &&
    hashPayloadB m.heap && mainReadyB m

#guard !eigenSeparateB metaAsFloat.heap
#guard !coreOkB metaAsFloat.heap

#guard match Interp.enterClassBody metaAsFloat "Point" false none .nil with
  | .next n => !baseChainsOkB n &&
      (ancestors n.heap (metaAsFloat.heap.objs.size + 1)).contains Boot.floatId
  | _ => false

-- Registration can turn a dangling constant into an alias to the new class. Thus reverse
-- name transport needs an old-id bound; this alias still cannot enter an old base's chain.
#guard
  let m := { bootMachine with
    heap := constSetIn bootMachine.heap Boot.objectId "Future" (.ref bootMachine.heap.objs.size) }
  (classNamed? m.heap "Future").isNone &&
    match Interp.enterClassBody m "Point" false none .nil with
    | .next n => classNamed? n.heap "Future" == some m.heap.objs.size && baseChainsOkB n
    | _ => false

#print axioms class_entry_bases
end Ratchet.Denote.Typed
