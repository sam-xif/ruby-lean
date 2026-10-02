import Denote.Sem.Core.Boot
import Ratchet.Check.Check

/-! The former complete main world permits unsafe fresh-class callbacks. -/
namespace Ratchet.Denote.Typed
open RubyCore Ratchet.Denote

private def forgedHook (name : String) : Machine :=
  let k := classOf bootMachine.heap (.ref Boot.objectId)
  let md : MethodDef :=
    { params := [.req "arg"], body := .send (some .nil) "+" [.int 1] .none,
      owner := k, fromPrelude := true }
  { bootMachine with heap := defineMethod bootMachine.heap k name md }

private def legacyReadyB (m : Machine) : Bool :=
  mainReadyBaseB m &&
    decide ((m.heap.classPayload? Boot.objectId).bind (·.attached) = none) &&
    !(m.heap.get Boot.objectId).frozen && !m.currentFrame.libraryOrigin && mainOwnNamesB m.heap

private def legacyBootStateBaseB (m : Machine) : Bool :=
  saturatedB m.heap && coreOkB m.heap && frameOkB m &&
  topScopeB m && methodsExactB Ratchet.ctx0 m &&
  nameFreeB m && missFreeB m && selfLiveB m &&
  localsEmptyB m && queryOkB m && clsQueryOkB m
    && baseChainsOkB m && nilQueryOkB m
    && primitiveDispatchB m.heap (nameFreeN Ratchet.ctx0)
    && primitiveErrorsB m.heap && stringPayloadB m.heap
    && arrayPayloadB m.heap
    && hashPayloadB m.heap && legacyReadyB m
    && newDispatchB m.heap (classOf m.heap (.ref Boot.objectId))
    && globalConstsOkB Ratchet.ctx0.pos.globalConsts m.heap
    && moduleBaseB (nameFreeN Ratchet.ctx0) m.heap
    && Proof.namesOkB m.heap
    && m.currentFrame.localAlias.isNone
    && rootCleanB m
    && primitiveInitB m.heap

private def legacyBootStateB (m : Machine) : Bool :=
  legacyBootStateBaseB m && rootInitOkB Ratchet.ctx0.defs m.heap

#guard classHooksQuietB bootMachine.heap
#guard legacyBootStateB (forgedHook "const_added")
#guard legacyBootStateB (forgedHook "inherited")
#guard !bootStateB (forgedHook "const_added")
#guard !bootStateB (forgedHook "inherited")
#guard ["const_added", "inherited"].all fun name =>
  Semantics.typeStuck (Interp.run 100
    { forgedHook name with ctl := .eval (.class' "FreshHookWitness" none (.int 1)), kont := [] })
#guard Ratchet.validateDWith (fun _ => true) (.class' "FreshHookWitness" none (.int 1))
  (.classDecl "FreshHookWitness" none (.intLit 1))

-- Object's ordinary instance definitions cannot replace its native class callbacks.
#guard ["const_added", "inherited"].all fun name =>
  classHooksQuietB (defineMethod bootMachine.heap Boot.objectId name
    { params := [], body := .int 1, owner := Boot.objectId })
#guard Ratchet.validateD (.def' "const_added" [] (.int 1)) (.defDecl "const_added" [] .int (.intLit 1))
-- `inherited` is reserved at top level: class sites keep subclass creation's callback native.
#guard !Ratchet.validateD (.def' "inherited" [] (.int 1)) (.defDecl "inherited" [] .int (.intLit 1))
end Ratchet.Denote.Typed
