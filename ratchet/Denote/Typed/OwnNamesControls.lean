import Denote.Sem.OwnNamesWrite
import Denote.Sem.OwnLookup
import Denote.Sem.ClassOwnNames
import Denote.Sanity

/-! Owner bounds are not body proofs. These independent inheritance/history/alias controls
exercise absence and publication only; no program gains acceptance from a selector bound. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.OwnNamesControls
open RubyCore Ratchet Ratchet.Denote

private def a : Defn := ⟨"alpha", [], .int 1⟩
private def b : Defn := ⟨"beta", [], .fls⟩
private def depot : Cls := classHeader "Depot"
private def satellite : Cls := { classHeader "Satellite" with super? := some "Depot" }
private def chainCtx : Ctx := { ctx0 with pos := { ctx0.pos with classes := [satellite, depot] } }

-- Ancestors and descendants are distinct in either direction; unknown ancestry declines.
#guard memberOwnersB chainCtx depot
#guard memberOwnersB chainCtx satellite
#guard !memberOwnersB { chainCtx with pos := { chainCtx.pos with classes :=
  [{ depot with super? := some "Missing" }, { satellite with super? := some "Missing" }] } } depot

-- A newer snapshot may have been based on an older header. Preserve both selectors.
private def history : CTable := [classWithMethod depot b, classWithMethod depot a, depot]
#guard (ownNames history "Depot").contains "alpha"
#guard (ownNames history "Depot").contains "beta"
#guard (ownNames history "Satellite").isEmpty

private def code (k : ObjId) (d : Defn) : MethodDef :=
  { owner := k, params := toRubyParams d.params, body := toRuby d.body, cref := [k, Boot.objectId] }

-- Real inheritance: the empty child does not define alpha. A hidden child override fails
-- the bound; publishing its own selector restores only the bound, not annotation typing.
#guard match Interp.run 100 (evalFrom bootMachine (.seq [
    .class' "Depot" none (.def' a.name a.params a.body),
    .class' "Satellite" (some (.const "Depot")) .nil])) with
  | .value _ m => match classNamed? m.heap "Satellite" with
    | some k =>
      let C := [satellite, classWithMethod depot a]
      let h := defineMethod m.heap k a.name (code k { a with body := .fls })
      classOwnNamesB C m.heap && !classOwnNamesB C h &&
        classOwnNamesB (classWithMethod satellite { a with body := .fls } :: C) h
    | none => false
  | _ => false

#guard match Interp.run 100 (evalFrom bootMachine (.class' "Depot" none (.seq [
    .def' a.name a.params a.body, .def' b.name b.params b.body]))) with
  | .value _ m => classOwnNamesB history m.heap
  | _ => false

-- Two names for one owner: updating Depot's record alone leaves Alias's bound stale.
#guard match Interp.run 100 (evalFrom bootMachine (.class' "Depot" none .nil)) with
  | .value _ m => match classNamed? m.heap "Depot" with
    | some k =>
      let alias := classHeader "Alias"
      let h := constSetIn m.heap Boot.objectId "Alias" (.ref k)
      let h' := defineMethod h k a.name (code k a)
      let C := [depot, alias]
      classNamed? h "Alias" == some k && classOwnNamesB C h &&
        !classOwnNamesB (classWithMethod depot a :: C) h' &&
        classOwnNamesB (classWithMethod alias a :: classWithMethod depot a :: C) h'
    | none => false
  | _ => false

-- A caller cannot discharge the publication guard while retaining a differently named
-- alias at full conformance. This is generic in both names, contexts and heap owners.
theorem aliased_owner_guard_rejects {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {c alias : Cls} {k : ObjId} (hm : StateOk κ Γ I m)
    (hc : c ∈ κ.classes) (ha : alias ∈ κ.classes)
    (hk : classNamed? m.heap c.name = some k) (hak : classNamed? m.heap alias.name = some k)
    (hne : alias.name ≠ c.name) : memberOwnersB κ c = false := by
  cases hf : memberOwnersB κ c with
  | false => rfl
  | true => exact False.elim (hne (memberOwnersB_sound hm hc hk hf alias ha hak))

#print axioms aliased_owner_guard_rejects
end Ratchet.Denote.Typed.OwnNamesControls
