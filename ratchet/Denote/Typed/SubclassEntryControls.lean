import Denote.Typed.SubclassEntry
import Denote.Sem.SubclassChains
import Denote.Sem.ClassChains
import Denote.Sem.OwnNames
import Denote.Sanity

/-! Actual subclass entry, inherited calls and cached/uncached metaclass controls.
These exercise the model's allocation path, not whole-program checker admission. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.SubclassEntryControls
open RubyCore Ratchet Ratchet.Denote

private def echo : Defn := ⟨"echo", [.req "flag"], .var .lvar "flag"⟩
private def anchor : Cls := classWithMethod (classHeader "Anchor") echo
private def leaf : Cls := { classHeader "Leaf" with super? := some "Anchor" }
private def baseProgram : Ratchet.Expr := .class' "Anchor" none (.def' echo.name echo.params echo.body)
private def call : Ratchet.Expr := .send (some (.send (some (.const "Leaf")) "new" [] none))
  "echo" [.tru] none

-- Parent and metaclass parent are both retained, at ids determined by the incoming heap.
#guard match Interp.run 100 (evalFrom bootMachine baseProgram) with
  | .value _ m => match classNamed? m.heap "Anchor" with
    | some parent => match (m.heap.get parent).eigen with
      | some ep => match Interp.enterClassBody m "Leaf" false (some parent) .nil with
        | .next n =>
          let k := m.heap.objs.size
          n.heap.objs.size == k + 2 && classNamed? n.heap "Leaf" == some k &&
            (n.heap.classPayload? k).any (fun cp => cp.superclass == some parent && cp.methods.isEmpty) &&
            (n.heap.get k).eigen == some (k + 1) &&
            (n.heap.classPayload? (k + 1)).any (fun cp => cp.superclass == some ep) &&
            (n.heap.get parent).eigen == some ep &&
            (match n.currentFrame.self with | .ref r => r == k | _ => false) &&
            n.currentFrame.defmod == k &&
            n.currentFrame.cref == [k, Boot.objectId] &&
            classReadyB n.heap && saturatedB n.heap && metaReadyB n.heap k && metaReadyB n.heap parent &&
            classChainsB [leaf, anchor] n.heap && classOwnNamesB [leaf, anchor] n.heap &&
            (match Interp.run 30 n with
              | .value _ finished => match Interp.run 100 (evalFrom finished call) with
                | .value (.bool true) _ => true
                | _ => false
              | _ => false)
        | _ => false
      | none => false
    | none => false
  | _ => false

-- Instance ancestry and own tables do not establish the cache premise. Without it,
-- the same valid subclass operation allocates a replacement parent metaclass as well.
#guard match Interp.run 100 (evalFrom bootMachine baseProgram) with
  | .value _ m => match classNamed? m.heap "Anchor" with
    | some parent =>
      let h := m.heap.set parent { m.heap.get parent with eigen := none }
      classChainsB [anchor] h && classOwnNamesB [anchor] h && classReadyB h && saturatedB h &&
        !metaReadyB h parent &&
        match Interp.enterClassBody { m with heap := h } "Leaf" false (some parent) .nil with
        | .next n =>
          let k := m.heap.objs.size
          n.heap.objs.size == k + 3 && (n.heap.get parent).eigen == some (k + 1) &&
            (n.heap.get k).eigen == some (k + 2) && classChainsB [leaf, anchor] n.heap &&
            classReadyB n.heap && saturatedB n.heap && metaReadyB n.heap k && metaReadyB n.heap parent &&
            (match Interp.run 30 n with
              | .value _ finished => match Interp.run 100 (evalFrom finished call) with
                | .value (.bool true) _ => true
                | _ => false
              | _ => false)
        | _ => false
    | none => false
  | _ => false

-- The superclass continuation, not enterClassBody itself, rejects a module receiver.
#guard match Interp.run 100 (evalFrom bootMachine (.module' "NotAClass" .nil)) with
  | .value _ m => match classNamed? m.heap "NotAClass" with
    | some parent => Semantics.typeStuck (Interp.run 30
        { m with ctl := .value (.ref parent), kont := [.classDefK "Leaf" .nil] })
    | none => false
  | _ => false

-- Synthetic heap controls, not reachable-program or full-StateOk witnesses.
-- An in-bounds self-cycle refutes deriving saturation from edge bounds alone.
#guard match (bootMachine.heap.get Boot.objectId).eigen with
  | some ep =>
    let h := Subclass.heap bootMachine.heap Boot.objectId "Loop" "Loop" bootMachine.heap.objs.size ep
    Proof.chainsInB h && !saturatedB h
  | none => false

-- Readiness still does not separate an arbitrary parent's metaclass from value bases.
-- Actual subclass entry can preserve readiness while introducing a proper Float subclass.
#guard match Interp.run 100 (evalFrom bootMachine baseProgram) with
  | .value _ m => match classNamed? m.heap "Anchor" with
    | some parent =>
      let h := m.heap.set parent { m.heap.get parent with eigen := some Boot.floatId }
      classReadyB h && saturatedB h && baseChainsOkB { m with heap := h } && !metaReadyB h parent &&
        match Interp.enterClassBody { m with heap := h } "Leaf" false (some parent) .nil with
        | .next n => classReadyB n.heap && saturatedB n.heap && !baseChainsOkB n &&
            (ancestors n.heap (h.objs.size + 1)).contains Boot.floatId
        | _ => false
    | none => false
  | _ => false

/-- A cached builtin-base alias is excluded by full conformance, for every declared class. -/
theorem aliased_meta_not_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {c : Cls} {k base : ObjId} {ch : List String} (hc : c ∈ κ.classes)
    (hn : classNamed? m.heap c.name = some k) (he : (m.heap.get k).eigen = some base)
    (hb : (base, ch) ∈ builtinBases) : ¬ StateOk κ Γ I m := by
  intro hm
  exact (hm.classSites.metaclass hc hn).not_base he hb rfl

theorem uncached_parent_not_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {c : Cls} {k : ObjId} (hc : c ∈ κ.classes) (hn : classNamed? m.heap c.name = some k)
    (he : (m.heap.get k).eigen = none) : ¬ StateOk κ Γ I m := by
  intro hm
  obtain ⟨e, he', _, _⟩ := hm.classSites.metaclass hc hn
  rw [he] at he'; cases he'

#print axioms aliased_meta_not_state
#print axioms uncached_parent_not_state
end Ratchet.Denote.Typed.SubclassEntryControls
