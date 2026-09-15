import Denote.Typed.SubclassEntry
import Denote.Sanity

/-! Real inherited constant reads and site-local exclusion controls. These execute model
inputs; they do not supply annotation-body proofs or admit constant-assignment syntax. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.SubclassScopeControls
open RubyCore Ratchet Ratchet.Denote

private def setup : Ratchet.Expr := .seq [
  .casgn "LIMIT" (.int 7),
  .class' "ScopeBase" none (.def' "readLimit" [] (.const "LIMIT"))]

private def sitesB (h : Heap) (k : ObjId) : Bool :=
  classFrontB h k && definitionHookQuietB h k && metaReadyB h k &&
    namesAtB (nameFreeN ctx0) h k && namesAtB (nameFreeN ctx0) h (classOf h (.ref k))

#guard match Interp.run 150 (evalFrom bootMachine setup) with
  | .value _ m => match classNamed? m.heap "ScopeBase" with
    | some parent => sitesB m.heap parent && (instanceConstResolve m.heap parent "ScopeChild").isNone &&
        match Interp.enterClassBody m "ScopeChild" false (some parent) (toRuby (.const "LIMIT")) with
        | .next n =>
          let k := m.heap.objs.size
          sitesB n.heap parent && sitesB n.heap k &&
            (constResolveAt n "LIMIT").any (·.identEq (.int 7)) &&
            (constResolveAt n "ScopeChild").any (·.identEq (.ref k)) &&
            (instanceConstResolve n.heap parent "ScopeChild").any (·.identEq (.ref k)) &&
            (constResolveAt n "Missing").isNone &&
            match Interp.run 30 n with
            | .value (.int 7) finished => match Interp.run 150 (evalFrom finished
                (.send (some (.send (some (.const "ScopeChild")) "new" [] none)) "readLimit" [] none)) with
              | .value (.int 7) _ => true
              | _ => false
            | _ => false
        | _ => false
    | none => false
  | _ => false

-- Real Ruby-shaped input, outside the checker fragment: an inherited nonglobal constant
-- breaks global scope agreement. Parent-site conformance already rules this out.
#guard match Interp.run 150 (evalFrom bootMachine
    (.class' "Vault" none (.casgn "SECRET" (.int 9)))) with
  | .value _ m => match classNamed? m.heap "Vault" with
    | some parent => sitesB m.heap parent && (constLookup m.heap "SECRET").isNone &&
        (instanceConstResolve m.heap parent "SECRET").any (·.identEq (.int 9)) &&
        match Interp.enterClassBody m "VaultChild" false (some parent) (toRuby (.const "SECRET")) with
        | .next n => (constLookup n.heap "SECRET").isNone &&
            (constResolveAt n "SECRET").any (·.identEq (.int 9)) &&
            match Interp.run 30 n with | .value (.int 9) _ => true | _ => false
        | _ => false
    | none => false
  | _ => false

theorem nonglobal_parent_constant_not_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {c : Cls} {k : ObjId} {cn : String} {v : Value}
    (hc : c ∈ κ.classes) (hk : classNamed? m.heap c.name = some k)
    (hg : constLookup m.heap cn = none) (hv : constOwn m.heap k cn = some v) : ¬ StateOk κ Γ I m := by
  intro hm
  have h := (hm.classSites.at_class hc hk).constants cn
  simp only [instanceConstResolve, List.firstM, hv, hg] at h
  cases h

#print axioms nonglobal_parent_constant_not_state
end Ratchet.Denote.Typed.SubclassScopeControls
