import Denote.Rules.Instance.InstanceCallEntry
import Denote.Controls.ClassStateControls
import Denote.Sem.Instance.InstanceSiteClass

/-! Persistent sites are demanded by installed classes and pending lexical scope,
not by a signature alone. Fresh unrelated declarations retain earlier sites. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem class_state_has_site (hb : bootOkB = true) {name : String} {body : Ratchet.Expr}
    (hq : FreshClass.nativeFrameB ctx0 name = true)
    (hn : constOwn bootMachine.heap Boot.objectId name = none) (hne : name.isEmpty = false) :
    ∃ n, Interp.stepFn (evalFrom bootMachine (.class' name none body)) = .next n ∧
      StateOk (classBodyCtx ctx0 name) [] .ivar0 n ∧
      ∃ k, InstanceSite (classBodyCtx ctx0 name) name k n.heap := by
  obtain ⟨n, hs, hm⟩ := boot_class_state hb hq hn hne
  exact ⟨n, hs, hm, hm.classSites.of_scope rfl⟩

-- A new constant becomes visible from an existing method's saved lexical scope.
#guard match Interp.run 150 (evalFrom bootMachine (.class' "Point" none
    (.def' "other" [] (.const "Other")))) with
  | .value _ m => match classNamed? m.heap "Point" with
    | some k => (instanceConstResolve m.heap k "Other").isNone &&
        match Interp.run 100 (evalFrom m (.class' "Other" none .nil)) with
        | .value _ n =>
            (instanceConstResolve n.heap k "Other").any (fun v => isClassRefNamed n.heap v "Other") &&
            match Interp.run 150 (evalFrom n
              (.send (some (.send (some (.const "Point")) "new" [] none)) "other" [] none)) with
            | .value v result => isClassRefNamed result.heap v "Other"
            | _ => false
        | _ => false
    | none => false
  | _ => false

-- Refuse preservation through nonfresh registration: an old nominal site would move.
theorem site_rebinding_not_preserved {κ : Ctx} {cn : String} {k e : ObjId} {h : Heap}
    (site : InstanceSite κ cn k h) (ho : (h.classPayload? Boot.objectId).isSome = true) :
    ¬ InstanceSite κ cn k (RubyCore.Proof.Judgment.freshClsHeap h Boot.objectId cn cn e) := by
  intro bad
  have hn := classNamed_freshClass (name := cn) (e := e) ho (lt_size_of_classPayload ho)
  have he : h.objs.size = k := Option.some.inj (hn.symm.trans bad.named)
  exact (Nat.ne_of_lt site.live) he.symm

#print axioms class_state_has_site
#print axioms site_rebinding_not_preserved
end Ratchet.Denote.Typed
