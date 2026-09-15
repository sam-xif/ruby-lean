import Denote.Typed.InstanceRead
import Denote.Sem.IvarMutation
import Denote.DenB

/-! Class-body prerequisites, not class admission. The small heap witnesses an actual
assignment step without claiming whole-program boot conformance. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

example {κ : Ctx} {Γ : Env} :
    SemSafeCtxA κ Γ (.ivarCons "@x" .int .ivar0) (.var .ivar "@x") .int
      κ Γ (.ivarCons "@x" .int .ivar0) := SemSafeCtxA.ivarRead

example {κ : Ctx} {Γ : Env} (hc : κ.scope.closedIvars = true) :
    SemSafeCtxA κ Γ .ivar0 (.var .ivar "@unset") .nilT κ Γ .ivar0 := by
  simpa [Ctx.ivarReadTy, ivarGet?, hc] using
    (SemSafeCtxA.ivarRead (κ := κ) (Γ := Γ) (I := .ivar0) (x := "@unset"))

-- A shadowed duplicate contributes no contradictory type to a read.
example {κ : Ctx} {Γ : Env} :
    SemSafeCtxA κ Γ (.ivarCons "@x" .int (.ivarCons "@x" (.cls "String") .ivar0))
      (.var .ivar "@x") .int κ Γ
      (.ivarCons "@x" .int (.ivarCons "@x" (.cls "String") .ivar0)) := SemSafeCtxA.ivarRead

private def pointHeap : Heap := ⟨#[
  { klass := 0 },
  { klass := 0, payload := .cls { name := "Object", superclass := none, consts := [("Point", .ref 2)] } },
  { klass := 0, payload := .cls { name := "Point", superclass := none } },
  { klass := 2 }]⟩

private def ivarBefore : Machine :=
  { (Machine.initOn pointHeap .nil) with
    frames := #[{ self := .ref 3, defmod := 2, kind := .method, meth := "initialize" }] }

private def ivarAfter : Machine := Interp.bindIvar ivarBefore "@x" (.int 1)

-- There are no caller locals involved: the universal preservation clause alone fails.
example : ivarBefore.currentFrame.locals = [] := rfl
example : ivarOf ivarBefore.heap (.ref 3) "@x" = .nil := rfl
example : ivarOf ivarAfter.heap (.ref 3) "@x" = .int 1 :=
  ivarOf_bindIvar_self rfl (by decide)

theorem initializer_write_changes_shape : ¬ Framed ivarBefore ivarAfter :=
  nil_ivar_write_not_framed (cn := "Point") rfl (by decide) (by decide) rfl

theorem initializer_write_real_step :
    Interp.stepFn { ivarBefore with ctl := .value (.int 1), kont := [.asgnK .ivar "@x"] } =
      .next { ivarAfter with ctl := .value (.int 1), kont := [] } :=
  stepFn_ivarWrite rfl rfl

-- The write does not invalidate method lookup or the object's nominal identity.
example (v : Value) (name : String) : lookup ivarAfter.heap v name = lookup ivarBefore.heap v name :=
  (bindIvar_ivarOnly ivarBefore "@x" (.int 1)).lookup_eq v name
example : isExactInst ivarAfter.heap (.ref 3) "Point" = true := by decide
example : ivarOf ivarAfter.heap (.ref 2) = ivarOf ivarBefore.heap (.ref 2) :=
  ivarOf_bindIvar_other rfl (by intro h; cases h)

private def aliasBefore : Machine :=
  { ivarBefore with heap := ⟨pointHeap.objs.push { klass := Boot.arrayId, payload := .arr #[.ref 3] }⟩ }
private def aliasAfter : Machine := Interp.bindIvar aliasBefore "@x" (.int 1)
private def retainedTy : Ty := .arrayOf (.inst "Point" (.ivarCons "@x" .nilT .ivar0))

/-- Excluding only the written receiver is insufficient: a distinct array observes its ivars. -/
theorem retained_array_observes_mutation :
    Value.ref 4 ≠ aliasBefore.currentFrame.self ∧ denM retainedTy aliasBefore (.ref 4) ∧
      ¬ denM retainedTy aliasAfter (.ref 4) := by
  have hpre : arrElems? aliasBefore.heap (.ref 4) = some #[.ref 3] := rfl
  have hpost : arrElems? aliasAfter.heap (.ref 4) = some #[.ref 3] := rfl
  refine ⟨(by intro h; cases h), denB_soundM _ _ (by
    simp only [retainedTy, denB, denSpineBFrom, hpre, ← Array.all_toList,
      List.all_cons, List.all_nil, Bool.and_true]; decide), ?_⟩
  intro hd
  have hb := ((denB_iff_aux retainedTy rfl).1 aliasAfter.heap aliasAfter (.ref 4) rfl).mpr hd
  have hfalse : denB retainedTy aliasAfter.heap (.ref 4) = false := by
    simp only [retainedTy, denB, denSpineBFrom, hpost, ← Array.all_toList,
      List.all_cons, List.all_nil, Bool.and_true]; decide
  rw [hfalse] at hb
  cases hb

#print axioms initializer_write_changes_shape
#print axioms initializer_write_real_step
#print axioms retained_array_observes_mutation
end Ratchet.Denote.Typed
