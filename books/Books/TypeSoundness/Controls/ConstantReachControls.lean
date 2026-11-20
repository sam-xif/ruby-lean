import Books.TypeSoundness.Conformance.Class.ClassConstScopeActual

/-! The old constant-equality fact alone does not imply reachability of future globals. -/
set_option autoImplicit false
namespace Checker.Soundness.ConstantReachControls
open RubyCore Checker RubyCore.Proof Checker.Soundness

/-! The ids this countermodel allocates are **relative to `Boot.mainId`**, not literals: adding a
bootstrap class moves `mainId` and every boot id after it, and a literal heap size would either
fall out of range or silently point at another object (issue #22). -/
private def detachedId : ObjId := Boot.mainId + 1
private def eigenId : ObjId := Boot.mainId + 2
private def heapSize : Nat := eigenId + 1
/-- The first id `FreshClassActual.heap` allocates on top of this heap. -/
private def freshId : ObjId := heapSize

private def row : List (String × Value) := [("Detached", .ref detachedId)]
private def basic : Object := { klass := Boot.classId, payload := .cls { superclass := none, name := "BasicObject" } }
private def root : Object :=
  { klass := Boot.classId, eigen := some eigenId,
    payload := .cls { name := "Object", superclass := some Boot.basicObjectId, consts := row } }
private def detached : Object :=
  { klass := Boot.classId, eigen := some eigenId,
    payload := .cls { name := "Detached", superclass := some Boot.basicObjectId, consts := row } }
private def hooks : List (String × MethodDef) :=
  [("method_added", { params := [], body := .nil, owner := eigenId, builtin := some "Module#method_added" }),
   ("singleton_method_added",
    { params := [], body := .nil, owner := eigenId, builtin := some "BasicObject#singleton_method_added" }),
   ("inherited", { params := [], body := .nil, owner := eigenId, builtin := some "Class#inherited" })]
private def eigenPayload : ClassPayload :=
  { superclass := some Boot.basicObjectId, name := "", attached := some detachedId, methods := hooks }
private def eigenObj : Object := { klass := Boot.classId, payload := .cls eigenPayload }
private def h : Heap :=
  { objs := ((((Array.replicate heapSize (default : Object)).set! 0 basic).set! 1 root).set!
    detachedId detached).set! eigenId eigenObj }
private def m : Machine :=
  { ctl := .value .nil, heap := h,
    frames := #[{ self := .ref Boot.mainId, defmod := Boot.objectId, cref := [], kind := .toplevel }], stack := [0] }

private theorem cp0 : h.classPayload? 0 = some { superclass := none, name := "BasicObject" } := rfl
private theorem cp1 : h.classPayload? 1 = some
    { name := "Object", superclass := some Boot.basicObjectId, consts := row } := rfl
private theorem cpDetached : h.classPayload? detachedId = some
    { name := "Detached", superclass := some Boot.basicObjectId, consts := row } := rfl
private theorem cpEigen : h.classPayload? eigenId = some eigenPayload := rfl

#guard chainsInB h
#guard saturatedB h
#guard ancestors h detachedId == [detachedId, Boot.basicObjectId]
#guard !((ancestors h detachedId).contains Boot.objectId)
#guard (constOwn h Boot.objectId "Next").isNone

private theorem old_constants (n : String) : instanceConstResolve h detachedId n = constLookup h n := by
  have ha : ancestors h detachedId = [detachedId, 0] := by decide
  have hown : constOwn h detachedId n = constLookup h n := by
    simp only [constOwn, constLookup, cpDetached, cp1, Boot.objectId, Option.bind_some]
  have hfrom : constLookupFrom h detachedId n = constLookup h n := by
    rw [FreshClassActual.const_from_eq_firstM, ha]
    have hzero : constOwn h 0 n = none := by
      simp only [constOwn, cp0, Option.bind_some, List.find?_nil, Option.map_none]
    simp only [List.firstM, hown, hzero]
    cases constLookup h n <;> rfl
  simp only [instanceConstResolve, List.firstM, hown, hfrom, cpDetached, Option.any_some,
    Bool.false_eq_true, ite_false]
  cases constLookup h n <;> rfl

private theorem old_site : InstanceSite (default : Ctx) "Detached" detachedId h := by
  refine ⟨by decide, by decide, by decide, old_constants, ?_, ?_, ?_, by decide, rfl, ?_, by decide,
    by rw [cpDetached]; rfl, by decide, by decide, by decide, ⟨eigenId, rfl, rfl, rfl⟩, by decide,
    by decide, by decide, by decide⟩
  · intro n hn owner md hm
    simp only [shadowableNames, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl <;>
      (change none = some (owner, md) at hm; cases hm)
  · refine ⟨eigenId, rfl, by decide, ?_⟩
    intro base ch hb
    have hbound := (builtinBase_bound hb).1
    simp only [Boot.procId] at hbound
    exact (Nat.ne_of_lt (Nat.lt_of_le_of_lt hbound (by decide : 29 < eigenId))).symm
  · intro n hn owner md hm
    simp only [shadowableNames, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl <;>
      (change none = some (owner, md) at hm; cases hm)
  · intro n _
    change constLookupFrom h eigenId n = none
    rw [FreshClassActual.const_from_eq_firstM, show ancestors h eigenId = [eigenId, 0] from by decide]
    simp only [List.firstM, constOwn, cpEigen, cp0, Option.bind_some, List.find?_nil, Option.map_none]
    rfl

#guard (constLookup (FreshClassActual.heap m "Next" eigenId) "Next").isSome
#guard (instanceConstResolve (FreshClassActual.heap m "Next" eigenId) detachedId "Next").isNone

theorem old_site_not_preserved :
    InstanceSite (default : Ctx) "Detached" detachedId h ∧
      ¬ InstanceSite (default : Ctx) "Detached" detachedId (FreshClassActual.heap m "Next" eigenId) := by
  refine ⟨old_site, ?_⟩
  intro site
  have he := site.constants "Next"
  have hmiss : instanceConstResolve (FreshClassActual.heap m "Next" eigenId) detachedId "Next" = none := rfl
  have hglobal : constLookup (FreshClassActual.heap m "Next" eigenId) "Next" = some (.ref freshId) := rfl
  rw [hmiss, hglobal] at he
  cases he

#print axioms old_site_not_preserved
end Checker.Soundness.ConstantReachControls
