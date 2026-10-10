import Books.TypeSoundness.Conformance.Class.ClassConstScopeActual

/-! The old constant-equality fact alone does not imply reachability of future globals. -/
set_option autoImplicit false
namespace Checker.Soundness.ConstantReachControls
open RubyCore Checker RubyCore.Proof Checker.Soundness

private def row : List (String × Value) := [("Detached", .ref 45)]
private def basic : Object := { klass := Boot.classId, payload := .cls { superclass := none, name := "BasicObject" } }
private def root : Object :=
  { klass := Boot.classId, eigen := some 46,
    payload := .cls { name := "Object", superclass := some Boot.basicObjectId, consts := row } }
private def detached : Object :=
  { klass := Boot.classId, eigen := some 46,
    payload := .cls { name := "Detached", superclass := some Boot.basicObjectId, consts := row } }
private def hooks : List (String × MethodDef) :=
  [("method_added", { params := [], body := .nil, owner := 46, builtin := some "Module#method_added" }),
   ("singleton_method_added",
    { params := [], body := .nil, owner := 46, builtin := some "BasicObject#singleton_method_added" }),
   ("inherited", { params := [], body := .nil, owner := 46, builtin := some "Class#inherited" })]
private def eigenPayload : ClassPayload :=
  { superclass := some Boot.basicObjectId, name := "", attached := some 45, methods := hooks }
private def eigenObj : Object := { klass := Boot.classId, payload := .cls eigenPayload }
/-- The three scratch ids (`detached` at 45, its eigenclass at 46, and the fresh
    `"Next"` object allocated on top at 47) sit immediately after the boot classes, so the
    literal size is `Boot.mainId + 3`. Expressed in terms of `mainId` so adding a bootstrap
    class (which moves `mainId`) cannot silently truncate the heap (issue #22). -/
private def heapSize : Nat := Boot.mainId + 3
private def h : Heap :=
  { objs := ((((Array.replicate heapSize (default : Object)).set! 0 basic).set! 1 root).set! 45 detached).set! 46 eigenObj }
private def m : Machine :=
  { ctl := .value .nil, heap := h,
    frames := #[{ self := .ref Boot.mainId, defmod := Boot.objectId, cref := [], kind := .toplevel }], stack := [0] }

private theorem cp0 : h.classPayload? 0 = some { superclass := none, name := "BasicObject" } := rfl
private theorem cp1 : h.classPayload? 1 = some
    { name := "Object", superclass := some Boot.basicObjectId, consts := row } := rfl
private theorem cp45 : h.classPayload? 45 = some
    { name := "Detached", superclass := some Boot.basicObjectId, consts := row } := rfl
private theorem cp46 : h.classPayload? 46 = some eigenPayload := rfl

#guard chainsInB h
#guard saturatedB h
#guard ancestors h 45 == [45, Boot.basicObjectId]
#guard !((ancestors h 45).contains Boot.objectId)
#guard (constOwn h Boot.objectId "Next").isNone

private theorem old_constants (n : String) : instanceConstResolve h 45 n = constLookup h n := by
  have ha : ancestors h 45 = [45, 0] := by decide
  have hown : constOwn h 45 n = constLookup h n := by
    simp only [constOwn, constLookup, cp45, cp1, Boot.objectId, Option.bind_some]
  have hfrom : constLookupFrom h 45 n = constLookup h n := by
    rw [FreshClassActual.const_from_eq_firstM, ha]
    have hzero : constOwn h 0 n = none := by
      simp only [constOwn, cp0, Option.bind_some, List.find?_nil, Option.map_none]
    simp only [List.firstM, hown, hzero]
    cases constLookup h n <;> rfl
  simp only [instanceConstResolve, List.firstM, hown, hfrom, cp45, Option.any_some,
    Bool.false_eq_true, ite_false]
  cases constLookup h n <;> rfl

private theorem old_site : InstanceSite (default : Ctx) "Detached" 45 h := by
  refine ⟨by decide, by decide, by decide, old_constants, ?_, ?_, ?_, by decide, rfl, ?_, by decide,
    by rw [cp45]; rfl, by decide, by decide, by decide, ⟨46, rfl, rfl, rfl⟩, by decide, by decide, by decide, by decide⟩
  · intro n hn owner md hm
    simp only [shadowableNames, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl <;>
      (change none = some (owner, md) at hm; cases hm)
  · refine ⟨46, rfl, by decide, ?_⟩
    intro base ch hb
    have hbound := (builtinBase_bound hb).1
    simp only [Boot.procId] at hbound
    exact (Nat.ne_of_lt (Nat.lt_of_le_of_lt hbound (by decide : 29 < 46))).symm
  · intro n hn owner md hm
    simp only [shadowableNames, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl <;>
      (change none = some (owner, md) at hm; cases hm)
  · intro n _
    change constLookupFrom h 46 n = none
    rw [FreshClassActual.const_from_eq_firstM, show ancestors h 46 = [46, 0] from by decide]
    simp only [List.firstM, constOwn, cp46, cp0, Option.bind_some, List.find?_nil, Option.map_none]
    rfl

#guard (constLookup (FreshClassActual.heap m "Next" 46) "Next").isSome
#guard (instanceConstResolve (FreshClassActual.heap m "Next" 46) 45 "Next").isNone

theorem old_site_not_preserved :
    InstanceSite (default : Ctx) "Detached" 45 h ∧
      ¬ InstanceSite (default : Ctx) "Detached" 45 (FreshClassActual.heap m "Next" 46) := by
  refine ⟨old_site, ?_⟩
  intro site
  have he := site.constants "Next"
  have hmiss : instanceConstResolve (FreshClassActual.heap m "Next" 46) 45 "Next" = none := rfl
  have hglobal : constLookup (FreshClassActual.heap m "Next" 46) "Next" = some (.ref 47) := rfl
  rw [hmiss, hglobal] at he
  cases he

#print axioms old_site_not_preserved
end Checker.Soundness.ConstantReachControls
