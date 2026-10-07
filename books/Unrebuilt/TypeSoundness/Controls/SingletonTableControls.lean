import Books.TypeSoundness.Rules.Singleton.SingletonPublish
import Books.TypeSoundness.Controls.ClassHeaderControls

/-! Real boot publication, separate same-named namespaces, and forged positive code. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.SingletonTableControls
open RubyCore Checker Checker.Soundness

private def copyDef : Defn := ⟨"copy", [.req "value"], .var .lvar "value"⟩
private def body : Checker.Expr := .defs .self' copyDef.name copyDef.params copyDef.body
private def ctx : Ctx := classHeaderCtx (classBodyCtx ctx0 "Point") "Point"

theorem boot_publish (hb : bootOkB = true)
    (hn : constOwn bootMachine.heap Boot.objectId "Point" = none) :
    ∃ m k e, StateOk ctx [] .ivar0 m ∧ classNamed? m.heap "Point" = some k ∧
      Interp.stepFn m = .next (Interp.withCtl
        (installSingleton m e "copy" [.req "value"] (.var .lvar "value")) (.value (.sym "copy"))) ∧
      ClassesOk [{ classHeader "Point" with smethods := [copyDef] }, classHeader "Point"]
        (installSingleton m e "copy" [.req "value"] (.var .lvar "value")) := by
  obtain ⟨m, step, hm⟩ := boot_point_header hb hn body
  obtain ⟨ep, he, hs⟩ := stepFn_class_fresh (body := body) (stateOk_boot hb) rfl hn (by decide)
  have hctl : m.ctl = .eval (toRuby body) := by rw [hs] at step; cases step; rfl
  obtain ⟨k, e, hk, hstep, table⟩ := scoped_singleton_publish (d := copyDef)
    (c := classHeader "Point") hm (by change _ ∈ [_]; simp) rfl rfl hctl (by
      intro old ho prev hp
      change old ∈ [classHeader "Point"] at ho
      have he := List.mem_singleton.mp ho
      subst old
      cases hp)
  exact ⟨m, k, e, hm, hk, hstep, table⟩

private def pairProgram : Checker.Expr := .seq [
  .class' "Point" none (.seq [body, .def' "copy" [] .tru]),
  .array [.send (some (.const "Point")) "copy" [.int 7] none,
    .send (some (.send (some (.const "Point")) "new" [] none)) "copy" [] none]]

#guard match Interp.run 250 (evalFrom bootMachine pairProgram) with
  | .value (.ref o) m => match (m.heap.get o).payload with
    | .arr #[.int 7, .bool true] => true
    | _ => false
  | _ => false

-- A cached, rooted, frontmost owner can still alias its ordinary class. The leaf fact
-- rejects this heap before publication could let an instance write overwrite a singleton.
#guard match Interp.enterClassBody bootMachine "Point" false none .nil with
  | .next m =>
    let k := bootMachine.heap.objs.size
    let h := m.heap.set k { m.heap.get k with eigen := some k }
    metaReadyB h k && classFrontB h (classOf h (.ref k)) &&
      !(h.get (classOf h (.ref k))).eigen.isNone
  | _ => false

private def good : Defn := ⟨"seven", [], .int 7⟩
private def code : MethodDef := { params := [], body := .int 7, owner := 1, cref := [0, Boot.objectId] }
private def heap : Heap := ⟨#[
  { klass := Boot.classId, eigen := some 1, payload := .cls { superclass := none, name := "Point" } },
  { klass := Boot.classId, payload := .cls { superclass := none, name := "eigen", methods := [("seven", code)] } }]⟩

theorem genuine_row : SingletonRows [good] 0 heap := by
  intro d hd
  have he := List.mem_singleton.mp hd
  subst d
  exact ⟨1, code, rfl, rfl, rfl, rfl, rfl, rfl, ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩⟩

theorem forged_body : ¬ SingletonRows [{ good with body := .tru }] 0 heap := by
  intro hp
  obtain ⟨e, md, he, _, row, _, hb, _⟩ := hp _ (List.mem_singleton_self _)
  have he' : some 1 = some e := he
  cases he'
  have row' : some code = some md := row
  cases row'
  contradiction

#print axioms boot_publish
#print axioms genuine_row
#print axioms forged_body
end Checker.Soundness.Typed.SingletonTableControls
