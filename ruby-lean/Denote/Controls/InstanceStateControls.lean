import Denote.Rules.Instance.InstanceState
import Denote.Sem.Instance.InstanceSiteEntry
import Denote.Rules.Class.ClassEntry
import Denote.Rules.Method.MethodChecked

/-! Body-local entry from annotations, plus actual define/call controls. These are not
class-rule admissions: caller restoration and persistent class-site publication remain. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private def decl : Defn := ⟨"inc", [.req "x"],
  .send (some (.var .lvar "x")) "+" [.int 1] none⟩
private def callerCtx : Ctx := reserveNameCtx ctx0 "inc"
private def bodyCtx : Ctx := instanceBodyCtx callerCtx ⟨"Point", "Point", "inc"⟩ .ivar0
private def hint : Deriv := .prim (.var .lvar "x") "+" [.intLit 1] .int .int
private def cert : Deriv := .defDecl "inc" [("x", .int)] .int hint
private def checked : CheckedBody bodyCtx .ivar0 decl :=
  (checkMethodBody 100 bodyCtx .ivar0 decl cert).get (by decide)

-- These are annotation checks, independent of whether a concrete call would succeed.
#guard (checkMethodBody 100 bodyCtx .ivar0 decl cert).isSome
#guard (checkMethodBody 100 bodyCtx .ivar0 decl
  (.defDecl "inc" [("x", .nilable .int)] .int hint)).isNone
#guard (checkMethodBody 100 bodyCtx .ivar0 decl
  (.defDecl "inc" [("x", .int)] .bool hint)).isNone

/-- A single checked body covers every Integer argument at full instance entry.
The RunSpec stops at the body boundary; it does not pretend to restore the caller. -/
theorem annotated_instance_body {m : Machine} {k : ObjId} {md : MethodDef} {recv : Value}
    (hm : StateOk callerCtx [] .ivar0 m) (site : InstanceSite callerCtx "Point" k m.heap)
    (code : InstanceMethodCode k "inc" md) (hv : denM (.inst "Point" .ivar0) m recv)
    (hp : md.params = [.req "x"]) (hb : md.body = toRuby decl.body) (v : Int) :
    ∃ n, Interp.enterUserMethod m recv "inc" md [.int v] none = .next n ∧
      n.ctl = .eval (toRuby decl.body) ∧
      StateOk bodyCtx [("x", .int)] .ivar0 n ∧
      RunSpec n (evalFrom n decl.body) [("x", .int)] .int bodyCtx .ivar0 := by
  obtain ⟨n, hn, hc, he⟩ := instance_enterUserMethod_state
    (ps := [("x", .int)]) (args := [.int v]) hm (ReframeFO.empty rfl rfl rfl rfl) rfl site
    (hm.runtime rfl).phase code rfl hv rfl
    (by simp [DenAll, denM, isIntV]) (by simp [FirstOrder, isAliasTy])
    (fun x => (constGet?_empty (κ := bodyCtx) rfl x).trans (constGet?_empty rfl x).symm) hp
  refine ⟨n, hn, hc.trans (congrArg Ctl.eval hb), he, ?_⟩
  exact checked_body_context checked n he

-- Actual definition and dispatch, not merely a declaration or a synthetic method frame.
#guard match Interp.run 200 (evalFrom bootMachine (.seq [
    .class' "Point" none (.def' decl.name decl.params decl.body),
    .send (some (.send (some (.const "Point")) "new" [] none)) "inc" [.int 3] none])) with
  | .value (.int 4) _ => true
  | _ => false

theorem boot_class_instance_site (hb : bootOkB = true) {name : String} {body : Ratchet.Expr}
    (hn : constOwn bootMachine.heap Boot.objectId name = none) (hne : name.isEmpty = false) :
    ∃ n, Interp.stepFn (evalFrom bootMachine (.class' name none body)) = .next n ∧
      InstanceSite ctx0 name bootMachine.heap.objs.size n.heap := by
  have hm := stateOk_boot hb
  obtain ⟨e, he, hs⟩ := stepFn_class_fresh (body := body) hm rfl hn hne
  refine ⟨_, hs, ?_⟩
  exact FreshClass.instanceSite (body := toRuby body) hm rfl he

private def namesAt (h : Heap) (k : ObjId) : Bool :=
  shadowableNames.all fun name => (Interp.methodOn h k name).all fun (_, md) =>
    md.builtin.isSome || md.undefined

-- Component countermodel, not full StateOk: class self and Object's metaclass both
-- mask Object#x. A fresh instance nevertheless reaches the hidden prelude body.
#guard match Interp.enterClassBody bootMachine "Point" false none .nil with
  | .next m =>
      let eigen := classOf m.heap (.ref Boot.objectId)
      let hidden := defineMethod m.heap Boot.objectId "x"
        { owner := Boot.objectId, params := [], body := .fls, fromPrelude := true }
      let masked := defineMethod hidden eigen "x"
        { owner := eigen, params := [], body := .nil, builtin := some "Object#nil?" }
      let m := { m with heap := masked }
      namesAt masked (classOf masked m.currentFrame.self) && namesAt masked eigen &&
        !namesAt masked Boot.objectId &&
        Semantics.typeStuck (Interp.run 200 (evalFrom m (.send
          (some (.send (some (.send (some (.const "Point")) "new" [] none)) "x" [] none))
          "+" [.int 1] none)))
  | _ => false

-- Global constant agreement says nothing about a different class's lexical resolution.
#guard match Interp.run 150 (evalFrom bootMachine (.seq [
    .casgn "LIMIT" (.int 7),
    .class' "Point" none (.seq [.casgn "LIMIT" .fls,
      .def' "answer" [] (.send (some (.const "LIMIT")) "+" [.int 1] none)])])) with
  | .value _ m => match classNamed? m.heap "Point" with
    | some k =>
        (constLookup m.heap "LIMIT").any (·.identEq (.int 7)) &&
        (instanceConstResolve m.heap k "LIMIT").any (·.identEq (.bool false)) &&
        Semantics.typeStuck (Interp.run 150 (evalFrom m
          (.send (some (.send (some (.const "Point")) "new" [] none)) "answer" [] none)))
    | none => false
  | _ => false

#print axioms annotated_instance_body
#print axioms boot_class_instance_site
end Ratchet.Denote.Typed
