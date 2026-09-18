import Ratchet.Controls.ReceiverCacheControls
import Denote.Rules.Instance.ReceiverCache
import Denote.Rules.Subclass.SubclassRule
import Denote.Rules.Class.ClassConstant
import Denote.Sem.Core.Boot

/-! The receiver cache is consumed at real inherited new dispatch; its checked String
field shape survives initialization and return. The getter's body has a separate proof. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.ReceiverCacheControls
open RubyCore Ratchet Ratchet.Denote
open Ratchet.ReceiverCacheControls

private def parentClass : Cls := classWithMethod
  (classWithMethod (classHeader "LabelBox")
    ⟨"initialize", [.req "value"], ClassCheckControls.initBody⟩)
  ⟨"get", [], .var .ivar "@value"⟩
private def childExpr : Ratchet.Expr := .class' child.name (some (.const parentClass.name)) .nil
private def newExpr : Ratchet.Expr := .send (some (.const child.name)) "new" [.str "Rex"] none

private theorem child_mem : child ∈ callerCtx.classes := List.mem_cons_self

theorem child_sem : SemSafeCtxA parent.ctx [] .ivar0 childExpr .nilT callerCtx [] .ivar0 := by
  have hc : parentClass ∈ parent.ctx.classes := by
    let f := (findClass "LabelBox" parent.ctx.classes).get (by decide +kernel)
    have he : f.cls = parentClass := clsEqB_sound _ _ (by decide +kernel)
    exact he ▸ f.member
  exact SemSafeCtxA.subclassDecl (SemSafeCtxA.constClass hc) hc SemSafeCtxA.nilLit (by decide +kernel)

private theorem new_from_cache (b : CallableInitializerAt callerCtx child)
    (hp : b.body.params = [("value", .cls "String")]) :
    SemSafeCtxA callerCtx [] .ivar0 newExpr (.inst child.name b.body.fields) callerCtx [] .ivar0 := by
  apply (SemSafeCtxA.constClass child_mem).sendVia
    (SemAllCtxA.cons (SemSafeCtxA.strLit (s := "Rex")) .nil rfl) rfl rfl
    (by simp [FirstOrder])
  intro m hm hk recv hv args hargs
  obtain ⟨k, n, hn, hs, hrun⟩ := checked_inherited_constructor_run b hm child_mem
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hk (by simpa [hp] using hargs)
  have he : recv = .ref k := by cases recv <;> simp_all [denM, isClassRefNamed]
  change StepSpec m [] (.inst child.name b.body.fields)
    (Interp.finishSend m recv .explicit "new" args .none) callerCtx .ivar0
  rw [he, hs]
  exact hrun

theorem new_sem : SemSafeCtxA callerCtx [] .ivar0 newExpr
    (.inst child.name init.body.fields) callerCtx [] .ivar0 :=
  new_from_cache init (by decide +kernel)

theorem boot_new (hb : bootOkB = true) :
    RunSpec bootMachine (evalFrom bootMachine
      (.seq [ClassCheckControls.cls "LabelBox", childExpr, newExpr])) []
      (.inst child.name (ClassCheckControls.fields (.cls "String"))) callerCtx .ivar0 := by
  have hp := certified_context parent
  have hshape : parent.out = [] ∧ parent.spine = .ivar0 := by decide +kernel
  rw [hshape.1, hshape.2] at hp
  have hi : init.body.fields = ClassCheckControls.fields (.cls "String") := by decide +kernel
  simpa only [hi] using (hp bootMachine (stateOk_boot hb)).thenSeq
    (.cons child_sem (.last new_sem))

theorem getter_body : SemSafeCtxA
    (instanceBodyCtx callerCtx ⟨child.name, get.owner, get.decl.name⟩ get.fields)
    get.body.params get.fields get.decl.body get.body.ret
    (instanceBodyCtx callerCtx ⟨child.name, get.owner, get.decl.name⟩ get.fields)
    get.body.out get.fields := djudge_context get.body.judged

theorem getter_returns_string : get.body.ret = .cls "String" := by decide +kernel

#guard match Interp.run 220 (evalFrom bootMachine
    (.seq [ClassCheckControls.cls "LabelBox", childExpr,
      .send (some newExpr) "get" [] none])) with
  | .value v m => Builtins.strPayload? m.heap v == some "Rex"
  | _ => false

#print axioms child_sem
#print axioms new_sem
#print axioms boot_new
#print axioms getter_body
#print axioms getter_returns_string
end Ratchet.Denote.Typed.ReceiverCacheControls
