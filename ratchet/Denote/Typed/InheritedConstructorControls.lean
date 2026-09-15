import Denote.Typed.InheritedConstructorExpr
import Denote.Typed.SubclassRule
import Denote.Typed.ConstructorGeneralControls

/-! Definition plus inherited call, with a body replayed at its original Boolean
annotation, a distinct receiver/lexical owner, and an instance result rather than Boolean. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.InheritedConstructorControls
open RubyCore Ratchet Ratchet.Denote

private def parent : Cls := classWithMethod FlagBox.header FlagBox.init
private def child : Cls := subclassHeader "FlagChild" "FlagBox"
private def bodyCtx : Ctx := subclassHeaderCtx (classBodyCtx FlagBox.callerCtx child.name)
  child.name parent.name
private def callerCtx : Ctx := returnScopeCtx FlagBox.callerCtx bodyCtx
private def program : Ratchet.Expr := .class' child.name (some (.const parent.name)) .nil
private def initCtx : Ctx := initializerBodyCtxAt callerCtx child.name parent.name

private theorem parent_mem : parent ∈ callerCtx.classes := by
  change parent ∈ [child, parent, FlagBox.header]; simp
private theorem child_mem : child ∈ callerCtx.classes := List.mem_cons_self
private theorem init_mem : FlagBox.init ∈ parent.methods := List.mem_cons_self
private theorem prefix_clear : ∀ cn ∈ [child.name], ∃ old ∈ callerCtx.classes,
    old.name = cn ∧ FlagBox.init.name ∉ ownNames callerCtx.classes cn := by
  intro cn hcn
  have he := List.mem_singleton.mp hcn
  subst cn
  exact ⟨child, child_mem, rfl, by decide⟩

-- The old annotation and body hint are replayed in the receiver-aware context;
-- neither the caller's argument nor an unchecked context cast enters this certificate.
private def inheritedInit : CheckedInitializer initCtx FlagBox.init :=
  (refreshInitializerBody 40 initCtx FlagBox.finalInit (.var .lvar "flag")).get (by decide)

#guard initCtx.scope.runtimeClass == some "FlagBox"
#guard initCtx.selfTy == some (.inst "FlagChild" .ivar0)
#guard (checkInitializerBody 40 initCtx FlagBox.init
  (.defDecl "initialize" [("flag", .bool)] .int (.var .lvar "flag"))).isNone
#guard (checkInitializerBody 40 initCtx FlagBox.init
  (.defDecl "initialize" [("flag", .nilable .bool)] .bool (.var .lvar "flag"))).isNone

theorem child_sem : SemSafeCtxA FlagBox.callerCtx [] .ivar0 program .nilT callerCtx [] .ivar0 := by
  have hc : parent ∈ FlagBox.callerCtx.classes := List.mem_cons_self
  exact SemSafeCtxA.subclassDecl (SemSafeCtxA.constClass hc) hc SemSafeCtxA.nilLit (by decide)

private def call (arg : Ratchet.Expr) : Ratchet.Expr :=
  .send (some (.const child.name)) "new" [arg] none

/-- One annotation-domain certificate serves any Boolean-typed argument expression. -/
theorem new_sem {arg : Ratchet.Expr}
    (ha : SemSafeCtxA callerCtx [] .ivar0 arg .bool callerCtx [] .ivar0)
    (hp : plainArgB arg = true) :
    SemSafeCtxA callerCtx [] .ivar0 (call arg) (.inst child.name .ivar0) callerCtx [] .ivar0 := by
  exact SemSafeCtxA.constructInherited (pre := [child.name]) (post := []) (ps := inheritedInit.params)
    (SemSafeCtxA.constClass child_mem) (.cons ha .nil hp) rfl child_mem parent_mem init_mem rfl
    (by decide) prefix_clear (by decide) (by change child.name ∈ [child.name, parent.name]; simp)
    inheritedInit.paramShape inheritedInit.paramsFO inheritedInit.sem
    (reframeTypesB_sound (by decide)) rfl rfl rfl rfl (by intro x; rfl) (by simp) inheritedInit.fieldsFO

theorem boot_new_true (hb : bootOkB = true) :
    RunSpec bootMachine (evalFrom bootMachine (.seq [FlagBox.program, program, call .tru])) []
      (.inst child.name .ivar0) callerCtx .ivar0 :=
  (FlagBox.class_run (stateOk_boot hb)).thenSeq (.cons child_sem (.last (new_sem .truLit rfl)))

theorem boot_new_false (hb : bootOkB = true) :
    RunSpec bootMachine (evalFrom bootMachine (.seq [FlagBox.program, program, call .fls])) []
      (.inst child.name .ivar0) callerCtx .ivar0 :=
  (FlagBox.class_run (stateOk_boot hb)).thenSeq (.cons child_sem (.last (new_sem .flsLit rfl)))

#guard match Interp.run 180 (evalFrom bootMachine (.seq [FlagBox.program, program, call .fls])) with
  | .value (.ref o) n => isExactInst n.heap (.ref o) child.name &&
      (classNamed? n.heap child.name).any (fun k =>
        (Interp.methodOn n.heap k "initialize").any (fun (owner, _) =>
          classNamed? n.heap parent.name == some owner))
  | _ => false
#guard match Interp.run 180 (evalFrom bootMachine (.seq [FlagBox.program, program,
    .send (some (.const child.name)) "new" [] none])) with
  | .uncaught exc m => isAName m.heap exc "ArgumentError"
  | _ => false

#print axioms new_sem
#print axioms boot_new_true
#print axioms boot_new_false
end Ratchet.Denote.Typed.InheritedConstructorControls
