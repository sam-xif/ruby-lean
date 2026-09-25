import Denote.Rules.Singleton.SingletonDispatch
import Denote.Controls.ClassStateControls

/-! A boot-grounded class scope, actual singleton installation/entry, and the two owner
distinctions a future annotation-checked singleton rule must retain. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.SingletonInstallControls
open RubyCore Ratchet Ratchet.Denote

def body : Ratchet.Expr := .defs .self' "copy" [.req "value"] (.var .lvar "value")
def program : Ratchet.Expr := .class' "Factory" none body
def entry : Machine := match Interp.stepFn (evalFrom bootMachine program) with
  | .next m => m
  | _ => bootMachine
def k : ObjId := bootMachine.heap.objs.size
def e : ObjId := k + 1
def md : MethodDef := definedSingleton entry e [.req "value"] (.var .lvar "value")
def installed : Machine := installSingleton entry e "copy" [.req "value"] (.var .lvar "value")

theorem checked_scope_install (hb : bootOkB = true)
    (hn : constOwn bootMachine.heap Boot.objectId "Factory" = none) :
    ∃ m lexical owner, Interp.stepFn (evalFrom bootMachine program) = .next m ∧
      StateOk (classBodyCtx ctx0 "Factory") [] .ivar0 m ∧
      Interp.stepFn m = .next (Interp.withCtl (installSingleton m owner "copy"
        [.req "value"] (.var .lvar "value")) (.value (.sym "copy"))) ∧
      SingletonMethodCode lexical owner (definedSingleton m owner [.req "value"] (.var .lvar "value")) ∧
      Framed m (installSingleton m owner "copy" [.req "value"] (.var .lvar "value")) := by
  obtain ⟨m, hs, hm⟩ := boot_class_state (name := "Factory") (body := body) hb
    (by decide) hn (by decide)
  obtain ⟨ep, he, hstep⟩ := stepFn_class_fresh (body := body) (stateOk_boot hb) rfl hn (by decide)
  have hctl : m.ctl = .eval (toRuby body) := by
    rw [hstep] at hs
    cases hs
    rfl
  obtain ⟨lexical, owner, _, _, _, hinstall, hcode, hframe, _⟩ :=
    scoped_singleton_install hm rfl rfl hctl
  exact ⟨m, lexical, owner, hs, hm, hinstall, hcode, hframe⟩

#guard (constOwn bootMachine.heap Boot.objectId "Factory").isNone
#guard singletonMethodCodeB k e md
#guard !ordinaryMethodCodeB k [k, Boot.objectId] md
#guard !instanceMethodCodeB e "copy" md
#guard installed.heap.objs.size == entry.heap.objs.size
#guard (requiredFrame (.ref k) "copy" md ["value"] [.int 7]).defmod == e
#guard (requiredFrame (.ref k) "copy" md ["value"] [.int 7]).cref == [k, Boot.objectId]
#guard match Interp.run 160 (evalFrom bootMachine (.seq [program,
    .send (some (.const "Factory")) "copy" [.int 7] none])) with
  | .value (.int 7) _ => true
  | _ => false

-- Cached/rooted metaclasses may have prepends: an owned installed row need not win lookup.
def prepended : Ratchet.Expr := .seq [
  .module' "Cloak" (.def' "origin" [] (.int 99)),
  .class' "Factory" none (.seq [
    .sclass .self' (.send none "prepend" [.const "Cloak"] none),
    .defs .self' "origin" [] (.int 7)]),
  .send (some (.const "Factory")) "origin" [] none]
#guard match Interp.run 300 (evalFrom bootMachine prepended) with
  | .value (.int 99) m => match classNamed? m.heap "Factory" with
    | some owner => metaReadyB m.heap owner &&
        ((m.heap.get owner).eigen.any fun eigen => !classFrontB m.heap eigen)
    | none => false
  | _ => false

#print axioms checked_scope_install
end Ratchet.Denote.Typed.SingletonInstallControls
