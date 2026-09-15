import Denote.Typed.SubclassRule
import Denote.Typed.ConstructorGeneralControls
import Denote.Typed.Bridge

/-! A full checked superclass/body/return composition with distinct local environments
and a newly installed annotated method. Inherited constructor calls remain model probes
until receiver-aware initializer/body caches are integrated into the checker. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.SubclassRunControls
open RubyCore Ratchet Ratchet.Denote

private def parent : Cls := classWithMethod FlagBox.header FlagBox.init
private def parentCache : CheckedCache := { initializers := [
  ⟨initializerBodyCtx FlagBox.callerCtx "FlagBox", "FlagBox", "FlagBox", FlagBox.init,
    FlagBox.finalInit, .var .lvar "flag"⟩] }
private def superclass : Ratchet.Expr := .seq [
  .class' "Sibling" none (.int 1),
  .vasgn .lvar "saved" (.str "caller"), .const "FlagBox"]
private def superCert : Certified [] superclass FlagBox.callerCtx .ivar0 :=
  (check 80 [] superclass (.seq [
    .classDecl "Sibling" none (.intLit 1),
    .vasgn .lvar "saved" (.strLit "caller"), .constCls "FlagBox"])
    FlagBox.callerCtx .ivar0 parentCache).get (by decide +kernel)

private def headerCtx : Ctx :=
  subclassHeaderCtx (classBodyCtx superCert.ctx "FlagChild") "FlagChild" "FlagBox"
private def answer : Ratchet.Expr := .def' "answer" [.req "flag"] (.var .lvar "flag")
private def body : Ratchet.Expr := .seq [.vasgn .lvar "saved" (.int 9), answer]
private def hint (input ret : Ty) : Deriv := .seq [
  .vasgn .lvar "saved" (.intLit 9), .defDecl "answer" [("flag", input)] ret (.var .lvar "flag")]
private def bodyCert : Certified [] body headerCtx .ivar0 :=
  (check 80 [] body (hint .bool .bool) headerCtx .ivar0 superCert.cache).get (by decide +kernel)
private def callerCtx : Ctx := returnScopeCtx superCert.ctx bodyCert.ctx
private def child : Ratchet.Expr := .class' "FlagChild" (some superclass) body

#guard (check 80 [] body (hint .bool .bool) headerCtx).isNone
#guard (check 80 [] body (hint .bool .int) headerCtx .ivar0 superCert.cache).isNone
#guard (check 80 [] body (hint (.nilable .bool) .bool) headerCtx .ivar0 superCert.cache).isNone
#guard (envGet? superCert.out "saved") == some (.cls "String")
#guard (envGet? bodyCert.out "saved") == some .int
#guard (mroGet? callerCtx.classes "FlagChild" "answer").any (fun (owner, _) => owner == "FlagChild")
#guard (clsGet? callerCtx.classes "Sibling").isSome

theorem child_sem : SemSafeCtxA FlagBox.callerCtx [] .ivar0 child .sym callerCtx
    [("saved", .cls "String")] .ivar0 := by
  have hc : parent ∈ superCert.ctx.classes := by
    let f := (findClass "FlagBox" superCert.ctx.classes).get (by decide +kernel)
    have he : f.cls = parent := clsEqB_sound _ _ (by decide +kernel)
    exact he ▸ f.member
  have hs := certified_context superCert
  have hp : superCert.ty = .clsOf "FlagBox" ∧ superCert.out = [("saved", .cls "String")] ∧
      superCert.spine = .ivar0 := by decide +kernel
  rw [hp.1, hp.2.1, hp.2.2] at hs
  have hb := certified_context bodyCert
  have hq : bodyCert.ty = .sym ∧ bodyCert.spine = .ivar0 := by decide +kernel
  rw [hq.1, hq.2] at hb
  exact SemSafeCtxA.subclassDecl (c := parent) hs hc hb (by decide +kernel)

private def program : Ratchet.Expr := .seq [FlagBox.program, child, .var .lvar "saved"]

/-- The parent initializer, superclass-expression class and child method are all checked.
The superclass changes Ctx and creates a String local; the child's Integer shadow stays local. -/
theorem boot_run (hb : bootOkB = true) :
    RunSpec bootMachine (evalFrom bootMachine program) [("saved", .cls "String")]
      (.cls "String") callerCtx .ivar0 :=
  (FlagBox.class_run (stateOk_boot hb)).thenSeq (.cons child_sem (.last (SemSafeCtxA.var rfl rfl)))

theorem returned_world (hb : bootOkB = true) {fuel rest : Nat} {v : Value} {m : Machine}
    (hr : runA fuel (evalFrom bootMachine program) = .ans (.val v) m rest) :
    StateOk callerCtx [("saved", .cls "String")] .ivar0 m ∧ denM (.cls "String") m v :=
  ⟨((boot_run hb).2 fuel (.val v) m rest hr).2.2 v rfl,
    ((boot_run hb).2 fuel (.val v) m rest hr).2.1⟩

private def childClass : Cls := classWithMethod (subclassHeader "FlagChild" "FlagBox")
  ⟨"answer", [.req "flag"], .var .lvar "flag"⟩
private def leafBodyCtx : Ctx := subclassHeaderCtx (classBodyCtx callerCtx "FlagLeaf") "FlagLeaf" "FlagChild"
private def leafCtx : Ctx := returnScopeCtx callerCtx leafBodyCtx
private def leaf : Ratchet.Expr := .class' "FlagLeaf" (some (.const "FlagChild")) .nil

theorem leaf_sem : SemSafeCtxA callerCtx [("saved", .cls "String")] .ivar0 leaf .nilT leafCtx
    [("saved", .cls "String")] .ivar0 := by
  have hc : childClass ∈ callerCtx.classes := by
    let f := (findClass "FlagChild" callerCtx.classes).get (by decide +kernel)
    have he : f.cls = childClass := clsEqB_sound _ _ (by decide +kernel)
    exact he ▸ f.member
  exact SemSafeCtxA.subclassDecl (SemSafeCtxA.constClass hc) hc SemSafeCtxA.nilLit (by decide +kernel)

theorem boot_multilevel_run (hb : bootOkB = true) :
    RunSpec bootMachine (evalFrom bootMachine (.seq [FlagBox.program, child, leaf, .var .lvar "saved"]))
      [("saved", .cls "String")] (.cls "String") leafCtx .ivar0 :=
  (FlagBox.class_run (stateOk_boot hb)).thenSeq
    (.cons child_sem (.cons leaf_sem (.last (SemSafeCtxA.var rfl rfl))))

#guard match Interp.run 180 (evalFrom bootMachine program) with
  | .value v m => Builtins.strPayload? m.heap v == some "caller" &&
      classChainsB callerCtx.classes m.heap && classOwnNamesB callerCtx.classes m.heap &&
      (classNamed? m.heap "Sibling").isSome &&
      (classNamed? m.heap "FlagChild").any (fun k =>
        (Interp.methodOn m.heap k "answer").any (fun (owner, _) => owner == k))
  | _ => false

-- These exercise actual new/initialize/answer dispatch, without claiming checker
-- admission of inherited constructor calls before their full-domain cache proof exists.
private def call (args : List Ratchet.Expr) : Ratchet.Expr :=
  .send (some (.send (some (.const "FlagChild")) "new" args none)) "answer" [.fls] none
#guard match Interp.run 200 (evalFrom bootMachine (.seq [FlagBox.program, child, call [.tru]])) with
  | .value (.bool false) _ => true
  | _ => false
#guard match Interp.run 200 (evalFrom bootMachine (.seq [FlagBox.program, child, call []])) with
  | .uncaught exc m => isAName m.heap exc "ArgumentError"
  | _ => false

#guard match Interp.run 220 (evalFrom bootMachine (.seq [FlagBox.program, child, leaf, .var .lvar "saved"])) with
  | .value v m => Builtins.strPayload? m.heap v == some "caller" && classChainsB leafCtx.classes m.heap
  | _ => false

#print axioms child_sem
#print axioms boot_run
#print axioms returned_world
#print axioms leaf_sem
#print axioms boot_multilevel_run
end Ratchet.Denote.Typed.SubclassRunControls
