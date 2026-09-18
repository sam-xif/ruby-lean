import Denote.Rules.Constructor.DefaultConstructor
import Denote.Bridge
import Denote.Rules.Constructor.ConstructorLookup

/-! Annotation-checked classes feeding default allocation, and the full-state root
initializer omission witness. These controls do not admit a new checker rule. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.DefaultConstructorControls
open RubyCore Ratchet Ratchet.Denote

def base : Ratchet.Expr := .class' "Depot" none (.def' "answer" [] (.str "ready"))
def child : Ratchet.Expr := .class' "Satellite" (some (.const "Depot")) .nil
def definitions : Ratchet.Expr := .seq [base, child]
def hint : Deriv := .seq [.classDecl "Depot" none
  (.defDecl "answer" [] (.cls "String") (.strLit "ready")), .classDecl "Satellite" (some "Depot") .nilLit]
def checked : Certified [] definitions := (check fuelD [] definitions hint).get (by decide +kernel)
def childClass : Cls := subclassHeader "Satellite" "Depot"
def newExpr (args : List Ratchet.Expr := []) : Ratchet.Expr :=
  .send (some (.const "Satellite")) "new" args none
def useExpr : Ratchet.Expr := .send (some (newExpr [])) "answer" [] none

theorem after_checked_definitions (hb : bootOkB = true) {fuel rest : Nat} {v : Value} {m : Machine}
    (hr : runA fuel (evalFrom bootMachine definitions) = .ans (.val v) m rest) :
    StateOk checked.ctx [] .ivar0 m := by
  have hs := certified_context checked
  have ho : checked.out = [] ∧ checked.spine = .ivar0 := by decide +kernel
  rw [ho.1, ho.2] at hs
  exact ((hs bootMachine (stateOk_boot hb)).2 fuel (.val v) m rest hr).2.2 v rfl

theorem default_after_definitions (hb : bootOkB = true) {fuel rest : Nat} {v : Value} {m : Machine}
    {k owner : ObjId} {md : MethodDef}
    (hr : runA fuel (evalFrom bootMachine definitions) = .ans (.val v) m rest)
    (hn : classNamed? m.heap "Satellite" = some k)
    (hnew : Interp.methodOn m.heap (classOf m.heap (.ref k)) "new" = some (owner, md))
    (hk : m.kont = []) :
    StepSpec m [] (.inst "Satellite" .ivar0)
      (Interp.finishSend m (.ref k) .explicit "new" [] .none) checked.ctx .ivar0 := by
  have hc : childClass ∈ checked.ctx.classes := by
    let f := (findClass "Satellite" checked.ctx.classes).get (by decide +kernel)
    have he : f.cls = childClass := clsEqB_sound _ _ (by decide +kernel)
    exact he ▸ f.member
  exact declared_default_constructor (after_checked_definitions hb hr) hc hn
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hnew hk

#guard validateD definitions hint
#guard noDeclaredSelectorB checked.ctx.classes "Satellite" "initialize"
#guard !noDeclaredSelectorB checked.ctx.classes "Satellite" "answer"
#guard !noDeclaredSelectorB checked.ctx.classes "Unknown" "initialize"
#guard !noDeclaredSelectorB [subclassHeader "Cycle" "Cycle"] "Cycle" "initialize"
#guard !noDeclaredSelectorB [subclassHeader "Child" "Base",
  classWithMethod (classHeader "Base") ⟨"initialize", [.req "x"], .var .lvar "x"⟩] "Child" "initialize"
#guard match Interp.run 160 (evalFrom bootMachine (.seq [definitions, useExpr])) with
  | .value v m => Builtins.strPayload? m.heap v == some "ready"
  | _ => false
#guard match Interp.run 160 (evalFrom bootMachine (.seq [definitions, newExpr [.int 1]])) with
  | .uncaught exc m => isAName m.heap exc "ArgumentError"
  | _ => false
-- Positive new dispatch and rule integration still precede checker admission.
#guard !validateD (.seq [definitions, newExpr []])
  (.seq [hint, .newInst "Satellite" [] (.inst "Satellite" .ivar0)])

def hiddenInit : MethodDef :=
  { owner := Boot.objectId, params := [.req "x"], body := .var .lvar "x",
    cref := [Boot.objectId], fromPrelude := true }
def hiddenRoot : Machine :=
  { bootMachine with heap := defineMethod bootMachine.heap Boot.objectId "initialize" hiddenInit }

-- The complete previous gate passes; the new root-initializer clause excludes this heap.
#guard bootStateBaseB hiddenRoot
#guard !bootStateB hiddenRoot
#guard (Interp.userInit? bootMachine.heap Boot.objectId).isNone
#guard (Interp.userInit? hiddenRoot.heap Boot.objectId).isSome

theorem hidden_root_full_state (hb : bootStateBaseB hiddenRoot = true) :
    StateCore ctx0 [] .ivar0 hiddenRoot ∧ ClassOwnNames ctx0.classes hiddenRoot.heap ∧
      ClassChains ctx0.classes hiddenRoot.heap ∧ Interp.userInit? hiddenRoot.heap Boot.objectId = some hiddenInit := by
  have hm := stateCore_of_bootStateBaseB hb
  have hl : (bootMachine.heap.classPayload? Boot.objectId).isSome = true := by
    simpa only [hiddenRoot, Proof.classPayload?_isSome_defineMethod] using (hm.runtime rfl).classLive
  have hp := ownMethod_defineMethod_self bootMachine.heap Boot.objectId "initialize" hiddenInit hl
  have hr := methodOn_own_first hm.core.classReady.objectChain hp
  exact ⟨hm, ClassOwnNames.empty _, ClassChains.empty _, by simp only [Interp.userInit?, hr]; rfl⟩

theorem hidden_root_not_state (hb : bootStateBaseB hiddenRoot = true) : ¬ StateOk ctx0 [] .ivar0 hiddenRoot := by
  intro hm
  have hi := hm.rootInit (by rfl)
  rw [(hidden_root_full_state hb).2.2.2] at hi
  cases hi

-- Same checked definitions, same empty declared initializer prefix; actual new now fails.
#guard match Interp.run 160 (evalFrom hiddenRoot (.seq [definitions, useExpr])) with
  | .uncaught exc m => isAName m.heap exc "ArgumentError"
  | _ => false

#print axioms after_checked_definitions
#print axioms default_after_definitions
#print axioms hidden_root_full_state
#print axioms hidden_root_not_state
end Ratchet.Denote.Typed.DefaultConstructorControls
