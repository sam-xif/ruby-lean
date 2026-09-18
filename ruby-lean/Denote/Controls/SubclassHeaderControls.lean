import Denote.Rules.Subclass.SubclassHeaderEntry
import Denote.Controls.SubclassStateControls
import Denote.Controls.ConstructorGeneralControls

/-! Headers after an annotation-checked parent initializer, plus real inherited constructor
calls. Plain allocation does not entail zero arity or an initializer result type. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.SubclassHeaderControls
open RubyCore Ratchet Ratchet.Denote

private def parentClass : Cls := classWithMethod FlagBox.header FlagBox.init
private def childCtx : Ctx := subclassHeaderCtx (classBodyCtx FlagBox.callerCtx "FlagChild") "FlagChild" "FlagBox"

private theorem tables (m : Machine) : ClassTablesFrame FlagBox.callerCtx "FlagChild" m := by
  refine ⟨?_, ?_, ?_⟩
  · intro cn τ ht
    change (none : Option Ty) = some τ at ht
    cases ht
  · intro owner cn τ ht; cases ht
  · intro owner cn c ht
    have hne := unqualifiedClassB_ne_path (by decide : unqualifiedClassB "FlagBox" = true) owner cn
    change clsGet? [parentClass, FlagBox.header] (owner ++ "::" ++ cn) = some c at ht
    simp [clsGet?, parentClass, classWithMethod, FlagBox.header, classHeader, hne] at ht

/-- No parent signature is a premise: its full annotation-domain body proof is consumed
by class_run before any resulting state can feed the generic child-header theorem. -/
theorem header_after_checked_initializer (hb : bootOkB = true) {m : Machine} {fuel rest : Nat} {v : Value}
    (hresult : runA fuel (evalFrom bootMachine FlagBox.program) = .ans (.val v) m rest)
    (body : RubyCore.Expr) :
    ∃ parent n, classNamed? m.heap "FlagBox" = some parent ∧
      Interp.enterClassBody m "FlagChild" false (some parent) body = .next n ∧
      StateOk childCtx [] .ivar0 n := by
  have hm := ((FlagBox.class_run (stateOk_boot hb)).2 fuel (.val v) m rest hresult).2.2 v rfl
  have hc : parentClass ∈ FlagBox.callerCtx.classes := List.mem_cons_self
  obtain ⟨parent, hp, _⟩ := hm.classes parentClass hc
  obtain ⟨n, he, hs⟩ := Subclass.enter_declared_header hm rfl rfl rfl (tables m) (by decide) hc hp
    (by decide) (by decide) (by decide) (by decide) (by constructor <;> decide)
    (by decide) (by decide) (by decide) (body := body)
  exact ⟨parent, n, hp, he, hs⟩

private def child : Ratchet.Expr := .class' "FlagChild" (some (.const "FlagBox")) .nil
private def grandchild : Ratchet.Expr := .class' "FlagLeaf" (some (.const "FlagChild")) .nil
private def make (cn : String) (args : List Ratchet.Expr) : Ratchet.Expr :=
  .send (some (.const cn)) "new" args none

#guard subclassHeaderFrameB FlagBox.callerCtx.classes "FlagChild" "FlagBox"
#guard (ctorGet? childCtx.classes "FlagChild").any fun (owner, decl) =>
  owner == "FlagBox" && decl.name == "initialize" && decl.params.length == 1
#guard (ownNames childCtx.classes "FlagChild").isEmpty

-- The initializer returns a Boolean, but Class#new must return the child instance.
#guard match Interp.run 150 (evalFrom bootMachine (.seq [FlagBox.program, child,
    make "FlagChild" [.fls]])) with
  | .value v m => isExactInst m.heap v "FlagChild"
  | _ => false
#guard match Interp.run 150 (evalFrom bootMachine (.seq [FlagBox.program, child,
    make "FlagChild" []])) with
  | .uncaught exc m => isAName m.heap exc "ArgumentError"
  | _ => false

-- The same empty-header transport handles a multi-level parent and preserves real MRO.
#guard match Interp.run 180 (evalFrom bootMachine (.seq [FlagBox.program, child, grandchild,
    make "FlagLeaf" [.tru]])) with
  | .value v m => isExactInst m.heap v "FlagLeaf" &&
      classChainsB (subclassHeader "FlagLeaf" "FlagChild" :: childCtx.classes) m.heap &&
      classOwnNamesB (subclassHeader "FlagLeaf" "FlagChild" :: childCtx.classes) m.heap
  | _ => false

#print axioms header_after_checked_initializer
end Ratchet.Denote.Typed.SubclassHeaderControls
