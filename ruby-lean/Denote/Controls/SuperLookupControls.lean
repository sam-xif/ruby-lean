import Denote.Rules.Super.SuperDispatch
import Denote.Bridge

/-! Super routes skip the defining owner, retain intermediate overrides, and cannot use
an unrelated or absent owner. Positive rows alone do not prove a super target. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.SuperLookupControls
open RubyCore Ratchet Ratchet.Denote

def echo (s : String) : Defn := ⟨"echo", [], .str s⟩
def root : Cls := classWithMethod (classHeader "Depot") (echo "root")
def middle : Cls := classWithMethod (subclassHeader "Relay" "Depot") (echo "middle")
def leaf : Cls := subclassHeader "Satellite" "Relay"
def table : CTable := [leaf, middle, root]
def gap : Cls := subclassHeader "Gap" "Depot"
#guard (superRoute? [leaf, { middle with super? := some "Gap" }, gap, root]
  "Satellite" "Relay" "Depot" (echo "root")).isSome

-- Ordinary lookup hits Relay; super from Relay skips its own override.
#guard (memberRoute? table "Satellite" "Relay" (echo "middle")).isSome
#guard (memberRoute? table "Satellite" "Depot" (echo "root")).isNone
#guard (superRoute? table "Satellite" "Relay" "Depot" (echo "root")).isSome
#guard (superRoute? table "Satellite" "Satellite" "Relay" (echo "middle")).isSome
#guard (superRoute? table "Satellite" "Satellite" "Depot" (echo "root")).isNone
#guard (superRoute? table "Satellite" "Relay" "Relay" (echo "middle")).isNone
#guard (superRoute? table "Satellite" "Missing" "Depot" (echo "root")).isNone
#guard (superRoute? table "Missing" "Relay" "Depot" (echo "root")).isNone
#guard (superRoute? table "Satellite" "Depot" "Relay" (echo "middle")).isNone
#guard (superRoute? [subclassHeader "Cycle" "Cycle", root] "Cycle" "Cycle" "Depot" (echo "root")).isNone
-- Every retained record contributes to absence; a newer empty record cannot hide Relay.
#guard (superRoute? (subclassHeader "Relay" "Depot" :: table)
  "Satellite" "Satellite" "Depot" (echo "root")).isNone

def definitions : Ratchet.Expr := .seq [
  .class' "Depot" none (.def' "echo" [] (.str "root")),
  .class' "Gap" (some (.const "Depot")) .nil,
  .class' "Relay" (some (.const "Gap")) (.def' "echo" [] (.str "middle")),
  .class' "Satellite" (some (.const "Relay")) .nil]
def hint : Deriv := .seq [
  .classDecl "Depot" none (.defDecl "echo" [] (.cls "String") (.strLit "root")),
  .classDecl "Gap" (some "Depot") .nilLit,
  .classDecl "Relay" (some "Gap") (.defDecl "echo" [] (.cls "String") (.strLit "middle")),
  .classDecl "Satellite" (some "Relay") .nilLit]
def checked : Certified [] definitions := (check fuelD [] definitions hint).get (by decide +kernel)
def route : SuperRoute checked.ctx.classes "Satellite" "Relay" "Depot" (echo "root") :=
  (superRoute? checked.ctx.classes "Satellite" "Relay" "Depot" (echo "root")).get (by decide +kernel)

/-- Actual checked definitions supply all code/absence/chain evidence. No physical
superFound equality is assumed, including when the receiver inherits the current body. -/
theorem after_definitions (hb : bootOkB = true) {fuel rest : Nat} {v : Value} {m : Machine}
    {r current : ObjId}
    (hr : runA fuel (evalFrom bootMachine definitions) = .ans (.val v) m rest)
    (hn : classNamed? m.heap "Satellite" = some r)
    (hc : classNamed? m.heap "Relay" = some current) :
    ∃ k md, classNamed? m.heap "Depot" = some k ∧
      Interp.superFound m.heap r current "echo" = some (k, md) ∧
      md.params = [] ∧ md.body = .str "root" ∧ md.undefined = false ∧ InstanceMethodCode k "echo" md := by
  have hs := certified_context checked
  have ho : checked.out = [] ∧ checked.spine = .ivar0 := by decide +kernel
  rw [ho.1, ho.2] at hs
  have hm := ((hs bootMachine (stateOk_boot hb)).2 fuel (.val v) m rest hr).2.2 v rfl
  have hl : leaf ∈ checked.ctx.classes := by
    let f := (findClass "Satellite" checked.ctx.classes).get (by decide +kernel)
    have he : f.cls = leaf := clsEqB_sound _ _ (by decide +kernel)
    exact he ▸ f.member
  exact declared_super_code hm hl hn hc route

#guard match Interp.run 160 (evalFrom bootMachine definitions) with
  | .value _ m => match classNamed? m.heap "Satellite", classNamed? m.heap "Relay",
      classNamed? m.heap "Depot" with
    | some r, some current, some k =>
      (Interp.superFound m.heap r current "echo").any (fun (o, md) =>
        o == k && md.body == .str "root") &&
      (Interp.methodOn m.heap r "echo").any (fun (o, _) => o == current)
    | _, _, _ => false
  | _ => false

-- A real inherited method activation dispatches super to Depot on the same instance.
#guard match Interp.run 200 (evalFrom bootMachine (.seq [definitions,
    .send (some (.const "Satellite")) "new" [] none])) with
  | .value recv m => match lookup m.heap recv "echo" with
    | some (_, md) => match Interp.enterUserMethod m recv "echo" md [] none with
      | .next n => match Interp.doSuper n [] none with
        | .next p => p.currentFrame.self.identEq recv && p.heap.objs.size == n.heap.objs.size &&
          match Interp.run 40 p with
          | .value v last => Builtins.strPayload? last.heap v == some "root"
          | _ => false
        | _ => false
      | _ => false
    | none => false
  | _ => false

-- A name and nominal receiver alone permit a block frame; methodFrameOf follows home.
-- The strengthened FrameOk excludes this counterexample.
def blockActivation : Machine := pushMethodFrame (Machine.init .nil)
  { self := .ref Boot.mainId, defmod := Boot.objectId, kind := .block, home := 0, meth := "echo" }
example : blockActivation.currentFrame.meth = "echo" ∧
    isAName blockActivation.heap blockActivation.currentFrame.self "Object" = true := by
  decide +kernel
example : ¬ FrameOk (some ⟨"Object", "Object", "echo"⟩) blockActivation := by
  unfold FrameOk
  decide +kernel
#guard blockActivation.currentFrame.meth == "echo"
#guard (blockActivation.frames.getD (Interp.methodFrameOf blockActivation) default).meth == ""
#guard match Interp.doSuper blockActivation [] none with
  | .unsupported why => why == "super outside a method"
  | _ => false

#print axioms after_definitions
end Ratchet.Denote.Typed.SuperLookupControls
