import Denote.Typed.Run

/-! Dispatch and representation facts for the primitive rows. -/

set_option autoImplicit false
set_option maxRecDepth 4000
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem primitive_lookup {Γ : Env} {m : Machine} (hm : StateOk ctx0 Γ .ivar0 m)
    {k : ObjId} {name bid : String} (hr : (k, name, bid) ∈ primitiveMethods) :
    ∃ owner md, Interp.methodOn m.heap k name = some (owner, md) ∧
      md.builtin = some bid ∧ md.undefined = false ∧ md.visibility = .pub ∧
      md.fromPrelude = false ∧
      Interp.crubyShadow m.heap ((ancestors m.heap k).takeWhile (fun x => x != owner)) name = none := by
  have hp := List.all_eq_true.mp hm.primitiveDispatch (k, name, bid) hr
  have hf : nameFreeN ctx0 name = true := by rfl
  simp only [hf, Bool.not_true, Bool.false_or] at hp
  cases hl : Interp.methodOn m.heap k name with
  | none => rw [hl] at hp; cases hp
  | some p =>
    obtain ⟨owner, md⟩ := p
    refine ⟨owner, md, rfl, ?_⟩
    simpa only [hl, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
      Option.isNone_iff_eq_none, and_assoc] using hp

theorem string_class {Γ : Env} {m : Machine} {v : Value}
    (hm : StateOk ctx0 Γ .ivar0 m) (hd : denM (.cls "String") m v) :
    classOf m.heap v = Boot.stringId := by
  have ha : (ancestors m.heap (classOf m.heap v)).contains Boot.stringId = true := by
    simpa only [denM, isAName, isA, hm.core.stringNamed] using hd
  have hb := hm.baseChains Boot.stringId (["String", "Comparable"] ++ rootAncestors)
    (by simp [builtinBases])
  exact (hb.2 (by rfl)).2 _ ha

theorem string_payload {Γ : Env} {m : Machine} {v : Value}
    (hm : StateOk ctx0 Γ .ivar0 m) (hd : denM (.cls "String") m v) :
    ∃ o s, v = .ref o ∧ (m.heap.get o).payload = .str s := by
  have hc := string_class hm hd
  cases v with
  | ref o =>
    obtain ⟨s, hs⟩ := hm.stringPayload o hc
    exact ⟨o, s, rfl, hs⟩
  | bool b => cases b <;> cases hc
  | int n => cases hc
  | flt x => cases hc
  | sym s => cases hc
  | nil => cases hc

theorem int_add_run (m : Machine) (x y : Int) :
    Builtins.run "Integer#+" (.int x) [.int y] m = .ok (.int (x + y)) m := by rfl
theorem int_sub_run (m : Machine) (x y : Int) :
    Builtins.run "Integer#-" (.int x) [.int y] m = .ok (.int (x - y)) m := by rfl
theorem int_mul_run (m : Machine) (x y : Int) :
    Builtins.run "Integer#*" (.int x) [.int y] m = .ok (.int (x * y)) m := by rfl
theorem int_div_run (m : Machine) (x y : Int) :
    Builtins.run "Integer#/" (.int x) [.int y] m =
      (if y == 0 then .err Boot.zeroDivisionErrorId "divided by 0" m
       else .ok (.int (Int.fdiv x y)) m) := by rfl
theorem int_lt_run (m : Machine) (x y : Int) :
    Builtins.run "Integer#<" (.int x) [.int y] m = .ok (.bool (compare x y == .lt)) m := by rfl
theorem bool_not_run (m : Machine) (x : Bool) :
    Builtins.run "Object#!" (.bool x) [] m = .ok (.bool (!x)) m := by cases x <;> rfl

theorem invokeDispatch_builtin {site : SendSite} {m : Machine} {recv : Value} {name bid : String}
    {args : List Value} {owner : ObjId} {md : MethodDef}
    (hl : lookup m.heap recv name = some (owner, md))
    (hb : md.builtin = some bid) (hu : md.undefined = false) (hv : md.visibility = .pub)
    (hp : md.fromPrelude = false)
    (hs : Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap recv)).takeWhile (fun x => x != owner)) name = none)
    (hd : Builtins.deferTwin? m.heap bid recv args = none) (hn : (bid == "Object#raise") = false) :
    Interp.invoke.invokeDispatch m recv site name args none [] =
      match Builtins.run bid recv args m with
      | .ok v n => .next (Interp.withCtl n (.value v))
      | .err cls msg n => .next (Interp.raiseErr n cls msg)
      | .throwV v n => .next (Interp.withCtl n (.jump (.raiseJ v)))
      | .unsupported r => .unsupported r := by
  have hvis : Interp.visError? m recv site md name = none := by
    cases site <;> simp [Interp.visError?, hv]
  simp only [Interp.invoke.invokeDispatch, hl, hu, hp, Bool.false_eq_true, ↓reduceIte,
    hs, hvis, hb, hd, hn, Option.isSome, Bool.false_and,
    Interp.appendKwHash, List.isEmpty, ↓reduceIte]
  cases Builtins.run bid recv args m <;> rfl

#print axioms primitive_lookup
#print axioms invokeDispatch_builtin
end Ratchet.Denote.Typed
