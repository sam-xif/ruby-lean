import Denote.Judgment.Run

/-! Dispatch and representation facts for the primitive rows. -/

set_option autoImplicit false
set_option maxRecDepth 4000
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem primitive_lookup {κ : Ctx} {I : Ty} {Γ : Env} {m : Machine} (hm : StateOk κ Γ I m)
    {k : ObjId} {name bid : String} (hr : (k, name, bid) ∈ primitiveMethods)
    (hf : nameFreeN κ name = true := by
  simp only [Builtins.run, List.any_cons, List.any_nil,
    Builtins.unrepresentableByteStr, Builtins.strPayload?, Builtins.complexEqualityImpure,
    Bool.false_or, Bool.or_false, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl) :
    ∃ owner md, Interp.methodOn m.heap k name = some (owner, md) ∧
      md.builtin = some bid ∧ md.undefined = false ∧ md.visibility = .pub ∧
      md.fromPrelude = false ∧
      Interp.crubyShadow m.heap ((ancestors m.heap k).takeWhile (fun x => x != owner)) name = none :=
  dispatch_lookup hm.primitiveDispatch (List.mem_append_left _ hr) hf

theorem string_class {κ : Ctx} {I : Ty} {Γ : Env} {m : Machine} {v : Value}
    (hm : StateOk κ Γ I m) (hd : denM (.cls "String") m v)
    (hg : isANoOk κ.wholeCls (["String", "Comparable"] ++ rootAncestors) = true := by
  simp only [Builtins.run, List.any_cons, List.any_nil,
    Builtins.unrepresentableByteStr, Builtins.strPayload?, Builtins.complexEqualityImpure,
    Bool.false_or, Bool.or_false, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl) :
    classOf m.heap v = Boot.stringId := by
  have ha : (ancestors m.heap (classOf m.heap v)).contains Boot.stringId = true := by
    simpa only [denM, isAName, isA, hm.core.stringNamed] using hd
  have hb := hm.baseChains Boot.stringId (["String", "Comparable"] ++ rootAncestors)
    (by simp [builtinBases])
  exact (hb.2 hg).2 _ ha

theorem string_payload {κ : Ctx} {I : Ty} {Γ : Env} {m : Machine} {v : Value}
    (hm : StateOk κ Γ I m) (hd : denM (.cls "String") m v)
    (hg : isANoOk κ.wholeCls (["String", "Comparable"] ++ rootAncestors) = true := by
  simp only [Builtins.run, List.any_cons, List.any_nil,
    Builtins.unrepresentableByteStr, Builtins.strPayload?, Builtins.complexEqualityImpure,
    Bool.false_or, Bool.or_false, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl) :
    ∃ o s, v = .ref o ∧ (m.heap.get o).payload = .str s := by
  have hc := string_class hm hd hg
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
    Builtins.run "Integer#+" (.int x) [.int y] m = .ok (.int (x + y)) m := by
  simp only [Builtins.run, List.any_cons, List.any_nil,
    Builtins.unrepresentableByteStr, Builtins.strPayload?, Builtins.complexEqualityImpure,
    Bool.false_or, Bool.or_false, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl
theorem int_sub_run (m : Machine) (x y : Int) :
    Builtins.run "Integer#-" (.int x) [.int y] m = .ok (.int (x - y)) m := by
  simp only [Builtins.run, List.any_cons, List.any_nil,
    Builtins.unrepresentableByteStr, Builtins.strPayload?, Builtins.complexEqualityImpure,
    Bool.false_or, Bool.or_false, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl
theorem int_mul_run (m : Machine) (x y : Int) :
    Builtins.run "Integer#*" (.int x) [.int y] m = .ok (.int (x * y)) m := by
  simp only [Builtins.run, List.any_cons, List.any_nil,
    Builtins.unrepresentableByteStr, Builtins.strPayload?, Builtins.complexEqualityImpure,
    Bool.false_or, Bool.or_false, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl
theorem int_div_run (m : Machine) (x y : Int) :
    Builtins.run "Integer#/" (.int x) [.int y] m =
      (if y == 0 then .err Boot.zeroDivisionErrorId "divided by 0" m
       else .ok (.int (Int.fdiv x y)) m) := by
  simp only [Builtins.run, List.any_cons, List.any_nil,
    Builtins.unrepresentableByteStr, Builtins.strPayload?, Builtins.complexEqualityImpure,
    Bool.false_or, Bool.or_false, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  cases x with
  | ofNat n => cases n with
    | zero => rfl
    | succ n => cases n <;> rfl
  | negSucc n => rfl
theorem int_lt_run (m : Machine) (x y : Int) :
    Builtins.run "Integer#<" (.int x) [.int y] m = .ok (.bool (compare x y == .lt)) m := by
  simp only [Builtins.run, List.any_cons, List.any_nil,
    Builtins.unrepresentableByteStr, Builtins.strPayload?, Builtins.complexEqualityImpure,
    Bool.false_or, Bool.or_false, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl
theorem int_gt_run (m : Machine) (x y : Int) :
    Builtins.run "Integer#>" (.int x) [.int y] m = .ok (.bool (compare x y == .gt)) m := by
  simp only [Builtins.run, List.any_cons, List.any_nil,
    Builtins.unrepresentableByteStr, Builtins.strPayload?, Builtins.complexEqualityImpure,
    Bool.false_or, Bool.or_false, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl
theorem bool_not_run (m : Machine) (x : Bool) :
    Builtins.run "Object#!" (.bool x) [] m = .ok (.bool (!x)) m := by
  cases x <;>
    simp only [Builtins.run, List.any_cons, List.any_nil,
      Builtins.unrepresentableByteStr, Builtins.strPayload?, Builtins.complexEqualityImpure,
      Bool.false_or, Bool.or_false, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte] <;> rfl

theorem int_to_s_run (m : Machine) (x : Int) :
    Builtins.run "Integer#to_s" (.int x) [] m =
      Builtins.okStrEnc m false (toString x) := by
  simp only [Builtins.run, List.any_cons, List.any_nil,
    Builtins.unrepresentableByteStr, Builtins.strPayload?, Builtins.complexEqualityImpure,
    Bool.false_or, Bool.or_false, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem invokeDispatch_builtin {site : SendSite} {m : Machine} {recv : Value} {name bid : String}
    {args : List Value} {owner : ObjId} {md : MethodDef}
    (hl : lookup m.heap recv name = some (owner, md))
    (hb : md.builtin = some bid) (hu : md.undefined = false) (hv : md.visibility = .pub)
    (hp : md.fromPrelude = false)
    (hs : Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap recv)).takeWhile (fun x => x != owner)) name = none)
    (hd : Builtins.deferTwin? m.heap bid recv args = none) (hn : (bid == "Object#raise") = false)
    (hc : Interp.procCallBid bid = false := by rfl)
    (hm : Interp.arrayMapBid bid = false := by rfl)
    (hentry : (bid.startsWith "Main#" ||
      ["Object#inspect", "Object#raise", "Object#fail", "Exception.exception",
       "Exception#exception", "Exception#to_s", "UncaughtThrowError#to_s",
       "Object#initialize_dup", "Object#initialize_clone", "String#initialize_copy",
       "Array#initialize_copy", "Hash#initialize_copy", "Class#new", "Module#new",
       "Class#allocate", "Module#const_set", "Class#initialize", "Module#initialize",
       "String#initialize", "Array#initialize", "Hash#initialize", "Exception#initialize",
       "Object#__forwardable_compile", "String#+"].contains bid ||
      Interp.nativeDupBid bid || Interp.nativeCloneBid bid || Interp.requireBid bid ||
      Interp.enumBid bid || Interp.nativeIteratorBid bid) = false := by decide +kernel) :
    Interp.invoke.invokeDispatch m recv site name args none [] =
      match Builtins.run bid recv args m with
      | .ok v n => .next (Interp.withCtl n (.value v))
      | .err cls msg n => .next (Interp.raiseErr n cls msg)
      | .throwV v n => .next (Interp.withCtl n (.jump (.raiseJ v)))
      | .frozen recv n => Interp.raiseFrozen n recv
      | .unsupported r => .unsupported r := by
  have hvis : Interp.visError? m recv site md name = none := by
    cases site <;> simp [Interp.visError?, hv]
  simp only [Bool.or_eq_false_iff, List.contains_cons, List.contains_nil] at hentry
  rcases hentry with ⟨⟨⟨⟨⟨⟨hmain, hnames⟩, hdup⟩, hclone⟩, hrequire⟩, henum⟩, hiter⟩
  simp only [Interp.invoke.invokeDispatch, hl, hu, hp, Bool.false_eq_true, ↓reduceIte,
    Interp.crubyResolvedShadow, hb, Option.any, hmain, hdup, hclone, hrequire, henum, hiter,
    hs, hvis, hc, hm, hd, hn, Option.isSome, Bool.false_and,
    Interp.appendKwHash, List.isEmpty, ↓reduceIte]
  simp_all only [Bool.or_eq_false_iff, Bool.false_or, Bool.or_false, Bool.false_eq_true,
    List.contains_cons, List.contains_nil, ↓reduceIte]
  cases Builtins.run bid recv args m <;> rfl

#print axioms primitive_lookup
#print axioms invokeDispatch_builtin
end Ratchet.Denote.Typed
