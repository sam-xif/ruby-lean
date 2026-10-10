import Books.TypeSoundness.Rules.Expr.StringSplit
import Books.TypeSoundness.Rules.Primitive.PrimitiveQueries

/-! `String#empty?`, `upcase`, `downcase`, `strip`: payload reads and one fresh String. -/
set_option autoImplicit false
set_option maxRecDepth 4000
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem strEmpty_step {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine} {recv : Value}
    (hm : StateOk κ Γ I m) (hk : m.kont = []) (hr : denM (.cls "String") m recv)
    (hfree : nameFreeN κ "empty?" = true)
    (hg : isANoOk κ.wholeCls (["String", "Comparable"] ++ rootAncestors) = true) :
    StepSpec m Γ .bool (Interp.invoke m recv site "empty?" [] none []) κ I := by
    obtain ⟨o, s, rfl, hs⟩ := string_payload hm hr hg
    rw [primitive_invoke (bid := "String#empty?") (k := Boot.stringId) hm
      (by simp [primitiveMethods]) (string_class hm hr hg) (by rfl)
      (by intro k hk; cases hk; exact ⟨s, hs⟩)
      (by first | rfl | simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
        nativeReal, rationalPayload?, complexPayload?, Builtins.toAryDefer?,
        Builtins.strCmpDefer?, Builtins.strCmpTwin?, hs]) (by rfl) hfree]
    have he : Builtins.runObjects "String#empty?" (.ref o) [] m = .ok (.bool s.isEmpty) m := by
      change Builtins.runStrings "String#empty?" (.ref o) [] m = _
      simp [Builtins.runStrings, Builtins.strPayload?, hs, Builtins.okStrFrom]
    rw [string_nullary_run (bid := "String#empty?") _ _ rfl (by decide +kernel) (by decide +kernel), he]
    exact stepSpec_value hm hk (by simp [denM, isBoolV])

#print axioms strEmpty_step

theorem strUpcase_step {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine} {recv : Value}
    (hm : StateOk κ Γ I m) (hk : m.kont = []) (hr : denM (.cls "String") m recv)
    (hfree : nameFreeN κ "upcase" = true)
    (hg : isANoOk κ.wholeCls (["String", "Comparable"] ++ rootAncestors) = true) :
    StepSpec m Γ (.cls "String") (Interp.invoke m recv site "upcase" [] none []) κ I := by
    obtain ⟨o, s, rfl, hs⟩ := string_payload hm hr hg
    rw [primitive_invoke (bid := "String#upcase") (k := Boot.stringId) hm
      (by simp [primitiveMethods]) (string_class hm hr hg) (by rfl)
      (by intro k hk; cases hk; exact ⟨s, hs⟩)
      (by first | rfl | simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
        nativeReal, rationalPayload?, complexPayload?, Builtins.toAryDefer?,
        Builtins.strCmpDefer?, Builtins.strCmpTwin?, hs]) (by rfl) hfree]
    have he : Builtins.runObjects "String#upcase" (.ref o) [] m = Builtins.okStrEnc m (Builtins.isBinaryStr m.heap (.ref o)) s.toUpper := by
      change Builtins.runStrings "String#upcase" (.ref o) [] m = _
      simp [Builtins.runStrings, Builtins.strPayload?, hs, Builtins.okStrFrom]
    rw [string_nullary_run (bid := "String#upcase") _ _ rfl (by decide +kernel) (by decide +kernel), he]
    exact stepSpec_string hm hk _ _

#print axioms strUpcase_step

theorem strReverse_step {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine} {recv : Value}
    (hm : StateOk κ Γ I m) (hk : m.kont = []) (hr : denM (.cls "String") m recv)
    (hfree : nameFreeN κ "reverse" = true)
    (hg : isANoOk κ.wholeCls (["String", "Comparable"] ++ rootAncestors) = true) :
    StepSpec m Γ (.cls "String") (Interp.invoke m recv site "reverse" [] none []) κ I := by
    obtain ⟨o, s, rfl, hs⟩ := string_payload hm hr hg
    rw [primitive_invoke (bid := "String#reverse") (k := Boot.stringId) hm
      (by simp [primitiveMethods]) (string_class hm hr hg) (by rfl)
      (by intro k hk; cases hk; exact ⟨s, hs⟩)
      (by first | rfl | simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
        nativeReal, rationalPayload?, complexPayload?, Builtins.toAryDefer?,
        Builtins.strCmpDefer?, Builtins.strCmpTwin?, hs]) (by rfl) hfree]
    have he : Builtins.runObjects "String#reverse" (.ref o) [] m = Builtins.okStrEnc m (Builtins.isBinaryStr m.heap (.ref o)) (String.ofList s.toList.reverse) := by
      change Builtins.runStrings "String#reverse" (.ref o) [] m = _
      simp [Builtins.runStrings, Builtins.strPayload?, hs, Builtins.okStrFrom]
    rw [string_nullary_run (bid := "String#reverse") _ _ rfl (by decide +kernel) (by decide +kernel), he]
    exact stepSpec_string hm hk _ _

#print axioms strReverse_step

theorem strEndWith_step {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine} {recv v : Value}
    (hm : StateOk κ Γ I m) (hk : m.kont = []) (hr : denM (.cls "String") m recv)
    (hv : denM (.cls "String") m v) (hfree : nameFreeN κ "end_with?" = true)
    (hg : isANoOk κ.wholeCls (["String", "Comparable"] ++ rootAncestors) = true) :
    StepSpec m Γ .bool (Interp.invoke m recv site "end_with?" [v] none []) κ I := by
  obtain ⟨o, s, rfl, hs⟩ := string_payload hm hr hg
  obtain ⟨p, t, rfl, ht⟩ := string_payload hm hv hg
  rw [primitive_invoke (bid := "String#end_with?") (k := Boot.stringId) hm
    (by simp [primitiveMethods]) (string_class hm hr hg) (by rfl)
    (by intro k hk; cases hk; exact ⟨s, hs⟩)
    (by simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
      nativeReal, rationalPayload?, complexPayload?, Builtins.toAryDefer?,
      Builtins.strCmpDefer?, Builtins.strCmpTwin?, hs, ht]) (by rfl) hfree]
  have he : Builtins.runObjects "String#end_with?" (.ref o) [.ref p] m =
      .ok (.bool (s.endsWith t)) m := by
    change Builtins.runStrings "String#end_with?" (.ref o) [.ref p] m = _
    simp [Builtins.runStrings, Builtins.binArg, Builtins.strPayload?, hs, ht]
  simp only [Builtins.run]
  repeat' split
  all_goals first | trivial | (rw [he]; exact stepSpec_value hm hk (by simp [denM, isBoolV])) | skip

#print axioms strEndWith_step

theorem intAbs_step {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine} (x : Int)
    (hm : StateOk κ Γ I m) (hk : m.kont = []) (hfree : nameFreeN κ "abs" = true) :
    StepSpec m Γ .int (Interp.invoke m (.int x) site "abs" [] none []) κ I := by
  have hrun : Builtins.run "Integer#abs" (.int x) [] m = .ok (.int x.natAbs) m := by
    simp only [Builtins.run, List.any_cons, List.any_nil, Builtins.unrepresentableByteStr,
      Builtins.strPayload?, Builtins.complexEqualityImpure, Bool.false_or, Bool.or_false,
      Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [primitive_invoke (bid := "Integer#abs") (k := Boot.integerId) hm
    (by simp [primitiveMethods]) rfl (by rfl) (by intro o ho; cases ho) (by rfl) (by rfl) hfree,
    hrun]
  exact stepSpec_value hm hk (by simp [denM, isIntV])

#print axioms intAbs_step

theorem intEven_step {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine} (x : Int)
    (hm : StateOk κ Γ I m) (hk : m.kont = []) (hfree : nameFreeN κ "even?" = true) :
    StepSpec m Γ .bool (Interp.invoke m (.int x) site "even?" [] none []) κ I := by
  have hrun : Builtins.run "Integer#even?" (.int x) [] m = .ok (.bool (x % 2 == 0)) m := by
    simp only [Builtins.run, List.any_cons, List.any_nil, Builtins.unrepresentableByteStr,
      Builtins.strPayload?, Builtins.complexEqualityImpure, Bool.false_or, Bool.or_false,
      Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [primitive_invoke (bid := "Integer#even?") (k := Boot.integerId) hm
    (by simp [primitiveMethods]) rfl (by rfl) (by intro o ho; cases ho) (by rfl) (by rfl) hfree,
    hrun]
  exact stepSpec_value hm hk (by simp [denM, isBoolV])

#print axioms intEven_step

theorem intOdd_step {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine} (x : Int)
    (hm : StateOk κ Γ I m) (hk : m.kont = []) (hfree : nameFreeN κ "odd?" = true) :
    StepSpec m Γ .bool (Interp.invoke m (.int x) site "odd?" [] none []) κ I := by
  have hrun : Builtins.run "Integer#odd?" (.int x) [] m = .ok (.bool (x % 2 != 0)) m := by
    simp only [Builtins.run, List.any_cons, List.any_nil, Builtins.unrepresentableByteStr,
      Builtins.strPayload?, Builtins.complexEqualityImpure, Bool.false_or, Bool.or_false,
      Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [primitive_invoke (bid := "Integer#odd?") (k := Boot.integerId) hm
    (by simp [primitiveMethods]) rfl (by rfl) (by intro o ho; cases ho) (by rfl) (by rfl) hfree,
    hrun]
  exact stepSpec_value hm hk (by simp [denM, isBoolV])

#print axioms intOdd_step

theorem intSucc_step {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine} (x : Int)
    (hm : StateOk κ Γ I m) (hk : m.kont = []) (hfree : nameFreeN κ "succ" = true) :
    StepSpec m Γ .int (Interp.invoke m (.int x) site "succ" [] none []) κ I := by
  have hrun : Builtins.run "Integer#succ" (.int x) [] m = .ok (.int (x + 1)) m := by
    simp only [Builtins.run, List.any_cons, List.any_nil, Builtins.unrepresentableByteStr,
      Builtins.strPayload?, Builtins.complexEqualityImpure, Bool.false_or, Bool.or_false,
      Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [primitive_invoke (bid := "Integer#succ") (k := Boot.integerId) hm
    (by simp [primitiveMethods]) rfl (by rfl) (by intro o ho; cases ho) (by rfl) (by rfl) hfree,
    hrun]
  exact stepSpec_value hm hk (by simp [denM, isIntV])

#print axioms intSucc_step

theorem strDowncase_step {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine} {recv : Value}
    (hm : StateOk κ Γ I m) (hk : m.kont = []) (hr : denM (.cls "String") m recv)
    (hfree : nameFreeN κ "downcase" = true)
    (hg : isANoOk κ.wholeCls (["String", "Comparable"] ++ rootAncestors) = true) :
    StepSpec m Γ (.cls "String") (Interp.invoke m recv site "downcase" [] none []) κ I := by
    obtain ⟨o, s, rfl, hs⟩ := string_payload hm hr hg
    rw [primitive_invoke (bid := "String#downcase") (k := Boot.stringId) hm
      (by simp [primitiveMethods]) (string_class hm hr hg) (by rfl)
      (by intro k hk; cases hk; exact ⟨s, hs⟩)
      (by first | rfl | simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
        nativeReal, rationalPayload?, complexPayload?, Builtins.toAryDefer?,
        Builtins.strCmpDefer?, Builtins.strCmpTwin?, hs]) (by rfl) hfree]
    have he : Builtins.runObjects "String#downcase" (.ref o) [] m = Builtins.okStrEnc m (Builtins.isBinaryStr m.heap (.ref o)) s.toLower := by
      change Builtins.runStrings "String#downcase" (.ref o) [] m = _
      simp [Builtins.runStrings, Builtins.strPayload?, hs, Builtins.okStrFrom]
    rw [string_nullary_run (bid := "String#downcase") _ _ rfl (by decide +kernel) (by decide +kernel), he]
    exact stepSpec_string hm hk _ _

#print axioms strDowncase_step

theorem strStrip_step {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine} {recv : Value}
    (hm : StateOk κ Γ I m) (hk : m.kont = []) (hr : denM (.cls "String") m recv)
    (hfree : nameFreeN κ "strip" = true)
    (hg : isANoOk κ.wholeCls (["String", "Comparable"] ++ rootAncestors) = true) :
    StepSpec m Γ (.cls "String") (Interp.invoke m recv site "strip" [] none []) κ I := by
    obtain ⟨o, s, rfl, hs⟩ := string_payload hm hr hg
    rw [primitive_invoke (bid := "String#strip") (k := Boot.stringId) hm
      (by simp [primitiveMethods]) (string_class hm hr hg) (by rfl)
      (by intro k hk; cases hk; exact ⟨s, hs⟩)
      (by first | rfl | simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
        nativeReal, rationalPayload?, complexPayload?, Builtins.toAryDefer?,
        Builtins.strCmpDefer?, Builtins.strCmpTwin?, hs]) (by rfl) hfree]
    have he : Builtins.runObjects "String#strip" (.ref o) [] m = Builtins.okStrEnc m (Builtins.isBinaryStr m.heap (.ref o)) s.trimAscii.toString := by
      change Builtins.runStrings "String#strip" (.ref o) [] m = _
      simp [Builtins.runStrings, Builtins.strPayload?, hs, Builtins.okStrFrom]
    rw [string_nullary_run (bid := "String#strip") _ _ rfl (by decide +kernel) (by decide +kernel), he]
    exact stepSpec_string hm hk _ _

#print axioms strStrip_step
end Checker.Soundness.Typed
