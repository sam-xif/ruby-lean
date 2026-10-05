import Denote.Rules.Expr.StringSplit
import Denote.Rules.Primitive.PrimitiveQueries

/-! `String#empty?`, `upcase`, `downcase`, `strip`: payload reads and one fresh String. -/
set_option autoImplicit false
set_option maxRecDepth 4000
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

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
end Ratchet.Denote.Typed
