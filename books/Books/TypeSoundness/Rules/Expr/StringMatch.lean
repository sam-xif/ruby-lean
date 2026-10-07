import Books.TypeSoundness.Rules.Primitive.PrimitiveAlloc

/-! `String#match?` at a Regexp: the search answers a Boolean at the unchanged machine
(`match?` sets no `$~`), or gates as unsupported. -/
set_option autoImplicit false
set_option maxRecDepth 4000
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem string_match_run {κ : Ctx} {I : Ty} {Γ : Env} {m : Machine} {o : ObjId} {s : String}
    {v : Value} (hm : StateOk κ Γ I m) (hk : m.kont = [])
    (hs : (m.heap.get o).payload = .str s) :
    StepSpec m Γ .bool (builtinStep (Builtins.run "String#match?" (.ref o) [v] m)) κ I := by
  simp only [Builtins.run]
  repeat' split
  all_goals first | trivial | skip
  all_goals
    change StepSpec m Γ _
      (builtinStep (Builtins.runRegex "String#match?" (.ref o) [v] m)) κ I
    rw [Builtins.runRegex.eq_def]
    simp only [Builtins.binArg]
    split
    · trivial
    · rename_i src opts hre
      rw [Builtins.runRegex.regexApply.eq_def]
      simp only [show "Regexp#" ++ "String#match?".drop 7 = "Regexp#match?" from rfl, hre,
        Builtins.strPayload?, hs]
      rw [Builtins.runRegex.applyTo.eq_def]
      split
      · trivial
      · simp only [↓reduceIte]
        exact stepSpec_value hm hk (by simp [denM, isBoolV])
      · simp only [↓reduceIte]
        exact stepSpec_value hm hk (by simp [denM, isBoolV])

#print axioms string_match_run
end Checker.Soundness.Typed
