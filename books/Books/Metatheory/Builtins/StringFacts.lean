import Init.Data.String.Lemmas.Pattern.TakeDrop.String

/-! Proof-facing reductions for the String pattern APIs. Their executable
implementations are opaque; the library's list characterizations let the
kernel check dispatch constants without trusting native evaluation. -/
namespace RubyCore.Proof

theorem startsWith_decide (s pat : String) :
    s.startsWith pat = decide (pat.toList <+: s.toList) := by
  apply Bool.eq_iff_iff.mpr
  simp

theorem endsWith_decide (s pat : String) :
    s.endsWith pat = decide (pat.toList <:+ s.toList) := by
  apply Bool.eq_iff_iff.mpr
  simp only [String.endsWith, String.Slice.endsWith_string_iff,
    String.copy_toSlice, decide_eq_true_eq]

end RubyCore.Proof
