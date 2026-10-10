import Books.TypeSoundness.Checker.Lang.ExprEq

/-! A callable carries its own supported syntax. Reflexive comparison is evidence that
our conservative comparator covers the code; it makes equality decidable without trusting
an opaque syntax BEq or encoding code as an unchecked table index. -/
namespace Checker

structure ClosureCode where
  params : List Param
  locals : List String
  body : Expr
  lam : Bool
  supported : (paramEqAll params params && exprEq body body) = true
deriving Repr

instance : Inhabited ClosureCode := ⟨⟨[], [], .nil, true, rfl⟩⟩

def closureCodeEq (a b : ClosureCode) : Bool :=
  paramEqAll a.params b.params && a.locals == b.locals &&
    exprEq a.body b.body && a.lam == b.lam

theorem closureCodeEq_sound {a b : ClosureCode} (h : closureCodeEq a b = true) : a = b := by
  cases a; cases b
  simp only [closureCodeEq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hp, hl⟩, hb⟩, hm⟩ := h
  cases paramEqAll_sound hp
  cases hl
  cases exprEq_sound _ _ hb
  cases hm
  rfl

theorem closureCodeEq_refl (a : ClosureCode) : closureCodeEq a a = true := by
  have hs := a.supported
  simp only [Bool.and_eq_true] at hs
  obtain ⟨hp, hb⟩ := hs
  simp [closureCodeEq, hp, hb]

instance : DecidableEq ClosureCode := fun a b =>
  if h : closureCodeEq a b = true then isTrue (closureCodeEq_sound h)
  else isFalse (fun he => h (he ▸ closureCodeEq_refl a))

instance : BEq ClosureCode := ⟨closureCodeEq⟩

instance : LawfulBEq ClosureCode where
  eq_of_beq := closureCodeEq_sound
  rfl := closureCodeEq_refl _

/-- Unsupported syntax is an explicit completeness boundary, never an assumed match. -/
def closureCode? (ps : List Param) (ls : List String) (body : Expr) (lam : Bool) :
    Option ClosureCode :=
  if h : (paramEqAll ps ps && exprEq body body) = true then
    some ⟨ps, ls, body, lam, h⟩
  else none

#print axioms closureCodeEq_sound
end Checker
