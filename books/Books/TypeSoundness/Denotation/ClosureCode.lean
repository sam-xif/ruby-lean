import Books.TypeSoundness.Checker.Lang.ClosureCode
import Books.TypeSoundness.Conformance.Core.Trans

/-! Conservative comparison across the syntax bridge. True carries exact translated
code equality, including parameters, block locals and lambda/proc mode. -/
namespace Checker.Soundness

def paramCodeEq : Checker.Param → RubyCore.Param → Bool
  | .req a, .req b => a == b
  | .rest a, .rest b => a == b
  | .kwrest a, .kwrest b => a == b
  | .block a, .block b => a == b
  | .fwd, .fwd => true
  | _, _ => false

def paramCodeEqAll : List Checker.Param → List RubyCore.Param → Bool
  | [], [] => true
  | a :: as, b :: bs => paramCodeEq a b && paramCodeEqAll as bs
  | _, _ => false

mutual

def exprCodeEq : Checker.Expr → RubyCore.Expr → Bool
  | .int a, .int b => a == b
  | .flt a, .flt b => a == b
  | .str a, .str b => a == b
  | .sym a, .sym b => a == b
  | .tru, .tru => true
  | .fls, .fls => true
  | .nil, .nil => true
  | .self', .self' => true
  | .var k a, .var k' b => toRubyVarKind k == k' && a == b
  | .vasgn k a e, .vasgn k' b e' => toRubyVarKind k == k' && a == b && exprCodeEq e e'
  | .const a, .const b => a == b
  | .vcall a, .vcall b => a == b
  -- The `Option Expr` fields are matched inline rather than through a helper: an
  -- `Option Expr → Option Expr → Bool` companion is not part of the nested-inductive
  -- bundle Lean builds structural recursion from, and adding one is what pushes this whole
  -- group onto well-founded recursion — at which point it stops reducing in the kernel and
  -- every `rfl` that depends on it fails. Discovered the hard way; see
  -- `../notes/type-soundness/implementation-notes.md` clink 9.
  | .send none m as none, .send none m' as' none =>
    m == m' && exprCodeEqAll as as'
  | .send (some r) m as none, .send (some r') m' as' none =>
    exprCodeEq r r' && m == m' && exprCodeEqAll as as'
  | .send none m as (some b), .send none m' as' (some b') =>
    m == m' && exprCodeEqAll as as' && exprCodeEq b b'
  | .send (some r) m as (some b), .send (some r') m' as' (some b') =>
    exprCodeEq r r' && m == m' && exprCodeEqAll as as' && exprCodeEq b b'
  | .block ps ls b, .block ps' ls' b' =>
    paramCodeEqAll ps ps' && ls == ls' && exprCodeEq b b'
  | .yield' as, .yield' as' => exprCodeEqAll as as'
  | .blockpass none, .blockpass none => true
  | .blockpass (some e), .blockpass (some e') => exprCodeEq e e'
  | .if' c t none, .if' c' t' none => exprCodeEq c c' && exprCodeEq t t'
  | .if' c t (some e), .if' c' t' (some e') =>
    exprCodeEq c c' && exprCodeEq t t' && exprCodeEq e e'
  | .def' n ps b, .def' n' ps' b' => n == n' && paramCodeEqAll ps ps' && exprCodeEq b b'
  | .defs r n ps b, .defs r' n' ps' b' =>
    exprCodeEq r r' && n == n' && paramCodeEqAll ps ps' && exprCodeEq b b'
  | .array es, .array es' => exprCodeEqAll es es'
  | .hash ps, .hash ps' => exprCodeEqPairs ps ps'
  | .ret none, .ret none => true
  | .ret (some e), .ret (some e') => exprCodeEq e e'
  | .class' n none b, .class' n' none b' => n == n' && exprCodeEq b b'
  | .class' n (some s) b, .class' n' (some s') b' =>
    n == n' && exprCodeEq s s' && exprCodeEq b b'
  | .module' n b, .module' n' b' => n == n' && exprCodeEq b b'
  | .super' as none, .super' as' none => exprCodeEqAll as as'
  | .super' as (some b), .super' as' (some b') => exprCodeEqAll as as' && exprCodeEq b b'
  | .seq es, .seq es' => exprCodeEqAll es es'
  | _, _ => false

def exprCodeEqAll : List Checker.Expr → List RubyCore.Expr → Bool
  | [], [] => true
  | a :: as, b :: bs => exprCodeEq a b && exprCodeEqAll as bs
  | _, _ => false

def exprCodeEqPairs : List (Checker.Expr × Checker.Expr) → List (RubyCore.Expr × RubyCore.Expr) → Bool
  | [], [] => true
  | (k, v) :: ps, (k', v') :: ps' =>
    exprCodeEq k k' && exprCodeEq v v' && exprCodeEqPairs ps ps'
  | _, _ => false

end

theorem paramCodeEq_sound {a : Checker.Param} {b : RubyCore.Param}
    (h : paramCodeEq a b = true) : toRubyParam a = b := by
  cases a <;> cases b <;> simp_all [paramCodeEq, toRubyParam]

theorem paramCodeEqAll_sound {a : List Checker.Param} {b : List RubyCore.Param}
    (h : paramCodeEqAll a b = true) : toRubyParams a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [paramCodeEqAll, toRubyParams]
  | cons a as ih =>
    cases b with
    | nil => cases h
    | cons b bs =>
      simp only [paramCodeEqAll, Bool.and_eq_true] at h
      simp only [toRubyParams, paramCodeEq_sound h.1, ih h.2]

theorem exprCodeEq_sound (a : Checker.Expr) (b : RubyCore.Expr) :
    exprCodeEq a b = true → toRuby a = b := by
  induction a, b using exprCodeEq.induct
    (motive_2 := fun a b => exprCodeEqPairs a b = true → toRubyPairs a = b)
    (motive_3 := fun a b => exprCodeEqAll a b = true → toRubyList a = b) <;>
    simp_all [exprCodeEq, exprCodeEqAll, exprCodeEqPairs, Bool.and_eq_true,
      toRuby, toRubyList, toRubyPairs, toRubyOpt]
  all_goals intros; simp_all
  all_goals apply paramCodeEqAll_sound; assumption

def ClosureMatches (code : ClosureCode) (cl : RubyCore.Closure) : Prop :=
  cl.params = toRubyParams code.params ∧ cl.locals = code.locals ∧
    cl.body = toRuby code.body ∧ cl.lam = code.lam ∧ cl.enumYield = none ∧ cl.forTargets = none

def closureMatchesB (code : ClosureCode) (cl : RubyCore.Closure) : Bool :=
  paramCodeEqAll code.params cl.params && code.locals == cl.locals &&
    exprCodeEq code.body cl.body && code.lam == cl.lam && cl.enumYield.isNone &&
    cl.forTargets.isNone

theorem closureMatchesB_sound {code : ClosureCode} {cl : RubyCore.Closure}
    (h : closureMatchesB code cl = true) : ClosureMatches code cl := by
  simp only [closureMatchesB, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at h
  exact ⟨(paramCodeEqAll_sound h.1.1.1.1.1).symm, h.1.1.1.1.2.symm,
    (exprCodeEq_sound _ _ h.1.1.1.2).symm, h.1.1.2.symm, h.1.2, h.2⟩

#print axioms closureMatchesB_sound
end Checker.Soundness
