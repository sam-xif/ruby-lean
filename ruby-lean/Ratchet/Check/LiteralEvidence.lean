import Ratchet.Check.Deriv
import Ratchet.Judgment.DJudge

/-! Source evidence for the current bottom of the clink rebuild. This is shared
by the validator and the bridge, and imports no semantic module. -/
set_option autoImplicit false
namespace Ratchet

/-- Source evidence for a literal and the exact authoring-rule name it uses. -/
inductive LiteralJudge : Expr → Ty → String → Prop where
  | intLit {n : Int} : LiteralJudge (.int n) .int "intLit"
  | fltLit {bits : UInt64} : LiteralJudge (.flt bits) .float "fltLit"
  | strLit {s : String} : LiteralJudge (.str s) (.cls "String") "strLit"
  | symLit {s : String} : LiteralJudge (.sym s) .sym "symLit"
  | truLit : LiteralJudge .tru .bool "truLit"
  | flsLit : LiteralJudge .fls .bool "flsLit"
  | nilLit : LiteralJudge .nil .nilT "nilLit"

theorem LiteralJudge.judged {p : Expr} {τ : Ty} {rule : String}
    (h : LiteralJudge p τ rule) {Γ : Env} {κ : Ctx} {I : Ty} :
    DJudge Γ p τ Γ κ I := by
  cases h
  · exact .intLit
  · exact .fltLit
  · exact .strLit
  · exact .symLit
  · exact .truLit
  · exact .flsLit
  · exact .nilLit

structure LiteralHint (p : Expr) where
  ty : Ty
  rule : String
  judged : LiteralJudge p ty rule

/-- Only direct literal hints qualify. Payload equality remains `validateD`'s
job; a flow wrapper cannot bypass the rule gate by containing a literal. -/
def literalHint? (p : Expr) (d : Deriv) : Option (LiteralHint p) :=
  match p, d with
  | .int _, .intLit _ => some ⟨.int, "intLit", .intLit⟩
  | .flt _, .fltLit _ => some ⟨.float, "fltLit", .fltLit⟩
  | .str _, .strLit _ => some ⟨.cls "String", "strLit", .strLit⟩
  | .sym _, .symLit _ => some ⟨.sym, "symLit", .symLit⟩
  | .tru, .truLit => some ⟨.bool, "truLit", .truLit⟩
  | .fls, .flsLit => some ⟨.bool, "flsLit", .flsLit⟩
  | .nil, .nilLit => some ⟨.nilT, "nilLit", .nilLit⟩
  | _, _ => none

end Ratchet
