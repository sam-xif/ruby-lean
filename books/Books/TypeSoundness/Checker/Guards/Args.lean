import Books.TypeSoundness.Checker.Lang.Expr

namespace Checker

/-- Argument lists interpret these heads specially instead of evaluating them as
ordinary expressions, for both sends and explicit super. -/
def plainArgB : Expr → Bool
  | .splat _ | .kwargs _ | .fwd => false
  | _ => true

end Checker
