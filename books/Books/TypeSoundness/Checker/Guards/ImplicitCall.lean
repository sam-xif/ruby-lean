import Books.TypeSoundness.Checker.Guards.Args

/-! The two no-receiver call spellings, preserving the bare-call dispatch site.
This is a syntax guard only; it grants no method lookup or body assumption. -/
namespace Checker

inductive ImplicitCallShape : Expr → String → List Expr → Prop
  | send {name : String} {args : List Expr} :
      ImplicitCallShape (.send none name args none) name args
  | vcall {name : String} : ImplicitCallShape (.vcall name) name []

theorem ImplicitCallShape.plainArg {e : Expr} {name : String} {args : List Expr}
    (h : ImplicitCallShape e name args) : plainArgB e = true := by
  cases h <;> rfl

end Checker
