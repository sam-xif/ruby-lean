import Ratchet.Check

/-!
Negative controls for `validateD`.

`answer-typed-schema.md` §8.10 asks for these from day one, and the reason is blunt: **a
checker that accepts everything satisfies its soundness statement just as well.** `check`
now returns the derivation (`Ratchet/Check.lean` §3), so "sound" is not the question these
controls answer — the typechecker answered it. What they answer is the other two:

* is the certificate *checked*, or ignored? (§1–§3: wrong program, wrong depth, wrong rule,
  wrong claimed type)
* is the **typing** real? (§4 — the control that flipped)

`#guard`, not `native_decide`: `certificate-language.md` §7 norm 5 forbids the latter on
anything the checker's answer depends on.
-/

namespace Ratchet

/-! ### The positive control: without one, every `false` below proves nothing
(`found-issues.md` §F24 vs §F25 -- run the control). -/

/-- `1 + 2`, with the derivation the emitter writes for it. -/
def ctlProg : Expr := .send (some (.int 1)) "+" [.int 2] none
def ctlDeriv : Deriv := .prim (.intLit 1) "+" [.intLit 2] .int .int

#guard validateD ctlProg ctlDeriv = true

-- Decimal conversion's result is String. Radix arguments need their own obligation.
#guard validateD (.send (some (.int (-5))) "to_s" [] none)
    (.prim (.intLit (-5)) "to_s" [] .int (.cls "String"))
#guard !validateD (.send (some (.int 5)) "to_s" [] none)
    (.prim (.intLit 5) "to_s" [] .int .int)
#guard dprim? .int "to_s" [.nilT] = none

-- Equality accepts unrelated argument types, but still checks arity and argument safety.
#guard validateD (.send (some (.int 1)) "==" [.nil] none)
    (.prim (.intLit 1) "==" [.nilLit] .int .bool)
#guard dprim? .int "==" [] = none
#guard dprim? .int "==" [.int, .int] = none
#guard dprim? .int "zero?" [.int] = none
#guard dprim? .int "<=" [.cls "String"] = none
#guard dprim? .int ">=" [.nilT] = none
#guard dprim? .nilT "==" [] = none
#guard dprim? (.cls "String") "length" [.int] = none
#guard !validateD (.send (some (.int 1)) "=="
    [.send (some (.str "a")) "+" [.int 1] none] none)
    (.prim (.intLit 1) "=="
      [.prim (.strLit "a") "+" [.intLit 1] (.cls "String") (.cls "String")] .int .bool)

/-! ### Control 1 -- a certificate for a different program

The derivation above, against `1 + 3`. Everything about the shape is right; only the
literal moved. This is the control that says a `Deriv` is *about* a program. -/
#guard validateD (.send (some (.int 1)) "+" [.int 3] none) ctlDeriv = false

-- The same at the method name: `1 - 2` does not admit the `+` derivation.
#guard validateD (.send (some (.int 1)) "-" [.int 2] none) ctlDeriv = false

/-! ### Control 2 -- a certificate of the wrong depth

An extra argument on one side and not the other. `checkAll` is where this is caught, and it
is caught in both directions. -/
#guard validateD (.send (some (.int 1)) "+" [.int 2, .int 3] none) ctlDeriv = false
#guard validateD ctlProg (.prim (.intLit 1) "+" [.intLit 2, .intLit 3] .int .int) = false

/-! ### Control 3 -- a certificate using the wrong rule

`Deriv.callSig` and `Deriv.prim` are both about sends, and only one of them is about a send
*with a receiver* — and `callSig` has no `DJudge` rule at all, so it is refused twice over. -/
#guard validateD ctlProg (.callSig "+" [.intLit 2] .int) = false

/-! ### Control 4 -- **the one that flipped**

`"a" + 1` is a `TypeError` at run time. Under the shape-check stub this certificate was
**accepted**, and the `#guard` recorded `true` with a note saying the line would have to be
edited the day the typing half landed. This is that edit: `dprim?` has no row for
`String#+` at an `Integer` argument, so `check` refuses, and the refusal is the difference
between a checker that reads a certificate and one that types a program. -/
#guard validateD (.send (some (.str "a")) "+" [.int 1] none)
                 (.prim (.strLit "a") "+" [.intLit 1] (.cls "String") (.cls "String"))
       = false

-- The control for it: the same shape with the *right* argument type is accepted, so §4's
-- `false` is about the types and not about `String#+` being missing from the table.
#guard validateD (.send (some (.str "a")) "+" [.str "b"] none)
                 (.prim (.strLit "a") "+" [.strLit "b"] (.cls "String") (.cls "String"))
       = true

/-! ### Control 5 -- a claimed type that is not the derived one

The certificate's `Ty` fields are recomputed and compared, so a certificate that is
perfectly well-shaped and *lies about the result type* is rejected. This is the property
that makes the untrusted emitter safe to be wrong: a wrong claim costs a rejection, never a
wrong accept (`sorbet-cert/README.md` §3's tamper argument, at this layer). -/
#guard validateD ctlProg (.prim (.intLit 1) "+" [.intLit 2] .int (.cls "String")) = false

-- …and lying about the *receiver* type is caught in the same place.
#guard validateD ctlProg (.prim (.intLit 1) "+" [.intLit 2] .bool .int) = false

/-! ### Control 6 -- an unbound local

`x` with no binding has no type, and the `var` rule's premise is `envGet? Γ x = some τ`, so
there is nothing to return. A certificate cannot supply the missing binding. -/
#guard validateD (.var .lvar "x") (.var .lvar "x") = false

-- The control: bound first, and the read types.
#guard validateD (.seq [.vasgn .lvar "x" (.int 1), .var .lvar "x"])
                 (.seq [.vasgn .lvar "x" (.intLit 1), .var .lvar "x"]) = true

/-! ### Control 7 -- the `if` join is recomputed

`true && false` desugars to a `seq` of a temp assignment and an `if`, and the `if`'s type is
the join of its branches. A certificate claiming a different join is rejected; the honest one
is accepted. -/
def ctlAnd : Expr :=
  .seq [.vasgn .lvar "t" .tru, .if' (.var .lvar "t") .fls (some (.var .lvar "t"))]

#guard validateD ctlAnd
  (.seq [.vasgn .lvar "t" .truLit,
         .ifD (.var .lvar "t") .flsLit (some (.var .lvar "t")) .bool]) = true

#guard validateD ctlAnd
  (.seq [.vasgn .lvar "t" .truLit,
         .ifD (.var .lvar "t") .flsLit (some (.var .lvar "t")) .int]) = false

-- An absent else contributes nil, and the certificate must record that join.
#guard validateD (.if' .fls (.int 1) none)
    (.ifD .flsLit (.intLit 1) none (.nilable .int))
#guard !validateD (.if' .fls (.int 1) none)
    (.ifD .flsLit (.intLit 1) none .int)
#guard !validateD (.if' .fls (.int 1) (some (.str "a")))
    (.ifD .flsLit (.intLit 1) none (.nilable .int))

-- Rung 042's unsafe reassignment must be refused by the checker itself, even if
-- an emitter supplies the certificate it currently declines to generate.
#guard !validateD
    (.seq [.vasgn .lvar "x" (.int 1), .if' .tru (.vasgn .lvar "x" (.str "hello")) none,
      .send (some (.var .lvar "x")) "+" [.int 1] none])
    (.seq [.vasgn .lvar "x" (.intLit 1),
      .ifD .truLit (.vasgn .lvar "x" (.strLit "hello")) none (.nilable (.cls "String")),
      .prim (.var .lvar "x") "+" [.intLit 1] .int .int])
#guard validateD
    (.seq [.vasgn .lvar "x" (.int 1), .if' .tru (.vasgn .lvar "x" (.int 2)) none,
      .send (some (.var .lvar "x")) "+" [.int 1] none])
    (.seq [.vasgn .lvar "x" (.intLit 1),
      .ifD .truLit (.vasgn .lvar "x" (.intLit 2)) none (.nilable .int),
      .prim (.var .lvar "x") "+" [.intLit 1] .int .int])

#guard validateD (.vcall "x") (.bareName "x")
#guard !validateD (.vcall "lambda") (.bareName "x")
#guard !validateD (.vcall "x") (.bareName "y")
#guard !validateD (.send none "x" [] none) (.bareName "x")

end Ratchet
