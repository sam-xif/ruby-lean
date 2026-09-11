import Ratchet.Deriv

/-!
Negative controls for `validateD`.

`answer-typed-schema.md` §8.10 asks for these from day one, and the reason is blunt: **a
checker that accepts everything satisfies `check_sound` just as well.** `validateD` is a
shape check today, so what these pin is exactly the property a shape check has -- that a
certificate is tied to *this* program -- and nothing more. When the typing half lands,
the ill-typed controls below stop being shape-accepted and this file grows the cases
that separate the two.

`#guard`, not `native_decide`: `certificate-language.md` §7 norm 5 forbids the latter on
anything the checker's answer depends on, and there is no reason to reach for it here.
-/

namespace Ratchet

/-! ### The positive control: without one, every `false` below proves nothing
(`found-issues.md` §F24 vs §F25 -- run the control). -/

/-- `1 + 2`, with the derivation the emitter writes for it. -/
def ctlProg : Expr := .send (some (.int 1)) "+" [.int 2] none
def ctlDeriv : Deriv := .prim (.intLit 1) "+" [.intLit 2] .int .int

#guard validateD ctlProg ctlDeriv = true

/-! ### Control 1 -- a certificate for a different program

The derivation above, against `1 + 3`. Everything about the shape is right; only the
literal moved. This is the control that says a `Deriv` is *about* a program. -/
#guard validateD (.send (some (.int 1)) "+" [.int 3] none) ctlDeriv = false

-- The same at the method name: `1 - 2` does not admit the `+` derivation.
#guard validateD (.send (some (.int 1)) "-" [.int 2] none) ctlDeriv = false

/-! ### Control 2 -- a certificate of the wrong depth

An extra argument on one side and not the other. `derivShapeAll` is where this is
caught, and it is caught in both directions. -/
#guard validateD (.send (some (.int 1)) "+" [.int 2, .int 3] none) ctlDeriv = false
#guard validateD ctlProg (.prim (.intLit 1) "+" [.intLit 2, .intLit 3] .int .int) = false

/-! ### Control 3 -- a certificate using the wrong rule

`Deriv.callSig` and `Deriv.prim` are both about sends, and only one of them is about a
send *with a receiver*. -/
#guard validateD ctlProg (.callSig "+" [.intLit 2] .int) = false

/-! ### Control 4 -- an ill-typed program with a well-shaped certificate

**This one is accepted, and that is the point.** `"a" + 1` is a `TypeError` at run time;
the emitter would never write this certificate (`prim_ret` has no row for it), but a
buggy or adversarial one could, and today's `validateD` has no grounds to refuse it. The
guard records `true` so that the day `check` lands, this line has to be edited -- which
is the cheapest possible reminder that the shape check is not a soundness check. -/
#guard validateD (.send (some (.str "a")) "+" [.int 1] none)
                 (.prim (.strLit "a") "+" [.intLit 1] (.cls "String") (.cls "String"))
       = true

/-! ### Control 5 -- a declared signature whose parameter names are not the `def`'s

`paramNamesMatch`: a certificate that renames a parameter is about a different program,
because the body is checked in an environment built from those names. -/
def ctlDef : Expr := .def' "add" [.req "x", .req "y"] (.var .lvar "x")
#guard validateD ctlDef (.defDecl "add" [("x", .int), ("y", .int)] .int (.var .lvar "x"))
       = true
#guard validateD ctlDef (.defDecl "add" [("x", .int), ("z", .int)] .int (.var .lvar "x"))
       = false
-- An optional or rest parameter is outside the fragment, and fails rather than being
-- accepted at some name the body does not bind.
#guard validateD (.def' "add" [.req "x", .opt "y" (.int 0)] (.var .lvar "x"))
                 (.defDecl "add" [("x", .int), ("y", .int)] .int (.var .lvar "x"))
       = false

end Ratchet
