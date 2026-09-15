import Ratchet.Check
import Ratchet.MethodCheck
import Ratchet.MethodControls
import Ratchet.InitCheckControls
import Ratchet.ClassCheckControls

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
*with a receiver* — `callSig` only admits implicit-self calls to installed, checked bodies. -/
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

-- Array types and arity are recomputed, including empty and nested arrays.
#guard validateD (.array []) (.arrayLit [] .never)
#guard !validateD (.array []) (.arrayLit [] .any)
#guard !validateD (.array [.int 1]) (.arrayLit [.intLit 1] .bool)
#guard !validateD (.array [.int 1]) (.arrayLit [] .int)
#guard !validateD (.array []) (.arrayLit [.intLit 1] .int)
#guard validateD (.array [.array [.int 1], .array [.int 2]])
  (.arrayLit [.arrayLit [.intLit 1] .int, .arrayLit [.intLit 2] .int] (.arrayOf .int))
#guard !validateD (.array [.splat (some (.int 1))]) (.arrayLit [.intLit 1] .int)
#guard !validateD (.array [.send (some (.int 1)) "+" [.str "x"] none])
  (.arrayLit [.prim (.intLit 1) "+" [.strLit "x"] .int .int] .int)

-- Element evaluation threads locals left to right; reading before the write is rejected.
#guard validateD (.array [.vasgn .lvar "x" (.int 1), .var .lvar "x"])
  (.arrayLit [.vasgn .lvar "x" (.intLit 1), .var .lvar "x"] .int)
#guard !validateD (.array [.var .lvar "x", .vasgn .lvar "x" (.int 1)])
  (.arrayLit [.var .lvar "x", .vasgn .lvar "x" (.intLit 1)] .int)

-- Higher-order values in an incoming environment cannot bypass the retention guard.
#guard (check 30 [("f", .arrow0 .int)] (.var .lvar "f") (.var .lvar "f")).isSome
#guard (check 30 [("f", .arrow0 .int)] (.array [.var .lvar "f"])
  (.arrayLit [.var .lvar "f"] (.arrow0 .int))).isNone

-- Hash certificate lists have independent arity checks and recomputed joins.
#guard validateD (.hash []) (.hashLit [] [] .never .never)
#guard !validateD (.hash []) (.hashLit [] [] .any .any)
#guard validateD (.hash [(.sym "k", .int 1), (.sym "k", .int 2)])
  (.hashLit [.symLit "k", .symLit "k"] [.intLit 1, .intLit 2] .sym .int)
#guard !validateD (.hash [(.sym "k", .int 1)]) (.hashLit [] [.intLit 1] .sym .int)
#guard !validateD (.hash [(.sym "k", .int 1)]) (.hashLit [.symLit "k"] [] .sym .int)
#guard !validateD (.hash []) (.hashLit [.symLit "k"] [.intLit 1] .sym .int)
#guard !validateD (.hash [(.sym "k", .int 1)]) (.hashLit [.symLit "k"] [.intLit 1] .int .int)
#guard !validateD (.hash [(.sym "k", .int 1)]) (.hashLit [.symLit "k"] [.intLit 1] .sym .bool)
#guard !validateD (.hash [(.sym "k", .send (some (.int 1)) "+" [.str "x"] none)])
  (.hashLit [.symLit "k"] [.prim (.intLit 1) "+" [.strLit "x"] .int .int] .sym .int)

-- Key before value, and the first value before the next key (not two separate walks).
#guard validateD (.hash [(.vasgn .lvar "x" (.int 1), .var .lvar "x")])
  (.hashLit [.vasgn .lvar "x" (.intLit 1)] [.var .lvar "x"] .int .int)
#guard validateD (.hash [(.int 1, .vasgn .lvar "x" (.int 2)), (.var .lvar "x", .int 3)])
  (.hashLit [.intLit 1, .var .lvar "x"] [.vasgn .lvar "x" (.intLit 2), .intLit 3] .int .int)
#guard !validateD (.hash [(.var .lvar "x", .int 1), (.vasgn .lvar "x" (.int 2), .int 3)])
  (.hashLit [.var .lvar "x", .vasgn .lvar "x" (.intLit 2)] [.intLit 1, .intLit 3] .int .int)
#guard validateD (.hash [(.sym "k", .array [.int 1])])
  (.hashLit [.symLit "k"] [.arrayLit [.intLit 1] .int] .sym (.arrayOf .int))
#guard (check 30 [("f", .arrow0 .int)] (.hash [(.var .lvar "f", .int 1)])
  (.hashLit [.var .lvar "f"] [.intLit 1] (.arrow0 .int) .int)).isNone
#guard (check 30 [("f", .arrow0 .int)] (.hash [(.int 1, .var .lvar "f")])
  (.hashLit [.intLit 1] [.var .lvar "f"] .int (.arrow0 .int))).isNone

-- Array indexing always claims element-or-nil, including at a literal in-range index.
def ctlIndex (i : Expr) : Expr := .send (some (.array [.int 1, .int 2])) "[]" [i] none
def ctlIndexCert (di : Deriv) (ret : Ty := .nilable .int) : Deriv :=
  .prim (.arrayLit [.intLit 1, .intLit 2] .int) "[]" [di] (.arrayOf .int) ret

#guard validateD (ctlIndex (.int 0)) (ctlIndexCert (.intLit 0))
#guard validateD (ctlIndex (.int (-1))) (ctlIndexCert (.intLit (-1)))
#guard validateD (ctlIndex (.int 99)) (ctlIndexCert (.intLit 99))
#guard !validateD (ctlIndex (.int 0)) (ctlIndexCert (.intLit 0) .int)
#guard !validateD (ctlIndex (.str "bad")) (ctlIndexCert (.strLit "bad"))
#guard validateD (.send (some (.array [])) "[]" [.int 0] none)
  (.prim (.arrayLit [] .never) "[]" [.intLit 0] (.arrayOf .never) (.nilable .never))
#guard !validateD (.send (some (.array [])) "[]" [] none)
  (.prim (.arrayLit [] .never) "[]" [] (.arrayOf .never) (.nilable .never))
#guard validateD
  (.send (some (.array [.vasgn .lvar "x" (.int 1)])) "[]"
    [.seq [.vasgn .lvar "x" (.str "changed"), .int 0]] none)
  (.prim (.arrayLit [.vasgn .lvar "x" (.intLit 1)] .int) "[]"
    [.seq [.vasgn .lvar "x" (.strLit "changed"), .intLit 0]] (.arrayOf .int) (.nilable .int))
#guard dprim? (.arrayOf (.arrow0 .int)) "[]" [.int] == none
#guard dprim? (.arrayOf (.arrayOf .int)) "[]" [.int] == some (.nilable (.arrayOf .int))

-- Hash queries may have a different type from stored keys, but the result remains nullable.
def ctlHashIndex (k : Expr) : Expr := .send (some (.hash [(.sym "a", .int 1)])) "[]" [k] none
def ctlHashIndexCert (dk : Deriv) (ret : Ty := .nilable .int) : Deriv :=
  .prim (.hashLit [.symLit "a"] [.intLit 1] .sym .int) "[]" [dk] (.hashOf .sym .int) ret

#guard validateD (ctlHashIndex (.sym "a")) (ctlHashIndexCert (.symLit "a"))
#guard validateD (ctlHashIndex (.sym "missing")) (ctlHashIndexCert (.symLit "missing"))
#guard validateD (ctlHashIndex (.int 1)) (ctlHashIndexCert (.intLit 1))
#guard !validateD (ctlHashIndex (.sym "a")) (ctlHashIndexCert (.symLit "a") .int)
#guard validateD (.send (some (.hash [])) "[]" [.nil] none)
  (.prim (.hashLit [] [] .never .never) "[]" [.nilLit] (.hashOf .never .never) (.nilable .never))
#guard !validateD (.send (some (.hash [])) "[]" [] none)
  (.prim (.hashLit [] [] .never .never) "[]" [] (.hashOf .never .never) (.nilable .never))
#guard !validateD (.send (some (.hash [])) "[]" [.nil, .nil] none)
  (.prim (.hashLit [] [] .never .never) "[]" [.nilLit, .nilLit]
    (.hashOf .never .never) (.nilable .never))
#guard validateD
  (.send (some (.hash [(.sym "a", .vasgn .lvar "x" (.int 1))])) "[]"
    [.seq [.vasgn .lvar "x" (.str "changed"), .sym "a"]] none)
  (.prim (.hashLit [.symLit "a"] [.vasgn .lvar "x" (.intLit 1)] .sym .int) "[]"
    [.seq [.vasgn .lvar "x" (.strLit "changed"), .symLit "a"]] (.hashOf .sym .int) (.nilable .int))
#guard dprim? (.hashOf (.arrow0 .int) .int) "[]" [.int] == none
#guard dprim? (.hashOf .sym (.arrow0 .int)) "[]" [.int] == none
#guard dprim? (.hashOf .sym (.arrayOf .int)) "[]" [.nilT] == some (.nilable (.arrayOf .int))

-- Definition admission must check annotations against the body even when no call follows.
-- These are permanent negative controls, not a positive claim of method coverage.
#guard !validateD (.def' "bad" [] .tru) (.defDecl "bad" [] .int .truLit)
#guard !validateD (.def' "bad" [.req "x"] (.var .lvar "x"))
  (.defDecl "bad" [("x", .int)] .bool (.var .lvar "x"))
#guard !validateD
  (.def' "bad" [.req "x"] (.send (some (.var .lvar "x")) "+" [.str "oops"] none))
  (.defDecl "bad" [("x", .int)] .int
    (.prim (.var .lvar "x") "+" [.strLit "oops"] .int .int))
-- A method body cannot borrow the definition site's local environment.
#guard !validateD (.seq [.vasgn .lvar "outer" (.int 1),
    .def' "bad" [] (.var .lvar "outer")])
  (.seq [.vasgn .lvar "outer" (.intLit 1), .defDecl "bad" [] .int (.var .lvar "outer")])
-- Signature data cannot rename the program's formal parameter or hoist an installation.
#guard !validateD (.def' "bad" [.req "x"] (.var .lvar "x"))
  (.defDecl "bad" [("y", .int)] .int (.var .lvar "x"))
#guard !validateD (.seq [.send none "later" [] none, .def' "later" [] (.int 1)])
  (.seq [.callSig "later" [] .int, .defDecl "later" [] .int (.intLit 1)])

-- An Integer call can work even when the body violates its nilable-Integer annotation.
-- The body check must use the annotation, not types inferred from those calls.
def ctlAnnotationBody : Expr := .send (some (.var .lvar "x")) "+" [.int 1] none
def ctlAnnotationBodyCert : Deriv := .prim (.var .lvar "x") "+" [.intLit 1] .int .int
def ctlAnnotationDef : Expr := .def' "annotation_probe" [.req "x"] ctlAnnotationBody
def ctlAnnotationDefCert : Deriv :=
  .defDecl "annotation_probe" [("x", .nilable .int)] .int ctlAnnotationBodyCert

-- These body-level controls are meaningful before definition admission exists.
#guard (check 100 [("x", .int)] ctlAnnotationBody ctlAnnotationBodyCert).isSome
#guard (check 100 [("x", .nilable .int)] ctlAnnotationBody ctlAnnotationBodyCert).isNone
#guard !validateD ctlAnnotationDef ctlAnnotationDefCert
#guard !validateD (.seq [ctlAnnotationDef, .send none "annotation_probe" [.int 1] none])
  (.seq [ctlAnnotationDefCert, .callSig "annotation_probe" [.intLit 1] .int])

-- Replay from a method frame and installed declaration table, not just ctx0.
def ctlMethodCtx : Ctx :=
  { ctx0 with
    pos := { ctx0.pos with defs := [⟨"annotation_probe", [.req "x"], ctlAnnotationBody⟩] }
    neg := { ctx0.neg with declared := ["annotation_probe"] }
    scope := { ctx0.scope with frame := some ⟨"Object", "Object", "annotation_probe"⟩ } }

#guard (check 100 [("x", .int)] ctlAnnotationBody ctlAnnotationBodyCert ctlMethodCtx).isSome
#guard (check 100 [("x", .nilable .int)] ctlAnnotationBody ctlAnnotationBodyCert ctlMethodCtx).isNone
#guard (check 100 [("x", .int)] ctlAnnotationBody ctlAnnotationBodyCert
  { ctlMethodCtx with neg := { ctlMethodCtx.neg with declared := ["annotation_probe", "+"] } }).isNone

-- Conditional replay compares the full method context and retains it in its result.
#guard match check 100 [("x", .int)] (.if' .tru ctlAnnotationBody (some (.int 0)))
    (.ifD .truLit ctlAnnotationBodyCert (some (.intLit 0)) .int) ctlMethodCtx with
  | some c => ctxEqB c.ctx ctlMethodCtx && c.spine == .ivar0 && c.ty == .int
  | none => false
#guard (check 100 [("x", .int)] (.if' .tru ctlAnnotationBody none)
  (.ifD .truLit ctlAnnotationBodyCert none (.nilable .int)) ctlMethodCtx).isSome
#guard (ctxEq? ctlMethodCtx { ctlMethodCtx with pos :=
  { ctlMethodCtx.pos with defs := [⟨"annotation_probe", [.req "x"], .nil⟩] } }).isNone

-- A reusable body artifact checks the whole declared signature, not merely the body hint.
def ctlMethodDecl : Defn := ⟨"annotation_probe", [.req "x"], ctlAnnotationBody⟩
def ctlCheckedBody (ps : List SigParam) (ret : Ty) :=
  checkMethodBody 100 ctlMethodCtx .ivar0 ctlMethodDecl
    (.defDecl "annotation_probe" ps ret ctlAnnotationBodyCert)
#guard (ctlCheckedBody [("x", .int)] .int).isSome
#guard (ctlCheckedBody [("x", .nilable .int)] .int).isNone
#guard (ctlCheckedBody [("x", .int)] (.cls "String")).isNone
#guard (ctlCheckedBody [("other", .int)] .int).isNone
#guard (ctlCheckedBody [] .int).isNone
#guard (ctlCheckedBody [("x", .int), ("extra", .int)] .int).isNone
#guard (ctlCheckedBody [("x", .sameAs "caller" .int)] .int).isNone
#guard (checkMethodBody 100 ctlMethodCtx .ivar0 ctlMethodDecl
  (.defDecl "other" [("x", .int)] .int ctlAnnotationBodyCert)).isNone
#guard (checkMethodBody 100 ctlMethodCtx .ivar0 ctlMethodDecl
  (.defDecl "annotation_probe" [("x", .int)] .int (.intLit 1))).isNone
-- A nullable annotation is usable when the body genuinely handles its entire domain.
#guard (checkMethodBody 100 ctlMethodCtx .ivar0 ⟨"identity", [.req "x"], .var .lvar "x"⟩
  (.defDecl "identity" [("x", .nilable .int)] (.nilable .int) (.var .lvar "x"))).isSome
-- A signature with an unsupported body cannot become a callable assumption.
#guard (checkMethodBody 100 ctlMethodCtx .ivar0
    ⟨"forward", [.req "x"], .send none "annotation_probe" [.var .lvar "x"] none⟩
  (.defDecl "forward" [("x", .int)] .int (.callSig "annotation_probe" [.var .lvar "x"] .int))).isNone

end Ratchet
