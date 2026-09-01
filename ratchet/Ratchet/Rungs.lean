import Ratchet.Proof.ChkSound

/-!
# The climbed rungs, typed by hand

One entry per rung of `corpus/001-*` … `corpus/013-*`, each carrying a **derivation term**
`Judge program ty` written out by hand. The point is that the ladder's claim
"13 rungs climbed" is backed by 13 readable derivations, not only by a `Bool`:

- The `deriv` field is a real proof term, so Lean's kernel checks each derivation
  against `Ratchet/Judge.lean`'s rules. A wrong `ty` — `.str "hello"` claimed `.sym`,
  say — does not compile.
- `chk_agrees_with_hand_derivations` (below) checks the *executable* checker answers the
  same type by `rfl`, per rung. So `chk` and the hand-authored judgment are pinned to
  each other in both directions on this fragment: `chk_sound` gives
  `chk ⇒ Judge` in general, and these 13 `rfl`s give `Judge ⇒ chk` where it matters.
- `CheckRungs.lean` (the `checkrungs` exe) closes the remaining two gaps that no proof in this
  package can: that each `program` below is *really* what the desugarer emitted for that
  rung's Ruby (decoded from `corpus/*.json` and compared with `==`), and that running the
  **real semantics** on it yields a value of the class `ty` names.

## Nothing here is trusted

These derivations used to be qualified by "…and none of them uses the trusted `claim`
leaf", a fact this file stated as a theorem over an empty certificate. Certificates are
gone (`AGENTS.md` §Claim-free), so the qualification is now structural: `Judge` has no
trusted leaf to use. Every derivation below is built only from rules that assert
something checkable about the real semantics.
-/

namespace Ratchet

/-- One rung: the program, the type it was hand-derived at, and the derivation. The
`deriv` field is what distinguishes this from a test table — it cannot be filled in
wrongly. -/
structure Rung where
  id : String
  program : Expr
  ty : Ty
  /-- The environment the program leaves behind. `[]` for every rung whose program
      binds nothing; tier 3's rungs are the first with anything in it, and printing it
      is how one reads off what the checker thinks each local ended up as. -/
  outEnv : Env
  /-- The derivation, in `ctx0` — every table empty and no `self` — from the empty local
      environment and the empty ivar spine, and coming back to the empty spine. Each of
      those emptinesses matters for a different reason, and `ctx0`'s docstring says which.
      A program's own `def`/`class` statements grow the syntax tables from inside, via
      `JudgeSeq.cons`, which is why no rung writes a table down.

      The **outgoing spine is required to be `.ivar0` too**, and that is a real (if
      currently free) restriction: a rung whose top-level code assigned an instance variable
      would not fit this structure. None does; `@x = 1` at `main` is legal Ruby that this
      judgment types but that no rung exercises. -/
  deriv : Judge (ctx0.withBlocks program) [] .ivar0 program ty outEnv .ivar0

/-! ## Tier 1 — the eight literals

Each derivation is a single rule application. What each one asserts about the real
semantics is in the comment: the class of the value CRuby produces. `CheckRungs.lean`
checks that assertion by running `stepFn`. -/

/-- `1` → `Integer`. -/
def r001 : Rung := ⟨"int-lit", .int 1, .int, [], .intLit⟩
/-- `true` → `TrueClass`, which `Ty.bool` covers (it does not distinguish the two
    boolean classes — see `Judge.truLit`). -/
def r002 : Rung := ⟨"bool-true", .tru, .bool, [], .truLit⟩
/-- `false` → `FalseClass`, same `Ty.bool`. -/
def r003 : Rung := ⟨"bool-false", .fls, .bool, [], .flsLit⟩
/-- `"hello"` → an *instance* of `String`, hence `.cls "String"`, not `.clsOf "String"`
    (which would be the class object). -/
def r004 : Rung := ⟨"str-lit", .str "hello", .cls "String", [], .strLit⟩
/-- `:ok` → `Symbol`. -/
def r005 : Rung := ⟨"sym-lit", .sym "ok", .sym, [], .symLit⟩
/-- `nil` → `NilClass`. `.nilT`, the singleton — deliberately not `.nilable _`. -/
def r006 : Rung := ⟨"nil-lit", .nil, .nilT, [], .nilLit⟩
/-- `1.5` → `Float`. The literal's IEEE bits are carried in the syntax and are
    irrelevant to its type. -/
def r007 : Rung := ⟨"flt-lit", .flt (Float.toBits 1.5), .float, [], .fltLit⟩
/-- `-5` → `Integer`, and note the *syntax*: the desugarer emits `int (-5)`, a single
    negative literal, **not** `send (int 5) "-@" []`. So this rung is `intLit` again, and
    no unary-operator rule is needed to climb it. Worth stating because it is a real fact
    about the desugarer that the hand derivation would get wrong the other way. -/
def r008 : Rung := ⟨"neg-int-lit", .int (-5), .int, [], .intLit⟩

/-! ## Tier 2 (first five) — arithmetic and string `+` as ordinary sends

`1 + 2` is not special syntax in Ruby and is not special syntax here: the desugarer emits
`send (int 1) "+" [int 2] nil`, and each derivation below is `Judge.prim` over the
receiver's derivation, the argument list's, and one `PrimSig` row. Reading one of these
terms *is* reading the dispatch: receiver type, argument types, signature, result. -/

/-- `1 + 2` → `Integer`. -/
def r009 : Rung :=
  ⟨"add", .send (some (.int 1)) "+" [.int 2] none, .int,
    [], .prim .intLit (.cons .intLit .nil) .intAdd⟩
/-- `5 - 3` → `Integer`. -/
def r010 : Rung :=
  ⟨"sub", .send (some (.int 5)) "-" [.int 3] none, .int,
    [], .prim .intLit (.cons .intLit .nil) .intSub⟩
/-- `4 * 3` → `Integer`. -/
def r011 : Rung :=
  ⟨"mul", .send (some (.int 4)) "*" [.int 3] none, .int,
    [], .prim .intLit (.cons .intLit .nil) .intMul⟩
/-- `10 / 2` → `Integer`. See `PrimSig.intDiv`'s docstring for the one subtlety on this
    rung: the signature does not claim division never raises (`10 / 0` raises
    `ZeroDivisionError`), only that it never reaches the
    `NoMethodError`/`ArgumentError`/`TypeError` family and returns an `Integer`. -/
def r012 : Rung :=
  ⟨"div", .send (some (.int 10)) "/" [.int 2] none, .int,
    [], .prim .intLit (.cons .intLit .nil) .intDiv⟩
/-- `"a" + "b"` → an instance of `String`. The argument's type matters here in a way it
    does not for the integer rows: `"a" + 1` raises `TypeError`, which is *in* the
    family, so `PrimSig.strAdd` demands `.cls "String"` and nothing weaker. -/
def r013 : Rung :=
  ⟨"str-concat", .send (some (.str "a")) "+" [.str "b"] none, .cls "String",
    [], .prim .strLit (.cons .strLit .nil) .strAdd⟩

/-! ## Tier 2's second half — comparisons, queries, `!`, and `==`

Same one rule per rung: `Judge.prim` over a receiver derivation, an argument-list
derivation, and one `PrimSig` row. What is new is *which* rows, and each of the four
shapes below is a different kind of claim about the semantics — see `PrimSig`'s
docstrings. -/

/-- `(1 + 2) * 3` → `Integer`. Nothing new in the rules: the outer send's *receiver* is
    itself a send, so the derivation nests. This is the rung the checker has always got
    "for free" from tiers 1–2's first half; it now has a derivation term like the rest. -/
def r027 : Rung :=
  ⟨"nested-arith",
    .send (some (.send (some (.int 1)) "+" [.int 2] none)) "*" [.int 3] none, .int,
    [], .prim (.prim .intLit (.cons .intLit .nil) .intAdd) (.cons .intLit .nil) .intMul⟩

/-- `3 < 5` → a boolean. The `[.int]` argument type is load-bearing: `3 < "a"` raises
    `ArgumentError`, which is in the type-stuck family. -/
def r014 : Rung :=
  ⟨"cmp-lt", .send (some (.int 3)) "<" [.int 5] none, .bool,
    [], .prim .intLit (.cons .intLit .nil) .intLt⟩
/-- `1 <= 2` → a boolean. -/
def r024 : Rung :=
  ⟨"cmp-le", .send (some (.int 1)) "<=" [.int 2] none, .bool,
    [], .prim .intLit (.cons .intLit .nil) .intLe⟩
/-- `1 >= 2` → a boolean (`false`, but the *type* is what is derived). -/
def r025 : Rung :=
  ⟨"cmp-ge", .send (some (.int 1)) ">=" [.int 2] none, .bool,
    [], .prim .intLit (.cons .intLit .nil) .intGe⟩
/-- `!true` → a boolean. Note the syntax: `!` is not an operator in the `Expr` grammar,
    the desugarer emits `send (tru) "!" []`, so this is `Judge.prim` with an *empty*
    argument list — no new rule shape was needed for a unary operator. -/
def r015 : Rung :=
  ⟨"not-expr", .send (some .tru) "!" [] none, .bool,
    [], .prim .truLit .nil .notBool⟩
/-- `5.to_s` → an instance of `String`. -/
def r019 : Rung :=
  ⟨"to-s-call", .send (some (.int 5)) "to_s" [] none, .cls "String",
    [], .prim .intLit .nil .intToS⟩
/-- `5.zero?` → a boolean. Sibling of `unknown-method` (`5.foo_bar_baz`), which is a
    permanent negative: the difference between them is entirely in whether `PrimSig` has
    a row, which is exactly what a hardcoded builtin table is for at this rung. -/
def r022 : Rung :=
  ⟨"unmodeled-builtin-zero-p", .send (some (.int 5)) "zero?" [] none, .bool,
    [], .prim .intLit .nil .intZeroP⟩
/-- `"abc".length` → an `Integer` — the same nullary-query shape on a different
    receiver class. -/
def r028 : Rung :=
  ⟨"str-length", .send (some (.str "abc")) "length" [] none, .int,
    [], .prim .strLit .nil .strLength⟩
/-- `1 == 1` → a boolean, by `PrimSig.objEq` with an `Integer` receiver. -/
def r020 : Rung :=
  ⟨"eq-same-type", .send (some (.int 1)) "==" [.int 1] none, .bool,
    [], .prim .intLit (.cons .intLit .nil) (.objEq .int)⟩
/-- `1 == "a"` → a boolean. The rung that forces `objEq`'s argument to be unconstrained:
    this is safe Ruby answering `false`, and a rule demanding matching operand types
    would reject it for no semantic reason. -/
def r021 : Rung :=
  ⟨"eq-different-type", .send (some (.int 1)) "==" [.str "a"] none, .bool,
    [], .prim .intLit (.cons .strLit .nil) (.objEq .int)⟩
/-- `nil == nil` → a boolean, receiver `NilClass`. -/
def r026 : Rung :=
  ⟨"nil-eq-nil", .send (some .nil) "==" [.nil] none, .bool,
    [], .prim .nilLit (.cons .nilLit .nil) (.objEq .nilT)⟩

/-! ## Tier 3 — locals: `vasgn`, `var`, `seq`, and a bare name

The first rungs whose derivations are not about a single expression. Two things to read
off each one:

- **the `outEnv` column**: what the checker believes each local ended up as. It is part
  of the `Rung` record precisely so a wrong environment cannot hide behind a right
  result type;
- **the threading**: a `seq`'s derivation is a right-nested `JudgeSeq` chain, and each
  link's outgoing environment is the next link's incoming one. `Judge.var` then reads a
  type back out with `envGet?`, discharged by `rfl` — that `rfl` *is* the check that the
  earlier assignment put the right thing there. -/

/-- `x = 5; x + 1` → `Integer`, leaving `x : Int`. The minimal statement of the whole
    tier: an assignment's effect on the environment is what the next statement's `var`
    read consumes. -/
def r029 : Rung :=
  ⟨"simple-assign",
    .seq [.vasgn .lvar "x" (.int 5),
          .send (some (.var .lvar "x")) "+" [.int 1] none],
    .int, [("x", .int)],
    .seq (.cons (.vasgn .intLit)
      (.last (.prim (.var rfl rfl) (.cons .intLit .nil) .intAdd)))⟩

/-- `x = 1; x = 2; x + 3` → `Integer`. Rebinding at the *same* type; the interesting
    sibling is the next rung. -/
def r030 : Rung :=
  ⟨"reassign-same-type",
    .seq [.vasgn .lvar "x" (.int 1), .vasgn .lvar "x" (.int 2),
          .send (some (.var .lvar "x")) "+" [.int 3] none],
    .int, [("x", .int)],
    .seq (.cons (.vasgn .intLit)
      (.cons (.vasgn .intLit)
        (.last (.prim (.var rfl rfl) (.cons .intLit .nil) .intAdd))))⟩

/-- `x = 1; x = true; x` → `Bool`, leaving `x : Bool`. The rung that pins down what a
    Ruby local is: `envSet` overwrites, and **no rule anywhere requires the new type to
    relate to the old one**. A checker that rejected this — or that joined `Int` and
    `Bool` into a union — would be describing a different language. -/
def r031 : Rung :=
  ⟨"reassign-different-type",
    .seq [.vasgn .lvar "x" (.int 1), .vasgn .lvar "x" .tru, .var .lvar "x"],
    .bool, [("x", .bool)],
    .seq (.cons (.vasgn .intLit) (.cons (.vasgn .truLit) (.last (.var rfl rfl))))⟩

/-- A bare `x`, never assigned → `.any`, environment untouched.

    This is the ladder's sharpest illustration that **type safety here is not
    crash-freedom**. `x` alone desugars to `vcall "x"`, not to a `var` read, and running
    it raises `NameError` — which is deliberately *outside* the
    `NoMethodError`/`ArgumentError`/`TypeError` family (`NoMethodError` is a *subclass*
    of `NameError`, but a bare name with no parentheses raises the parent, not the
    child). So the program is type-safe and crashes, and the type is `.any` because the
    expression never produces a value for anything to depend on.

    What makes this admissible rather than a hole is `BareNameError`: a one-row table,
    not a blanket rule. See its docstring for why a blanket rule would be unsound
    (`proc` is also a bare name, and it raises `ArgumentError`).

    The second premise — the `rfl`, discharging `defGet? [] "x" = none` — arrived with
    tier 6: now that a `def'` is typeable, "nothing has defined this name" has to be
    *checked* rather than guaranteed by the absence of a rule. On this rung it is trivial,
    because the program contains no `def`; the control that makes it non-trivial is
    `def x; 1 + true; end; x` in `CheckRungs.lean`. -/
def r032 : Rung :=
  ⟨"bare-undeclared-var", .vcall "x", .any, [], .bareName .x rfl rfl⟩

/-- `x = 1; y = 2; x + y` → `Integer`, leaving both locals bound. Two *different* names,
    where the previous rungs rebind one — so this is the rung that would catch an
    `envSet` that clobbered the whole environment instead of one entry. -/
def r033 : Rung :=
  ⟨"seq-multiple-stmts",
    .seq [.vasgn .lvar "x" (.int 1), .vasgn .lvar "y" (.int 2),
          .send (some (.var .lvar "x")) "+" [.var .lvar "y"] none],
    .int, [("x", .int), ("y", .int)],
    .seq (.cons (.vasgn .intLit)
      (.cons (.vasgn .intLit)
        (.last (.prim (.var rfl rfl) (.cons (.var rfl rfl) .nil) .intAdd))))⟩

/-- `x = 1; y = x + 1; z = y + 1; z` → `Integer`. A four-statement chain where each
    assignment's right-hand side reads the previous one's binding: the environment has
    to thread through a *nested* `Judge` (inside the `vasgn`), not just along the
    `seq`. -/
def r034 : Rung :=
  ⟨"assignment-chain",
    .seq [.vasgn .lvar "x" (.int 1),
          .vasgn .lvar "y" (.send (some (.var .lvar "x")) "+" [.int 1] none),
          .vasgn .lvar "z" (.send (some (.var .lvar "y")) "+" [.int 1] none),
          .var .lvar "z"],
    .int, [("x", .int), ("y", .int), ("z", .int)],
    .seq (.cons (.vasgn .intLit)
      (.cons (.vasgn (.prim (.var rfl rfl) (.cons .intLit .nil) .intAdd))
        (.cons (.vasgn (.prim (.var rfl rfl) (.cons .intLit .nil) .intAdd))
          (.last (.var rfl rfl)))))⟩

/-! ## Tier 4 — conditionals, and tier 2's `&&`/`||`

`if'` derivations read as: condition, then-branch, else-branch, and *two* joins — one
over the result types, one over the environments. The `ty` and `outEnv` fields below are
the **computed** joins written out longhand, so a wrong `joinT`/`joinEnv` would stop
these from compiling. -/

/-- `if true then 1 else 2` → `Integer`. Both branches agree, so `joinT` is the identity
    on them and no union appears. -/
def r035 : Rung :=
  ⟨"if-true-branch", .if' .tru (.int 1) (some (.int 2)), .int, [],
    .if' .truLit .intLit .intLit rfl⟩

/-- `if true then 1 end` (no `else`) → `nilable Int`. The absent branch contributes
    `nil`, and `joinT .int .nilT` is `mkNilable .int`. -/
def r036 : Rung :=
  ⟨"if-no-else", .if' .tru (.int 1) none, .nilable .int, [],
    .ifNoElse .truLit .intLit rfl⟩

/-- `if 5 then 1 else 2` → `Integer`. The rung that pins the condition being
    unconstrained: `5` is a perfectly good Ruby condition (only `nil`/`false` are falsy)
    and `Judge.if'` never looks at `σ`. -/
def r037 : Rung :=
  ⟨"if-condition-not-bool", .if' (.int 5) (.int 1) (some (.int 2)), .int, [],
    .if' .intLit .intLit .intLit rfl⟩

/-- `if true then 1 else "a"` → `union(Int, String)`. The first type in this package that
    is not the type of any single value: `Ty.union` was in the grammar and inert, and
    this is the rung that makes `joinT` produce one instead of giving up. -/
def r038 : Rung :=
  ⟨"if-branch-mismatch", .if' .tru (.int 1) (some (.str "a")),
    .union .int (.cls "String"), [],
    .if' .truLit .intLit .strLit rfl⟩

/-- `if true then 1 elsif false then 2 else "a"` → `union(Int, String)`, **not**
    `union(Int, union(Int, String))`. `elsif` is nested `if'`, so the outer join sees
    `Int` against the inner union; the answer is only the smaller type because `joinT`
    flattens and dedups. This rung is why it does. -/
def r039 : Rung :=
  ⟨"elsif-chain-mismatch",
    .if' .tru (.int 1) (some (.if' .fls (.int 2) (some (.str "a")))),
    .union .int (.cls "String"), [],
    .if' .truLit .intLit (.if' .flsLit .intLit .strLit rfl) rfl⟩

/-- `if nil then 1 else 2` → `Integer`. `nil` is falsy, never a type error. -/
def r040 : Rung :=
  ⟨"if-nil-condition", .if' .nil (.int 1) (some (.int 2)), .int, [],
    .if' .nilLit .intLit .intLit rfl⟩

/-- A nested `if` in the then-branch → `Integer`. -/
def r041 : Rung :=
  ⟨"nested-if",
    .if' .tru (.if' .fls (.int 1) (some (.int 2))) (some (.int 3)), .int, [],
    .if' .truLit (.if' .flsLit .intLit .intLit rfl) .intLit rfl⟩

/-- `if true then 1 elsif false then 2 else 3` → `Integer`: the uniform three-way
    chain, joining twice. -/
def r043 : Rung :=
  ⟨"elsif-chain",
    .if' .tru (.int 1) (some (.if' .fls (.int 2) (some (.int 3)))), .int, [],
    .if' .truLit .intLit (.if' .flsLit .intLit .intLit rfl) rfl⟩

/-! ### Tier 2's stragglers: `&&` and `||`

Not sends at all. `true && false` desugars to a temporary local, a `seq` and an `if`:

```
seq (vasgn local __dt_t1 true) (if (var local __dt_t1) false (var local __dt_t1))
```

which is why these two rungs sat unclimbed through tiers 2 and 3 and fall out for free
here. The `outEnv` records the desugarer's temporary — the checker has no idea it is a
temporary, and does not need to. -/

/-- `true && false` → `Bool`. -/
def r016 : Rung :=
  ⟨"bool-and",
    .seq [.vasgn .lvar "__dt_t1" .tru,
          .if' (.var .lvar "__dt_t1") .fls (some (.var .lvar "__dt_t1"))],
    .bool, [("__dt_t1", .bool)],
    .seq (.cons (.vasgn .truLit)
      (.last (.if' (Γ₁ := [("__dt_t1", .bool)]) (Γ₂ := [("__dt_t1", .bool)])
                (τ₁ := .bool) (τ₂ := .bool) (.var rfl rfl) .flsLit (.var rfl rfl) rfl)))⟩

/-- `false || true` → `Bool`. Same shape, branches swapped. -/
def r017 : Rung :=
  ⟨"bool-or",
    .seq [.vasgn .lvar "__dt_t1" .fls,
          .if' (.var .lvar "__dt_t1") (.var .lvar "__dt_t1") (some .tru)],
    .bool, [("__dt_t1", .bool)],
    .seq (.cons (.vasgn .flsLit)
      (.last (.if' (Γ₁ := [("__dt_t1", .bool)]) (Γ₂ := [("__dt_t1", .bool)])
                (τ₁ := .bool) (τ₂ := .bool) (.var rfl rfl) (.var rfl rfl) .truLit rfl)))⟩

/-! ## Tier 5 — array and hash literals, and `#[]`

Two new rules (`arrayLit`, `hashLit`) and two new `PrimSig` rows, and the interesting
content is all in the **types**, not the derivation shapes: an array literal reuses
`JudgeAll` (the same relation that types a send's arguments), and a hash literal's
`JudgePairs` produces no type at all. The `ty` field below is the *computed* `elemTy`
join written out longhand, so a wrong element type would not compile. -/

/-- `[1, 2, 3]` → `arrayOf Int`. All three elements join to `Int`, so no union appears —
    `elemTy`'s singleton base case plus `joinT`'s equal-types case. -/
def r044 : Rung :=
  ⟨"array-int", .array [.int 1, .int 2, .int 3], .arrayOf .int, [],
    .arrayLit (.cons .intLit (.cons .intLit (.cons .intLit .nil)))⟩

/-- `[]` → `arrayOf never`. The empty literal's element type is `elemTy []`, the unit of
    the join: "every element of `[]` does not return a value" is vacuously true and is the
    most precise claim available. Tier 5 wrote `arrayOf any` here because `Ty` had no
    bottom type; tier 6 added one (`Ty.never`), and this rung is where the difference is
    visible. -/
def r045 : Rung :=
  ⟨"array-empty", .array [], .arrayOf .never, [], .arrayLit .nil⟩

/-- `[1, "a", true]` → `arrayOf (union Int (union String Bool))`. Heterogeneous arrays are
    ordinary Ruby, and tier 4's join is what makes them typeable rather than rejected.
    Note the right-nesting: `elemTy` folds from the right, so the members come out in
    source order. -/
def r046 : Rung :=
  ⟨"array-heterogeneous", .array [.int 1, .str "a", .tru],
    .arrayOf (.union .int (.union (.cls "String") .bool)), [],
    .arrayLit (.cons .intLit (.cons .strLit (.cons .truLit .nil)))⟩

/-- `[1 + 1, 2 + 2]` → `arrayOf Int`. The elements are `send`s, so this rung is what pins
    that `arrayLit` really recurses: each element gets a full derivation, and one that
    failed to type would sink the literal. -/
def r047 : Rung :=
  ⟨"array-of-sends",
    .array [.send (some (.int 1)) "+" [.int 1] none,
            .send (some (.int 2)) "+" [.int 2] none],
    .arrayOf .int, [],
    .arrayLit (.cons (.prim .intLit (.cons .intLit .nil) .intAdd)
      (.cons (.prim .intLit (.cons .intLit .nil) .intAdd) .nil))⟩

/-- `{"a" => 1, "b" => 2}` → `T::Hash[String, Integer]`.

    **Retyped at tier 17b** (clink 41). The original note read: "the keys' and values' types
    (`String`, `Int`) are derived and then discarded — `JudgePairs` carries no type in its
    conclusion, because `Ty` has nowhere to put one", and it was the first place on the ladder
    where "these subterms must be well-typed" and "and here is the type" came apart (clink 4).
    `Ty.hashOf` closed it, and the premise's *shape* did not change: `JudgePairs` now reports
    two joined types, folded exactly as `elemTy` folds an array literal's elements, so this
    derivation term is character-for-character the one that was on file. -/
def r048 : Rung :=
  ⟨"hash-lit", .hash [(.str "a", .int 1), (.str "b", .int 2)],
    .hashOf (.cls "String") .int, [],
    .hashLit (.cons .strLit .intLit (.cons .strLit .intLit .nil))⟩

/-- `[[1, 2], [3, 4]]` → `arrayOf (arrayOf Int)`. `elemTy`'s join at the outer level sees
    two *equal* `arrayOf Int`s, so `joinTy`'s equality case answers and no union appears —
    which is exactly where `arrayOf`'s invariance shows up as a *feature*: had the inner
    arrays differed (`[[1], ["a"]]`), the outer element type would be a union rather than
    a silently-widened `arrayOf (union …)`. -/
def r049 : Rung :=
  ⟨"nested-array",
    .array [.array [.int 1, .int 2], .array [.int 3, .int 4]],
    .arrayOf (.arrayOf .int), [],
    .arrayLit (.cons (.arrayLit (.cons .intLit (.cons .intLit .nil)))
      (.cons (.arrayLit (.cons .intLit (.cons .intLit .nil))) .nil))⟩

/-- `[1, 2, 3][0]` → `nilable Int`. Indexing is a plain `send`, so the derivation is
    `prim` with the new `arrayIndex` row; the `nilable` is the honest answer to an index
    the checker cannot bound (`[1,2,3][99]` is `nil`). The semantics produces an
    `Integer` here, which `nilable Int` admits — `CheckRungs.lean`'s set-membership
    check, deliberately weaker than an equality for these types. -/
def r050 : Rung :=
  ⟨"array-index",
    .send (some (.array [.int 1, .int 2, .int 3])) "[]" [.int 0] none,
    .nilable .int, [],
    .prim (.arrayLit (.cons .intLit (.cons .intLit (.cons .intLit .nil))))
      (.cons .intLit .nil) .arrayIndex⟩

/-- `{"a" => 1}["a"]` → `T.nilable(Integer)`.

    **The rung this ladder spent longest unable to type usefully**, and the retyping is the
    whole story of tier 17b. It used to answer `.any` — "the only sound result type is the one
    nothing can consume" — because `.cls "Hash"` said nothing about what the hash mapped to. It
    now answers `nilable Integer`, and the negative control the old note pointed at
    (`{"a"=>1}["a"] + 1`, safe Ruby no rule could type) is *still* declined, but for a
    different and much better reason: the value may be absent, so the type is `nilable`, and
    that is a fact about hashes rather than about this `Ty`. Its total sibling `fetch` is what
    the target actually writes, 62 times. -/
def r051 : Rung :=
  ⟨"hash-index",
    .send (some (.hash [(.str "a", .int 1)])) "[]" [.str "a"] none,
    .nilable .int, [],
    .prim (.hashLit (.cons .strLit .intLit .nil)) (.cons .strLit .nil) (.hashIndex .cls)⟩

/-! ## Tier 6 — top-level methods

The first tier whose derivations are not shaped like their programs. A `def` statement's
derivation is one leaf (`defStmt` — the body is not looked at), and the *body*'s derivation
hangs off the **call site** instead, inside `callDef`. So `simple-fun` reads: a `def` leaf,
then a call whose fourth premise is the entire derivation of `x + y` in an environment made
of the call's own argument types.

Two things to watch for in what follows:

- **`rfl` appears in three new roles.** `defGet? D m = some d` (the method was defined by an
  earlier statement), `paramEnv d.params argTys = some Γb` (the arity matched and every
  parameter is required), and `asmGet? Δ m argTys = some ρ` (this instantiation is the one
  currently being discharged). Each is a computation on tables the derivation carries, so a
  wrong table makes the `rfl` fail rather than making the rung silently pass.
- **`D` is never written down.** It is threaded by `JudgeSeq.cons`, so the derivations below
  read the def table off the program's own statement order. That is exactly the property
  that makes `foo(); def foo; end` underivable — and it is why `fun-calling-another-fun`
  works regardless of which `def` comes first (both have run by the time either is called). -/

/-- `def add(x, y) = x + y; add(1, 2)` → `Integer`. The signature `(Int, Int) → Int` appears
    nowhere in the program *and nowhere in the derivation either*: what stands in for it is
    `paramEnv`'s `[("x", Int), ("y", Int)]`, built from this call site's argument types, in
    which the body is then judged directly. -/
def r052 : Rung :=
  ⟨"simple-fun",
    .seq [.def' "add" [.req "x", .req "y"]
            (.send (some (.var .lvar "x")) "+" [.var .lvar "y"] none),
          .send none "add" [.int 1, .int 2] none],
    .int, [],
    .seq (.cons .defStmt
      (.last (.callDef (.cons .intLit (.cons .intLit .nil)) rfl rfl
        (.prim (.var rfl rfl) (.cons (.var rfl rfl) .nil) .intAdd))))⟩

/-- `def get5 = 5; get5()` → `Integer`. The degenerate case, and worth having: with no
    parameters there is nothing for the call site to contribute, so `paramEnv [] [] = []`
    and the body is judged in the empty environment. -/
def r055 : Rung :=
  ⟨"fun-zero-arg",
    .seq [.def' "get5" [] (.int 5), .send none "get5" [] none],
    .int, [],
    .seq (.cons .defStmt (.last (.callDef .nil rfl rfl .intLit)))⟩

/-- `def inc(x) = x + 1; def twice(x) = inc(inc(x)); twice(3)` → `Integer`. A call inside a
    body inside a call: `twice`'s body is judged with `D` holding *both* methods, because
    `D` is the one in force at `twice(3)` — after every top-level `def` has run. Source
    order between the two `def`s is therefore irrelevant, while source order between a `def`
    and a call is not. -/
def r057 : Rung :=
  ⟨"fun-calling-another-fun",
    .seq [.def' "inc" [.req "x"]
            (.send (some (.var .lvar "x")) "+" [.int 1] none),
          .def' "twice" [.req "x"]
            (.send none "inc" [.send none "inc" [.var .lvar "x"] none] none),
          .send none "twice" [.int 3] none],
    .int, [],
    .seq (.cons .defStmt (.cons .defStmt
      (.last (.callDef (.cons .intLit .nil) rfl rfl
        (.callDef
          (.cons (.callDef (.cons (.var rfl rfl) .nil) rfl rfl
                   (.prim (.var rfl rfl) (.cons .intLit .nil) .intAdd)) .nil)
          rfl rfl
          (.prim (.var rfl rfl) (.cons .intLit .nil) .intAdd))))))⟩

/-- `def sum3(a, b, c) = a + b + c; sum3(1, 2, 3)` → `Integer`. Three required parameters,
    so the interesting part is `paramEnv`'s three-way length match. -/
def r058 : Rung :=
  ⟨"fun-three-params",
    .seq [.def' "sum3" [.req "a", .req "b", .req "c"]
            (.send (some (.send (some (.var .lvar "a")) "+" [.var .lvar "b"] none))
              "+" [.var .lvar "c"] none),
          .send none "sum3" [.int 1, .int 2, .int 3] none],
    .int, [],
    .seq (.cons .defStmt
      (.last (.callDef (.cons .intLit (.cons .intLit (.cons .intLit .nil))) rfl rfl
        (.prim (.prim (.var rfl rfl) (.cons (.var rfl rfl) .nil) .intAdd)
          (.cons (.var rfl rfl) .nil) .intAdd))))⟩

/-- `def make_pair(x, y) = [x, y]; make_pair(1, 2)` → `arrayOf Int`. The return type is
    *structured* and comes entirely from the body, while the parameters are constrained
    entirely by the call site — nothing in `[x, y]` says what `x` is. The clearest rung for
    why this rule is per-call-site instantiation rather than signature inference. -/
def r059 : Rung :=
  ⟨"fun-returning-array",
    .seq [.def' "make_pair" [.req "x", .req "y"]
            (.array [.var .lvar "x", .var .lvar "y"]),
          .send none "make_pair" [.int 1, .int 2] none],
    .arrayOf .int, [],
    .seq (.cons .defStmt
      (.last (.callDef (.cons .intLit (.cons .intLit .nil)) rfl rfl
        -- `(τs := …)` written out because the element types come from `.var rfl rfl` reads of
        -- the parameter environment, and `elemTy ?τs = arrayOf Int` is not something
        -- unification can invert.
        (.arrayLit (τs := [.int, .int])
          (.cons (.var rfl rfl) (.cons (.var rfl rfl) .nil))))))⟩

/-- `def fact(n) = if n <= 1 then 1 else n * fact(n - 1); fact(4)` → `Integer`. **The rung
    tier 6 exists for.**

    Read the derivation from the inside out. The recursive occurrence is a `callAsm`, whose
    `rfl` looks `("fact", [Int])` up in `Δ` and finds `Int` — the assumption `callDef` put
    there. So `n * fact(n - 1)` is an ordinary `intMul`, the two branches join at `Int`, and
    the body synthesizes exactly the `Int` that was assumed. That coincidence *is* the
    check: `callDef`'s premise demands the body produce the assumed type, so an assumption
    that does not reproduce itself yields no derivation.

    Nothing in this term says how `Int` was found. `Ratchet/Validate.lean` finds it by
    typing the body once with the recursive call at `.never` — the only route by which the
    `then` branch's type becomes visible before the `else` branch has one — and that pass
    leaves no trace here, because it is a hint and hints are not evidence. -/
def r060 : Rung :=
  ⟨"fun-recursive-factorial",
    .seq [.def' "fact" [.req "n"]
            (.if' (.send (some (.var .lvar "n")) "<=" [.int 1] none)
              (.int 1)
              (some (.send (some (.var .lvar "n")) "*"
                [.send none "fact"
                  [.send (some (.var .lvar "n")) "-" [.int 1] none] none] none))),
          .send none "fact" [.int 4] none],
    .int, [],
    .seq (.cons .defStmt
      (.last (.callDef (.cons .intLit .nil) rfl rfl
        (.if' (.prim (.var rfl rfl) (.cons .intLit .nil) .intLe)
          .intLit
          (.prim (.var rfl rfl)
            (.cons (.callAsm
              (.cons (.prim (.var rfl rfl) (.cons .intLit .nil) .intSub) .nil) rfl) .nil)
            .intMul)
          rfl))))⟩

/-! ## Tier 7 — the object model

Where tier 6's derivations stopped being shaped like their programs, these stop being
shaped like anything on the page at all: a `class` statement is one leaf (`classStmt`), and
every method body's derivation hangs off a **`new` or a dispatch** somewhere else entirely.
`class-basic`'s derivation is a `classStmt`, then a `callMethod` whose sixth premise is
`@x`'s one-line read — and whose *receiver* premise contains the entire derivation of
`initialize`.

The `ty` fields are worth reading as the payoff. `class-basic` claims `Int` for
`Point.new(1, 2).getX` with **no annotation anywhere in the program**: the `Int` travelled
from the literal `1`, through `initialize`'s parameter, into the ivar spine inside
`Ty.inst "Point" …`, out through `getX`'s `@x`, and the derivation is the record of that
trip. `class-array-of-instances` is where the spine becomes visible in a rung's own type.

The four `rfl`s that show up per dispatch are `clsGet?` (the class is declared),
`defGet?` (it has that method), `paramEnv` (the arity matched), and — inside a `vcall` —
`κ.selfTy`. Each is a computation on a table the derivation carries, so a wrong table fails
the `rfl` rather than passing quietly.

Inheritance, `super` and singleton methods are the other three rungs and are not here; see
`AGENTS.md` §Frontier. -/

/-- The ivar spine `Point.new(x)` produces for a one-parameter `initialize` that stores it.
Written once because five rungs share it, and spelled out rather than computed so that a
wrong `ivarSet` would not compile. -/
def pointSpine1 : Ty := .ivarCons "@x" .int .ivar0

/-- `Box`'s spine, needed by name for a reason worth recording: `ivarSet` is **not
invertible by unification**. In `class-setter-method` the body's outgoing spine is
`ivarSet ?I' "@size" ?τ` and `callMethod` requires it to equal `Iself`, which is itself an
unreduced `ivarSet …`; Lean matches the two `ivarSet` applications structurally and solves
`?I' := .ivar0`, which is the wrong environment. Pinning both to this literal spine makes
the check a *reduction* (`ivarSet boxSpine "@size" .int` really is `boxSpine`) instead of a
match — which is exactly the fact the rung is about. -/
def boxSpine : Ty := .ivarCons "@size" .int .ivar0

/-- `class Point; def initialize(x, y); @x = x; @y = y; end; def getX; @x; end; end;
    Point.new(1, 2).getX` → `Integer`. **Tier 7's headline rung.**

    Nothing in this program says `@x` is an `Integer`. The type comes from the literal `1`,
    through `initialize`'s parameter `x`, into the spine that `newInst` builds and stores in
    `Ty.inst "Point" …`, and back out through `getX`'s `ivarRead`. Read the derivation
    inside out and it is that path, in order. -/
def r061 : Rung :=
  ⟨"class-basic",
    .seq [.class' "Point" none (.seq [
            .def' "initialize" [.req "x", .req "y"]
              (.seq [.vasgn .ivar "@x" (.var .lvar "x"),
                     .vasgn .ivar "@y" (.var .lvar "y")]),
            .def' "getX" [] (.var .ivar "@x")]),
          .send (some (.send (some (.const "Point")) "new" [.int 1, .int 2] none))
            "getX" [] none],
    .int, [],
    .seq (.cons (.classStmt rfl rfl rfl .nil .nil)
      (.last (.callMethod
        (.newInst (.constCls rfl rfl) (.cons .intLit (.cons .intLit .nil)) rfl rfl
          (.seq (.cons (.ivarAsgn (.var rfl rfl)) (.last (.ivarAsgn (.var rfl rfl))))))
        .nil rfl rfl .ivarRead)))⟩

/-- `class Counter; def initialize(n); @n = n; end; def add(k); @n + k; end; end;
    c = Counter.new(10); c.add(5)` → `Integer`. An instance stored in a local, so the
    `outEnv` below is the first place an `.inst` type with its spine is printed as part of
    the environment rather than only as a result. -/
def r062 : Rung :=
  ⟨"class-method-with-param",
    .seq [.class' "Counter" none (.seq [
            .def' "initialize" [.req "n"] (.vasgn .ivar "@n" (.var .lvar "n")),
            .def' "add" [.req "k"]
              (.send (some (.var .ivar "@n")) "+" [.var .lvar "k"] none)]),
          .vasgn .lvar "c" (.send (some (.const "Counter")) "new" [.int 10] none),
          .send (some (.var .lvar "c")) "add" [.int 5] none],
    .int, [("c", .inst "Counter" (.ivarCons "@n" .int .ivar0))],
    .seq (.cons (.classStmt rfl rfl rfl .nil .nil)
      (.cons (.vasgn (.newInst (.constCls rfl rfl) (.cons .intLit .nil) rfl rfl
                (.ivarAsgn (.var rfl rfl))))
        (.last (.callMethod (.var rfl rfl) (.cons .intLit .nil) rfl rfl
          (.prim .ivarRead (.cons (.var rfl rfl) .nil) .intAdd)))))⟩

/-- `p.getX + p.getY` on a two-ivar `Point` → `Integer`. Two dispatches on the *same*
    receiver type, each reading a different ivar out of the same spine — so this is the rung
    that would catch an `ivarGet?` that answered positionally rather than by name. -/
def r063 : Rung :=
  ⟨"class-two-getters",
    .seq [.class' "Point" none (.seq [
            .def' "initialize" [.req "x", .req "y"]
              (.seq [.vasgn .ivar "@x" (.var .lvar "x"),
                     .vasgn .ivar "@y" (.var .lvar "y")]),
            .def' "getX" [] (.var .ivar "@x"),
            .def' "getY" [] (.var .ivar "@y")]),
          .vasgn .lvar "p" (.send (some (.const "Point")) "new" [.int 3, .int 4] none),
          .send (some (.send (some (.var .lvar "p")) "getX" [] none)) "+"
            [.send (some (.var .lvar "p")) "getY" [] none] none],
    .int, [("p", .inst "Point" (.ivarCons "@x" .int (.ivarCons "@y" .int .ivar0)))],
    .seq (.cons (.classStmt rfl rfl rfl .nil .nil)
      (.cons (.vasgn (.newInst (.constCls rfl rfl) (.cons .intLit (.cons .intLit .nil))
                rfl rfl
                (.seq (.cons (.ivarAsgn (.var rfl rfl)) (.last (.ivarAsgn (.var rfl rfl)))))))
        (.last (.prim
          (.callMethod (.var rfl rfl) .nil rfl rfl .ivarRead)
          (.cons (.callMethod (.var rfl rfl) .nil rfl rfl .ivarRead) .nil)
          .intAdd))))⟩

/-- `class Rect; …; def area; @w * @h; end; def describe; "area=" + area.to_s; end; end;
    Rect.new(3, 4).describe` → `String`. The rung `selfCall` exists for: the `area` inside
    `describe` is a **`vcall`**, not a local read and not a top-level function call, and
    resolving it needs `κ.selfTy` — which is why `bareName` had to be restricted to top
    level in the same clink. -/
def r064 : Rung :=
  ⟨"class-method-calls-method",
    .seq [.class' "Rect" none (.seq [
            .def' "initialize" [.req "w", .req "h"]
              (.seq [.vasgn .ivar "@w" (.var .lvar "w"),
                     .vasgn .ivar "@h" (.var .lvar "h")]),
            .def' "area" [] (.send (some (.var .ivar "@w")) "*" [.var .ivar "@h"] none),
            .def' "describe" []
              (.send (some (.str "area=")) "+"
                [.send (some (.vcall "area")) "to_s" [] none] none)]),
          .send (some (.send (some (.const "Rect")) "new" [.int 3, .int 4] none))
            "describe" [] none],
    .cls "String", [],
    .seq (.cons (.classStmt rfl rfl rfl .nil .nil)
      (.last (.callMethod
        (.newInst (.constCls rfl rfl) (.cons .intLit (.cons .intLit .nil)) rfl rfl
          (.seq (.cons (.ivarAsgn (.var rfl rfl)) (.last (.ivarAsgn (.var rfl rfl))))))
        .nil rfl rfl
        (.prim .strLit
          (.cons (.prim (.selfCall rfl rfl rfl
                    (.prim .ivarRead (.cons .ivarRead .nil) .intMul))
                   .nil .intToS) .nil)
          .strAdd))))⟩

/-- `class Animal; def speak; "..."; end; end; class Dog < Animal; def speak; "Woof"; end;
    end; Dog.new.speak` → `String`.

    This rung climbs **without any inheritance support**, and it is worth saying why rather
    than letting it look like a lucky pass: `Dog` overrides `speak`, so lookup never has to
    walk up; and `Dog` declares no `initialize`, so `newInstNoInit` handles `Dog.new`.
    `extendClasses` does record `Dog`'s superclass — `Cls.super?` is populated and read by
    nothing yet — and `class-inheritance-field`, whose `Dog` inherits both, is exactly the
    rung that needs the walk and is exactly the one still unclimbed. -/
def r066 : Rung :=
  ⟨"class-inheritance-override",
    .seq [.class' "Animal" none (.def' "speak" [] (.str "...")),
          .class' "Dog" (some (.const "Animal")) (.def' "speak" [] (.str "Woof")),
          .send (some (.send (some (.const "Dog")) "new" [] none)) "speak" [] none],
    .cls "String", [],
    .seq (.cons (.classStmt rfl rfl rfl .nil .nil) (.cons (.classStmt rfl rfl rfl .nil .nil)
      (.last (.callMethod (.newInstNoInit (.constCls rfl rfl) .nil rfl rfl)
        .nil rfl rfl .strLit))))⟩

/-- `a = Point.new(1); b = Point.new(2); a.getX + b.getX` → `Integer`. Two instances of one
    class, and the point is that they get the *same* type — `pointSpine1` both times —
    because they were built at the same argument shape. Two `new`s at different shapes would
    get different types, which is `newInst`'s whole design and something no rung tests
    directly. -/
def r068 : Rung :=
  ⟨"class-multiple-instances",
    .seq [.class' "Point" none (.seq [
            .def' "initialize" [.req "x"] (.vasgn .ivar "@x" (.var .lvar "x")),
            .def' "getX" [] (.var .ivar "@x")]),
          .vasgn .lvar "a" (.send (some (.const "Point")) "new" [.int 1] none),
          .vasgn .lvar "b" (.send (some (.const "Point")) "new" [.int 2] none),
          .send (some (.send (some (.var .lvar "a")) "getX" [] none)) "+"
            [.send (some (.var .lvar "b")) "getX" [] none] none],
    .int, [("a", .inst "Point" pointSpine1), ("b", .inst "Point" pointSpine1)],
    .seq (.cons (.classStmt rfl rfl rfl .nil .nil)
      (.cons (.vasgn (.newInst (.constCls rfl rfl) (.cons .intLit .nil) rfl rfl
                (.ivarAsgn (.var rfl rfl))))
        (.cons (.vasgn (.newInst (.constCls rfl rfl) (.cons .intLit .nil) rfl rfl
                  (.ivarAsgn (.var rfl rfl))))
          (.last (.prim
            (.callMethod (.var rfl rfl) .nil rfl rfl .ivarRead)
            (.cons (.callMethod (.var rfl rfl) .nil rfl rfl .ivarRead) .nil)
            .intAdd)))))⟩

/-- `class Greeter; def hi; "hi"; end; end; Greeter.new.hi` → `String`. The rung that pins
    `newInstNoInit`: no `initialize`, so the spine is empty and — the load-bearing part —
    the argument list must be empty too, because `Object#new` inherited unchanged raises
    `ArgumentError` on any argument. -/
def r069 : Rung :=
  ⟨"class-no-initialize",
    .seq [.class' "Greeter" none (.def' "hi" [] (.str "hi")),
          .send (some (.send (some (.const "Greeter")) "new" [] none)) "hi" [] none],
    .cls "String", [],
    .seq (.cons (.classStmt rfl rfl rfl .nil .nil)
      (.last (.callMethod (.newInstNoInit (.constCls rfl rfl) .nil rfl rfl)
        .nil rfl rfl .strLit)))⟩

/-- `class Box; def reveal; @secret; end; end; Box.new.reveal` → **`Nil`**. Reading an
    instance variable that was never assigned yields `nil` in Ruby — it does not raise — so
    `ivarRead`'s `.getD .nilT` is the rule's content rather than a fallback, and this is the
    rung that says so. The claim is checked by execution: the semantics really produces a
    `NilClass` here. -/
def r070 : Rung :=
  ⟨"class-ivar-lazy-nil",
    .seq [.class' "Box" none (.def' "reveal" [] (.var .ivar "@secret")),
          .send (some (.send (some (.const "Box")) "new" [] none)) "reveal" [] none],
    .nilT, [],
    .seq (.cons (.classStmt rfl rfl rfl .nil .nil)
      (.last (.callMethod (.newInstNoInit (.constCls rfl rfl) .nil rfl rfl)
        .nil rfl rfl .ivarRead)))⟩

/-- `[Point.new(1), Point.new(2)]` → `arrayOf (inst Point {@x: Int})`. The rung where the
    ivar spine appears in a rung's *own* declared type rather than only inside a derivation,
    and where tier 5's `elemTy` meets tier 7's instances: the two elements have the same
    `.inst` type, so `joinT`'s equality case answers and no union appears. Two instances at
    different argument shapes would produce a union here — correctly, and no rung asks. -/
def r071 : Rung :=
  ⟨"class-array-of-instances",
    .seq [.class' "Point" none
            (.def' "initialize" [.req "x"] (.vasgn .ivar "@x" (.var .lvar "x"))),
          .array [.send (some (.const "Point")) "new" [.int 1] none,
                  .send (some (.const "Point")) "new" [.int 2] none]],
    .arrayOf (.inst "Point" pointSpine1), [],
    .seq (.cons (.classStmt rfl rfl rfl .nil .nil)
      (.last (.arrayLit
        (τs := [.inst "Point" pointSpine1, .inst "Point" pointSpine1])
        (.cons (.newInst (.constCls rfl rfl) (.cons .intLit .nil) rfl rfl
                 (.ivarAsgn (.var rfl rfl)))
          (.cons (.newInst (.constCls rfl rfl) (.cons .intLit .nil) rfl rfl
                   (.ivarAsgn (.var rfl rfl))) .nil)))))⟩

/-- `{"origin" => Point.new(0)}` → `T::Hash[String, Point{@x: Integer}]`.

    **Retyped at tier 17b.** The original note read "the instance's type is derived and then
    discarded, because `Ty` has no `hashOf` — the same gap tier 5's `hash-lit` records, now
    throwing away something the checker worked harder for". It is no longer thrown away, and
    the value type is the full `.inst` **with its ivar spine** — so a hash of objects now
    carries as much information as the objects do. -/
def r072 : Rung :=
  ⟨"class-instance-in-hash",
    .seq [.class' "Point" none
            (.def' "initialize" [.req "x"] (.vasgn .ivar "@x" (.var .lvar "x"))),
          .hash [(.str "origin", .send (some (.const "Point")) "new" [.int 0] none)]],
    .hashOf (.cls "String") (.inst "Point" (.ivarCons "@x" .int .ivar0)), [],
    .seq (.cons (.classStmt rfl rfl rfl .nil .nil)
      (.last (.hashLit (.cons .strLit
        (.newInst (.constCls rfl rfl) (.cons .intLit .nil) rfl rfl
          (.ivarAsgn (.var rfl rfl))) .nil))))⟩

/-- `class Box; def initialize(size); @size = size; end; def grow; @size = @size + 1; end;
    end; Box.new(1).grow` → `Integer`.

    **The boundary case for `callMethod`'s no-retyping premise.** `grow` really does mutate
    an instance variable, and it is admissible only because `Integer + Integer` is an
    `Integer` — the ivar's *type* is unchanged even though its value is not, so
    `ivarSet I "@size" .int` is the spine it started with and the premise `… Iself` holds by
    `rfl`. A `grow` that stored a `String` would be rejected. -/
def r074 : Rung :=
  ⟨"class-setter-method",
    .seq [.class' "Box" none (.seq [
            .def' "initialize" [.req "size"] (.vasgn .ivar "@size" (.var .lvar "size")),
            .def' "grow" []
              (.vasgn .ivar "@size"
                (.send (some (.var .ivar "@size")) "+" [.int 1] none))]),
          .send (some (.send (some (.const "Box")) "new" [.int 1] none)) "grow" [] none],
    .int, [],
    .seq (.cons (.classStmt rfl rfl rfl .nil .nil)
      (.last (.callMethod
        (.newInst (.constCls rfl rfl) (.cons .intLit .nil) rfl rfl
          (.ivarAsgn (.var rfl rfl)))
        (Iself := boxSpine) .nil rfl rfl
        (.ivarAsgn (I' := boxSpine)
          (.prim .ivarRead (.cons .intLit .nil) .intAdd)))))⟩

/-- `def describe(p); p.getX; end; describe(Point.new(5))` → `Integer`. Tier 6's
    per-call-site instantiation meeting tier 7's instances: `describe`'s parameter `p` is
    bound to a full `.inst "Point" {@x: Int}` — spine included — so the `p.getX` inside its
    body dispatches with everything it needs. Nothing declares `describe` to take a
    `Point`. -/
def r075 : Rung :=
  ⟨"class-instance-as-fun-arg",
    .seq [.class' "Point" none (.seq [
            .def' "initialize" [.req "x"] (.vasgn .ivar "@x" (.var .lvar "x")),
            .def' "getX" [] (.var .ivar "@x")]),
          .def' "describe" [.req "p"] (.send (some (.var .lvar "p")) "getX" [] none),
          .send none "describe" [.send (some (.const "Point")) "new" [.int 5] none] none],
    .int, [],
    .seq (.cons (.classStmt rfl rfl rfl .nil .nil) (.cons .defStmt
      (.last (.callDef
        (.cons (.newInst (.constCls rfl rfl) (.cons .intLit .nil) rfl rfl
                 (.ivarAsgn (.var rfl rfl))) .nil)
        rfl rfl
        (.callMethod (.var rfl rfl) .nil rfl rfl .ivarRead)))))⟩

/-- `Point.new(7).myself.getX` where `def myself; self; end` → `Integer`. The rung
    `selfExpr` exists for, and the reason its type is `κ.selfTy` rather than "a `Point`":
    `myself` returns a value whose type still carries `@x : Integer`, so the `.getX` chained
    onto it can still read the ivar out. A `self` typed as the bare `.cls "Point"` would
    lose the spine and this rung would not climb. -/
def r076 : Rung :=
  ⟨"class-self-returning-method",
    .seq [.class' "Point" none (.seq [
            .def' "initialize" [.req "x"] (.vasgn .ivar "@x" (.var .lvar "x")),
            .def' "getX" [] (.var .ivar "@x"),
            .def' "myself" [] .self']),
          .send (some (.send (some (.send (some (.const "Point")) "new" [.int 7] none))
            "myself" [] none)) "getX" [] none],
    .int, [],
    .seq (.cons (.classStmt rfl rfl rfl .nil .nil)
      (.last (.callMethod
        (.callMethod
          (.newInst (.constCls rfl rfl) (.cons .intLit .nil) rfl rfl
            (.ivarAsgn (.var rfl rfl)))
          .nil rfl rfl (.selfExpr rfl))
        .nil rfl rfl .ivarRead)))⟩

/-! ### Tier 7's hierarchy — the last three

Each of these is about a place where "which class?" has a different answer from the obvious
one, and the derivations are where that shows: `class-inheritance-field`'s two `mroGet?`
`rfl`s each resolve on a class the receiver is *not*; `class-super-call`'s `superCall`
resolves on the class the running method was *declared* in; and `class-factory-method`'s body
is judged with `self` typed `.clsOf "Point"` rather than as an instance. -/

/-- `class Animal; def initialize(name); @name = name; end; def speak; @name; end; end;
    class Dog < Animal; end; Dog.new("Rex").speak` → `String`.

    `Dog` declares nothing at all — its body is `nil` — so both `rfl`s below resolve on
    `Animal`: `mroGet? C "Dog" "initialize"` walks up to find the constructor that builds the
    spine, and `mroGet? C "Dog" "speak"` walks up again to find the reader. The instance's
    type is still `.inst "Dog" {@name: String}`: the class is the receiver's, the *method* is
    the ancestor's, and keeping those separate is what `mroGet?` returning the definition
    site is for. -/
def r065 : Rung :=
  ⟨"class-inheritance-field",
    .seq [.class' "Animal" none (.seq [
            .def' "initialize" [.req "name"] (.vasgn .ivar "@name" (.var .lvar "name")),
            .def' "speak" [] (.var .ivar "@name")]),
          .class' "Dog" (some (.const "Animal")) .nil,
          .send (some (.send (some (.const "Dog")) "new" [.str "Rex"] none))
            "speak" [] none],
    .cls "String", [],
    .seq (.cons (.classStmt rfl rfl rfl .nil .nil) (.cons (.classStmt rfl rfl rfl .nil .nil)
      (.last (.callMethod
        (.newInst (.constCls rfl rfl) (.cons .strLit .nil) rfl rfl (.ivarAsgn (.var rfl rfl)))
        .nil rfl rfl .ivarRead))))⟩

/-- `class Shape; def initialize(sides); @sides = sides; end; def sides; @sides; end; end;
    class Triangle < Shape; def initialize; super(3); end; end; Triangle.new.sides` →
    `Integer`. **The rung `Ctx.frame` exists for.**

    `Triangle#initialize` takes no arguments and delegates. The class `super` walks up from is
    `Triangle` — the class this running method was *declared* in — which `κ.selfTy` cannot
    say (and which is not even set inside a constructor). `newInst` therefore enters the body
    through `Ctx.inCtor`, recording the definition site and nothing else, and `superCall`
    reads it back.

    The other half is that **the spine threads through the `super`**: `Shape#initialize`'s
    body is judged with the spine as of the end of `super`'s arguments and its outgoing spine
    becomes the super call's, which becomes `Triangle#initialize`'s, which is the one
    `newInst` puts in the type. `@sides` is set by the *parent*, in the *child's* object, and
    the derivation is that sentence. -/
def r067 : Rung :=
  ⟨"class-super-call",
    .seq [.class' "Shape" none (.seq [
            .def' "initialize" [.req "sides"] (.vasgn .ivar "@sides" (.var .lvar "sides")),
            .def' "sides" [] (.var .ivar "@sides")]),
          .class' "Triangle" (some (.const "Shape"))
            (.def' "initialize" [] (.super' [.int 3] none)),
          .send (some (.send (some (.const "Triangle")) "new" [] none)) "sides" [] none],
    .int, [],
    .seq (.cons (.classStmt rfl rfl rfl .nil .nil) (.cons (.classStmt rfl rfl rfl .nil .nil)
      (.last (.callMethod
        (.newInst (.constCls rfl rfl) .nil rfl rfl
          (.superCall (.cons .intLit .nil) rfl rfl rfl rfl rfl
            (.ivarAsgn (.var rfl rfl))))
        .nil rfl rfl .ivarRead))))⟩

/-- `class Point; def initialize(x, y); @x = x; @y = y; end; def self.origin; new(0, 0);
    end; end; Point.origin` → `inst Point {@x: Int, @y: Int}`.

    Two things that no earlier rung has. `origin` lives in a **separate method table**
    (`Cls.smethods`, filled by `clsMember?`'s `defs .self'` case), reached by `smroGet?` —
    `Point.origin` and a `Point`'s `origin` would be different methods. And its body is judged
    with `self` typed **`.clsOf "Point"`**, which is what lets the bare `new(0, 0)` inside it
    mean "allocate one of me": that `send none "new" …` is `selfNew`, an implicit-self call
    resolved against a `self` that is a class object rather than an instance.

    The rung's declared type is the instance type, spine and all — so this is also the one
    place a factory's product is described as precisely as a direct `Point.new(0, 0)`. -/
def r073 : Rung :=
  ⟨"class-factory-method",
    .seq [.class' "Point" none (.seq [
            .def' "initialize" [.req "x", .req "y"]
              (.seq [.vasgn .ivar "@x" (.var .lvar "x"),
                     .vasgn .ivar "@y" (.var .lvar "y")]),
            .defs .self' "origin" []
              (.send none "new" [.int 0, .int 0] none)]),
          .send (some (.const "Point")) "origin" [] none],
    .inst "Point" (.ivarCons "@x" .int (.ivarCons "@y" .int .ivar0)), [],
    .seq (.cons (.classStmt rfl rfl rfl .nil .nil)
      (.last (.callSMethod (.constCls rfl rfl) .nil rfl rfl
        (.selfNew rfl (.cons .intLit (.cons .intLit .nil)) rfl rfl
          (.seq (.cons (.ivarAsgn (.var rfl rfl)) (.last (.ivarAsgn (.var rfl rfl)))))))))⟩

/-! ## Tier 8 — modules

**The cheapest tier on the ladder, and that is the finding rather than luck.** Every one of
these ten rungs is `module M; def self.foo; …; end; M.foo(args)`, and `M.foo` is
`callSMethod` — tier 7's singleton-method rule — with *nothing added*. A module already was,
in this judgment, an object with a singleton method table; the only rules tier 8 needed were
`moduleStmt` (a statement type, because `Expr.module'` is a different head from `class'`) and
`selfSCall` (the bare-name form, because `self` inside a module method is a `.clsOf`, not an
instance).

What tier 8 *did* need was a soundness guard in the other direction: `Cls.isModule`, because
**a module cannot be allocated**. Without it `M.new` would find no `initialize`, fall through
to the zero-argument allocator, and certify a program that raises `NoMethodError`. The rungs
below never write `new`, so the flag is invisible in them and visible only in
`CheckRungs.lean`'s control — which is exactly the shape of guard that would have rotted
undetected without one.

Read the derivations as a pair of `rfl`s each: `smroGet?` (the module declares that singleton
method) and `paramEnv` (the arity matched). The receiver is always `constCls`, which now
denotes a module object as happily as a class object. -/

/-- `module M; def self.foo; 1; end; end; M.foo` → `Integer`. -/
def r077 : Rung :=
  ⟨"module-basic",
    .seq [.module' "M" (.defs .self' "foo" [] (.int 1)),
          .send (some (.const "M")) "foo" [] none],
    .int, [],
    .seq (.cons (.moduleStmt rfl rfl rfl .nil .nil)
      (.last (.callSMethod (.constCls rfl rfl) .nil rfl rfl .intLit)))⟩

/-- `module Greeter; def self.hello(name); "hi " + name; end; end; Greeter.hello("sam")` →
    `String`. A parameter, so `paramEnv` binds it at the call site's `String` and the body's
    `strAdd` is only admissible because of that — the same per-call-site instantiation tier 6
    introduced, now on a module. -/
def r078 : Rung :=
  ⟨"module-method-with-arg",
    .seq [.module' "Greeter" (.defs .self' "hello" [.req "name"]
            (.send (some (.str "hi ")) "+" [.var .lvar "name"] none)),
          .send (some (.const "Greeter")) "hello" [.str "sam"] none],
    .cls "String", [],
    .seq (.cons (.moduleStmt rfl rfl rfl .nil .nil)
      (.last (.callSMethod (.constCls rfl rfl) (.cons .strLit .nil) rfl rfl
        (.prim .strLit (.cons (.var rfl rfl) .nil) .strAdd))))⟩

/-- `M.foo + M.bar` where both are module methods → `Integer`. Two singleton lookups in one
    expression, so the rung that would catch an `smroGet?` keyed on anything but the name. -/
def r079 : Rung :=
  ⟨"module-multiple-methods",
    .seq [.module' "M" (.seq [.defs .self' "foo" [] (.int 1),
                              .defs .self' "bar" [] (.int 2)]),
          .send (some (.send (some (.const "M")) "foo" [] none)) "+"
            [.send (some (.const "M")) "bar" [] none] none],
    .int, [],
    .seq (.cons (.moduleStmt rfl rfl rfl .nil .nil)
      (.last (.prim
        (.callSMethod (.constCls rfl rfl) .nil rfl rfl .intLit)
        (.cons (.callSMethod (.constCls rfl rfl) .nil rfl rfl .intLit) .nil)
        .intAdd)))⟩

/-- `module M; def self.value; 21; end; def self.describe; value * 2; end; end; M.describe`
    → `Integer`. **The rung `selfSCall` exists for.** The `value` inside `describe` is a
    `vcall`, and resolving it needs `self` to be typed `.clsOf "M"` *and* the lookup to go to
    the singleton table — a plain `def value` of the same name would be a different method
    and would correctly not be found. -/
def r080 : Rung :=
  ⟨"module-method-calls-method",
    .seq [.module' "M" (.seq [.defs .self' "value" [] (.int 21),
            .defs .self' "describe" []
              (.send (some (.vcall "value")) "*" [.int 2] none)]),
          .send (some (.const "M")) "describe" [] none],
    .int, [],
    .seq (.cons (.moduleStmt rfl rfl rfl .nil .nil)
      (.last (.callSMethod (.constCls rfl rfl) .nil rfl rfl
        (.prim (.selfSCall rfl rfl rfl .intLit) (.cons .intLit .nil) .intMul))))⟩

/-- `module Calc; def self.add(a, b); a + b; end; end; Calc.add(1, 2)` → `Integer`. -/
def r081 : Rung :=
  ⟨"module-with-arithmetic",
    .seq [.module' "Calc" (.defs .self' "add" [.req "a", .req "b"]
            (.send (some (.var .lvar "a")) "+" [.var .lvar "b"] none)),
          .send (some (.const "Calc")) "add" [.int 1, .int 2] none],
    .int, [],
    .seq (.cons (.moduleStmt rfl rfl rfl .nil .nil)
      (.last (.callSMethod (.constCls rfl rfl) (.cons .intLit (.cons .intLit .nil)) rfl rfl
        (.prim (.var rfl rfl) (.cons (.var rfl rfl) .nil) .intAdd))))⟩

/-- `M1.foo` where `M1`'s body calls `M2.bar` → `Integer`. A module method reaching another
    *module*, so the derivation nests a whole `callSMethod` inside one — and it works
    regardless of declaration order, for the same reason `fun-calling-another-fun` does: the
    body is checked against the table in force at `M1.foo`'s call site, by which time both
    `module` statements have run. -/
def r082 : Rung :=
  ⟨"module-calling-another-module",
    .seq [.module' "M2" (.defs .self' "bar" [] (.int 10)),
          .module' "M1" (.defs .self' "foo" []
            (.send (some (.send (some (.const "M2")) "bar" [] none)) "+"
              [.int 1] none)),
          .send (some (.const "M1")) "foo" [] none],
    .int, [],
    .seq (.cons (.moduleStmt rfl rfl rfl .nil .nil) (.cons (.moduleStmt rfl rfl rfl .nil .nil)
      (.last (.callSMethod (.constCls rfl rfl) .nil rfl rfl
        (.prim (.callSMethod (.constCls rfl rfl) .nil rfl rfl .intLit)
          (.cons .intLit .nil) .intAdd)))))⟩

/-- `module M; def self.pair; [1, 2]; end; end; M.pair` → `arrayOf Int`. A structured return
    type out of a module method, i.e. tier 5's `elemTy` reached through tier 8's dispatch. -/
def r083 : Rung :=
  ⟨"module-returns-array",
    .seq [.module' "M" (.defs .self' "pair" [] (.array [.int 1, .int 2])),
          .send (some (.const "M")) "pair" [] none],
    .arrayOf .int, [],
    .seq (.cons (.moduleStmt rfl rfl rfl .nil .nil)
      (.last (.callSMethod (.constCls rfl rfl) .nil rfl rfl
        (.arrayLit (.cons .intLit (.cons .intLit .nil))))))⟩

/-- `module M; def self.positive?(n); n > 0; end; end; M.positive?(5)` → `Bool`. A method
    name ending in `?` is an ordinary name — nothing in the judgment or the lookup treats it
    specially — and the `>` row is the one admitted in clink 1 with no rung asking; this is
    the rung that finally asks. -/
def r084 : Rung :=
  ⟨"module-boolean-method",
    .seq [.module' "M" (.defs .self' "positive?" [.req "n"]
            (.send (some (.var .lvar "n")) ">" [.int 0] none)),
          .send (some (.const "M")) "positive?" [.int 5] none],
    .bool, [],
    .seq (.cons (.moduleStmt rfl rfl rfl .nil .nil)
      (.last (.callSMethod (.constCls rfl rfl) (.cons .intLit .nil) rfl rfl
        (.prim (.var rfl rfl) (.cons .intLit .nil) .intGt))))⟩

/-- `M.greeting.length` → `Integer`. A `PrimSig` row consuming a module method's result, so
    the rung that pins the result type being a real `Ty` and not something inert. -/
def r085 : Rung :=
  ⟨"module-nested-call-chain",
    .seq [.module' "M" (.defs .self' "greeting" [] (.str "hi")),
          .send (some (.send (some (.const "M")) "greeting" [] none)) "length" [] none],
    .int, [],
    .seq (.cons (.moduleStmt rfl rfl rfl .nil .nil)
      (.last (.prim (.callSMethod (.constCls rfl rfl) .nil rfl rfl .strLit)
        .nil .strLength)))⟩

/-- `M.sum3(1, 2, 3)` → `Integer`. Three parameters, so `paramEnv`'s length match again. -/
def r086 : Rung :=
  ⟨"module-passing-multiple-args",
    .seq [.module' "M" (.defs .self' "sum3" [.req "a", .req "b", .req "c"]
            (.send (some (.send (some (.var .lvar "a")) "+" [.var .lvar "b"] none))
              "+" [.var .lvar "c"] none)),
          .send (some (.const "M")) "sum3" [.int 1, .int 2, .int 3] none],
    .int, [],
    .seq (.cons (.moduleStmt rfl rfl rfl .nil .nil)
      (.last (.callSMethod (.constCls rfl rfl)
        (.cons .intLit (.cons .intLit (.cons .intLit .nil))) rfl rfl
        (.prim (.prim (.var rfl rfl) (.cons (.var rfl rfl) .nil) .intAdd)
          (.cons (.var rfl rfl) .nil) .intAdd))))⟩

/-! ## Tier 9a — callable values

Seven of tier 9's twenty-two: the ones whose callable is created and invoked with `lambda`,
`proc` and `#call`/`#[]`, with no block ever *passed to* a method. See `Ty.clos` for the
design and `implementation-notes.md` clink 9 for what is left.

The `ty` fields are the unusual thing here: a callable's type is `.clos idx captured`, an
index into the whole-program block table plus the locals the lambda closed over. Both halves
are written out longhand below, so a wrong `collectBlocks` order or a wrong captured
environment stops the rung compiling. The indices are not arbitrary — they are the order
`collectBlocks` walks the program — and `lambda-returns-lambda` is the rung where reading them
off tells you something: the outer literal is 0 and the inner is 1, because the collector
descends into a block's body. -/

/-- `f = lambda { 1 }; f.call` → `Integer`. The degenerate callable: no parameters, so
    `paramEnv [] []` is empty and the body is judged in the captured environment alone (also
    empty). The type `.clos 0 ivar0` is the whole of what the checker knows about `f`. -/
def r087 : Rung :=
  ⟨"lambda-zero-arity",
    .seq [.vasgn .lvar "f" (.send none "lambda" [] (some (.block [] [] (.int 1)))),
          .send (some (.var .lvar "f")) "call" [] none],
    .int, [("f", .clos 0 .ivar0 .never)],
    .seq (.cons (.vasgn (.lambdaLit (idx := 0) (.inl rfl) rfl))
      (.last (.closCall (.inl rfl) (.var rfl rfl) .nil rfl rfl .intLit rfl)))⟩

/-- `lambda { |x| x + 1 }.call(2)` → `Integer`. **The rung that shows why a callable's type
    is a reference and not an arrow.** Nothing in `lambda { |x| x + 1 }` says `x` is an
    `Integer`; the `2` at the call site does, and `closCall` is where the two meet — the body
    is judged with `x : Int` because that is what this call passed. -/
def r088 : Rung :=
  ⟨"lambda-stabby-one-param",
    .send (some (.send none "lambda" []
      (some (.block [.req "x"] [] (.send (some (.var .lvar "x")) "+" [.int 1] none)))))
      "call" [.int 2] none,
    .int, [],
    .closCall (.inl rfl) (.lambdaLit (idx := 0) (.inl rfl) rfl)
      (.cons .intLit .nil) rfl rfl
      (.prim (.var rfl rfl) (.cons .intLit .nil) .intAdd) rfl⟩

/-- `p = proc { |x| x * 2 }; p.call(3)` → `Integer`. `proc` takes the same rule as `lambda`
    (`.inr rfl` rather than `.inl rfl` is the only difference in the whole derivation), which
    is the recorded imprecision: this checker imposes a lambda's *strict* arity on both. See
    `Judge.lambdaLit`, and `proc-arity-leniency` for the rung that pays for it. -/
def r089 : Rung :=
  ⟨"proc-basic",
    .seq [.vasgn .lvar "p" (.send none "proc" []
            (some (.block [.req "x"] []
              (.send (some (.var .lvar "x")) "*" [.int 2] none)))),
          .send (some (.var .lvar "p")) "call" [.int 3] none],
    .int, [("p", .clos 0 .ivar0 .never)],
    .seq (.cons (.vasgn (.lambdaLit (idx := 0) (.inr rfl) rfl))
      (.last (.closCall (.inl rfl) (.var rfl rfl) (.cons .intLit .nil) rfl rfl
        (.prim (.var rfl rfl) (.cons .intLit .nil) .intMul) rfl)))⟩

/-- `p = proc { |x| x * 2 }; p[3]` → `Integer`. `p[3]` is Ruby's other spelling of
    `p.call(3)`, so it is the same rule reached through `.inr rfl` on the *method-name*
    disjunction. Worth having as its own rung because `[]` is also `PrimSig.arrayIndex`'s
    method name: the two cannot collide, because that row's receiver is an `arrayOf` and this
    rule's is a `.clos`. -/
def r090 : Rung :=
  ⟨"proc-bracket-call",
    .seq [.vasgn .lvar "p" (.send none "proc" []
            (some (.block [.req "x"] []
              (.send (some (.var .lvar "x")) "*" [.int 2] none)))),
          .send (some (.var .lvar "p")) "[]" [.int 3] none],
    .int, [("p", .clos 0 .ivar0 .never)],
    .seq (.cons (.vasgn (.lambdaLit (idx := 0) (.inr rfl) rfl))
      (.last (.closCall (.inr rfl) (.var rfl rfl) (.cons .intLit .nil) rfl rfl
        (.prim (.var rfl rfl) (.cons .intLit .nil) .intMul) rfl)))⟩

/-- `n = 10; add_n = lambda { |x| x + n }; add_n.call(5)` → `Integer`. **The rung the
    captured spine exists for.** `n` is not a parameter and is not in scope where the body is
    checked — unless the type carries it, which is what `.clos 0 (ivarCons "n" Int ivar0)`
    says. Read `add_n`'s entry in the `outEnv` below and the closure is legible as a type. -/
def r098 : Rung :=
  ⟨"lambda-closure-capture",
    .seq [.vasgn .lvar "n" (.int 10),
          .vasgn .lvar "add_n" (.send none "lambda" []
            (some (.block [.req "x"] []
              (.send (some (.var .lvar "x")) "+" [.var .lvar "n"] none)))),
          .send (some (.var .lvar "add_n")) "call" [.int 5] none],
    .int, [("n", .int), ("add_n", .clos 0 (.ivarCons "n" .int .ivar0) .never)],
    .seq (.cons (.vasgn .intLit)
      (.cons (.vasgn (.lambdaLit (idx := 0) (.inl rfl) rfl))
        (.last (.closCall (.inl rfl) (.var rfl rfl) (.cons .intLit .nil) rfl rfl
          (.prim (.var rfl rfl) (.cons (.var rfl rfl) .nil) .intAdd) rfl))))⟩

/-- `add = lambda { |x| lambda { |y| x + y } }; add.call(1).call(2)` → `Integer`.
    **Currying, with no arrow type anywhere.**

    The outer call returns `.clos 1 (ivarCons "x" Int ivar0)` — index 1 because
    `collectBlocks` descends into a block's body, and the captured `x` because the inner
    literal was reached while `x` was the outer's parameter. Then the second `.call` judges
    the inner body in `[("y", Int)] ++ [("x", Int)]`. Nothing in the program is annotated and
    nothing in the derivation is an arrow; the type of a two-stage function here is just
    "block 0, having captured nothing", and the intermediate value's type is what does the
    work. -/
def r099 : Rung :=
  ⟨"lambda-returns-lambda",
    .seq [.vasgn .lvar "add" (.send none "lambda" []
            (some (.block [.req "x"] []
              (.send none "lambda" []
                (some (.block [.req "y"] []
                  (.send (some (.var .lvar "x")) "+" [.var .lvar "y"] none))))))),
          .send (some (.send (some (.var .lvar "add")) "call" [.int 1] none))
            "call" [.int 2] none],
    .int, [("add", .clos 0 .ivar0 .never)],
    .seq (.cons (.vasgn (.lambdaLit (idx := 0) (.inl rfl) rfl))
      (.last (.closCall (.inl rfl)
        (.closCall (.inl rfl) (.var rfl rfl) (.cons .intLit .nil) rfl rfl
          (.lambdaLit (idx := 1) (.inl rfl) rfl) rfl)
        (.cons .intLit .nil) rfl rfl
        (.prim (.var rfl rfl) (.cons (.var rfl rfl) .nil) .intAdd) rfl)))⟩

/-- `def apply(f, v); f.call(v); end; apply(lambda { |x| x * 2 }, 5)` → `Integer`. A callable
    passed as an ordinary argument: tier 6's `paramEnv` binds `f` to `.clos 0 ivar0` exactly
    as it would bind an `Int`, and `closCall` inside `apply`'s body reads the index back out.
    Nothing declares `apply` to take a function. -/
def r100 : Rung :=
  ⟨"lambda-as-argument",
    .seq [.def' "apply" [.req "f", .req "v"]
            (.send (some (.var .lvar "f")) "call" [.var .lvar "v"] none),
          .send none "apply"
            [.send none "lambda" []
               (some (.block [.req "x"] []
                 (.send (some (.var .lvar "x")) "*" [.int 2] none))),
             .int 5] none],
    .int, [],
    .seq (.cons .defStmt
      (.last (.callDef
        (.cons (.lambdaLit (idx := 0) (.inl rfl) rfl) (.cons .intLit .nil)) rfl rfl
        (.closCall (.inl rfl) (.var rfl rfl) (.cons (.var rfl rfl) .nil) rfl rfl
          (.prim (.var rfl rfl) (.cons .intLit .nil) .intMul) rfl))))⟩

/-! ### Tier 9b — a block reaching a method

Three more, and the shift is in *where the block goes*: in tier 9a a block literal was the
value; here it is passed to a method, so `callDefBlk` puts it in two places at once — in
`Ctx.blockTy` for `yield` to find, and in front of `paramEnvB` for a `&b` parameter to name.
One rung uses each. The third closes a gap the `bareName` docstring has recorded since tier 6.

Note that a block literal and a lambda literal are the *same node* (`Expr.block`), so both
rungs' block types are `.clos 0 ivar0`, built by the same index into the same
whole-program table. The only difference between tier 9a and 9b is where the node sits. -/

/-- `def twice; yield(1) + yield(2); end; twice { |x| x * 10 }` → `Integer`. **The rung
    `Ctx.blockTy` exists for.**

    `yield` names nothing: Ruby passes a block out of band from the argument list, and this is
    the only way to reach it without a `&b` parameter. So the block's type has to be somewhere
    in the context, and `callDefBlk` is what puts it there. The two `yield`s are checked
    independently, each instantiating the block's body at its own argument type — the same
    per-call-site discipline as every other call in this judgment; here they happen to agree
    at `Int`. -/
def r094 : Rung :=
  ⟨"yield-arith",
    .seq [.def' "twice" []
            (.send (some (.yield' [.int 1])) "+" [.yield' [.int 2]] none),
          .send none "twice" []
            (some (.block [.req "x"] []
              (.send (some (.var .lvar "x")) "*" [.int 10] none)))],
    .int, [],
    .seq (.cons .defStmt
      (.last (.callDefBlk rfl .nil rfl rfl rfl
        (.prim
          (.yieldExpr rfl (.cons .intLit .nil) rfl rfl
            (.prim (.var rfl rfl) (.cons .intLit .nil) .intMul) rfl)
          (.cons (.yieldExpr rfl (.cons .intLit .nil) rfl rfl
            (.prim (.var rfl rfl) (.cons .intLit .nil) .intMul) rfl) .nil)
          .intAdd))))⟩

/-- `def run(&b); b.call(5); end; run { |x| x + 1 }` → `Integer`. The other half of
    `callDefBlk`: the same block, this time *named* by a `&b` parameter, so the body reaches
    it as an ordinary local and `closCall` does the rest. `paramEnvB` is what binds it — and
    the reason it binds `.nilT` when there is no block is that `b` is in scope either way
    (`def run(&b); b; end; run` is `nil`). -/
def r095 : Rung :=
  ⟨"block-param-ampersand",
    .seq [.def' "run" [.block (some "b")]
            (.send (some (.var .lvar "b")) "call" [.int 5] none),
          .send none "run" []
            (some (.block [.req "x"] []
              (.send (some (.var .lvar "x")) "+" [.int 1] none)))],
    .int, [],
    .seq (.cons .defStmt
      (.last (.callDefBlk rfl .nil rfl rfl rfl
        (.closCall (.inl rfl) (.var rfl rfl) (.cons .intLit .nil) rfl rfl
          (.prim (.var rfl rfl) (.cons .intLit .nil) .intAdd) rfl))))⟩

/-- `def apply_twice; doubler = lambda { |x| return x * 2 }; doubler.call(3); end;
    apply_twice` → `Integer`. Two gaps closed at once.

    The **`return` inside the lambda** is handled by `bodyResult`, a function on the body's
    shape rather than a `Judge` rule for `.ret` — read its docstring for why the obvious rule
    is unsound. A `return` anywhere but as the whole body still has no rule.

    The **bare `apply_twice`** is `vcallDef`, closing the conservatism `bareName`'s docstring
    has recorded since tier 6: the desugarer emits a `vcall` for a parenthesis-less call, and
    until now no rule matched one that named a defined method. It is `callDef` at zero
    arguments, assume-then-verify included, which is why `vcallAsm` came with it. -/
def r105 : Rung :=
  ⟨"lambda-explicit-return",
    .seq [.def' "apply_twice" []
            (.seq [.vasgn .lvar "doubler" (.send none "lambda" []
                     (some (.block [.req "x"] []
                       (.ret (some (.send (some (.var .lvar "x")) "*" [.int 2] none)))))),
                   .send (some (.var .lvar "doubler")) "call" [.int 3] none]),
          .vcall "apply_twice"],
    .int, [],
    .seq (.cons .defStmt
      (.last (.vcallDef rfl rfl rfl
        (.seq (.cons (.vasgn (.lambdaLit (idx := 0) (.inl rfl) rfl))
          (.last (.closCall (.inl rfl) (.var rfl rfl) (.cons .intLit .nil) rfl rfl
            (.prim (.var rfl rfl) (.cons .intLit .nil) .intMul) rfl)))))))⟩

/-! ## Tier 11 — features in concert

The tier that adds no feature. Every rung is a *combination* of things that already have
rules, and it exists because a corpus-driven ladder is blind to exactly that: tier 7 gave
instance dispatch, tier 9 gave blocks-passed-to-methods, and nothing in either passes a block
to an instance method — so `A.new.a { |v| v }` had no rule and nobody noticed until a human
wrote ordinary Ruby. Nine of the ten are demands; this is the one that is climbed. -/

/-- `def t; yield(1); end; a = 1; t { |x| a = a + x }; a + 1` → `Integer`. **The boundary case
    for `capIntact`, and the rung that says why it compares types rather than forbidding
    assignment.**

    The block really does mutate a captured local — Ruby blocks capture by reference — and
    that is admissible only because it leaves the *type* alone: `Integer + Integer` is an
    `Integer`. Exactly the boundary `class-setter-method` sits on for instance variables, and
    the final `rfl` below is the `capIntact` check discharging on `a`.

    Its neighbour `xc-block-retypes-capture` is the same program with `a = "s"` instead, and
    it really raises `TypeError`. That one is a permanent negative target, and the pair is
    what stops clink 11's soundness fix from being quietly reverted. -/
def r121 : Rung :=
  ⟨"xc-block-accumulates-capture",
    .seq [.def' "t" [] (.yield' [.int 1]),
          .vasgn .lvar "a" (.int 1),
          .send none "t" []
            (some (.block [.req "x"] []
              (.vasgn .lvar "a"
                (.send (some (.var .lvar "a")) "+" [.var .lvar "x"] none)))),
          .send (some (.var .lvar "a")) "+" [.int 1] none],
    .int, [("a", .int)],
    .seq (.cons .defStmt
      (.cons (.vasgn .intLit)
        (.cons (.callDefBlk rfl .nil rfl rfl rfl
                 (.yieldExpr rfl (.cons .intLit .nil) rfl rfl
                   (.vasgn (.prim (.var rfl rfl) (.cons (.var rfl rfl) .nil) .intAdd)) rfl))
          (.last (.prim (.var rfl rfl) (.cons .intLit .nil) .intAdd)))))⟩

/-! ## Tier 12 — narrowing

The two rungs whose conditions test a local *directly*, which is what makes them the first
two: no aliasing (the condition names `x`, not a desugarer temporary), no `subTy`, and no
class constant. Read the pair together — they are the same program with the polarity of the
test flipped, and the derivations differ only in which of `refineThen`/`refineElse` lands on
which branch. That is the property `corpus/135-narrow-backwards-unsafe` is a permanent
negative for. -/

/-- `a = [1,2,3]; x = a[0]; if x then x + 1 else 0 end` → `Integer`.

    **The rung tier 5 made impossible and tier 12 makes routine.** `Array#[]` answers
    `nilable Int` (`PrimSig.arrayIndex` — an out-of-range index is `nil`), and `nilable Int`
    matches no arithmetic row, so `a[0] + 1` was a recorded negative control from tier 5
    onwards: safe Ruby the checker could not type. The guard is what fixes it, and the fix is
    entirely in the environment the then-branch is typed in — `truthyTy (nilable Int) = Int`,
    so the `.var rfl rfl` below finds `x : Int` and `.intAdd` applies unchanged.

    Read the two branch environments off the outgoing one: `x` leaves as
    `joinT Int nilT = nilable Int`, i.e. the checker forgets the refinement at the merge
    point, which is correct — after the `if`, either branch may have run.

    `corpus/136-narrow-absent-unsafe` is this program with the `if` deleted (`a = []`), and it
    really raises `NoMethodError`. It stays a permanent negative, which is the precise
    statement that the *guard* is what makes this rung safe, not the indexing. -/
def r125 : Rung :=
  ⟨"narrow-nilable-truthy",
    .seq [.vasgn .lvar "a" (.array [.int 1, .int 2, .int 3]),
          .vasgn .lvar "x" (.send (some (.var .lvar "a")) "[]" [.int 0] none),
          .if' (.var .lvar "x")
            (.send (some (.var .lvar "x")) "+" [.int 1] none)
            (some (.int 0))],
    .int, [("a", .arrayOf .int), ("x", .nilable .int)],
    .seq (.cons (.vasgn (.arrayLit (.cons .intLit (.cons .intLit (.cons .intLit .nil)))))
      (.cons (.vasgn (.prim (.var rfl rfl) (.cons .intLit .nil) .arrayIndex))
        (.last (.if' (.var rfl rfl)
                 (.prim (.var rfl rfl) (.cons .intLit .nil) .intAdd)
                 .intLit rfl))))⟩

/-- `a = [1,2,3]; x = a[1]; if x.nil? then 0 else x + 10 end` → `Integer`.

    The same shape with the branches the other way round, and the rung that brings in the
    `nil?` row. Two things are worth reading:

    **The condition has to type, and typing it is where `NilQSafe` is discharged.** The
    `.nilQuery (.nilable .int)` leaf below is the whole guard: `nilable Int` is admitted
    because `Int` is, and `nilable (inst Dog)` would not be, because a program-declared class
    may override `nil?`.

    **The polarity.** `nil?` answering `true` means `x` **is** `nil`, so the *then*-branch is
    the one that learns nothing useful (`isNilTy (nilable Int) = nilT`, and it does not touch
    `x` at all) and the *else*-branch is where `nonNilTy` produces the `Int` that `+ 10`
    needs. A rule that used `truthyTy`/`falsyTy` here — the obvious "reuse the truthiness
    refinement" move — would refine both branches backwards. -/
def r126 : Rung :=
  ⟨"narrow-nilable-nil-check",
    .seq [.vasgn .lvar "a" (.array [.int 1, .int 2, .int 3]),
          .vasgn .lvar "x" (.send (some (.var .lvar "a")) "[]" [.int 1] none),
          .if' (.send (some (.var .lvar "x")) "nil?" [] none)
            (.int 0)
            (some (.send (some (.var .lvar "x")) "+" [.int 10] none))],
    .int, [("a", .arrayOf .int), ("x", .nilable .int)],
    .seq (.cons (.vasgn (.arrayLit (.cons .intLit (.cons .intLit (.cons .intLit .nil)))))
      (.cons (.vasgn (.prim (.var rfl rfl) (.cons .intLit .nil) .arrayIndex))
        (.last (.if' (.prim (.var rfl rfl) .nil (.nilQuery (.nilable .int)))
                 .intLit
                 (.prim (.var rfl rfl) (.cons .intLit .nil) .intAdd) rfl))))⟩

/-- `def pick(flag); if flag then 1 else "s" end; end; v = pick(true);
    if v.is_a?(Integer) then v + 1 else v + "!" end` → `union(Int, String)`.

    **The rung that makes a `union` usable.** The `def` produces one — `if flag` narrows
    nothing (`truthyTy .bool = falsyTy .bool = .bool`, since `Ty` has no singleton `true`),
    so `pick`'s body joins `Int` and `String` — and then `is_a?` takes it apart again:
    `isATy "Integer"` keeps the `.int` member (`builtinAncestors .int` names `Integer`) and
    kills the `.cls "String"` member (its chain does not), and `notATy` does the reverse. So
    `v + 1` and `v + "!"` are typed at the two *different* types the same local has in the
    two branches. Before this clink, no expression in this package could consume a `Ty.union`
    at all.

    Two leaves worth naming. `.constBuiltin .integer rfl rfl` is the first constant this judgment
    types for a class the program did not declare — its second premise is `clsGet? = none`,
    which is what keeps it disjoint from `constCls`. And `.isAQuery`'s third premise is
    `isADispatchOk`, which is `true` here because neither member of the union is an `.inst`,
    so no user-written `is_a?` can be in the way.

    The result type is the union again, which is right: the two branches genuinely return
    different classes, and the join forgets which branch ran. -/
def r127 : Rung :=
  ⟨"narrow-union-is-a",
    .seq [.def' "pick" [.req "flag"]
            (.if' (.var .lvar "flag") (.int 1) (some (.str "s"))),
          .vasgn .lvar "v" (.send none "pick" [.tru] none),
          .if' (.send (some (.var .lvar "v")) "is_a?" [.const "Integer"] none)
            (.send (some (.var .lvar "v")) "+" [.int 1] none)
            (some (.send (some (.var .lvar "v")) "+" [.str "!"] none))],
    .union .int (.cls "String"), [("v", .union .int (.cls "String"))],
    .seq (.cons .defStmt
      (.cons (.vasgn (.callDef (.cons .truLit .nil) rfl rfl
                (.if' (.var rfl rfl) .intLit .strLit rfl)))
        -- `Γc` is written out because `narrowEnvs` appears in `if'`'s *conclusion*: until
        -- the condition's derivation is elaborated Lean cannot reduce it, and the condition
        -- here is three constructors deep. The two tier-12 rungs above need no annotation
        -- because their conditions leave the environment visibly untouched.
        (.last (.if' (Γc := [("v", .union .int (.cls "String"))])
                 (.isAQuery (.var rfl rfl) (.cons (.constBuiltin .integer rfl rfl) .nil) rfl)
                 (.prim (.var rfl rfl) (.cons .intLit .nil) .intAdd)
                 (.prim (.var rfl rfl) (.cons .strLit .nil) .strAdd) rfl))))⟩

/-- `class Animal; def speak; "..."; end; end; class Dog < Animal; def fetch; "ball"; end;
    end; def make(flag) … end; v = make(true); if v.is_a?(Dog) then v.fetch else v.speak end`
    → `String`.

    **The rung whose refinement is asymmetric, which is the whole content of it.**
    `is_a?(Dog)` must narrow the `Animal` member *away* — an `Animal` is not a `Dog` — while
    leaving the `Dog` member; and in the else-branch it must narrow the `Dog` member away
    while leaving `Animal`, because a `Dog` **is** an `Animal` and so cannot survive
    `is_a?(Dog)` being false. Get that backwards and `v.fetch` is called on an `Animal`, which
    raises `NoMethodError`.

    That asymmetry is `isAAnswer`, and `isAAnswer` is where the *negative* answer needs an
    argument: `ancestors? C "Animal" = some ["Animal"]`, and `"Dog"` is not in it, so no
    `Animal` is a `Dog` — **provided the chain is complete**. It is, because a class enters
    `CTable` only if `classMethods?` could read its whole body, and `classMethods?` reads
    only `def`s; a body with `include M` never gets in. See `ancestorsUp`'s docstring, which
    also records the obligation this puts on whichever tier gives `include` a rule.

    Note what did *not* happen: clink 7 predicted `subTy` would come due here, and it did not.
    Narrowing needs *class membership*, which is the ancestor walk `mroGet?` was already
    built on, not `Ty`-level subsumption. `subTy` is still unused. -/
def r130 : Rung :=
  ⟨"narrow-union-subclass",
    .seq [.class' "Animal" none (.def' "speak" [] (.str "...")),
          .class' "Dog" (some (.const "Animal")) (.def' "fetch" [] (.str "ball")),
          .def' "make" [.req "flag"]
            (.if' (.var .lvar "flag")
              (.send (some (.const "Dog")) "new" [] none)
              (some (.send (some (.const "Animal")) "new" [] none))),
          .vasgn .lvar "v" (.send none "make" [.tru] none),
          .if' (.send (some (.var .lvar "v")) "is_a?" [.const "Dog"] none)
            (.send (some (.var .lvar "v")) "fetch" [] none)
            (some (.send (some (.var .lvar "v")) "speak" [] none))],
    .cls "String",
    [("v", .union (.inst "Dog" .ivar0) (.inst "Animal" .ivar0))],
    .seq (.cons (.classStmt rfl rfl rfl .nil .nil) (.cons (.classStmt rfl rfl rfl .nil .nil) (.cons .defStmt
      (.cons (.vasgn (.callDef (.cons .truLit .nil) rfl rfl
                (.if' (.var rfl rfl)
                  (.newInstNoInit (.constCls rfl rfl) .nil rfl rfl)
                  (.newInstNoInit (.constCls rfl rfl) .nil rfl rfl) rfl)))
        -- **The four written-out implicits are the readable part of this rung, not noise.**
        -- `if'`'s conclusion is `joinT τ₁ τ₂` over `joinEnv Γ₁ Γ₂`, and neither `joinT` nor
        -- `joinEnv` is injective, so Lean cannot recover the branch types or the branch
        -- environments from the *result* — it needs them from the premises, and here the
        -- premises are `.callMethod`s whose receiver type is itself read out of the branch
        -- environment. So they are stated, and stating them is exactly stating what narrowing
        -- did: `Γ₁` has `v : Dog`, `Γ₂` has `v : Animal`, and the join puts the union back.
        -- `Γc` is written for the same reason: `narrowEnvs` appears in the conclusion.
        (.last (.if'
                 (Γc := [("v", .union (.inst "Dog" .ivar0) (.inst "Animal" .ivar0))])
                 (Γ₁ := [("v", .inst "Dog" .ivar0)])
                 (Γ₂ := [("v", .inst "Animal" .ivar0)])
                 (τ₁ := .cls "String") (τ₂ := .cls "String")
                 (.isAQuery (.var rfl rfl) (.cons (.constCls rfl rfl) .nil) rfl)
                 (.callMethod (.var rfl rfl) .nil rfl rfl .strLit)
                 (.callMethod (.var rfl rfl) .nil rfl rfl .strLit) rfl))))))⟩

/-- `def first_or_zero(a); x = a[0]; return 0 if x.nil?; x + 1; end; first_or_zero([5])`
    → `Integer`.

    **The guard clause — the one narrowing idiom with no `if` around the narrowed code.**
    `x + 1` is a top-level statement of the method body; nothing syntactically encloses it, and
    yet it may treat `x` as an `Integer`, because the only path that reaches it is the one the
    guard let through. So the refinement is applied by a **`JudgeSeq`** rule
    (`JudgeSeq.guard`), not by `Judge.if'`: the fact being used — "that statement did not fall
    through" — is a fact about the *sequence*.

    Read the derivation's shape against the program's: the body is a three-statement `seq`, and
    the derivation is `.cons` (the assignment) then `.guard`, which swallows **both** the guard
    statement and the rest of the sequence. `.guard`'s two `Judge` premises are the condition
    and the *returned* expression (`0`, typed where the guard fired), and its `JudgeSeq` premise
    is `x + 1` typed in `(narrowEnvs …).2`, where `x : Int`. The method's type is
    `joinT Int Int` — a value leaving from somewhere other than the last statement, which is
    the only place in this judgment that happens.

    Note what still has no rule: `.ret` itself. `def f; return "a"; 2; end` remains underivable,
    which is the property `bodyResult`'s docstring argues for and which this rule was shaped
    around rather than against. -/
def r131 : Rung :=
  ⟨"narrow-guard-clause",
    .seq [.def' "first_or_zero" [.req "a"]
            (.seq [.vasgn .lvar "x" (.send (some (.var .lvar "a")) "[]" [.int 0] none),
                   .if' (.send (some (.var .lvar "x")) "nil?" [] none)
                     (.ret (some (.int 0))) none,
                   .send (some (.var .lvar "x")) "+" [.int 1] none]),
          .send none "first_or_zero" [.array [.int 5]] none],
    .int, [],
    .seq (.cons .defStmt
      (.last (.callDef (.cons (.arrayLit (.cons .intLit .nil)) .nil) rfl rfl
        (.seq (.cons (.vasgn (.prim (.var rfl rfl) (.cons .intLit .nil) .arrayIndex))
          (.guard (.prim (.var rfl rfl) .nil (.nilQuery (.nilable .int))) .intLit rfl
            (.last (.prim (.var rfl rfl) (.cons .intLit .nil) .intAdd))))))))⟩

/-- `class Holder; def initialize(flag); if flag then @v = 1 else @v = "s" end; end;
    def describe; if @v.is_a?(Integer) then @v + 1 else @v + "!" end; end; end;
    Holder.new(true).describe` → `union(Int, String)`.

    **The rung that reverses clink 6's most deliberate restriction.** `Judge.if'` used to
    *require* the two branches to agree on the ivar spine, so this class was not typeable at
    all: its `initialize` assigns `@v` at `Int` on one path and `String` on the other, and there
    was no spine that described the result. The premise is now `joinSpine I₁ I₂ = I₃`, and the
    instance's type is `inst Holder (@v : union Int String)`.

    Clink 6's argument for the restriction was not wrong, it was *early*: a spine is part of the
    type of `self`, and widening it to a union is only honest if a union is something code can
    consume. Tier 12 is what made that true, and this rung is the pair — the widening in
    `initialize`, the narrowing in `describe`, and neither is any use without the other.

    Two mechanical points worth reading off the derivation:

    - the condition is `.ivarRead`, and the refinement lands in the **spine** rather than the
      environment (`narrowSpine`, selected by the `VarKind` `narrowCond?` now returns);
    - `callMethod`'s premise that a method may not retype an instance variable
      (`… d.body ρ Γb' Iself`, clink 6's soundness invariant) still holds, and holds *because*
      of the join: the two branches leave `@v` at `Int` and at `String`, and `joinSpine` puts it
      back at exactly the `union` it came in as. Had the join produced anything else, this rung
      would not compile. -/
def r129 : Rung :=
  ⟨"narrow-union-in-ivar",
    .seq [.class' "Holder" none (.seq [
            .def' "initialize" [.req "flag"]
              (.if' (.var .lvar "flag")
                (.vasgn .ivar "@v" (.int 1))
                (some (.vasgn .ivar "@v" (.str "s")))),
            .def' "describe" []
              (.if' (.send (some (.var .ivar "@v")) "is_a?" [.const "Integer"] none)
                (.send (some (.var .ivar "@v")) "+" [.int 1] none)
                (some (.send (some (.var .ivar "@v")) "+" [.str "!"] none)))]),
          .send (some (.send (some (.const "Holder")) "new" [.tru] none)) "describe" [] none],
    .union .int (.cls "String"), [],
    -- `Iself` is written out because `callMethod`'s body premise reads the method's syntax out
    -- of a `Defn` that a *later* premise's `rfl` produces, and the body here is an `if'` whose
    -- own premises mention `narrowSpine … Ic` — so without it the refinement cannot reduce
    -- while the branches are being elaborated. It is also the most informative thing to state
    -- about this rung: it *is* the widened spine.
    (by
      refine .seq (.cons (.classStmt rfl rfl rfl .nil .nil)
        (.last (.callMethod
          (Iself := .ivarCons "@v" (.union .int (.cls "String")) .ivar0) (Γb' := [])
          (.newInst (.constCls rfl rfl) (.cons .truLit .nil) rfl rfl
            (.if' (.var rfl rfl) (.ivarAsgn .intLit) (.ivarAsgn .strLit) rfl))
          .nil rfl rfl ?_)))
      -- `describe`'s body, deferred to a hole so it is elaborated *after* `callMethod`'s
      -- `mroGet?` premise has produced the `Defn` it is the `.body` of. Without that, the
      -- condition's syntax is still a metavariable when `narrowSpine` has to reduce, and the
      -- refined `@v` cannot be computed.
      -- Every index of the `if'` is written out, and then each premise is a separate hole.
      -- The reason is the same one `narrow-union-subclass` records — `joinT`/`joinEnv`/
      -- `joinSpine` are not injective, so the branch types, environments and spines cannot be
      -- recovered from the conclusion — with one addition specific to an *ivar* refinement:
      -- `narrowSpine` also needs the condition's **syntax**, which only the conclusion
      -- supplies. `refine` unifies the conclusion first; the holes are then concrete.
      -- Read the six as the statement of what this rung does: `@v` enters as a union, the
      -- branches see `Int` and `String`, and `joinSpine` returns it to the union.
      refine Judge.if' (Γc := []) (Γ₁ := []) (Γ₂ := [])
        (Ic := .ivarCons "@v" (.union .int (.cls "String")) .ivar0)
        (I₁ := .ivarCons "@v" .int .ivar0)
        (I₂ := .ivarCons "@v" (.cls "String") .ivar0)
        (τ₁ := .int) (τ₂ := .cls "String") (σ := .bool) ?_ ?_ ?_ rfl
      · exact .isAQuery .ivarRead (.cons (.constBuiltin .integer rfl rfl) .nil) rfl
      · exact .prim .ivarRead (.cons .intLit .nil) .intAdd
      · exact .prim .ivarRead (.cons .strLit .nil) .strAdd)⟩

/-! ## Tier 9c — the builtin iterators

The nine rungs `Judge.iterBlock`/`iterSymPass`/`iterClosPass` climb, and the reason they are
worth reading as a group is that **five of them differ only in the iterator's name** and yet
come out at five different types. That is the whole content of `IterSig` (see its section
docstring in `Judge.lean`): a single "block rule" would get most of these wrong.

Every derivation below has the same shape — receiver, arguments, signature, the block's
parameter environment, the block's body, `capIntact` — because the rule does. What differs is
the last thing: the *result*, and which premise justifies it. -/

/-- `[1, 2, 3].each { |x| x + 1 }` → `arrayOf Int`, **the receiver**.

    `each`'s block return type appears nowhere in the result, which is the point of it being a
    separate `IterSig` row from `map`'s: the block is run for effect and its value discarded.
    The body still has to *type* — `[1,2].each { |x| x + "a" }` is a permanent
    `unsafe_program` negative (`block-bad-arith`) precisely because the block wrapper must not
    launder a `TypeError`. -/
def r091 : Rung :=
  ⟨"block-each-int",
    .send (some (.array [.int 1, .int 2, .int 3])) "each" []
      (some (.block [.req "x"] [] (.send (some (.var .lvar "x")) "+" [.int 1] none))),
    .arrayOf .int, [],
    .iterBlock (.arrayLit (.cons .intLit (.cons .intLit (.cons .intLit .nil)))) .nil
      .each rfl (.prim (.var rfl rfl) (.cons .intLit .nil) .intAdd) rfl⟩

/-- `[1, 2, 3].map { |n| n.to_s }` → `arrayOf String`. The `each` rung with one word changed,
    and a different result type: `map`'s row is the one that reads the block's return type. -/
def r092 : Rung :=
  ⟨"block-map-to-s",
    .send (some (.array [.int 1, .int 2, .int 3])) "map" []
      (some (.block [.req "n"] [] (.send (some (.var .lvar "n")) "to_s" [] none))),
    .arrayOf (.cls "String"), [],
    .iterBlock (.arrayLit (.cons .intLit (.cons .intLit (.cons .intLit .nil)))) .nil
      .map rfl (.prim (.var rfl rfl) .nil .intToS) rfl⟩

/-- `[1, 2].map do |x| y = x * 2; y + 1 end` → `arrayOf Int`.

    **The `|x; y|` block-local rung.** The desugarer records `y` in the `block` node's *third*
    field, because a local first assigned inside a `do`/`end` body is block-scoped in Ruby, and
    `blockLocals` binds each of them at `.nilT` — which is what Ruby does (a block-local read
    before assignment is `nil`) and is why the name is in scope at all. `Judge.lambdaLit` still
    refuses a block with locals; nothing needed to change there, because a block passed to an
    iterator never becomes a `Ty.clos`. -/
def r093 : Rung :=
  ⟨"block-doend-with-block-local",
    .send (some (.array [.int 1, .int 2])) "map" []
      (some (.block [.req "x"] ["y"]
        (.seq [.vasgn .lvar "y" (.send (some (.var .lvar "x")) "*" [.int 2] none),
               .send (some (.var .lvar "y")) "+" [.int 1] none]))),
    .arrayOf .int, [],
    .iterBlock (.arrayLit (.cons .intLit (.cons .intLit .nil))) .nil .map rfl
      (.seq (.cons (.vasgn (.prim (.var rfl rfl) (.cons .intLit .nil) .intMul))
        (.last (.prim (.var rfl rfl) (.cons .intLit .nil) .intAdd)))) rfl⟩

/-- `[1, 2].map(&:to_s)` → `arrayOf String`.

    **`Symbol#to_proc`, and the pleasing part is that it needed no new claim about types.** The
    coerced proc sends `to_s` to each element, so the block's return type is the result of a
    send — and `.intToS` below is the *same* `PrimSig` row `block-map-to-s` uses. Two syntaxes,
    one table row. -/
def r096 : Rung :=
  ⟨"block-pass-symbol-to-proc",
    .send (some (.array [.int 1, .int 2])) "map" [] (some (.blockpass (some (.sym "to_s")))),
    .arrayOf (.cls "String"), [],
    .iterSymPass (.arrayLit (.cons .intLit (.cons .intLit .nil))) .nil .map .intToS⟩

/-- `double = ->(x) { x * 2 }; [1, 2].map(&double)` → `arrayOf Int`.

    The other `&` form: the block is a **callable value**, so this is `closCall` with the
    argument types supplied by `IterSig` instead of by a call site. `double`'s type is
    `clos 0 ivar0` — a reference to block 0 of the program plus the (empty) environment it
    captured — and `iterClosPass` instantiates its body at the receiver's element type. -/
def r097 : Rung :=
  ⟨"block-pass-lambda-variable",
    .seq [.vasgn .lvar "double" (.send none "lambda" []
            (some (.block [.req "x"] [] (.send (some (.var .lvar "x")) "*" [.int 2] none)))),
          .send (some (.array [.int 1, .int 2])) "map" []
            (some (.blockpass (some (.var .lvar "double"))))],
    .arrayOf .int, [("double", .clos 0 .ivar0 .never)],
    .seq (.cons (.vasgn (.lambdaLit (idx := 0) (.inl rfl) rfl))
      (.last (.iterClosPass (.arrayLit (.cons .intLit (.cons .intLit .nil))) .nil
        (.var rfl rfl) .map rfl rfl (.prim (.var rfl rfl) (.cons .intLit .nil) .intMul) rfl)))⟩

/-- `[[1, 2], [3, 4]].map { |row| row.map { |x| x + 1 } }` → `arrayOf (arrayOf Int)`.

    Nesting costs nothing, and that is worth checking rather than assuming: the outer block's
    body *is* an iterator call, so the rule applies to itself, with `row : arrayOf Int` coming
    from the outer receiver's element type. Note there is no block *table* involved anywhere —
    `iterBlock` types the block where it stands, so a block inside a block needs no index and
    no captured-environment spine. -/
def r101 : Rung :=
  ⟨"block-nested-map",
    .send (some (.array [.array [.int 1, .int 2], .array [.int 3, .int 4]])) "map" []
      (some (.block [.req "row"] []
        (.send (some (.var .lvar "row")) "map" []
          (some (.block [.req "x"] []
            (.send (some (.var .lvar "x")) "+" [.int 1] none)))))),
    .arrayOf (.arrayOf .int), [],
    .iterBlock
      (.arrayLit (.cons (.arrayLit (.cons .intLit (.cons .intLit .nil)))
        (.cons (.arrayLit (.cons .intLit (.cons .intLit .nil))) .nil))) .nil .map rfl
      (.iterBlock (.var rfl rfl) .nil .map rfl
        (.prim (.var rfl rfl) (.cons .intLit .nil) .intAdd) rfl) rfl⟩

/-- `[1, 2, 3].inject(0) { |acc, x| acc + x }` → `Integer`.

    **The two-parameter iterator, and the only one with an accumulator fixed point.** `α` is
    the initial value's type (`Int`), the block is typed with `acc : α` and `x : elem`, and the
    body is *required to come back at `α`* — because the block's result is the next iteration's
    accumulator. A block that returned something else really would change the accumulator's
    type between iterations, and no single `Ty` describes that. Same assume-then-verify shape as
    `Judge.callDef`'s recursion, with the initial value playing the part of the candidate.

    The result is `α` rather than the block's return type, and they are the same type by that
    premise — which matters for the empty receiver, where `inject` returns `init` and the block
    never runs. -/
def r102 : Rung :=
  ⟨"block-two-params-inject",
    .send (some (.array [.int 1, .int 2, .int 3])) "inject" [.int 0]
      (some (.block [.req "acc", .req "x"] []
        (.send (some (.var .lvar "acc")) "+" [.var .lvar "x"] none))),
    .int, [],
    .iterBlock (.arrayLit (.cons .intLit (.cons .intLit (.cons .intLit .nil))))
      (.cons .intLit .nil) .inject rfl
      (.prim (.var rfl rfl) (.cons (.var rfl rfl) .nil) .intAdd) rfl⟩

/-- `[1, 2, 3, 4].select { |x| if x > 2 then true else false end }` → `arrayOf Int`.

    `select`'s block result is only ever tested for **truthiness**, which never raises in Ruby,
    so `IterSig.select` leaves the block's return type unconstrained — the one iterator row with
    no side condition on `ρ` besides `map`'s (which consumes it) and `each`'s (which discards
    it). The `if` in the body is incidental; it is here because a corpus that only ever put a
    single send in a block body would not have exercised a block body with control flow. -/
def r103 : Rung :=
  ⟨"block-select-with-if",
    .send (some (.array [.int 1, .int 2, .int 3, .int 4])) "select" []
      (some (.block [.req "x"] []
        (.if' (.send (some (.var .lvar "x")) ">" [.int 2] none) .tru (some .fls)))),
    .arrayOf .int, [],
    .iterBlock
      (.arrayLit (.cons .intLit (.cons .intLit (.cons .intLit (.cons .intLit .nil))))) .nil
      .select rfl (.if' (.prim (.var rfl rfl) (.cons .intLit .nil) .intGt) .truLit .flsLit rfl)
      rfl⟩

/-- `["aaa", "b"].sort_by { |s| s.length }` → `arrayOf String`.

    **The iterator whose side condition is a soundness requirement, not precision.**
    `sort_by` compares the block's results with `<=>`, and
    `["a"].sort_by { |s| nil }` raises `ArgumentError` ("comparison of NilClass with NilClass
    failed") — *inside* the NoMethodError/ArgumentError/TypeError family this ladder defines
    type-safety over. So `IterSig.sortBy` carries `Comparable ρ`, discharged here by
    `Comparable.int` because `String#length` answers an `Integer`. An unconstrained `sort_by`
    row would be unsound; `select`'s, in the rung above, is not. -/
def r104 : Rung :=
  ⟨"block-sort-by-length",
    .send (some (.array [.str "aaa", .str "b"])) "sort_by" []
      (some (.block [.req "s"] [] (.send (some (.var .lvar "s")) "length" [] none))),
    .arrayOf (.cls "String"), [],
    .iterBlock (.arrayLit (.cons .strLit (.cons .strLit .nil))) .nil (.sortBy .int) rfl
      (.prim (σ := .cls "String") (.var rfl rfl) .nil .strLength) rfl⟩

/-- `class Shelf; def initialize(items); @items = items; end; def names; @items.map { |i|
    i.to_s }; end; end; Shelf.new([1, 2]).names` → `arrayOf String` (tier 11).

    **The cross-product rung tier 9c unblocked for free**, and the reason it came free is a
    deliberate omission in `iterBlock`: unlike `closCall` and `callDefBlk`, it has **no
    `κ.selfTy = none` premise**. Those two need one because they build a `Ty.clos` whose
    captured environment is only meaningful at a creation site this judgment can describe; here
    nothing is captured into a type, `κ` passes through unchanged, and so `self` inside the
    block body is the `self` outside it — which is exactly Ruby. Hence an iterator may appear
    inside a method body, over an ivar receiver. -/
def r122 : Rung :=
  ⟨"xc-ivar-array-map",
    .seq [.class' "Shelf" none (.seq [
            .def' "initialize" [.req "items"] (.vasgn .ivar "@items" (.var .lvar "items")),
            .def' "names" []
              (.send (some (.var .ivar "@items")) "map" []
                (some (.block [.req "i"] []
                  (.send (some (.var .lvar "i")) "to_s" [] none))))]),
          .send (some (.send (some (.const "Shelf")) "new"
            [.array [.int 1, .int 2]] none)) "names" [] none],
    .arrayOf (.cls "String"), [],
    .seq (.cons (.classStmt rfl rfl rfl .nil .nil)
      (.last (.callMethod
        (.newInst (.constCls rfl rfl) (.cons (.arrayLit (.cons .intLit (.cons .intLit .nil))) .nil)
          rfl rfl (.ivarAsgn (.var rfl rfl)))
        .nil rfl rfl
        (.iterBlock .ivarRead .nil .map rfl (.prim (.var rfl rfl) .nil .intToS) rfl))))⟩

/-- `t = [1, 2]; s = 0; t.each do |x| y = [10, 20][x]; if y then s = s + y end end; s`
    → `Integer` (tier 12).

    **Narrowing inside a block body**, and the rung that shows the two capabilities compose
    without either one knowing about the other. `[10,20][x]` is `nilable Int`
    (`PrimSig.arrayIndex`), `if y` narrows it to `Int` in the then-branch (clink 13), and the
    accumulation `s = s + y` is admissible because it leaves `s`'s *type* alone — which is
    `capIntact`, the clink-11 premise, discharged by the final `rfl`.

    Worth being precise about why carrying the enclosing environment out unchanged is right
    here and not merely convenient: `each` may run the block **zero** times, so the outgoing
    environment cannot be the body's; and `capIntact` says the body did not change any outer
    name's type, so it cannot be wrong to use the incoming one either. The two facts together
    are what make a single environment correct for both cases. -/
def r134 : Rung :=
  ⟨"narrow-in-block",
    .seq [.vasgn .lvar "t" (.array [.int 1, .int 2]),
          .vasgn .lvar "s" (.int 0),
          .send (some (.var .lvar "t")) "each" []
            (some (.block [.req "x"] ["y"]
              (.seq [.vasgn .lvar "y"
                       (.send (some (.array [.int 10, .int 20])) "[]"
                         [.var .lvar "x"] none),
                     .if' (.var .lvar "y")
                       (.vasgn .lvar "s"
                         (.send (some (.var .lvar "s")) "+" [.var .lvar "y"] none))
                       none]))),
          .var .lvar "s"],
    .int, [("t", .arrayOf .int), ("s", .int)],
    .seq (.cons (.vasgn (.arrayLit (.cons .intLit (.cons .intLit .nil))))
      (.cons (.vasgn .intLit)
        (.cons (.iterBlock (.var rfl rfl) .nil .each rfl
                 (.seq (.cons (.vasgn (.prim (.arrayLit (.cons .intLit (.cons .intLit .nil)))
                                        (.cons (.var rfl rfl) .nil) .arrayIndex))
                   (.last (.ifNoElse (.var rfl rfl)
                     (.vasgn (.prim (.var rfl rfl) (.cons (.var rfl rfl) .nil) .intAdd)) rfl))))
                 rfl)
          (.last (.var rfl rfl)))))⟩

/-- `class Box; def initialize(f); @f = f; end; def apply(v); @f.call(v); end; end;
    Box.new(lambda { |x| x * 2 }).apply(4)` → `Integer` (tier 11).

    **A callable stored in an instance variable**, and the rung that made `Ty.clos`'s third
    field necessary. Reading `@f` inside `Box#apply` gives a `.clos`, and calling it means
    typing a body that was written somewhere else entirely — at top level, where `self` was not
    typed and no instance variable existed. `closCall` used to insist that the *call* site have
    `κ.selfTy = none`, which is not a property of the closure at all, and that is exactly the
    premise this program cannot satisfy: `apply`'s `self` is a `Box`.

    Read the `Iself` annotation below and the fix is legible: `Box`'s spine holds
    `@f : <closure#0>`, and `closCall` judges block 0's body against **`.never`** — the `self`
    recorded *in that type* — not against the `Box`. Judging it against the `Box` would be
    unsound in general: an `@y` in the body would read `Box`'s `@y` out of a body belonging to
    `main`. -/
def r117 : Rung :=
  ⟨"xc-lambda-in-ivar",
    .seq [.class' "Box" none (.seq [
            .def' "initialize" [.req "f"] (.vasgn .ivar "@f" (.var .lvar "f")),
            .def' "apply" [.req "v"]
              (.send (some (.var .ivar "@f")) "call" [.var .lvar "v"] none)]),
          .send (some (.send (some (.const "Box")) "new"
            [.send none "lambda" []
              (some (.block [.req "x"] []
                (.send (some (.var .lvar "x")) "*" [.int 2] none)))] none))
            "apply" [.int 4] none],
    .int, [],
    .seq (.cons (.classStmt rfl rfl rfl .nil .nil)
      (.last (.callMethod
        (Iself := .ivarCons "@f" (.clos 0 .ivar0 .never) .ivar0)
        (.newInst (.constCls rfl rfl)
          (.cons (.lambdaLit (idx := 0) (.inl rfl) rfl) .nil) rfl rfl
          (.ivarAsgn (.var rfl rfl)))
        (.cons .intLit .nil) rfl rfl
        (.closCall (.inl rfl) .ivarRead (.cons (.var rfl rfl) .nil) rfl rfl
          (.prim (.var rfl rfl) (.cons .intLit .nil) .intMul) rfl))))⟩

/-- `module Twice; def self.apply(f, v); f.call(f.call(v)); end; end;
    Twice.apply(lambda { |x| x + 1 }, 5)` → `Integer` (tier 11).

    The same lifting, one `self`-shape over: inside `Twice.apply` the `self` is a **class
    object** (`.clsOf "Twice"`), so `closCall`'s old premise failed here too. And the rung
    exercises the composition the tier is named for — `f.call(f.call(v))`, one closure
    instantiated twice at the same argument type, nested. -/
def r123 : Rung :=
  ⟨"xc-module-applies-lambda",
    .seq [.module' "Twice" (.defs .self' "apply" [.req "f", .req "v"]
            (.send (some (.var .lvar "f")) "call"
              [.send (some (.var .lvar "f")) "call" [.var .lvar "v"] none] none)),
          .send (some (.const "Twice")) "apply"
            [.send none "lambda" []
               (some (.block [.req "x"] []
                 (.send (some (.var .lvar "x")) "+" [.int 1] none))),
             .int 5] none],
    .int, [],
    .seq (.cons (.moduleStmt rfl rfl rfl .nil .nil)
      (.last (.callSMethod (.constCls rfl rfl)
        (.cons (.lambdaLit (idx := 0) (.inl rfl) rfl) (.cons .intLit .nil)) rfl rfl
        (.closCall (.inl rfl) (.var rfl rfl)
          (.cons (.closCall (.inl rfl) (.var rfl rfl) (.cons (.var rfl rfl) .nil) rfl rfl
                    (.prim (.var rfl rfl) (.cons .intLit .nil) .intAdd) rfl) .nil)
          rfl rfl (.prim (.var rfl rfl) (.cons .intLit .nil) .intAdd) rfl))))⟩

/-! ## Tier 11 — a block reaching a method of an object

The four rungs that had no rule for a reason worth remembering: tier 9 wrote the
block-carrying call rule only for the **top-level `defs` table**, so `A.new.a { … }` — a
class and a block, both of which had rules — was underivable, and the corpus did not notice
because nothing in it combined them (clink 11). Each derivation below is its block-less twin
plus `callDefBlk`'s two moves: build the block's `Ty.clos`, and put it in *both* `blockTy` and
`paramEnvB`. -/

/-- `class A; def a(&blk); blk.call(3); end; end; A.new.a { |v| v }` → `Integer`.

    The `&blk` route: the block arrives out of band, `paramEnvB` names it, and `blk.call(3)` is
    an ordinary `closCall` — on a `Ty.clos` whose creation `self` is `.never`, because the block
    literal sits at top level even though the *call* is a method call. Both halves of clink
    19's fix are in play at once here: the block reaches an instance method, and its body is
    still judged against the `self` where it was written. -/
def r115 : Rung :=
  ⟨"xc-class-block-param",
    .seq [.class' "A" none
            (.def' "a" [.block (some "blk")]
              (.send (some (.var .lvar "blk")) "call" [.int 3] none)),
          .send (some (.send (some (.const "A")) "new" [] none)) "a" []
            (some (.block [.req "v"] [] (.var .lvar "v")))],
    .int, [],
    .seq (.cons (.classStmt rfl rfl rfl .nil .nil)
      (.last (.callMethodBlk
        (.newInstNoInit (.constCls rfl rfl) .nil rfl rfl) .nil rfl rfl rfl
        (.closCall (.inl rfl) (.var rfl rfl) (.cons .intLit .nil) rfl rfl (.var rfl rfl) rfl))))⟩

/-- `class Counter; def initialize(n); @n = n; end; def bump; yield(@n); end; end;
    Counter.new(5).bump { |x| x + 1 }` → `Integer`.

    The `yield` route, and the rung that needed clink 19's other half: `yieldExpr` used to carry
    `κ.selfTy = none`, which is false inside `Counter#bump`. What crosses the boundary is worth
    tracing — `@n` is read from the **object's** spine (`ivarRead`, inside `bump`), passed as an
    argument to a block whose body is judged against the block's own creation `self` (top level,
    `.never`). Two different `self`s in one derivation, each used where it belongs. -/
def r116 : Rung :=
  ⟨"xc-class-yield-ivar",
    .seq [.class' "Counter" none (.seq [
            .def' "initialize" [.req "n"] (.vasgn .ivar "@n" (.var .lvar "n")),
            .def' "bump" [] (.yield' [.var .ivar "@n"])]),
          .send (some (.send (some (.const "Counter")) "new" [.int 5] none)) "bump" []
            (some (.block [.req "x"] []
              (.send (some (.var .lvar "x")) "+" [.int 1] none)))],
    .int, [],
    .seq (.cons (.classStmt rfl rfl rfl .nil .nil)
      (.last (.callMethodBlk
        (.newInst (.constCls rfl rfl) (.cons .intLit .nil) rfl rfl (.ivarAsgn (.var rfl rfl)))
        .nil rfl rfl rfl
        -- `τ := .int` written out because the block parameter's type comes from
        -- `(ivarGet? Iself "@n").getD .nilT`, which does not reduce until `Iself` is solved --
        -- and `Judge.var`'s `isAliasTy τ = false` premise needs it before then.
        (.yieldExpr rfl (.cons .ivarRead .nil) rfl rfl
          (.prim (.var (τ := .int) rfl rfl) (.cons .intLit .nil) .intAdd) rfl))))⟩

/-- `module Runner; def self.twice; yield(1) + yield(2); end; end;
    Runner.twice { |x| x * 10 }` → `Integer`.

    A module function with a block, and the rung that shows a method may `yield` **more than
    once**: each `yield` is a separate `yieldExpr`, checked independently at its own argument
    types. Here both are `Int`, so both come back `Int`; a method yielding at two different
    types would get two different answers, which is the same per-call-site instantiation the
    whole ladder uses. -/
def r118 : Rung :=
  ⟨"xc-module-yield",
    .seq [.module' "Runner" (.defs .self' "twice" []
            (.send (some (.yield' [.int 1])) "+" [.yield' [.int 2]] none)),
          .send (some (.const "Runner")) "twice" []
            (some (.block [.req "x"] []
              (.send (some (.var .lvar "x")) "*" [.int 10] none)))],
    .int, [],
    .seq (.cons (.moduleStmt rfl rfl rfl .nil .nil)
      (.last (.callSMethodBlk (.constCls rfl rfl) .nil rfl rfl rfl
        (.prim
          (.yieldExpr rfl (.cons .intLit .nil) rfl rfl
            (.prim (.var rfl rfl) (.cons .intLit .nil) .intMul) rfl)
          (.cons (.yieldExpr rfl (.cons .intLit .nil) rfl rfl
            (.prim (.var rfl rfl) (.cons .intLit .nil) .intMul) rfl) .nil)
          .intAdd))))⟩

/-- `class Base; def wrap; "[" + yield.to_s + "]"; end; end;
    class Child < Base; def show; wrap { 7 }; end; end; Child.new.show` → `String`.

    **The densest cross-product in the corpus**, and the point is that nothing new was needed
    for it. `wrap { 7 }` is an implicit-receiver send carrying a block, *inside* a method, whose
    target is *inherited*: `selfCallBlk` finds `Base#wrap` by tier 7's ordinary `mroGet?` walk,
    and the block — written inside `Child#show`, so with creation `self` `.inst "Child" ivar0`
    — travels down to a `yield` in the parent's body. Tier 7's hierarchy, tier 9's blocks and
    clink 19's creation-`self` field, meeting with nothing added to any of them. -/
def r119 : Rung :=
  ⟨"xc-inherit-implicit-block",
    .seq [.class' "Base" none
            (.def' "wrap" []
              (.send (some (.send (some (.str "[")) "+"
                [.send (some (.yield' [])) "to_s" [] none] none)) "+" [.str "]"] none)),
          .class' "Child" (some (.const "Base"))
            (.def' "show" [] (.send none "wrap" [] (some (.block [] [] (.int 7))))),
          .send (some (.send (some (.const "Child")) "new" [] none)) "show" [] none],
    .cls "String", [],
    .seq (.cons (.classStmt rfl rfl rfl .nil .nil) (.cons (.classStmt rfl rfl rfl .nil .nil)
      (.last (.callMethod (.newInstNoInit (.constCls rfl rfl) .nil rfl rfl) .nil rfl rfl
        (.selfCallBlk rfl .nil rfl rfl rfl
          (.prim
            (.prim .strLit
              (.cons (.prim (.yieldExpr rfl .nil rfl rfl .intLit rfl) .nil .intToS) .nil)
              .strAdd)
            (.cons .strLit .nil) .strAdd))))))⟩

/-! ## Tier 10 — metaprogramming

Deliberately last on the ladder. What is interesting about the first of these rungs is that it
turned out **not** to be metaprogramming at all: a reopened class is the same thing a class
always was, and the table was simply wrong about it. -/

/-- `class Foo; def a; 1; end; end; class Foo; def b; 2; end; end; Foo.new.a + Foo.new.b`
    → `Integer`.

    **Class reopening, which was a bug rather than a missing feature.** `extendClasses`
    prepended a fresh `Cls` per `class` statement and `clsGet?` is a `find?`, so the second
    statement *shadowed* the first: `Foo` had `b` and not `a`, and this program could not be
    typed. `mergeCls` accumulates instead, which is what Ruby does.

    Note where the merge happens: `JudgeSeq.cons`, via `Ctx.afterStmt`, so the table grows
    **statement by statement** and a call placed *between* the two `class` statements still sees
    only the first body. That is the property tier 6 built `DefTable` threading for, and it is
    what makes reopening safe to model as accumulation rather than as a whole-program scan.

    The two controls are the two directions the merge can go wrong: a redefinition must win over
    what it replaces, and a method must not be visible before its `class` statement. -/
def r109 : Rung :=
  ⟨"metaprog-class-reopening",
    .seq [.class' "Foo" none (.def' "a" [] (.int 1)),
          .class' "Foo" none (.def' "b" [] (.int 2)),
          .send (some (.send (some (.send (some (.const "Foo")) "new" [] none)) "a" [] none))
            "+" [.send (some (.send (some (.const "Foo")) "new" [] none)) "b" [] none] none],
    .int, [],
    .seq (.cons (.classStmt rfl rfl rfl .nil .nil) (.cons (.classStmt rfl rfl rfl .nil .nil)
      (.last (.prim
        (.callMethod (.newInstNoInit (.constCls rfl rfl) .nil rfl rfl) .nil rfl rfl .intLit)
        (.cons (.callMethod (.newInstNoInit (.constCls rfl rfl) .nil rfl rfl) .nil rfl rfl
          .intLit) .nil)
        .intAdd))))⟩

/-- `module Greetable; def greet; "hi"; end; end; class Person; include Greetable; end;
    Person.new.greet` → `String`.

    **`include`**, and the derivation is `callMethod` unchanged — which is the finding. All the
    work is in the lookup: `mroGet?` now searches the class's own methods, then the modules in
    `Cls.includes` (reversed, because a later `include` wins), then up the superclass chain,
    which is Ruby's `ancestors` order. The `dc` it reports is `"Greetable"`, so the body is
    entered with `frame` naming the *module* — exactly as tier 7 intended `dc` to mean "where
    the method was found".

    Two things had to change beyond the lookup, and both are soundness rather than reach:
    `Judge.classStmt` gained the `allModules` premise (`include SomeClass` raises `TypeError`),
    and `ancestorsUp` had to start naming included modules, or `is_a?(Greetable)` would answer
    a *wrong* `some false` — the obligation clink 14 recorded against this exact tier. -/
def r110 : Rung :=
  ⟨"metaprog-include",
    .seq [.module' "Greetable" (.def' "greet" [] (.str "hi")),
          .class' "Person" none (.send none "include" [.const "Greetable"] none),
          .send (some (.send (some (.const "Person")) "new" [] none)) "greet" [] none],
    .cls "String", [],
    .seq (.cons (.moduleStmt rfl rfl rfl .nil .nil) (.cons (.classStmt rfl rfl rfl .nil .nil)
      (.last (.callMethod (.newInstNoInit (.constCls rfl rfl) .nil rfl rfl) .nil rfl rfl
        .strLit))))⟩

/-- `module Loud; def shout; "LOUD"; end; end; class Person; extend Loud; end; Person.shout`
    → `String`.

    **`extend`**, whose entire content is one asymmetry: it takes the module's **instance**
    methods and makes them methods of the class *object*. So `Cls.extended` is consulted by
    `smroGet?` — the singleton walk — and what it looks in is the module's `.methods`, not its
    `.smethods`. `mixinGet?` serves both directions for exactly that reason: both read
    `.methods`, and only the table consulted at the call site differs.

    The pair of controls below is the pair of mistakes: an *instance* must not get an extended
    method, and the class object must not get an included one. Both really raise
    `NoMethodError`. -/
def r111 : Rung :=
  ⟨"metaprog-extend",
    .seq [.module' "Loud" (.def' "shout" [] (.str "LOUD")),
          .class' "Person" none (.send none "extend" [.const "Loud"] none),
          .send (some (.const "Person")) "shout" [] none],
    .cls "String", [],
    .seq (.cons (.moduleStmt rfl rfl rfl .nil .nil) (.cons (.classStmt rfl rfl rfl .nil .nil)
      (.last (.callSMethod (.constCls rfl rfl) .nil rfl rfl .strLit))))⟩

/-- `module Logger; def speak; "logged: " + super; end; end; class Person; prepend Logger;
    def speak; "hi"; end; end; Person.new.speak` → `String`.

    **`prepend`, which is the rung that turned the MRO into a list.** Up to tier 8 instance
    dispatch could be a walk over `Cls.super?`, because "the next place to look" was always
    reachable from where you were. A prepended module breaks that: `Person.ancestors` is
    `[Logger, Person]`, so `Logger#speak` wins — and the `super` inside it has to run
    `Person#speak`, which is not `Logger`'s superclass and which nothing about `Logger` names.

    So `mroList?` builds the order once (`prepends ++ [self] ++ includes`, per class, up the
    chain), `searchMro` dispatches into it, and `super` becomes `afterInMro` — "keep going from
    where I was found". Tier 7's `c.super?` walk was the special case of that for an MRO with no
    mixins in it. `Frame` gained `recvClass` because `afterInMro` needs to know *which* MRO.

    The `super` here is a **`zsuper`** (`super` with no argument list), which had no rule until
    now; `Judge.zsuperCall` covers the parameterless case, which is what "forward my arguments"
    means when there are none.

    A note on how this rung was nearly climbed for the wrong reason. When `Cls` grew its third
    `List String` field, a positional `⟨…⟩` in `mergeCls` silently bound `includes := prepends`
    — so `Logger` landed *after* `Person` in the MRO, dispatch found `Person#speak`, the
    `zsuper` in the module was never reached, and `validate` said `true`. The rung "passed" with
    the feature it exists to test entirely bypassed. `mergeCls` now uses **named** fields, and
    the control below pins the ordering by execution. -/
def r112 : Rung :=
  ⟨"metaprog-prepend",
    .seq [.module' "Logger"
            (.def' "speak" []
              (.send (some (.str "logged: ")) "+" [.zsuper none] none)),
          .class' "Person" none (.seq [
            .send none "prepend" [.const "Logger"] none,
            .def' "speak" [] (.str "hi")]),
          .send (some (.send (some (.const "Person")) "new" [] none)) "speak" [] none],
    .cls "String", [],
    .seq (.cons (.moduleStmt rfl rfl rfl .nil .nil) (.cons (.classStmt rfl rfl rfl .nil .nil)
      (.last (.callMethod (.newInstNoInit (.constCls rfl rfl) .nil rfl rfl) .nil rfl rfl
        (.prim .strLit
          (.cons (.zsuperCall rfl rfl rfl rfl rfl rfl rfl .strLit) .nil)
          .strAdd)))))⟩

/-- `class Ghost; def method_missing(name); "called " + name.to_s; end; end;
    Ghost.new.anything_at_all` → `String`.

    **`method_missing`, and the interesting premise is the one about when it does *not* fire.**
    Mechanically this is `callMethod` with the name looked up changed to `"method_missing"` and
    a `.sym` pushed onto the front of the argument list — Ruby passes the missing name as a
    Symbol. (Which is also why tier 10 needed a `Symbol#to_s` row: the idiomatic body calls
    `to_s` on it immediately.)

    The premise worth reading is `not_objectMethod rfl`. This judgment's class table holds only
    what the *program* declared, so `mroGet?` misses for `to_s`, `inspect`, `hash`, `==`,
    `class` — every method `Object` provides — and Ruby runs **those**, not `method_missing`.
    Without the guard, `Ghost.new.to_s` would be typed by this rule, and the failure mode is not
    a rejection but a **wrong answer**: with `def method_missing(name); 5; end` the checker would
    say `Integer` where the real value is a `String`. That is control (ggg), and it is why
    `ObjectMethod`'s list is the one table on this ladder whose *completeness* is the soundness
    condition rather than the coverage one.

    Its splat sibling `metaprog-method-missing-splat` — the idiomatic
    `def method_missing(name, *args)` — is a permanent `ty_language_gap` and stays one: `*args`
    has no `Ty`. This rung exists next to it precisely to show the gap is the rest parameter and
    not `method_missing` dispatch. -/
def r113 : Rung :=
  ⟨"metaprog-method-missing-fixed-arity",
    .seq [.class' "Ghost" none
            (.def' "method_missing" [.req "name"]
              (.send (some (.str "called ")) "+"
                [.send (some (.var .lvar "name")) "to_s" [] none] none)),
          .send (some (.send (some (.const "Ghost")) "new" [] none))
            "anything_at_all" [] none],
    .cls "String", [],
    .seq (.cons (.classStmt rfl rfl rfl .nil .nil)
      (.last (.callMissing (.newInstNoInit (.constCls rfl rfl) .nil rfl rfl) .nil rfl
        (not_objectMethod rfl) rfl rfl
        (.prim .strLit (.cons (.prim (.var rfl rfl) .nil .symToS) .nil) .strAdd))))⟩

/-- `class Ghost; def method_missing(name, *args); "called"; end; end;
    Ghost.new.anything_at_all` → `String`, and **a flagged `Ty` language gap that turned out
    not to be one** (retargeted 2026-09-01).

    The recorded reason was: "its true signature is 'one Sym, then zero or more of anything', and
    `Ty`'s arrow spine has no vararg constructor, so there is no `Ty` value that honestly
    describes this parameter list". That is a correct statement about *signatures* — and this
    checker never writes one. `callDef`/`callMissing` type the body once per **call-site argument
    shape** (tier 6's finding), so a rest parameter needs no arity spine at all: `paramBind`
    binds `*args` to `arrayOf (elemTy <the remaining argument types>)`, which is the *second* of
    the two fixes the original description itself proposed.

    So it climbed with nothing added — by tier 14b's rest-parameter rows, written for
    `param-rest`, and it took two clinks for anyone to notice. The general lesson is the one tier
    6 already recorded and this rung re-proves at a distance: **"what signature does this method
    have" is a question this judgment does not ask**, and a gap phrased in terms of signatures
    should be re-read before it is believed.

    Its companion `proc-arity-leniency` (`proc { |x, y| x }.call(1)`) is *not* fixed by the same
    work, and it is not a `Ty` gap either: it needs `Ty.clos` to record whether a callable is a
    proc or a lambda, because only a proc's arity is lenient. -/
def r114 : Rung :=
  ⟨"metaprog-method-missing-splat",
    .seq [.class' "Ghost" none
            (.def' "method_missing" [.req "name", .rest (some "args")] (.str "called")),
          .send (some (.send (some (.const "Ghost")) "new" [] none))
            "anything_at_all" [] none],
    .cls "String", [],
    .seq (.cons (.classStmt rfl rfl rfl .nil .nil)
      (.last (.callMissing (.newInstNoInit (.constCls rfl rfl) .nil rfl rfl) .nil rfl
        (not_objectMethod rfl) rfl rfl .strLit)))⟩

/-- `def pick(flag) … end; v = pick(false); case v when Integer then v * 2 when String then
    v + v else 0 end` → `union(Int, String)`.

    **The aliasing rung.** `case` desugars to a temporary assigned from the scrutinee, tests on
    the **temporary**, and branch bodies that use **`v`**:

    ```
    seq (vasgn local __dt_t1 (var local v))
        (if (send (const Integer) "===" [var local __dt_t1])
            (send (var local v) "*" [int 2])              -- v, not __dt_t1
            (if (send (const String) "===" [var local __dt_t1]) … ))
    ```

    so refinement has to reach a name the condition does not mention. `Ty.sameAs` is how: the
    assignment records "`__dt_t1` holds the same object as `v`" *in the environment*, which is
    already threaded, so every place that could invalidate the alias is a place that already
    writes to the environment. `implementation-notes.md` clink 17 has the three cheaper designs
    that are **unsound** and why.

    Read the derivation against the shape and three things line up:

    - `vasgnAlias` is the only new statement rule, and it differs from `vasgn` only in what
      lands in the environment.
    - `caseEqQuery` types `Integer === __dt_t1`. `Module#===` is the ancestor test with its
      sides swapped, so `narrowCond?` gets the same `.isA` kind out of it that `is_a?` gives.
    - the argument of each `===` is a `varAlias` — reading an aliased name yields the payload,
      so no expression ever has type `Ty.sameAs`.

    And the *nesting* is what made the environment the right place for the alias rather than a
    `JudgeSeq` rule over the (assignment, `if`) pair: the second `when` is an `if` inside the
    first's **else**-branch, where only `Judge.if'` is looking, and it needs the alias to still
    be there — refined, in fact, since `v` is already known not to be an `Integer`.

    `__dt_t1`'s entry in the outgoing environment below is worth a look: it is a *union of
    aliases*, one per arm, and a union is not a `sameAs` — so the alias is gone by the time
    anything after the `case` could read it. That is the join doing the invalidation for free. -/
def r128 : Rung :=
  ⟨"narrow-union-case-when",
    .seq [.def' "pick" [.req "flag"]
            (.if' (.var .lvar "flag") (.int 1) (some (.str "s"))),
          .vasgn .lvar "v" (.send none "pick" [.fls] none),
          .seq [.vasgn .lvar "__dt_t1" (.var .lvar "v"),
                .if' (.send (some (.const "Integer")) "===" [.var .lvar "__dt_t1"] none)
                  (.send (some (.var .lvar "v")) "*" [.int 2] none)
                  (some (.if'
                    (.send (some (.const "String")) "===" [.var .lvar "__dt_t1"] none)
                    (.send (some (.var .lvar "v")) "+" [.var .lvar "v"] none)
                    (some (.int 0))))]],
    .union .int (.cls "String"),
    [("v", .union .int (.cls "String")),
     ("__dt_t1", .union (.sameAs "v" .int)
       (.union (.sameAs "v" (.cls "String")) (.sameAs "v" .never)))],
    .seq (.cons .defStmt
      (.cons (.vasgn (.callDef (.cons .flsLit .nil) rfl rfl
                (.if' (.var rfl rfl) .intLit .strLit rfl)))
        (.last (.seq (.cons (.vasgnAlias rfl rfl rfl)
          (.last (.if'
            (.caseEqQuery (.constBuiltin .integer rfl rfl) (.cons (.varAlias rfl) .nil) rfl)
            (.prim (.var rfl rfl) (.cons .intLit .nil) .intMul)
            (.if'
              (.caseEqQuery (.constBuiltin .string rfl rfl) (.cons (.varAlias rfl) .nil) rfl)
              (.prim (.var rfl rfl) (.cons (.var rfl rfl) .nil) .strAdd)
              .intLit rfl)
            rfl)))))))⟩

/-- `a = [3]; x = a[0]; if x && x > 1 then x + 1 else 0 end` → `Integer`.

    **The last rung on the ladder, and the one that needed narrowing to survive a *compound*
    condition.** `&&` desugars to a temporary plus a nested `if`, so the outer `if`'s condition
    position holds an entire `seq`:

    ```
    if (seq (vasgn local __dt_t1 (var local x))
            (if (var local __dt_t1) (send (var local x) ">" [int 1]) (var local __dt_t1)))
       (send (var local x) "+" [int 1])
       (int 0)
    ```

    Three things have to line up, and each was a separate piece of the tier:

    - **`x > 1` inside the condition already needs `x` narrowed** — the refinement is consumed
      in the same expression that establishes it. That comes from the **inner** `if`, whose
      condition is the temporary, via the alias (`Ty.sameAs`, clink 25). Without aliasing this
      rung is not typeable at all, which is why clink 17 put them in the same bucket.
    - **The outer refinement is `thenOnly`.** A truthy `&&` means `x` was truthy; a falsy one
      could have been either conjunct, so the else-branch learns *nothing* and must not be
      refined. `NarrowSides` is that distinction, and it is the first asymmetric refinement on
      the ladder.
    - **`noLocalAsgn rhs`.** The refinement lands on the environment at the *end* of the
      condition, and `x && (x = false; 1)` is truthy while leaving `x` false. A whitelist, so
      that a shape the function has not been taught about answers `false` rather than "clean".

    Read `__dt_t1`'s outgoing entry — `union(Integer (= x), NilClass (= x))` — and the inner
    `if`'s join has already retired the alias, exactly as in `narrow-union-case-when`. -/
def r132 : Rung :=
  ⟨"narrow-and-guard",
    .seq [.vasgn .lvar "a" (.array [.int 3]),
          .vasgn .lvar "x" (.send (some (.var .lvar "a")) "[]" [.int 0] none),
          .if' (.seq [.vasgn .lvar "__dt_t1" (.var .lvar "x"),
                      .if' (.var .lvar "__dt_t1")
                        (.send (some (.var .lvar "x")) ">" [.int 1] none)
                        (some (.var .lvar "__dt_t1"))])
            (.send (some (.var .lvar "x")) "+" [.int 1] none)
            (some (.int 0))],
    .int,
    [("a", .arrayOf .int), ("x", .nilable .int),
     ("__dt_t1", .union (.sameAs "x" .int) (.sameAs "x" .nilT))],
    .seq (.cons (.vasgn (.arrayLit (.cons .intLit .nil)))
      (.cons (.vasgn (.prim (.var rfl rfl) (.cons .intLit .nil) .arrayIndex))
        -- The outer `if'`'s indices are written out because its condition is a whole `seq`:
        -- `narrowEnvs` cannot reduce until the condition's syntax *and* `Γc` are known, and
        -- neither is available while the premises are being elaborated. Read them as the
        -- statement of what this rung does -- `Γ₁` has `x : Integer`, `Γ₂` is `Γc` untouched,
        -- which is `NarrowSides.thenOnly`.
        (.last (.if'
          (Γc := [("a", .arrayOf .int), ("x", .nilable .int),
                  ("__dt_t1", .union (.sameAs "x" .int) (.sameAs "x" .nilT))])
          (Γ₁ := [("a", .arrayOf .int), ("x", .int),
                  ("__dt_t1", .union (.sameAs "x" .int) (.sameAs "x" .nilT))])
          (Γ₂ := [("a", .arrayOf .int), ("x", .nilable .int),
                  ("__dt_t1", .union (.sameAs "x" .int) (.sameAs "x" .nilT))])
          (σ := .nilable .bool) (τ₁ := .int) (τ₂ := .int)
          -- …and the inner `if'`'s for the same reason one level down. These are the
          -- interesting ones: `Γ₁` is where the **alias** does its work, refining `x` to
          -- `Integer` off a test on `__dt_t1`, which is what makes `x > 1` type inside the
          -- condition that establishes it.
          (.seq (.cons (.vasgnAlias rfl rfl rfl)
            (.last (.if'
              (Γc := [("a", .arrayOf .int), ("x", .nilable .int),
                      ("__dt_t1", .sameAs "x" (.nilable .int))])
              (Γ₁ := [("a", .arrayOf .int), ("x", .int),
                      ("__dt_t1", .sameAs "x" .int)])
              (Γ₂ := [("a", .arrayOf .int), ("x", .nilT),
                      ("__dt_t1", .sameAs "x" .nilT)])
              (Ic := .ivar0) (I₁ := .ivar0) (I₂ := .ivar0)
              (σ := .nilable .int) (τ₁ := .bool) (τ₂ := .nilT)
              (.varAlias rfl)
              (.prim (.var rfl rfl) (.cons .intLit .nil) .intGt)
              (.varAlias rfl) rfl))))
          (.prim (.var rfl rfl) (.cons .intLit .nil) .intAdd)
          .intLit rfl))))⟩


/-! ## Tiers 13-17 — the rungs the slice's syntax brought in that were already covered

Eight of the 85 rungs added with the Homebrew slice (`AGENTS.md` §The syntactic gap)
answered `true` the day they were written, with no rule added. That is the outcome a
target-driven tier is *supposed* to have some of, and each one is a small finding:

- `param-block` says `Frontier` item 11's "the cleared implementation rejects any `def'`
  using `Param.block`" is stale — tier 9b's `callDefBlk`/`paramEnvB` already bind a `&b`
  parameter, and `block-param-ampersand` was that rung. The slice's
  `version/parser.rb#initialize(regex, &block)` needs nothing new.
- The four control-flow rungs (`ctl-unless`, `ctl-ternary`, `ctl-or-assign`,
  `ctl-safe-nav`) confirm the prediction each of their corpus descriptions makes: all four
  are **sugar**, and the desugarer has already turned them into `if`/`seq`/`vasgn`. The
  interesting two are the last: `x ||= 5` is typed `Integer` rather than
  `T.nilable(Integer)` only because tier 12's `falsyTy` reads the then-branch as dead, and
  `x&.length` is narrowing over a **desugarer-generated temporary**, i.e. clink 17's
  aliasing machinery driven by syntax nobody wrote by hand.
- `str-interpolation` is the one worth reading twice, and its derivation is below. -/

/-- `def run(&b); b.call(2); end; run { |x| x * 3 }` → `Integer`.

    Identical in shape to `block-param-ampersand` (r095) and included because the slice
    writes it: `version/parser.rb`'s `RegexParser#initialize(regex, &block)` stores the
    block and calls it later. Nothing new — which is the point of the rung. -/
def r157 : Rung :=
  ⟨"param-block",
    .seq [.def' "run" [.block (some "b")]
            (.send (some (.var .lvar "b")) "call" [.int 2] none),
          .send none "run" []
            (some (.block [.req "x"] []
              (.send (some (.var .lvar "x")) "*" [.int 3] none)))],
    .int, [],
    .seq (.cons .defStmt
      (.last (.callDefBlk rfl .nil rfl rfl rfl
        (.closCall (.inl rfl) (.var rfl rfl) (.cons .intLit .nil) rfl rfl
          (.prim (.var rfl rfl) (.cons .intLit .nil) .intMul) rfl))))⟩

/-- `name = "world"; "hello #{name}"` → `String`.

    **String interpolation is narrowing.** The desugarer does not emit a concatenation of
    `to_s` calls; it emits, per interpolated subterm, a temporary plus a `String === t`
    test:

    ```
    send (str "hello ") "+"
      [seq (vasgn local __dt_t1 (var local name))
           (if (send (const String) "===" [var local __dt_t1])
               (var local __dt_t1)
               (send (var local __dt_t1) "__as_string" []))]
    ```

    — the fast path for a value that is already a String, and `__as_string` otherwise. So
    this rung climbed with **no `__as_string` row at all**: `caseEqQuery` refines
    `__dt_t1` to `.cls "String"` in the then-branch and to `notATy "String" (.cls
    "String") = .never` in the else-branch, `primNever` types the send on a `.never`
    receiver as `.never`, and `joinT (.cls "String") .never` is `.cls "String"`. The
    else-branch is *dead*, and the checker can see it.

    That is `Ty.never`'s dead-branch reading paying for itself a third time (clink 26's
    control (nnn) was the second), and it is why `str-interpolation-nonstring` — the same
    program with an `Integer` inside the braces — is **not** climbed: there the
    else-branch is live and `__as_string` is a row the table does not have. The two rungs
    are next to each other in the corpus for exactly that contrast. -/
def r165 : Rung :=
  ⟨"str-interpolation",
    .seq [.vasgn .lvar "name" (.str "world"),
          .send (some (.str "hello ")) "+"
            [.seq [.vasgn .lvar "__dt_t1" (.var .lvar "name"),
                   .if' (.send (some (.const "String")) "===" [.var .lvar "__dt_t1"] none)
                     (.var .lvar "__dt_t1")
                     (some (.send (some (.var .lvar "__dt_t1")) "__as_string" [] none))]]
            none],
    .cls "String",
    [("name", .cls "String"),
     ("__dt_t1", .union (.sameAs "name" (.cls "String")) (.sameAs "name" .never))],
    .seq (.cons (.vasgn .strLit)
      (.last (.prim .strLit
        (.cons (.seq (.cons (.vasgnAlias rfl rfl rfl)
          (.last (.if'
            (.caseEqQuery (.constBuiltin .string rfl rfl) (.cons (.varAlias rfl) .nil) rfl)
            (.varAlias rfl)
            (.primNever (.varAlias rfl) .nil (.inl rfl))
            rfl)))) .nil)
        .strAdd)))⟩

/-- `s = :affected; s.to_s.length` → `Integer`. `Ty.sym` has been in the language since the
    port and `symToS` since tier 10's `method_missing` rung; the slice's 299 symbols make
    them worth a rung of their own rather than a step inside someone else's. -/
def r168 : Rung :=
  ⟨"sym-literal",
    .seq [.vasgn .lvar "s" (.sym "affected"),
          .send (some (.send (some (.var .lvar "s")) "to_s" [] none)) "length" [] none],
    .int, [("s", .sym)],
    .seq (.cons (.vasgn .symLit)
      (.last (.prim (.prim (.var rfl rfl) .nil .symToS) .nil .strLength)))⟩

/-- `s = :high; s == :high` → `Boolean`. Tier 2's `objEq` covers it, with `EqSafe .sym`
    discharging the receiver side. The rung is the *negative* finding: a checker growing a
    `Symbol#==` row would be adding one it does not need, and the slice compares symbols
    everywhere. -/
def r169 : Rung :=
  ⟨"sym-compare",
    .seq [.vasgn .lvar "s" (.sym "high"),
          .send (some (.var .lvar "s")) "==" [.sym "high"] none],
    .bool, [("s", .sym)],
    .seq (.cons (.vasgn .symLit)
      (.last (.prim (.var rfl rfl) (.cons .symLit .nil) (.objEq .sym))))⟩

/-- `x = 1; unless x.nil? then x + 1 else 0 end` → `Integer`.

    `unless` is `if` with a `!` on the condition — the desugarer does **not** swap the
    branches, which is the fact the rung exists to pin: tier 12's refinements are keyed to
    which branch is which, so a desugarer that swapped them and a checker that did not
    would each be wrong in the opposite direction and the pair would look right. -/
def r188 : Rung :=
  ⟨"ctl-unless",
    .seq [.vasgn .lvar "x" (.int 1),
          .if' (.send (some (.send (some (.var .lvar "x")) "nil?" [] none)) "!" [] none)
            (.send (some (.var .lvar "x")) "+" [.int 1] none)
            (some (.int 0))],
    .int, [("x", .int)],
    .seq (.cons (.vasgn .intLit)
      (.last (.if' (.prim (.prim (.var rfl rfl) .nil (.nilQuery .int)) .nil .notBool)
               (.prim (.var rfl rfl) (.cons .intLit .nil) .intAdd)
               .intLit rfl)))⟩

/-- `x = 1; x.zero? ? "zero" : "nonzero"` → `String`. An `if` in expression position, which
    `Judge.if'` never distinguished from one in statement position — there is no statement
    grammar here (clink 2). -/
def r189 : Rung :=
  ⟨"ctl-ternary",
    .seq [.vasgn .lvar "x" (.int 1),
          .if' (.send (some (.var .lvar "x")) "zero?" [] none)
            (.str "zero") (some (.str "nonzero"))],
    .cls "String", [("x", .int)],
    .seq (.cons (.vasgn .intLit)
      (.last (.if' (.prim (.var rfl rfl) .nil .intZeroP) .strLit .strLit rfl)))⟩

/-- `x = nil; x ||= 5; x + 1` → `Integer`.

    `x ||= 5` desugars to `if x then x else x = 5 end`, so it is tier 4's rule and tier
    12's refinement together — and the **type is the finding**. Without narrowing, the
    then-branch reads `x` at `NilClass` and the join with the else-branch's `Integer` is
    `T.any(NilClass, Integer)`, on which `+ 1` does not type. With it, `truthyTy .nilT` is
    `.never` (Ruby's only falsy values are `nil` and `false`, so a `nil` that tested truthy
    is unreachable), the then-branch is dead, and `joinT .never .int = .int`. So `x + 1`
    types — and it types for a reason about Ruby's truthiness, not about `||=`. -/
def r190 : Rung :=
  ⟨"ctl-or-assign",
    .seq [.vasgn .lvar "x" .nil,
          .if' (.var .lvar "x") (.var .lvar "x") (some (.vasgn .lvar "x" (.int 5))),
          .send (some (.var .lvar "x")) "+" [.int 1] none],
    .int, [("x", .int)],
    .seq (.cons (.vasgn .nilLit)
      (.cons (.if' (.var rfl rfl) (.var rfl rfl) (.vasgn .intLit) rfl)
        (.last (.prim (.var rfl rfl) (.cons .intLit .nil) .intAdd))))⟩

/-- `x = nil; x&.length` → `NilClass`.

    Safe navigation desugars to a temporary plus a `nil?` test — the same shape `case/when`
    produces (r128) and for the same reason, so it is typed by the same three rules:
    `vasgnAlias` records `__dt_t1 = x`, `nilQuery` narrows off the temporary, and the
    refinement lands on **`x`** through the alias.

    Here `x` is statically `nil`, so it is the *else*-branch that is dead: `nonNilTy .nilT`
    is `.never` and `primNever` types `__dt_t1.length` at `.never` without needing to know
    anything about `String#length`'s receiver. The whole expression is `NilClass`, which is
    what CRuby computes. The slice writes `&.` on genuinely nilable receivers
    (`severity&.to_s&.upcase`), where the else-branch is live — that is the rung this one is
    the degenerate, already-climbed corner of. -/
def r191 : Rung :=
  ⟨"ctl-safe-nav",
    .seq [.vasgn .lvar "x" .nil,
          .seq [.vasgn .lvar "__dt_t1" (.var .lvar "x"),
                .if' (.send (some (.var .lvar "__dt_t1")) "nil?" [] none)
                  .nil
                  (some (.send (some (.var .lvar "__dt_t1")) "length" [] none))]],
    .nilT,
    [("x", .nilT), ("__dt_t1", .union (.sameAs "x" .nilT) (.sameAs "x" .never))],
    .seq (.cons (.vasgn .nilLit)
      (.last (.seq (.cons (.vasgnAlias rfl rfl rfl)
        (.last (.if' (.prim (.varAlias rfl) .nil (.nilQuery .nilT))
                 .nilLit
                 (.primNever (.varAlias rfl) .nil (.inl rfl))
                 rfl))))))⟩

/-! ## Tier 13 — constants

The tier's first clink: a top-level constant assigned and then read. What it costs is one
new component of `Ctx` (`Ctx.consts`) and one new argument to `Ctx.afterStmt` — see
§Constants in `Ratchet/Judge.lean` for why a constant cannot live in `Env` (a method body
gets a fresh one) and cannot be a pre-pass table (`X + 1; X = 10` raises `NameError`). -/

/-- `LIMIT = 10; LIMIT + 1` → `Integer`.

    Read the derivation right to left through `JudgeSeq.cons`: `casgn` types the statement at
    its right-hand side's type and binds *nothing*; the binding is `cons`'s, made by
    `Ctx.afterStmt (.casgn "LIMIT" _) .int`, which is the first time `afterStmt` has used the
    type of the statement it follows. The second statement then reads it with `constEnv` —
    whose premise is a lookup that would answer `none` had the two statements been swapped,
    which is the whole reason the table is threaded rather than collected.

    `outEnv` is `[]`: a constant is not a local, and `Env` never learns its name. -/
def r137 : Rung :=
  ⟨"const-assign-read",
    .seq [.casgn "LIMIT" (.int 10),
          .send (some (.const "LIMIT")) "+" [.int 1] none],
    .int, [],
    .seq (.cons (.casgn .intLit)
      (.last (.prim (.constEnv rfl) (.cons .intLit .nil) .intAdd)))⟩

/-- `class Box; SIZE = 3; def size; SIZE; end; end; Box.new.size` → `Integer`.

    Three separate mechanisms, one per line of the Ruby:

    - `SIZE = 3` is a **class-body member** now (`ClsMember.constM`), so `classMethods?` reads
      it and `classStmt`'s new `JudgeConsts` premise types it — `.cons rfl .intLit .nil`, i.e.
      "`constLitTy? (int 3)` says `Integer`, and here is the derivation that it *is* one".
      That premise is the whole soundness story for the syntactic `extendConsts`.
    - the binding lands at `"::Box::SIZE"`, put there by `Ctx.afterStmt` via `extendConsts`,
      which reads the body a second time (`bodyConsts`) because `afterStmt` sees a statement
      and not a judgment.
    - and the bare `SIZE` inside `size`'s body resolves **lexically**: `constGet?` tries
      `"::Box::SIZE"` first because `κ.frame`'s `defClass` is `Box`, which is where the `def`
      was written. At top level the same read would try only `"::SIZE"` and be rejected, which
      is what Ruby does (`NameError`).

    Note what the derivation does *not* contain: any judgment of `SIZE` at the class
    statement's own position. The constant is typed once, where it is written, and read from
    the table thereafter. -/
def r138 : Rung :=
  ⟨"const-in-class",
    .seq [.class' "Box" none (.seq [.casgn "SIZE" (.int 3),
                                    .def' "size" [] (.const "SIZE")]),
          .send (some (.send (some (.const "Box")) "new" [] none)) "size" [] none],
    .int, [],
    .seq (.cons (.classStmt rfl rfl rfl (.cons rfl .intLit .nil) .nil)
      (.last (.callMethod (.newInstNoInit (.constCls rfl rfl) .nil rfl rfl)
        .nil rfl rfl (.constEnv rfl))))⟩

/-- `NAMES = ["a", "b"].freeze; NAMES[0]` → `T.nilable(String)`.

    The rung is here for `.freeze`, which is how every frozen constant table in the target is
    written, and the finding is how little it costs: `PrimSig.freezeId` is the **identity** on
    its receiver, guarded by `NilQSafe` — the same predicate `nil?` uses, reused rather than
    twinned, because both are asking the one question "is this receiver's method table the
    builtin one?". A `def freeze` on a user class would be dispatched to instead, so `.inst`
    is refused and the row cannot be reached for one.

    The type is `nilable String` and not `String`: `Array#[]` is tier 5's row, and
    `["a","b"][0]` could have been out of range as far as the type language can see. -/
def r143 : Rung :=
  ⟨"const-frozen-array",
    .seq [.casgn "NAMES" (.send (some (.array [.str "a", .str "b"])) "freeze" [] none),
          .send (some (.const "NAMES")) "[]" [.int 0] none],
    .nilable (.cls "String"), [],
    .seq (.cons (.casgn (.prim (.arrayLit (.cons .strLit (.cons .strLit .nil))) .nil
                          (.freezeId (.arrayOf))))
      (.last (.prim (.constEnv rfl) (.cons .intLit .nil) .arrayIndex)))⟩

/-- `TABLE = { "a" => 1, "b" => 2 }.freeze; TABLE["a"]` → `T.untyped`.

    `freezeId` again, on a hash this time, and the type is where the tier's real demand shows
    up. `Hash` is the bare `.cls "Hash"` (tier 5), so `Hash#[]` can only answer `.any` — and
    `.any` is **inert**: nothing consumes it, so the value this rung produces cannot be used
    for anything. The rung climbs and the capability does not arrive.

    That is the ladder's sharpest statement of §Frontier item A. `cvss.rb` reads all seven of
    its metric tables exactly this way and puts the result straight into Float arithmetic, so
    a `fetch` answering `.any` types the *read* and rejects the file. A parameterised hash type
    is the fix, and this rung is where it would first be visible. -/
def r144 : Rung :=
  ⟨"const-frozen-hash",
    .seq [.casgn "TABLE" (.send (some (.hash [(.str "a", .int 1), (.str "b", .int 2)]))
                            "freeze" [] none),
          .send (some (.const "TABLE")) "[]" [.str "a"] none],
    .nilable .int, [],
    .seq (.cons (.casgn (.prim (.hashLit (.cons .strLit .intLit
                                          (.cons .strLit .intLit .nil))) .nil
                          (.freezeId (.hashOf))))
      (.last (.prim (.constEnv rfl) (.cons .strLit .nil) (.hashIndex .cls))))⟩

/-- `module M; X = 5; end; M::X + 1` → `Integer`.

    The scoped read, and the shape of the derivation says what is new: `constPath` has **two**
    premises where `constEnv` has one. The extra one judges the *base* — `.const "M"` at
    `.clsOf "M"`, i.e. `constCls` — and it is not decoration. `M = 5; M::X` raises `TypeError`,
    and after that `casgn` the only rule that types `.const "M"` is `constEnv`, which answers
    `.int`; the premise fails and the read is rejected. Compare `constEnv`'s lookup, which
    *searches* a path list because a bare name has to be resolved; here the name says where to
    look, so it is a single `envGet?`. -/
def r139 : Rung :=
  ⟨"const-scoped-read",
    .seq [.module' "M" (.casgn "X" (.int 5)),
          .send (some (.cpath (some (.const "M")) "X")) "+" [.int 1] none],
    .int, [],
    .seq (.cons (.moduleStmt rfl rfl rfl (.cons rfl .intLit .nil) .nil)
      (.last (.prim (.constPath (.constCls rfl rfl) rfl rfl) (.cons .intLit .nil) .intAdd)))⟩

/-- `module M; end; M::X = 4; M::X + 1` → `Integer`.

    A constant written into a namespace **from outside its body**, which is `casgn`'s twin in
    every respect: `cpathAsgn` types the statement at its right-hand side's type and binds
    nothing, and `Ctx.afterStmt` makes the binding — here at `"::M::X"`, which is the same key
    the same module's body would have used. So the third statement cannot tell how the
    constant got there, and that is the right answer: neither can Ruby.

    Note the module body is `nil`, not empty, and `classMethods?` reads it as a class with no
    members — so `JudgeConsts` is `.nil` and this module contributes nothing to the table
    itself. -/
def r142 : Rung :=
  ⟨"const-scoped-assign",
    .seq [.module' "M" .nil,
          .cpathAsgn (some (.const "M")) "X" (.int 4),
          .send (some (.cpath (some (.const "M")) "X")) "+" [.int 1] none],
    .int, [],
    .seq (.cons (.moduleStmt rfl rfl rfl .nil .nil)
      (.cons (.cpathAsgn (.constCls rfl rfl) .intLit)
        (.last (.prim (.constPath (.constCls rfl rfl) rfl rfl) (.cons .intLit .nil) .intAdd))))⟩

/-- `class Box; SECRET = 1; private_constant :SECRET; def get; SECRET; end; end;
    Box.new.get` → `Integer`.

    `private_constant` declares nothing, so `splitMembers` drops the member and the
    derivation looks exactly like `const-in-class`'s. What it *does* is hide the constant from
    a scoped read — `Box::SECRET` raises `NameError` — and that fact lives on
    `Judge.constPath`'s third premise, off `Ctx.privConsts`.

    Worth being clear that this is **precision, not soundness**: `NameError` is outside the
    type-stuck family, so ignoring `private_constant` entirely would have been "sound" and
    would have certified a program Ruby refuses to run. Control (p13j) is that program. -/
def r145 : Rung :=
  ⟨"const-private-constant",
    .seq [.class' "Box" none (.seq [.casgn "SECRET" (.int 1),
                                    .send none "private_constant" [.sym "SECRET"] none,
                                    .def' "get" [] (.const "SECRET")]),
          .send (some (.send (some (.const "Box")) "new" [] none)) "get" [] none],
    .int, [],
    .seq (.cons (.classStmt rfl rfl rfl (.cons rfl .intLit .nil) .nil)
      (.last (.callMethod (.newInstNoInit (.constCls rfl rfl) .nil rfl rfl)
        .nil rfl rfl (.constEnv rfl))))⟩

/-- `class Point; attr_reader :x, :y; def initialize(x, y); @x = x; @y = y; end; end;
    Point.new(1, 2).x + Point.new(1, 2).y` → `Integer`.

    **Nothing in the derivation mentions `attr_reader`.** `splitMembers` expands the member
    into the two `def x; @x; end`/`def y; @y; end` it stands for, so both reads are the
    ordinary `callMethod` + `ivarRead` of tier 7 — and the ivar types come, as always, from
    the constructor's argument shape rather than from the reader.

    That expansion is where the whole content of `attr_reader` is: the ivar's name is the
    reader's with an `@`. The reason it can be done syntactically at all is the same reason
    `include` can (tier 10): a class body's declarations are read declaratively, matched at
    the exact syntax the desugarer emits, with `attr_reader(*names)` deliberately unread. -/
def r146 : Rung :=
  ⟨"const-attr-reader",
    .seq [.class' "Point" none (.seq [
            .send none "attr_reader" [.sym "x", .sym "y"] none,
            .def' "initialize" [.req "x", .req "y"]
              (.seq [.vasgn .ivar "@x" (.var .lvar "x"),
                     .vasgn .ivar "@y" (.var .lvar "y")])]),
          .send (some (.send (some (.send (some (.const "Point")) "new"
                                     [.int 1, .int 2] none)) "x" [] none)) "+"
            [.send (some (.send (some (.const "Point")) "new" [.int 1, .int 2] none))
               "y" [] none] none],
    .int, [],
    .seq (.cons (.classStmt rfl rfl rfl .nil .nil)
      (.last (.prim
        (.callMethod
          (.newInst (.constCls rfl rfl) (.cons .intLit (.cons .intLit .nil)) rfl rfl
            (.seq (.cons (.ivarAsgn (.var rfl rfl)) (.last (.ivarAsgn (.var rfl rfl))))))
          .nil rfl rfl .ivarRead)
        (.cons
          (.callMethod
            (.newInst (.constCls rfl rfl) (.cons .intLit (.cons .intLit .nil)) rfl rfl
              (.seq (.cons (.ivarAsgn (.var rfl rfl)) (.last (.ivarAsgn (.var rfl rfl))))))
            .nil rfl rfl .ivarRead)
          .nil)
        .intAdd)))⟩

/-- `class Box; def size; 3; end; alias length size; end; Box.new.length` → `Integer`.

    An alias is a *copy* of the method under a second name, and it is resolved by
    `classMethods?` rather than by `clsMember?` — a member kind on its own cannot see the
    method it aliases. So `mroGet? "length"` finds an ordinary `Defn` whose body is `3`, and
    again nothing downstream knows the alias existed.

    Two decisions recorded in `resolveAliases`. An **unresolvable** alias makes the whole class
    unreadable rather than being skipped, because skipping would put a class in the table
    missing a method and fail a later dispatch for the wrong reason. And Ruby's *ordering*
    requirement (the method must be defined before the `alias` line) is **not** enforced:
    `splitMembers` keeps each kind's source order but loses the interleaving, so
    `class C; alias b a; def a; 1; end; end` types here and raises `NameError` in Ruby —
    outside the family, and recorded rather than fixed. -/
def r147 : Rung :=
  ⟨"const-alias",
    .seq [.class' "Box" none (.seq [.def' "size" [] (.int 3),
                                    .alias' "length" "size"]),
          .send (some (.send (some (.const "Box")) "new" [] none)) "length" [] none],
    .int, [],
    .seq (.cons (.classStmt rfl rfl rfl .nil .nil)
      (.last (.callMethod (.newInstNoInit (.constCls rfl rfl) .nil rfl rfl)
        .nil rfl rfl .intLit)))⟩

/-- `module Outer; module Inner; Y = "deep"; end; end; Outer::Inner::Y` → `String`.

    The nested-namespace rung, and the derivation reads outside-in: `constPath` for the last
    step, and its **base** is `constPathCls` — `Outer::Inner` is a class-or-module *object*,
    typed `.clsOf "Outer::Inner"`, which is why the two rules are siblings rather than one
    rule with two lookups. Nesting deeper just nests `constPathCls` deeper.

    The qualified name is the load-bearing choice: `M::Box.name` in CRuby is the string
    `"M::Box"`, so keying `CTable`/`Ty.clsOf`/`Ty.inst` by the qualified name makes this
    package's names and the semantics' agree instead of agreeing by convention. The constant's
    key follows from it — `"::Outer::Inner::Y"`.

    Note what `moduleStmt`'s premises now do here: the outer module's `JudgeNested` premise is
    what types the *inner* module statement, because a nested declaration is not a statement of
    any sequence and `JudgeSeq` is the only thing that would otherwise judge it. -/
def r140 : Rung :=
  ⟨"const-scoped-nested",
    .seq [.module' "Outer" (.module' "Inner" (.casgn "Y" (.str "deep"))),
          .cpath (some (.cpath (some (.const "Outer")) "Inner")) "Y"],
    .cls "String", [],
    .seq (.cons (.moduleStmt rfl rfl rfl .nil
                  (.cons rfl rfl rfl (.cons rfl .strLit .nil) .nil .nil))
      (.last (.constPath (.constPathCls (.constCls rfl rfl) rfl rfl) rfl rfl)))⟩

/-- `module M; class Box; def initialize(v); @v = v; end; def get; @v; end; end; end;
    M::Box.new(7).get` → `Integer`.

    A class inside a module, allocated and dispatched through its scoped name. `constPathCls`
    answers `.clsOf "M::Box"`, and from there tier 7's object model is untouched: `newInst`
    looks `"M::Box"` up in the table (where `extendClasses`' new `nestedClasses` pass put it),
    judges `initialize` at the call's argument shape, and `callMethod` dispatches off
    `.inst "M::Box" spine`.

    So the whole cost of a namespaced class is *naming*, and the reason nothing else moved is
    that dispatch was already by table lookup on a string. -/
def r141 : Rung :=
  ⟨"const-scoped-class-ref",
    .seq [.module' "M" (.class' "Box" none (.seq [
            .def' "initialize" [.req "v"] (.vasgn .ivar "@v" (.var .lvar "v")),
            .def' "get" [] (.var .ivar "@v")])),
          .send (some (.send (some (.cpath (some (.const "M")) "Box")) "new"
                        [.int 7] none)) "get" [] none],
    .int, [],
    .seq (.cons (.moduleStmt rfl rfl rfl .nil (.cons rfl rfl rfl .nil .nil .nil))
      (.last (.callMethod
        (.newInst (.constPathCls (.constCls rfl rfl) rfl rfl)
          (.cons .intLit .nil) rfl rfl (.ivarAsgn (.var rfl rfl)))
        .nil rfl rfl .ivarRead)))⟩

/-- `module M; class Box; end; end; M::Box.new.class.to_s` → `String`, and the string is
    `"M::Box"`.

    The rung that closes tier 13, and two rules that are each the inverse of something already
    here. `Object#class` is `newInst`'s inverse — `.inst n _` in, `.clsOf n` out, forgetting the
    ivar spine exactly as the value does — and it needs **no override guard**, which is a fact
    about Ruby's grammar rather than a gap: `class` is a keyword, so `def class` cannot be
    written. Compare `is_a?`, which can be overridden and therefore carries `isADispatchOk`.

    `Module#to_s` is total and never raises, so its only route to a raise is a `def self.to_s`
    on the class object — `smroGet? … = none` is that guard, the same shape `caseEqQuery` uses
    for `Module#===`. It is a `Judge` rule rather than a `PrimSig` row precisely because the
    guard needs the class table, which `PrimSig` cannot see.

    Both take their arity as `JudgeAll … args []` rather than requiring `args = []`
    syntactically, which is `newInstNoInit`'s shape and is what `chk`'s `argTys = []` guard
    actually establishes. -/
def r148 : Rung :=
  ⟨"const-class-of-const",
    .seq [.module' "M" (.class' "Box" none .nil),
          .send (some (.send (some (.send (some (.cpath (some (.const "M")) "Box"))
                                     "new" [] none)) "class" [] none)) "to_s" [] none],
    .cls "String", [],
    .seq (.cons (.moduleStmt rfl rfl rfl .nil (.cons rfl rfl rfl .nil .nil .nil))
      (.last (.clsToS
        (.classOf (.newInstNoInit (.constPathCls (.constCls rfl rfl) rfl rfl) .nil rfl rfl)
          .nil)
        .nil rfl)))⟩

/-! ## Tier 14 — parameters and arguments

Tier 14a: an **optional** parameter with a literal default. -/

/-- `def greet(name, greeting = "hi"); greeting + " " + name; end;
    greet("a") + greet("a", "yo")` → `String`.

    Two `callDef`s over the same `def`, at *different argument counts*, and that is the whole
    rung: tier 6's design — a method body is typed once per call-site argument shape, with no
    signature anywhere — already had room for this. `paramEnv` grew two cases, and the
    interesting call is the *first*: with one argument, `greeting` is bound to the type
    `constLitTy?` reads off `"hi"`.

    **Nothing in this derivation discharges that.** There is no premise saying `"hi"` is a
    `String`; the fact is inside `paramEnv`, which is a function. What makes that legitimate is
    `constLitTy?_sound` (`Proof/ChkSound.lean`) — "an expression `constLitTy?` types really has
    that type, in any context, unconditionally" — which is a theorem about `Judge`, not a
    trusted table row. It is the same function tier 13b uses for a class-body constant, and
    proving it there would have been optional; here it is what lets `paramEnv` stay a function
    rather than becoming a relation that every call rule and every derivation on file would
    have had to thread.

    What that costs is the rung *next* to this one: `def pad(s, n = s.length)` reads an earlier
    parameter, `constLitTy?` cannot type it, and no unconditional theorem could — the default
    has to be judged in the environment built so far. That is `ParamEnv`-as-a-relation, and
    it is deferred. -/
def r150 : Rung :=
  ⟨"param-optional",
    .seq [.def' "greet" [.req "name", .opt "greeting" (.str "hi")]
            (.send (some (.send (some (.var .lvar "greeting")) "+" [.str " "] none)) "+"
              [.var .lvar "name"] none),
          .send (some (.send none "greet" [.str "a"] none)) "+"
            [.send none "greet" [.str "a", .str "yo"] none] none],
    .cls "String", [],
    .seq (.cons .defStmt
      (.last (.prim
        (.callDef (.cons .strLit .nil) rfl rfl
          (.prim (.prim (.var rfl rfl) (.cons .strLit .nil) .strAdd)
            (.cons (.var rfl rfl) .nil) .strAdd))
        (.cons
          (.callDef (.cons .strLit (.cons .strLit .nil)) rfl rfl
            (.prim (.prim (.var rfl rfl) (.cons .strLit .nil) .strAdd)
              (.cons (.var rfl rfl) .nil) .strAdd))
          .nil)
        .strAdd)))⟩

/-! ### Tier 14b — rest parameters -/

/-- `def tag(first, *rest); first + rest.length; end; tag(1, 2, 3)` → `Integer`.

    A rest parameter is `arrayOf (elemTy τs)` over the argument types it swallows — the same
    `elemTy` an array literal uses, which is right because the value *is* an array built from
    those arguments.

    `paramEnv` accepts a rest parameter **only as the last one**, and the reason is Ruby's
    matching order: `def f(*a, b)` with three arguments binds `a = [1, 2]` and `b = 3`, so a
    rest that swallows everything is correct exactly when nothing follows it. With something
    following, `paramEnv` answers `none` — conservative rather than wrong, and the same shape of
    argument as clink 33's greedy optionals.

    The one new row is `PrimSig.arrayLength`. Unlike `Array#[]` it needs no care about the
    element type, because the element type does not appear in the result. -/
def r153 : Rung :=
  ⟨"param-req-then-rest",
    .seq [.def' "tag" [.req "first", .rest (some "rest")]
            (.send (some (.var .lvar "first")) "+"
              [.send (some (.var .lvar "rest")) "length" [] none] none),
          .send none "tag" [.int 1, .int 2, .int 3] none],
    .int, [],
    .seq (.cons .defStmt
      (.last (.callDef (.cons .intLit (.cons .intLit (.cons .intLit .nil))) rfl rfl
        (.prim (.var rfl rfl)
          (.cons (.prim (.var rfl rfl) .nil .arrayLength) .nil) .intAdd))))⟩

/-- `def total(*ns); ns.inject(0) { |a, b| a + b }; end; total(1, 2, 3) + total()` → `Integer`.

    **The rung is the second call.** `total()` binds `ns` to `arrayOf (elemTy []) = arrayOf
    .never`, and that type is a real statement rather than a shrug: `.never` is uninhabited, so
    an array whose elements all have type `.never` **has no elements**. The block is therefore
    judged with `b : .never`, `a + b` is `.never` by strictness (`primNever`), and the general
    `IterSig.inject` row — which requires the block to return the accumulator's type — fails on
    a call that cannot possibly go wrong.

    `IterSig.injectEmpty` is that row, and note where its side condition sits: on the
    **receiver's element type**, not on `ρ`. Keyed on `ρ = .never` it would be a much weaker
    claim (a block that never returns for a *non-empty* array is a different situation
    entirely); keyed on the receiver it is the argument above, in one line.

    So the two calls in this program take *different* `IterSig` rows for the same `inject`, and
    the derivation shows it: `.inject` on the left, `.injectEmpty` on the right. -/
def r152 : Rung :=
  ⟨"param-rest",
    .seq [.def' "total" [.rest (some "ns")]
            (.send (some (.var .lvar "ns")) "inject" [.int 0]
              (some (.block [.req "a", .req "b"] []
                (.send (some (.var .lvar "a")) "+" [.var .lvar "b"] none)))),
          .send (some (.send none "total" [.int 1, .int 2, .int 3] none)) "+"
            [.send none "total" [] none] none],
    .int, [],
    .seq (.cons .defStmt
      (.last (.prim
        (.callDef (.cons .intLit (.cons .intLit (.cons .intLit .nil))) rfl rfl
          (.iterBlock (.var rfl rfl) (.cons .intLit .nil) .inject rfl
            (.prim (.var rfl rfl) (.cons (.var rfl rfl) .nil) .intAdd) rfl))
        (.cons
          (.callDef .nil rfl rfl
            (.iterBlock (.var rfl rfl) (.cons .intLit .nil) .injectEmpty rfl
              (.primNever (.var rfl rfl) (.cons (.var rfl rfl) .nil) (.inr rfl)) rfl))
          .nil)
        .intAdd)))⟩

/-! ### Tier 14c — keyword arguments

The call shape changes here, which is why these three needed a new rule rather than a new row.
`Expr.kwargs` is the last element of an argument list and **is not a value**: it has no `Ty` and
`JudgeAll` cannot type it. So `Judge.callDefKw` splits the list — positional arguments by
`JudgeAll`, keyword arguments by `JudgeKw` into name/type pairs — and `paramEnvK` matches
keywords **by name**. -/

/-- `def build(type:, name:); type + "/" + name; end; build(type: "brew", name: "x")` →
    `String`.

    The plain case, and what to read off the derivation is where the *soundness* of this tier
    sits: in `paramEnvK`, which is `paramBind` and answers `none` in two situations that both
    raise `ArgumentError` — a **missing required** keyword (the tier's permanent negative,
    `param-missing-keyword-unsafe`) and an **unexpected** keyword (`paramBind`'s `kws.isEmpty`
    check at the end of the walk, control (e2)). Unlike a positional arity mismatch, which is
    also an `ArgumentError` but which `paramEnv`'s length matching already refused for free,
    these two are *name*-directed and had to be built.

    Note what is absent: no assumption is added to `κ.asms`. An `AsmTable` key is a `List Ty`
    and cannot distinguish a keyword call from a positional one at the same types, so a
    *believed* assumption under such a key would be unsound — see `Judge.callDefKw`. A
    keyword-recursive method therefore does not type, which no rung wants and which is
    conservative. -/
def r154 : Rung :=
  ⟨"param-keyword",
    .seq [.def' "build" [.key "type" none, .key "name" none]
            (.send (some (.send (some (.var .lvar "type")) "+" [.str "/"] none)) "+"
              [.var .lvar "name"] none),
          .send none "build" [.kwargs [.pair "type" (.str "brew"), .pair "name" (.str "x")]]
            none],
    .cls "String", [],
    .seq (.cons .defStmt
      (.last (.callDefKw rfl .nil (.pair .strLit (.pair .strLit .nil)) rfl rfl
        (.prim (.prim (.var rfl rfl) (.cons .strLit .nil) .strAdd)
          (.cons (.var rfl rfl) .nil) .strAdd))))⟩

/-- `def build(name:, version: nil); version.nil? ? name : name + "@" + version; end;
    build(name: "x") + build(name: "x", version: "1")` → `String`.

    **The rung where tier 14 and tier 12 meet.** One `def`, two calls, and the *same* `if` is
    typed twice with opposite branches dead:

    - `build(name: "x")` — `version` takes its default, so it is `.nilT`. `nonNilTy .nilT` is
      `.never`, the **else**-branch is dead, and `name + "@" + version` types by `primNever`
      without any claim about `String#+`.
    - `build(name: "x", version: "1")` — `version` is a `String`. `isNilTy` makes the
      **then**-branch's `version` `.never`, but the branch returns `name`, so nothing notices;
      the else-branch is live and `name + "@" + version` is an ordinary `strAdd` chain.

    Both branches join to `String` either way. A keyword default is `constLitTy?`'s answer,
    exactly as an optional positional default is (clink 33), which is why `nil` as a default
    gives the precise `.nilT` rather than a nilable — and that precision is the whole reason the
    first call's else-branch is dead rather than merely unreachable-looking. -/
def r155 : Rung :=
  ⟨"param-keyword-default",
    .seq [.def' "build" [.key "name" none, .key "version" (some .nil)]
            (.if' (.send (some (.var .lvar "version")) "nil?" [] none)
              (.var .lvar "name")
              (some (.send (some (.send (some (.var .lvar "name")) "+" [.str "@"] none)) "+"
                [.var .lvar "version"] none))),
          .send (some (.send none "build" [.kwargs [.pair "name" (.str "x")]] none)) "+"
            [.send none "build"
               [.kwargs [.pair "name" (.str "x"), .pair "version" (.str "1")]] none] none],
    .cls "String", [],
    .seq (.cons .defStmt
      (.last (.prim (σ := .cls "String") (argTys := [.cls "String"])
        (.callDefKw (ρ := .cls "String") rfl .nil (.pair .strLit .nil) rfl rfl
          -- The branch types are pinned because they have to be: the `if`'s type is
          -- `joinT τ₁ τ₂`, and until both are known the elaborator cannot see that it is the
          -- `String` the surrounding `+` wants, so it postpones the `rfl`s inside the branches
          -- and never comes back. Purely an elaboration-order matter -- and the *values*
          -- pinned are the finding: `.never` on the right is the dead else-branch.
          (.if' (τ₁ := .cls "String") (τ₂ := .never)
              (.prim (.var rfl rfl) .nil (.nilQuery .nilT))
            (.var rfl rfl)
            (.primNever (.prim (.var rfl rfl) (.cons .strLit .nil) .strAdd)
              (.cons (.var rfl rfl) .nil) (.inr rfl))
            rfl))
        (.cons
          (.callDefKw (ρ := .cls "String") rfl .nil
              (.pair .strLit (.pair .strLit .nil)) rfl rfl
            (.if' (τ₁ := .cls "String") (τ₂ := .cls "String")
                (.prim (.var rfl rfl) .nil (.nilQuery .cls))
              (.var rfl rfl)
              (.prim (.prim (.var rfl rfl) (.cons .strLit .nil) .strAdd)
                (.cons (.var rfl rfl) .nil) .strAdd)
              rfl))
          .nil)
        .strAdd)))⟩

/-- `def build(type:, name:); type + "/" + name; end; type = "brew"; name = "x";
    build(type:, name:)` → `String`.

    Ruby 3.1's keyword shorthand, and the finding is that it is **not sugar at the AST level**
    the way `x ||= 5` is: the desugarer emits `kwargs [pair "type" (var local "type"), …]`, so
    the *value* of each keyword is an ordinary local read and `JudgeKw` types it with the rule
    it already had. Nothing was added for this rung.

    What it does exercise is that a keyword's value is typed in the *caller's* environment while
    its name binds in the *callee's* — the two `type`s in `type: type` are different variables
    in different scopes, and the derivation's `.var rfl rfl` under `.pair` is the caller's. -/
def r161 : Rung :=
  ⟨"param-shorthand-kwarg",
    .seq [.def' "build" [.key "type" none, .key "name" none]
            (.send (some (.send (some (.var .lvar "type")) "+" [.str "/"] none)) "+"
              [.var .lvar "name"] none),
          .vasgn .lvar "type" (.str "brew"),
          .vasgn .lvar "name" (.str "x"),
          .send none "build"
            [.kwargs [.pair "type" (.var .lvar "type"), .pair "name" (.var .lvar "name")]]
            none],
    .cls "String", [("type", .cls "String"), ("name", .cls "String")],
    .seq (.cons .defStmt (.cons (.vasgn .strLit) (.cons (.vasgn .strLit)
      (.last (.callDefKw rfl .nil
        (.pair (.var rfl rfl) (.pair (.var rfl rfl) .nil)) rfl rfl
        (.prim (.prim (.var rfl rfl) (.cons .strLit .nil) .strAdd)
          (.cons (.var rfl rfl) .nil) .strAdd))))))⟩

/-! ## Tier 15 — strings, symbols and regexps

Tier 15a: the rows. Nine `PrimSig` rows plus one `Judge` rule (`regexpLit`), and the finding is
how ordinary the target's string diet turns out to be — total `String -> String` and
`String -> Bool` methods, with exactly one row (`String#match`) that answers something the
caller has to be careful with. -/

/-- `n = 3; "n = #{n + 1}"` → `String`.

    `str-interpolation`'s twin (r165) and the pair is the point: there, the interpolated
    expression was already a `String`, so `caseEqQuery` refined the else-branch to `.never` and
    the rung climbed with **no `__as_string` row at all**. Here it is an `Integer`, the
    then-branch is the dead one, and the row is needed. `PrimSig.intAsString` is it —
    `__as_string` is the desugarer's marker for interpolation's `to_s`, not a method anyone
    writes.

    So the derivation is r165's with the two branches' roles swapped: `primNever` on the *then*
    side (`String === 4` is false, so `isATy` makes `__dt_t1` `.never` there) and a real send on
    the else side. `joinT .never (cls String)` is `String`. -/
def r166 : Rung :=
  ⟨"str-interpolation-nonstring",
    .seq [.vasgn .lvar "n" (.int 3),
          .send (some (.str "n = ")) "+"
            [.seq [.vasgn .lvar "__dt_t1" (.send (some (.var .lvar "n")) "+" [.int 1] none),
                   .if' (.send (some (.const "String")) "===" [.var .lvar "__dt_t1"] none)
                     (.var .lvar "__dt_t1")
                     (some (.send (some (.var .lvar "__dt_t1")) "__as_string" [] none))]]
            none],
    .cls "String", [("n", .int), ("__dt_t1", .int)],
    .seq (.cons (.vasgn .intLit)
      (.last (.prim .strLit
        (.cons (.seq (.cons (.vasgn (.prim (.var rfl rfl) (.cons .intLit .nil) .intAdd))
          (.last (.if' (τ₁ := .never) (τ₂ := .cls "String")
            (.caseEqQuery (.constBuiltin .string rfl rfl) (.cons (.var rfl rfl) .nil) rfl)
            (.var rfl rfl)
            (.prim (.var rfl rfl) .nil .intAsString)
            rfl)))) .nil)
        .strAdd)))⟩

/-- `%w[a b c].length` → `Integer`, and it climbed with **no rule written at all** — twice over.
    `%w[…]` is not a syntactic form by the time this checker sees it (the desugarer emits an
    ordinary array of string literals), and `Array#length` arrived with tier 14b's rest
    parameters, for a completely unrelated reason. A free rung, recorded as one. -/
def r170 : Rung :=
  ⟨"str-percent-w",
    .send (some (.array [.str "a", .str "b", .str "c"])) "length" [] none,
    .int, [],
    .prim (.arrayLit (.cons .strLit (.cons .strLit (.cons .strLit .nil)))) .nil .arrayLength⟩

/-- `"1.2.3".match?(/\A\d+(\.\d+)*\z/)` → `Bool`.

    The first regexp rung, and it settles the design question cheaply: a `Regexp` is
    `.cls "Regexp"` and **opaque**. Nothing reads the pattern text, which is forced rather than
    chosen — `regexp-interpolated` shows a pattern can be built at runtime, so any reasoning
    about pattern text would work on literals and fail on exactly the patterns the target
    writes. `match?` answers `Bool` and computes nothing about *which* bool. -/
def r171 : Rung :=
  ⟨"regexp-match-p",
    .send (some (.str "1.2.3")) "match?" [.regexpLit "\\A\\d+(\\.\\d+)*\\z" 0] none,
    .bool, [],
    .prim .strLit (.cons .regexpLit .nil) .strMatchP⟩

/-- `"abc".match(/\d+/).nil?` → `Bool`.

    `String#match` answers `T.nilable(MatchData)`, and this rung is the *safe* half of what that
    buys: asking a nilable whether it is nil is always fine, because `NilQSafe` is recursive at
    `nilable` (it has been since tier 2, for `nil?` on an `Array#[]` result). The unsafe half is
    `regexp-match-captures` / `regexp-no-match-unsafe`, which this row deliberately does not
    separate — see `PrimSig.strMatch`. -/
def r173 : Rung :=
  ⟨"regexp-match-nil",
    .send (some (.send (some (.str "abc")) "match" [.regexpLit "\\d+" 0] none)) "nil?" []
      none,
    .bool, [],
    .prim (.prim .strLit (.cons .regexpLit .nil) .strMatch) .nil
      (.nilQuery (.nilable .cls))⟩

/-- `"v1.2.3".sub(/\Av/, "")` → `String`. -/
def r174 : Rung :=
  ⟨"regexp-sub",
    .send (some (.str "v1.2.3")) "sub" [.regexpLit "\\Av" 0, .str ""] none,
    .cls "String", [],
    .prim .strLit (.cons .regexpLit (.cons .strLit .nil)) .strSub⟩

/-- `"a_b_c".gsub(/_/, "-")` → `String`. `sub`'s twin, and a separate row rather than one row
    for both because they are different methods — the shared signature is a coincidence of this
    call shape, and `gsub`'s block and Hash forms (rung `regexp-gsub-block`) are not `sub`'s. -/
def r175 : Rung :=
  ⟨"regexp-gsub",
    .send (some (.str "a_b_c")) "gsub" [.regexpLit "_" 0, .str "-"] none,
    .cls "String", [],
    .prim .strLit (.cons .regexpLit (.cons .strLit .nil)) .strGsub⟩

/-- `"a/b/c".split("/").length` → `Integer`.

    `String#split` is the one row in this batch whose *result* says something a caller can use:
    `arrayOf (cls String)`. What it cannot say is how many — which is `narrow-nilable-and-union`'s
    length-indexed array arriving from the direction the slice asks for it most
    (`a, b = s.split("-")` in `identify.rb`). Here only `length` is taken, so the gap does not
    bite. -/
def r177 : Rung :=
  ⟨"regexp-split",
    .send (some (.send (some (.str "a/b/c")) "split" [.str "/"] none)) "length" [] none,
    .int, [],
    .prim (.prim .strLit (.cons .strLit .nil) .strSplit) .nil .arrayLength⟩

/-- `re = /…/x; "12".match?(re)` → `Bool`, with the `/x` (extended) flag.

    The rung exists to check that **ignoring the flags is enough**, and it is: the flags are
    carried in the syntax (`Expr.regexpLit`'s `opts`, `2` here) and `Judge.regexpLit` does not
    look at them, because what they change is which strings match — an answer this type language
    never computes. The regexp also goes through a local on the way, which is the shape
    `semver.rb` writes. -/
def r179 : Rung :=
  ⟨"regexp-extended-flag",
    .seq [.vasgn .lvar "re" (.regexpLit "\n  \\A\n  \\d+\n  \\z\n" 2),
          .send (some (.str "12")) "match?" [.var .lvar "re"] none],
    .bool, [("re", .cls "Regexp")],
    .seq (.cons (.vasgn .regexpLit)
      (.last (.prim .strLit (.cons (.var rfl rfl) .nil) .strMatchP)))⟩

/-- `s = "  Foo_Bar  "; s.strip.downcase.tr("_", "-").delete_prefix("f")` → `String`.

    Four rows in one chain, and all four are the same row twice over: total, `String` in,
    `String` out. The arguments are *not* unconstrained — `tr` and `delete_prefix` raise
    `TypeError` on a non-String — which is the only thing to be careful about in the batch and
    the reason the rows name `.cls "String"` rather than a wildcard. -/
def r181 : Rung :=
  ⟨"str-methods",
    .seq [.vasgn .lvar "s" (.str "  Foo_Bar  "),
          .send (some (.send (some (.send (some (.send (some (.var .lvar "s")) "strip" []
            none)) "downcase" [] none)) "tr" [.str "_", .str "-"] none)) "delete_prefix"
            [.str "f"] none],
    .cls "String", [("s", .cls "String")],
    .seq (.cons (.vasgn .strLit)
      (.last (.prim
        (.prim
          (.prim (.prim (.var rfl rfl) .nil .strStrip) .nil .strDowncase)
          (.cons .strLit (.cons .strLit .nil)) .strTr)
        (.cons .strLit .nil) .strDeletePrefix)))⟩

/-- `"CVE-2026-1".start_with?("CVE-")` → `Bool`. -/
def r182 : Rung :=
  ⟨"str-start-with",
    .send (some (.str "CVE-2026-1")) "start_with?" [.str "CVE-"] none,
    .bool, [],
    .prim .strLit (.cons .strLit .nil) .strStartsWith⟩

/-! ## Tier 16 — control flow beyond `if`

Tier 16a: the loop, the `next` guard, and `case/when` over values. `begin`/`rescue` is a
separate clink. -/

/-- `i = 0; n = 0; while i < 3; n = n + i; i = i + 1; end; n` → `Integer`.

    **Both of `while'`'s premises come back to the environment they started in**, and that is
    the whole rule. A loop body's outgoing environment feeds its own *next* iteration, so
    letting it change the environment would need a fixed point over `Env`; requiring the
    condition and the body to leave every type where they found it makes the fixed point
    trivial — every iteration is typed by the same two derivations.

    It is not a restriction on *assignment*: `n = n + i` and `i = i + 1` both assign, and both
    keep their types, which is all the premises ask. What it refuses is a loop that changes a
    local's *type*, and a checker that allowed that would be reasoning about the first iteration
    only.

    Third appearance of clink 11's rule — a callee may not retype state its caller can still
    see — with the loop as the callee. -/
def r184 : Rung :=
  ⟨"ctl-while",
    .seq [.vasgn .lvar "i" (.int 0),
          .vasgn .lvar "n" (.int 0),
          .while' (.send (some (.var .lvar "i")) "<" [.int 3] none)
            (.seq [.vasgn .lvar "n" (.send (some (.var .lvar "n")) "+"
                     [.var .lvar "i"] none),
                   .vasgn .lvar "i" (.send (some (.var .lvar "i")) "+" [.int 1] none)]),
          .var .lvar "n"],
    .int, [("i", .int), ("n", .int)],
    .seq (.cons (.vasgn .intLit) (.cons (.vasgn .intLit)
      (.cons (.while' (.prim (.var rfl rfl) (.cons .intLit .nil) .intLt) rfl rfl
               (.seq (.cons (.vasgn (.prim (.var rfl rfl) (.cons (.var rfl rfl) .nil) .intAdd))
                 (.last (.vasgn (.prim (.var rfl rfl) (.cons .intLit .nil) .intAdd)))))
               rfl rfl)
        (.last (.var rfl rfl)))))⟩

/-- `i = 0; until i >= 3; i = i + 1; end; i` → `Integer`.

    **`until` is not a rule.** The desugarer emits `while (cond).!`, so this is `r184` with one
    more `PrimSig.notBool` in the condition — which is why tier 2's decision to make `!` an
    ordinary send rather than syntax (clink 1) keeps paying off. -/
def r185 : Rung :=
  ⟨"ctl-until",
    .seq [.vasgn .lvar "i" (.int 0),
          .while' (.send (some (.send (some (.var .lvar "i")) ">=" [.int 3] none)) "!" []
                     none)
            (.vasgn .lvar "i" (.send (some (.var .lvar "i")) "+" [.int 1] none)),
          .var .lvar "i"],
    .int, [("i", .int)],
    .seq (.cons (.vasgn .intLit)
      (.cons (.while' (.prim (.prim (.var rfl rfl) (.cons .intLit .nil) .intGe) .nil .notBool)
               rfl rfl
               (.vasgn (.prim (.var rfl rfl) (.cons .intLit .nil) .intAdd)) rfl rfl)
        (.last (.var rfl rfl))))⟩

/-- `s = 0; [1, 2, 3, 4].each do |x| next if x == 2; s = s + x end; s` → `Integer`.

    `next` gets no rule of its own, and both obvious rules are unsound. Typed `.never` it breaks
    `map { next }`, where the element really is `nil` and `arrayOf .never` claims the array is
    *empty*. Typed `.nilT` it breaks the sequence, because `JudgeSeq` takes the last statement's
    type and would miss that the statements after the `next` do not run on that path.

    Both failures are about the **sequence**, so — exactly as for `.ret` in tier 12 — the rule
    belongs to the sequence: `JudgeSeq.nextGuard`, `guard`'s twin with `ρ` fixed at `.nilT`. The
    block body's type is `joinT .nilT Int = T.nilable(Integer)`, which `each` discards
    (`IterSig.each` leaves the block's return type unconstrained), and the same narrowing
    applies — the statements after `next if c` are typed in the else-branch's environment.

    `capIntact` is what makes the `s = s + x` inside the block legal: `s` is captured, and it is
    reassigned but not retyped. -/
def r186 : Rung :=
  ⟨"ctl-next",
    .seq [.vasgn .lvar "s" (.int 0),
          .send (some (.array [.int 1, .int 2, .int 3, .int 4])) "each" []
            (some (.block [.req "x"] []
              (.seq [.if' (.send (some (.var .lvar "x")) "==" [.int 2] none) (.nxt none) none,
                     .vasgn .lvar "s" (.send (some (.var .lvar "s")) "+"
                       [.var .lvar "x"] none)]))),
          .var .lvar "s"],
    .int, [("s", .int)],
    .seq (.cons (.vasgn .intLit)
      (.cons (.iterBlock (.arrayLit (.cons .intLit (.cons .intLit (.cons .intLit
                 (.cons .intLit .nil))))) .nil .each rfl
               (.seq (.nextGuard (.prim (.var rfl rfl) (.cons .intLit .nil) (.objEq .int))
                 (.last (.vasgn (.prim (.var rfl rfl) (.cons (.var rfl rfl) .nil) .intAdd)))))
               rfl)
        (.last (.var rfl rfl))))⟩

/-- `def kind(t); case t; when "pypi" then "python"; when "gem" then "ruby"; else "other"; end;
    end; kind("gem") + kind("x")` → `String`.

    `case/when` over **values** rather than classes, and the desugaring is the finding: it emits
    `"pypi" === __dt_t1`, i.e. a send whose *receiver* is the `when` clause's literal. So this is
    not tier 12's `caseEqQuery` (which wants a class object and consults the class table) but a
    `PrimSig` row, guarded by `EqSafe` exactly as `==` is — `Object#===` is `==` unless someone
    overrode it, and `EqSafe` is precisely the receivers whose method table is the builtin one.

    The two rules are disjoint because `.clsOf` is not `EqSafe`, so no program has a derivation
    reading one `===` two ways.

    Nothing narrows here, and nothing needs to: the branches are all `String` literals, and
    knowing *which* string `t` is would tell the checker nothing it uses. Two calls at the same
    argument shape, so `callDef` types the body twice identically. -/
def r196 : Rung :=
  ⟨"ctl-case-when-string",
    .seq [.def' "kind" [.req "t"]
            (.seq [.vasgn .lvar "__dt_t1" (.var .lvar "t"),
                   .if' (.send (some (.str "pypi")) "===" [.var .lvar "__dt_t1"] none)
                     (.str "python")
                     (some (.if' (.send (some (.str "gem")) "===" [.var .lvar "__dt_t1"] none)
                       (.str "ruby")
                       (some (.str "other"))))]),
          .send (some (.send none "kind" [.str "gem"] none)) "+"
            [.send none "kind" [.str "x"] none] none],
    .cls "String", [],
    .seq (.cons .defStmt
      (.last (.prim
        (.callDef (.cons .strLit .nil) rfl rfl
          (.seq (.cons (.vasgnAlias rfl rfl rfl)
            (.last (.if' (.prim .strLit (.cons (.varAlias rfl) .nil) (.caseEqPrim .cls))
              .strLit
              (.if' (.prim .strLit (.cons (.varAlias rfl) .nil) (.caseEqPrim .cls))
                .strLit .strLit rfl)
              rfl)))))
        (.cons
          (.callDef (.cons .strLit .nil) rfl rfl
            (.seq (.cons (.vasgnAlias rfl rfl rfl)
              (.last (.if' (.prim .strLit (.cons (.varAlias rfl) .nil) (.caseEqPrim .cls))
                .strLit
                (.if' (.prim .strLit (.cons (.varAlias rfl) .nil) (.caseEqPrim .cls))
                  .strLit .strLit rfl)
                rfl)))))
          .nil)
        .strAdd)))⟩

/-! ### Tier 16b — `begin`/`rescue`, which in this target is not error handling

§Frontier item E: `Vulnerability` defines its own `Uncomparable < StandardError` and uses
raise/rescue as the **comparison protocol**, so a checker that cannot follow exceptions cannot
type the decision core at all. -/

/-- `def parse(s); raise ArgumentError, "bad" if s.empty?; s.length; rescue ArgumentError => e;
    e.message.length; end; parse("") + parse("ab")` → `Integer`.

    Four new pieces, and each is a different kind of thing:

    - **`raise` is `.never`.** It does not return, so no claim about its value can be falsified —
      the same reading `primNever` gives a send with a non-returning argument, arrived at from
      the other side. Its premise (`excName?`) is soundness: `raise 5` raises `TypeError`.
    - **`ArgumentError` needed a third `const` rule.** `ExcCls` is deliberately not folded into
      `BuiltinCls`, which is kept to the classes `builtinAncestors` can answer `is_a?` for.
    - **`rescue … => e` binds `e` at `.cls "ArgumentError"`**, and `PrimSig.excMessage` is the
      one row on this ladder whose *receiver* is guarded by a name predicate rather than a type
      shape — without the guard it would fire for `.cls "String"`, where `message` is a
      `NoMethodError`.
    - **`noLocalAsgn body` is the environment story**, and it is the interesting one. A handler
      runs at an *arbitrary point inside the body*, so it cannot be typed in the body's incoming
      environment, nor its outgoing one, nor the join of the two: `v = 1; v = "s"; v = 2` has the
      same types at both ends and a different one in the middle. A body with no local assignment
      has no intermediate state to get wrong, and tier 12's whitelist is reused unchanged.

    Both branches join to `Integer`, and the derivation shows the join twice over: the body's
    `s.length` and the handler's `e.message.length`. -/
def r192 : Rung :=
  ⟨"ctl-rescue",
    .seq [.def' "parse" [.req "s"]
            (.begin'
              (.seq [.if' (.send (some (.var .lvar "s")) "empty?" [] none)
                       (.send none "raise" [.const "ArgumentError", .str "bad"] none) none,
                     .send (some (.var .lvar "s")) "length" [] none])
              [([.const "ArgumentError"], some (.lvar, "e"),
                 .send (some (.send (some (.var .lvar "e")) "message" [] none)) "length" []
                   none)]
              none none),
          .send (some (.send none "parse" [.str ""] none)) "+"
            [.send none "parse" [.str "ab"] none] none],
    .int, [],
    .seq (.cons .defStmt
      (.last (.prim
        (.callDef (.cons .strLit .nil) rfl rfl
          (.begin' (τb := .int)
            (.seq (.cons (.ifNoElse (τ := .never)
                     (.prim (.var rfl rfl) .nil .strEmptyP)
                     (.raiseCls (.cons (.constExc .argumentError rfl rfl)
                       (.cons .strLit .nil)) (.inr rfl) rfl)
                     rfl)
              (.last (.prim (σ := .cls "String") (.var rfl rfl) .nil .strLength))))
            rfl rfl rfl
            (.cons rfl rfl rfl
              (.prim (.prim (.var rfl rfl) .nil (.excMessage .argumentError)) .nil
                .strLength)
              rfl rfl .nil)))
        (.cons
          (.callDef (.cons .strLit .nil) rfl rfl
            (.begin' (τb := .int)
              (.seq (.cons (.ifNoElse (τ := .never)
                       (.prim (.var rfl rfl) .nil .strEmptyP)
                       (.raiseCls (.cons (.constExc .argumentError rfl rfl)
                         (.cons .strLit .nil)) (.inr rfl) rfl)
                       rfl)
                (.last (.prim (σ := .cls "String") (.var rfl rfl) .nil .strLength))))
              rfl rfl rfl
              (.cons rfl rfl rfl
                (.prim (.prim (.var rfl rfl) .nil (.excMessage .argumentError)) .nil
                  .strLength)
                rfl rfl .nil)))
          .nil)
        .intAdd)))⟩

/-- `class Uncomparable < StandardError; end; def cmp(a); raise Uncomparable if a.nil?; 1;
    rescue Uncomparable; 0; end; cmp(nil) + cmp(1)` → `Integer`.

    **The rung the target actually needs.** `Vulnerability` raises and rescues its own
    `Uncomparable` as the comparison protocol, and this is that shape in miniature.

    What is new over `ctl-rescue` is that `Uncomparable` is a **user** class, so `excName?` has
    to *walk*: not a builtin exception name, so look it up in `CTable`, follow `Cls.super?` to
    `StandardError`, and that is a builtin one. The walk is fuel-bounded for `nestedClasses`'
    reason (a `super?` chain has no structural measure) and answers `false` when it runs out,
    which is a rejected `raise` rather than a wrong one.

    The handler has no `=> e`, so `rescueBind?` contributes the empty environment — which is
    what lets a *user* exception be rescued at all today, since `.cls n` is only offered for the
    builtin names. Binding one would want `.inst n .ivar0`, and no rung asks. -/
def r194 : Rung :=
  ⟨"ctl-raise-custom",
    .seq [.class' "Uncomparable" (some (.const "StandardError")) .nil,
          .def' "cmp" [.req "a"]
            (.begin'
              (.seq [.if' (.send (some (.var .lvar "a")) "nil?" [] none)
                       (.send none "raise" [.const "Uncomparable"] none) none,
                     .int 1])
              [([.const "Uncomparable"], none, .int 0)]
              none none),
          .send (some (.send none "cmp" [.nil] none)) "+"
            [.send none "cmp" [.int 1] none] none],
    .int, [],
    .seq (.cons (.classStmt rfl rfl rfl .nil .nil) (.cons .defStmt
      (.last (.prim
        (.callDef (.cons .nilLit .nil) rfl rfl
          (.begin' (τb := .int)
            (.seq (.cons (.ifNoElse (τ := .never)
                     (.prim (.var rfl rfl) .nil (.nilQuery .nilT))
                     (.raiseCls (.cons (.constCls rfl rfl) .nil) (.inl rfl) rfl)
                     rfl)
              (.last .intLit)))
            rfl rfl rfl
            (.cons rfl rfl rfl .intLit rfl rfl .nil)))
        (.cons
          (.callDef (.cons .intLit .nil) rfl rfl
            (.begin' (τb := .int)
              (.seq (.cons (.ifNoElse (τ := .never)
                       (.prim (.var rfl rfl) .nil (.nilQuery .int))
                       (.raiseCls (.cons (.constCls rfl rfl) .nil) (.inl rfl) rfl)
                       rfl)
                (.last .intLit)))
              rfl rfl rfl
              (.cons rfl rfl rfl .intLit rfl rfl .nil)))
          .nil)
        .intAdd))))⟩

/-! ## Tier 17 — collections

Tier 17a: the `Array` rows and iterators. `homebrew/README.md` §2 measures the gap these close
over all of Homebrew (6.4% of 113,610 call sites resolve to nothing we have); this is its
slice-sized head, and it is almost entirely *rows* — the only new idea is that three guards move
from the receiver's type to the **element's**. -/

/-- `(1 <=> 2) + (2 <=> 1)` → `Integer`. `Integer#<=>` on two Integers always answers an
    Integer; it is `nil` only for incomparable operands, which this row's argument type
    excludes. -/
def r200 : Rung :=
  ⟨"lib-spaceship-int",
    .send (some (.send (some (.int 1)) "<=>" [.int 2] none)) "+"
      [.send (some (.int 2)) "<=>" [.int 1] none] none,
    .int, [],
    .prim (.prim .intLit (.cons .intLit .nil) .intSpaceship)
      (.cons (.prim .intLit (.cons .intLit .nil) .intSpaceship) .nil) .intAdd⟩

/-- `h = { "a" => 1 }; h.key?("a")` → `Bool`.

    The guard is on the **argument**, because that is what `Hash#key?` hashes — the first row
    where `NilQSafe` is asked about something other than the receiver. And note what the rung
    does *not* get: `Bool`, with nothing about the value behind the key, because the bare
    `.cls "Hash"` cannot describe it (§Frontier item A). -/
def r205 : Rung :=
  ⟨"lib-hash-key-p",
    .seq [.vasgn .lvar "h" (.hash [(.str "a", .int 1)]),
          .send (some (.var .lvar "h")) "key?" [.str "a"] none],
    .bool, [("h", .hashOf (.cls "String") .int)],
    .seq (.cons (.vasgn (.hashLit (.cons .strLit .intLit .nil)))
      (.last (.prim (.var rfl rfl) (.cons .strLit .nil) (.hashKeyP .cls))))⟩

/-- `xs = [1, 2, 3]; [xs.any? { |x| x > 2 }, xs.all? { |x| x > 0 }, xs.include?(2),
    xs.empty?].length` → `Integer`.

    Four query forms in one array literal, and the array literal is what makes the rung a rung:
    all four have to answer `Bool` for `elemTy` to be `bool` rather than a union nothing
    consumes.

    `any?`/`all?` leave the block's return type unconstrained, for `select`'s reason — the
    result is only tested for truthiness, which never raises. `include?` carries a
    `NilQSafe` guard on the **element** type, because it calls `==` on the elements and a
    user-written `==` can raise. -/
def r207 : Rung :=
  ⟨"lib-array-queries",
    .seq [.vasgn .lvar "xs" (.array [.int 1, .int 2, .int 3]),
          .send (some (.array [
            .send (some (.var .lvar "xs")) "any?" []
              (some (.block [.req "x"] [] (.send (some (.var .lvar "x")) ">" [.int 2] none))),
            .send (some (.var .lvar "xs")) "all?" []
              (some (.block [.req "x"] [] (.send (some (.var .lvar "x")) ">" [.int 0] none))),
            .send (some (.var .lvar "xs")) "include?" [.int 2] none,
            .send (some (.var .lvar "xs")) "empty?" [] none])) "length" [] none],
    .int, [("xs", .arrayOf .int)],
    .seq (.cons (.vasgn (.arrayLit (.cons .intLit (.cons .intLit (.cons .intLit .nil)))))
      (.last (.prim
        (.arrayLit (.cons (.iterBlock (.var rfl rfl) .nil .anyP rfl
                            (.prim (.var rfl rfl) (.cons .intLit .nil) .intGt) rfl)
          (.cons (.iterBlock (.var rfl rfl) .nil .allP rfl
                   (.prim (.var rfl rfl) (.cons .intLit .nil) .intGt) rfl)
            (.cons (.prim (.var rfl rfl) (.cons .intLit .nil) (.arrayInclude .int))
              (.cons (.prim (.var rfl rfl) .nil .arrayEmptyP) .nil)))))
        .nil .arrayLength)))⟩

/-- `[1, 1, nil, 2].compact.uniq.length` → `Integer`.

    **`compact`'s result type is computed by a tier-12 refinement.** The literal is
    `arrayOf (nilable Int)` (`elemTy` joins `Int` with `nil`), and removing the `nil`s is exactly
    `nonNilTy` — the first time one of narrowing's type functions is used on a *result* rather
    than in a branch. `uniq` then keeps the element type and carries the `NilQSafe` guard, for
    `include?`'s reason one method over (it hashes the elements). -/
def r209 : Rung :=
  ⟨"lib-array-uniq-compact",
    .send (some (.send (some (.send (some (.array [.int 1, .int 1, .nil, .int 2]))
      "compact" [] none)) "uniq" [] none)) "length" [] none,
    .int, [],
    .prim (.prim (.prim (.arrayLit (.cons .intLit (.cons .intLit (.cons .nilLit
      (.cons .intLit .nil))))) .nil .arrayCompact) .nil (.arrayUniq .int)) .nil .arrayLength⟩

/-- `[[1, 2], [3]].flat_map { |a| a }.length` → `Integer`.

    The one iterator row whose applicability is decided by the **block's return type**: the
    block must return an array, and the result's element type is that array's. Ruby also accepts
    a non-array return (it is included as-is), and that shape has no row — the result would be a
    union of two element types and nothing consumes one. -/
def r210 : Rung :=
  ⟨"lib-array-flat-map",
    .send (some (.send (some (.array [.array [.int 1, .int 2], .array [.int 3]]))
      "flat_map" [] (some (.block [.req "a"] [] (.var .lvar "a"))))) "length" [] none,
    .int, [],
    .prim (.iterBlock (.arrayLit (.cons (.arrayLit (.cons .intLit (.cons .intLit .nil)))
      (.cons (.arrayLit (.cons .intLit .nil)) .nil))) .nil .flatMap rfl (.var rfl rfl) rfl)
      .nil .arrayLength⟩

/-- `[1, 2, 3].filter_map { |x| x > 1 ? x : nil }.length` → `Integer`.

    `filter_map` keeps the block's **truthy** results, so the element type is `truthyTy ρ` — the
    second result type computed by a narrowing function, and `truthyTy` rather than `nonNilTy`
    because `false` is dropped too. Here `ρ` is `joinT Int nilT = T.nilable(Integer)` and
    `truthyTy` of that is `Integer`. -/
def r211 : Rung :=
  ⟨"lib-array-filter-map",
    .send (some (.send (some (.array [.int 1, .int 2, .int 3])) "filter_map" []
      (some (.block [.req "x"] []
        (.if' (.send (some (.var .lvar "x")) ">" [.int 1] none) (.var .lvar "x")
          (some .nil)))))) "length" [] none,
    .int, [],
    .prim (.iterBlock (.arrayLit (.cons .intLit (.cons .intLit (.cons .intLit .nil))))
      .nil .filterMap rfl
      (.if' (.prim (.var rfl rfl) (.cons .intLit .nil) .intGt) (.var rfl rfl) .nilLit rfl)
      rfl)
      .nil .arrayLength⟩

/-- `[1, 2, 3].find { |x| x > 1 }` → `T.nilable(Integer)`.

    `find` answers an element **or nil**, because nothing may match — and the rung's recorded
    type is the nilable, which is the honest one. It is also the shape §Frontier item G is about:
    the slice writes `find` where it knows something matches, and `Ty` cannot say so. -/
def r212 : Rung :=
  ⟨"lib-array-find",
    .send (some (.array [.int 1, .int 2, .int 3])) "find" []
      (some (.block [.req "x"] [] (.send (some (.var .lvar "x")) ">" [.int 1] none))),
    .nilable .int, [],
    .iterBlock (.arrayLit (.cons .intLit (.cons .intLit (.cons .intLit .nil)))) .nil
      .findFirst rfl (.prim (.var rfl rfl) (.cons .intLit .nil) .intGt) rfl⟩

/-- `["a", "b"].join("/")` → `String`. Restricted to `String` elements, because `join` calls
    `to_s` on every element and a user-written `to_s` can do anything. -/
def r215 : Rung :=
  ⟨"lib-array-join",
    .send (some (.array [.str "a", .str "b"])) "join" [.str "/"] none,
    .cls "String", [],
    .prim (.arrayLit (.cons .strLit (.cons .strLit .nil))) (.cons .strLit .nil) .arrayJoin⟩

/-- `s = 0; [10, 20].each_with_index do |v, i| s = s + v + i end; s` → `Integer`.

    The **first two-parameter iterator whose second parameter is not an accumulator**: `inject`
    binds `[α, τ]`, this binds `[τ, .int]`, and that `.int` is the only type in the iterator
    table that comes from neither the receiver nor the call's arguments. `capIntact` is again
    what makes `s = s + v + i` legal — `s` is captured, reassigned, not retyped. -/
def r216 : Rung :=
  ⟨"lib-array-each-with-index",
    .seq [.vasgn .lvar "s" (.int 0),
          .send (some (.array [.int 10, .int 20])) "each_with_index" []
            (some (.block [.req "v", .req "i"] []
              (.vasgn .lvar "s" (.send (some (.send (some (.var .lvar "s")) "+"
                [.var .lvar "v"] none)) "+" [.var .lvar "i"] none)))),
          .var .lvar "s"],
    .int, [("s", .int)],
    .seq (.cons (.vasgn .intLit)
      (.cons (.iterBlock (.arrayLit (.cons .intLit (.cons .intLit .nil))) .nil
                .eachWithIndex rfl
                (.vasgn (.prim (.prim (.var rfl rfl) (.cons (.var rfl rfl) .nil) .intAdd)
                  (.cons (.var rfl rfl) .nil) .intAdd)) rfl)
        (.last (.var rfl rfl))))⟩

/-! ### Tier 17b — the parameterised `Hash`

§Frontier item A, the widest gap this ladder had recorded: `Hash#fetch` is the slice's most-used
builtin at **62 sites**, and `cvss.rb` reads all seven of its frozen metric tables that way. One
new `Ty` constructor (`hashOf key val`), and it retyped four rungs that had been climbing with
`.any` since tier 5. -/

/-- `h = { "a" => 1 }; h.fetch("a") + h.fetch("b", 0)` → `Integer`.

    **The rung the whole gap was about**, and the interesting half is why `fetch` is more useful
    to a checker than `[]`. `h["a"]` answers `nilable Integer`, because the key may be absent and
    the checker cannot tell. `h.fetch("a")` answers `Integer` — *not* nilable — because a missing
    key raises `KeyError`, which is **outside** the type-stuck family: if the key is absent,
    execution ends there and no claim about the result can be falsified. That is the same
    argument `NameError` gets in tier 13, reused, and it is what makes 62 call sites typeable.

    The two-argument form joins the value type with the default's, because either can come back.

    The type is uniform (`hashOf key val`), not keyed, and `cvss.rb` is the reason: it reads its
    tables as `TABLE.fetch(metric)` with `metric` a *variable*, so a per-key map would answer
    nothing there. What the target needs is "every value in this table is a Float". -/
def r203 : Rung :=
  ⟨"lib-hash-fetch",
    .seq [.vasgn .lvar "h" (.hash [(.str "a", .int 1)]),
          .send (some (.send (some (.var .lvar "h")) "fetch" [.str "a"] none)) "+"
            [.send (some (.var .lvar "h")) "fetch" [.str "b", .int 0] none] none],
    .int, [("h", .hashOf (.cls "String") .int)],
    .seq (.cons (.vasgn (.hashLit (.cons .strLit .intLit .nil)))
      (.last (.prim (.prim (.var rfl rfl) (.cons .strLit .nil) (.hashFetch .cls))
        (.cons (.prim (.var rfl rfl) (.cons .strLit (.cons .intLit .nil))
          (.hashFetchD .cls)) .nil)
        .intAdd)))⟩

/-- `h = { "pkg" => { "name" => "x" } }; h.dig("pkg", "name")` → `T.nilable(String)`.

    A hash **of hashes**, which the new constructor nests for free — `hashOf (cls String)
    (hashOf (cls String) (cls String))` — and `dig`'s two-level row reads the inner value type
    off it. The row has to name the nesting depth in its *type*, so each depth is a separate row;
    the slice writes at most two, so there are two.

    `nilable`, for `[]`'s reason at both levels: either key may be absent. -/
def r204 : Rung :=
  ⟨"lib-hash-dig",
    .seq [.vasgn .lvar "h" (.hash [(.str "pkg", .hash [(.str "name", .str "x")])]),
          .send (some (.var .lvar "h")) "dig" [.str "pkg", .str "name"] none],
    .nilable (.cls "String"),
    [("h", .hashOf (.cls "String") (.hashOf (.cls "String") (.cls "String")))],
    .seq (.cons (.vasgn (.hashLit (.cons .strLit
                                    (.hashLit (.cons .strLit .strLit .nil)) .nil)))
      (.last (.prim (.var rfl rfl) (.cons .strLit (.cons .strLit .nil))
        (.hashDig2 .cls .cls))))⟩

/-- `def opts(**kw); kw["a"].nil? ? 0 : 1; end; opts(a: 1)` → `Integer`.

    A keyword-rest, and tier 17b is what makes the *binding* worth having: `**kw` is
    `hashOf Symbol Integer` — symbol keys because the call site wrote `a: 1`, and the value type
    folded from what was passed, exactly as a hash literal's is. Until then it was the bare
    `.cls "Hash"` and `kw["a"]` could only be `.any`, which `nil?` has no row for.

    The rung reads it with a **String** key on purpose, and it is worth saying why that types:
    `Hash#[]`'s key argument is deliberately *not* required to match the key parameter, because a
    missing key is `nil` in Ruby rather than an error. So `kw["a"]` is `nilable Integer`, `nil?`
    answers `Bool`, and the ternary joins two `Integer`s. At runtime the answer is `0`, which is
    the branch the type says is possible. -/
def r156 : Rung :=
  ⟨"param-kwrest",
    .seq [.def' "opts" [.kwrest (some "kw")]
            (.if' (.send (some (.send (some (.var .lvar "kw")) "[]" [.str "a"] none)) "nil?"
                    [] none)
              (.int 0) (some (.int 1))),
          .send none "opts" [.kwargs [.pair "a" (.int 1)]] none],
    .int, [],
    .seq (.cons .defStmt
      (.last (.callDefKw rfl .nil (.pair .intLit .nil) rfl rfl
        (.if' (.prim (σ := .nilable .int) (.prim (.var rfl rfl) (.cons .strLit .nil)
                       (.hashIndex .cls)) .nil (.nilQuery (.nilable .int)))
          .intLit .intLit rfl))))⟩

/-- `def f(a, b = 2, *rest, c:, d: 4, **kw, &blk); [a, b, rest.length, c, d, kw.length,
    blk.nil?].length; end; f(1, c: 3)` → `Integer`.

    **Every parameter kind at once**, which is why it is the tier's last rung: one required, one
    optional taking its default, a rest taking nothing (`arrayOf .never`), one required keyword
    supplied, one defaulted, a keyword-rest taking nothing (`hashOf Symbol .never`), and a block
    parameter with no block (`.nilT`).

    Read the derivation as a checklist of the four clinks it took: `paramBind` is one walk with
    three entry points (clink 35), the two defaults come from `constLitTy?` licensed by
    `constLitTy?_sound` (clink 33), the rest parameter's `noPositionalParams` side condition is
    satisfied because only keyword/kwrest/block parameters follow it (clink 35 corrected clink
    34's "must be last"), and `**kw` gets a `hashOf` (this clink). `blk.nil?` is the one thing
    that was always free: a `&b` parameter binds `.nilT` when no block is passed, which is
    exactly Ruby.

    The array literal's element type is a union of six `Integer`s and a `Boolean`, which nothing
    consumes — and nothing needs to, because only `length` is taken. -/
def r162 : Rung :=
  ⟨"param-all-kinds",
    .seq [.def' "f" [.req "a", .opt "b" (.int 2), .rest (some "rest"), .key "c" none,
                     .key "d" (some (.int 4)), .kwrest (some "kw"), .block (some "blk")]
            (.send (some (.array [
               .var .lvar "a", .var .lvar "b",
               .send (some (.var .lvar "rest")) "length" [] none,
               .var .lvar "c", .var .lvar "d",
               .send (some (.var .lvar "kw")) "length" [] none,
               .send (some (.var .lvar "blk")) "nil?" [] none])) "length" [] none),
          .send none "f" [.int 1, .kwargs [.pair "c" (.int 3)]] none],
    .int, [],
    .seq (.cons .defStmt
      (.last (.callDefKw rfl (.cons .intLit .nil) (.pair .intLit .nil) rfl rfl
        (.prim (.arrayLit (.cons (.var rfl rfl) (.cons (.var rfl rfl)
          (.cons (.prim (.var rfl rfl) .nil .arrayLength)
            (.cons (.var rfl rfl) (.cons (.var rfl rfl)
              (.cons (.prim (.var rfl rfl) .nil .hashLength)
                (.cons (.prim (.var rfl rfl) .nil (.nilQuery .nilT)) .nil))))))))
          .nil .arrayLength))))⟩

/-- Every rung with a hand-authored derivation, in corpus order. -/
def rungs : List Rung :=
  [r001, r002, r003, r004, r005, r006, r007, r008, r009, r010, r011, r012, r013,
   r014, r015, r016, r017, r019, r020, r021, r022, r024, r025, r026, r027, r028,
   r029, r030, r031, r032, r033, r034,
   r035, r036, r037, r038, r039, r040, r041, r043,
   r044, r045, r046, r047, r048, r049, r050, r051,
   r052, r055, r057, r058, r059, r060,
   r061, r062, r063, r064, r065, r066, r067, r068, r069, r070, r071, r072, r073,
   r074, r075, r076,
   r077, r078, r079, r080, r081, r082, r083, r084, r085, r086,
   r087, r088, r089, r090, r091, r092, r093, r094, r095, r096, r097, r098, r099, r100,
   r101, r102, r103, r104, r105,
   r109, r110, r111, r112, r113, r114,
   r115, r116, r117, r118, r119, r121, r122, r123,
   r125, r126, r127, r128, r129, r130, r131, r132, r134,
   r157, r165, r168, r169, r188, r189, r190, r191,
   r137, r138, r139, r140, r141, r142, r143, r144, r145, r146, r147, r148,
   r150, r152, r153, r154, r155, r156, r161, r162,
   r166, r170, r171, r173, r174, r175, r177, r179, r181, r182,
   r184, r185, r186, r192, r194, r196,
   r200, r203, r204, r205, r207, r209, r210, r211, r212, r215, r216]

/-! ## `chk` answers exactly what was derived by hand

One `rfl` per rung. These are the `Judge ⇒ chk` direction (`chk_sound` is the converse,
and the one that matters for trusting a `true`); together they say the executable checker
and the hand-authored judgment have not drifted apart anywhere on this fragment. -/

-- Raised from the default 512 when tier 13's rungs pushed the list past it. The two `rfl`s
-- below reduce `chk` over *every* rung in one term, so the recursion depth grows with the
-- corpus; it is an elaboration limit and not a soundness knob (it can only turn a proof into
-- an error).
set_option maxRecDepth 8000 in
theorem chk_agrees_with_hand_derivations :
    rungs.all (fun r =>
      chk fuelDefault (ctx0.withBlocks r.program) [] .ivar0 r.program
        == some (r.ty, r.outEnv, Ty.ivar0)) = true := by rfl

set_option maxRecDepth 8000 in
/-- And therefore `validate` — the number the ratchet runner reports — says `true` on every
one of them. Stated separately from the above because it is the weaker fact (it forgets
*which* type), and it is the one `Main.lean` observes. -/
theorem validate_all_rungs : rungs.all (fun r => validate r.program) = true := by
  rfl


end Ratchet
