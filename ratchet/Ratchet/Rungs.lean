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
  deriv : Judge ctx0 [] .ivar0 program ty outEnv .ivar0

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
      (.last (.prim (.var rfl) (.cons .intLit .nil) .intAdd)))⟩

/-- `x = 1; x = 2; x + 3` → `Integer`. Rebinding at the *same* type; the interesting
    sibling is the next rung. -/
def r030 : Rung :=
  ⟨"reassign-same-type",
    .seq [.vasgn .lvar "x" (.int 1), .vasgn .lvar "x" (.int 2),
          .send (some (.var .lvar "x")) "+" [.int 3] none],
    .int, [("x", .int)],
    .seq (.cons (.vasgn .intLit)
      (.cons (.vasgn .intLit)
        (.last (.prim (.var rfl) (.cons .intLit .nil) .intAdd))))⟩

/-- `x = 1; x = true; x` → `Bool`, leaving `x : Bool`. The rung that pins down what a
    Ruby local is: `envSet` overwrites, and **no rule anywhere requires the new type to
    relate to the old one**. A checker that rejected this — or that joined `Int` and
    `Bool` into a union — would be describing a different language. -/
def r031 : Rung :=
  ⟨"reassign-different-type",
    .seq [.vasgn .lvar "x" (.int 1), .vasgn .lvar "x" .tru, .var .lvar "x"],
    .bool, [("x", .bool)],
    .seq (.cons (.vasgn .intLit) (.cons (.vasgn .truLit) (.last (.var rfl))))⟩

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
        (.last (.prim (.var rfl) (.cons (.var rfl) .nil) .intAdd))))⟩

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
      (.cons (.vasgn (.prim (.var rfl) (.cons .intLit .nil) .intAdd))
        (.cons (.vasgn (.prim (.var rfl) (.cons .intLit .nil) .intAdd))
          (.last (.var rfl)))))⟩

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
                (τ₁ := .bool) (τ₂ := .bool) (.var rfl) .flsLit (.var rfl) rfl)))⟩

/-- `false || true` → `Bool`. Same shape, branches swapped. -/
def r017 : Rung :=
  ⟨"bool-or",
    .seq [.vasgn .lvar "__dt_t1" .fls,
          .if' (.var .lvar "__dt_t1") (.var .lvar "__dt_t1") (some .tru)],
    .bool, [("__dt_t1", .bool)],
    .seq (.cons (.vasgn .flsLit)
      (.last (.if' (Γ₁ := [("__dt_t1", .bool)]) (Γ₂ := [("__dt_t1", .bool)])
                (τ₁ := .bool) (τ₂ := .bool) (.var rfl) (.var rfl) .truLit rfl)))⟩

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

/-- `{"a" => 1, "b" => 2}` → `.cls "Hash"`, the unparameterised class type. The keys' and
    values' types (`String`, `Int`) are derived and then discarded: `JudgePairs` carries
    no type in its conclusion, because `Ty` has nowhere to put one. -/
def r048 : Rung :=
  ⟨"hash-lit", .hash [(.str "a", .int 1), (.str "b", .int 2)], .cls "Hash", [],
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

/-- `{"a" => 1}["a"]` → `.any`. The `Ty` gap the corpus records, in its sharpest form:
    `.cls "Hash"` says nothing about what the hash maps to, so the only sound result type
    is the one nothing can consume. The rung validates; a rung that then *used* the
    result (`{"a"=>1}["a"] + 1`) would not, and is a negative control. -/
def r051 : Rung :=
  ⟨"hash-index",
    .send (some (.hash [(.str "a", .int 1)])) "[]" [.str "a"] none,
    .any, [],
    .prim (.hashLit (.cons .strLit .intLit .nil)) (.cons .strLit .nil) .hashIndex⟩

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
        (.prim (.var rfl) (.cons (.var rfl) .nil) .intAdd))))⟩

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
          (.cons (.callDef (.cons (.var rfl) .nil) rfl rfl
                   (.prim (.var rfl) (.cons .intLit .nil) .intAdd)) .nil)
          rfl rfl
          (.prim (.var rfl) (.cons .intLit .nil) .intAdd))))))⟩

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
        (.prim (.prim (.var rfl) (.cons (.var rfl) .nil) .intAdd)
          (.cons (.var rfl) .nil) .intAdd))))⟩

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
        -- `(τs := …)` written out because the element types come from `.var rfl` reads of
        -- the parameter environment, and `elemTy ?τs = arrayOf Int` is not something
        -- unification can invert.
        (.arrayLit (τs := [.int, .int])
          (.cons (.var rfl) (.cons (.var rfl) .nil))))))⟩

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
        (.if' (.prim (.var rfl) (.cons .intLit .nil) .intLe)
          .intLit
          (.prim (.var rfl)
            (.cons (.callAsm
              (.cons (.prim (.var rfl) (.cons .intLit .nil) .intSub) .nil) rfl) .nil)
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
    .seq (.cons (.classStmt rfl)
      (.last (.callMethod
        (.newInst (.constCls rfl) (.cons .intLit (.cons .intLit .nil)) rfl rfl
          (.seq (.cons (.ivarAsgn (.var rfl)) (.last (.ivarAsgn (.var rfl))))))
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
    .seq (.cons (.classStmt rfl)
      (.cons (.vasgn (.newInst (.constCls rfl) (.cons .intLit .nil) rfl rfl
                (.ivarAsgn (.var rfl))))
        (.last (.callMethod (.var rfl) (.cons .intLit .nil) rfl rfl
          (.prim .ivarRead (.cons (.var rfl) .nil) .intAdd)))))⟩

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
    .seq (.cons (.classStmt rfl)
      (.cons (.vasgn (.newInst (.constCls rfl) (.cons .intLit (.cons .intLit .nil))
                rfl rfl
                (.seq (.cons (.ivarAsgn (.var rfl)) (.last (.ivarAsgn (.var rfl)))))))
        (.last (.prim
          (.callMethod (.var rfl) .nil rfl rfl .ivarRead)
          (.cons (.callMethod (.var rfl) .nil rfl rfl .ivarRead) .nil)
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
    .seq (.cons (.classStmt rfl)
      (.last (.callMethod
        (.newInst (.constCls rfl) (.cons .intLit (.cons .intLit .nil)) rfl rfl
          (.seq (.cons (.ivarAsgn (.var rfl)) (.last (.ivarAsgn (.var rfl))))))
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
    .seq (.cons (.classStmt rfl) (.cons (.classStmt rfl)
      (.last (.callMethod (.newInstNoInit (.constCls rfl) .nil rfl rfl)
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
    .seq (.cons (.classStmt rfl)
      (.cons (.vasgn (.newInst (.constCls rfl) (.cons .intLit .nil) rfl rfl
                (.ivarAsgn (.var rfl))))
        (.cons (.vasgn (.newInst (.constCls rfl) (.cons .intLit .nil) rfl rfl
                  (.ivarAsgn (.var rfl))))
          (.last (.prim
            (.callMethod (.var rfl) .nil rfl rfl .ivarRead)
            (.cons (.callMethod (.var rfl) .nil rfl rfl .ivarRead) .nil)
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
    .seq (.cons (.classStmt rfl)
      (.last (.callMethod (.newInstNoInit (.constCls rfl) .nil rfl rfl)
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
    .seq (.cons (.classStmt rfl)
      (.last (.callMethod (.newInstNoInit (.constCls rfl) .nil rfl rfl)
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
    .seq (.cons (.classStmt rfl)
      (.last (.arrayLit
        (τs := [.inst "Point" pointSpine1, .inst "Point" pointSpine1])
        (.cons (.newInst (.constCls rfl) (.cons .intLit .nil) rfl rfl
                 (.ivarAsgn (.var rfl)))
          (.cons (.newInst (.constCls rfl) (.cons .intLit .nil) rfl rfl
                   (.ivarAsgn (.var rfl))) .nil)))))⟩

/-- `{"origin" => Point.new(0)}` → `.cls "Hash"`. The instance's type is derived and then
    discarded, because `Ty` has no `hashOf` (§Ty language gaps) — the same gap tier 5's
    `hash-lit` records, now throwing away something the checker worked harder for. -/
def r072 : Rung :=
  ⟨"class-instance-in-hash",
    .seq [.class' "Point" none
            (.def' "initialize" [.req "x"] (.vasgn .ivar "@x" (.var .lvar "x"))),
          .hash [(.str "origin", .send (some (.const "Point")) "new" [.int 0] none)]],
    .cls "Hash", [],
    .seq (.cons (.classStmt rfl)
      (.last (.hashLit (.cons .strLit
        (.newInst (.constCls rfl) (.cons .intLit .nil) rfl rfl
          (.ivarAsgn (.var rfl))) .nil))))⟩

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
    .seq (.cons (.classStmt rfl)
      (.last (.callMethod
        (.newInst (.constCls rfl) (.cons .intLit .nil) rfl rfl
          (.ivarAsgn (.var rfl)))
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
    .seq (.cons (.classStmt rfl) (.cons .defStmt
      (.last (.callDef
        (.cons (.newInst (.constCls rfl) (.cons .intLit .nil) rfl rfl
                 (.ivarAsgn (.var rfl))) .nil)
        rfl rfl
        (.callMethod (.var rfl) .nil rfl rfl .ivarRead)))))⟩

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
    .seq (.cons (.classStmt rfl)
      (.last (.callMethod
        (.callMethod
          (.newInst (.constCls rfl) (.cons .intLit .nil) rfl rfl
            (.ivarAsgn (.var rfl)))
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
    .seq (.cons (.classStmt rfl) (.cons (.classStmt rfl)
      (.last (.callMethod
        (.newInst (.constCls rfl) (.cons .strLit .nil) rfl rfl (.ivarAsgn (.var rfl)))
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
    .seq (.cons (.classStmt rfl) (.cons (.classStmt rfl)
      (.last (.callMethod
        (.newInst (.constCls rfl) .nil rfl rfl
          (.superCall (.cons .intLit .nil) rfl rfl rfl rfl rfl
            (.ivarAsgn (.var rfl))))
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
    .seq (.cons (.classStmt rfl)
      (.last (.callSMethod (.constCls rfl) .nil rfl rfl
        (.selfNew rfl (.cons .intLit (.cons .intLit .nil)) rfl rfl
          (.seq (.cons (.ivarAsgn (.var rfl)) (.last (.ivarAsgn (.var rfl)))))))))⟩

/-- Every rung with a hand-authored derivation, in corpus order. -/
def rungs : List Rung :=
  [r001, r002, r003, r004, r005, r006, r007, r008, r009, r010, r011, r012, r013,
   r014, r015, r016, r017, r019, r020, r021, r022, r024, r025, r026, r027, r028,
   r029, r030, r031, r032, r033, r034,
   r035, r036, r037, r038, r039, r040, r041, r043,
   r044, r045, r046, r047, r048, r049, r050, r051,
   r052, r055, r057, r058, r059, r060,
   r061, r062, r063, r064, r065, r066, r067, r068, r069, r070, r071, r072, r073,
   r074, r075, r076]

/-! ## `chk` answers exactly what was derived by hand

One `rfl` per rung. These are the `Judge ⇒ chk` direction (`chk_sound` is the converse,
and the one that matters for trusting a `true`); together they say the executable checker
and the hand-authored judgment have not drifted apart anywhere on this fragment. -/

theorem chk_agrees_with_hand_derivations :
    rungs.all (fun r =>
      chk fuelDefault ctx0 [] .ivar0 r.program
        == some (r.ty, r.outEnv, Ty.ivar0)) = true := by rfl

/-- And therefore `validate` — the number the ratchet runner reports — says `true` on all
13. Stated separately from the above because it is the weaker fact (it forgets *which*
type), and it is the one `Main.lean` observes. -/
theorem validate_all_rungs : rungs.all (fun r => validate r.program) = true := by
  rfl

end Ratchet
