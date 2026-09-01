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
  deriv : Judge [] program ty outEnv

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
    (`proc` is also a bare name, and it raises `ArgumentError`). -/
def r032 : Rung :=
  ⟨"bare-undeclared-var", .vcall "x", .any, [], .bareName .x⟩

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
    .if' .truLit .intLit .intLit⟩

/-- `if true then 1 end` (no `else`) → `nilable Int`. The absent branch contributes
    `nil`, and `joinT .int .nilT` is `mkNilable .int`. -/
def r036 : Rung :=
  ⟨"if-no-else", .if' .tru (.int 1) none, .nilable .int, [],
    .ifNoElse .truLit .intLit⟩

/-- `if 5 then 1 else 2` → `Integer`. The rung that pins the condition being
    unconstrained: `5` is a perfectly good Ruby condition (only `nil`/`false` are falsy)
    and `Judge.if'` never looks at `σ`. -/
def r037 : Rung :=
  ⟨"if-condition-not-bool", .if' (.int 5) (.int 1) (some (.int 2)), .int, [],
    .if' .intLit .intLit .intLit⟩

/-- `if true then 1 else "a"` → `union(Int, String)`. The first type in this package that
    is not the type of any single value: `Ty.union` was in the grammar and inert, and
    this is the rung that makes `joinT` produce one instead of giving up. -/
def r038 : Rung :=
  ⟨"if-branch-mismatch", .if' .tru (.int 1) (some (.str "a")),
    .union .int (.cls "String"), [],
    .if' .truLit .intLit .strLit⟩

/-- `if true then 1 elsif false then 2 else "a"` → `union(Int, String)`, **not**
    `union(Int, union(Int, String))`. `elsif` is nested `if'`, so the outer join sees
    `Int` against the inner union; the answer is only the smaller type because `joinT`
    flattens and dedups. This rung is why it does. -/
def r039 : Rung :=
  ⟨"elsif-chain-mismatch",
    .if' .tru (.int 1) (some (.if' .fls (.int 2) (some (.str "a")))),
    .union .int (.cls "String"), [],
    .if' .truLit .intLit (.if' .flsLit .intLit .strLit)⟩

/-- `if nil then 1 else 2` → `Integer`. `nil` is falsy, never a type error. -/
def r040 : Rung :=
  ⟨"if-nil-condition", .if' .nil (.int 1) (some (.int 2)), .int, [],
    .if' .nilLit .intLit .intLit⟩

/-- A nested `if` in the then-branch → `Integer`. -/
def r041 : Rung :=
  ⟨"nested-if",
    .if' .tru (.if' .fls (.int 1) (some (.int 2))) (some (.int 3)), .int, [],
    .if' .truLit (.if' .flsLit .intLit .intLit) .intLit⟩

/-- `if true then 1 elsif false then 2 else 3` → `Integer`: the uniform three-way
    chain, joining twice. -/
def r043 : Rung :=
  ⟨"elsif-chain",
    .if' .tru (.int 1) (some (.if' .fls (.int 2) (some (.int 3)))), .int, [],
    .if' .truLit .intLit (.if' .flsLit .intLit .intLit)⟩

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
                (τ₁ := .bool) (τ₂ := .bool) (.var rfl) .flsLit (.var rfl))))⟩

/-- `false || true` → `Bool`. Same shape, branches swapped. -/
def r017 : Rung :=
  ⟨"bool-or",
    .seq [.vasgn .lvar "__dt_t1" .fls,
          .if' (.var .lvar "__dt_t1") (.var .lvar "__dt_t1") (some .tru)],
    .bool, [("__dt_t1", .bool)],
    .seq (.cons (.vasgn .flsLit)
      (.last (.if' (Γ₁ := [("__dt_t1", .bool)]) (Γ₂ := [("__dt_t1", .bool)])
                (τ₁ := .bool) (τ₂ := .bool) (.var rfl) (.var rfl) .truLit)))⟩

/-- Every rung with a hand-authored derivation, in corpus order. -/
def rungs : List Rung :=
  [r001, r002, r003, r004, r005, r006, r007, r008, r009, r010, r011, r012, r013,
   r014, r015, r016, r017, r019, r020, r021, r022, r024, r025, r026, r027, r028,
   r029, r030, r031, r032, r033, r034,
   r035, r036, r037, r038, r039, r040, r041, r043]

/-! ## `chk` answers exactly what was derived by hand

One `rfl` per rung. These are the `Judge ⇒ chk` direction (`chk_sound` is the converse,
and the one that matters for trusting a `true`); together they say the executable checker
and the hand-authored judgment have not drifted apart anywhere on this fragment. -/

theorem chk_agrees_with_hand_derivations :
    rungs.all (fun r => chk [] r.program == some (r.ty, r.outEnv)) = true := by rfl

/-- And therefore `validate` — the number the ratchet runner reports — says `true` on all
13. Stated separately from the above because it is the weaker fact (it forgets *which*
type), and it is the one `Main.lean` observes. -/
theorem validate_all_rungs : rungs.all (fun r => validate r.program) = true := by
  rfl

end Ratchet
