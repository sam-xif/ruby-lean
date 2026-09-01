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
  deriv : Judge program ty

/-! ## Tier 1 — the eight literals

Each derivation is a single rule application. What each one asserts about the real
semantics is in the comment: the class of the value CRuby produces. `CheckRungs.lean`
checks that assertion by running `stepFn`. -/

/-- `1` → `Integer`. -/
def r001 : Rung := ⟨"int-lit", .int 1, .int, .intLit⟩
/-- `true` → `TrueClass`, which `Ty.bool` covers (it does not distinguish the two
    boolean classes — see `Judge.truLit`). -/
def r002 : Rung := ⟨"bool-true", .tru, .bool, .truLit⟩
/-- `false` → `FalseClass`, same `Ty.bool`. -/
def r003 : Rung := ⟨"bool-false", .fls, .bool, .flsLit⟩
/-- `"hello"` → an *instance* of `String`, hence `.cls "String"`, not `.clsOf "String"`
    (which would be the class object). -/
def r004 : Rung := ⟨"str-lit", .str "hello", .cls "String", .strLit⟩
/-- `:ok` → `Symbol`. -/
def r005 : Rung := ⟨"sym-lit", .sym "ok", .sym, .symLit⟩
/-- `nil` → `NilClass`. `.nilT`, the singleton — deliberately not `.nilable _`. -/
def r006 : Rung := ⟨"nil-lit", .nil, .nilT, .nilLit⟩
/-- `1.5` → `Float`. The literal's IEEE bits are carried in the syntax and are
    irrelevant to its type. -/
def r007 : Rung := ⟨"flt-lit", .flt (Float.toBits 1.5), .float, .fltLit⟩
/-- `-5` → `Integer`, and note the *syntax*: the desugarer emits `int (-5)`, a single
    negative literal, **not** `send (int 5) "-@" []`. So this rung is `intLit` again, and
    no unary-operator rule is needed to climb it. Worth stating because it is a real fact
    about the desugarer that the hand derivation would get wrong the other way. -/
def r008 : Rung := ⟨"neg-int-lit", .int (-5), .int, .intLit⟩

/-! ## Tier 2 (first five) — arithmetic and string `+` as ordinary sends

`1 + 2` is not special syntax in Ruby and is not special syntax here: the desugarer emits
`send (int 1) "+" [int 2] nil`, and each derivation below is `Judge.prim` over the
receiver's derivation, the argument list's, and one `PrimSig` row. Reading one of these
terms *is* reading the dispatch: receiver type, argument types, signature, result. -/

/-- `1 + 2` → `Integer`. -/
def r009 : Rung :=
  ⟨"add", .send (some (.int 1)) "+" [.int 2] none, .int,
    .prim .intLit (.cons .intLit .nil) .intAdd⟩
/-- `5 - 3` → `Integer`. -/
def r010 : Rung :=
  ⟨"sub", .send (some (.int 5)) "-" [.int 3] none, .int,
    .prim .intLit (.cons .intLit .nil) .intSub⟩
/-- `4 * 3` → `Integer`. -/
def r011 : Rung :=
  ⟨"mul", .send (some (.int 4)) "*" [.int 3] none, .int,
    .prim .intLit (.cons .intLit .nil) .intMul⟩
/-- `10 / 2` → `Integer`. See `PrimSig.intDiv`'s docstring for the one subtlety on this
    rung: the signature does not claim division never raises (`10 / 0` raises
    `ZeroDivisionError`), only that it never reaches the
    `NoMethodError`/`ArgumentError`/`TypeError` family and returns an `Integer`. -/
def r012 : Rung :=
  ⟨"div", .send (some (.int 10)) "/" [.int 2] none, .int,
    .prim .intLit (.cons .intLit .nil) .intDiv⟩
/-- `"a" + "b"` → an instance of `String`. The argument's type matters here in a way it
    does not for the integer rows: `"a" + 1` raises `TypeError`, which is *in* the
    family, so `PrimSig.strAdd` demands `.cls "String"` and nothing weaker. -/
def r013 : Rung :=
  ⟨"str-concat", .send (some (.str "a")) "+" [.str "b"] none, .cls "String",
    .prim .strLit (.cons .strLit .nil) .strAdd⟩

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
    .prim (.prim .intLit (.cons .intLit .nil) .intAdd) (.cons .intLit .nil) .intMul⟩

/-- `3 < 5` → a boolean. The `[.int]` argument type is load-bearing: `3 < "a"` raises
    `ArgumentError`, which is in the type-stuck family. -/
def r014 : Rung :=
  ⟨"cmp-lt", .send (some (.int 3)) "<" [.int 5] none, .bool,
    .prim .intLit (.cons .intLit .nil) .intLt⟩
/-- `1 <= 2` → a boolean. -/
def r024 : Rung :=
  ⟨"cmp-le", .send (some (.int 1)) "<=" [.int 2] none, .bool,
    .prim .intLit (.cons .intLit .nil) .intLe⟩
/-- `1 >= 2` → a boolean (`false`, but the *type* is what is derived). -/
def r025 : Rung :=
  ⟨"cmp-ge", .send (some (.int 1)) ">=" [.int 2] none, .bool,
    .prim .intLit (.cons .intLit .nil) .intGe⟩
/-- `!true` → a boolean. Note the syntax: `!` is not an operator in the `Expr` grammar,
    the desugarer emits `send (tru) "!" []`, so this is `Judge.prim` with an *empty*
    argument list — no new rule shape was needed for a unary operator. -/
def r015 : Rung :=
  ⟨"not-expr", .send (some .tru) "!" [] none, .bool,
    .prim .truLit .nil .notBool⟩
/-- `5.to_s` → an instance of `String`. -/
def r019 : Rung :=
  ⟨"to-s-call", .send (some (.int 5)) "to_s" [] none, .cls "String",
    .prim .intLit .nil .intToS⟩
/-- `5.zero?` → a boolean. Sibling of `unknown-method` (`5.foo_bar_baz`), which is a
    permanent negative: the difference between them is entirely in whether `PrimSig` has
    a row, which is exactly what a hardcoded builtin table is for at this rung. -/
def r022 : Rung :=
  ⟨"unmodeled-builtin-zero-p", .send (some (.int 5)) "zero?" [] none, .bool,
    .prim .intLit .nil .intZeroP⟩
/-- `"abc".length` → an `Integer` — the same nullary-query shape on a different
    receiver class. -/
def r028 : Rung :=
  ⟨"str-length", .send (some (.str "abc")) "length" [] none, .int,
    .prim .strLit .nil .strLength⟩
/-- `1 == 1` → a boolean, by `PrimSig.objEq` with an `Integer` receiver. -/
def r020 : Rung :=
  ⟨"eq-same-type", .send (some (.int 1)) "==" [.int 1] none, .bool,
    .prim .intLit (.cons .intLit .nil) (.objEq .int)⟩
/-- `1 == "a"` → a boolean. The rung that forces `objEq`'s argument to be unconstrained:
    this is safe Ruby answering `false`, and a rule demanding matching operand types
    would reject it for no semantic reason. -/
def r021 : Rung :=
  ⟨"eq-different-type", .send (some (.int 1)) "==" [.str "a"] none, .bool,
    .prim .intLit (.cons .strLit .nil) (.objEq .int)⟩
/-- `nil == nil` → a boolean, receiver `NilClass`. -/
def r026 : Rung :=
  ⟨"nil-eq-nil", .send (some .nil) "==" [.nil] none, .bool,
    .prim .nilLit (.cons .nilLit .nil) (.objEq .nilT)⟩

/-- Every rung with a hand-authored derivation, in corpus order. -/
def rungs : List Rung :=
  [r001, r002, r003, r004, r005, r006, r007, r008, r009, r010, r011, r012, r013,
   r014, r015, r019, r020, r021, r022, r024, r025, r026, r027, r028]

/-! ## `chk` answers exactly what was derived by hand

One `rfl` per rung. These are the `Judge ⇒ chk` direction (`chk_sound` is the converse,
and the one that matters for trusting a `true`); together they say the executable checker
and the hand-authored judgment have not drifted apart anywhere on this fragment. -/

theorem chk_agrees_with_hand_derivations :
    rungs.all (fun r => chk r.program == some r.ty) = true := by rfl

/-- And therefore `validate` — the number the ratchet runner reports — says `true` on all
13. Stated separately from the above because it is the weaker fact (it forgets *which*
type), and it is the one `Main.lean` observes. -/
theorem validate_all_rungs : rungs.all (fun r => validate r.program) = true := by
  rfl

end Ratchet
