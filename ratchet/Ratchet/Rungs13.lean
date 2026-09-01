import Ratchet.Proof.ChkSound

/-!
# The first 13 rungs, typed by hand

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
- `Check13.lean` (the `check13` exe) closes the remaining two gaps that no proof in this
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
semantics is in the comment: the class of the value CRuby produces. `Check13.lean`
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

/-- The 13 rungs, in corpus order. -/
def rungs13 : List Rung :=
  [r001, r002, r003, r004, r005, r006, r007, r008, r009, r010, r011, r012, r013]

/-! ## `chk` answers exactly what was derived by hand

One `rfl` per rung. These are the `Judge ⇒ chk` direction (`chk_sound` is the converse,
and the one that matters for trusting a `true`); together they say the executable checker
and the hand-authored judgment have not drifted apart anywhere on this fragment. -/

theorem chk_agrees_with_hand_derivations :
    rungs13.all (fun r => chk r.program == some r.ty) = true := by rfl

/-- And therefore `validate` — the number the ratchet runner reports — says `true` on all
13. Stated separately from the above because it is the weaker fact (it forgets *which*
type), and it is the one `Main.lean` observes. -/
theorem validate_all_13 : rungs13.all (fun r => validate r.program) = true := by
  rfl

end Ratchet
