import Ratchet.Corpus
import Ratchet.Rungs
import Semantics.Interp

/-!
# `checkrungs` — pinning the hand-authored derivations to reality

`Ratchet/Rungs.lean` proves that the hand-written `Judge` derivations typecheck and that
`chk` agrees with each. Neither of those facts, on its own, rules out the two ways a
hand-authored judgment can be confidently wrong:

1. **The syntax could be a fiction.** A derivation about `send (int 1) "+" [int 2] nil`
   says nothing about the rung if the desugarer actually emits something else for
   `1 + 2`. So: decode each rung's committed `corpus/*.json` with the real
   `Ratchet.Decode.program` and compare it to the hand-written `Expr` with `==`.
2. **The types could be a fiction.** `Judge` says `1 + 2 : Int` and `"a" + "b" :
   String`; that is an assertion about what the semantics *does*. So: decode the same
   JSON a second time with the real `RubyCore.Decode.program`, run it under the real
   `stepFn` from the real booted heap, and check the value's actual class is one the
   claimed `Ty` names — and that the run is not type-stuck.

This is the one file in the package allowed to see both sides (`Ratchet/`'s copied type
language and `../lean/RubyCore`'s semantics); see `Semantics/Interp.lean`'s docstring for
why the boundary is drawn that way. It is a separate executable from `ratchet` on
purpose: the ratchet's headline number stays a pure statement about `validate`, and this
is the evidence behind the rungs it now counts.
-/

open Ratchet
open Lean (Json)

/-- The runtime class names a `Ty` admits — the bridge between the two languages, and
the only place a `Ty` is given an extensional reading in this package.

`.bool` maps to *both* boolean classes because `Ty` does not distinguish them
(`Judge.truLit`). Only the constructors the climbed rungs use are listed; anything else
returns `[]`, which fails loudly rather than passing vacuously. -/
def expectedClasses : Ty → List String
  | .int => ["Integer"]
  | .float => ["Float"]
  | .sym => ["Symbol"]
  | .nilT => ["NilClass"]
  | .bool => ["TrueClass", "FalseClass"]
  | .cls n => [n]
  -- Tier 4's joins produce types that admit more than one class, and the reading is
  -- exactly the obvious one: a `nilable` also admits `nil`, a `union` admits either
  -- side's classes. This is the point at which a `Ty` stops naming *the* class of the
  -- value and starts naming a *set* it belongs to (see `Ty.joinT`'s docstring), so the
  -- cross-check gets correspondingly weaker for these rungs -- deliberately, and
  -- visibly: the rung still fails if the class produced is outside the set.
  | .nilable τ => "NilClass" :: expectedClasses τ
  | .union σ τ => expectedClasses σ ++ expectedClasses τ
  -- Tier 5: an array literal's value is an `Array` whatever its element type is. The
  -- element type itself is *not* cross-checked against the semantics here — this harness
  -- compares the class of the whole result value, and nothing in it inspects an array's
  -- contents. What backs the element type instead is `arrayLit`'s premise: each element
  -- has its own derivation, and each of those would be a row here if it were a rung.
  | .arrayOf _ => ["Array"]
  -- Tier 9: a callable value is a `Proc` whether it came from `lambda` or `proc` (a lambda
  -- *is* a Proc, with `lambda? == true`). The block index and captured spine inside the type
  -- are not cross-checked here, for the same reason an array's element type is not: this
  -- harness compares the class of the result value. What backs them is that every rung whose
  -- type depends on them (`lambda-closure-capture`, `lambda-returns-lambda`) *calls* the
  -- closure, so a wrong index or a wrong capture shows up as a wrong result class there.
  | .clos _ _ => ["Proc"]
  -- Tier 7: a user-class instance's class is its name. The *ivar spine* is not
  -- cross-checked against the semantics here — this harness compares the class of the
  -- result value and nothing in it reaches inside an object. What backs the spine instead
  -- is that every rung whose type *depends* on it (`class-basic`'s `Integer`,
  -- `class-ivar-lazy-nil`'s `NilClass`) reads an ivar out through a method call, so a wrong
  -- spine shows up as a wrong result class on that rung.
  | .inst n _ => [n]
  | _ => []

/-- Fuel: these are small literal/arithmetic programs; a few hundred steps is already
generous, and `outOfFuel` is reported as a failure rather than silently passing. -/
def fuel : Nat := 20000

structure Row where
  id : String
  syntaxOk : Bool
  claimedTy : Ty
  outcome : String
  actualClass : Option String
  typeStuck : Bool
  semOk : Bool

def rowOk (r : Row) : Bool := r.syntaxOk && r.semOk && !r.typeStuck

def loadJson (p : System.FilePath) : IO Json := do
  match Json.parse (← IO.FS.readFile p) with
  | .error e => throw (IO.userError s!"{p}: JSON parse error: {e}")
  | .ok j => pure j

def checkRung (corpusDir : System.FilePath) (files : List System.FilePath)
    (r : Rung) : IO Row := do
  -- Find this rung's file by its recorded `id`, not by filename arithmetic.
  let mut found : Option Json := none
  for f in files do
    let j ← loadJson f
    match j.getObjValAs? String "id" with
    | .ok id => if id == r.id then found := some j
    | .error _ => pure ()
  let some j := found
    | throw (IO.userError s!"no corpus entry with id '{r.id}' under {corpusDir}")

  -- (1) syntax: does the real desugarer output decode to the hand-written `Expr`?
  let entry ← match CorpusEntry.ofJson? j with
    | .error e => throw (IO.userError s!"{r.id}: {e}")
    | .ok e => pure e
  let syntaxOk := entry.program == r.program

  -- (2) semantics: decode the same JSON into the real `RubyCore.Expr` and run it.
  let rp ← match RubyCore.Decode.program (← match j.getObjVal? "program" with
      | .error e => throw (IO.userError s!"{r.id}: missing program: {e}")
      | .ok p => pure p) with
    | .error e => throw (IO.userError s!"{r.id}: RubyCore decode: {e}")
    | .ok p => pure p
  let res := Ratchet.Semantics.run fuel rp
  let actualClass := Ratchet.Semantics.resultClassName res
  let stuck := Ratchet.Semantics.typeStuck res
  -- `.any` is the one type with no extensional content: it names no class, so the only
  -- thing left to check about a run is that it did not go type-stuck (which is checked
  -- separately, by `rowOk`). Today exactly one rung derives it —
  -- `bare-undeclared-var`, which raises `NameError` and so produces no value at all —
  -- and a rung that claimed `.any` for a program that *does* return a value would be
  -- passing here vacuously. That is the honest cost of `.any` being in the grammar; it
  -- is flagged in the report as `claims .any` rather than shown as a class match.
  let semOk := if r.ty == .any then true else match actualClass with
    | some cn => (expectedClasses r.ty).contains cn
    | none => false
  return { id := r.id, syntaxOk, claimedTy := r.ty
           outcome := Ratchet.Semantics.outcomeLabel res
           actualClass, typeStuck := stuck, semOk }

/-! ## Negative controls for `PrimSig`

Confirming the climbed rungs pass says nothing about whether `PrimSig`'s five rows are too
*generous* — a table with `PrimSig.intAdd : PrimSig .int "+" [.any] .int` would also pass
them all. These controls are the other side: neighbours of the rungs, one syntactic step
away, that `chk` must **not** certify. Each is hand-written syntax (not a corpus rung) —
that is the point, since what is being probed is the table's argument types, and it is
run under the real semantics to say which kind of rejection it is:

- **sound rejection** — the program really is type-stuck, so rejecting it is required.
- **conservative rejection** — the program is safe and `chk` still says no. Honest
  incompleteness, recorded rather than hidden: `1 + 1.5` is fine Ruby, and `PrimSig` has
  no `Integer#+ Float` row because no rung has needed one yet.

`BareNameError` gets the controls that matter most on this ladder, because the rule it
gates is the one a careless reading would state as a blanket "a bare name raises
NameError, which is not a type error". `proc` and `lambda` are bare names that resolve
to real `Kernel` methods and raise **ArgumentError** with no block — squarely in the
type-stuck family — so they are sound rejections that only the table's narrowness earns.
`y` is the other side: genuinely unbound and therefore safe, rejected purely because
nobody has added its row.

Note what the model says about `proc`/`lambda` versus what CRuby does. CRuby raises
`ArgumentError` ("tried to create Proc object without a block") — verified directly, and
that is the fact the narrowness of `BareNameError` is justified against. `RubyCore` does
not model the block-less form at all and answers `unsupported`, which is neither safe
nor stuck, so these two controls print the "model declined" verdict rather than a
soundness claim. They still do their job: the blanket rule is refuted by Ruby, and the
model's silence is not evidence for it.

The tier-2 rows added alongside `objEq` each get a control of the same kind: `1 < "a"`
and `1.length` and `nil.zero?` probe the receiver/argument constraints of the comparison
and nullary-query rows (all three genuinely raise), while `!nil`, `"a" < "b"` and
`5.to_s(2)` are the conservative side — safe Ruby whose signature is deliberately not in
the table. `PrimSig.objEq` has no *sound-rejection* control at all, and that is not an
oversight: `==` really is total on every receiver `EqSafe` admits, so there is no
neighbouring `==` program in this fragment that raises. What constrains it is `EqSafe`
itself, and the only way to violate that is with a `Ty` (`.any`, an arrow) no expression
in this fragment synthesizes.

The check fails only on a `validate = true` here; a conservative rejection is expected. -/
structure Control where
  label : String
  program : Expr

def controls : List Control :=
  [ ⟨"1 + true", .send (some (.int 1)) "+" [.tru] none⟩
  , ⟨"1 + \"a\"", .send (some (.int 1)) "+" [.str "a"] none⟩
  , ⟨"\"a\" + 1", .send (some (.str "a")) "+" [.int 1] none⟩
  , ⟨"1 + nil", .send (some (.int 1)) "+" [.nil] none⟩
  , ⟨"1 + 1.5 (safe; no PrimSig row)", .send (some (.int 1)) "+" [.flt (Float.toBits 1.5)] none⟩
  , ⟨"1.5 + 1 (safe; no PrimSig row)", .send (some (.flt (Float.toBits 1.5))) "+" [.int 1] none⟩
  , ⟨"1 < \"a\"", .send (some (.int 1)) "<" [.str "a"] none⟩
  , ⟨"1.length", .send (some (.int 1)) "length" [] none⟩
  , ⟨"nil.zero?", .send (some .nil) "zero?" [] none⟩
  , ⟨"!nil (safe; no PrimSig row)", .send (some .nil) "!" [] none⟩
  , ⟨"\"a\" < \"b\" (safe; no PrimSig row)", .send (some (.str "a")) "<" [.str "b"] none⟩
  , ⟨"5.to_s(2) (safe; no PrimSig row for the base form)",
      .send (some (.int 5)) "to_s" [.int 2] none⟩
  , ⟨"proc (a bare name that is NOT unbound)", .vcall "proc"⟩
  , ⟨"lambda (likewise)", .vcall "lambda"⟩
  , ⟨"y (safe; unbound, but not a BareNameError row)", .vcall "y"⟩
    -- The environment-join control: the same shape as
    -- `corpus/042-if-does-not-leak-reassignment`, kept here as well because this is
    -- where a rejection is labelled *sound* by actually running the program. An `if`
    -- rule that carried the pre-`if` environment forward would certify this.
  , ⟨"x = 1; if true then x = \"hello\" end; x + 1",
      .seq [.vasgn .lvar "x" (.int 1),
            .if' .tru (.vasgn .lvar "x" (.str "hello")) none,
            .send (some (.var .lvar "x")) "+" [.int 1] none]⟩
    -- ### Tier 5's controls
    --
    -- One per new `PrimSig` row, plus the two places tier 5's honest imprecision shows.
    -- The first is the only *unsound*-if-admitted one; the rest are safe programs this
    -- checker declines, and they are here so the cost is a recorded number rather than a
    -- surprise.
    -- `arrayIndex`'s `[.int]` argument is load-bearing: a String subscript raises
    -- TypeError, inside the family.
  , ⟨"[1,2,3][\"a\"]",
      .send (some (.array [.int 1, .int 2, .int 3])) "[]" [.str "a"] none⟩
    -- `nilable` is the price of not tracking lengths: this is safe Ruby (`2`) that the
    -- checker cannot type, because `nilable Int` matches no arithmetic row.
  , ⟨"[1,2,3][0] + 1 (safe; nilable result matches no PrimSig row)",
      .send (some (.send (some (.array [.int 1, .int 2, .int 3])) "[]" [.int 0] none))
        "+" [.int 1] none⟩
    -- The `Ty` gap in `hash-lit`/`hashIndex`, cashed out: safe Ruby (`2`), untypeable
    -- because `.any` is inert by design.
  , ⟨"{\"a\"=>1}[\"a\"] + 1 (safe; .any result is inert)",
      .send (some (.send (some (.hash [(.str "a", .int 1)])) "[]" [.str "a"] none))
        "+" [.int 1] none⟩
    -- And the element-union's price: safe Ruby (`2`), rejected because the array's
    -- element type is a union.
  , ⟨"[1,\"a\"][0] + 1 (safe; element type is a union)",
      .send (some (.send (some (.array [.int 1, .str "a"])) "[]" [.int 0] none))
        "+" [.int 1] none⟩
    -- ### Tier 6's controls
    --
    -- The first two are the two places tier 6 could have been *unsound*, and each one
    -- corresponds to a specific premise added this clink. They are the reason those
    -- premises are not decoration.
    -- (a) `Judge.callDef`'s second pass. `def f(x) = if x <= 0 then 1 else f(x-1) + true`
    -- really raises TypeError: the recursion bottoms out, returns 1, and `1 + true` runs.
    -- The *first* pass alone accepts it — the recursive call typed at `.never` makes the
    -- whole `else` branch `.never`, which the join then discards, leaving `Int`. Only
    -- re-running the body with `Int` assumed exposes `Int + true`.
  , ⟨"def f(x) = if x<=0 then 1 else f(x-1)+true; f(1)",
      .seq [.def' "f" [.req "x"]
              (.if' (.send (some (.var .lvar "x")) "<=" [.int 0] none)
                (.int 1)
                (some (.send
                  (some (.send none "f"
                    [.send (some (.var .lvar "x")) "-" [.int 1] none] none))
                  "+" [.tru] none))),
            .send none "f" [.int 1] none]⟩
    -- (b) `Judge.bareName`'s `defGet? D m = none` premise. Without it this takes the
    -- `BareNameError "x"` route to `.any` and validates a program that raises TypeError.
  , ⟨"def x; 1 + true; end; x",
      .seq [.def' "x" [] (.send (some (.int 1)) "+" [.tru] none), .vcall "x"]⟩
    -- (c) Per-call-site instantiation, from the failing side: the same `def` is fine at
    -- Int and stuck at String, and only the call site decides which.
  , ⟨"def f(x) = x + 1; f(\"a\")",
      .seq [.def' "f" [.req "x"] (.send (some (.var .lvar "x")) "+" [.int 1] none),
            .send none "f" [.str "a"] none]⟩
    -- (d) `paramEnv`'s required-parameters-only restriction, measured: safe Ruby the
    -- checker declines because `Param.opt` answers `none` (AGENTS.md §Frontier item 3).
  , ⟨"def f(x = 1); x; end; f() (safe; optional param unsupported)",
      .seq [.def' "f" [.opt "x" (.int 1)] (.var .lvar "x"),
            .send none "f" [] none]⟩
    -- ### Tier 7's controls
    --
    -- (a) **The control for `Judge.callMethod`'s no-retyping premise**, and the most
    -- important one in this file. `set` stores a String into an ivar the caller's type says
    -- is an Integer; afterwards `c.get + 1` really raises TypeError. Without the premise the
    -- caller keeps its stale `.inst C {@x: Int}`, `c.get` answers Int, and the whole thing
    -- validates. This is also, transitively, the control for `ivarRead`'s `nil` default:
    -- that default is sound only because a spine records *every* ivar the object will ever
    -- have, which is precisely what the premise buys.
  , ⟨"class C; @x=x; def set; @x=\"s\"; end; …; c.set; c.get + 1",
      .seq [.class' "C" none (.seq [
              .def' "initialize" [.req "x"] (.vasgn .ivar "@x" (.var .lvar "x")),
              .def' "set" [] (.vasgn .ivar "@x" (.str "s")),
              .def' "get" [] (.var .ivar "@x")]),
            .vasgn .lvar "c" (.send (some (.const "C")) "new" [.int 1] none),
            .send (some (.var .lvar "c")) "set" [] none,
            .send (some (.send (some (.var .lvar "c")) "get" [] none)) "+"
              [.int 1] none]⟩
    -- (b) `newInstNoInit`'s `argTys = []` premise: `Object#new` inherited unchanged takes no
    -- arguments, and passing one raises ArgumentError — inside the family.
  , ⟨"class G; def hi; \"hi\"; end; end; G.new(1)",
      .seq [.class' "G" none (.def' "hi" [] (.str "hi")),
            .send (some (.const "G")) "new" [.int 1] none]⟩
    -- (c) `bareName`'s `κ.selfTy = none` premise, the tier-7 twin of tier 6's `defGet?`
    -- one. `x` is the single `BareNameError` row, and here it is also a method of `self`
    -- with a type-stuck body; the program raises TypeError. Without the premise the `vcall`
    -- inside `go` would take the bare-name route to `.any` and validate.
  , ⟨"class C; def x; 1 + true; end; def go; x; end; end; C.new.go",
      .seq [.class' "C" none (.seq [
              .def' "x" [] (.send (some (.int 1)) "+" [.tru] none),
              .def' "go" [] (.vcall "x")]),
            .send (some (.send (some (.const "C")) "new" [] none)) "go" [] none]⟩
    -- (d) The same premise's *conservative* cost, measured: a method that lazily creates an
    -- ivar the constructor never set is perfectly safe Ruby (this returns 1) and is
    -- rejected, because its outgoing spine is longer than its incoming one.
  , ⟨"class C; def set; @y = 1; end; def get; @y; end; end; c = C.new; c.set; c.get "
      ++ "(safe; a method may not add an ivar)",
      .seq [.class' "C" none (.seq [
              .def' "set" [] (.vasgn .ivar "@y" (.int 1)),
              .def' "get" [] (.var .ivar "@y")]),
            .vasgn .lvar "c" (.send (some (.const "C")) "new" [] none),
            .send (some (.var .lvar "c")) "set" [] none,
            .send (some (.var .lvar "c")) "get" [] none]⟩
    -- (e) `constCls`'s "declared classes only": an undeclared constant. Runs to a
    -- NameError, which is *outside* the family (like `bare-undeclared-var`), so the harness
    -- reports this as a conservative rejection of a program that nevertheless crashes —
    -- the same distinction `PrimSig.intDiv` established.
  , ⟨"Undeclared.new (no class statement)",
      .send (some (.const "Undeclared")) "new" [] none⟩
    -- ### Tier 7's hierarchy controls
    --
    -- (f) The walk is not a licence: a method neither the class nor any ancestor declares
    -- still raises NoMethodError. This is the control for `mroGet?` *terminating* in `none`
    -- rather than falling back on anything.
  , ⟨"class A; end; class B < A; end; B.new.nope",
      .seq [.class' "A" none .nil,
            .class' "B" (some (.const "A")) .nil,
            .send (some (.send (some (.const "B")) "new" [] none)) "nope" [] none]⟩
    -- (g) `super` walks from the *definition site*, and the parent's body is checked there:
    -- Child#go delegates to Parent#go, whose body is type-stuck, so the program raises
    -- TypeError even though nothing at the call site looks wrong. The tier-7 twin of
    -- `fun-body-mismatch`.
  , ⟨"class P; def go; 1 + true; end; end; class C < P; def go; super; end; end; C.new.go",
      .seq [.class' "P" none (.def' "go" [] (.send (some (.int 1)) "+" [.tru] none)),
            .class' "C" (some (.const "P")) (.def' "go" [] (.super' [] none)),
            .send (some (.send (some (.const "C")) "new" [] none)) "go" [] none]⟩
    -- (h) `super` with no superclass: `Judge.superCall`'s `c.super? = some sn` premise.
    -- Ruby raises NoMethodError ("super: no superclass method"), inside the family.
  , ⟨"class A; def go; super; end; end; A.new.go",
      .seq [.class' "A" none (.def' "go" [] (.super' [] none)),
            .send (some (.send (some (.const "A")) "new" [] none)) "go" [] none]⟩
    -- (i) A singleton method is *not* an instance method, and the two tables really are
    -- separate: calling one on an instance raises NoMethodError.
  , ⟨"class P; def self.origin; 1; end; end; P.new.origin",
      .seq [.class' "P" none (.defs .self' "origin" [] (.int 1)),
            .send (some (.send (some (.const "P")) "new" [] none)) "origin" [] none]⟩
    -- ### Tier 8's controls
    --
    -- (j) **`Cls.isModule`, the reason it exists.** A module cannot be allocated: `M.new`
    -- raises NoMethodError. Without the flag `M.new` would find no `initialize`, fall
    -- through to the zero-argument allocator, and certify this. No rung writes `new` on a
    -- module, so this control is the only thing holding the guard in place.
  , ⟨"module M; def self.foo; 1; end; end; M.new",
      .seq [.module' "M" (.defs .self' "foo" [] (.int 1)),
            .send (some (.const "M")) "new" [] none]⟩
    -- (k) A module's *instance* methods are recorded and unreachable: `M.foo` for a plain
    -- `def foo` raises NoMethodError, because the two method tables are separate. Reaching
    -- them needs `include`/`extend`/`module_function`, none of which has a rule.
  , ⟨"module M; def foo; 1; end; end; M.foo",
      .seq [.module' "M" (.def' "foo" [] (.int 1)),
            .send (some (.const "M")) "foo" [] none]⟩
    -- (l) And the body of a module method is checked at its call site like any other:
    -- nothing at the call site looks wrong here, and the program raises TypeError.
  , ⟨"module M; def self.bad(x); x + true; end; end; M.bad(1)",
      .seq [.module' "M" (.defs .self' "bad" [.req "x"]
              (.send (some (.var .lvar "x")) "+" [.tru] none)),
            .send (some (.const "M")) "bad" [.int 1] none]⟩
    -- ### Tier 9a's controls
    --
    -- (m) A lambda's body is checked at its call site, so a body that is stuck *for these*
    -- arguments is caught -- the `closCall` twin of `fun-body-mismatch`. The lambda literal
    -- itself says nothing about `x`.
    --
    -- Its counterpart is deliberately *not* in this list, because it is a program the checker
    -- is right to certify: `lambda { |x| x + true }` with no call validates, and should, since
    -- it merely evaluates to a Proc. A body is an obligation of its *call sites*, so a method
    -- or lambda nobody invokes cannot make a program type-stuck. That has been true since
    -- `Judge.defStmt` (clink 5) and it is the same fact here.
  , ⟨"lambda { |x| x + true }.call(1)",
      .send (some (.send none "lambda" []
        (some (.block [.req "x"] [] (.send (some (.var .lvar "x")) "+" [.tru] none)))))
        "call" [.int 1] none⟩
    -- (n) Arity is checked strictly, via `paramEnv`: too *few* arguments to a lambda raises
    -- ArgumentError. (Too many is the corpus rung `lambda-arity-mismatch`; the same shape on
    -- a `proc` is legal Ruby and is the recorded `ty_language_gap`.)
  , ⟨"lambda { |x, y| x }.call(1)",
      .send (some (.send none "lambda" []
        (some (.block [.req "x", .req "y"] [] (.var .lvar "x")))))
        "call" [.int 1] none⟩
    -- (o) A `.clos` is inert to everything but `call`/`[]`: no PrimSig row takes one and it
    -- is not EqSafe. Safe Ruby (a Proc really has `#arity`) that the checker declines.
  , ⟨"lambda { 1 }.arity (safe; no rule for Proc#arity)",
      .send (some (.send none "lambda" [] (some (.block [] [] (.int 1))))) "arity" [] none⟩
    -- ### Tier 9b's controls
    --
    -- (p) `yield` needs `Ctx.blockTy`, which only `callDefBlk` sets. A method that yields but
    -- was called *without* a block raises LocalJumpError -- and note that is *outside* the
    -- NoMethodError/ArgumentError/TypeError family, so this is a conservative rejection of a
    -- program that nevertheless crashes, exactly like `bare-undeclared-var`'s NameError.
  , ⟨"def t; yield(1); end; t (safe by this ladder; LocalJumpError)",
      .seq [.def' "t" [] (.yield' [.int 1]), .send none "t" [] none]⟩
    -- (q) The block's body is checked at each `yield`, at that yield's argument types. This
    -- one really raises TypeError, and nothing at the call site or in the method looks wrong
    -- -- the `yieldExpr` twin of `fun-body-mismatch`.
  , ⟨"def t; yield(\"a\"); end; t { |x| x + 1 }",
      .seq [.def' "t" [] (.yield' [.str "a"]),
            .send none "t" []
              (some (.block [.req "x"] []
                (.send (some (.var .lvar "x")) "+" [.int 1] none)))]⟩
    -- (r) `paramEnvB` binds a `&b` parameter to `.nilT` when no block is passed, which is
    -- what Ruby does -- and then `b.call` raises NoMethodError on nil. So the binding is not
    -- a formality: without it `b` would be unbound and this would fail for the wrong reason.
  , ⟨"def run(&b); b.call(5); end; run",
      .seq [.def' "run" [.block (some "b")]
              (.send (some (.var .lvar "b")) "call" [.int 5] none),
            .send none "run" [] none]⟩
    -- (s) `bodyResult` reads a `return` only as a lambda's *entire* body. A `return` inside a
    -- sequence has no rule, which is the point: typing `.ret e` as `e`'s type would make this
    -- validate at Int, and it really returns a String.
  , ⟨"lambda { |x| return \"a\"; 2 }.call(1) + 1 (unsound if `.ret` had a rule)",
      .send (some (.send (some (.send none "lambda" []
        (some (.block [.req "x"] []
          (.seq [.ret (some (.str "a")), .int 2])))))
        "call" [.int 1] none)) "+" [.int 1] none⟩
    -- ### Tier 12's controls
    --
    -- Narrowing is the first capability on this ladder whose *most likely bug is a swap*, so
    -- three of these five are the same program with a polarity reversed. Each of the three is
    -- certified by an implementation that gets one refinement backwards, and each really
    -- raises. Note `a = []` throughout: the empty array is what makes the `nil` branch the one
    -- that actually runs, so the semantics labels these `stuck` rather than merely "rejected".
    --
    -- (t) `truthy`/`falsy` swapped. `x` is `nil`, the condition is falsy, the else-branch runs
    -- and `nil + 1` raises NoMethodError. Sound only because `falsyTy` puts `nilT` — not
    -- `truthyTy`'s `Int` — into the else-branch's environment.
  , ⟨"a = []; x = a[0]; if x then 0 else x + 1 end",
      .seq [.vasgn .lvar "a" (.array []),
            .vasgn .lvar "x" (.send (some (.var .lvar "a")) "[]" [.int 0] none),
            .if' (.var .lvar "x") (.int 0)
              (some (.send (some (.var .lvar "x")) "+" [.int 1] none))]⟩
    -- (u) `isNil`/`nonNil` swapped — the `nil?` twin of (t), and the more tempting mistake,
    -- because "the guard is true, so we are in the good case" is the reading every
    -- `if x.nil?`-free codebase trains. `nil?` answering true means `x` **is** nil.
  , ⟨"a = []; x = a[0]; if x.nil? then x + 1 else 0 end",
      .seq [.vasgn .lvar "a" (.array []),
            .vasgn .lvar "x" (.send (some (.var .lvar "a")) "[]" [.int 0] none),
            .if' (.send (some (.var .lvar "x")) "nil?" [] none)
              (.send (some (.var .lvar "x")) "+" [.int 1] none)
              (some (.int 0))]⟩
    -- (v) No guard at all — `corpus/136-narrow-absent-unsafe`, kept here too because this is
    -- where a rejection gets labelled by *running* the program. Catches any rule that lets a
    -- `nilable T` receiver reach a `T` row.
  , ⟨"a = []; x = a[0]; x + 1",
      .seq [.vasgn .lvar "a" (.array []),
            .vasgn .lvar "x" (.send (some (.var .lvar "a")) "[]" [.int 0] none),
            .send (some (.var .lvar "x")) "+" [.int 1] none]⟩
    -- (w) **The control that makes `NilQSafe` load-bearing.** `nil?` is total on every object
    -- in the standard library, so the honest `PrimSig` row wants a wildcard receiver — and a
    -- wildcard receiver in this type language also covers instances of classes the *program*
    -- declared, which may override `nil?` with anything at all. Here `Dog#nil?` raises
    -- TypeError, and `nilable (inst Dog)` is a type this checker really produces (index an
    -- array of Dogs). `NilQSafe.nilable` requires its payload to be safe, and `.inst` is not
    -- admitted, so the condition is untypeable and the program is rejected.
  , ⟨"class Dog; def nil?; 1 + \"a\"; end; end; x = [Dog.new][0]; if x.nil? then 0 else 1 end",
      .seq [.class' "Dog" none (.def' "nil?" [] (.send (some (.int 1)) "+" [.str "a"] none)),
            .vasgn .lvar "x"
              (.send (some (.array [.send (some (.const "Dog")) "new" [] none])) "[]"
                [.int 0] none),
            .if' (.send (some (.var .lvar "x")) "nil?" [] none) (.int 0) (some (.int 1))]⟩
    -- (x) What that guard costs, as a recorded number: the same shape with an *ordinary* Dog.
    -- Perfectly safe Ruby, conservatively declined, because nothing in this judgment looks at
    -- whether the declared class actually overrides `nil?`. The precise version is a
    -- `NilQSafe` premise that consults `κ.classes`; no rung needs it.
  , ⟨"class Dog; def bark; 1; end; end; x = [Dog.new][0]; if x.nil? then 0 else 1 end"
      ++ " (safe; NilQSafe excludes a declared class)",
      .seq [.class' "Dog" none (.def' "bark" [] (.int 1)),
            .vasgn .lvar "x"
              (.send (some (.array [.send (some (.const "Dog")) "new" [] none])) "[]"
                [.int 0] none),
            .if' (.send (some (.var .lvar "x")) "nil?" [] none) (.int 0) (some (.int 1))]⟩ ]

mutual

/-- `Ratchet.Expr` → `RubyCore.Expr` for the controls only: they are hand-written on this
package's side of the isolation boundary, so there is no JSON to decode twice the way a
corpus rung has. Covers exactly the constructors `controls` uses; anything else is a
`none` that fails loudly. -/
def toRubyCore : Expr → Option RubyCore.Expr
  | .int n => some (.int n)
  | .flt b => some (.flt b)
  | .str s => some (.str s)
  | .sym s => some (.sym s)
  | .tru => some .tru
  | .fls => some .fls
  | .nil => some .nil
  | .vcall m => some (.vcall m)
  | .var .lvar x => some (.var .lvar x)
  | .vasgn .lvar x e => (toRubyCore e).map (fun e' => .vasgn .lvar x e')
  | .seq es => (es.mapM toRubyCore).map (fun es' => .seq es')
  | .if' c t e => do
    let c' ← toRubyCore c
    let t' ← toRubyCore t
    match e with
    | none => return .if' c' t' none
    | some e => return .if' c' t' (some (← toRubyCore e))
  | .block ps ls body => do
    let ps' ← ps.mapM toRubyCoreParam
    return .block ps' ls (← toRubyCore body)
  | .send none m args (some blk) => do
    let args' ← args.mapM toRubyCore
    return .send none m args' (some (← toRubyCore blk))
  | .send (some r) m args (some blk) => do
    let r' ← toRubyCore r
    let args' ← args.mapM toRubyCore
    return .send (some r') m args' (some (← toRubyCore blk))
  | .self' => some .self'
  | .const n => some (.const n)
  | .var .ivar x => some (.var .ivar x)
  | .vasgn .ivar x e => (toRubyCore e).map (fun e' => .vasgn .ivar x e')
  | .module' n body => (toRubyCore body).map (fun b => .module' n b)
  | .class' n sup body => do
    let body' ← toRubyCore body
    match sup with
    | none => return .class' n none body'
    | some sup => return .class' n (some (← toRubyCore sup)) body'
  | .yield' args => (args.mapM toRubyCore).map (fun args' => .yield' args')
  | .ret e =>
    match e with
    | none => some (.ret none)
    | some x => (toRubyCore x).map (fun x' => .ret (some x'))
  | .super' args none =>
    (args.mapM toRubyCore).map (fun args' => .super' args' none)
  | .defs recv n ps body => do
    let recv' ← toRubyCore recv
    let ps' ← ps.mapM toRubyCoreParam
    return .defs recv' n ps' (← toRubyCore body)
  | .def' n ps body => do
    let ps' ← ps.mapM toRubyCoreParam
    return .def' n ps' (← toRubyCore body)
  | .send none m args none =>
    (args.mapM toRubyCore).map (fun args' => .send none m args' none)
  | .array es => (es.mapM toRubyCore).map (fun es' => .array es')
  | .hash ps => (toRubyCorePairs ps).map (fun ps' => .hash ps')
  | .send (some r) m args none => do
    let r' ← toRubyCore r
    let args' ← args.mapM toRubyCore
    return .send (some r') m args' none
  | _ => none

/-- Parameters, for the controls' `def`s. Only the two kinds the controls use. -/
def toRubyCoreParam : Param → Option RubyCore.Param
  | .req x => some (.req x)
  | .block x => some (.block x)
  | .opt x d => (toRubyCore d).map (fun d' => .opt x d')
  | _ => none

/-- The pair-list companion, spelled out rather than a `mapM` with a lambda: the lambda
hides the structural decrease from the termination checker. -/
def toRubyCorePairs : List (Expr × Expr) → Option (List (RubyCore.Expr × RubyCore.Expr))
  | [] => some []
  | (k, v) :: ps => do
    let k' ← toRubyCore k
    let v' ← toRubyCore v
    return (k', v') :: (← toRubyCorePairs ps)

end

def main (args : List String) : IO UInt32 := do
  let corpusDir : System.FilePath := args.headD "corpus"
  let dirEntries ← corpusDir.readDir
  let files := (dirEntries.map (·.path)).toList.filter (fun p => p.toString.endsWith ".json")
  let rows ← rungs.mapM (checkRung corpusDir files)

  IO.println "--- climbed rungs: hand-authored derivations, pinned to corpus + semantics ---"
  for r in rows do
    let cls := r.actualClass.getD "-"
    let mark := if rowOk r then "ok  " else "FAIL"
    IO.println s!"{mark} {r.id}: claimed {repr r.claimedTy}, ran to {r.outcome} of class {cls}, type_stuck={r.typeStuck}, syntax_matches_corpus={r.syntaxOk}"

  IO.println "\n--- negative controls: neighbours `PrimSig` must not certify ---"
  let mut controlFails : List String := []
  for c in controls do
    let certified := validate c.program
    let some rp := toRubyCore c.program
      | throw (IO.userError s!"control '{c.label}': not translatable to RubyCore.Expr")
    let res := Ratchet.Semantics.run fuel rp
    let stuck := Ratchet.Semantics.typeStuck res
    let label := Ratchet.Semantics.outcomeLabel res
    let verdict :=
      if certified then "CERTIFIED -- table is too generous"
      else if stuck then "rejected (sound: really type-stuck)"
      else if label.startsWith "unsupported" || label == "outOfFuel" then
        -- The model declined to run it, so it says nothing either way. Recorded as its
        -- own verdict rather than being swept into "conservative: safe": calling a
        -- program safe because the model would not execute it is exactly the kind of
        -- vacuous pass this file exists to prevent.
        "rejected (model declined to run it -- see the control's note)"
      else "rejected (conservative: safe, no rule yet)"
    IO.println s!"{if certified then "FAIL" else "ok  "} {c.label}: {verdict}, ran to {Ratchet.Semantics.outcomeLabel res}"
    if certified then controlFails := c.label :: controlFails

  let bad := rows.filter (fun r => !rowOk r)
  IO.println s!"\n{rows.length - bad.length}/{rows.length} rungs confirmed: the hand derivation's type agrees with the class the real semantics produced, on the real desugarer's syntax, with nothing trusted anywhere."
  IO.println s!"{controls.length - controlFails.length}/{controls.length} negative controls rejected as required."
  if bad.isEmpty && controlFails.isEmpty then
    IO.println "CHECKRUNGS OK"
    return 0
  else
    for r in bad do IO.eprintln s!"  FAIL: {r.id}"
    for l in controlFails do IO.eprintln s!"  FAIL (control certified): {l}"
    return 1
