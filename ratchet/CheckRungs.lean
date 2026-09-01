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
  | .clos _ _ _ => ["Proc"]
  -- Tier 7: a user-class instance's class is its name. The *ivar spine* is not
  -- cross-checked against the semantics here — this harness compares the class of the
  -- result value and nothing in it reaches inside an object. What backs the spine instead
  -- is that every rung whose type *depends* on it (`class-basic`'s `Integer`,
  -- `class-ivar-lazy-nil`'s `NilClass`) reads an ivar out through a method call, so a wrong
  -- spine shows up as a wrong result class on that rung.
  | .inst n _ => [n]
  -- Tier 12: `Ty.sameAs` is a fact about a *binding*, not about a value, and `Judge.var`
  -- strips it -- so no rung's type can be one. `[]` fails loudly if that ever changes.
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
            .if' (.send (some (.var .lvar "x")) "nil?" [] none) (.int 0) (some (.int 1))]⟩
    -- ### Tier 12's `is_a?` controls
    --
    -- (y) The `is_a?` polarity swap — `corpus/135-narrow-backwards-unsafe` as a control, so
    -- the rejection is labelled by running it. `pick(false)` returns `"s"`, `is_a?(Integer)`
    -- is false, the else-branch runs and `"s" + 1` raises TypeError. Certified by any
    -- implementation that hands `isATy` to the else-branch.
  , ⟨"def pick(f); f ? 1 : \"s\"; end; v = pick(false); if v.is_a?(Integer) then v + \"!\""
      ++ " else v + 1 end",
      .seq [.def' "pick" [.req "flag"]
              (.if' (.var .lvar "flag") (.int 1) (some (.str "s"))),
            .vasgn .lvar "v" (.send none "pick" [.fls] none),
            .if' (.send (some (.var .lvar "v")) "is_a?" [.const "Integer"] none)
              (.send (some (.var .lvar "v")) "+" [.str "!"] none)
              (some (.send (some (.var .lvar "v")) "+" [.int 1] none))]⟩
    -- (z) **The control that makes `isADispatchOk` load-bearing.** `is_a?` is total on every
    -- object in the standard library, but a program-declared class may override it -- and
    -- `is_a?` cannot refuse `.inst` receivers the way `NilQSafe` does, because narrowing a
    -- union of declared classes is the whole point of `narrow-union-subclass`. So the guard
    -- is the precise one: no `.inst` component's MRO may define `is_a?`. Here `D`'s does, and
    -- it raises TypeError.
  , ⟨"class D; def is_a?(k); 1 + \"a\"; end; end; D.new.is_a?(D)",
      .seq [.class' "D" none
              (.def' "is_a?" [.req "k"] (.send (some (.int 1)) "+" [.str "a"] none)),
            .send (some (.send (some (.const "D")) "new" [] none)) "is_a?" [.const "D"] none]⟩
    -- (aa) The argument must be a class object. `1.is_a?(5)` raises TypeError ("class or
    -- module required"), which is inside the family, so `Judge.isAQuery`'s `[.clsOf cn]`
    -- index is a soundness requirement rather than a convenience.
  , ⟨"1.is_a?(5)", .send (some (.int 1)) "is_a?" [.int 5] none⟩
    -- (bb) `constBuiltin` licenses a builtin class's *identity* and nothing else. If builtin
    -- classes were seeded into `CTable` instead, `new` would find the zero-argument allocator
    -- (`Judge.newInstNoInit`) and certify this, and it raises NoMethodError.
  , ⟨"Integer.new", .send (some (.const "Integer")) "new" [] none⟩
    -- (cc) What `BuiltinCls`'s deliberate shortness costs: `Numeric` is a real class and
    -- `1.is_a?(Numeric)` is safe, but it is not a row, so the constant is untypeable. A row
    -- would be one line; it is absent because `builtinAncestors` is where the *answer* would
    -- have to come from and no rung asks.
  , ⟨"1.is_a?(Numeric) (safe; Numeric is not a BuiltinCls row)",
      .send (some (.int 1)) "is_a?" [.const "Numeric"] none⟩
    -- ### Tier 12's guard-clause controls
    --
    -- (dd) The guard's polarity, and the sharpest one on the ladder because *nothing
    -- syntactically encloses the narrowed code*: this is `narrow-guard-clause` with the guard
    -- negated (`unless x.nil?` spelled as `if !x.nil?` would be the idiom; here the same
    -- effect is had by returning on the *non*-nil path). `a[0]` is `nil`, the guard does not
    -- fire, and `nil + 1` raises NoMethodError. Certified by any implementation that types the
    -- rest of the sequence in `(narrowEnvs …).1` instead of `.2`.
  , ⟨"def f(a); x = a[0]; return 0 if x.is_a?(Integer); x + 1; end; f([])",
      .seq [.def' "f" [.req "a"]
              (.seq [.vasgn .lvar "x" (.send (some (.var .lvar "a")) "[]" [.int 0] none),
                     .if' (.send (some (.var .lvar "x")) "is_a?" [.const "Integer"] none)
                       (.ret (some (.int 0))) none,
                     .send (some (.var .lvar "x")) "+" [.int 1] none]),
            .send none "f" [.array []] none]⟩
    -- (ee) **`.ret` still has no rule**, and this is the control that says so. `JudgeSeq.guard`
    -- matches only `.if' c (.ret (some e)) none` in *non-final* position, so a bare `return`
    -- as a statement is untypeable -- which is what stops the unsound rule `bodyResult`'s
    -- docstring warns about: giving `.ret e` the type of `e` would make this validate at `Int`
    -- when the method really returns a String.
  , ⟨"def f; return \"a\"; 2; end; f() + 1 (unsound if `.ret` had a rule)",
      .seq [.def' "f" [] (.seq [.ret (some (.str "a")), .int 2]),
            .send (some (.send none "f" [] none)) "+" [.int 1] none]⟩
    -- (ff) The guard's *returned* expression is typed too, in the then-branch's environment.
    -- Here it is type-stuck (`nil + 1`, on the path where `x` is `nil`), and nothing at the
    -- call site or after the guard looks wrong -- the `guard` twin of `fun-body-mismatch`.
  , ⟨"def f(a); x = a[0]; return x + 1 if x.nil?; 0; end; f([])",
      .seq [.def' "f" [.req "a"]
              (.seq [.vasgn .lvar "x" (.send (some (.var .lvar "a")) "[]" [.int 0] none),
                     .if' (.send (some (.var .lvar "x")) "nil?" [] none)
                       (.ret (some (.send (some (.var .lvar "x")) "+" [.int 1] none))) none,
                     .int 0]),
            .send none "f" [.array []] none]⟩
    -- ### Tier 12's ivar controls
    --
    -- (gg) The polarity swap, one piece of state over: `@v` is a String, `is_a?(Integer)` is
    -- false, the else-branch runs and `"s" + 1` raises TypeError. Certified by any
    -- implementation that hands `isATy` to the else-branch of an *ivar* test -- which is a
    -- separate code path from the local one, hence a separate control.
  , ⟨"class H; @v = \"s\"; def d; if @v.is_a?(Integer) then @v + \"!\" else @v + 1 end; end;"
      ++ " H.new.d",
      .seq [.class' "H" none (.seq [
              .def' "initialize" [] (.vasgn .ivar "@v" (.str "s")),
              .def' "d" []
                (.if' (.send (some (.var .ivar "@v")) "is_a?" [.const "Integer"] none)
                  (.send (some (.var .ivar "@v")) "+" [.str "!"] none)
                  (some (.send (some (.var .ivar "@v")) "+" [.int 1] none)))]),
            .send (some (.send (some (.const "H")) "new" [] none)) "d" [] none]⟩
    -- (hh) **The control that says the spine *join* did not weaken clink 6's invariant.**
    -- `Judge.if'` now widens a disagreeing spine instead of rejecting it, and the question that
    -- raises is whether a *method* can now retype an instance variable out from under its
    -- caller. It cannot: `callMethod`'s premise is still that the body's outgoing spine equals
    -- its incoming one, and `joinSpine` of two branches that both say `@x : String` is
    -- `@x : String`, not `@x : Int`. This program really raises TypeError.
  , ⟨"class C; @x = 1; def m(f); if f then @x = \"s\" else @x = \"s\" end; end; def get; @x;"
      ++ " end; end; c = C.new; c.m(true); c.get + 1",
      .seq [.class' "C" none (.seq [
              .def' "initialize" [] (.vasgn .ivar "@x" (.int 1)),
              .def' "m" [.req "f"]
                (.if' (.var .lvar "f")
                  (.vasgn .ivar "@x" (.str "s"))
                  (some (.vasgn .ivar "@x" (.str "s")))),
              .def' "get" [] (.var .ivar "@x")]),
            .vasgn .lvar "c" (.send (some (.const "C")) "new" [] none),
            .send (some (.var .lvar "c")) "m" [.tru] none,
            .send (some (.send (some (.var .lvar "c")) "get" [] none)) "+" [.int 1] none]⟩
    -- ### Tier 9c's iterator controls
    --
    -- (ii) **`sort_by`'s `Comparable` side condition is a soundness requirement**, and the
    -- failure mode is worth stating precisely, because the obvious guess is wrong: it is *not*
    -- that some key type has no `<=>` at all. `nil <=> nil` is `0`, so
    -- `["a","b"].sort_by { |s| nil }` sorts fine. What raises is a key type whose `<=>` is not
    -- total **across its own values** -- a union (`1 <=> "a"` is `nil`, hence
    -- `ArgumentError: comparison of Integer with String failed`, *inside* the family), or a
    -- user class that inherits `Object#<=>` (which answers `0` for identical objects and `nil`
    -- otherwise). `Comparable`'s three rows are exactly the types this `Ty` can produce a
    -- genuinely ordered array of. Its sibling `select`, two controls down, shows the contrast:
    -- `select` needs no condition on `ρ`, because a `select` block's result is only ever tested
    -- for truthiness.
  , ⟨"[1, \"a\"].sort_by { |x| x }",
      .send (some (.array [.int 1, .str "a"])) "sort_by" []
        (some (.block [.req "x"] [] (.var .lvar "x")))⟩
    -- (jj) …and the same block under `select`, which is safe Ruby and *validates* -- so this
    -- is not a control but a note; what is recorded here instead is the `select` shape that
    -- must NOT validate: a block body that is itself type-stuck. The iterator wrapper must
    -- not launder it, exactly as `block-bad-arith` requires of `each`.
  , ⟨"[1, 2].select { |x| x + \"a\" }",
      .send (some (.array [.int 1, .int 2])) "select" []
        (some (.block [.req "x"] []
          (.send (some (.var .lvar "x")) "+" [.str "a"] none)))⟩
    -- (kk) **`inject`'s accumulator fixed point, from the inside.** The block returns an
    -- `Integer` on one path and a `String` on the other, so the accumulator *changes type
    -- between iterations*: iteration 1 sees `acc = 0`, takes the then-branch and returns
    -- `"s"`; iteration 2 sees `acc = "s"`, takes the else-branch, and `"s" + 1` raises
    -- TypeError. No single `Ty` describes that accumulator, which is exactly why
    -- `IterSig.inject` requires the body to come back at the initial value's type -- here the
    -- body comes back at `union(String, Int)`, and the row rejects it.
  , ⟨"[1, 2].inject(0) { |acc, x| if acc == 0 then \"s\" else acc + 1 end }",
      .send (some (.array [.int 1, .int 2])) "inject" [.int 0]
        (some (.block [.req "acc", .req "x"] []
          (.if' (.send (some (.var .lvar "acc")) "==" [.int 0] none)
            (.str "s")
            (some (.send (some (.var .lvar "acc")) "+" [.int 1] none)))))⟩
    -- (kk2) …and from the outside: `inject`'s *result* is the initial value's type only
    -- because the block is required to reproduce it. Here the block returns a `String` every
    -- time, so the real result is `"2"` and `+ 1` raises TypeError. Certified by any
    -- implementation that reports `inject`'s result as `init`'s type without checking the
    -- block against it.
  , ⟨"[1, 2].inject(0) { |acc, x| x.to_s } + 1",
      .send (some (.send (some (.array [.int 1, .int 2])) "inject" [.int 0]
        (some (.block [.req "acc", .req "x"] []
          (.send (some (.var .lvar "x")) "to_s" [] none))))) "+" [.int 1] none⟩
    -- (ll) **`each` returns the receiver, not the block's value.** `[1,2].each { |x| x.to_s }`
    -- is an `Array`, so `+ "!"` raises TypeError ("no implicit conversion of String into
    -- Array"). Certified by any implementation that gives `each` `map`'s row.
  , ⟨"[1, 2].each { |x| x.to_s } + \"!\"",
      .send (some (.send (some (.array [.int 1, .int 2])) "each" []
        (some (.block [.req "x"] [] (.send (some (.var .lvar "x")) "to_s" [] none)))))
        "+" [.str "!"] none⟩
    -- (mm) **`select` returns the receiver's elements, not the block's.** The block answers a
    -- `Bool`, and `[true, false]` would have no `+ 1`; the result really is `[1, 2]`, so this
    -- is the *sound* direction -- `x + 1` on an element. Kept as a control because it is
    -- rejected: `arrayOf Int` is not an `Integer`, and there is no `Array#+ Integer`. The
    -- point is that it fails for the *arity* reason and not because `select` was mistyped.
  , ⟨"[1, 2].select { |x| x > 1 } + 1 (safe-ish; no Array#+ Integer row)",
      .send (some (.send (some (.array [.int 1, .int 2])) "select" []
        (some (.block [.req "x"] [] (.send (some (.var .lvar "x")) ">" [.int 1] none)))))
        "+" [.int 1] none⟩
    -- (nn) **The `&` forms are not a free pass.** `[1,2].map(&:foo_bar)` has no `PrimSig` row
    -- for `Integer#foo_bar`, and really raises NoMethodError. This is the control that says
    -- `iterSymPass` reads a *table* rather than assuming any symbol coerces to something
    -- total.
  , ⟨"[1, 2].map(&:foo_bar)",
      .send (some (.array [.int 1, .int 2])) "map" []
        (some (.blockpass (some (.sym "foo_bar"))))⟩
    -- (oo) **A block passed to an iterator may not retype a captured local**, the clink-11
    -- rule one syntax over: `each` carries the enclosing environment out unchanged, so
    -- `capIntact` is what stops the caller keeping a stale type. Really raises TypeError.
  , ⟨"a = 1; [1, 2].each { |x| a = \"s\" }; a + 1",
      .seq [.vasgn .lvar "a" (.int 1),
            .send (some (.array [.int 1, .int 2])) "each" []
              (some (.block [.req "x"] [] (.vasgn .lvar "a" (.str "s")))),
            .send (some (.var .lvar "a")) "+" [.int 1] none]⟩
    -- (pp) A non-array receiver has no iterator rule at all. `{"a"=>1}.map { … }` is
    -- perfectly safe Ruby; `iterBlock` requires `arrayOf elem`, and `Ty` has no `hashOf` to
    -- read an element type out of (the third recorded `Ty` language gap).
  , ⟨"{\"a\" => 1}.map { |p| p } (safe; iterators need an arrayOf receiver)",
      .send (some (.hash [(.str "a", .int 1)])) "map" []
        (some (.block [.req "p"] [] (.var .lvar "p")))⟩
    -- ### Tier 11's closure-`self` control
    --
    -- (qq) **The control that makes `Ty.clos`'s third field load-bearing.** The lambda is
    -- created inside `A#mk`, where `@v` is a String, and invoked inside `B#run`, where `@v` is
    -- an `Integer`. Its body is `@v + 1`, so at runtime it computes `"s" + 1` and raises
    -- TypeError. A `closCall` that judged the body against the **caller's** `self` and ivar
    -- spine -- which is what this rule did before the field existed, behind a
    -- `κ.selfTy = none` premise that hid the question rather than answering it -- would see
    -- `@v : Integer` and certify it.
    --
    -- The positive twin is the same program with the two classes' ivars swapped: creation self
    -- `@v : Integer`, so `@v + 1` types, and it really returns `2`. That one is not a control
    -- because it *validates* -- which is the whole point of putting the creation `self` in the
    -- type rather than forbidding the program.
  , ⟨"class A; @v=\"s\"; def mk; lambda { @v + 1 }; end; end; class B; @v=1; def run(f);"
      ++ " f.call; end; end; B.new.run(A.new.mk)",
      .seq [.class' "A" none (.seq [
              .def' "initialize" [] (.vasgn .ivar "@v" (.str "s")),
              .def' "mk" []
                (.send none "lambda" []
                  (some (.block [] []
                    (.send (some (.var .ivar "@v")) "+" [.int 1] none))))]),
            .class' "B" none (.seq [
              .def' "initialize" [] (.vasgn .ivar "@v" (.int 1)),
              .def' "run" [.req "f"]
                (.send (some (.var .lvar "f")) "call" [] none)]),
            .send (some (.send (some (.const "B")) "new" [] none)) "run"
              [.send (some (.send (some (.const "A")) "new" [] none)) "mk" [] none] none]⟩
    -- (rr) What `Ctx.inClosure`'s two erasures cost, recorded rather than argued away: a
    -- closure body's `frame` and `blockTy` are cleared, so a `super` or a `yield` inside a
    -- block body has no rule even where Ruby resolves it to the enclosing method's. This is
    -- safe Ruby (`3`) that the judgment declines. Making it precise means recording those two
    -- in `Ty.clos` as well, exactly as `selfTy` now is.
  , ⟨"def t; f = lambda { yield }; f.call; end; t { 3 } (safe; blockTy is cleared in a"
      ++ " closure body)",
      .seq [.def' "t" []
              (.seq [.vasgn .lvar "f" (.send none "lambda" []
                       (some (.block [] [] (.yield' [])))),
                     .send (some (.var .lvar "f")) "call" [] none]),
            .send none "t" [] (some (.block [] [] (.int 3)))]⟩
    -- ### Tier 11's block-carrying-call controls
    --
    -- (ss) The block wrapper must not launder a type error, the same requirement
    -- `block-bad-arith` puts on `each` but through a *method*: `bump` yields the object's `@n`
    -- (a String) into a block that adds `1` to it. Really raises TypeError, and nothing at the
    -- call site or in the method looks wrong -- the `callMethodBlk` twin of
    -- `fun-body-mismatch`.
  , ⟨"class C; @n=\"s\"; def bump; yield(@n); end; end; C.new.bump { |x| x + 1 }",
      .seq [.class' "C" none (.seq [
              .def' "initialize" [] (.vasgn .ivar "@n" (.str "s")),
              .def' "bump" [] (.yield' [.var .ivar "@n"])]),
            .send (some (.send (some (.const "C")) "new" [] none)) "bump" []
              (some (.block [.req "x"] []
                (.send (some (.var .lvar "x")) "+" [.int 1] none)))]⟩
    -- (tt) **`yield` without a block is still not derivable**, even now that the yielding
    -- method may be an instance method. `blockTy` is set only by the three block-carrying call
    -- rules, so `C.new.bump` with no block has no `yieldExpr` premise to discharge. Raises
    -- LocalJumpError, which is *outside* the family -- so this is a conservative rejection of a
    -- program that nevertheless crashes, exactly like `bare-undeclared-var`'s NameError.
  , ⟨"class C; def bump; yield(1); end; end; C.new.bump (safe by this ladder; LocalJumpError)",
      .seq [.class' "C" none (.def' "bump" [] (.yield' [.int 1])),
            .send (some (.send (some (.const "C")) "new" [] none)) "bump" [] none]⟩
    -- (uu) `paramEnvB` binds a `&b` parameter to `.nilT` when no block is passed -- which is
    -- Ruby -- so `blk.call` on the block-less path raises NoMethodError on `nil`. The instance
    -- method twin of the tier-9b control, and it says the binding is not a formality: without
    -- it `blk` would be unbound and this would fail for the wrong reason.
  , ⟨"class C; def a(&blk); blk.call(3); end; end; C.new.a",
      .seq [.class' "C" none
              (.def' "a" [.block (some "blk")]
                (.send (some (.var .lvar "blk")) "call" [.int 3] none)),
            .send (some (.send (some (.const "C")) "new" [] none)) "a" [] none]⟩
    -- (vv) A block with `|x; y|` block-locals is refused on the *method* routes, because the
    -- block becomes a `Ty.clos` and `Clos` records only `(params, body)`. Safe Ruby, declined
    -- -- and note the asymmetry with the iterator route, which types the block where it stands
    -- and so admits locals (`block-doend-with-block-local`). Lifting this means recording the
    -- locals in `Clos`.
  , ⟨"class C; def bump; yield(1); end; end; C.new.bump do |x; y| y = x; y end (safe; Clos"
      ++ " records no block-locals)",
      .seq [.class' "C" none (.def' "bump" [] (.yield' [.int 1])),
            .send (some (.send (some (.const "C")) "new" [] none)) "bump" []
              (some (.block [.req "x"] ["y"]
                (.seq [.vasgn .lvar "y" (.var .lvar "x"), .var .lvar "y"])))]⟩
    -- ### Tier 10's reopening controls
    --
    -- (ww) **A redefinition must win.** `mergeCls` puts the later body's methods *first*
    -- because `defGet?` is a `find?`; reversed, `Foo#a` would still look like an `Integer` and
    -- `"s" + 1` would validate. Really raises TypeError.
  , ⟨"class Foo; def a; 1; end; end; class Foo; def a; \"s\"; end; end; Foo.new.a + 1",
      .seq [.class' "Foo" none (.def' "a" [] (.int 1)),
            .class' "Foo" none (.def' "a" [] (.str "s")),
            .send (some (.send (some (.send (some (.const "Foo")) "new" [] none)) "a" []
              none)) "+" [.int 1] none]⟩
    -- (xx) **…and a method must not be visible before its `class` statement.** The merge
    -- happens in `JudgeSeq.cons`, statement by statement, so at the middle statement `Foo` has
    -- only `a`. Really raises NoMethodError -- which is what makes accumulation safe to model
    -- this way rather than by a whole-program scan.
  , ⟨"class Foo; def a; 1; end; end; Foo.new.b; class Foo; def b; 2; end; end",
      .seq [.class' "Foo" none (.def' "a" [] (.int 1)),
            .send (some (.send (some (.const "Foo")) "new" [] none)) "b" [] none,
            .class' "Foo" none (.def' "b" [] (.int 2))]⟩
    -- ### Tier 10's mixin controls
    --
    -- (yy) **`include` on a non-Module raises TypeError**, which is inside the family -- so
    -- `Judge.classStmt`'s `allModules` premise is a soundness requirement. Without it, `P`
    -- would get `K`'s methods and `P.new.m` would validate a program that raises before it
    -- ever dispatches.
  , ⟨"class K; def m; 1; end; end; class P; include K; end; P.new.m",
      .seq [.class' "K" none (.def' "m" [] (.int 1)),
            .class' "P" none (.send none "include" [.const "K"] none),
            .send (some (.send (some (.const "P")) "new" [] none)) "m" [] none]⟩
    -- (zz) **`extend` does not give *instances* the method.** `Cls.extended` is consulted only
    -- by `smroGet?`, so `P.new.shout` finds nothing. Really raises NoMethodError.
  , ⟨"module L; def shout; \"L\"; end; end; class P; extend L; end; P.new.shout",
      .seq [.module' "L" (.def' "shout" [] (.str "L")),
            .class' "P" none (.send none "extend" [.const "L"] none),
            .send (some (.send (some (.const "P")) "new" [] none)) "shout" [] none]⟩
    -- (aaa) …and the mirror: **`include` does not give the class *object* the method.** Really
    -- raises NoMethodError. The two controls together are what pin `include` and `extend` to
    -- different tables rather than to one "mixins" list.
  , ⟨"module G; def greet; \"hi\"; end; end; class P; include G; end; P.greet",
      .seq [.module' "G" (.def' "greet" [] (.str "hi")),
            .class' "P" none (.send none "include" [.const "G"] none),
            .send (some (.const "P")) "greet" [] none]⟩
    -- (bbb) **The control that makes `ancestorsUp` name included modules.** `x` really *is* an
    -- `M`, so the then-branch runs and `x.nope` raises NoMethodError. Under a module-blind
    -- ancestor chain `isAAnswer` would answer `some false`, `isATy` would refine `x` to
    -- `.never`, and the whole then-branch would become vacuous -- `joinT never Int = Int`, and
    -- the program validates. This is the obligation clink 14 wrote down against tier 10, as an
    -- executable check.
  , ⟨"module M; end; class P; include M; end; x = P.new; if x.is_a?(M) then x.nope else 0 end",
      .seq [.module' "M" .nil,
            .class' "P" none (.send none "include" [.const "M"] none),
            .vasgn .lvar "x" (.send (some (.const "P")) "new" [] none),
            .if' (.send (some (.var .lvar "x")) "is_a?" [.const "M"] none)
              (.send (some (.var .lvar "x")) "nope" [] none)
              (some (.int 0))]⟩
    -- (ccc) …and the same shape one level deeper, which `mixinAncestors?` refuses outright: a
    -- module that itself includes another has an ancestor the one-level walk would omit, so the
    -- chain becomes *unknown* rather than under-reported. Rejected -- and soundly, since this
    -- also raises NoMethodError.
  , ⟨"module A; end; module B; include A; end; class P; include B; end; x = P.new;"
      ++ " if x.is_a?(A) then x.nope else 0 end",
      .seq [.module' "A" .nil,
            .module' "B" (.send none "include" [.const "A"] none),
            .class' "P" none (.send none "include" [.const "B"] none),
            .vasgn .lvar "x" (.send (some (.const "P")) "new" [] none),
            .if' (.send (some (.var .lvar "x")) "is_a?" [.const "A"] none)
              (.send (some (.var .lvar "x")) "nope" [] none)
              (some (.int 0))]⟩
    -- ### Tier 10's prepend controls
    --
    -- (ddd) **The MRO order, pinned by execution.** `prepend` puts the module *ahead* of the
    -- class, so `M#f` is what runs and this program returns `"m"` -- `"m" + 1` raises
    -- TypeError. A checker that put the module *after* the class (which is what `include`
    -- does, and which a positional-field mistake in `mergeCls` really did produce) would find
    -- `P#f`, see an `Integer`, and certify it.
  , ⟨"module M; def f; \"m\"; end; end; class P; prepend M; def f; 1; end; end; P.new.f + 1",
      .seq [.module' "M" (.def' "f" [] (.str "m")),
            .class' "P" none (.seq [
              .send none "prepend" [.const "M"] none,
              .def' "f" [] (.int 1)]),
            .send (some (.send (some (.send (some (.const "P")) "new" [] none)) "f" [] none))
              "+" [.int 1] none]⟩
    -- (eee) …and the `include` twin of the same program, which must go the *other* way: the
    -- class's own method wins, the result is `1`, and `+ "!"` raises TypeError. The pair is
    -- what stops `prepends` and `includes` from being collapsed into one list.
  , ⟨"module M; def f; \"m\"; end; end; class P; include M; def f; 1; end; end;"
      ++ " P.new.f + \"!\"",
      .seq [.module' "M" (.def' "f" [] (.str "m")),
            .class' "P" none (.seq [
              .send none "include" [.const "M"] none,
              .def' "f" [] (.int 1)]),
            .send (some (.send (some (.send (some (.const "P")) "new" [] none)) "f" [] none))
              "+" [.str "!"] none]⟩
    -- (fff) **`zsuper`'s arity premise.** The running method takes a parameter, so `zsuper`
    -- forwards it -- to a parent that takes none, which raises ArgumentError, *inside* the
    -- family. `Judge.zsuperCall` requires the running method's parameter list to be empty, so
    -- this is rejected; without that premise it would type as a zero-argument `super`.
  , ⟨"class B; def f; 1; end; end; class C < B; def f(x); super; end; end; C.new.f(2)",
      .seq [.class' "B" none (.def' "f" [] (.int 1)),
            .class' "C" (some (.const "B")) (.def' "f" [.req "x"] (.zsuper none)),
            .send (some (.send (some (.const "C")) "new" [] none)) "f" [.int 2] none]⟩
    -- ### Tier 10's `method_missing` controls
    --
    -- (ggg) **The control that makes `ObjectMethod`'s list a soundness condition.** `to_s` is
    -- not in the program's class table, so `mroGet?` misses -- but Ruby runs `Object#to_s`, not
    -- `method_missing`. Here `method_missing` returns an `Integer` while `Object#to_s` returns
    -- a String, so without the guard the checker would type `Ghost.new.to_s` as `Integer`,
    -- accept `+ 1`, and be **wrong about the value's class** rather than merely permissive.
    -- Really raises TypeError.
  , ⟨"class G; def method_missing(n); 5; end; end; G.new.to_s + 1",
      .seq [.class' "G" none (.def' "method_missing" [.req "n"] (.int 5)),
            .send (some (.send (some (.send (some (.const "G")) "new" [] none)) "to_s" []
              none)) "+" [.int 1] none]⟩
    -- (hhh) **`method_missing` is a fallback, not an override.** `a` exists, so it runs and
    -- returns a String; `"s" + 1` raises TypeError. A rule that could fire while an ordinary
    -- method exists would give the wrong type for every call on a class that defines
    -- `method_missing` at all.
  , ⟨"class G; def a; \"s\"; end; def method_missing(n); 1; end; end; G.new.a + 1",
      .seq [.class' "G" none (.seq [
              .def' "a" [] (.str "s"),
              .def' "method_missing" [.req "n"] (.int 1)]),
            .send (some (.send (some (.send (some (.const "G")) "new" [] none)) "a" [] none))
              "+" [.int 1] none]⟩
    -- (iii) **The missing name is passed *in addition to* the original arguments**, so
    -- `def method_missing(name)` cannot absorb a call that had any. `paramEnv`'s length check
    -- rejects it, and Ruby raises ArgumentError -- inside the family, so this is a sound
    -- rejection rather than a conservative one.
  , ⟨"class G; def method_missing(n); 1; end; end; G.new.whatever(7)",
      .seq [.class' "G" none (.def' "method_missing" [.req "n"] (.int 1)),
            .send (some (.send (some (.const "G")) "new" [] none)) "whatever" [.int 7] none]⟩
    -- ### Tier 12's aliasing controls
    --
    -- `Ty.sameAs`'s soundness is entirely a question of **invalidation**, so these controls are
    -- one per way an alias can go stale. Each uses the desugarer's own temporary name, because
    -- that is what `Judge.vasgnAlias` admits; a hand-written control can spell it.
    --
    -- (jjj) **Reassigning the alias's target.** `v` gets a new object, so `__dt_t1` no longer
    -- holds the same one -- and `Integer === __dt_t1` is still *true* (it holds the old `1`), so
    -- the then-branch runs and `"s" + 1` raises TypeError. Without `killAliasesTo` in
    -- `Judge.vasgn`, the refinement would reach `v` and certify it.
  , ⟨"def pick(f) …; v = pick(true); __dt_t1 = v; v = \"s\";"
      ++ " if Integer === __dt_t1 then v + 1 else 0 end",
      .seq [.def' "pick" [.req "flag"]
              (.if' (.var .lvar "flag") (.int 1) (some (.str "s"))),
            .vasgn .lvar "v" (.send none "pick" [.tru] none),
            .vasgn .lvar "__dt_t1" (.var .lvar "v"),
            .vasgn .lvar "v" (.str "s"),
            .if' (.send (some (.const "Integer")) "===" [.var .lvar "__dt_t1"] none)
              (.send (some (.var .lvar "v")) "+" [.int 1] none)
              (some (.int 0))]⟩
    -- (kkk) **A block reassigning the target**, which is the case that made clink 17 reject the
    -- `Ty.sameAs` design outright. It is not visible as an assignment: the iterator rule carries
    -- the caller's environment out unchanged, justified by `capIntact` -- which compares *types*
    -- -- and here the block reassigns `v` at the *same* union type. So the type survives and the
    -- alias must not, which is what `killAliases` on those rules' outgoing environments does.
    -- Really raises TypeError.
  , ⟨"def pick(f) …; v = pick(true); __dt_t1 = v; [1].each { |z| v = pick(false) };"
      ++ " if Integer === __dt_t1 then v + 1 else 0 end",
      .seq [.def' "pick" [.req "flag"]
              (.if' (.var .lvar "flag") (.int 1) (some (.str "s"))),
            .vasgn .lvar "v" (.send none "pick" [.tru] none),
            .vasgn .lvar "__dt_t1" (.var .lvar "v"),
            .send (some (.array [.int 1])) "each" []
              (some (.block [.req "z"] []
                (.vasgn .lvar "v" (.send none "pick" [.fls] none)))),
            .if' (.send (some (.const "Integer")) "===" [.var .lvar "__dt_t1"] none)
              (.send (some (.var .lvar "v")) "+" [.int 1] none)
              (some (.int 0))]⟩
    -- (lll) What the `desugarTemps` restriction costs: the same program with a *user-written*
    -- name records no alias, so `v` is not refined and this safe Ruby is declined. The
    -- restriction is blast radius rather than soundness (`Judge.vasgnAlias`), and this is the
    -- price, recorded as a number.
  , ⟨"def pick(f) …; v = pick(true); t = v; if Integer === t then v + 1 else 0 end (safe;"
      ++ " aliases are recorded only for desugarer temporaries)",
      .seq [.def' "pick" [.req "flag"]
              (.if' (.var .lvar "flag") (.int 1) (some (.str "s"))),
            .vasgn .lvar "v" (.send none "pick" [.tru] none),
            .vasgn .lvar "t" (.var .lvar "v"),
            .if' (.send (some (.const "Integer")) "===" [.var .lvar "t"] none)
              (.send (some (.var .lvar "v")) "+" [.int 1] none)
              (some (.int 0))]⟩
    -- (mmm) **`Module#===` can be overridden on the class object**, which is what
    -- `Judge.caseEqQuery`'s `smroGet? … = none` premise excludes. Here `C.===` raises TypeError.
    -- Note this is a *different* guard from `is_a?`'s: `Module#===` is implemented directly as
    -- the ancestor test and does not go through `obj.is_a?`, so a user `is_a?` cannot affect it
    -- and `isADispatchOk` is not the right question.
  , ⟨"class C; def self.===(o); 1 + \"a\"; end; end; if C === 5 then 1 else 2 end",
      .seq [.class' "C" none
              (.defs .self' "===" [.req "o"]
                (.send (some (.int 1)) "+" [.str "a"] none)),
            .if' (.send (some (.const "C")) "===" [.int 5] none) (.int 1) (some (.int 2))]⟩
    -- ### Tier 12's `&&` controls
    --
    -- (nnn) **`NarrowSides.thenOnly`, and it is a soundness requirement rather than caution.**
    -- `x` is `3`, so the condition's first conjunct is truthy and the second (`3 > 5`) is false
    -- -- the **else**-branch runs, with `x` an ordinary `Integer`, and `3 + "!"` raises
    -- TypeError. Refining the else-branch (`sides = .both`) would give `x` type
    -- `falsyTy Int = .never`, which makes the whole branch *vacuous*: `x + "!"` becomes
    -- `.never` by strictness, `joinT Int never = Int`, and the program validates. This is the
    -- sharpest control on the ladder for `Ty.never`'s dead-branch reading, because it is the
    -- one place that reading can be reached by a branch that is *not* dead.
  , ⟨"x = 3; if x && x > 5 then 0 else x + \"!\" end",
      .seq [.vasgn .lvar "x" (.int 3),
            .if' (.seq [.vasgn .lvar "__dt_t1" (.var .lvar "x"),
                        .if' (.var .lvar "__dt_t1")
                          (.send (some (.var .lvar "x")) ">" [.int 5] none)
                          (some (.var .lvar "__dt_t1"))])
              (.int 0)
              (some (.send (some (.var .lvar "x")) "+" [.str "!"] none))]⟩
    -- (ooo) **`noLocalAsgn` on the right conjunct.** The refinement is applied to the
    -- environment at the *end* of the condition, and here the right conjunct **reassigns `x`**
    -- (to `b[0]`, which is `nil`) and then answers `true`. So the condition is truthy, the
    -- then-branch runs, and `nil + 1` raises NoMethodError -- while a checker that refined `x`
    -- by `truthyTy` on the strength of a test on its *old* value would call it an `Integer`.
    -- The `.vasgn` inside a `seq` is exactly what the whitelist refuses.
  , ⟨"a = [3]; b = []; x = a[0]; if x && (x = b[0]; true) then x + 1 else 0 end",
      .seq [.vasgn .lvar "a" (.array [.int 3]),
            .vasgn .lvar "b" (.array []),
            .vasgn .lvar "x" (.send (some (.var .lvar "a")) "[]" [.int 0] none),
            .if' (.seq [.vasgn .lvar "__dt_t1" (.var .lvar "x"),
                        .if' (.var .lvar "__dt_t1")
                          (.seq [.vasgn .lvar "x"
                                   (.send (some (.var .lvar "b")) "[]" [.int 0] none),
                                 .tru])
                          (some (.var .lvar "__dt_t1"))])
              (.send (some (.var .lvar "x")) "+" [.int 1] none)
              (some (.int 0))]⟩
    -- ### Tier 13's controls — the constant table's three edges
    --
    -- (p13a) **The reason `classStmt`/`moduleStmt` grew a `constGet?` premise.** Assigning a
    -- constant and *then* declaring a class at the same name raises `TypeError` ("X is not a
    -- class") — inside the family. Without the premise `chk` would type both statements
    -- happily, each in isolation being fine.
  , ⟨"X = 5; class X; end",
      .seq [.casgn "X" (.int 5), .class' "X" none .nil]⟩
    -- (p13b) **The reason `constCls` grew one.** Here the class comes first, so the
    -- declaration is legal (Ruby warns about the reassignment and takes it); what is then
    -- illegal is `X.new`, because `X` is `5`. The class table still has a `X` row, so the old
    -- two-rule `const` would have answered `.clsOf "X"` and certified the allocation.
  , ⟨"class X; end; X = 5; X.new",
      .seq [.class' "X" none .nil, .casgn "X" (.int 5),
            .send (some (.const "X")) "new" [] none]⟩
    -- (p13c) **A constant read is still just a read.** `constEnv` gives `X` the type of what
    -- was assigned and nothing more, so an unmodeled method on it is a NoMethodError this
    -- rejects for the ordinary reason.
  , ⟨"X = 5; X.foo",
      .seq [.casgn "X" (.int 5), .send (some (.const "X")) "foo" [] none]⟩
    -- (p13d) **Order-sensitivity, which is why the table is threaded.** Reading a constant
    -- before its assignment raises `NameError`, and a whole-program constant pre-pass would
    -- have certified this. `NameError` is *not* in the type-stuck family, so the semantics
    -- reports this one as safe and the rejection prints as conservative — the honest verdict:
    -- the rejection is required by Ruby, not by this package's definition of type-stuck.
  , ⟨"X + 1; X = 10 (safe by this package's definition; really a NameError)",
      .seq [.send (some (.const "X")) "+" [.int 1] none, .casgn "X" (.int 10)]⟩
    -- (p13e) **A class-body constant's initializer must be a *literal*** (tier 13b). This is
    -- perfectly safe Ruby and rejected anyway: `constLitTy?` cannot read `1 + 2`, so
    -- `classStmt`'s `JudgeConsts` premise has no type to judge it at. The conservatism is the
    -- price of `extendConsts` being a syntactic function -- see §A class body's constants.
  , ⟨"class Box; SIZE = 1 + 2; end; Box.new (safe; a class constant needs a literal)",
      .seq [.class' "Box" none (.casgn "SIZE" (.send (some (.int 1)) "+" [.int 2] none)),
            .send (some (.const "Box")) "new" [] none]⟩
    -- (p13f) **A class's constant is not in scope at top level.** `constGet?` tries the
    -- frame-relative path first and the top-level one second, and outside any method there is
    -- no frame -- so this read misses. Ruby raises `NameError` (it wants `Box::SIZE`), which is
    -- outside the type-stuck family, so this prints as conservative for the same reason
    -- (p13d) does.
  , ⟨"class Box; SIZE = 3; end; SIZE + 1 (really a NameError)",
      .seq [.class' "Box" none (.casgn "SIZE" (.int 3)),
            .send (some (.const "SIZE")) "+" [.int 1] none]⟩
    -- (p13g) **`PrimSig.freezeId`'s guard.** `freeze` is the identity on a builtin value, and
    -- `NilQSafe` is what keeps the row off an `.inst` -- where a user-written `def freeze` is
    -- dispatched to instead, and this one raises TypeError.
  , ⟨"class C; def freeze; 1 + \"a\"; end; end; C.new.freeze",
      .seq [.class' "C" none (.def' "freeze" []
              (.send (some (.int 1)) "+" [.str "a"] none)),
            .send (some (.send (some (.const "C")) "new" [] none)) "freeze" [] none]⟩
    -- (p13h) **`constPath`'s base premise, which is the whole reason it has one** (tier 13c).
    -- `M` is rebound to `5`, so `M::X` raises TypeError ("5 is not a class/module") even
    -- though the constant table still holds a perfectly good `"::M::X"`. A rule that formed
    -- the key syntactically and looked it up would certify this.
  , ⟨"module M; X = 1; end; M = 5; M::X",
      .seq [.module' "M" (.casgn "X" (.int 1)), .casgn "M" (.int 5),
            .cpath (some (.const "M")) "X"]⟩
    -- (p13i) The write side of the same fact: assigning into something that is not a
    -- namespace.
  , ⟨"M = 5; M::X = 4",
      .seq [.casgn "M" (.int 5), .cpathAsgn (some (.const "M")) "X" (.int 4)]⟩
    -- (p13j) **`private_constant`, the only thing it does** (tier 13d). Reading the constant
    -- from outside raises `NameError`. Outside the type-stuck family, so this prints as
    -- conservative -- but a checker that dropped the member as a no-op would *certify* it,
    -- which is why `Ctx.privConsts` exists at all.
  , ⟨"class Box; SECRET = 1; private_constant :SECRET; end; Box::SECRET (really a NameError)",
      .seq [.class' "Box" none (.seq [.casgn "SECRET" (.int 1),
                                      .send none "private_constant" [.sym "SECRET"] none]),
            .cpath (some (.const "Box")) "SECRET"]⟩
    -- (p13k) **An unresolvable `alias` makes the class unreadable.** `resolveAliases` answers
    -- `none`, so `classMethods?` does, so the class never enters the table -- and the program
    -- really does raise (`NameError` at the `alias` line).
  , ⟨"class Box; alias length size; end; Box.new (really a NameError at the alias)",
      .seq [.class' "Box" none (.alias' "length" "size"),
            .send (some (.const "Box")) "new" [] none]⟩
    -- (p13l) **`attr_reader` is expanded, not trusted.** The reader really does read `@z`,
    -- which this object never assigns -- so it is `nil`, and `nil + 1` raises NoMethodError.
    -- A checker that gave a reader the type of the constructor's matching parameter by name
    -- would certify this.
  , ⟨"class C; attr_reader :z; def initialize(v); @v = v; end; end; C.new(1).z + 1",
      .seq [.class' "C" none (.seq [.send none "attr_reader" [.sym "z"] none,
              .def' "initialize" [.req "v"] (.vasgn .ivar "@v" (.var .lvar "v"))]),
            .send (some (.send (some (.send (some (.const "C")) "new" [.int 1] none))
              "z" [] none)) "+" [.int 1] none]⟩ ]

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
  -- Tier 9c: `&expr` as a block argument.
  | .blockpass e =>
    match e with
    | none => some (.blockpass none)
    | some x => (toRubyCore x).map (fun x' => .blockpass (some x'))
  | .send none m args (some blk) => do
    let args' ← args.mapM toRubyCore
    return .send none m args' (some (← toRubyCore blk))
  | .send (some r) m args (some blk) => do
    let r' ← toRubyCore r
    let args' ← args.mapM toRubyCore
    return .send (some r') m args' (some (← toRubyCore blk))
  | .self' => some .self'
  | .const n => some (.const n)
  -- Tier 13: a constant assignment (the controls' `X = 5`).
  | .casgn n e => (toRubyCore e).map (fun e' => .casgn n e')
  -- Tier 13c: `M::X` and `M::X = 4`.
  | .cpath (some b) n => (toRubyCore b).map (fun b' => .cpath (some b') n)
  -- Tier 13d: `alias new old` in a class body.
  | .alias' nw od => some (.alias' nw od)
  | .cpathAsgn (some b) n e => do
    let b' ← toRubyCore b
    return .cpathAsgn (some b') n (← toRubyCore e)
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
  -- Tier 10: `super` with no argument list.
  | .zsuper none => some (.zsuper none)
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
