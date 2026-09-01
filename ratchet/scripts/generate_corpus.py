#!/usr/bin/env python3
"""Generate the ratchet corpus (`../corpus/*.json` + `.rb` sources) from **real** Ruby,
run through the real desugarer (`harness/desugar-dt/bin/export-json`) -- not a
hand-authored AST. See `../AGENTS.md`.

Each rung is (id, tier, description, rb source, expect_validate, false_reason).
A rung carries **no certificate**: there is nothing for the checker to trust, so
`validate` either synthesizes the program's type itself or answers `false`. (Rungs used
to carry `claims` -- (subterm, Ty) pairs the checker was allowed to believe. That was a
soundness hole with a nice interface: a rung "climbed" by a claim was a rung nobody had
checked. Removed 2026-08-31; see `../AGENTS.md` §Claim-free.)

**Every rung's target is `expect_validate = True` unless `false_reason` is given.**
`false_reason` is one of:
  - "unsafe_program"   -- the program really does raise NoMethodError/ArgumentError/
                          TypeError when run. A checker that certified it is unsound.
  - "ty_language_gap"  -- the program is safe, but the current `Ty` grammar has no value
                          that describes the type in question at all (see
                          `Ratchet/Ty.lean`). Flagged, not silently left `False`.
`R()` asserts this pairing is never violated.

Regenerate with: `python3 scripts/generate_corpus.py` from `ratchet/`.
Then check the ladder with `scripts/run_ratchet.sh` (which also difftests every rung
against CRuby through the Lean semantics before reporting).
"""
import json
import os
import subprocess
import tempfile

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
RATCHET_DIR = os.path.normpath(os.path.join(SCRIPT_DIR, ".."))
HARNESS = os.path.normpath(os.path.join(RATCHET_DIR, "..", "harness", "desugar-dt", "bin", "export-json"))
CORPUS_DIR = os.path.join(RATCHET_DIR, "corpus")


def export(rb_source: str) -> dict:
    """Run the real desugarer on `rb_source`, returning the parsed `{"v":.., "ast":..}`."""
    with tempfile.NamedTemporaryFile(mode="w", suffix=".rb", delete=False) as f:
        f.write(rb_source)
        path = f.name
    try:
        proc = subprocess.run([HARNESS, path], capture_output=True, text=True, check=True)
    finally:
        os.unlink(path)
    return json.loads(proc.stdout)


# ---------------------------------------------------------------------------
# The rungs
# ---------------------------------------------------------------------------

RUNGS = []
FALSE_REASONS = {"unsafe_program", "ty_language_gap"}


def R(id_, tier, description, rb, *, expect_validate, false_reason=None):
    if expect_validate:
        assert false_reason is None, f"{id_}: false_reason set but expect_validate=True"
    else:
        assert false_reason in FALSE_REASONS, (
            f"{id_}: expect_validate=False needs false_reason in {FALSE_REASONS}")
    program = export(rb)
    RUNGS.append({
        "id": id_,
        "tier": tier,
        "description": description,
        "program": program,
        "expect_validate": expect_validate,
        "false_reason": false_reason,
        "_rb": rb,
    })


# --- Tier 1: literals (chk synthesizes all of these today) ------------------

R("int-lit", 1, "1 : Int.", "1\n", expect_validate=True)
R("bool-true", 1, "true : Bool.", "true\n", expect_validate=True)
R("bool-false", 1, "false : Bool.", "false\n", expect_validate=True)
R("str-lit", 1, '"hello" : an instance of String.', '"hello"\n', expect_validate=True)
R("sym-lit", 1, ":ok : Sym.", ":ok\n", expect_validate=True)
R("nil-lit", 1, "nil : Nil.", "nil\n", expect_validate=True)
R("flt-lit", 1, "1.5 : Float.", "1.5\n", expect_validate=True)
R("neg-int-lit", 1, "-5 desugars directly to a negative int literal, not a unary send.",
  "-5\n", expect_validate=True)

# --- Tier 2: arithmetic/string/bool sends (the hardcoded builtin table) ----

R("add", 2, "1 + 2, real desugared as a send, typed via the hardcoded Integer#+ rule.",
  "1 + 2\n", expect_validate=True)
R("sub", 2, "5 - 3 : Int.", "5 - 3\n", expect_validate=True)
R("mul", 2, "4 * 3 : Int.", "4 * 3\n", expect_validate=True)
R("div", 2, "10 / 2 : Int.", "10 / 2\n", expect_validate=True)
R("str-concat", 2, '"a" + "b", an instance of String.', '"a" + "b"\n', expect_validate=True)
R("cmp-lt", 2, "3 < 5 : Bool.", "3 < 5\n", expect_validate=True)
R("not-expr", 2, "!true desugars to a send of `!` with no args; Bool.",
  "!true\n", expect_validate=True)
R("bool-and", 2,
  "true && false desugars to a synthetic-temp vasgn + if, not a send -- and it "
  "type-checks with no special-casing at all, purely from the var/vasgn/if rules "
  "already needed for tier 3/4.",
  "true && false\n", expect_validate=True)
R("bool-or", 2, "false || true, same desugaring shape as bool-and.",
  "false || true\n", expect_validate=True)
R("bad-plus", 2,
  "1 + true is real, genuinely ill-typed Ruby: it raises TypeError when run, "
  "unconditionally. No certificate should ever certify it -- a checker that did "
  "would be unsound. Permanent negative target.",
  "1 + true\n", expect_validate=False, false_reason="unsafe_program")
R("to-s-call", 2, "5.to_s, an instance of String, via the universal Object#to_s rule.",
  "5.to_s\n", expect_validate=True)
R("eq-same-type", 2, "1 == 1 : Bool (both sides Int).", "1 == 1\n", expect_validate=True)
R("eq-different-type", 2,
  '1 == "a" is completely safe real Ruby -- `==` never raises, it just answers '
  "false for unrelated types. So the `==` rule chk needs is Object#== : (any) -> "
  "Bool, on *any* two receivers; a rule requiring both sides the same Ty would be "
  "conservative (it would reject this safe program) rather than sound-and-tight.",
  '1 == "a"\n',
  expect_validate=True)
R("unmodeled-builtin-zero-p", 2,
  "5.zero? is a real, total Integer method that is not in the hardcoded builtin "
  "table (unlike to_s): safe to run, and Int -> Bool every time. Climbing it means "
  "adding that row to PrimSig, justified against the semantics the way the five "
  "existing rows were -- there is no shortcut, and that is the point.",
  "5.zero?\n",
  expect_validate=True)
R("unknown-method", 2,
  "5.foo_bar_baz is a made-up method name -- Integer has no such method, so this "
  "really does raise NoMethodError when run. Permanent negative target, and the "
  "pair to unmodeled-builtin-zero-p: same shape, one real method and one not, so "
  "a checker cannot pass both by being generous about unknown selectors.",
  "5.foo_bar_baz\n", expect_validate=False, false_reason="unsafe_program")
R("cmp-le", 2, "1 <= 2 : Bool.", "1 <= 2\n", expect_validate=True)
R("cmp-ge", 2, "1 >= 2 : Bool.", "1 >= 2\n", expect_validate=True)
R("nil-eq-nil", 2, "nil == nil : Bool (both sides Nil).", "nil == nil\n", expect_validate=True)
R("nested-arith", 2, "(1 + 2) * 3 : Int -- the outer send's receiver is itself a send.",
  "(1 + 2) * 3\n", expect_validate=True)
R("str-length", 2,
  '"abc".length is another unmodeled-but-total builtin, on a different receiver '
  "type: String -> Int. Same climb as unmodeled-builtin-zero-p, and worth having "
  "both, since a PrimSig row is receiver-directed and the two exercise different "
  "rows.",
  '"abc".length\n',
  expect_validate=True)

# --- Tier 3: var / vasgn / seq ----------------------------------------------

R("simple-assign", 3, "x = 5; x + 1 : Int -- vasgn's type flows into the following var read.",
  "x = 5\nx + 1\n", expect_validate=True)
R("reassign-same-type", 3, "x = 1; x = 2; x + 3 : Int.",
  "x = 1\nx = 2\nx + 3\n", expect_validate=True)
R("reassign-different-type", 3,
  "x = 1; x = true; x : Bool -- real Ruby locals are not statically single-typed, "
  "and neither is this checker's flat environment: the second vasgn simply "
  "overwrites x's recorded type. This is not a gap, it's the correct behavior for "
  "a dynamically-typed language's locals.",
  "x = 1\nx = true\nx\n", expect_validate=True)
R("bare-undeclared-var", 3,
  "A bare `x`, never assigned anywhere, desugars to a `vcall` (a method-call "
  "attempt), not a `var` read. If run, it raises NameError -- but NameError is "
  "*not* in the type-error family (NoMethodError/ArgumentError/TypeError) this "
  "project's notion of type safety is defined over, exactly like ZeroDivisionError "
  "isn't (see tier 2's div rung in the old design notes). So by this project's own "
  "precise definition, this program is type-safe even though it crashes -- type "
  "safety here is not the same as crash-freedom. Claimed `Ty.any` on the vcall "
  "node, since it never actually produces a value for anything to depend on.",
  "x\n",
  expect_validate=True)
R("seq-multiple-stmts", 3, "x = 1; y = 2; x + y : Int.",
  "x = 1\ny = 2\nx + y\n", expect_validate=True)
R("assignment-chain", 3, "x = 1; y = x + 1; z = y + 1; z : Int -- a four-statement chain.",
  "x = 1\ny = x + 1\nz = y + 1\nz\n", expect_validate=True)

# --- Tier 4: conditionals ----------------------------------------------------

R("if-true-branch", 4, "if true then 1 else 2 end : Int.",
  "if true\n  1\nelse\n  2\nend\n", expect_validate=True)
R("if-no-else", 4,
  "if true then 1 end (no else): types as nilable(Int) via Ty.mkNilable.",
  "if true\n  1\nend\n", expect_validate=True)
R("if-condition-not-bool", 4,
  "if 5 then 1 else 2 end: Ruby's `if` accepts *any* value as a condition (only "
  "nil/false are falsy) and never raises over the condition's type -- unlike some "
  "statically typed languages. Requiring the condition to be exactly Bool would be "
  "an artificial restriction with no basis in real Ruby safety; a rebuilt `if'` "
  "rule should type the whole expression as joinTy(thenTy, elseTy) regardless of "
  "the condition's type. Both branches are Int here, so it joins trivially.",
  "if 5\n  1\nelse\n  2\nend\n", expect_validate=True)
R("if-branch-mismatch", 4,
  'if true then 1 else "a" end: Ty.joinTy has no *structural* case for (Int, an '
  "instance of String), but this is exactly the situation Ty.union exists for -- "
  "union(Int, an instance of String) is already expressible in the current "
  "grammar (see Ty.union's own docstring: currently inert on the checker path). "
  "No language gap -- what is missing is a joinTy that produces a union instead of "
  "answering none, so the if' rule can infer this type rather than reject it.",
  'if true\n  1\nelse\n  "a"\nend\n',
  expect_validate=True)
R("elsif-chain-mismatch", 4,
  "if/elsif/else desugars to nested if' nodes, so a union-producing joinTy has to "
  "compose with itself: the inner if' joins Int with an instance of String, and "
  "the outer joins Int with *that*. Getting union(Int, String) rather than "
  "union(Int, union(Int, String)) needs joinTy to absorb a repeat member -- the "
  "first place the ladder asks for a normal form on unions, and still no language "
  "gap.",
  'if true\n  1\nelsif false\n  2\nelse\n  "a"\nend\n',
  expect_validate=True)
R("if-nil-condition", 4,
  "if nil then 1 else 2 end: nil is falsy (always takes the else branch), and -- "
  "same reasoning as if-condition-not-bool -- never raises over the condition's "
  "type. Both branches Int, joins trivially.",
  "if nil\n  1\nelse\n  2\nend\n", expect_validate=True)
R("nested-if", 4, "if true then (if false then 1 else 2) else 3 end : Int.",
  "if true\n  if false\n    1\n  else\n    2\n  end\nelse\n  3\nend\n",
  expect_validate=True)
R("if-does-not-leak-reassignment", 4,
  'x = 1; if true; x = "hello"; end; x + 1 -- an UNSAFE program, and the rung that '
  "makes environment-joining at an `if` a soundness requirement rather than a "
  "precision nicety. The lone branch rebinds x to a String, so `x + 1` really does "
  "raise TypeError (verified under CRuby and under the model; that is why this "
  "corpus entry agrees). An `if` rule that discarded the branches' environments -- "
  "carrying the environment from *before* the if forward, which is what an earlier "
  "version of this checker did and what this rung's description used to claim was a "
  "harmless simplification -- would see x as Int and certify a program that raises. "
  "The correct rule joins the branch environments, giving x : union(Int, String) "
  "afterwards, which matches no PrimSig row, so `x + 1` is soundly rejected. The "
  "rung's name is kept for continuity with the ladder's history; what it now pins "
  "is that the leak MUST be modelled.",
  'x = 1\nif true\n  x = "hello"\nend\nx + 1\n',
  expect_validate=False, false_reason="unsafe_program")
R("elsif-chain", 4,
  "if/elsif/else desugars to nested if' nodes; a three-way chain with every "
  "branch Int types fine via nested joinTy calls.",
  "if true\n  1\nelsif false\n  2\nelse\n  3\nend\n", expect_validate=True)

# --- Tier 5: arrays / hashes --------------------------------------------------

R("array-int", 5, "[1, 2, 3] : an Array of Int.", "[1, 2, 3]\n", expect_validate=True)
R("array-empty", 5, "[] : an Array of Ty.any (nothing to unify an element type from).",
  "[]\n", expect_validate=True)
R("array-heterogeneous", 5,
  '[1, "a", true] is runtime-safe real Ruby (Ruby arrays are heterogeneous). '
  "Ty.arrayOf requires one element type structurally, but Ty.any already exists "
  "for exactly this: arrayOf(Ty.any) is expressible today. No language gap -- the "
  "array rule needs to join its element types (falling back to `any`) rather than "
  "requiring them equal.",
  '[1, "a", true]\n',
  expect_validate=True)
R("array-of-sends", 5, "[1 + 1, 2 + 2] : an Array of Int -- elements are checked recursively.",
  "[1 + 1, 2 + 2]\n", expect_validate=True)
R("hash-lit", 5,
  'A Hash literal types as the bare, unparameterised .cls "Hash" -- this Ty '
  "language has no parameterised Hash type the way it has arrayOf for Array "
  "(see Ty.lean's module docstring); every hash literal gets the same generic "
  "class type regardless of its key/value shapes. This does not block "
  "*validating* the literal itself, only precise reasoning about what a later "
  "index on it returns (see hash-index).",
  '{"a" => 1, "b" => 2}\n', expect_validate=True)
R("nested-array", 5, "[[1, 2], [3, 4]] : an Array of (an Array of Int).",
  "[[1, 2], [3, 4]]\n", expect_validate=True)
R("array-index", 5,
  "Indexing is just `#[]`, a send -- the real Expr has no dedicated index "
  "constructor. Typing it structurally means a receiver-directed rule reading the "
  "element type back off arrayOf Int (and, to be honest about out-of-range "
  "indices, returning nilable Int unless the index is a literal in range).",
  "[1, 2, 3][0]\n",
  expect_validate=True)
R("hash-index", 5,
  'Hash indexing is also just `#[]`, but there is nothing to read the value type '
  'off: Ty has no parameterised Hash type (see hash-lit), so the receiver\'s '
  '.cls "Hash" says nothing about what comes out. Typing this precisely needs a '
  'hashOf-style constructor; the honest intermediate answer is Ty.any.',
  '{"a" => 1}["a"]\n',
  expect_validate=True)

# --- Tier 6: top-level functions -------------------------------------------
# A `def'` node declares nothing to the checker on its own: typing a call means
# inferring the function's signature from its body and its params, then checking
# the call site against it. With no claims to lean on, the params are the hard
# part -- nothing in the syntax says `add`'s x and y are Ints, so either the body
# constrains them (x + y needs Integer#+, which PrimSig has) or the rule needs a
# real inference story. That is the tier's design question, and it is now asked
# honestly rather than answered by a declaration nobody checked.

R("simple-fun", 6,
  "def add(x, y) = x + y; add(1, 2) : Int. The signature (Int, Int) -> Int is not "
  "written anywhere in the program: it has to come from the body (x + y is only "
  "typeable when both are Int, given PrimSig) and be checked against the call "
  "site's arguments.",
  "def add(x, y)\n  x + y\nend\nadd(1, 2)\n", expect_validate=True)
R("fun-wrong-arity", 6,
  "The same add as simple-fun, called with one argument instead of two: this "
  "really does raise ArgumentError when run. Arity is visible in the syntax on "
  "both sides, so this is the cheapest soundness regression test in tier 6. "
  "Permanent negative target.",
  "def add(x, y)\n  x + y\nend\nadd(1)\n",
  expect_validate=False, false_reason="unsafe_program")
R("fun-body-mismatch", 6,
  "def bad(x) = x + true; bad(1) -- the body really does raise NoMethodError "
  "when called (Int has no matching + for Bool). The call site looks fine; the "
  "error is inside a body that is only reached by dispatch, so a checker has to "
  "look through the def to see it. Permanent negative target.",
  "def bad(x)\n  x + true\nend\nbad(1)\n",
  expect_validate=False, false_reason="unsafe_program")
R("fun-zero-arg", 6,
  "def get5 = 5; get5() : Int -- a zero-parameter function, so its signature is "
  "fixed by its body alone with no parameter inference needed at all. (This rung "
  "was `fun-dishonest-return-claim` while certificates existed: a safe program "
  "carrying a cert that claimed String for a body returning Int, targeting false "
  "so that a self-inconsistent certificate could never validate. With claims "
  "gone there is no cert to be dishonest, and what is left is the simplest "
  "function in the tier.)",
  "def get5\n  5\nend\nget5()\n",
  expect_validate=True)
R("fun-unknown-call", 6,
  "A call to undefined_fn, declared nowhere: this really does raise "
  "NoMethodError when run, exactly like tier 2's unknown-method. Permanent "
  "negative target.",
  "undefined_fn(1)\n", expect_validate=False, false_reason="unsafe_program")
R("fun-calling-another-fun", 6,
  "def inc(x) = x + 1; def twice(x) = inc(inc(x)); twice(3) : Int -- both "
  "top-level defs are collected into the function-signature table *before* any "
  "body is checked, so twice's body can call inc regardless of source order.",
  "def inc(x)\n  x + 1\nend\ndef twice(x)\n  inc(inc(x))\nend\ntwice(3)\n",
  expect_validate=True)
R("fun-three-params", 6,
  "def sum3(a, b, c) = a + b + c; sum3(1, 2, 3) : Int -- three required params, "
  "each a separate nested send.",
  "def sum3(a, b, c)\n  a + b + c\nend\nsum3(1, 2, 3)\n",
  expect_validate=True)
R("fun-returning-array", 6,
  "def make_pair(x, y) = [x, y]; make_pair(1, 2) : an Array of Int -- the return "
  "type is inferred from the body and is a structured Ty (arrayOf), not a scalar; "
  "the parameters are constrained only by the call site here, not by the body.",
  "def make_pair(x, y)\n  [x, y]\nend\nmake_pair(1, 2)\n",
  expect_validate=True)
R("fun-recursive-factorial", 6,
  "def fact(n) = if n <= 1 then 1 else n * fact(n - 1); fact(4) : Int -- fact "
  "calls itself by name, so its signature is needed to check the very body it is "
  "inferred from. Whatever replaces the old declaration table has to break that "
  "cycle (assume-then-verify, or a fixpoint), which is the real content of this "
  "rung.",
  "def fact(n)\n  if n <= 1\n    1\n  else\n    n * fact(n - 1)\n  end\nend\nfact(4)\n",
  expect_validate=True)

# --- Tier 7: classes ----------------------------------------------------------
# All safe, real Ruby -- expect_validate=True throughout. Every rung here needs the
# same three things from `chk`, none of them new Ty vocabulary (`cls`/`clsOf` cover
# instances vs. class objects fine): a declaration table over class bodies,
# ancestor-chain dispatch for sends against an instance type, and ivar types
# inferred from the writes in `initialize` and read back in other methods. What the
# tier used to do instead was carry an arrow-spine claim on every def'/defs node and
# a by-name claim on every ivar read -- i.e. hand the checker its answers, including
# the deliberately unsound simplification that an ivar's type is global by name
# rather than per class. See AGENTS.md §Frontier.

R("class-basic", 7,
  "class Point; def initialize(x, y); @x = x; @y = y; end; def getX; @x; end; "
  "end; Point.new(1, 2).getX -- construction, an ivar write in initialize, an "
  "ivar read in another method.",
  "class Point\n  def initialize(x, y)\n    @x = x\n    @y = y\n  end\n\n"
  "  def getX\n    @x\n  end\nend\n\nPoint.new(1, 2).getX\n",
  expect_validate=True)
R("class-method-with-param", 7,
  "class Counter; def initialize(n); @n = n; end; def add(k); @n + k; end; "
  "end; c = Counter.new(10); c.add(5) -- an instance stored in a local, then a "
  "method call taking its own argument.",
  "class Counter\n  def initialize(n)\n    @n = n\n  end\n\n"
  "  def add(k)\n    @n + k\n  end\nend\n\nc = Counter.new(10)\nc.add(5)\n",
  expect_validate=True)
R("class-two-getters", 7,
  "A class exposing two separate ivars through two separate getter methods, "
  "combined arithmetically at the call site.",
  "class Point\n  def initialize(x, y)\n    @x = x\n    @y = y\n  end\n\n"
  "  def getX\n    @x\n  end\n\n  def getY\n    @y\n  end\nend\n\n"
  "p = Point.new(3, 4)\np.getX + p.getY\n",
  expect_validate=True)
R("class-method-calls-method", 7,
  "A method (describe) calling another method (area) on the same object via "
  "an implicit-self `vcall` -- resolving that requires a rebuilt `vcall` rule to "
  "consult the current `self` type, not just a top-level function table.",
  "class Rect\n  def initialize(w, h)\n    @w = w\n    @h = h\n  end\n\n"
  "  def area\n    @w * @h\n  end\n\n  def describe\n    \"area=\" + area.to_s\n  end\n"
  "end\n\nRect.new(3, 4).describe\n",
  expect_validate=True)
R("class-inheritance-field", 7,
  "class Animal; def initialize(name); @name = name; end; def speak; @name; "
  "end; end; class Dog < Animal; end; Dog.new(\"Rex\").speak -- Dog inherits "
  "both the field and the method from Animal; a rebuilt dispatch rule needs to "
  "walk the parent chain to find speak declared on Animal.",
  "class Animal\n  def initialize(name)\n    @name = name\n  end\n\n"
  "  def speak\n    @name\n  end\nend\n\nclass Dog < Animal\nend\n\n"
  'Dog.new("Rex").speak\n',
  expect_validate=True)
R("class-inheritance-override", 7,
  "Dog overrides the speak method Animal also defines -- the two `def speak` "
  "nodes are disambiguated by scoping the search to each class' own body, "
  "since names alone collide.",
  'class Animal\n  def speak\n    "..."\n  end\nend\n\n'
  'class Dog < Animal\n  def speak\n    "Woof"\n  end\nend\n\n'
  "Dog.new.speak\n",
  expect_validate=True)
R("class-super-call", 7,
  "Triangle's initialize calls super(3) to delegate to Shape's initialize -- "
  "the `super'` head, which a rebuilt rule types as whatever the parent's matching "
  "method returns -- so the ancestor walk has to run at typing time, not just at "
  "dispatch time.",
  "class Shape\n  def initialize(sides)\n    @sides = sides\n  end\n\n"
  "  def sides\n    @sides\n  end\nend\n\n"
  "class Triangle < Shape\n  def initialize\n    super(3)\n  end\nend\n\n"
  "Triangle.new.sides\n",
  expect_validate=True)
R("class-multiple-instances", 7,
  "Two independent Point instances, their getX results combined.",
  "class Point\n  def initialize(x)\n    @x = x\n  end\n\n  def getX\n    @x\n  end\nend\n\n"
  "a = Point.new(1)\nb = Point.new(2)\na.getX + b.getX\n",
  expect_validate=True)
R("class-no-initialize", 7,
  "A class with no initialize at all -- real Ruby's default #new takes no "
  "arguments and returns the new instance; a rebuilt `.new` dispatch rule needs "
  "this as a fallback default when the class declares no `initialize`, not an "
  "error.",
  'class Greeter\n  def hi\n    "hi"\n  end\nend\n\nGreeter.new.hi\n',
  expect_validate=True)
R("class-ivar-lazy-nil", 7,
  "reveal reads @secret, which no method ever assigns -- real Ruby answers nil "
  "for an unset ivar rather than raising. So ivar inference cannot simply collect "
  "the writes: a read with no matching write is Nil, not an error.",
  "class Box\n  def reveal\n    @secret\n  end\nend\n\nBox.new.reveal\n",
  expect_validate=True)
R("class-array-of-instances", 7,
  "An array literal containing two constructed instances -- element type "
  "arrayOf(an instance of Point), which follows structurally once `.new` dispatch "
  "types a construction.",
  "class Point\n  def initialize(x)\n    @x = x\n  end\nend\n\n"
  "[Point.new(1), Point.new(2)]\n",
  expect_validate=True)
R("class-instance-in-hash", 7,
  "A hash literal whose value is a constructed instance -- typed as the bare "
  '.cls "Hash" regardless, same as any other hash literal.',
  'class Point\n  def initialize(x)\n    @x = x\n  end\nend\n\n'
  '{"origin" => Point.new(0)}\n',
  expect_validate=True)
R("class-factory-method", 7,
  "Point.origin is a singleton (self.) method on the class itself that "
  "constructs and returns an ordinary instance -- `defs` nested inside a "
  "`class'`, the same shape a module's `self.` methods use. Its body's bare "
  "`new(0, 0)` is a vcall/send dispatched with self bound to Ty.clsOf \"Point\", "
  "resolving to Point's own initialize.",
  "class Point\n  def initialize(x, y)\n    @x = x\n    @y = y\n  end\n\n"
  "  def self.origin\n    new(0, 0)\n  end\nend\n\nPoint.origin\n",
  expect_validate=True)
R("class-setter-method", 7,
  "grow reassigns @size to a new value derived from the old one -- an ivar "
  "vasgn whose right-hand side reads the same ivar.",
  "class Box\n  def initialize(size)\n    @size = size\n  end\n\n"
  "  def grow\n    @size = @size + 1\n  end\nend\n\nBox.new(1).grow\n",
  expect_validate=True)
R("class-instance-as-fun-arg", 7,
  "A top-level function taking an instance as a parameter (typed Ty.cls "
  '"Point" -- an ordinary Ty value usable anywhere, including a funSig\'s own '
  "param types) and calling a method on it -- mixing tier 6's function "
  "dispatch with a class instance.",
  "class Point\n  def initialize(x)\n    @x = x\n  end\n\n  def getX\n    @x\n  end\nend\n\n"
  "def describe(p)\n  p.getX\nend\n\ndescribe(Point.new(5))\n",
  expect_validate=True)
R("class-self-returning-method", 7,
  "myself returns bare `self`; the result is then chained into another method "
  "call -- typed as whatever self is bound to for an instance method "
  '(Ty.cls "Point"), so the `self\'` node needs the enclosing method\'s receiver '
  'type in scope.',
  "class Point\n  def initialize(x)\n    @x = x\n  end\n\n  def getX\n    @x\n  end\n\n"
  "  def myself\n    self\n  end\nend\n\nPoint.new(7).myself.getX\n",
  expect_validate=True)

# --- Tier 8: modules -----------------------------------------------------------
# Same treatment as tier 7, and no new Ty vocabulary either.
# `self.`-methods are `defs (self') name params body`, dispatched (once chk exists)
# as `Owner.method(...)` with self bound to Ty.clsOf owner -- symmetric with
# instance methods binding self to Ty.cls owner.

R("module-basic", 8, "module M; def self.foo; 1; end; end; M.foo : Int at runtime.",
  "module M\n  def self.foo\n    1\n  end\nend\n\nM.foo\n",
  expect_validate=True)
R("module-method-with-arg", 8,
  'module Greeter; def self.hello(name); "hi " + name; end; end; '
  'Greeter.hello("sam").',
  'module Greeter\n  def self.hello(name)\n    "hi " + name\n  end\nend\n\n'
  'Greeter.hello("sam")\n',
  expect_validate=True)
R("module-multiple-methods", 8,
  "A module with two independent singleton methods.",
  "module M\n  def self.foo\n    1\n  end\n\n  def self.bar\n    2\n  end\nend\n\n"
  "M.foo + M.bar\n",
  expect_validate=True)
R("module-method-calls-method", 8,
  "self.describe calls self.value, another singleton method on the same "
  "module, via an implicit-self `vcall` -- self bound to Ty.clsOf \"M\" inside "
  "a `self.` method, resolved the same way class-method-calls-method's `area` "
  "was.",
  "module M\n  def self.value\n    21\n  end\n\n  def self.describe\n    value * 2\n  end\nend\n\n"
  "M.describe\n",
  expect_validate=True)
R("module-with-arithmetic", 8,
  "A module method doing ordinary arithmetic on its arguments.",
  "module Calc\n  def self.add(a, b)\n    a + b\n  end\nend\n\nCalc.add(1, 2)\n",
  expect_validate=True)
R("module-calling-another-module", 8,
  "M1.foo calls M2.bar -- two separate modules, one calling into the other "
  "via `.const \"M2\"` typed Ty.clsOf \"M2\".",
  "module M2\n  def self.bar\n    10\n  end\nend\n\n"
  "module M1\n  def self.foo\n    M2.bar + 1\n  end\nend\n\nM1.foo\n",
  expect_validate=True)
R("module-returns-array", 8,
  "A module method returning an array literal.",
  "module M\n  def self.pair\n    [1, 2]\n  end\nend\n\nM.pair\n",
  expect_validate=True)
R("module-boolean-method", 8,
  "A module method returning the result of a comparison.",
  "module M\n  def self.positive?(n)\n    n > 0\n  end\nend\n\nM.positive?(5)\n",
  expect_validate=True)
R("module-nested-call-chain", 8,
  "M.greeting.length chains a module call into a builtin method call on its "
  "result, so the `.length` rule (tier 2's str-length) has to fire on a receiver "
  "type that came out of user-defined dispatch rather than a literal.",
  'module M\n  def self.greeting\n    "hi"\n  end\nend\n\nM.greeting.length\n',
  expect_validate=True)
R("module-passing-multiple-args", 8,
  "A module method taking three arguments.",
  "module M\n  def self.sum3(a, b, c)\n    a + b + c\n  end\nend\n\nM.sum3(1, 2, 3)\n",
  expect_validate=True)

# --- Tier 9: blocks, procs and lambdas ---------------------------------------
# Ruby's three callable literals, and the one place the desugarer is *most*
# uniform: `lambda { .. }`, `->(x) { .. }` and `proc { .. }` are all an ordinary
# `send none "lambda"/"proc" [] (block ..)` -- the block is the send's `blk`
# child, exactly the same node an iterator call like `[1,2].map { .. }` carries.
# So there is no separate "lambda expression" in Expr at all: typing this tier
# means typing (a) the `block` literal itself as an arrow, (b) the `call`/`[]`/
# `yield` elimination forms that apply one, and (c) the receiver-directed
# iterator rules (`Array#map`/`each`/`select`/`inject`/`sort_by`) that say what
# block a builtin passes its element to and what the whole send returns.
#
# The Ty vocabulary is already there: a callable's type is the same arrow spine a
# `def'` gets (`arrow_of([Int], Int)`), which is why nearly every rung here targets
# True. One thing this tier finds that the vocabulary *cannot* say:
#   - proc-vs-lambda arity discipline. A lambda is strict (`->(x){x}.call(1,2)`
#     raises ArgumentError -- the `lambda-arity-mismatch` rung, a real
#     unsafe_program); a proc is lenient, padding missing params with nil and
#     dropping extras. `arrow_of([Int, Int], Int)` describes both, so a checker
#     reading only the arrow would either reject the legal proc call or accept
#     the illegal lambda one. FLAGGED as the tier's one ty_language_gap
#     (`proc-arity-leniency`).
# And one that is a dispatch-design item rather than a gap: `&:to_s` needs a
# Symbol#to_proc rule (sym `s` over receiver `T` behaves as the arrow of T's `s`
# method) before an iterator rule has any arrow to work with.

R("lambda-zero-arity", 9,
  "The smallest callable literal: `lambda { 1 }` desugars to `send none "
  "\"lambda\" [] (block [] [] (int 1))` -- no new Expr head, just a send whose "
  "`blk` child is a block with no params. The type belongs to the *block* node "
  "and is an arrow spine with no params, arrow_of([], Int); `f.call` then "
  "eliminates it. (This is the same program the umbrella project's J31 semantic-"
  "axiom pilot uses.)",
  "f = lambda { 1 }\nf.call\n",
  expect_validate=True)
R("lambda-stabby-one-param", 9,
  "`->(x) { x + 1 }.call(2)`: the stabby-lambda syntax desugars to the *exact "
  "same* shape as `lambda { .. }` (`send none \"lambda\"`), so a checker needs "
  "one rule, not two. Nothing declares `x`'s type: it has to come from the body "
  "(`x + 1` is typeable only at Int, given PrimSig) or from the call site's "
  "argument -- the same parameter-inference question tier 6 asks about `def`.",
  "->(x) { x + 1 }.call(2)\n",
  expect_validate=True)
R("proc-basic", 9,
  "`proc { |x| x * 2 }` is the same send-with-block shape as lambda, differing "
  "only in the selector (\"proc\" vs \"lambda\"). Called at the arity it "
  "declares, a proc behaves exactly like a lambda, so the same arrow type is "
  "honest here -- contrast proc-arity-leniency, which is the case where it "
  "stops being honest.",
  "p = proc { |x| x * 2 }\np.call(3)\n",
  expect_validate=True)
R("proc-bracket-call", 9,
  "`p[3]` is proc invocation spelled as `#[]` -- and it desugars to an ordinary "
  "`send (var local p) \"[]\" [(int 3)]`, structurally identical to tier 5's "
  "array indexing. The elimination rule for an arrow-typed receiver therefore "
  "has to fire on `[]` as well as on `call`, and `[]` has to dispatch on the "
  "receiver's type (Array vs a callable), not on the selector alone.",
  "p = proc { |x| x * 2 }\np[3]\n",
  expect_validate=True)
R("block-each-int", 9,
  "The first *iterator* block: `[1,2,3].each { |x| x + 1 }`. The block is the "
  "send's `blk` child, and the rule that types it is receiver-directed -- "
  "Array#each feeds the block one element (Int, from the receiver's "
  "arrayOf Int) and returns the *receiver*, not the block's result.",
  "[1, 2, 3].each { |x| x + 1 }\n",
  expect_validate=True)
R("block-map-to-s", 9,
  "`[1,2,3].map { |n| n.to_s }`: unlike each, Array#map's result type is "
  "arrayOf(the block's *return* type) -- so the whole send is arrayOf(an "
  "instance of String) even though the receiver is arrayOf Int, and the "
  "iterator rule has to read the block's return type back out of the block.",
  '[1, 2, 3].map { |n| n.to_s }\n',
  expect_validate=True)
R("block-doend-with-block-local", 9,
  "A multi-statement do/end block that assigns a block-local `y`. The "
  "desugarer records `y` in the block node's *locals* slot (v5's fourth child), "
  "separately from its params -- so a block frame binds params and locals "
  "together, and `y` must not leak to the enclosing scope. Body is a `seq`, "
  "typed left to right, block's type is its last statement's.",
  "[1, 2].map do |x|\n  y = x * 2\n  y + 1\nend\n",
  expect_validate=True)
R("yield-arith", 9,
  "`yield` is its own Expr head, and it invokes the *enclosing method's* "
  "implicitly-passed block -- there is no variable naming it. Typing "
  "`yield(1) + yield(2)` inside `twice` therefore needs the block's arrow to be "
  "part of the method's own context, threaded from the call site's block "
  "literal: a real dependency of the callee's typing on the caller's argument, "
  "and the first rung where a method cannot be typed without its call site.",
  "def twice\n  yield(1) + yield(2)\nend\n\ntwice { |x| x * 10 }\n",
  expect_validate=True)
R("block-param-ampersand", 9,
  "`def run(&b)` reifies the passed block as an ordinary local `b` (a `pblock` "
  "param), which is then called with `b.call(5)` -- the same elimination form "
  "as a lambda's. This is the reified counterpart of yield-arith: the block "
  "arrives as a *value* with an arrow type, so `Param.block`'s type is exactly "
  "the type of the block literal at the call site.",
  "def run(&b)\n  b.call(5)\nend\n\nrun { |x| x + 1 }\n",
  expect_validate=True)
R("block-pass-symbol-to-proc", 9,
  "`[1,2].map(&:to_s)` has *no* block node at all: the desugarer produces "
  "`blockpass (sym to_s)`, and Ruby coerces the Symbol to a proc "
  "(Symbol#to_proc) at call time. So there is no block node to type and no arrow "
  "anywhere in the syntax: a checker needs a Symbol#to_proc rule (sym `s` used as "
  "a block over receiver `T` behaves as the arrow of T's `s` method) to "
  "manufacture one before the Array#map rule can fire at all.",
  '[1, 2].map(&:to_s)\n',
  expect_validate=True)
R("block-pass-lambda-variable", 9,
  "The other blockpass shape: `&double` where `double` is a local holding a "
  "lambda. Here the arrow *is* available -- `blockpass (var local double)` -- "
  "so the iterator rule can use the variable's own type as the block's type, with "
  "no coercion rule needed. Contrast block-pass-symbol-to-proc.",
  "double = ->(x) { x * 2 }\n[1, 2].map(&double)\n",
  expect_validate=True)
R("lambda-closure-capture", 9,
  "`n = 10; add_n = ->(x) { x + n }` -- the block body mentions a local bound "
  "in the *enclosing* scope. The block's arrow says nothing about `n`: typing "
  "the body requires the environment at the point of the literal, not just its "
  "params, which is the first rung on this ladder where a block cannot be "
  "typed in isolation.",
  "n = 10\nadd_n = ->(x) { x + n }\nadd_n.call(5)\n",
  expect_validate=True)
R("lambda-returns-lambda", 9,
  "Curried addition: `add = ->(x) { ->(y) { x + y } }`, eliminated by "
  "`add.call(1).call(2)`. The outer block's type is a *higher-order* arrow -- "
  "arrow_of([Int], arrow_of([Int], Int)) -- which the Ty spine can already "
  "state, since `arrow0`'s return is an arbitrary Ty. The inner block also "
  "captures the outer's `x` (closure capture again, one level in).",
  "add = ->(x) { ->(y) { x + y } }\nadd.call(1).call(2)\n",
  expect_validate=True)
R("lambda-as-argument", 9,
  "The other half of higher-order: a *method parameter* whose type is an "
  "arrow. `def apply(f, v); f.call(v); end` has signature "
  "arrow_of([arrow_of([Int], Int), Int], Int) -- an arrow nested in a param "
  "position rather than a return position -- and the call site passes a lambda "
  "literal, so the argument check is arrow-against-arrow.",
  "def apply(f, v)\n  f.call(v)\nend\n\napply(->(x) { x * 2 }, 5)\n",
  expect_validate=True)
R("block-nested-map", 9,
  "`[[1,2],[3,4]].map { |row| row.map { |x| x + 1 } }` -- a block literal "
  "inside a block literal, over a nested array. The outer block's param is "
  "arrayOf Int (the receiver's element type) and its return is arrayOf Int, "
  "making the whole send arrayOf(arrayOf Int): the iterator rule has to compose "
  "with itself, and `arrayOf` has to nest.",
  '[[1, 2], [3, 4]].map { |row| row.map { |x| x + 1 } }\n',
  expect_validate=True)
R("block-two-params-inject", 9,
  "`[1,2,3].inject(0) { |acc, x| acc + x }`: the first block in the corpus with "
  "*two* params, and the first whose param types come from two different places "
  "-- `acc` from the send's seed argument, `x` from the receiver's element "
  "type -- with the extra obligation that the block's return type must equal "
  "`acc`'s (that is what makes the fold well-typed at every step, not just the "
  "first).",
  '[1, 2, 3].inject(0) { |acc, x| acc + x }\n',
  expect_validate=True)
R("block-select-with-if", 9,
  "A predicate block whose body is a whole `if` expression: "
  "`[1,2,3,4].select { |x| if x > 2 then true else false end }`. Combines "
  "tier 4's join-the-branches rule *inside* a block body (both branches Bool, "
  "so the block is arrow_of([Int], Bool)) with Array#select's rule, which "
  "unlike map returns arrayOf(the *receiver's* element type) regardless of the "
  "block's return type.",
  '[1, 2, 3, 4].select { |x| if x > 2 then true else false end }\n',
  expect_validate=True)
R("block-sort-by-length", 9,
  '`["aaa","b"].sort_by { |s| s.length }` -- the block\'s param and return '
  "types differ (an instance of String in, Int out), the whole send is "
  "arrayOf String (like select, the receiver's element type), and the body "
  "needs tier 2's str-length rule for `#length`. Three separate rules "
  "interlocking on one line.",
  '["aaa", "b"].sort_by { |s| s.length }\n',
  expect_validate=True)
R("lambda-explicit-return", 9,
  "`doubler = ->(x) { return x * 2 }; doubler.call(3)` is 6, not a "
  "LocalJumpError: `return` inside "
  "a *lambda* returns from the lambda, locally. (The same `return` inside a "
  "proc or a bare block would return from the enclosing method instead -- a "
  "non-local jump.) So the arrow stays exactly arrow_of([Int], Int), but "
  "a checker must read the `return` against the lambda's own return type, and "
  "must know which of the three callable flavors it is inside to do so. "
  "(Wrapped in a method because a bare top-level `return` is a parse error, "
  "which incidentally pins the lambda inside a method body, exactly where the "
  "proc/block reading would differ.)",
  "def apply_twice\n  doubler = ->(x) { return x * 2 }\n  doubler.call(3)\nend\n\napply_twice\n",
  expect_validate=True)
R("block-bad-arith", 9,
  "`[1,2].each { |x| x + \"a\" }` really raises TypeError (\"String can't be "
  "coerced into Integer\") on the first element -- tier 2's bad-plus, moved "
  "inside a block body where the receiver's element type is what makes it "
  "ill-typed. Nothing about the block wrapper should launder it. Permanent "
  "negative target.",
  '[1, 2].each { |x| x + "a" }\n',
  expect_validate=False, false_reason="unsafe_program")
R("lambda-arity-mismatch", 9,
  "`->(x) { x }.call(1, 2)` raises ArgumentError (given 2, expected 1): lambda "
  "arity is *strict*. The arrow spine says exactly this -- one param -- so this "
  "is a rung a checker equipped with the arrow elimination rule should reject "
  "on its own, and no certificate should ever certify. Permanent negative "
  "target, and the honest half of the proc/lambda arity story.",
  "->(x) { x }.call(1, 2)\n",
  expect_validate=False, false_reason="unsafe_program")
R("proc-arity-leniency", 9,
  "The dishonest half. `proc { |x, y| x }.call(1)` is *legal* Ruby: a proc "
  "pads missing params with nil (y = nil) and drops extras, so this returns 1. "
  "But the only Ty that describes that block is "
  "arrow_of([Int, Int], Int), which says the call site is wrong -- and "
  "weakening it to arrow_of([Int, nilable Int], Int) still cannot express "
  "\"...and the second argument may simply be absent\", nor that an extra third "
  "argument is fine too. There is no Ty value describing proc arity discipline "
  "at all, so the rung cannot be honestly certified today. FLAGGED "
  "ty_language_gap: Ty needs optional/rest arity (the same missing "
  "constructor metaprog-method-missing-splat asks for, reached from the other "
  "direction).",
  "proc { |x, y| x }.call(1)\n",
  expect_validate=False, false_reason="ty_language_gap")

# --- Tier 10: metaprogramming -- LAST on the ladder --------------------------
# method_missing, class reopening, and mixins (include/extend/prepend). Real
# Ruby desugars all three to *ordinary constructs already in Expr* --
# include/extend/prepend are plain `send none "include"/... [const Module] none`
# calls (confirming the umbrella project's "everything is a message send" claim
# even for metaprogramming), and class reopening is just two `class'` nodes
# sharing a name. None of that needs new Ty vocabulary -- what it needs is a
# declaration table whose ancestor walk also follows mixins and reopenings, which
# is a `chk`-design extension (Frontier), not a type language gap.
#
# method_missing is different: its second parameter is a *rest* param (`*args`),
# and Ty's arrow spine (`arrow0`/`arrowCons`) has no vararg/rest-arity
# constructor -- there is no Ty value that describes a variadic signature at
# all. That is the one genuine ty_language_gap this tier finds;
# the fixed-arity method_missing rung right next to it shows the gap is
# specifically about rest params, not method_missing dispatch itself.

R("metaprog-class-reopening", 10,
  "Foo is defined via two separate `class' \"Foo\"` nodes, each contributing "
  "different methods -- the declaration table accumulates across both by "
  "name, the same way it would across any two top-level defs.",
  "class Foo\n  def a\n    1\n  end\nend\n\nclass Foo\n  def b\n    2\n  end\nend\n\n"
  "Foo.new.a + Foo.new.b\n",
  expect_validate=True)
R("metaprog-include", 10,
  "Person includes Greetable; greet, defined once inside the module, becomes "
  "callable as an instance method of Person. `include` desugars to an ordinary "
  "`send none \"include\" [const Greetable] none` inside Person's class body -- "
  "no special Expr head at all. A rebuilt ancestor walk needs to treat "
  "Greetable as an *additional* instance-method source for Person (distinct "
  "from superclass lookup), which is a dispatch-design extension, not a "
  "language gap: greet's signature is the same arrow-spine shape as any other "
  "method's.",
  "module Greetable\n  def greet\n    \"hi\"\n  end\nend\n\n"
  "class Person\n  include Greetable\nend\n\nPerson.new.greet\n",
  expect_validate=True)
R("metaprog-extend", 10,
  "Person extends Loud; shout becomes callable as a *singleton* method of "
  "Person (Person.shout), not an instance method -- `extend` is the same "
  "ordinary `send` shape as `include`, but the mixed-in methods land on the "
  "class's own singleton ancestry instead of its instance ancestry. A further "
  "dispatch-design extension (symmetric with `include`, on the other side), "
  "not a language gap.",
  "module Loud\n  def shout\n    \"LOUD\"\n  end\nend\n\n"
  "class Person\n  extend Loud\nend\n\nPerson.shout\n",
  expect_validate=True)
R("metaprog-prepend", 10,
  "Person prepends Logger, which defines its own speak calling `super`. "
  "prepend puts Logger *ahead* of Person in the ancestor chain, so "
  "Person.new.speak resolves to Logger#speak first, whose bare `super` (a "
  "`zsuper` node) forwards to the *next* speak in the chain -- Person's own. "
  "Typing this needs an MRO-aware `super'`/`zsuper` rule on top of the "
  "prepend-ordered ancestry -- a genuinely nontrivial dispatch-design item, but "
  "still no new Ty vocabulary: both speak methods have the same "
  "arrow_of([], an instance of String) shape as anywhere else.",
  "module Logger\n  def speak\n    \"logged: \" + super\n  end\nend\n\n"
  "class Person\n  prepend Logger\n  def speak\n    \"hi\"\n  end\nend\n\n"
  "Person.new.speak\n",
  expect_validate=True)
R("metaprog-method-missing-fixed-arity", 10,
  "Ghost declares method_missing with a single *required* param (no splat); "
  "calling an undeclared method (anything_at_all, with no arguments) dispatches "
  "to it with exactly one argument (the missed method's name, as a Sym) -- an "
  "arity Ty can honestly state: arrow_of([Sym], an instance of String). "
  "Needs a method_missing-fallback dispatch rule (try every declared method "
  "first, then method_missing if the class declares one) -- a dispatch-design "
  "extension, not a language gap, precisely because there is no rest param "
  "here. Contrast metaprog-method-missing-splat.",
  "class Ghost\n  def method_missing(name)\n    \"called \" + name.to_s\n  end\nend\n\n"
  "Ghost.new.anything_at_all\n",
  expect_validate=True)
R("metaprog-method-missing-splat", 10,
  "The idiomatic method_missing shape: `def method_missing(name, *args)`. Its "
  "true signature is 'one Sym, then zero or more of anything' -- and Ty's "
  "arrow spine (arrow0/arrowCons) has no vararg/rest-arity constructor at all. "
  "There is no Ty value that honestly describes this parameter list, not just "
  "no `chk` rule for it yet: arrow_of([Sym], ...) would be a lie about the real "
  "arity (it fits this one zero-extra-args call site while being wrong for "
  "`some_method(1, 2, 3)` elsewhere). FLAGGED ty_language_gap: Ty needs "
  "something like an `arrowRest (rest ret : Ty)` constructor, or modeling a rest "
  "param as `arrayOf Ty`, before this signature can be written down at all.",
  "class Ghost\n  def method_missing(name, *args)\n    \"called\"\n  end\nend\n\n"
  "Ghost.new.anything_at_all\n",
  expect_validate=False, false_reason="ty_language_gap")


# --- Tier 11: cross-cutting -- features in concert ---------------------------
#
# Every tier above this one adds a *feature*. This one adds no feature at all: each rung
# is a combination of features that already have rules, and it exists because the ladder
# is corpus-driven and therefore blind to exactly that. Tier 7 gave instance dispatch and
# tier 9 gave blocks-passed-to-methods; nothing in either tier passes a block to an
# instance method, so `A.new.a { |v| v }` had no rule and nobody noticed. The first rung
# below is that program, reported by a human writing ordinary Ruby.
#
# One rung here already earned its keep before it was written: sketching `xc-block-
# retypes-capture` found a real unsoundness in the committed tier-9 rules (a block
# captures locals by reference, and the call rules were discarding the body's outgoing
# environment). See ../implementation-notes.md clink 11.
#
# Deliberately NOT here: `super { |x| ... }`. It is ordinary Ruby that CRuby runs fine,
# but it is outside the *Lean semantics* fragment ("zsuper with an explicit block"), so a
# rung for it would be a type attached to a program the model cannot execute -- which is
# the one thing scripts/run_agreement.sh exists to prevent. It is a demand on ../lean/,
# not on this checker, and is recorded in AGENTS.md §Frontier instead.

R("xc-class-block-param", 11,
  "class A; def a(&blk); blk.call(3); end; end; A.new.a { |v| v } -- REPORTED BY A HUMAN, "
  "and the reason this tier exists. Two independent blockers, both of them restrictions "
  "introduced deliberately in earlier tiers, neither of them an unmodeled feature. (1) No "
  "rule covers an explicit-receiver send that carries a block: callMethod (tier 7) requires "
  "blk = none and callDefBlk (tier 9b) requires an implicit receiver, so this program "
  "matches nothing -- and removing the block, or moving the def to top level, makes each "
  "half validate on its own. (2) Behind it, closCall requires selfTy = none, so `blk.call` "
  "*inside an instance method body* would still be rejected even with (1) fixed; that one is "
  "documented (clink 9) and its fix is to put selfTy into Ty.clos beside the captured "
  "locals. Safe Ruby returning 3, so this is conservative, not unsound.",
  "class A\n  def a(&blk)\n    blk.call(3)\n  end\nend\n\n\nA.new.a { |v| v }\n",
  expect_validate=True)

R("xc-class-yield-ivar", 11,
  "An instance method that yields, with the block reading an instance variable through the "
  "receiver's ivar spine: Counter.new(5).bump { |x| x + 1 } : Int. Needs tier 7's ivar spine "
  "and tier 9b's Ctx.blockTy at the same time -- and needs blockTy to be set by a *dispatch* "
  "rule rather than only by callDefBlk, which is the tier-7-x-tier-9b gap again from the "
  "yield side rather than the &blk side.",
  "class Counter\n  def initialize(n)\n    @n = n\n  end\n\n  def bump\n    yield(@n)\n"
  "  end\nend\n\n\nCounter.new(5).bump { |x| x + 1 }\n",
  expect_validate=True)

R("xc-lambda-in-ivar", 11,
  "A callable stored in an instance variable and invoked through a method: "
  "Box.new(lambda { |x| x * 2 }).apply(4) : Int. The interesting part is that the ivar "
  "spine has to hold a Ty.clos -- tier 7's Ty.inst carrying tier 9's callable -- so the "
  "closure's index and captured environment survive inside an object's type. Also needs "
  "closCall to work with selfTy set, since @f.call happens inside a method body.",
  "class Box\n  def initialize(f)\n    @f = f\n  end\n\n  def apply(v)\n    @f.call(v)\n"
  "  end\nend\n\n\nBox.new(lambda { |x| x * 2 }).apply(4)\n",
  expect_validate=True)

R("xc-module-yield", 11,
  "A module singleton method that yields: Runner.twice { |x| x * 10 } : Int. Tier 8's "
  "callSMethod does not set Ctx.blockTy, and there is no rule for an explicit-receiver send "
  "with a block, so this fails for the same reason xc-class-block-param does -- one tier "
  "over. Worth having separately because the fix for a `.clsOf` receiver is not literally "
  "the fix for an `.inst` one.",
  "module Runner\n  def self.twice\n    yield(1) + yield(2)\n  end\nend\n\n\n"
  "Runner.twice { |x| x * 10 }\n",
  expect_validate=True)

R("xc-inherit-implicit-block", 11,
  'Child#show calls an *inherited* method with a block, by bare name: wrap { 7 }, where '
  'Base#wrap is "[" + yield.to_s + "]". Three tiers in concert -- tier 7\'s mroGet? walk to '
  "find wrap on Base, tier 9b's blockTy for the yield inside it, and tier 8-style "
  "implicit-self dispatch (selfCall) which today handles only a zero-argument vcall with no "
  "block. String result, so it also exercises strAdd over a yielded value.",
  'class Base\n  def wrap\n    "[" + yield.to_s + "]"\n  end\nend\n\nclass Child < Base\n'
  "  def show\n    wrap { 7 }\n  end\nend\n\n\nChild.new.show\n",
  expect_validate=True)

R("xc-block-retypes-capture", 11,
  "def t; yield(1); end; a = 1; t { |x| a = \"s\" }; a + 1 -- an UNSAFE program, and the one "
  "that found a real soundness bug in the committed tier-9 rules. A Ruby block captures "
  "locals **by reference**, so the assignment inside it is visible afterwards and `a + 1` "
  "really raises TypeError. Ty.clos captures by *value* into a spine and the call rules "
  "discarded the body's outgoing environment, so the checker still believed a : Int and "
  "certified this. Fixed by the capIntact premise on closCall/yieldExpr -- the exact analogue "
  "of callMethod's no-retyping premise for instance variables, and the same general rule: a "
  "callee may not retype state its caller can still see. Permanent negative target; it is "
  "what stops that fix from being quietly reverted.",
  'def t\n  yield(1)\nend\n\na = 1\nt { |x| a = "s" }\na + 1\n',
  expect_validate=False, false_reason="unsafe_program")

R("xc-block-accumulates-capture", 11,
  "def t; yield(1); end; a = 1; t { |x| a = a + x }; a + 1 : Int -- the boundary case for "
  "capIntact, and the reason it compares *types* rather than forbidding assignment. The "
  "block really does mutate a captured local, and that is fine because it leaves the type "
  "alone: same shape as class-setter-method for ivars. Sits next to "
  "xc-block-retypes-capture on purpose -- the two differ only in the assigned type.",
  "def t\n  yield(1)\nend\n\na = 1\nt { |x| a = a + x }\na + 1\n",
  expect_validate=True)

R("xc-ivar-array-map", 11,
  "Shelf.new([1, 2]).names, where names is @items.map { |i| i.to_s } : an Array of String. "
  "Four tiers at once: tier 5's array literal and elemTy, tier 7's ivar spine holding an "
  "arrayOf, tier 9c's still-unwritten higher-order rule for Array#map, and the tier-7-x-9 "
  "gap for a block reaching an instance method. The deepest rung in the corpus by feature "
  "count.",
  "class Shelf\n  def initialize(items)\n    @items = items\n  end\n\n  def names\n"
  "    @items.map { |i| i.to_s }\n  end\nend\n\n\nShelf.new([1, 2]).names\n",
  expect_validate=True)

R("xc-module-applies-lambda", 11,
  "Twice.apply(lambda { |x| x + 1 }, 5) : Int, where the module method calls its argument "
  "twice: f.call(f.call(v)). The blocker is precisely closCall's selfTy = none premise -- "
  "inside a singleton method body selfTy is some (.clsOf \"Twice\"), so the callable cannot "
  "be invoked even though it was created at top level and captured nothing. The cleanest "
  "single demand in this tier for putting selfTy into Ty.clos.",
  "module Twice\n  def self.apply(f, v)\n    f.call(f.call(v))\n  end\nend\n\n\n"
  "Twice.apply(lambda { |x| x + 1 }, 5)\n",
  expect_validate=True)

R("xc-block-retypes-ivar", 11,
  "An UNSAFE program: a block retypes an *instance variable* rather than a local. "
  "`run { @x = \"s\" }` then `@x + 1` really raises TypeError. The ivar twin of "
  "xc-block-retypes-capture, and it checks a different premise: the block body is judged "
  "with the enclosing ivar spine, and closCall/yieldExpr require that spine to come back "
  "unchanged. Permanent negative target.",
  'class C\n  def initialize(x)\n    @x = x\n  end\n\n  def run\n    yield\n  end\n\n'
  '  def go\n    run { @x = "s" }\n    @x + 1\n  end\nend\n\n\nC.new(1).go\n',
  expect_validate=False, false_reason="unsafe_program")


# --- Tier 12: narrowing -- making `nilable` and `union` usable ---------------
#
# `Ty.nilable` and `Ty.union` are the two types this checker can *produce* but has no way
# to *consume*: no PrimSig row takes either as a receiver and neither is EqSafe, which is
# why producing one is trivially sound (Judge.if's docstring) and why almost every
# interesting program that produces one becomes untypeable. Tiers 4 and 5 recorded that
# cost in three negative controls; this tier turns the cost into pressure.
#
# Every rung here is safe Ruby a human would write without thinking, and every one needs
# the checker to *refine a type inside a branch*. Read the demands off the DESUGARED form,
# not the surface syntax -- that is the whole lesson of this tier, and three rungs exist
# specifically because the two disagree:
#
#   * `case v when Integer` becomes a temp `__dt_t1 = v` plus `Integer === __dt_t1`, and
#     the branch bodies use **v, not the temp**. Narrowing the variable named in the
#     condition therefore refines the wrong one. Narrowing needs an aliasing story, not a
#     syntactic rewrite.
#   * `if x && x > 1` puts a whole `seq` (temp assignment + nested if) in the *condition*
#     position, and the then-branch again uses `x` rather than the temp. Refinement has to
#     flow out of a compound condition expression.
#   * `return 0 if x.nil?` is a `.ret` inside an `if` inside a `seq`, and the narrowing it
#     licenses applies to *everything after* the guard -- refinement by elimination of a
#     branch that leaves. That also needs JudgeSeq to stop taking the last statement's type
#     unconditionally (bodyResult's docstring records why the naive `.ret` rule is unsound).
#
# Two further demands entailed by narrowing but not themselves narrowing:
#   * **Builtin class constants.** `Integer`/`String` as receivers are `Expr.const`, and
#     Judge.constCls only types constants for classes the program *declared*. Every
#     is_a?/=== rung needs `.clsOf` for a builtin.
#   * **A `nil?` row.** `nil?` is total on every object, so its PrimSig row wants `.any` on
#     the receiver -- the wildcard clink 1 deliberately declined to admit for `!`.
#
# The two negative rungs keep the capability honest once it exists: narrow-backwards-unsafe
# is certified by any implementation that refines the branches the wrong way round, and
# narrow-absent-unsafe by any implementation that refines without a guard at all.

R("narrow-nilable-truthy", 12,
  "a = [1,2,3]; x = a[0]; if x then x + 1 else 0 end : Int. The simplest possible narrowing "
  "rung and the right first one: the desugared condition is a bare `var local x`, so no "
  "aliasing and no new PrimSig row are involved. Array#[] gives `nilable Int` (correctly -- "
  "an out-of-range index is nil), and `nilable Int` matches no arithmetic row, so the "
  "then-branch must see `x : Int` or nothing types. Note the shape of the obligation: "
  "truthiness excludes *both* nil and false, so narrowing `nilable T` on a truthy test is "
  "sound for any T that is not Bool -- and for `nilable Bool` it would have to keep `false`.",
  "a = [1, 2, 3]\nx = a[0]\nif x\n  x + 1\nelse\n  0\nend\n",
  expect_validate=True)

R("narrow-nilable-nil-check", 12,
  "if x.nil? then 0 else x + 10 end : Int -- narrowing in the **else** branch, which is a "
  "different rule from the truthy one and not merely its mirror: the condition is a send "
  "(`send (var x) \"nil?\" []`), so the checker has to recognise a *method call* as a type "
  "test. Also forces a PrimSig row for `nil?`, whose honest receiver is `.any` -- the "
  "wildcard receiver clink 1 explicitly declined to admit for `!`. This rung is where that "
  "decision has to be revisited.",
  "a = [1, 2, 3]\nx = a[1]\nif x.nil?\n  0\nelse\n  x + 10\nend\n",
  expect_validate=True)

R("narrow-union-is-a", 12,
  "The flagship union rung. `pick(flag)` joins Int and String, so `v : union(Int, String)` "
  "by joinT -- a type this checker produces today and can do nothing with. Then "
  "`if v.is_a?(Integer)` must refine it to Int in the then-branch and String in the else, "
  "because the branches use different operators (`v + 1` vs `v + \"!\"`) and neither "
  "typechecks at the union. Demands: `.clsOf` for the builtin constant Integer, an `is_a?` "
  "row, and refinement of a union by class in both directions at once.",
  'def pick(flag)\n  if flag\n    1\n  else\n    "s"\n  end\nend\n\nv = pick(true)\n'
  'if v.is_a?(Integer)\n  v + 1\nelse\n  v + "!"\nend\n',
  expect_validate=True)

R("narrow-union-case-when", 12,
  "`case v when Integer ... when String ... end` -- the idiomatic Ruby form, and the rung "
  "that proves narrowing cannot be a syntactic rewrite. The desugarer emits a temp: "
  "`__dt_t1 = v`, then nested ifs on `Integer === __dt_t1`, and **the branch bodies use v, "
  "not __dt_t1**. So refining the variable named in the condition refines the wrong one, and "
  "the checker has to know the temp and v hold the same value. Narrowing needs an aliasing "
  "story. Also needs a `===` row on a class object, which is is_a? with its arguments "
  "swapped.",
  'def pick(flag)\n  if flag\n    1\n  else\n    "s"\n  end\nend\n\nv = pick(false)\n'
  'case v\nwhen Integer\n  v * 2\nwhen String\n  v + v\nelse\n  0\nend\n',
  expect_validate=True)

R("narrow-union-in-ivar", 12,
  "A union living in an **instance variable**, narrowed inside a method: Holder's initialize "
  "assigns @v at Int or String depending on a parameter, and describe narrows it back apart. "
  "Two capabilities at once, and the first is a change to an existing rule: Judge.if' "
  "currently requires the two branches to *agree* on the ivar spine (I1 = I2), so this "
  "program cannot even produce the union -- that premise has to become a join once narrowing "
  "exists to consume one. Then the narrowing has to refine an ivar rather than a local, "
  "which is a different environment.",
  'class Holder\n  def initialize(flag)\n    if flag\n      @v = 1\n    else\n      @v = "s"\n'
  '    end\n  end\n\n  def describe\n    if @v.is_a?(Integer)\n      @v + 1\n    else\n'
  '      @v + "!"\n    end\n  end\nend\n\n\nHolder.new(true).describe\n',
  expect_validate=True)

R("narrow-union-subclass", 12,
  "Narrowing a union of *user classes* by is_a?, where the two arms are related by "
  "inheritance: union(inst Dog, inst Animal) refined to Dog in one branch to reach #fetch, "
  "and left alone in the other to reach the inherited #speak. Tier 7's mroGet? walk in "
  "concert with narrowing -- and the rung where subTy finally has something to do, since "
  "`is_a?(Animal)` must *not* narrow a Dog away while `is_a?(Dog)` must narrow an Animal. "
  "subTy has sat in Ty.lean unused since the port and this is the first rung that needs it.",
  'class Animal\n  def speak\n    "..."\n  end\nend\n\nclass Dog < Animal\n  def fetch\n'
  '    "ball"\n  end\nend\n\ndef make(flag)\n  if flag\n    Dog.new\n  else\n    Animal.new\n'
  '  end\nend\n\nv = make(true)\nif v.is_a?(Dog)\n  v.fetch\nelse\n  v.speak\nend\n',
  expect_validate=True)

R("narrow-guard-clause", 12,
  "def first_or_zero(a); x = a[0]; return 0 if x.nil?; x + 1; end : Int -- the idiomatic "
  "guard clause, and the hardest narrowing shape here. The refinement is licensed not by "
  "being inside a branch but by the *other* branch having left: after the guard, x cannot be "
  "nil because that path returned. So this needs narrowing by elimination, plus a real story "
  "for `.ret` in statement position -- JudgeSeq takes the last statement's type "
  "unconditionally today, and bodyResult's docstring records why the naive `.ret` rule is "
  "unsound. Also the first rung whose narrowing crosses a statement boundary rather than "
  "living inside one expression.",
  "def first_or_zero(a)\n  x = a[0]\n  return 0 if x.nil?\n  x + 1\nend\n\n\n"
  "first_or_zero([5])\n",
  expect_validate=True)

R("narrow-and-guard", 12,
  "`if x && x > 1` -- narrowing that has to flow out of a **compound condition**. `&&` "
  "desugars to a temp plus a nested if, so the outer if's condition position holds an entire "
  "`seq`, and the then-branch uses `x` rather than the temp. Two things follow: the checker "
  "cannot read the tested variable off the condition's syntax, and the refinement "
  "established inside the condition has to survive being carried out of it. Note also that "
  "`x > 1` inside the condition already needs x narrowed -- the refinement is used in the "
  "same expression that establishes it.",
  "a = [3]\nx = a[0]\nif x && x > 1\n  x + 1\nelse\n  0\nend\n",
  expect_validate=True)

R("narrow-nilable-and-union", 12,
  "arr = [1, \"a\"]; v = arr[0]; if v.is_a?(Integer) ... -- both layers at once, and the rung "
  "that turned out to be a **Ty language gap** rather than a demand on narrowing. elemTy joins "
  "the heterogeneous literal to `union(Int, String)`, Array#[] wraps that in `nilable`, so v is "
  "`nilable (union Int String)`. The then-branch is fine -- is_a?(Integer) excludes nil *and* "
  "String in one step, which is the case showing refinement is a filter over a set of "
  "possibilities. The **else**-branch is not: notATy leaves `nilable (cls String)`, because "
  "`nil.is_a?(Integer)` is false too, so `v + \"!\"` would be `nil + \"!\"` and raise "
  "NoMethodError. This program is safe only because *this* array has an element at index 0, "
  "and no `Ty` here can say that: `arrayOf` carries an element type and no **length**. A "
  "sound checker must reject it, so the target is false -- see AGENTS.md section Ty language "
  "gaps for the missing constructor.",
  'arr = [1, "a"]\nv = arr[0]\nif v.is_a?(Integer)\n  v + 1\nelse\n  v + "!"\nend\n',
  expect_validate=False, false_reason="ty_language_gap")

R("narrow-in-block", 12,
  "Narrowing inside a block body, in concert with tier 9c's iterators and clink 11's "
  "capIntact: `t.each do |x| y = [10,20][x]; if y then s = s + y end end`. The nilable comes "
  "from Array#[] inside the block, the narrowing happens in the block's own environment, and "
  "the accumulation into the captured `s` is legal only because it preserves s's type -- the "
  "boundary xc-block-accumulates-capture pins. Deliberately the messiest rung in the tier.",
  "t = [1, 2]\ns = 0\nt.each do |x|\n  y = [10, 20][x]\n  if y\n    s = s + y\n  end\n"
  "end\ns\n",
  expect_validate=True)

R("narrow-backwards-unsafe", 12,
  "An UNSAFE program, and the control that keeps narrowing honest: the branches use the "
  "*wrong* refinement (`v + \"!\"` where v was narrowed to Integer, `v + 1` where it was "
  "narrowed to String). pick(false) returns \"s\", so the else branch runs and `\"s\" + 1` "
  "really raises TypeError. Any implementation that refines the two branches the wrong way "
  "round certifies this, which is exactly the bug a narrowing rule is most likely to have. "
  "Permanent negative target.",
  'def pick(flag)\n  if flag\n    1\n  else\n    "s"\n  end\nend\n\nv = pick(false)\n'
  'if v.is_a?(Integer)\n  v + "!"\nelse\n  v + 1\nend\n',
  expect_validate=False, false_reason="unsafe_program")

R("narrow-absent-unsafe", 12,
  "An UNSAFE program: a = []; x = a[0]; x + 1 really raises NoMethodError (\"undefined "
  "method '+' for nil\"), because the array is empty and x is nil. The control for narrowing "
  "being *required* rather than assumed -- an implementation that treated `nilable T` as T "
  "wherever convenient would certify it. Note this is narrow-nilable-truthy with the guard "
  "deleted, which is the point: the guard is what makes that rung safe, not the indexing. "
  "Permanent negative target.",
  "a = []\nx = a[0]\nx + 1\n",
  expect_validate=False, false_reason="unsafe_program")


# ---------------------------------------------------------------------------

def main():
    os.makedirs(CORPUS_DIR, exist_ok=True)
    for old in os.listdir(CORPUS_DIR):
        if old.endswith(".json") or old.endswith(".rb"):
            os.remove(os.path.join(CORPUS_DIR, old))

    for i, rung in enumerate(RUNGS, start=1):
        base = f"{i:03d}-{rung['id']}"
        rb_source = rung.pop("_rb")
        with open(os.path.join(CORPUS_DIR, f"{base}.rb"), "w") as f:
            f.write(rb_source)
        json_path = os.path.join(CORPUS_DIR, f"{base}.json")
        with open(json_path, "w") as f:
            json.dump(rung, f, indent=2)
            f.write("\n")
    print(f"wrote {len(RUNGS)} corpus entries to {CORPUS_DIR}")


if __name__ == "__main__":
    main()
