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


# ===========================================================================
# Tiers 13-19: the Homebrew slice
#
# Everything above this line is Ruby written *for* the ladder, one feature per
# rung. Everything below it is driven by a **target**: the eight files of
# `homebrew/PLAN.md` §2 -- Homebrew's version + vulnerability stack, the slice
# that already runs in the model at 351/355 harvested spec examples and as one
# linked 2,159-line program (`homebrew/slice-driver/`).
#
# The ordering is the same one the ladder has used throughout, applied to a
# corpus nobody here chose: **tiers 13-17 are the syntactic forms the slice uses
# and the corpus did not**, one rung per form, measured rather than guessed (a
# node-head census of the linked slice's desugared AST against every corpus
# rung's -- see `../AGENTS.md` §The syntactic gap); **tier 18 is the eight files
# themselves**, each with a driver that exercises its own API; **tier 19 is the
# whole linked slice**. So the ladder now ends where the target does, and the
# gap between "we type this feature" and "we type this program" is a tier
# boundary rather than a research question.
# ===========================================================================

# --- Tier 13: constants and scoped names -----------------------------------
#
# 928 `const` reads, 155 `cpath`s and 54 `casgn`s in the linked slice; the
# corpus had `const` (as a class name in `C.new`) and neither of the others.
# What is new is that a constant is a *binding* -- `casgn` writes one, `cpath`
# reads one out of a namespace -- so the checker needs a constant environment
# beside `Env`, and it has to be threaded through `class'`/`module'` bodies
# rather than being a whole-program table, because `M::X` and a bare `X` inside
# `M` are the same binding reached two ways.

R("const-assign-read", 13,
  "LIMIT = 10; LIMIT + 1 : Int -- the smallest thing a constant is, and the one that "
  "says what the tier costs: `casgn` writes a binding the rest of the program reads, so "
  "`Judge` needs a constant environment. It cannot be folded into `Env` (locals shadow "
  "per-scope and constants do not) and it cannot be a pre-pass table (`chk` would then "
  "accept `X + 1; X = 10`, which raises NameError).",
  "LIMIT = 10\nLIMIT + 1\n", expect_validate=True)

R("const-in-class", 13,
  "A constant declared in a class body and read from an instance method -- the shape "
  "`vulns/cvss.rb` uses for all six of its metric tables. The read is a bare `const` "
  "node with no path, so resolving it needs the *enclosing* declaration, which is what "
  "makes the constant environment scope-threaded rather than flat.",
  "class Box\n  SIZE = 3\n\n  def size\n    SIZE\n  end\nend\n\nBox.new.size\n",
  expect_validate=True)

R("const-scoped-read", 13,
  "M::X -- the `cpath` node, 155 of them in the slice. Ruby has no member-access "
  "syntax for constants: `cpath` is its own head with an optional base expression, so "
  "this is not a `send` and no `PrimSig` row can reach it.",
  'module M\n  X = 5\nend\n\nM::X + 1\n', expect_validate=True)

R("const-scoped-nested", 13,
  "Outer::Inner::Y -- a `cpath` whose base is another `cpath`, which is how every name "
  "in the slice is spelled (`Homebrew::Vulns::Semver`). The rule has to be recursive in "
  "its base, and the base's type is a namespace rather than a value: `Ty.clsOf` covers "
  "a class object, and a module used purely as a namespace is the same thing (tier 8).",
  'module Outer\n  module Inner\n    Y = "deep"\n  end\nend\n\nOuter::Inner::Y\n',
  expect_validate=True)

R("const-scoped-class-ref", 13,
  "M::Box.new(7).get -- a `cpath` in *receiver* position, resolving to a class object "
  "that is then allocated. This is the join between tier 13 and tier 7: `newInst` reads "
  "the class off the receiver's `Ty.clsOf`, so it needs `cpath` to produce one, and "
  "every `Purl.new`/`Version.new` in the slice is this shape.",
  'module M\n  class Box\n    def initialize(v)\n      @v = v\n    end\n\n    def get\n'
  '      @v\n    end\n  end\nend\n\nM::Box.new(7).get\n', expect_validate=True)

R("const-scoped-assign", 13,
  "M::X = 4 -- `cpath_asgn`, the write half. Rare in the slice (a constant is normally "
  "written from inside its own namespace) but the constructor exists in `Expr` and the "
  "read rule is unsound without it: a checker that treats the constant environment as "
  "fixed after the declaration bodies run is wrong about this program.",
  'module M\nend\n\nM::X = 4\nM::X + 1\n', expect_validate=True)

R("const-frozen-array", 13,
  'NAMES = ["a", "b"].freeze; NAMES[0] -- the shape of every table in the slice '
  "(`BASE_METRICS`, `TAG_PATTERNS`, `LOWERCASE_PATH_HOSTS`). Two demands: `Object#freeze` "
  "returns the receiver at the receiver's own type, and the constant's type is the "
  "*initialiser's* type, which is where constant inference differs from a local -- there "
  "is one assignment, so there is a principal type and no join.",
  'NAMES = ["a", "b"].freeze\nNAMES[0]\n', expect_validate=True)

R("const-frozen-hash", 13,
  "The same for a hash. Notable because tier 5 left `Hash` unparameterised (`.cls "
  '"Hash"`), so `TABLE["a"]` is `.any` -- and the slice reads its frozen tables with '
  "`fetch`, whose result then flows into arithmetic (`cvss.rb`'s `AV.fetch(...)` is a "
  "Float). A `Hash` with no key/value parameters cannot type that chain, which is the "
  "first concrete demand for a parameterised hash type in the whole ladder.",
  'TABLE = { "a" => 1, "b" => 2 }.freeze\nTABLE["a"]\n', expect_validate=True)

R("const-private-constant", 13,
  "`private_constant :SECRET` -- 30 sites in the slice, on essentially every constant "
  "it declares. It is an ordinary implicit-self `send` in a class body whose *effect* is "
  "on the constant environment, so the checker either models it (and rejects an "
  "out-of-scope read) or ignores it (and is merely imprecise). Ignoring it is sound; the "
  "rung is here to make that a decision rather than an oversight.",
  'class Box\n  SECRET = 1\n  private_constant :SECRET\n\n  def get\n    SECRET\n  end\n'
  'end\n\nBox.new.get\n', expect_validate=True)

R("const-attr-reader", 13,
  "`attr_reader :x, :y` -- the slice's other definition form (14 sites), and one the "
  "ladder has never had: a method that exists because a *call in a class body* created "
  "it. Tier 10 taught the checker that `define_method` does this; `attr_reader` is the "
  "same move with a fixed body (return the ivar of the same name), so the rule is a row "
  "in the class-body interpretation rather than anything new in `Judge`.",
  'class Point\n  attr_reader :x, :y\n\n  def initialize(x, y)\n    @x = x\n    @y = y\n'
  '  end\nend\n\nPoint.new(1, 2).x + Point.new(1, 2).y\n', expect_validate=True)

R("const-alias", 13,
  "`alias length size` -- three sites in the slice (`Purl#eql?`, `PkgVersion#eql?`, "
  "`Version#eql?`, all aliasing `==`). A second name for one method table entry; the "
  "MRO list from clink 23 already has the shape this needs, so the rung is small on "
  "purpose -- it is here because `alias'` is a head the corpus never emitted.",
  'class Box\n  def size\n    3\n  end\n  alias length size\nend\n\nBox.new.length\n',
  expect_validate=True)

R("const-class-of-const", 13,
  "M::Box.new.class.to_s -- `Object#class`, 11 sites in the slice, and the one place "
  "`Ty.clsOf` is produced by an *expression* rather than by naming a class. It is the "
  "inverse of `newInst`: `.inst n _` in, `.clsOf n` out. `purl.rb` needs it "
  "(`self.class.encode`) to reach a singleton method from an instance method.",
  'module M\n  class Box\n  end\nend\n\nM::Box.new.class.to_s\n', expect_validate=True)

R("const-string-arith-unsafe", 13,
  'An UNSAFE program: SIZE = "3"; SIZE + 1 really raises TypeError. The control for '
  "constant *inference* -- a checker that gave every constant `.any` rather than its "
  "initialiser's type would certify it, and `.any` is the tempting shortcut here "
  "precisely because the slice's constants are tables. Permanent negative target.",
  'SIZE = "3"\nSIZE + 1\n', expect_validate=False, false_reason="unsafe_program")

# --- Tier 14: parameters and arguments -------------------------------------
#
# The ladder has only ever had required positional parameters (`preq`), and
# `Frontier` item 11 has recorded the rest as owed since tier 6. The slice
# settles it: 8 `pkey`, 2 `popt`, 3 `prest`, 1 `pkwrest`, and **105 `kwargs`
# nodes at call sites**. Keyword arguments are not a corner of this target, they
# are how it is written.

R("param-optional", 14,
  "def greet(name, greeting = \"hi\") -- the optional parameter. `Judge.callDef` types a "
  "body once per call-site argument shape, so an optional parameter is not one signature "
  "with a hole: it is *two* shapes, and the default's own type is judged in the "
  "environment of the parameters to its left. Both call shapes appear here so the rung "
  "cannot be climbed by handling only one.",
  'def greet(name, greeting = "hi")\n  greeting + " " + name\nend\n\n'
  'greet("a") + greet("a", "yo")\n', expect_validate=True)

R("param-optional-uses-earlier", 14,
  "def pad(s, n = s.length) -- the default *reads an earlier parameter*, which is what "
  "makes \"judge the default in the environment of the parameters to its left\" a real "
  "premise rather than a formality. Ruby evaluates defaults left to right at call time, "
  "so `paramEnv` has to be built incrementally.",
  'def pad(s, n = s.length)\n  n\nend\n\npad("abc")\n', expect_validate=True)

R("param-rest", 14,
  "def total(*ns) -- the rest parameter, bound to an `Array` of the remaining arguments. "
  "This is half of the `ty_language_gap` that `proc-arity-leniency` and "
  "`metaprog-method-missing-splat` have flagged since tier 9: the *value* side is easy "
  "(`arrayOf` of the join of the extra arguments' types), and the gap is in describing "
  "the arity, which only matters for a callable in a variable. A `def` is called by name, "
  "so this rung needs no arity spine at all -- which is the finding.",
  'def total(*ns)\n  ns.inject(0) { |a, b| a + b }\nend\n\ntotal(1, 2, 3) + total()\n',
  expect_validate=True)

R("param-req-then-rest", 14,
  "def tag(first, *rest) -- required-then-rest, the split `identify.rb`'s "
  "`self.repo_url(*urls)` uses. The rule has to bind the prefix positionally and collect "
  "the suffix, so the parameter list stops being a zip and becomes a small match.",
  'def tag(first, *rest)\n  first + rest.length\nend\n\ntag(1, 2, 3)\n',
  expect_validate=True)

R("param-keyword", 14,
  "def build(type:, name:) -- the required keyword parameter, and the corresponding "
  "`kwargs` node at the call site. This is `purl.rb`'s constructor exactly. Arguments "
  "stop being positional: the call's `kwargs` entries have to be matched to parameters "
  "**by name**, and a missing one is an ArgumentError, which is in the type-error family "
  "-- so unlike a positional arity mismatch this is a soundness obligation the checker "
  "must discharge, not a convenience.",
  'def build(type:, name:)\n  type + "/" + name\nend\n\nbuild(type: "brew", name: "x")\n',
  expect_validate=True)

R("param-keyword-default", 14,
  "def build(name:, version: nil) -- an optional keyword, whose default is `nil`, whose "
  "body then *narrows* it. The rung where tier 12 and tier 14 meet: the parameter's type "
  "at a call site that omits it is `Nil`, at one that supplies it is `String`, and only "
  "per-call-site instantiation makes both precise. A checker with one signature per "
  "method would have to type it `nilable String` in both.",
  'def build(name:, version: nil)\n  version.nil? ? name : name + "@" + version\nend\n\n'
  'build(name: "x") + build(name: "x", version: "1")\n', expect_validate=True)

R("param-kwrest", 14,
  "def opts(**kw) -- the keyword-rest parameter, bound to a `Hash`. Same shape as "
  "`param-rest` and the same finding, with tier 5's unparameterised `Hash` now the "
  "binding constraint: `kw[\"a\"]` can only be `.any` until a hash type carries its "
  "keys. `version.rb`'s `self.detect(url, **specs)` is this.",
  'def opts(**kw)\n  kw["a"].nil? ? 0 : 1\nend\n\nopts(a: 1)\n', expect_validate=True)

R("param-block", 14,
  "def run(&b) -- the block parameter as a *declared* parameter rather than an "
  "out-of-band one. Tier 9b already types `&b` (`callDefBlk` puts the block in "
  "`paramEnvB`); what this rung adds is that `Param.block` is a parameter kind the "
  "`def'` rule must accept rather than refuse, which `Frontier` item 11 records it "
  "refusing. `version/parser.rb`'s `initialize(regex, &block)` is the slice's use.",
  'def run(&b)\n  b.call(2)\nend\n\nrun { |x| x * 3 }\n', expect_validate=True)

R("arg-splat-call", 14,
  "add(*xs) -- a `splat` in *argument* position. The dual of `param-rest`, and the "
  "harder direction: the callee's arity is known and the caller's argument *count* is "
  "not, because it is the length of an array. `arrayOf` carries an element type and no "
  "length (the same fact `narrow-nilable-and-union` is a `ty_language_gap` for), so a "
  "sound rule must either reject this or find the length another way.",
  'def add(a, b)\n  a + b\nend\n\nxs = [1, 2]\nadd(*xs)\n', expect_validate=True)

R("arg-splat-array-literal", 14,
  "[1, *xs, 4] -- a splat inside an array literal, which `elemTy` has to join *through*: "
  "the spliced elements contribute `xs`'s element type, not `xs`'s type. Unlike the call "
  "form this needs no length, which is why it is a separate rung from `arg-splat-call`.",
  'xs = [2, 3]\nys = [1, *xs, 4]\nys.length\n', expect_validate=True)

R("arg-kwsplat-call", 14,
  "build(**kw) -- the `kwsplat` entry kind in a `kwargs` node. Same problem as the "
  "positional splat and worse: the hash's *keys* decide which parameters are bound, and "
  "tier 5's `Hash` type does not carry them, so a sound checker cannot tell whether the "
  "required keywords are all present.",
  'def build(type:, name:)\n  type + "/" + name\nend\n\nkw = { type: "brew", name: "x" }\n'
  'build(**kw)\n', expect_validate=True)

R("param-shorthand-kwarg", 14,
  "build(type:, name:) at the *call site* -- Ruby 3.1's shorthand for `type: type`. "
  "Pure sugar, and the desugarer expands it (this is `implicit_node`, the single gate "
  "that stood between the front end and 61% vs 97% of Homebrew -- `homebrew/README.md` "
  "§1). The rung exists to pin that it really is expanded, so no checker rule is owed.",
  'def build(type:, name:)\n  type + "/" + name\nend\n\ntype = "brew"\nname = "x"\n'
  'build(type:, name:)\n', expect_validate=True)

R("param-all-kinds", 14,
  "def f(a, b = 2, *rest, c:, d: 4, **kw, &blk) -- every parameter kind in one "
  "signature, called with only the two arguments that are required. The cross-product "
  "rung for this tier: each kind above has a rule, and the ordering constraints between "
  "them (positional prefix, then rest, then keywords in any order, then the block) are "
  "only visible when they are all present at once.",
  'def f(a, b = 2, *rest, c:, d: 4, **kw, &blk)\n'
  '  [a, b, rest.length, c, d, kw.length, blk.nil?].length\nend\n\nf(1, c: 3)\n',
  expect_validate=True)

R("param-arity-unsafe", 14,
  "An UNSAFE program: `def f(a); end; f(1, 2)` really raises ArgumentError, which is in "
  "the type-error family. The control that keeps positional arity a *checked* premise -- "
  "the ladder has never had a rung where a `def` call could get the count wrong, because "
  "before this tier every parameter was required and every call site literal.",
  'def f(a)\n  a\nend\n\nf(1, 2)\n', expect_validate=False, false_reason="unsafe_program")

R("param-missing-keyword-unsafe", 14,
  "An UNSAFE program: `build(type: \"brew\")` against `def build(type:, name:)` raises "
  "ArgumentError (\"missing keyword: :name\"). The control for keyword matching being "
  "by name: a checker that only counted arguments certifies it, and counting is exactly "
  "what the positional rule does. Permanent negative target.",
  'def build(type:, name:)\n  type + name\nend\n\nbuild(type: "brew")\n',
  expect_validate=False, false_reason="unsafe_program")

# --- Tier 15: strings, symbols and regexps ---------------------------------
#
# 85 `__as_string` calls (string interpolation), 58 `regexp_lit`s and 299 `sym`s
# in the linked slice, against 0, 0 and 2 in the corpus. This tier is the
# slice's actual *diet*: `identify.rb` is a table of regexes, `semver.rb` builds
# its grammar by interpolating four constants into one, and every `to_s` in the
# whole stack ends in an interpolation.

R("str-interpolation", 15,
  '"hello #{name}" -- the desugarer expands interpolation into `__as_string` calls and a '
  "concatenation, so this is *not* a new `Expr` node; what is new is the `__as_string` "
  "row itself, which is total (every object answers `to_s`) and returns `String`. Total "
  "and unconstrained, so it is the cleanest new `PrimSig` row on the ladder.",
  'name = "world"\n"hello #{name}"\n', expect_validate=True)

R("str-interpolation-nonstring", 15,
  '"n = #{n + 1}" over an Integer -- the point of the previous rung, made unavoidable: '
  "the interpolated subterm has a non-String type and the result is a String anyway. A "
  "checker that typed interpolation as `String#+` would reject it.",
  'n = 3\n"n = #{n + 1}"\n', expect_validate=True)

R("str-interpolation-in-method", 15,
  '"#{Box.new(2)}" where Box defines its own `to_s` -- interpolation *dispatches*. This '
  "is `pkg_version.rb`'s `\"#{version}_#{revision}\"` exactly, and it is why "
  "`__as_string` cannot be a plain builtin row: on a user instance it has to reach the "
  "class's own `to_s` through the MRO, and fall back to the default only if there is none.",
  'class Box\n  def initialize(v)\n    @v = v\n  end\n\n  def to_s\n    "Box(#{@v})"\n'
  '  end\nend\n\n"#{Box.new(2)}"\n', expect_validate=True)

R("sym-literal", 15,
  "s = :affected; s.to_s.length -- `Ty.sym` has existed since the port and two rungs "
  "have used it. The slice uses 299, as the vocabulary of its state machine "
  "(`:affected`/`:fixed`/`:not_applicable`, `:critical`/`:high`/`:medium`/`:low`), so "
  "the tier starts by pinning `Symbol#to_s`.",
  "s = :affected\ns.to_s.length\n", expect_validate=True)

R("sym-compare", 15,
  "s == :high -- comparing symbols, which is how every one of the slice's state tests is "
  "written. Already covered by `Object#==`'s unconstrained-argument row (tier 2), and "
  "the rung is here to say so: a checker that grew a `Symbol#==` row would be adding one "
  "it does not need.",
  "s = :high\ns == :high\n", expect_validate=True)

R("str-percent-w", 15,
  "%w[a b c] -- a word array, five sites in the slice (`BASE_METRICS`, "
  "`SUPPORTED_PREFIXES`). Sugar for an array of string literals, so like "
  "`param-shorthand-kwarg` the rung's content is that the desugarer has already dealt "
  "with it.",
  '%w[a b c].length\n', expect_validate=True)

R("regexp-match-p", 15,
  '"1.2.3".match?(/\\A\\d+(\\.\\d+)*\\z/) -- `regexp_lit`, the head, and the cheapest '
  "eliminator: `String#match?` is total and returns `Bool`. That makes it the right "
  "first rung of the regexp story, because it needs a type for a `Regexp` value and "
  "nothing else -- `Ty` has no `Regexp`, so this rung's whole demand is one `.cls` row.",
  '"1.2.3".match?(/\\A\\d+(\\.\\d+)*\\z/)\n', expect_validate=True)

R("regexp-match-captures", 15,
  'm = "1.2.3".match(/(\\d+)\\.(\\d+)/); m[1] + m[2] -- `String#match` answers a '
  "`MatchData` **or nil**, and `MatchData#[]` answers a `String` or nil. So the honest "
  "type is `nilable`, twice over, and this program is safe only because the match "
  "succeeds -- which no `Ty` here can say. Expect this to be the tier's hard rung: it is "
  "`narrow-nilable-and-union`'s problem in the slice's own idiom, and `semver.rb`, "
  "`identify.rb` and `pkg_version.rb` all write it.",
  'm = "1.2.3".match(/(\\d+)\\.(\\d+)/)\nm[1] + "-" + m[2]\n', expect_validate=True)

R("regexp-match-nil", 15,
  '"abc".match(/\\d+/).nil? -- the safe half of the previous rung: the `nilable` is '
  "consumed by `nil?` rather than by an index. Tier 12's narrowing already handles the "
  "shape; what is new is that the nilable comes out of a builtin's *return* type rather "
  "than out of `Array#[]`.",
  '"abc".match(/\\d+/).nil?\n', expect_validate=True)

R("regexp-sub", 15,
  '"v1.2.3".sub(/\\Av/, "") -- `String#sub`, seven sites in the slice and the exact call '
  "`vulnerability.rb`'s `normalize_version` makes on every version string that enters "
  "the decision core. Total, `String` in and `String` out, whether or not it matched.",
  '"v1.2.3".sub(/\\Av/, "")\n', expect_validate=True)

R("regexp-gsub", 15,
  '"a_b_c".gsub(/_/, "-") -- `String#gsub`, eight sites. Same row shape as `sub`; the '
  "pair is two rungs rather than one because the slice uses both and a table with one of "
  "them is a table that was written from a rung rather than from the target.",
  '"a_b_c".gsub(/_/, "-")\n', expect_validate=True)

R("regexp-gsub-block", 15,
  '"abc".gsub(/[abc]/) { |c| c.upcase } -- `gsub` with a **block**, which is a '
  "higher-order `PrimSig` row of exactly the kind tier 9c introduced for the iterators: "
  "the block is called with a `String` and its result must be one. `purl.rb`'s `encode` "
  "and `identify.rb`'s `decode` are both this, and both are on the path of every purl the "
  "slice emits.",
  '"abc".gsub(/[abc]/) { |c| c.upcase }\n', expect_validate=True)

R("regexp-split", 15,
  '"a/b/c".split("/") -- six sites in the slice. Returns `arrayOf String`, which is the '
  "first builtin on the ladder whose return type is a *parameterised* array rather than "
  "the receiver or an element of it.",
  '"a/b/c".split("/").length\n', expect_validate=True)

R("regexp-interpolated", 15,
  "re = /\\A#{seg}\\z/ -- a regexp literal built by **interpolation**, which is how "
  "`semver.rb` writes `SEMVER_REGEX` (four interpolated constants) and `identify.rb` "
  "writes its per-forge patterns (`Regexp.escape(host)` spliced into a pattern). The "
  "consequence for the checker is that a `regexp_lit`'s source is not always static, so "
  "nothing can be read off the pattern text -- a `Regexp` is opaque, which is the "
  "conservative answer and, this rung argues, the right one.",
  'seg = "\\\\d+"\nre = /\\A#{seg}\\z/\n"12".match?(re)\n', expect_validate=True)

R("regexp-extended-flag", 15,
  "A `/x`-flagged multi-line regexp -- `regexp_lit`'s second field is its option bits, "
  "and `semver.rb`, `identify.rb` and `version.rb` all use `/x` (and `/i`, and `/n`) to "
  "keep their patterns readable. The rung pins that the options survive the desugarer, "
  "because a `/x` pattern read without them matches nothing.",
  're = /\n  \\A\n  \\d+\n  \\z\n/x\n"12".match?(re)\n', expect_validate=True)

R("regexp-last-match", 15,
  'if "v1.2" =~ /v(\\d+)/ then Regexp.last_match(1) -- the `=~` operator and the '
  "**global** match state behind it, 12 sites in `identify.rb`. `Regexp.last_match` is a "
  "read of state that a `send` two lines earlier wrote, so it is the one place in the "
  "slice where a value's type depends on a side effect rather than on a subterm -- and "
  "the honest answer is `nilable String`, narrowed by the `if`.",
  'if "v1.2" =~ /v(\\d+)/\n  Regexp.last_match(1)\nelse\n  ""\nend\n',
  expect_validate=True)

R("str-methods", 15,
  "s.strip.downcase.tr(\"_\", \"-\").delete_prefix(\"f\") -- the String chain, four rows "
  "at once, all total and all `String -> String`. Written as one rung rather than four "
  "because that is how the slice writes them (`semver.rb`'s `parse` opens with "
  "`version.strip.delete_prefix(\"v\").delete_prefix(\"V\").match(...)`), and because a "
  "chain is where a wrong return type shows up immediately.",
  's = "  Foo_Bar  "\ns.strip.downcase.tr("_", "-").delete_prefix("f")\n',
  expect_validate=True)

R("str-start-with", 15,
  '"CVE-2026-1".start_with?("CVE-") -- the predicate `vulnerability.rb#cve_ids` filters '
  "on. A nullary-total-query row with an argument, so it extends tier 2's shape rather "
  "than adding one.",
  '"CVE-2026-1".start_with?("CVE-")\n', expect_validate=True)

R("regexp-no-match-unsafe", 15,
  'An UNSAFE program: `"abc".match(/(\\d+)/)[1]` really raises NoMethodError, because '
  "`match` answers nil when it does not match. The control for `String#match`'s return "
  "being `nilable` rather than `MatchData` -- and the sharpest one on this tier, because "
  "the *safe* twin (`regexp-match-captures`) is a program the checker must also accept, "
  "so the two together force the narrowing rather than a blanket answer either way. "
  "Permanent negative target.",
  'm = "abc".match(/(\\d+)/)\nm[1]\n', expect_validate=False, false_reason="unsafe_program")

# --- Tier 16: control flow beyond `if` -------------------------------------
#
# The corpus's whole control repertoire was `if`. The slice adds 11 `next`s, a
# `while`, 4 `begin` (rescue/else/ensure) blocks and 98 `return`s -- and the
# `begin`s are load-bearing rather than incidental: `Vulnerability` defines its
# own `Uncomparable < StandardError` and uses raise/rescue as the *control flow*
# of the comparison itself.

R("ctl-while", 16,
  "A `while` loop accumulating into a local -- `Expr.while'`, a head the corpus never "
  "emitted. The design question is not the loop but its **environment**: the body's "
  "outgoing environment feeds its own next iteration, so the rule needs a fixed point, "
  "and the cheap sound answer (require the body to preserve every local's type, i.e. "
  "clink 11's rule applied to the loop) is what this rung is here to force a decision on.",
  "i = 0\nn = 0\nwhile i < 3\n  n = n + i\n  i = i + 1\nend\nn\n", expect_validate=True)

R("ctl-until", 16,
  "`until` -- sugar for `while !cond`, and the rung is here to pin that the desugarer "
  "does that rather than emitting a second head.",
  "i = 0\nuntil i >= 3\n  i = i + 1\nend\ni\n", expect_validate=True)

R("ctl-next", 16,
  "`next if x == 2` inside an `each` block -- 11 sites in the slice, and the idiom "
  "`identify.rb`'s two `each` loops are built out of. `Expr.nxt` ends the block's "
  "*iteration*, so the block's result type is the join of its normal exit and every "
  "`next`, which is `bodyResult`'s problem from tier 9b in a new position.",
  "s = 0\n[1, 2, 3, 4].each do |x|\n  next if x == 2\n  s = s + x\nend\ns\n",
  expect_validate=True)

R("ctl-break", 16,
  "`break if x == 3` -- `Expr.brk`, which ends the *call* rather than the iteration, so "
  "unlike `next` it contributes to the type of the `each` send itself. Two heads, two "
  "rules, and the difference between them is the rung.",
  "s = 0\n[1, 2, 3, 4].each do |x|\n  break if x == 3\n  s = s + x\nend\ns\n",
  expect_validate=True)

R("ctl-unless", 16,
  "`unless x.nil? ... else ... end` -- sugar for `if` with the branches swapped, and the "
  "rung matters because of **narrowing**: tier 12's refinements are keyed to which "
  "branch is which, so a desugarer that swaps them and a checker that does not both "
  "produce a wrong answer, in opposite directions.",
  "x = 1\nunless x.nil?\n  x + 1\nelse\n  0\nend\n", expect_validate=True)

R("ctl-ternary", 16,
  'x.zero? ? "zero" : "nonzero" -- an `if` in expression position, and the shape the '
  "slice writes its short branches in. Nothing new for `Judge`; the rung is the control "
  "that says so.",
  'x = 1\nx.zero? ? "zero" : "nonzero"\n', expect_validate=True)

R("ctl-or-assign", 16,
  "x ||= 5 -- desugars to `x || (x = 5)`, so like `&&`/`||` in tier 2 it is a `seq` and "
  "an `if` rather than a send. The interesting part is the type: `x` is `Nil` going in "
  "and `Int` coming out, which only works because `joinEnv` is applied to the two "
  "branches and the `nil` branch's contribution is the *narrowed* one. Tier 12's "
  "`falsyTy` is what makes the answer `Int` rather than `nilable Int`.",
  "x = nil\nx ||= 5\nx + 1\n", expect_validate=True)

R("ctl-safe-nav", 16,
  "x&.length -- the safe-navigation operator, which the slice uses on every nilable it "
  "does not want to narrow by hand (`severity&.to_s&.upcase`, `namespace&.downcase`). It "
  "desugars to a temp plus an `if`, so it is narrowing again -- and this time the "
  "narrowing is *generated by the desugarer*, which is the cleanest possible test of "
  "clink 12's finding that refinement needs an aliasing story rather than a syntactic one.",
  'x = nil\nx&.length\n', expect_validate=True)

R("ctl-rescue", 16,
  "A method body with a `rescue` clause and a typed exception binding -- `Expr.begin'`, "
  "a head the corpus never emitted, and the def-body form (no explicit `begin`) that the "
  "slice uses. Three demands: the body's type joins with the handler's, the bound "
  "variable `e` enters the handler's environment at the rescued class's type, and a "
  "`raise` is `Ty.never` so it contributes nothing to the join.",
  'def parse(s)\n  raise ArgumentError, "bad" if s.empty?\n  s.length\n'
  'rescue ArgumentError => e\n  e.message.length\nend\n\nparse("") + parse("ab")\n',
  expect_validate=True)

R("ctl-begin-rescue-else-ensure", 16,
  "All four clauses of `begin` at once. `else` runs only when the body did not raise and "
  "`ensure` runs on every path and contributes *nothing* to the value -- two facts a "
  "checker gets wrong in opposite directions if it treats the four clauses uniformly.",
  'log = []\nbegin\n  v = 1\nrescue StandardError\n  log << "rescue"\nelse\n'
  '  log << "else"\nensure\n  log << "ensure"\nend\nlog.length\n', expect_validate=True)

R("ctl-raise-custom", 16,
  "A user-defined `Uncomparable < StandardError`, raised and rescued -- "
  "`vulnerability.rb`'s own control flow, verbatim in miniature: `semver_compare!` "
  "raises it when two versions are incomparable and three callers rescue it to mean "
  "\"skip this range\". So exceptions here are not error handling, they are the "
  "*comparison protocol*, and a checker that cannot follow them cannot type the decision "
  "core at all.",
  'class Uncomparable < StandardError\nend\n\ndef cmp(a)\n  raise Uncomparable if a.nil?\n'
  '  1\nrescue Uncomparable\n  0\nend\n\ncmp(nil) + cmp(1)\n', expect_validate=True)

R("ctl-rescue-in-block", 16,
  "A `rescue` clause **inside a block body**, with `next` as the handler -- the shape "
  "`range_status` uses in its innermost loop (`rescue Uncomparable; next`). It is the "
  "cross-product of this tier with tier 9's blocks, and it is where the block's result "
  "type has three contributors rather than two.",
  "s = 0\n[1, 0, 2].each do |d|\n  s = s + (10 / d)\nrescue ZeroDivisionError\n  next\n"
  "end\ns\n", expect_validate=True)

R("ctl-return-early", 16,
  "`return d if a.empty?` -- the guard clause, in a method with a *value* after it. "
  "Already the subject of `narrow-guard-clause` (tier 12); this rung is the plain "
  "control-flow half of it, without the narrowing, so the two can be climbed "
  "independently and the `.ret`-in-statement-position rule can be justified once.",
  'def first_or(a, d)\n  return d if a.empty?\n  a[0]\nend\n\nfirst_or([], 9) + first_or([1], 9)\n',
  expect_validate=True)

R("ctl-case-when-string", 16,
  "`case t when \"pypi\" ... else ... end` -- the dispatch `purl.rb#normalize` and "
  "`identify.rb#registry_package` are both written as. `case/when` desugars to a temp "
  "plus a chain of `===` sends against that temp, which is clink 12's finding "
  "(narrowing cannot be a syntactic rewrite) arriving from the target rather than from "
  "a hand-written rung -- and with `String#===` rather than `Module#===`, so it needs no "
  "refinement at all, only a join.",
  'def kind(t)\n  case t\n  when "pypi" then "python"\n  when "gem" then "ruby"\n'
  '  else "other"\n  end\nend\n\nkind("gem") + kind("x")\n', expect_validate=True)

R("ctl-rescue-wrong-class-unsafe", 16,
  "An UNSAFE program: the body raises TypeError and the handler only catches "
  "ArgumentError, so the TypeError escapes. The control that keeps `rescue` from being "
  "read as \"and therefore nothing raises\" -- a checker that treated any `begin` as "
  "discharging the type-error family would certify it, and that is the natural wrong "
  "generalisation of the `ctl-rescue` rule. Permanent negative target.",
  'begin\n  1 + "a"\nrescue ArgumentError\n  0\nend\n',
  expect_validate=False, false_reason="unsafe_program")

# --- Tier 17: the collection and Comparable idioms -------------------------
#
# The last syntactic tier, and the one that is mostly *library*: the builtin
# call shapes the slice reaches for constantly and the corpus reached for
# never. `homebrew/README.md` §2 measures the same gap over all of Homebrew
# (6.4% of 113,610 call sites resolve to nothing we have, 1,020 distinct names);
# these are that gap's slice-sized head.

R("lib-comparable", 17,
  "`include Comparable` plus a `<=>`, and the five operators it manufactures. Three of "
  "the eight slice files do exactly this (`Version`, `PkgVersion`, `Version::Token`), and "
  "it is the payoff of tier 10's mixin work: `Comparable` is a module in the MRO whose "
  "methods are *defined in terms of a method the including class supplies*, so typing "
  "`r < s` means dispatching to `Comparable#<`, whose body calls the receiver's own "
  "`<=>`. Nothing new in `Judge`; everything in the prelude the checker reads.",
  'class Rev\n  include Comparable\n\n  def initialize(n)\n    @n = n\n  end\n\n'
  '  def n\n    @n\n  end\n\n  def <=>(other)\n    n <=> other.n\n  end\nend\n\n'
  'r = Rev.new(1)\ns = Rev.new(2)\n[r < s, r > s, r.between?(r, s), r.clamp(r, s).n].length\n',
  expect_validate=True)

R("lib-spaceship-int", 17,
  "`1 <=> 2` -- the builtin row underneath the previous rung. Returns `Integer`, and on "
  "mismatched types returns **nil**, which is why `pkg_version.rb`'s `<=>` is declared "
  "`T.nilable(Integer)` and why every caller in the slice checks. One row; two rungs, "
  "because the mixin and the primitive fail independently.",
  "(1 <=> 2) + (2 <=> 1)\n", expect_validate=True)

R("lib-struct-kwinit", 17,
  "`Struct.new(:state, :fixed_in, keyword_init: true)` -- a class **manufactured by a "
  "call**, assigned to a constant, with readers and a keyword constructor. This is "
  "`Vulnerability::RangeStatus` and `Identify::RegistryPackage`, i.e. the type the whole "
  "decision core *returns*. Tier 10's `define_method` is the precedent; what is new is "
  "that the class itself, not just a method, comes from a runtime call, so the class "
  "table has an entry no `class'` node produced.",
  'Status = Struct.new(:state, :fixed_in, keyword_init: true)\n'
  's = Status.new(state: :affected, fixed_in: "1.0")\ns.state == :affected\n',
  expect_validate=True)

R("lib-struct-with-body", 17,
  "The same with a **block** defining extra methods -- `RangeStatus`'s `affected?`/ "
  "`fixed?` exactly. The block body is a class body, so the checker has to judge it in "
  "a `self` typed as the class it is in the middle of manufacturing.",
  'Status = Struct.new(:state, keyword_init: true) do\n  def affected?\n'
  '    state == :affected\n  end\nend\n\nStatus.new(state: :affected).affected?\n',
  expect_validate=True)

R("lib-hash-fetch", 17,
  "`h.fetch(\"a\")` and `h.fetch(\"b\", 0)` -- **62 sites** in the slice, the single most "
  "used builtin in it. Two rows, and the difference is the point: one-argument `fetch` "
  "raises KeyError on a miss (outside the type-error family, so it is safe by this "
  "ladder's reading) and two-argument `fetch` is total. Both return the value type, "
  "which tier 5's unparameterised `Hash` cannot name -- so this rung is the strongest "
  "demand in the corpus for a keyed hash type.",
  'h = { "a" => 1 }\nh.fetch("a") + h.fetch("b", 0)\n', expect_validate=True)

R("lib-hash-dig", 17,
  'h.dig("pkg", "name") -- eight sites. `dig` walks and answers nil at any miss, so its '
  "result is `nilable`; `vulnerability.rb#affected_entry_relevant?` then narrows it in "
  "the same expression (`if (ecosystem = aff.dig(...)) && ...`).",
  'h = { "pkg" => { "name" => "x" } }\nh.dig("pkg", "name")\n', expect_validate=True)

R("lib-hash-key-p", 17,
  'h.key?("a") -- the guard `cvss.rb#valid_values?` is eight copies of. Total, `Bool`.',
  'h = { "a" => 1 }\nh.key?("a")\n', expect_validate=True)

R("lib-array-push", 17,
  "`xs << 1` -- the mutating append, and the rung tier 5 named as an inherited "
  "obligation: \"`arrayOf`'s invariance is not yet load-bearing -- there is no rule for "
  "`Array#<<`, and the tier that adds one inherits the obligation\". Here it is. The "
  "sound rule has to either require the element to match or widen the array's element "
  "type *in the environment*, and the second is only possible because the environment "
  "threads (clink 2).",
  "xs = []\nxs << 1\nxs << 2\nxs.length\n", expect_validate=True)

R("lib-array-queries", 17,
  "`any?`/`all?` with a block, `include?`, `empty?` -- the four predicates, in one rung "
  "because they share a row shape (higher-order for the first two, total for the last "
  "two) and all four appear in `cvss.rb#parse` alone.",
  "xs = [1, 2, 3]\n[xs.any? { |x| x > 2 }, xs.all? { |x| x > 0 }, xs.include?(2), xs.empty?].length\n",
  expect_validate=True)

R("lib-array-first-last", 17,
  "`xs.first` / `xs.last` -- `nilable elem`, for the same reason `Array#[]` is (tier 5), "
  "and worth its own rung because the slice calls them on arrays it has just checked are "
  "non-empty, which is the narrowing-by-length case `Ty` has no vocabulary for.",
  "xs = [1, 2, 3]\nxs.first + xs.last\n", expect_validate=True)

R("lib-array-uniq-compact", 17,
  "`compact.uniq` -- and `compact` is the interesting half: it takes `arrayOf (nilable "
  "T)` to `arrayOf T`, so it is the one builtin in the slice that *removes* a nilable "
  "rather than introducing or consuming one.",
  "[1, 1, nil, 2].compact.uniq.length\n", expect_validate=True)

R("lib-array-flat-map", 17,
  "`flat_map` -- `fixed_versions` is two nested ones. A higher-order row whose result "
  "type is the block's *element* type, which is a third answer beside tier 9c's three "
  "(`map`'s block return, `each`'s receiver, `select`'s element).",
  "[[1, 2], [3]].flat_map { |a| a }.length\n", expect_validate=True)

R("lib-array-filter-map", 17,
  "`filter_map` -- `arrayOf` of the **non-nil part** of the block's return type, which "
  "makes it the eliminator twin of `compact` and a fourth distinct higher-order answer. "
  "`fix_urls` and `fixed_versions` both use it.",
  "[1, 2, 3].filter_map { |x| x > 1 ? x : nil }.length\n", expect_validate=True)

R("lib-array-find", 17,
  "`find` -- `nilable elem`, because there may be no match. `advisory_url` is "
  "`references.find { ... }&.dig(\"url\")`, i.e. this rung composed with safe navigation "
  "and `dig`, so all three have to answer nilable for that one line to type.",
  '[1, 2, 3].find { |x| x > 1 }\n', expect_validate=True)

R("lib-array-partition", 17,
  "`a, b = xs.partition { ... }` -- a block-taking builtin returning a **pair**, "
  "destructured by a multiple assignment. Two new things at once: a tuple-shaped result "
  "(which `arrayOf` cannot describe, since the two halves are the same type here but "
  "need not be) and `masgn`.",
  "a, b = [1, 2, 3, 4].partition { |x| x.even? }\na.length + b.length\n",
  expect_validate=True)

R("lib-array-zip", 17,
  '[1, 2].zip(["a", "b"]) -- `arrayOf (arrayOf (union Int String))` under the current '
  "type language, which is *sound and useless*: the real answer is an array of pairs. "
  "`semver.rb#compare_prerelease` uses `zip` with a block and relies on the pairing, so "
  "this is where the ladder's array type stops being expressive enough for the target.",
  '[1, 2].zip(["a", "b"]).length\n', expect_validate=True)

R("lib-array-join", 17,
  '["a", "b"].join("/") -- total, `String`. `purl.rb#to_s` builds every namespace with '
  "it.",
  '["a", "b"].join("/")\n', expect_validate=True)

R("lib-array-each-with-index", 17,
  "`each_with_index` with a two-parameter block -- the block's parameters have "
  "*different* types (element, `Integer`), which tier 9's iterator rows never needed: "
  "`inject` has two parameters but both come from the same place.",
  "s = 0\n[10, 20].each_with_index do |v, i|\n  s = s + v + i\nend\ns\n",
  expect_validate=True)

R("lib-array-to-h", 17,
  '[["a", 1]].to_h -- an array of pairs to a Hash, which `cvss.rb#parse` uses with a '
  "block to build its metric table. The inverse of the `zip` problem and blocked on the "
  "same missing pair type.",
  '[["a", 1]].to_h["a"]\n', expect_validate=True)

R("lib-array-sort-by-max-by", 17,
  "`sort_by` and `max_by` -- tier 9 has `sort_by`; `max_by` is its `nilable`-returning "
  "sibling (nil on an empty receiver), and `range_status` ends with "
  "`past_fixes.max_by { |v| Version.new(v) }` feeding a field that is declared nilable "
  "for exactly that reason.",
  'xs = ["bbb", "a", "cc"]\nxs.sort_by { |s| s.length }.first + xs.max_by { |s| s.length }\n',
  expect_validate=True)

R("lib-array-wrap", 17,
  "`Array(x)` -- **20 sites**, and `Vulnerability#initialize` is nine of them in nine "
  "consecutive lines. It is a *conversion*: nil becomes `[]`, an array passes through, "
  "anything else is wrapped. So its result type is a three-way case on the argument's "
  "type, which is the first builtin row on the ladder that has to inspect its argument's "
  "type rather than constrain it.",
  "Array(nil).length + Array([1, 2]).length + Array(3).length\n", expect_validate=True)

R("lib-multiple-assign", 17,
  'a, b = "x-1".split("-") -- `masgn` over an array of unknown length, which is how '
  "`identify.rb` reads every `rpartition`/`partition` result. Each target gets `nilable "
  "elem` on the honest reading, and the program is safe only because the split yields "
  "two -- the length problem again, now in assignment position.",
  'a, b = "x-1".split("-")\na + b\n', expect_validate=True)

R("lib-array-first-nil-unsafe", 17,
  "An UNSAFE program: `[].first + 1` really raises NoMethodError. The control for "
  "`Array#first` being `nilable` -- the same shape as tier 12's `narrow-absent-unsafe` "
  "but on the named accessor rather than on `#[]`, because a checker can plausibly get "
  "one right and the other wrong. Permanent negative target.",
  "xs = []\nxs.first + 1\n", expect_validate=False, false_reason="unsafe_program")


# --- Tiers 18 and 19: the slice files themselves ----------------------------
#
# These rungs' Ruby is not written here: it is `slice/<name>.rb`, composed by
# `scripts/build_slice_rungs.py` out of Homebrew's own source (boot stubs +
# `linker` over the file's require-closure + a driver from `slice/drivers/`).
# The composition needs the vendored `homebrew/vendor/brew` checkout, which is
# gitignored; the *composed* programs are committed, so regenerating the corpus
# does not. See that script's docstring.

SLICE_DIR = os.path.join(RATCHET_DIR, "slice")


def RS(id_, tier, description, slice_name, *, expect_validate, false_reason=None):
    """A rung whose Ruby is `slice/<slice_name>.rb`."""
    path = os.path.join(SLICE_DIR, f"{slice_name}.rb")
    if not os.path.isfile(path):
        raise SystemExit(
            f"{id_}: missing {path} -- run scripts/build_slice_rungs.py first")
    R(id_, tier, description, open(path).read(),
      expect_validate=expect_validate, false_reason=false_reason)


# --- Tier 18: the eight slice files, one rung each --------------------------
#
# Each rung is one slice file plus its require-closure plus a **driver** that
# exercises that file's own API with real calls -- no value is printed that the
# file would not compute. They are ordered by dependency, which is also roughly
# by size (219 lines to 1,734), so the tier is itself a ladder: `semver.rb` is a
# module of four pure class methods and `version.rb` is nine classes and a
# 30-entry parser table.
#
# What a rung means here is different from every tier above it. Above, a rung
# isolates a feature and `validate` answering `false` names a missing rule.
# Here `validate` answers `false` because *some* subterm somewhere is out of the
# fragment, and the useful question stops being yes/no -- which is the ratchet's
# own version of the finding `homebrew/slice-verdict.md` reaches from the other
# side (`reject` with basis `uncertified`, and the metric that replaces it is
# per-method-body). Expect these to stay `false` for a long time; they are the
# demand list the tiers above are ordered to serve.

RS("slice-semver", 18,
   "`vulns/semver.rb` + a driver over SemVer 2.0 §11: 18 ordered pairs, seven spec "
   "violations that must answer nil, and a sort. The smallest slice file (5 `def`s, one "
   "module, no state) and therefore the first whole-file target: it needs tier 13's "
   "constants and `private_constant`, tier 15's interpolated `/x` regexp and "
   "`match`/`match?`/`strip`/`delete_prefix`, tier 16's guard `return`s, and tier 17's "
   "`fetch`/`zip`/`empty?` -- and nothing else. If any file on this ladder is accepted "
   "first, it is this one.",
   "semver", expect_validate=True)

RS("slice-cvss", 18,
   "`vulns/cvss.rb` + a driver over the FIRST specification's own worked examples, every "
   "severity-band boundary, and eight malformed vectors that must answer nil rather than "
   "raise. Seven `def`s, six frozen `Hash` constants, and the slice's only **Float** "
   "arithmetic -- `**`, `round`, and the Appendix A Roundup. The binding constraint is "
   "tier 17's `Hash#fetch`: every one of the seven metric lookups is a `fetch` into a "
   "constant table, and `Ty`'s unparameterised `Hash` cannot say the result is a Float.",
   "cvss", expect_validate=True)

RS("slice-purl", 18,
   "`vulns/purl.rb` + a driver over construction, per-type normalisation, "
   "percent-encoding and structural equality. The slice's smallest *class*: an "
   "`initialize` with four keyword parameters (two optional), `attr_reader`, an `alias`, "
   "a `case/when` on a String, `self.class` dispatch from an instance method, and a "
   "`gsub` with a block. So it is tiers 13, 14, 15 and 16 in one 90-line file, which is "
   "what makes it the right second target.",
   "purl", expect_validate=True)

RS("slice-version-parser", 18,
   "`version/parser.rb` + a driver over the parser hierarchy. The slice's one piece of "
   "classical OO -- an `abstract!` base, `RegexParser` holding a regexp and an optional "
   "block, and two subclasses that differ only in `process_spec`. Tier 7's `super`, tier "
   "10's mixin ancestry and tier 14's `&block` parameter, over a receiver whose method "
   "is found three classes up. Also the file that exposed the boot-stub gap the ratchet "
   "had to close: with only `Object#blank?` stubbed, `nil.blank?` is *false* and "
   "`RegexParser#parse` is unusable -- see `scripts/build_slice_rungs.py`'s "
   "`BLANK_NIL_STUB`.",
   "version-parser", expect_validate=True)

RS("slice-version", 18,
   "`version.rb` + a driver over the token hierarchy, the ordering it induces, and "
   "`Version.detect` across ten source-URL shapes. The largest file in the slice: nine "
   "classes, 63 `def`s, a 30-entry `VERSION_PARSERS` table built by interpolating six "
   "regexp fragments into each other, and the `<=>` that the whole vulnerability "
   "decision rests on whenever an advisory range is `ECOSYSTEM`-typed. Everything below "
   "this rung in the tier is a proper part of what it needs.",
   "version", expect_validate=True)

RS("slice-pkg-version", 18,
   "`pkg_version.rb` + a driver over parsing, the composite ordering, the `Comparable` "
   "operators and the `Forwardable` delegation. Only 8 `def`s, but it is the tier's "
   "**mixin** rung: `include Comparable` and `extend Forwardable` in one class, plus a "
   "`delegate` DSL call that manufactures five methods -- tier 17's `lib-comparable` and "
   "tier 13's `attr_reader` are the two isolated capabilities it composes, over the "
   "whole of `version.rb` underneath.",
   "pkg-version", expect_validate=True)

RS("slice-identify", 18,
   "`vulns/identify.rb` + a driver over 40 real source URLs: ten forge shapes, eight tag "
   "patterns, fourteen package registries, and the near-misses that must *not* match. "
   "The most regexp-dense file in the slice (14 patterns, several interpolated, one "
   "`/x`), plus `Struct.new(keyword_init: true)`, `Regexp.last_match`, and a `case/when` "
   "with fourteen arms over a String. Tier 15 and tier 17 together, at the density the "
   "target actually writes them.",
   "identify", expect_validate=True)

RS("slice-vulnerability", 18,
   "`vulns/vulnerability.rb` (with `version.rb`) + a driver over a structurally faithful "
   "OSV advisory: every field reader, `range_status` at eleven boundary versions, the "
   "`ECOSYSTEM` path, `affects_version?`, `fix_available?`, and the end-to-end verdict a "
   "user would be told. The slice's decision core and the last rung before the whole "
   "thing: 28 `def`s, a `T::Struct`, a `Struct.new` with a body, a user-defined "
   "`StandardError` used as *control flow*, and two lambdas selected by the advisory's "
   "own `type` field -- which is the finding the slice exists to make legible, since the "
   "two lambdas implement two different version orderings.",
   "vulnerability", expect_validate=True)

# --- Tier 19: the whole linked slice ----------------------------------------
#
# All eight files, linked into one program by `linker` from the three entry
# points that reach them, with a driver on top. This is where the ladder ends:
# there is no larger rung to write against this target, and `validate`'s verdict
# on `slice-whole` is the number the whole exercise is for.

RS("slice-whole", 19,
   "**The whole slice, as one program.** All eight files linked from `pkg_version.rb`, "
   "`vulns/vulnerability.rb` and `vulns/identify.rb` (8 spliced, 0 thunked, 0 external "
   "requires, 0 cycles), driven by `homebrew/slice-driver/driver.rb`: an OSV advisory "
   "with a `SEMVER` range and an `ECOSYSTEM` range over the same package, ten installed "
   "versions through `range_status`, the two orderings compared on the pairs where they "
   "differ, CVSS scoring, purl construction and six source URLs identified. ~2,180 lines. "
   "The driver is referenced rather than copied -- it is the demonstration "
   "`homebrew/slice-driver/` already runs, now also a rung.",
   "slice-whole", expect_validate=True)

RS("slice-input-sweep", 19,
   "The same linked program, driven by a **sweep of generated inputs**: 16 versions "
   "through one advisory carrying both a `SEMVER` and an `ECOSYSTEM` range, reported as "
   "a histogram (`{affected: 8, fixed: 4, not_applicable: 4, none: 0, raised: 0}`). One "
   "output line, and it is the one that says the verdict is genuinely "
   "**input-dependent** rather than constant -- which is what makes typing this program "
   "a statement about a function rather than about a constant folding. Narrowed from "
   "`probes/input-sweep.rb`'s 64 inputs to fit the agreement gate's 10-second budget; "
   "the cost per input is the probe's own finding and stays recorded there.",
   "slice-input-sweep", expect_validate=True)

RS("slice-adversarial", 19,
   "**An UNSAFE program, and the ladder's last word.** The same linked slice, driven by "
   "`probes/adversarial-inputs.rb`: the real `range_status`/`affects_version?` entry "
   "points, with only the advisory Hash and the version String varying over shapes a "
   "caller can actually supply. It reaches five type-family raises -- four "
   "`ArgumentError` from `Version.new("")` and two `TypeError` from `Integer#[]` -- and "
   "two of them come from a *schema-conformant* advisory. So the whole-slice program is "
   "type-safe only under a precondition on its inputs, and this rung is the permanent "
   "negative that says so: certifying it would be unsound, and the sibling `slice-whole` "
   "rung is the same code under inputs that satisfy the precondition. That pair is the "
   "sharpest statement on the ladder of what a `validate` verdict does and does not "
   "claim. (One row of the upstream probe is dropped -- a sorbet-runtime `T.let` failure "
   "whose message carries the caller's file path, so the two executors cannot agree on "
   "it by construction.)",
   "slice-adversarial", expect_validate=False, false_reason="unsafe_program")


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
