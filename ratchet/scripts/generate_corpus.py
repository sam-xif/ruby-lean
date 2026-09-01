#!/usr/bin/env python3
"""Generate the ratchet corpus (`../corpus/*.json` + `.rb` sources) from **real** Ruby,
run through the real desugarer (`harness/desugar-dt/bin/export-json`) -- not a
hand-authored AST. See `../AGENTS.md`.

Each rung is (id, tier, description, rb source, claims, expect_validate). `claims` are
built by `claim(program, predicate, ty)`, which runs the real desugarer on `rb` once and
extracts the claimed subterm out of that *exact* parsed AST via `find_node` -- so a
claim's `expr` field can never accidentally drift from what the program actually
contains (no hand-transcribed wire-format JSON anywhere in this file).

Regenerate with: `python3 scripts/generate_corpus.py` from `ratchet/`.
Then check the ladder with `scripts/run_ratchet.sh`.
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


def find_node(node, pred):
    """Depth-first search of a parsed wire-format AST (nested lists) for a node
    satisfying `pred`. Returns the first match, or None."""
    if pred(node):
        return node
    if isinstance(node, list):
        for child in node:
            found = find_node(child, pred)
            if found is not None:
                return found
    return None


def is_head(node, head, **fields):
    """Does `node` look like `[head, ...]`, optionally matching specific positional
    fields by index (e.g. `is_head(n, "def", 1="add")` checks n[1] == "add")?"""
    if not (isinstance(node, list) and len(node) >= 1 and node[0] == head):
        return False
    return all(node[int(i)] == v for i, v in fields.items())


def claim(program: dict, pred, ty: dict) -> dict:
    node = find_node(program["ast"], pred)
    assert node is not None, f"claim(): no node matched in {program['ast']!r}"
    return {"expr": node, "ty": ty}


# ---------------------------------------------------------------------------
# Ty JSON (must match Ratchet/Ty.lean's `Ty.ofJson?` tags exactly)
# ---------------------------------------------------------------------------

T_INT = {"tag": "int"}
T_BOOL = {"tag": "bool"}
T_NIL = {"tag": "nilT"}
T_SYM = {"tag": "sym"}
T_FLOAT = {"tag": "float"}
T_ANY = {"tag": "any"}


def T_CLS(name):
    return {"tag": "cls", "name": name}


def T_ARRAYOF(elem):
    return {"tag": "arrayOf", "elem": elem}


def T_ARROW0(ret):
    return {"tag": "arrow0", "ret": ret}


def T_ARROWCONS(param, rest):
    return {"tag": "arrowCons", "param": param, "rest": rest}


def arrow_of(params, ret):
    t = T_ARROW0(ret)
    for p in reversed(params):
        t = T_ARROWCONS(p, t)
    return t


T_STR = T_CLS("String")


# ---------------------------------------------------------------------------
# The rungs
# ---------------------------------------------------------------------------

RUNGS = []


def R(id_, tier, description, rb, claims=None, *, expect_validate):
    program = export(rb)
    RUNGS.append({
        "id": id_,
        "tier": tier,
        "description": description,
        "program": program,
        "cert": {"claims": claims(program) if claims else []},
        "expect_validate": expect_validate,
        "_rb": rb,
    })


# --- Tier 1: literals (chk synthesizes all of these; no claims needed) ------

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
  "1 + true is real, genuinely ill-typed Ruby (TypeError at runtime): the "
  "hardcoded Integer#+ rule has no (Int, Bool) case, so validate rejects it -- no "
  "dishonest certificate needed, unlike the previous corpus design, because chk "
  "synthesizes arithmetic truth structurally rather than checking a claim.",
  "1 + true\n", expect_validate=False)
R("to-s-call", 2, "5.to_s, an instance of String, via the universal Object#to_s rule.",
  "5.to_s\n", expect_validate=True)
R("eq-same-type", 2, "1 == 1 : Bool (both sides Int).", "1 == 1\n", expect_validate=True)
R("eq-different-type", 2,
  '1 == "a" is runtime-safe real Ruby (== never raises; it just answers false for '
  "unrelated types) -- but this package's `==` rule requires both sides the same "
  "Ty, so validate is conservative here and rejects it. A real gap, kept honest "
  "rather than special-cased away (see AGENTS.md).",
  '1 == "a"\n', expect_validate=False)
R("unknown-method-with-claim", 2,
  "5.zero? is not in the hardcoded builtin table (unlike to_s), but an explicit "
  "claim on this exact send node supplies its type -- the escape hatch a "
  "certificate exists for.",
  "5.zero?\n",
  claims=lambda p: [claim(p, lambda n: is_head(n, "send", **{"2": "zero?"}), T_BOOL)],
  expect_validate=True)
R("unknown-method-no-claim", 2,
  "5.foo_bar_baz is the same shape as unknown-method-with-claim but with no "
  "claim at all: validate gates it honestly instead of guessing.",
  "5.foo_bar_baz\n", expect_validate=False)
R("cmp-le", 2, "1 <= 2 : Bool.", "1 <= 2\n", expect_validate=True)
R("cmp-ge", 2, "1 >= 2 : Bool.", "1 >= 2\n", expect_validate=True)
R("nil-eq-nil", 2, "nil == nil : Bool (both sides Nil).", "nil == nil\n", expect_validate=True)
R("nested-arith", 2, "(1 + 2) * 3 : Int -- the outer send's receiver is itself a send.",
  "(1 + 2) * 3\n", expect_validate=True)
R("str-length-with-claim", 2,
  '"abc".length is not in the hardcoded builtin table; an explicit claim on this '
  "exact send node supplies its type (Int), the same escape hatch as "
  "unknown-method-with-claim but on a different receiver type.",
  '"abc".length\n',
  claims=lambda p: [claim(p, lambda n: is_head(n, "send", **{"2": "length"}), T_INT)],
  expect_validate=True)
R("str-length-no-claim", 2,
  'Same shape as str-length-with-claim but with no claim: rejected.',
  '"abc".length\n', expect_validate=False)

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
  "A bare `x`, never assigned anywhere: Prism itself desugars this to a `vcall` "
  "(a method-call attempt), not a `var` read, exactly because it was never "
  "assigned. With no zero-arg function named x and no claim, validate rejects it.",
  "x\n", expect_validate=False)
R("seq-multiple-stmts", 3, "x = 1; y = 2; x + y : Int.",
  "x = 1\ny = 2\nx + y\n", expect_validate=True)
R("assignment-chain", 3, "x = 1; y = x + 1; z = y + 1; z : Int -- a four-statement chain.",
  "x = 1\ny = x + 1\nz = y + 1\nz\n", expect_validate=True)

# --- Tier 4: conditionals ----------------------------------------------------

R("if-true-branch", 4, "if true then 1 else 2 end : Int.",
  "if true\n  1\nelse\n  2\nend\n", expect_validate=True)
R("if-no-else", 4,
  "if true then 1 end (no else): types as nilable(Int) via Ty.mkNilable, not "
  "rejected the way the previous (invented-Ty) corpus required an exact Nil type.",
  "if true\n  1\nend\n", expect_validate=True)
R("if-condition-not-bool", 4,
  "if 5 then 1 else 2 end: the condition is Int, not Bool -- rejected.",
  "if 5\n  1\nelse\n  2\nend\n", expect_validate=False)
R("if-branch-mismatch", 4,
  'if true then 1 else "a" end: Ty.joinTy has no case for (Int, an instance of '
  "String) -- neither equal nor nil on either side -- so it's rejected, honestly "
  "reflecting that this Ty language has no union/join for unrelated class types "
  "yet (see Ty.union's docstring).",
  'if true\n  1\nelse\n  "a"\nend\n', expect_validate=False)
R("nested-if", 4, "if true then (if false then 1 else 2) else 3 end : Int.",
  "if true\n  if false\n    1\n  else\n    2\n  end\nelse\n  3\nend\n",
  expect_validate=True)
R("if-does-not-leak-reassignment", 4,
  'x = 1; if true; x = "hello"; end; x + 1 -- KNOWN SIMPLIFICATION, not a bug: '
  "this checker's `if` does not propagate a branch's reassignments into the "
  "following code (the environment after an if is the environment from *before* "
  "it, documented in Ratchet/Validate.lean). So `x` is still seen as Int after "
  "the if, and `x + 1` validates -- even though the *only* branch this if has is "
  "the one that reassigns x to a String. Real Ruby's x really would be a String "
  "here; this checker cannot see that yet.",
  'x = 1\nif true\n  x = "hello"\nend\nx + 1\n', expect_validate=True)
R("elsif-chain", 4,
  "if/elsif/else desugars to nested if' nodes; a three-way chain with every "
  "branch Int types fine via nested joinTy calls.",
  "if true\n  1\nelsif false\n  2\nelse\n  3\nend\n", expect_validate=True)
R("elsif-chain-mismatch", 4,
  "Same elsif chain shape, but the final else branch is a String: the innermost "
  "nested if' fails to join (Int, an instance of String), which fails the whole "
  "chain even though the first two branches agree.",
  'if true\n  1\nelsif false\n  2\nelse\n  "a"\nend\n', expect_validate=False)
R("if-nil-condition", 4,
  "if nil then 1 else 2 end: the condition is Nil, not Bool -- rejected, just "
  "like if-condition-not-bool.",
  "if nil\n  1\nelse\n  2\nend\n", expect_validate=False)

# --- Tier 5: arrays / hashes --------------------------------------------------

R("array-int", 5, "[1, 2, 3] : an Array of Int.", "[1, 2, 3]\n", expect_validate=True)
R("array-empty", 5, "[] : an Array of Ty.any (nothing to unify an element type from).",
  "[]\n", expect_validate=True)
R("array-heterogeneous", 5,
  '[1, "a", true] is runtime-safe real Ruby (Ruby arrays are heterogeneous), but '
  "this checker's `array` rule requires a uniform element type -- Ty.arrayOf has "
  "no representation for a mixed-element array yet, so it's rejected rather than "
  "mis-certified.",
  '[1, "a", true]\n', expect_validate=False)
R("array-of-sends", 5, "[1 + 1, 2 + 2] : an Array of Int -- elements are checked recursively.",
  "[1 + 1, 2 + 2]\n", expect_validate=True)
R("hash-lit", 5,
  'A Hash literal types as the bare, unparameterised .cls "Hash" -- this Ty '
  "language has no parameterised Hash type the way it has arrayOf for Array "
  "(see Ty.lean's module docstring); every hash literal gets the same generic "
  "class type regardless of its key/value shapes.",
  '{"a" => 1, "b" => 2}\n', expect_validate=True)
R("nested-array", 5, "[[1, 2], [3, 4]] : an Array of (an Array of Int).",
  "[[1, 2], [3, 4]]\n", expect_validate=True)
R("array-index-with-claim", 5,
  "Indexing is just `#[]`, a send -- the real Expr has no dedicated index "
  "constructor. Not in the builtin table, but an explicit claim on this send "
  "node supplies its type.",
  "[1, 2, 3][0]\n",
  claims=lambda p: [claim(p, lambda n: is_head(n, "send", **{"2": "[]"}), T_INT)],
  expect_validate=True)
R("array-index-no-claim", 5,
  "Same shape as array-index-with-claim but with no claim: rejected.",
  "[1, 2, 3][0]\n", expect_validate=False)
R("hash-index-with-claim", 5,
  'Hash indexing is also just `#[]`. An explicit claim supplies its type.',
  '{"a" => 1}["a"]\n',
  claims=lambda p: [claim(p, lambda n: is_head(n, "send", **{"2": "[]"}), T_INT)],
  expect_validate=True)
R("hash-index-no-claim", 5,
  "Same shape as hash-index-with-claim but with no claim: rejected.",
  '{"a" => 1}["a"]\n', expect_validate=False)

# --- Tier 6: top-level functions, declared via a claim on the `def` node ----

_add_claim = lambda p: [claim(p, lambda n: is_head(n, "def", **{"1": "add"}),
                               arrow_of([T_INT, T_INT], T_INT))]
R("simple-fun", 6,
  "def add(x, y) = x + y; add(1, 2) : Int -- add's signature is a claim on its "
  "own `def` node (an arrow spine), the only mechanism this package has for a "
  "declared function type; there is no separate FunCert format.",
  "def add(x, y)\n  x + y\nend\nadd(1, 2)\n", claims=_add_claim, expect_validate=True)
R("fun-wrong-arity", 6,
  "The same add/claim as simple-fun, but called with one argument instead of "
  "two: Ty.subTys fails on the length mismatch and the call site is rejected, "
  "even though add's own body is fine.",
  "def add(x, y)\n  x + y\nend\nadd(1)\n", claims=_add_claim, expect_validate=False)
R("fun-body-mismatch", 6,
  "def bad(x) = x + true is claimed to have signature (Int) -> Int, but its body "
  "does not even type-check (Int + Bool has no builtin rule) -- defsOk rejects "
  "it before the call site is ever reached.",
  "def bad(x)\n  x + true\nend\nbad(1)\n",
  claims=lambda p: [claim(p, lambda n: is_head(n, "def", **{"1": "bad"}),
                           arrow_of([T_INT], T_INT))],
  expect_validate=False)
R("fun-dishonest-return-claim", 6,
  "def get5 = 5 really returns an Int, but its claim dishonestly declares Str: "
  "defsOk checks the body's actual inferred type against the *claimed* retTy and "
  "rejects the mismatch structurally -- no execution is needed to catch a "
  "dishonest declared signature.",
  "def get5\n  5\nend\nget5()\n",
  claims=lambda p: [claim(p, lambda n: is_head(n, "def", **{"1": "get5"}),
                           arrow_of([], T_STR))],
  expect_validate=False)
R("fun-unknown-call", 6,
  "A call to undefined_fn, declared nowhere: no def, no claim, so validate "
  "rejects it exactly like unknown-method-no-claim did for sends.",
  "undefined_fn(1)\n", expect_validate=False)
R("fun-calling-another-fun", 6,
  "def inc(x) = x + 1; def twice(x) = inc(inc(x)); twice(3) : Int -- both "
  "top-level defs are collected into the function-signature table *before* any "
  "body is checked, so twice's body can call inc regardless of source order.",
  "def inc(x)\n  x + 1\nend\ndef twice(x)\n  inc(inc(x))\nend\ntwice(3)\n",
  claims=lambda p: [
      claim(p, lambda n: is_head(n, "def", **{"1": "inc"}), arrow_of([T_INT], T_INT)),
      claim(p, lambda n: is_head(n, "def", **{"1": "twice"}), arrow_of([T_INT], T_INT)),
  ],
  expect_validate=True)
R("fun-three-params", 6,
  "def sum3(a, b, c) = a + b + c; sum3(1, 2, 3) : Int -- three required params, "
  "each a separate nested send.",
  "def sum3(a, b, c)\n  a + b + c\nend\nsum3(1, 2, 3)\n",
  claims=lambda p: [claim(p, lambda n: is_head(n, "def", **{"1": "sum3"}),
                           arrow_of([T_INT, T_INT, T_INT], T_INT))],
  expect_validate=True)
R("fun-returning-array", 6,
  "def make_pair(x, y) = [x, y]; make_pair(1, 2) : an Array of Int -- a "
  "function's claimed return type can be any Ty this checker can synthesize, "
  "including arrayOf.",
  "def make_pair(x, y)\n  [x, y]\nend\nmake_pair(1, 2)\n",
  claims=lambda p: [claim(p, lambda n: is_head(n, "def", **{"1": "make_pair"}),
                           arrow_of([T_INT, T_INT], T_ARRAYOF(T_INT)))],
  expect_validate=True)
R("fun-recursive-factorial", 6,
  "def fact(n) = if n <= 1 then 1 else n * fact(n - 1); fact(4) : Int -- fact "
  "calls itself by name, resolved through the same function-signature table "
  "its own claim populated (self-reference works because buildFunSigs collects "
  "every top-level def's claim before any body is checked).",
  "def fact(n)\n  if n <= 1\n    1\n  else\n    n * fact(n - 1)\n  end\nend\nfact(4)\n",
  claims=lambda p: [claim(p, lambda n: is_head(n, "def", **{"1": "fact"}),
                           arrow_of([T_INT], T_INT))],
  expect_validate=True)

# --- Tier 7: classes -- FRONTIER (chk has no rule for class'/module'/defs/ ---
# super', and `.const` is not yet typed as Ty.clsOf, so validate rejects every
# rung here regardless of claims; empty claims throughout, since there is
# nothing this checker could currently do with one for these constructs. Real,
# varied real-Ruby class programs are still worth having on hand -- see
# AGENTS.md's Frontier section for what unlocks this tier.

R("class-basic", 7,
  "class Point; def initialize(x, y); @x = x; @y = y; end; def getX; @x; end; "
  "end; Point.new(1, 2).getX -- construction, an ivar write in initialize, an "
  "ivar read in another method.",
  "class Point\n  def initialize(x, y)\n    @x = x\n    @y = y\n  end\n\n"
  "  def getX\n    @x\n  end\nend\n\nPoint.new(1, 2).getX\n",
  expect_validate=False)
R("class-method-with-param", 7,
  "class Counter; def initialize(n); @n = n; end; def add(k); @n + k; end; "
  "end; c = Counter.new(10); c.add(5) -- an instance stored in a local, then a "
  "method call taking its own argument.",
  "class Counter\n  def initialize(n)\n    @n = n\n  end\n\n"
  "  def add(k)\n    @n + k\n  end\nend\n\nc = Counter.new(10)\nc.add(5)\n",
  expect_validate=False)
R("class-two-getters", 7,
  "A class exposing two separate ivars through two separate getter methods, "
  "combined arithmetically at the call site.",
  "class Point\n  def initialize(x, y)\n    @x = x\n    @y = y\n  end\n\n"
  "  def getX\n    @x\n  end\n\n  def getY\n    @y\n  end\nend\n\n"
  "p = Point.new(3, 4)\np.getX + p.getY\n",
  expect_validate=False)
R("class-method-calls-method", 7,
  "A method (describe) calling another method (area) on the same object via "
  "an implicit self-send.",
  "class Rect\n  def initialize(w, h)\n    @w = w\n    @h = h\n  end\n\n"
  "  def area\n    @w * @h\n  end\n\n  def describe\n    \"area=\" + area.to_s\n  end\n"
  "end\n\nRect.new(3, 4).describe\n",
  expect_validate=False)
R("class-inheritance-field", 7,
  "class Animal; def initialize(name); @name = name; end; def speak; @name; "
  "end; end; class Dog < Animal; end; Dog.new(\"Rex\").speak -- Dog inherits "
  "both the field and the method from Animal.",
  "class Animal\n  def initialize(name)\n    @name = name\n  end\n\n"
  "  def speak\n    @name\n  end\nend\n\nclass Dog < Animal\nend\n\n"
  'Dog.new("Rex").speak\n',
  expect_validate=False)
R("class-inheritance-override", 7,
  "Dog overrides the speak method Animal also defines.",
  'class Animal\n  def speak\n    "..."\n  end\nend\n\n'
  'class Dog < Animal\n  def speak\n    "Woof"\n  end\nend\n\n'
  "Dog.new.speak\n",
  expect_validate=False)
R("class-super-call", 7,
  "Triangle's initialize calls super(3) to delegate to Shape's initialize -- "
  "the `super'` head, unrelated to anything chk models.",
  "class Shape\n  def initialize(sides)\n    @sides = sides\n  end\n\n"
  "  def sides\n    @sides\n  end\nend\n\n"
  "class Triangle < Shape\n  def initialize\n    super(3)\n  end\nend\n\n"
  "Triangle.new.sides\n",
  expect_validate=False)
R("class-multiple-instances", 7,
  "Two independent Point instances, their getX results combined.",
  "class Point\n  def initialize(x)\n    @x = x\n  end\n\n  def getX\n    @x\n  end\nend\n\n"
  "a = Point.new(1)\nb = Point.new(2)\na.getX + b.getX\n",
  expect_validate=False)
R("class-no-initialize", 7,
  "A class with no initialize at all -- real Ruby's default #new takes no "
  "arguments.",
  'class Greeter\n  def hi\n    "hi"\n  end\nend\n\nGreeter.new.hi\n',
  expect_validate=False)
R("class-ivar-lazy-nil", 7,
  "reveal reads @secret, which no method ever assigns -- real Ruby answers "
  "nil for an unset ivar rather than raising, a real nuance any future "
  "class-typing rule will have to account for.",
  "class Box\n  def reveal\n    @secret\n  end\nend\n\nBox.new.reveal\n",
  expect_validate=False)
R("class-array-of-instances", 7,
  "An array literal containing two constructed instances.",
  "class Point\n  def initialize(x)\n    @x = x\n  end\nend\n\n"
  "[Point.new(1), Point.new(2)]\n",
  expect_validate=False)
R("class-instance-in-hash", 7,
  "A hash literal whose value is a constructed instance.",
  'class Point\n  def initialize(x)\n    @x = x\n  end\nend\n\n'
  '{"origin" => Point.new(0)}\n',
  expect_validate=False)
R("class-factory-method", 7,
  "Point.origin is a singleton (self.) method on the class itself that "
  "constructs and returns an ordinary instance -- `defs` nested inside a "
  "`class'`, the same shape a module's `self.` methods use.",
  "class Point\n  def initialize(x, y)\n    @x = x\n    @y = y\n  end\n\n"
  "  def self.origin\n    new(0, 0)\n  end\nend\n\nPoint.origin\n",
  expect_validate=False)
R("class-setter-method", 7,
  "grow reassigns @size to a new value derived from the old one -- an "
  "ivar vasgn whose right-hand side reads the same ivar.",
  "class Box\n  def initialize(size)\n    @size = size\n  end\n\n"
  "  def grow\n    @size = @size + 1\n  end\nend\n\nBox.new(1).grow\n",
  expect_validate=False)
R("class-instance-as-fun-arg", 7,
  "A top-level function taking an instance as a parameter and calling a "
  "method on it -- mixing tier 6's function dispatch with a class instance.",
  "class Point\n  def initialize(x)\n    @x = x\n  end\n\n  def getX\n    @x\n  end\nend\n\n"
  "def describe(p)\n  p.getX\nend\n\ndescribe(Point.new(5))\n",
  expect_validate=False)
R("class-self-returning-method", 7,
  "myself returns self; the result is then chained into another method call.",
  "class Point\n  def initialize(x)\n    @x = x\n  end\n\n  def getX\n    @x\n  end\n\n"
  "  def myself\n    self\n  end\nend\n\nPoint.new(7).myself.getX\n",
  expect_validate=False)

# --- Tier 8: modules -- FRONTIER (same reasons as tier 7) --------------------

R("module-basic", 8, "module M; def self.foo; 1; end; end; M.foo : Int at runtime.",
  "module M\n  def self.foo\n    1\n  end\nend\n\nM.foo\n", expect_validate=False)
R("module-method-with-arg", 8,
  'module Greeter; def self.hello(name); "hi " + name; end; end; '
  'Greeter.hello("sam").',
  'module Greeter\n  def self.hello(name)\n    "hi " + name\n  end\nend\n\n'
  'Greeter.hello("sam")\n',
  expect_validate=False)
R("module-multiple-methods", 8,
  "A module with two independent singleton methods.",
  "module M\n  def self.foo\n    1\n  end\n\n  def self.bar\n    2\n  end\nend\n\n"
  "M.foo + M.bar\n",
  expect_validate=False)
R("module-method-calls-method", 8,
  "self.describe calls self.value, another singleton method on the same "
  "module, via an implicit self-send.",
  "module M\n  def self.value\n    21\n  end\n\n  def self.describe\n    value * 2\n  end\nend\n\n"
  "M.describe\n",
  expect_validate=False)
R("module-with-arithmetic", 8,
  "A module method doing ordinary arithmetic on its arguments.",
  "module Calc\n  def self.add(a, b)\n    a + b\n  end\nend\n\nCalc.add(1, 2)\n",
  expect_validate=False)
R("module-calling-another-module", 8,
  "M1.foo calls M2.bar -- two separate modules, one calling into the other.",
  "module M2\n  def self.bar\n    10\n  end\nend\n\n"
  "module M1\n  def self.foo\n    M2.bar + 1\n  end\nend\n\nM1.foo\n",
  expect_validate=False)
R("module-returns-array", 8,
  "A module method returning an array literal.",
  "module M\n  def self.pair\n    [1, 2]\n  end\nend\n\nM.pair\n",
  expect_validate=False)
R("module-boolean-method", 8,
  "A module method returning the result of a comparison.",
  "module M\n  def self.positive?(n)\n    n > 0\n  end\nend\n\nM.positive?(5)\n",
  expect_validate=False)
R("module-nested-call-chain", 8,
  "M.greeting.length chains a module call into a builtin method call on its "
  "result.",
  'module M\n  def self.greeting\n    "hi"\n  end\nend\n\nM.greeting.length\n',
  expect_validate=False)
R("module-passing-multiple-args", 8,
  "A module method taking three arguments.",
  "module M\n  def self.sum3(a, b, c)\n    a + b + c\n  end\nend\n\nM.sum3(1, 2, 3)\n",
  expect_validate=False)


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
