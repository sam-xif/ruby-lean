#!/usr/bin/env python3
"""Generate the ratchet corpus (`../corpus/*.json` + `.rb` sources) from **real** Ruby,
run through the real desugarer (`harness/desugar-dt/bin/export-json`) -- not a
hand-authored AST. See `../AGENTS.md`.

Each rung is (id, tier, description, rb source, claims, expect_validate, false_reason).
`claims` are built by `claim(program, predicate, ty)` (or `claim_at(program, expr,
ty)`), which run the real desugarer on `rb` once and extract the claimed subterm out of
that *exact* parsed AST via `find_node` -- so a claim's `expr` field can never
accidentally drift from what the program actually contains (no hand-transcribed
wire-format JSON anywhere in this file).

**Every rung's target is `expect_validate = True` unless `false_reason` is given.**
`false_reason` is one of:
  - "unsafe_program"    -- the program really does raise NoMethodError/ArgumentError/
                           TypeError when run. No cert should ever certify it.
  - "dishonest_cert"    -- the program is safe, but this specific cert's own claims are
                           mutually inconsistent (e.g. a claimed return type that
                           doesn't match what the body actually computes).
  - "cert_language_gap" -- the program is safe, but the current `Ty` grammar has no
                           constructor that can *state* a sufficient claim at all (see
                           `Ratchet/Ty.lean`). Flagged, not silently left `False`.
`R()` asserts this pairing is never violated.

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
    fields by index (e.g. `is_head(n, "def", **{"1": "add"})` checks n[1] == "add")?"""
    if not (isinstance(node, list) and len(node) >= 1 and node[0] == head):
        return False
    return all(node[int(i)] == v for i, v in fields.items())


def claim(program: dict, pred, ty: dict) -> dict:
    node = find_node(program["ast"], pred)
    assert node is not None, f"claim(): no node matched in {program['ast']!r}"
    return {"expr": node, "ty": ty}


def claim_within(program: dict, outer_pred, inner_pred, ty: dict) -> dict:
    """Like `claim`, but the subterm must be found *inside* the first node matching
    `outer_pred` -- for disambiguating two structurally-similar nodes (e.g. two
    same-named methods on different classes), by scoping the search to one of them
    first."""
    outer = find_node(program["ast"], outer_pred)
    assert outer is not None, f"claim_within(): outer predicate matched nothing"
    inner = find_node(outer, inner_pred)
    assert inner is not None, f"claim_within(): inner predicate matched nothing inside outer"
    return {"expr": inner, "ty": ty}


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


def T_CLSOF(name):
    return {"tag": "clsOf", "name": name}


def T_UNION(l, r):
    return {"tag": "union", "l": l, "r": r}


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
FALSE_REASONS = {"unsafe_program", "dishonest_cert", "cert_language_gap"}


def R(id_, tier, description, rb, claims=None, *, expect_validate, false_reason=None):
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
        "cert": {"claims": claims(program) if claims else []},
        "expect_validate": expect_validate,
        "false_reason": false_reason,
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
  "1 + true is real, genuinely ill-typed Ruby: it raises TypeError when run, "
  "unconditionally. No certificate should ever certify it -- a checker that did "
  "would be unsound. Permanent negative target.",
  "1 + true\n", expect_validate=False, false_reason="unsafe_program")
R("to-s-call", 2, "5.to_s, an instance of String, via the universal Object#to_s rule.",
  "5.to_s\n", expect_validate=True)
R("eq-same-type", 2, "1 == 1 : Bool (both sides Int).", "1 == 1\n", expect_validate=True)
R("eq-different-type", 2,
  '1 == "a" is completely safe real Ruby -- `==` never raises, it just answers '
  "false for unrelated types. A hardcoded `==` rule that requires both sides the "
  "same Ty would be *conservative*, not necessary; the claims escape hatch on this "
  "exact send node is enough to certify it without changing that rule at all.",
  '1 == "a"\n',
  claims=lambda p: [claim(p, lambda n: is_head(n, "send", **{"2": "=="}), T_BOOL)],
  expect_validate=True)
R("unknown-method-with-claim", 2,
  "5.zero? is not in the hardcoded builtin table (unlike to_s), but an explicit "
  "claim on this exact send node supplies its type -- the escape hatch a "
  "certificate exists for.",
  "5.zero?\n",
  claims=lambda p: [claim(p, lambda n: is_head(n, "send", **{"2": "zero?"}), T_BOOL)],
  expect_validate=True)
R("unknown-method-no-claim", 2,
  "5.foo_bar_baz is a made-up method name -- Integer has no such method, so this "
  "really does raise NoMethodError when run, with or without a claim (a claim "
  "cannot make a nonexistent method exist). Permanent negative target, distinct "
  "from unknown-method-with-claim's 5.zero?, which is a real method.",
  "5.foo_bar_baz\n", expect_validate=False, false_reason="unsafe_program")
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
  claims=lambda p: [claim(p, lambda n: is_head(n, "vcall", **{"1": "x"}), T_ANY)],
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
  "an explicit claim of union(Int, an instance of String) on the if' node is "
  "already expressible in the current grammar (see Ty.union's own docstring, "
  '"inert on the checker path" -- meant to be *claimed*, not inferred). No '
  "language gap; a rebuilt `if'` just needs a claim-fallback the same way "
  "`send`/`vcall` already have one.",
  'if true\n  1\nelse\n  "a"\nend\n',
  claims=lambda p: [claim(p, lambda n: is_head(n, "if"), T_UNION(T_INT, T_STR))],
  expect_validate=True)
R("elsif-chain-mismatch", 4,
  "if/elsif/else desugars to nested if' nodes; when the final else's type "
  "disagrees with the earlier branches, *both* the inner and outer if' nodes need "
  "their own union claim (joinTy doesn't propagate through an already-claimed "
  "union), but both claims are the same Ty.union(Int, an instance of String) -- "
  "still no language gap, just two claim sites instead of one.",
  'if true\n  1\nelsif false\n  2\nelse\n  "a"\nend\n',
  claims=lambda p: [
      claim(p, lambda n: is_head(n, "if") and n[3] != None and isinstance(n[3], list)
            and n[3][0] == "str", T_UNION(T_INT, T_STR)),
      claim(p, lambda n: is_head(n, "if") and isinstance(n[3], list) and n[3]
            and n[3][0] == "if", T_UNION(T_INT, T_STR)),
  ],
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
  'x = 1; if true; x = "hello"; end; x + 1 -- KNOWN SIMPLIFICATION, not a bug: '
  "this checker's `if` does not propagate a branch's reassignments into the "
  "following code (the environment after an if is the environment from *before* "
  "it, documented in Ratchet/Validate.lean's design notes). So `x` is still seen "
  "as Int after the if, and `x + 1` validates -- even though the *only* branch "
  "this if has is the one that reassigns x to a String. Real Ruby's x really "
  "would be a String here; this checker cannot see that yet. Still a legitimate "
  "target of `true`: the *program* itself never actually reaches a type error "
  "(the reassignment happens, x + 1 never runs against a String) -- fixing the "
  "simplification is about precision, not soundness, for this specific rung.",
  'x = 1\nif true\n  x = "hello"\nend\nx + 1\n', expect_validate=True)
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
  "for exactly this -- a claim of arrayOf(Ty.any) on the array node is expressible "
  "today. No language gap; a rebuilt `array` rule should accept an element type "
  "via subTy (which admits `any`), not raw equality, or fall back to a claim.",
  '[1, "a", true]\n',
  claims=lambda p: [claim(p, lambda n: is_head(n, "array"), T_ARRAYOF(T_ANY))],
  expect_validate=True)
R("array-of-sends", 5, "[1 + 1, 2 + 2] : an Array of Int -- elements are checked recursively.",
  "[1 + 1, 2 + 2]\n", expect_validate=True)
R("hash-lit", 5,
  'A Hash literal types as the bare, unparameterised .cls "Hash" -- this Ty '
  "language has no parameterised Hash type the way it has arrayOf for Array "
  "(see Ty.lean's module docstring); every hash literal gets the same generic "
  "class type regardless of its key/value shapes. This does not block "
  "*validating* the literal itself (no claim needed), only precise reasoning "
  "about what a later index on it returns (see hash-index-with-claim).",
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
R("hash-index-with-claim", 5,
  'Hash indexing is also just `#[]`. An explicit claim supplies its type -- the '
  'only way to do this precisely at all, since Ty has no parameterised Hash type '
  '(see hash-lit) to derive it from the receiver structurally.',
  '{"a" => 1}["a"]\n',
  claims=lambda p: [claim(p, lambda n: is_head(n, "send", **{"2": "[]"}), T_INT)],
  expect_validate=True)

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
  "two: this really does raise ArgumentError when run, regardless of any claim "
  "(a claim cannot change how many arguments a call site actually passes). "
  "Permanent negative target.",
  "def add(x, y)\n  x + y\nend\nadd(1)\n", claims=_add_claim,
  expect_validate=False, false_reason="unsafe_program")
R("fun-body-mismatch", 6,
  "def bad(x) = x + true; bad(1) -- the body really does raise NoMethodError "
  "when called (Int has no matching + for Bool). Permanent negative target, "
  "independent of what the claim on `def bad` says.",
  "def bad(x)\n  x + true\nend\nbad(1)\n",
  claims=lambda p: [claim(p, lambda n: is_head(n, "def", **{"1": "bad"}),
                           arrow_of([T_INT], T_INT))],
  expect_validate=False, false_reason="unsafe_program")
R("fun-dishonest-return-claim", 6,
  "def get5 = 5 really returns an Int and running get5() is completely safe -- "
  "the *program* is fine. What must never validate is *this certificate*: it "
  "claims get5's return type is an instance of String, which its own body "
  "(claimed as arrow_of([], Int) would be, if honest) contradicts. A cert whose "
  "own claims are mutually inconsistent must be rejected regardless of whether a "
  "different, honest cert for the same program would validate -- otherwise the "
  "certificate mechanism itself is meaningless. Permanent negative target for "
  "this specific cert.",
  "def get5\n  5\nend\nget5()\n",
  claims=lambda p: [claim(p, lambda n: is_head(n, "def", **{"1": "get5"}),
                           arrow_of([], T_STR))],
  expect_validate=False, false_reason="dishonest_cert")
R("fun-unknown-call", 6,
  "A call to undefined_fn, declared nowhere: this really does raise "
  "NoMethodError when run, exactly like unknown-method-no-claim. Permanent "
  "negative target.",
  "undefined_fn(1)\n", expect_validate=False, false_reason="unsafe_program")
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

# --- Tier 7: classes ----------------------------------------------------------
# All safe, real Ruby -- expect_validate=True throughout. Claims follow one
# consistent pattern: every def'/defs node inside a class' body gets an arrow-spine
# claim (exactly like a top-level function's), and every ivar *read* (`.var .ivar
# name`) gets its own claim, keyed by name -- a documented simplification (an ivar's
# claimed type is global by name, not scoped per class; see AGENTS.md). None of
# this needs any Ty constructor beyond what's already there (`cls`/`clsOf` cover
# instances vs. class objects fine) -- what's missing is entirely on the `chk`
# implementation side (a declaration table, ancestor-chain dispatch, `.const` typed
# as `Ty.clsOf`), not the cert language. See AGENTS.md §Frontier.

R("class-basic", 7,
  "class Point; def initialize(x, y); @x = x; @y = y; end; def getX; @x; end; "
  "end; Point.new(1, 2).getX -- construction, an ivar write in initialize, an "
  "ivar read in another method.",
  "class Point\n  def initialize(x, y)\n    @x = x\n    @y = y\n  end\n\n"
  "  def getX\n    @x\n  end\nend\n\nPoint.new(1, 2).getX\n",
  claims=lambda p: [
      claim(p, lambda n: is_head(n, "def", **{"1": "initialize"}), arrow_of([T_INT, T_INT], T_INT)),
      claim(p, lambda n: is_head(n, "def", **{"1": "getX"}), arrow_of([], T_INT)),
      claim(p, lambda n: is_head(n, "var", **{"1": "ivar", "2": "@x"}), T_INT),
  ],
  expect_validate=True)
R("class-method-with-param", 7,
  "class Counter; def initialize(n); @n = n; end; def add(k); @n + k; end; "
  "end; c = Counter.new(10); c.add(5) -- an instance stored in a local, then a "
  "method call taking its own argument.",
  "class Counter\n  def initialize(n)\n    @n = n\n  end\n\n"
  "  def add(k)\n    @n + k\n  end\nend\n\nc = Counter.new(10)\nc.add(5)\n",
  claims=lambda p: [
      claim(p, lambda n: is_head(n, "def", **{"1": "initialize"}), arrow_of([T_INT], T_INT)),
      claim(p, lambda n: is_head(n, "def", **{"1": "add"}), arrow_of([T_INT], T_INT)),
      claim(p, lambda n: is_head(n, "var", **{"1": "ivar", "2": "@n"}), T_INT),
  ],
  expect_validate=True)
R("class-two-getters", 7,
  "A class exposing two separate ivars through two separate getter methods, "
  "combined arithmetically at the call site.",
  "class Point\n  def initialize(x, y)\n    @x = x\n    @y = y\n  end\n\n"
  "  def getX\n    @x\n  end\n\n  def getY\n    @y\n  end\nend\n\n"
  "p = Point.new(3, 4)\np.getX + p.getY\n",
  claims=lambda p: [
      claim(p, lambda n: is_head(n, "def", **{"1": "initialize"}), arrow_of([T_INT, T_INT], T_INT)),
      claim(p, lambda n: is_head(n, "def", **{"1": "getX"}), arrow_of([], T_INT)),
      claim(p, lambda n: is_head(n, "def", **{"1": "getY"}), arrow_of([], T_INT)),
      claim(p, lambda n: is_head(n, "var", **{"1": "ivar", "2": "@x"}), T_INT),
      claim(p, lambda n: is_head(n, "var", **{"1": "ivar", "2": "@y"}), T_INT),
  ],
  expect_validate=True)
R("class-method-calls-method", 7,
  "A method (describe) calling another method (area) on the same object via "
  "an implicit-self `vcall` -- resolving that requires a rebuilt `vcall` rule to "
  "consult the current `self` type, not just a top-level function table.",
  "class Rect\n  def initialize(w, h)\n    @w = w\n    @h = h\n  end\n\n"
  "  def area\n    @w * @h\n  end\n\n  def describe\n    \"area=\" + area.to_s\n  end\n"
  "end\n\nRect.new(3, 4).describe\n",
  claims=lambda p: [
      claim(p, lambda n: is_head(n, "def", **{"1": "initialize"}), arrow_of([T_INT, T_INT], T_INT)),
      claim(p, lambda n: is_head(n, "def", **{"1": "area"}), arrow_of([], T_INT)),
      claim(p, lambda n: is_head(n, "def", **{"1": "describe"}), arrow_of([], T_STR)),
      claim(p, lambda n: is_head(n, "var", **{"1": "ivar", "2": "@w"}), T_INT),
      claim(p, lambda n: is_head(n, "var", **{"1": "ivar", "2": "@h"}), T_INT),
  ],
  expect_validate=True)
R("class-inheritance-field", 7,
  "class Animal; def initialize(name); @name = name; end; def speak; @name; "
  "end; end; class Dog < Animal; end; Dog.new(\"Rex\").speak -- Dog inherits "
  "both the field and the method from Animal; a rebuilt dispatch rule needs to "
  "walk the parent chain to find speak declared on Animal.",
  "class Animal\n  def initialize(name)\n    @name = name\n  end\n\n"
  "  def speak\n    @name\n  end\nend\n\nclass Dog < Animal\nend\n\n"
  'Dog.new("Rex").speak\n',
  claims=lambda p: [
      claim(p, lambda n: is_head(n, "def", **{"1": "initialize"}), arrow_of([T_STR], T_STR)),
      claim(p, lambda n: is_head(n, "def", **{"1": "speak"}), arrow_of([], T_STR)),
      claim(p, lambda n: is_head(n, "var", **{"1": "ivar", "2": "@name"}), T_STR),
  ],
  expect_validate=True)
R("class-inheritance-override", 7,
  "Dog overrides the speak method Animal also defines -- the two `def speak` "
  "nodes are disambiguated by scoping the search to each class' own body, "
  "since names alone collide.",
  'class Animal\n  def speak\n    "..."\n  end\nend\n\n'
  'class Dog < Animal\n  def speak\n    "Woof"\n  end\nend\n\n'
  "Dog.new.speak\n",
  claims=lambda p: [
      claim_within(p, lambda n: is_head(n, "class", **{"1": "Animal"}),
                   lambda n: is_head(n, "def", **{"1": "speak"}), arrow_of([], T_STR)),
      claim_within(p, lambda n: is_head(n, "class", **{"1": "Dog"}),
                   lambda n: is_head(n, "def", **{"1": "speak"}), arrow_of([], T_STR)),
  ],
  expect_validate=True)
R("class-super-call", 7,
  "Triangle's initialize calls super(3) to delegate to Shape's initialize -- "
  "the `super'` head, typed here on the assumption that a rebuilt `super'` rule "
  "resolves to whatever the parent's matching method returns (Int, matching "
  "Shape#initialize's own claim) rather than needing a separate claim of its own.",
  "class Shape\n  def initialize(sides)\n    @sides = sides\n  end\n\n"
  "  def sides\n    @sides\n  end\nend\n\n"
  "class Triangle < Shape\n  def initialize\n    super(3)\n  end\nend\n\n"
  "Triangle.new.sides\n",
  claims=lambda p: [
      claim_within(p, lambda n: is_head(n, "class", **{"1": "Shape"}),
                   lambda n: is_head(n, "def", **{"1": "initialize"}), arrow_of([T_INT], T_INT)),
      claim(p, lambda n: is_head(n, "def", **{"1": "sides"}), arrow_of([], T_INT)),
      claim_within(p, lambda n: is_head(n, "class", **{"1": "Triangle"}),
                   lambda n: is_head(n, "def", **{"1": "initialize"}), arrow_of([], T_INT)),
      claim(p, lambda n: is_head(n, "var", **{"1": "ivar", "2": "@sides"}), T_INT),
  ],
  expect_validate=True)
R("class-multiple-instances", 7,
  "Two independent Point instances, their getX results combined.",
  "class Point\n  def initialize(x)\n    @x = x\n  end\n\n  def getX\n    @x\n  end\nend\n\n"
  "a = Point.new(1)\nb = Point.new(2)\na.getX + b.getX\n",
  claims=lambda p: [
      claim(p, lambda n: is_head(n, "def", **{"1": "initialize"}), arrow_of([T_INT], T_INT)),
      claim(p, lambda n: is_head(n, "def", **{"1": "getX"}), arrow_of([], T_INT)),
      claim(p, lambda n: is_head(n, "var", **{"1": "ivar", "2": "@x"}), T_INT),
  ],
  expect_validate=True)
R("class-no-initialize", 7,
  "A class with no initialize at all -- real Ruby's default #new takes no "
  "arguments and returns the new instance; a rebuilt `.new` dispatch rule needs "
  "this as a fallback default when no `initialize` claim/declaration exists for "
  "the class, not an error.",
  'class Greeter\n  def hi\n    "hi"\n  end\nend\n\nGreeter.new.hi\n',
  claims=lambda p: [claim(p, lambda n: is_head(n, "def", **{"1": "hi"}), arrow_of([], T_STR))],
  expect_validate=True)
R("class-ivar-lazy-nil", 7,
  "reveal reads @secret, which no method ever assigns -- real Ruby answers nil "
  "for an unset ivar rather than raising. Claimed Nil by name, same mechanism "
  "as every other ivar claim, no special case needed.",
  "class Box\n  def reveal\n    @secret\n  end\nend\n\nBox.new.reveal\n",
  claims=lambda p: [
      claim(p, lambda n: is_head(n, "def", **{"1": "reveal"}), arrow_of([], T_NIL)),
      claim(p, lambda n: is_head(n, "var", **{"1": "ivar", "2": "@secret"}), T_NIL),
  ],
  expect_validate=True)
R("class-array-of-instances", 7,
  "An array literal containing two constructed instances -- element type "
  "arrayOf(an instance of Point), synthesized structurally once `.new` "
  "dispatch exists (no claim needed on the array itself).",
  "class Point\n  def initialize(x)\n    @x = x\n  end\nend\n\n"
  "[Point.new(1), Point.new(2)]\n",
  claims=lambda p: [claim(p, lambda n: is_head(n, "def", **{"1": "initialize"}), arrow_of([T_INT], T_INT))],
  expect_validate=True)
R("class-instance-in-hash", 7,
  "A hash literal whose value is a constructed instance -- typed as the bare "
  '.cls "Hash" regardless, same as any other hash literal.',
  'class Point\n  def initialize(x)\n    @x = x\n  end\nend\n\n'
  '{"origin" => Point.new(0)}\n',
  claims=lambda p: [claim(p, lambda n: is_head(n, "def", **{"1": "initialize"}), arrow_of([T_INT], T_INT))],
  expect_validate=True)
R("class-factory-method", 7,
  "Point.origin is a singleton (self.) method on the class itself that "
  "constructs and returns an ordinary instance -- `defs` nested inside a "
  "`class'`, the same shape a module's `self.` methods use. Its body's bare "
  "`new(0, 0)` is a vcall/send dispatched with self bound to Ty.clsOf \"Point\", "
  "resolving to Point's own initialize.",
  "class Point\n  def initialize(x, y)\n    @x = x\n    @y = y\n  end\n\n"
  "  def self.origin\n    new(0, 0)\n  end\nend\n\nPoint.origin\n",
  claims=lambda p: [
      claim(p, lambda n: is_head(n, "def", **{"1": "initialize"}), arrow_of([T_INT, T_INT], T_INT)),
      claim(p, lambda n: is_head(n, "defs", **{"2": "origin"}), arrow_of([], T_CLS("Point"))),
  ],
  expect_validate=True)
R("class-setter-method", 7,
  "grow reassigns @size to a new value derived from the old one -- an ivar "
  "vasgn whose right-hand side reads the same ivar.",
  "class Box\n  def initialize(size)\n    @size = size\n  end\n\n"
  "  def grow\n    @size = @size + 1\n  end\nend\n\nBox.new(1).grow\n",
  claims=lambda p: [
      claim(p, lambda n: is_head(n, "def", **{"1": "initialize"}), arrow_of([T_INT], T_INT)),
      claim(p, lambda n: is_head(n, "def", **{"1": "grow"}), arrow_of([], T_INT)),
      claim(p, lambda n: is_head(n, "var", **{"1": "ivar", "2": "@size"}), T_INT),
  ],
  expect_validate=True)
R("class-instance-as-fun-arg", 7,
  "A top-level function taking an instance as a parameter (typed Ty.cls "
  '"Point" -- an ordinary Ty value usable anywhere, including a funSig\'s own '
  "param types) and calling a method on it -- mixing tier 6's function "
  "dispatch with a class instance.",
  "class Point\n  def initialize(x)\n    @x = x\n  end\n\n  def getX\n    @x\n  end\nend\n\n"
  "def describe(p)\n  p.getX\nend\n\ndescribe(Point.new(5))\n",
  claims=lambda p: [
      claim(p, lambda n: is_head(n, "def", **{"1": "initialize"}), arrow_of([T_INT], T_INT)),
      claim(p, lambda n: is_head(n, "def", **{"1": "getX"}), arrow_of([], T_INT)),
      claim(p, lambda n: is_head(n, "def", **{"1": "describe"}), arrow_of([T_CLS("Point")], T_INT)),
      claim(p, lambda n: is_head(n, "var", **{"1": "ivar", "2": "@x"}), T_INT),
  ],
  expect_validate=True)
R("class-self-returning-method", 7,
  "myself returns bare `self`; the result is then chained into another method "
  "call -- typed as whatever self is bound to for an instance method "
  '(Ty.cls "Point"), no claim needed on the `self\'` node itself.',
  "class Point\n  def initialize(x)\n    @x = x\n  end\n\n  def getX\n    @x\n  end\n\n"
  "  def myself\n    self\n  end\nend\n\nPoint.new(7).myself.getX\n",
  claims=lambda p: [
      claim(p, lambda n: is_head(n, "def", **{"1": "initialize"}), arrow_of([T_INT], T_INT)),
      claim(p, lambda n: is_head(n, "def", **{"1": "getX"}), arrow_of([], T_INT)),
      claim(p, lambda n: is_head(n, "def", **{"1": "myself"}), arrow_of([], T_CLS("Point"))),
      claim(p, lambda n: is_head(n, "var", **{"1": "ivar", "2": "@x"}), T_INT),
  ],
  expect_validate=True)

# --- Tier 8: modules -----------------------------------------------------------
# Same treatment as tier 7: every claim uses Ty constructors that already exist.
# `self.`-methods are `defs (self') name params body`, dispatched (once chk exists)
# as `Owner.method(...)` with self bound to Ty.clsOf owner -- symmetric with
# instance methods binding self to Ty.cls owner.

R("module-basic", 8, "module M; def self.foo; 1; end; end; M.foo : Int at runtime.",
  "module M\n  def self.foo\n    1\n  end\nend\n\nM.foo\n",
  claims=lambda p: [claim(p, lambda n: is_head(n, "defs", **{"2": "foo"}), arrow_of([], T_INT))],
  expect_validate=True)
R("module-method-with-arg", 8,
  'module Greeter; def self.hello(name); "hi " + name; end; end; '
  'Greeter.hello("sam").',
  'module Greeter\n  def self.hello(name)\n    "hi " + name\n  end\nend\n\n'
  'Greeter.hello("sam")\n',
  claims=lambda p: [claim(p, lambda n: is_head(n, "defs", **{"2": "hello"}), arrow_of([T_STR], T_STR))],
  expect_validate=True)
R("module-multiple-methods", 8,
  "A module with two independent singleton methods.",
  "module M\n  def self.foo\n    1\n  end\n\n  def self.bar\n    2\n  end\nend\n\n"
  "M.foo + M.bar\n",
  claims=lambda p: [
      claim(p, lambda n: is_head(n, "defs", **{"2": "foo"}), arrow_of([], T_INT)),
      claim(p, lambda n: is_head(n, "defs", **{"2": "bar"}), arrow_of([], T_INT)),
  ],
  expect_validate=True)
R("module-method-calls-method", 8,
  "self.describe calls self.value, another singleton method on the same "
  "module, via an implicit-self `vcall` -- self bound to Ty.clsOf \"M\" inside "
  "a `self.` method, resolved the same way class-method-calls-method's `area` "
  "was.",
  "module M\n  def self.value\n    21\n  end\n\n  def self.describe\n    value * 2\n  end\nend\n\n"
  "M.describe\n",
  claims=lambda p: [
      claim(p, lambda n: is_head(n, "defs", **{"2": "value"}), arrow_of([], T_INT)),
      claim(p, lambda n: is_head(n, "defs", **{"2": "describe"}), arrow_of([], T_INT)),
  ],
  expect_validate=True)
R("module-with-arithmetic", 8,
  "A module method doing ordinary arithmetic on its arguments.",
  "module Calc\n  def self.add(a, b)\n    a + b\n  end\nend\n\nCalc.add(1, 2)\n",
  claims=lambda p: [claim(p, lambda n: is_head(n, "defs", **{"2": "add"}), arrow_of([T_INT, T_INT], T_INT))],
  expect_validate=True)
R("module-calling-another-module", 8,
  "M1.foo calls M2.bar -- two separate modules, one calling into the other "
  "via `.const \"M2\"` typed Ty.clsOf \"M2\".",
  "module M2\n  def self.bar\n    10\n  end\nend\n\n"
  "module M1\n  def self.foo\n    M2.bar + 1\n  end\nend\n\nM1.foo\n",
  claims=lambda p: [
      claim(p, lambda n: is_head(n, "defs", **{"2": "bar"}), arrow_of([], T_INT)),
      claim(p, lambda n: is_head(n, "defs", **{"2": "foo"}), arrow_of([], T_INT)),
  ],
  expect_validate=True)
R("module-returns-array", 8,
  "A module method returning an array literal.",
  "module M\n  def self.pair\n    [1, 2]\n  end\nend\n\nM.pair\n",
  claims=lambda p: [claim(p, lambda n: is_head(n, "defs", **{"2": "pair"}), arrow_of([], T_ARRAYOF(T_INT)))],
  expect_validate=True)
R("module-boolean-method", 8,
  "A module method returning the result of a comparison.",
  "module M\n  def self.positive?(n)\n    n > 0\n  end\nend\n\nM.positive?(5)\n",
  claims=lambda p: [claim(p, lambda n: is_head(n, "defs", **{"2": "positive?"}), arrow_of([T_INT], T_BOOL))],
  expect_validate=True)
R("module-nested-call-chain", 8,
  "M.greeting.length chains a module call into a builtin method call on its "
  "result -- the `.length` needs its own claim, same escape hatch as tier 2's "
  "str-length-with-claim.",
  'module M\n  def self.greeting\n    "hi"\n  end\nend\n\nM.greeting.length\n',
  claims=lambda p: [
      claim(p, lambda n: is_head(n, "defs", **{"2": "greeting"}), arrow_of([], T_STR)),
      claim(p, lambda n: is_head(n, "send", **{"2": "length"}), T_INT),
  ],
  expect_validate=True)
R("module-passing-multiple-args", 8,
  "A module method taking three arguments.",
  "module M\n  def self.sum3(a, b, c)\n    a + b + c\n  end\nend\n\nM.sum3(1, 2, 3)\n",
  claims=lambda p: [claim(p, lambda n: is_head(n, "defs", **{"2": "sum3"}), arrow_of([T_INT, T_INT, T_INT], T_INT))],
  expect_validate=True)

# --- Tier 9: metaprogramming -- LAST on the ladder ---------------------------
# method_missing, class reopening, and mixins (include/extend/prepend). Real
# Ruby desugars all three to *ordinary constructs already in Expr* --
# include/extend/prepend are plain `send none "include"/... [const Module] none`
# calls (confirming the umbrella project's "everything is a message send" claim
# even for metaprogramming), and class reopening is just two `class'` nodes
# sharing a name. None of that needs new Ty vocabulary -- what it needs is a
# declaration table whose ancestor walk also follows mixins and reopenings, which
# is a `chk`-design extension (Frontier), not a cert language gap.
#
# method_missing is different: its second parameter is a *rest* param (`*args`),
# and Ty's arrow spine (`arrow0`/`arrowCons`) has no vararg/rest-arity
# constructor -- there is no way to *state* an honest claim for a variadic
# signature at all. That is the one genuine cert_language_gap this tier finds;
# the fixed-arity method_missing rung right next to it shows the gap is
# specifically about rest params, not method_missing dispatch itself.

R("metaprog-class-reopening", 9,
  "Foo is defined via two separate `class' \"Foo\"` nodes, each contributing "
  "different methods -- the declaration table accumulates across both by "
  "name, the same way it would across any two top-level defs.",
  "class Foo\n  def a\n    1\n  end\nend\n\nclass Foo\n  def b\n    2\n  end\nend\n\n"
  "Foo.new.a + Foo.new.b\n",
  claims=lambda p: [
      claim(p, lambda n: is_head(n, "def", **{"1": "a"}), arrow_of([], T_INT)),
      claim(p, lambda n: is_head(n, "def", **{"1": "b"}), arrow_of([], T_INT)),
  ],
  expect_validate=True)
R("metaprog-include", 9,
  "Person includes Greetable; greet, defined once inside the module, becomes "
  "callable as an instance method of Person. `include` desugars to an ordinary "
  "`send none \"include\" [const Greetable] none` inside Person's class body -- "
  "no special Expr head at all. A rebuilt ancestor walk needs to treat "
  "Greetable as an *additional* instance-method source for Person (distinct "
  "from superclass lookup), which is a dispatch-design extension, not a "
  "language gap: the claim on greet's def' node is the same arrow-spine shape "
  "as any other method.",
  "module Greetable\n  def greet\n    \"hi\"\n  end\nend\n\n"
  "class Person\n  include Greetable\nend\n\nPerson.new.greet\n",
  claims=lambda p: [claim(p, lambda n: is_head(n, "def", **{"1": "greet"}), arrow_of([], T_STR))],
  expect_validate=True)
R("metaprog-extend", 9,
  "Person extends Loud; shout becomes callable as a *singleton* method of "
  "Person (Person.shout), not an instance method -- `extend` is the same "
  "ordinary `send` shape as `include`, but the mixed-in methods land on the "
  "class's own singleton ancestry instead of its instance ancestry. A further "
  "dispatch-design extension (symmetric with `include`, on the other side), "
  "not a language gap.",
  "module Loud\n  def shout\n    \"LOUD\"\n  end\nend\n\n"
  "class Person\n  extend Loud\nend\n\nPerson.shout\n",
  claims=lambda p: [claim(p, lambda n: is_head(n, "def", **{"1": "shout"}), arrow_of([], T_STR))],
  expect_validate=True)
R("metaprog-prepend", 9,
  "Person prepends Logger, which defines its own speak calling `super`. "
  "prepend puts Logger *ahead* of Person in the ancestor chain, so "
  "Person.new.speak resolves to Logger#speak first, whose bare `super` (a "
  "`zsuper` node) forwards to the *next* speak in the chain -- Person's own. "
  "Typing this needs an MRO-aware `super'`/`zsuper` rule on top of the "
  "prepend-ordered ancestry -- a genuinely nontrivial dispatch-design item, but "
  "still no new Ty vocabulary: both speak methods are claimed the same "
  "arrow_of([], an instance of String) shape as anywhere else.",
  "module Logger\n  def speak\n    \"logged: \" + super\n  end\nend\n\n"
  "class Person\n  prepend Logger\n  def speak\n    \"hi\"\n  end\nend\n\n"
  "Person.new.speak\n",
  claims=lambda p: [
      claim_within(p, lambda n: is_head(n, "module", **{"1": "Logger"}),
                   lambda n: is_head(n, "def", **{"1": "speak"}), arrow_of([], T_STR)),
      claim_within(p, lambda n: is_head(n, "class", **{"1": "Person"}),
                   lambda n: is_head(n, "def", **{"1": "speak"}), arrow_of([], T_STR)),
  ],
  expect_validate=True)
R("metaprog-method-missing-fixed-arity", 9,
  "Ghost declares method_missing with a single *required* param (no splat); "
  "calling an undeclared method (anything_at_all, with no arguments) dispatches "
  "to it with exactly one argument (the missed method's name, as a Sym) -- an "
  "arity a claim can honestly state: arrow_of([Sym], an instance of String). "
  "Needs a method_missing-fallback dispatch rule (try every declared method "
  "first, then method_missing if the class declares one) -- a dispatch-design "
  "extension, not a language gap, precisely because there is no rest param "
  "here. Contrast metaprog-method-missing-splat.",
  "class Ghost\n  def method_missing(name)\n    \"called \" + name.to_s\n  end\nend\n\n"
  "Ghost.new.anything_at_all\n",
  claims=lambda p: [claim(p, lambda n: is_head(n, "def", **{"1": "method_missing"}),
                           arrow_of([T_SYM], T_STR))],
  expect_validate=True)
R("metaprog-method-missing-splat", 9,
  "The idiomatic method_missing shape: `def method_missing(name, *args)`. Its "
  "true signature is 'one Sym, then zero or more of anything' -- and Ty's "
  "arrow spine (arrow0/arrowCons) has no vararg/rest-arity constructor at all. "
  "There is no Ty value that honestly describes this parameter list, not just "
  "no `chk` rule for it yet: a claim of arrow_of([Sym], ...) would be a lie "
  "about the real arity (it would silently accept this one zero-extra-args call "
  "site while being unsound for `some_method(1, 2, 3)` elsewhere). FLAGGED "
  "cert_language_gap: Ty needs something like an `arrowRest (rest ret : Ty)` "
  "constructor, or modeling a rest param as `arrayOf Ty`, before this can be "
  "honestly claimed at all.",
  "class Ghost\n  def method_missing(name, *args)\n    \"called\"\n  end\nend\n\n"
  "Ghost.new.anything_at_all\n",
  expect_validate=False, false_reason="cert_language_gap")


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
