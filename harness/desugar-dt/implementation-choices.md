# Implementation Choices — desugar differential-testing harness

This file records non-critical decisions made while building the harness, so any of them
can be revisited/reverted. It is committed to git on every update (per project request)
to preserve a rollback trail.

Design reference: `../../docs/semantics/06-desugaring-and-its-testing.md` (the oracle,
the evaluation-order trace, the three-pronged corpus, the exit criterion) and
`../../docs/semantics/05-differential-testing.md` (observation normalization).

---

## C1 — Host language: Ruby, using the built-in Prism parser

**Decision.** Implement the harness (parser bridge, `desugar`, `render_core`, observer,
driver) in **Ruby**, parsing with **Prism** (bundled in the Ruby 4.0.5 we installed;
`ruby -v` shows `+PRISM`).

**Why.** `desugar` operates on a parsed Ruby AST and `render_core` emits Ruby; both are
most naturally written where a production-grade Ruby parser already lives. Prism is
CRuby's own parser, so we inherit exactly CRuby's parse decisions (e.g. bare-identifier
vs. local-read disambiguation) for free — critical, since those decisions are upstream of
desugaring.

**Consequence / relationship to Lean.** The eventual `desugar` lives in Lean. This Ruby
implementation is a **reference prototype** serving two purposes: (1) validate the
*methodology* of artifact 06 before we commit it to Lean, and (2) become a differential
oracle for the Lean port later (Lean `desugar` vs. this one on the same corpus). It is
explicitly not the final artifact.

**Revisit if.** We decide to author `desugar` directly in Lean and drive it from a
prism-JSON dump instead (Prism can emit a serialized AST); then this becomes redundant.

## C2 — RubyCore represented as tagged S-expressions (arrays)

**Decision.** RubyCore nodes are Ruby arrays with a leading `Symbol` head, e.g.
`[:send, recv, "+", [args], block]`, `[:if, c, t, e]`, `[:seq, *nodes]`. Full set in
`lib/rubycore.rb`.

**Why.** Trivial to construct, pattern-match, render, and — importantly — compare
*structurally* for the normal-form/idempotence check (artifact 06 §1). A class hierarchy
would be tidier but adds ceremony with no benefit at this scale.

**Revisit if.** The node set grows past ~25 forms, at which point typed structs may pay off.

## C3 — Fragment-restricted, not whole-Ruby

**Decision.** The harness handles a **bounded fragment** (literals, `self`, local
var read/write, `send` incl. operators and blocks with simple positional params, `if`,
`while`, `seq`, and the desugared forms below). Any Prism node outside the fragment makes
`desugar` raise `Unsupported`, and the driver classifies that program as
**OUT-OF-FRAGMENT** and skips it (with a reason) rather than failing.

**Why.** Writing a total `render_core` for all of Ruby is a large job and unnecessary to
validate the methodology. Restricting the fragment keeps `render_core` small and matches
artifact 06's "modeled fragment" framing (§3, §7). Coverage of the fragment is grown by
adding rules, not by handling everything at once.

**Desugaring rules implemented in this first slice** (each tracked for rule coverage):
`unless→if(!)`, `until→while(!)`, `&&/and→if` (with a temp to preserve single
evaluation), `||/or→if` (ditto), `x ||= e` / `x &&= e` (local), string interpolation →
`to_s` + `+` chain, and the structural mappings (`if`, `while`, `send`, `seq`, literals,
local read/write). Operators arrive from Prism already as `call_node`s, so
"operator→send" is largely Prism's doing; we map uniformly.

## C4 — Correct (single-evaluation) desugaring of `&&`/`||`

**Decision.** `a && b` desugars to `t = a; if t then b else t` using a **fresh temp** (not
the naive `if a then b else a`, which evaluates `a` twice). Same for `||`.

**Why.** Single-evaluation is the real semantics and exactly the obligation the
evaluation-order trace exists to check (artifact 06 §2). The naive form is available
behind `DESUGAR_BUG=1` purely to demonstrate the harness *catches* the double-evaluation
(see harness README); it is never the default.

**Temp naming.** `__dt_tN` with a per-`desugar`-call counter reset to 0, so output is
deterministic (required for the normal-form check and for reproducible diffs).

## C5 — Observation = (stdout, value-inspect, exception); stdout is the trace

**Decision.** `obs⁺(program)` runs the program in a fresh CRuby subprocess and records:
`stdout` (the ordered side-effect trace), `value` (`inspect` of the program's last
expression), and `exc` (`[class_name, message]` if it raised). The program is inlined into
a wrapper that captures the value and writes `{value, exc}` as JSON to a side file
(`OBS_OUT`), while the program's own stdout stays on the child's stdout and is captured
separately. `Exception` (not just `StandardError`) is caught, so we observe *all* raises.

**Why.** stdout already records order+multiplicity of `print`/`puts` markers, so it *is*
the evaluation-order trace (artifact 06 §2) with no AST injection needed — adversarial
seeds just print markers. Separating the value/exc onto `OBS_OUT` keeps program output
clean.

**Revisit if.** We need traces of evaluations that don't print (then inject markers at the
AST level per artifact 06 §2).

## C6 — Determinism / normalization

**Decision.** In the wrapper: `srand(0)` (fix `rand`). In normalization: replace
`0x[0-9a-f]+` addresses with `0xXXXX` on both `stdout` and `value` (artifact 05 §3.2).
Time is not stubbed yet; seeds avoid `Time`/`rand`/threads.

**Known gap.** Hash-seed randomization is *not* pinned here — Ruby exposes no simple flag
for it, and small hashes preserve insertion order in `inspect` anyway, so it rarely bites.
Documented as a limitation; if it surfaces, normalize hash `inspect` output or set a seed
via a C-level mechanism. Programs that depend on hash ordering are out-of-fragment for now.

## C7 — Program value captured via `begin … end` inlining (not `eval`)

**Decision.** The wrapper inlines the program text inside `__val = begin <SRC> rescue … end`
rather than `eval`-ing a string.

**Why.** Inlining preserves normal top-level lexical scoping (a string `eval` subtly
changes local-variable scope and `__method__`). **Limitation:** programs containing
`__END__`, top-level `BEGIN{}`/`END{}`, or a top-level `return` won't wrap cleanly; such
programs are out-of-fragment for the harness. Acceptable for self-contained seeds.

## C8 — Corpus prongs

**Decision.** Prong 1 ships as a **bootstraptest harvester** (`bin/harvest_bootstraptest`)
that reads a local checkout of MRI `bootstraptest/` if pointed at one, plus a hand-written
**seed corpus** (`corpus/seeds/`) that exercises every implemented rule, including
evaluation-order adversarial cases. Prongs 2 (fuzzing) and 3 (AI agent) are **stubbed with
interfaces** but not implemented in this first slice — the driver consumes any `.rb` files
under `corpus/`, so new sources drop in without code changes.

**Why.** bootstraptest isn't vendored into the installed Ruby (it lives in the ruby/ruby
source tree), so we make harvesting opt-in and ship a working seed corpus now to validate
the pipeline end-to-end.

## C9 — Normal-form failure is a warning, not a hard failure

**Decision.** If `desugar(reparse(render_core(desugar(P)))) ≠ desugar(P)`, the driver
reports a `NORMAL-FORM` warning but does not count it as a round-trip disagreement.

**Why.** Non-idempotent-but-behavior-preserving rendering (e.g. extra parens that
re-parse identically) is a `render_core` quality issue, not necessarily a correctness bug.
We surface it so it can be fixed, without conflating it with an observable-behavior
disagreement.

## C10 — `eval` of a string is out-of-fragment (gate rejects it)

**Decision.** `desugar` raises `Unsupported` for a call to `eval`, and for
`instance_eval`/`class_eval`/`module_eval` whose first argument is a string literal. The
block forms of `*_eval` remain in-fragment (ordinary sends with a block).

**Why.** `eval` of an arbitrary string smuggles out-of-fragment code past the syntactic
gate (found in testing: `eval "while true; return; end …"` — a top-level `return` that
also terminated the observation wrapper before it recorded anything). Rejecting string
`eval` matches the documented scope (artifact 00 §6, PROJECT_PLAN §4: "`eval` of
arbitrary strings — support only where it desugars to modeled constructs").

## C11 — `stmts` tolerates non-`StatementsNode` bodies

**Decision.** The `stmts` helper, when handed a node that isn't a `StatementsNode` (e.g. a
`BeginNode` for a `begin/rescue` method/block body, or a bare expression), routes it
through the normal `node` dispatch instead of calling `.body` on it.

**Why.** Prism puts a `BeginNode` (not a `StatementsNode`) in the body slot of a
`def`/block/parens that uses `begin/rescue`. Without this, the harness raised a
`NoMethodError` (miscategorized as `parse-error`) instead of a clean OUT-OF-FRAGMENT skip.
Now such programs route to `node`, which raises `Unsupported` cleanly. Fixed 8
mislabeled programs in the bootstraptest run.

## Validation results (first slice)

Against the hand-written seeds **plus** 1304 programs harvested from MRI `bootstraptest/`
(prong 1), on CRuby 4.0.5:

- **224 agree, 0 disagree, 0 parse-errors, 0 harness-errors**; 1090 correctly gated
  OUT-OF-FRAGMENT (classes, constants, floats, `for`, multiple-assignment, `eval`-string,
  threads/GC, etc.).
- **Desugaring-rule coverage 23/23** across the combined corpus (seeds supply
  `while`/`until→while`/`lvor`/`lvand`, which in-fragment bootstraptest programs happened
  not to exercise).
- The injected-bug demo (`bin/run --bug`, naive double-evaluating `&&`/`||`) is caught on
  the two adversarial seeds via the **evaluation-order trace** (`[trace]` bucket) — the
  value is identical on both sides; only stdout exposes the double evaluation.

This validates the artifact-06 methodology end-to-end before any RubyCore semantics exist:
the oracle needs no interpreter, and the trace catches the once-only-evaluation class of
bug that a value-only oracle would miss.

## C12 — RubyCore node-addition policy (keep the core small)

**Decision.** Expanding `RubyCore::HEADS` is treated as a **red flag**. When growing the
fragment (see `fragment-expansion-strategy.md`), a surface feature is handled by, in
order of preference:

1. **Desugaring to `send` + existing RubyCore forms** — the default. The project bet is
   "everything is a message send" (AGENTS.md, artifact 02 §6), so operators, attribute
   access, collection construction with a clean constructor method, etc. become sends.
2. **Desugaring to existing control/binding forms** — `unless→if`, `until→while`,
   op-assign→assignment, `case→if/===`, `for→each`, multiple-assignment, etc.
3. **A new RubyCore head — only if the construct is genuinely irreducible**, i.e. it is
   one of: (a) variable access in the five namespaces, (b) a primitive value literal, (c)
   a primitive control form, (d) the object-model core (`send`/`block`/`def`/`class`/
   `module`/`self`). If a feature isn't in one of those categories, it should desugar.

**Litmus test before adding a head:** "Is there a behavior-identical `send` or existing-
form rewrite?" If yes, desugar. If the rewrite is fragile (edge cases change observable
behavior — e.g. splat/kwargs corner cases) or the construct is a true language primitive,
a head is justified — record *why* here.

**Applied to M1:** variable namespaces (ivar/cvar/gvar/const) and `float` get heads
(irreducible: variable access + value literal). `range`, `rational`, `imaginary` desugar
to constructor sends (`Range.new`, `Rational()`, `Complex()`) — no heads. op-assign and
multiple-assignment are desugarings — no heads. `return`/`break`/`next` are primitive
control forms — heads (small), added when their batch lands.

## C13 — Unified `var`/`vasgn` node for the four variable namespaces

**Decision.** Rather than 8 separate heads (`lvar`/`ivar`/`cvar`/`gvar` × read/write), the
four *variable* namespaces share **one parametric pair**: `[:var, kind, name]` and
`[:vasgn, kind, name, expr]` with `kind ∈ :local|:ivar|:cvar|:gvar`. `local` replaces the
former `lvar`/`lasgn`. **Constants stay separate** (`[:const, name]`/`[:casgn, name, expr]`)
because they are not storage variables — they have lexical+ancestor lookup and paths
(artifact 03 §5), a different primitive.

**Why.** Keeps `RubyCore::HEADS` minimal (C12): 4 heads (`var`/`vasgn`/`const`/`casgn`)
instead of 10. `kind` carries the namespace for the eventual Lean semantics (each has
distinct scoping); `render_core` ignores `kind` and just emits `name`, which already
carries its sigil (`@x`/`@@x`/`$x`) exactly as Prism reports it. This also makes the future
op-assign desugaring uniform across namespaces.

**Deferred:** `constant_path_node` (`A::B`), numbered/back-ref globals (`$1`, `$~`) — special
forms, added with their batches.

**Result:** bootstraptest gate coverage 214 → **258** (+44), all agree on the round-trip.

## C14 — M1 literals & op-assign: desugar to sends where clean; defer `defined?`-dependent forms

**Decisions (all follow C12 — no new heads except the `float` value literal):**

- **`float`** → new head `[:flt, Float]` (irreducible value literal).
- **`range`** (`1..5`, `1...5`, endless/beginless) → `Range.new(lo, hi, excl)` send
  (behavior-identical; `nil` endpoints for open ends). No head.
- **`rational`** (`2r`, `2.5r`) → `Rational(numerator, denominator)` using the literal's
  *exact* value, so it is precise even for float-derived rationals. **`imaginary`** (`3i`)
  → `Complex(real, imag)`. No heads.
- **op-assign** (`v <op>= e`) for local/ivar/cvar/gvar/const → `v = (v <op> e)`. No temp
  needed: variable/constant reads are side-effect-free, so single-evaluation is automatic.
  **Indexed/attr op-assign** (`a[i] += e`, `a.b += e`) *do* have a once-only receiver/index
  obligation and are **deferred** (they need temps — a trace-adversarial batch of their own).
- **`||=`/`&&=`** for local/ivar/gvar → `if v then v else (v = e)` etc. **`const ||=` and
  `@@x ||=` are deferred**: reading an *undefined* constant/class-var **raises** (not `nil`),
  so the correct desugaring needs `defined?` semantics — which is itself out of fragment
  until its own batch. Handling them naively would change behavior, so `desugar` raises
  `Unsupported` for them for now.

**Result:** bootstraptest gate coverage 258 → **353** (+95), all agree on the round-trip.

## C15 — Finishing M1: hash, return/break/next, multiple-assignment; splat deferred

**Heads added** (all legitimate per C12): `hash` (collection literal, parallel to `array`),
and `return`/`break`/`next` (primitive non-local control). No others.

- **`hash`** literal → `[:hash, [[k,v], …]]`; `assoc_splat` (`**h`) deferred.
- **`return`/`break`/`next`** → control heads. **Top-level `return` is gated** (`@fn_depth`
  tracks def-nesting): a top-level `return` terminates the whole script (Ruby 2.4+),
  bypassing the observation wrapper (C7), so it is `Unsupported` unless inside a `def`.
  `break`/`next` at top level merely raise `LocalJumpError`, which the wrapper observes
  identically on both sides, so they are not gated.
- **Multiple assignment** → desugaring (no head), **correct subset only**: RHS must be an
  explicit value list (array literal), no rest/splat target, no splat in the RHS, simple
  variable/constant targets. Desugars to a temp array + index-assigns (order-preserving;
  value is the array). Single-RHS (`a, b = x`, needs `to_ary` coercion), splat, rest, and
  nested/index targets are deferred.
- **Splat deferred** entirely (call `foo(*a)`, array `[*a]`, massign RHS). It is
  irreducible (would need a head), and its position-validity + `to_ary` interactions
  warrant a dedicated batch rather than a rushed addition. So "M1" here means M1 minus
  splat.

**Bug the harness caught (interpolation + control flow).** Admitting `return`/`break`/`next`
surfaced 3 bootstraptest programs with a jump *inside* string interpolation (`"#{next}"`).
Our `interp` desugaring wraps the embedded statement as a `to_s` receiver, producing
`(next).to_s` — a **SyntaxError** (a jump cannot sit in value position). Fix: `interp`
now rejects an embedded statement whose tail is a control jump (`tail_jump?`), as
Unsupported. General limitation noted: jumps in other value positions (send arg, array
element) would similarly be invalid; the round-trip will flag any such case as a
harness-error, to be gated when it appears.

**Result:** bootstraptest gate coverage 353 → **403** (+50), all agree on the round-trip,
0 harness-errors.

## C16 — Linearization pass: hoist unconditional jumps out of operand position

**Decision.** Replace the reactive interpolation gate (C15) with a general **linearization
pass** (`lib/linearize.rb`), run over the desugared tree in `Desugar.program`. It rewrites
so that no *unconditionally-jumping* node (`definitely_jumps?`) sits in an operand position
(send recv/arg, array/hash element, assignment RHS, if/while cond), by sequencing the
operands up to and including the jump and dropping the unreachable remainder. **No
temporaries** are introduced — a hoisted operand never yields a value, so there is nothing
to bind. Conditional jumps (a jump in one `if`/ternary branch) are left inline, because
Ruby accepts them in branch position even when the enclosing `if` is an operand.

**Why.** `"#{next}"` desugars structurally to `(next).to_s` — a SyntaxError (jump in
operand position). CRuby handles this in its *compiler* (emit the jump, leave the string
build as dead code); linearization is the source-level analogue. This removes the C15 gate
(the 3 formerly-gated `test_syntax_*` programs now round-trip correctly), adds **no
RubyCore head** (uses `seq` + existing forms, per C12), and generalizes: the same
`definitely_jumps?`-driven hoisting will serve future order-sensitive desugarings. Fully
documented — including the verified legal/illegal operand-position table — in
`../../docs/semantics/linearization.md`.

**Result:** bootstraptest gate coverage 403 → **406** (+3), all agree, 0 harness-errors.

## C17 — Splat batch

**One head added** (`splat`) — splat is irreducible (array expansion at a call/construction
site; no behavior-identical send rewrite exists). `[:splat, expr_or_nil]` is a marker valid
only as a send-arg or array element; `nil` expr is the anonymous forwarding `*`.

- **Call args / array literals:** a `splat_node` element → `[:splat, e]` (shared `arg_node`
  helper). Renders `*(e)` / `*`.
- **Rest params** (`def f(a, *b, c)`, blocks `{ |x, *ys| }`): the parameter list stays a
  list of *strings*; a rest param is stored verbatim as `"*b"` (or `"*"` anonymous), which
  renders directly — **no structural change** to the `def`/`block` node. Post-rest required
  params supported. Optional/keyword/keyword-rest/block(`&`) params and block-local vars
  (`|x; y|`) remain deferred (their own batches).
- **Multiple assignment** gains two cases for free/cheap: **splat in the RHS list**
  (`a, b = 1, *rest`) now works because the temp-array literal supports splat; and a **rest
  target** (`a, *b, c = …`) via array slicing — `b = t[Range.new(L, -(R+1))]`, post targets
  by negative index. Single-RHS massign (needs `to_ary`) stays deferred.

Deferred (not "splat" proper): double-splat `**` / keyword args, block-pass `&blk`,
`...` argument forwarding.

**Bug the harness caught (massign underflow).** The first rest-target implementation
indexed post-rest targets from the *end* (`t[-(R-j)]`). That is correct only when there
are enough values; on **underflow** Ruby fills post targets *front-to-back* after the
rest's share — `*a, b, c, d, e, f = [0]` gives `b=0` (not `f=0`), and the rest can be
empty. 14 `test_massign_*` programs disagreed. Fix: compute the runtime
`rest_len = [t.length - #lefts - #rights, 0].max`; the rest is `(t[#lefts, rest_len]).to_a`
(the `.to_a` turns a nil out-of-range slice into `[]`), and post target *j* is
`t[rest_len + #lefts + j]`. This is the front-to-back rule and matches CRuby exactly.

**Result:** bootstraptest gate coverage 406 → **473** (+67), all agree on the round-trip
after the fix.

## C18 — M3 batch strategy: object-model core first, then re-measure (not a mega-batch)

**Decision.** Scope the M3 batch to the **object-model/control core only** — `class`,
`module`, singleton-class (`class << obj`), singleton def (`def self.m` / `def o.m`),
`begin`/`rescue`/`else`/`ensure`, `retry`, and `super` — then re-run `bin/coverage` and let
the *new* first-blocker histogram pick the next batch. Do **not** speculatively bundle the
intra-method blockers (optional/keyword params, `yield`, `case`) into this batch.

**Why.** The `bin/coverage` histogram is a *first-blocker* count: a program charged to
`class_node` (280 of them) almost always has a class *body* full of methods that then
re-block on a secondary construct (`yield`, optional params, `case`, `begin`). So admitting
classes does **not** convert all ~280+121(`begin`) programs — many fall to a secondary
blocker. `fragment-expansion-strategy.md`'s "~84% after M3" assumed M2's full params were
already in; they are not. Shipping the core and re-measuring keeps the one-batch-per-ratchet
discipline (each ratchet step is attributable) and produces an honest next-blocker signal.

**Sub-decisions (asked, answered):**
- **`super`: in.** In *desugar* it needs no method-owner tracking (that is a Lean-semantics
  concern); the round-trip oracle handles dispatch. `super` is just a keyword-rendering
  head. Bare `super` (forwards args) and explicit `super(...)`/`super()` are distinct and
  get distinct heads (`:zsuper` vs `:super`).
- **Constant-path reads (`A::B`): deferred.** A namespaced superclass (`class Foo < A::B`)
  re-blocks on `constant_path_node` — clean gate, admitted in a later batch. Constant-path
  *names* in definition position (`class A::B`) likewise deferred (distinct lexical-nesting
  primitive, artifact 03 §5).

**Result (measured).** in-fragment **473 → 752** (+279), 36.4% → 57.9% of parseable, **0
disagreements, 0 harness-errors**, rule coverage 46/46. The fresh `--full` histogram now
names the next batch unambiguously: **M2 params** (`optional_parameter_node` 106,
`block_parameter_node` 95, keyword params) + **`yield_node`** (73), then `case`/`when` (30),
`constant_path_node` (41), `defined?` (38).

## C19 — M3 implementation: heads, the "don't rewrite class to Class.new" rule, and three latent bugs the harness caught

**Heads added** (all C12 category (d) object-model/control primitives — justified, not a red
flag): `class`, `module`, `sclass`, `defs`, `begin`, `retry`, `super`, `zsuper`. **No sugar
was forced into a head, and no primitive was wrongly desugared:**

- **`class`/`module`/`sclass` stay as heads rendered to the keyword form** — *not* desugared
  to `Foo = Class.new do … end`. The keyword form pushes the constant onto the lexical
  nesting (`Module.nesting`) and evaluates the body with that cref and `self` = the new
  module; a `Class.new` block keeps the outer lexical scope. Rendering back to `class …;
  end` is faithful and trivially round-trippable.
- **`defs`** (`def recv.m`): `desugar_def` now emits `[:defs, recv, name, params, body]` when
  the Prism `def_node` has a receiver (previously raised `Unsupported`). Renders
  `def (recv).m(params); …; end`.
- **`begin`**: `[:begin, body, [rescues], else_or_nil, ensure_or_nil]`; each rescue is
  `[[exc_class_nodes], ref_or_nil, handler]`, `ref` a `[kind, name]` target pair. Bare
  rescue = empty exception list. **`expr rescue fallback`** (rescue-modifier) and an implicit
  method-body `begin` reuse this (no extra head). Verified `[V]` against the oracle:
  `ensure` overrides a pending `return`; bare `rescue` matches `StandardError` **not**
  `Exception` (a raised `Exception` escapes it); `retry` re-runs the body; `=> e` binds the
  exception. Seeds `19`–`22`.
- **`super`/`zsuper`**: explicit `super(args)` (incl. `super()` = empty args) vs bare
  forwarding `super`. Distinct heads; seed `21`.
- **Linearization** (`lib/linearize.rb`) now recurses into the new structural heads (its old
  `else` fallback left them un-recursed), so an operand-position jump *inside* a class/def
  body or a `super` arg still linearizes. `retry` joins the `definitely_jumps?` set.

**Three latent bugs in *existing* desugarings that admitting classes/`begin` made
reachable** (the harness flagged all three as disagreements — its purpose):

1. **String interpolation used `to_s`, but interpolation is `rb_obj_as_string`.** A value
   already a `String` is used verbatim — a redefined `String#to_s` is **not** called (`[V]`
   test_yjit_112/114, which reopen `String`). Fix: `"#{e}"` now desugars to **`String(e)`**
   (`Kernel#String`), which passes Strings through (via `to_str`) and calls `to_s` only on
   non-Strings — matching CRuby exactly.
2. **An assignment-call (`obj[i] = v`, `obj.attr = v`) evaluated to the writer method's
   return, not the RHS.** Prism emits these as `call_node`s to `[]=`/`attr=` but marks them
   with `equal_loc`. The *value* of the expression is always the RHS `v`. Fix: `assign_call`
   binds the RHS to a fresh temp **in its own (last) argument position**
   (`recv.[]=(idx…, (t = v)); t`), so receiver→indices→RHS still evaluate left-to-right
   exactly once (eval order preserved) and the expression yields `v`. New rule
   `attr-index-write`; adversarial seed `23`. (This retires the plain-assignment half of the
   C14 indexed/attr deferral; the op-assign half, `a[i] += e`, is still deferred.)
3. **Do-while (`begin … end while C`) was desugared as a plain `while`, dropping the
   run-once semantics.** Prism marks it `begin_modifier?`. Desugaring by duplicating the body
   is wrong (a `next`/`break` in the first copy would not be inside a loop), and a `[:while]`
   head has no run-once flag, so it is **gated as `Unsupported` (deferred)** — clean, 2
   programs (test_syntax_092/093).

**Also:** `bin/coverage`'s `SUPPORTED` set (used only by `--full` profiling) was brought
current (it was stale since M1); and a pre-existing bug on its `--full` path
(`full_blocker[t] += 1 && seen.add(t)` mis-parses as `+= (1 && Set)` → `TypeError`) was
fixed so the next-blocker profiler runs.

## C20 — Observation equality is checked before ok-ness: identical error-observations are agreement

**Decision.** In `Roundtrip.check`, compare `obs_src == obs_core` **first**, before the
"either side failed to observe" harness-error branch. Two *identical* observations are an
agreement even when both are error-observations (`Obs#==` already compares
stdout+value+exc+error). Only reclassify as `harness_error` when the observations **differ**
and at least one side failed.

**Why.** A program that redefines a core method the observation *wrapper itself* relies on
(e.g. `String#==`, test_yjit_188) crashes the in-process wrapper (C7 inlines the program in
the same process). Because `desugar` is faithful, it crashes the wrapper the **same way** on
both `src` and the rendered core — identical `stdout`, identical `no-observation` error.
That is not a desugaring disagreement; it is behavior the harness genuinely cannot observe,
identically on both sides. Flagging it as a harness-error conflated a harness limitation
with a defect. The reorder is strictly safe: a real desugar bug perturbs stdout/value/exc or
produces an asymmetric failure, which still surfaces as disagreement/harness-error. This is a
narrow, documented harness limitation in the spirit of C6 (hash-seed) — the C7 in-process
wrapper cannot observe programs that monkeypatch its own dependencies.

## C21 — L1 block/proc front-end: `yield` head, block-locals slot, `->`→`lambda` send

**Decision.** Bring blocks fully into the desugared fragment (model side is L1, separate):
1. Add a **`yield`** head `[:yield, [args]]` (Prism `yield_node`); args reuse `arg_node`
   (splat-capable) and linearize like call args (hoist a jump out of operand position).
2. Extend **`block`** from `[:block, params, body]` to `[:block, params, locals, body]`,
   un-gating block-local variables (`{ |x; t| … }`, Prism `parameters.locals`). Renders as
   `{ |params; locals| body }`. This is the lexical block-local set the L1 model needs to
   resolve free variables up the captured-frame chain (artifact 03 §2).
3. Desugar **`->(params){body}`** (Prism `lambda_node`) to `[:send, nil, "lambda", [],
   [:block, params, locals, body]]` — behavior-identical to `lambda { … }`, so **no new
   head**, and lambda-ness stays a property the callee confers on the block (artifact 04
   §1). `proc`/`Proc.new`/`lambda` need no desugar change — already ordinary sends-with-block.

Consumers updated in lockstep: `rubycore.rb` (HEADS + `is_core?`), `desugar.rb`
(`block_params` helper, `desugar_yield`, `desugar_lambda`, RULES `yield`/`lambda->send`),
`render.rb`, and — the one easy-to-miss consumer — **`linearize.rb`**, which reconstructs
`:block` in four places (send/standalone/super/zsuper) and needed a `:yield` case; folded
into a `blk_of` helper. Round-trip: **818 agree / 0 disagree**, in-fragment ratchet
**752 → 792**, rule coverage 48/48 (seeds 24–26).

**Why / caveat.** The `block` shape change is not backward compatible, so `Export::VERSION`
is bumped **1 → 2**. The Lean SUT decoder (`ruby/lean/RubyCore/Syntax.lean`) still expects
v1 and will reject v2 with an "unsupported version" error until the L1 model lands — i.e.
`--sut lean` is intentionally red between this desugar milestone and the model milestone.
The round-trip harness (`bin/run`/`bin/coverage`) does not use the export and is fully green.

## C22 — Two idempotence checks: AST-space (critical) vs render round-trip (benign)

**Decision.** Split the single normal-form check (C9) into two, so a rendering
artifact can be told apart from a real desugaring bug:
- **`normal_form`** (C9, unchanged): `desugar(parse(render(core))) == core`. Goes
  *out* to surface and back, so it also trips on `parse ∘ render ≠ id` artifacts
  that are not desugar bugs — e.g. a `[:send, _, "name=", _]` writer send whose
  rendered `.name=(…)` re-parses as an attribute assignment and re-lowers (C21).
  Reported as `ok*`, still a benign warning, does **not** fail the run.
- **`ast_idempotent`** (new, critical): `Linearize.run(core) == core`, with **no
  render/parse in the loop** — pure RubyCore→RubyCore. A failure is a genuine
  non-idempotence of our own AST transformation. Reported as `AST` and **fails the
  run** (nonzero exit), alongside disagreements.

**Why.** The Prism→RubyCore step cannot be self-composed (its input is a Prism
AST, not RubyCore), so the only bridge back into it is `render` — and that bridge
is exactly what injects the `name=`/ATTRASGN re-lowering. Testing idempotence
*through* render therefore conflates "our desugaring isn't a fixpoint" (a bug)
with "surface syntax can't round-trip this core node" (cosmetic, unavoidable —
there is no call-position spelling of a `name=` setter; the lexer splits it into
`name` + `=`). The render-free `ast_idempotent` check isolates the former: across
the corpus it is **0 failures / 818 in-fragment cores**, and every one of the 10
`normal_form` warnings is `ast_idempotent = true` — proving they are all
render↔parse artifacts, not desugar defects. As we add RubyCore→RubyCore passes
beyond `Linearize`, fold them into this check so AST-space idempotence stays a
hard invariant.

## C23 — Block-capture param `&blk` as a sigil-prefixed flat string (L1b, commit 1)

**Decision.** Admit the block-capture parameter `def m(&blk)` / `{ |&blk| }` by
carrying it in the existing **flat `[String]`** param slot as the verbatim string
`"&blk"` (or `"&"` for an anonymous `&`), exactly mirroring the `*rest` → `"*a"`
convention (C17). No new head, no structured-param migration.

**Why here, not in M2.** The full structured-param migration (flat `[String]` →
`[:preq]`/`[:popt]`/… nodes) exists to carry **optional defaults**, which are
arbitrary *expressions* evaluated lazily in the callee scope — a string cannot
hold them and `linearize` must recurse into them. A block-capture param has **no
attached expression**: it is fully described by a name + the `&` sigil, so the
string trick is lossless and there is nothing for `linearize` to hoist. This lets
block passing land as its own small batch (L1b) while the structured-param
migration stays deferred to M2.

**Scope.** Consumers are untouched by design: `is_core?` still checks
`params.all? { String }` (`"&blk"` is a String); `render` emits it via
`params.join(', ')`; `linearize` passes the param list through. The only edit is
`param_names` in `desugar.rb` (drop the `raise`, append `"&#{p.block.name}"`,
fire `:block-capture`). Anonymous `&` (`p.block.name == nil`) → `"&"`.
This is **commit 1** of L1b; the call-site block-pass `foo(&expr)`
(`[:blockpass, expr]` marker) is commit 2. Ratchet: **792 → 826** in-fragment
bootstraptest, 0 disagree / 0 harness-error; seed `corpus/seeds/28_block_capture.rb`.

## C24 — Call-site block-pass `foo(&expr)` as a `[:blockpass, expr]` slot marker (L1b, commit 2)

**Decision.** Admit block-pass arguments `foo(&e)` / `super(&e)` (and `&:sym`,
`&nil`, anonymous `&`) with a new head `[:blockpass, expr_or_nil]` that occupies
the **existing send/super block slot** — the same slot a literal `[:block,…]`
uses. The two are mutually exclusive in Ruby (both parse into Prism's `.block`),
so no new field is needed; `nil` expr = anonymous `&` (forward the enclosing `&`).

**Representation & consumers.**
- `desugar.rb`: one `call_block` helper dispatches `.block` on type
  (`:block_node` → `block_node`; `:block_argument_node` → `[:blockpass, …]`),
  routed from `send`/`super`/`zsuper`. Fires `:blockpass`.
- `rubycore.rb`: `blockpass` head; `explain` mirrors `:splat` (structurally valid
  anywhere, but only *produced* in a block slot). Slot checks unchanged (they
  already recurse via `is_core?`).
- `render.rb`: a block-pass is an **argument** — rendered `&(e)` (or bare `&`)
  *inside* the call parens as the last arg, NOT a trailing brace block. `send_str`
  and the super/zsuper renders branch on `blk[0]`.
- `linearize.rb`: the block-pass `e` is an **operand evaluated last**, so it joins
  the `hoist` operand list (after args) — `foo(&(return))` aborts the call
  correctly. `blk_of` is now slot-type-aware; a literal block's body stays a
  deferred (non-operand) position. `blk_operand` splices the linearized expr into
  the hoist sequence.

**Interface.** New head on the Lean JSON interface → `Export::VERSION` 2→3.
`--sut lean` stays red until the model decodes it (block-capture strings need no
encoding change; `blockpass` is a new node).

Ratchet: **826 → 852** in-fragment bootstraptest, 0 disagree / 0 harness-error /
0 AST-idempotence failures. Seed `corpus/seeds/29_block_pass.rb` covers `&Proc`,
`&:sym` (`to_proc`), `&nil`, forwarding `def f(&b); g(&b); end`, and the
eval-order obligation (args before the `&`-operand's evaluation/coercion).

## C25 — M2: structured parameter list + keyword call args (optional/keyword/kwrest params, `foo(a: 1, **h)`)

**Decision.** Migrate the `def`/`defs`/`block`/lambda **parameter slot from a flat
`[String]` to a structured list of param nodes**, and admit keyword arguments at a
call site as a `[:kwargs, elems]` marker. This unblocks the whole M2 family (optional,
keyword, keyword-rest, block-capture params, and brace-less keyword args), which
dominated the post-M3 first-blocker histogram once class bodies exposed method signatures.

**Why the migration (not the flat-string trick).** Required params, `*rest`, and `&blk`
were carried as sigil-prefixed strings (C17/C23) because they are fully described by a
name. An **optional default** (`a = E`) and an **optional-keyword default** (`a: E`) are
not: `E` is an arbitrary expression evaluated *lazily, left-to-right, in the callee scope,
at call time, only for omitted args* (`def f(a, b = a + 1)`), so it must be carried as a
real desugared node — and `linearize` must recurse into it. A string cannot hold that.
So the param slot becomes a list of param nodes (a sub-grammar of the object-model
primitives, **not** a new top-level head — C12 category d):

| Param node | Surface | Renders |
|------------|---------|---------|
| `[:preq, name]` | `a` (incl. post-rest) | `a` |
| `[:popt, name, default]` | `a = E` | `a = (E)` |
| `[:prest, name_or_nil]` | `*a` / `*` | `*a` / `*` |
| `[:pkey, name, default_or_nil]` | `a: E` / `a:` (required) | `a: (E)` / `a:` |
| `[:pkwrest, name_or_nil]` | `**o` / `**` | `**o` / `**` |
| `[:pblock, name_or_nil]` | `&b` / `&` | `&b` / `&` |

`nil` default on `:pkey` = a *required* keyword. Order is Ruby's canonical
requireds→optionals→rest→posts→keywords→kwrest→block. Consumers migrated in lockstep:
`rubycore.rb` gains `PARAM_HEADS` + a `params_error` validator (replacing the three
`params.all? { String }` checks); `render.rb` gains `render_params`/`param_str`;
`desugar.rb` replaces `param_names`→`build_params` (+`req_param`); `linearize.rb` gains
`run_params` (recurses into `:popt`/`:pkey` defaults — a default is an operand position,
but is never hoisted *out* of the list).

**Keyword call args — the Ruby-3 separation (like "don't rewrite class to Class.new").**
`foo(a: 1, **h)` is a brace-less trailing keyword hash (Prism `keyword_hash_node`). It is
**not** desugared to a positional hash `foo({a: 1})`: since Ruby 3.0 keyword and
positional-hash args are separated (a positional hash uses braces; keyword args bind to
keyword params). So it is kept as `[:kwargs, elems]` (elem = `[k, v]` assoc or
`[:kwsplat, e_or_nil]`) rendered **brace-less** with `=>` for every key (`(k) => (v)`,
`**（e)`) — verified `[V]` behavior-identical to `k:`/`**` and, in an array literal
`[a: 1]`, to the trailing-hash form. `arg_node` produces it (shared by call/array/yield
args); `linearize` gets `run_arg`/`run_kwargs` to recurse into the values.

**Deferred (enumerated):** argument/param forwarding `...` (`forwarding_parameter_node`,
now the top param blocker at 31), destructuring block params `|(a, b)|`
(`multi_target_node`), numbered params `_1`/`it` (`numbered_parameters_node`), implicit
rest `a, = x`, `**nil` (`no_keywords_parameter_node`).

**Interface.** Breaking change to the Lean JSON export (param-slot shape + `kwargs` head)
→ `Export::VERSION` 3→4. `--sut lean` stays red until the model migrates its param
decoder and adds `kwargs`. The round-trip harness (`bin/run`/`bin/coverage`) does not use
the export and is fully green.

**Result (measured).** in-fragment **852 → 1006** (+154), 65.6% → **77.4%** of parseable,
**0 disagree / 0 harness-error / 0 AST-idempotence failures**; rule coverage 54/54 (seeds
`30_params`, `31_param_defaults_eval_order` — the lazy-default eval-order adversarial
seed — `32_kwargs` — the Ruby-3 separation seed, both directions). The fresh first-blocker
histogram now names the next batches: `defined?` (34), `case`/`when` (30), `alias_method`
(15), single-RHS massign (15), constant paths `A::B` (13+9+5).

## C26 — M4: `case`/`when` → if-chain over `===`, and `defined?` as a primitive head

**Decision.** Admit `case`/`when` by **desugaring to a temp + if/elsif chain over `===`**
(no head — C12), and `defined?` as a new **`[:defined, expr]` head** (irreducible).

**`case`/`when`.** The subject is evaluated **once** into a fresh temp `t`; each `when`
value becomes a `(value === t)` test, and a `when` with multiple values ORs them with
short-circuit (`[:if, test1, [:true], test2]`, so only truthiness reaches the enclosing
`if` and a later value isn't evaluated once an earlier one matches). A **subjectless**
`case` (`case; when cond; …`) truth-tests each condition directly (no `===`). `[V]`
verified against the oracle: subject-once, then when-values left-to-right until a match.
A **splat `when *arr`** tests whether any element matches — desugared to
`[*arr].any? { |w| w === t }`; the `[*arr]` array-splat (already in-fragment) reproduces
Ruby's non-array coercion (`when *5` ≡ `when 5`), which a bare `arr.any?` would get wrong
(`5.any?` raises). Deferred: splat in a *subjectless* `when` (8 cases), and `case x in pat`
pattern matching (distinct `case_match_node`).

**`defined?`.** `defined?(expr)` inspects its *syntactic* argument (mostly **without
evaluating** it) and returns a describing String or `nil`. There is no send it reduces to,
so it is a head; the inner expr is desugared normally and rendered back inside
`defined?(…)`. Because it does not evaluate, `linearize` leaves it in the passthrough (no
jump-hoisting). `[V]` seed pins `local-variable`/`instance-variable`/`constant`/`method`/
`expression`/`self`/`nil` results and the no-side-effect property (`defined?(boom)` does
not call `boom`).

**Result (measured).** in-fragment **1006 → 1048** (+42), 77.4% → **80.7%** of parseable,
**0 disagree / 0 harness-error / 0 AST-idempotence failures**; seeds `33_case_when`
(incl. splat-when + eval-order) and `34_defined`. No export change (`case` desugars away;
`defined` head is auto-encoded — `Export::VERSION` stays 4, but the Lean decoder must add
`defined` when it migrates). Next blockers: `...` forwarding (31), constant paths `A::B`
(19+13+5), regex (16), `alias_method` (15), single-RHS massign (15), `redo` (11).

## C27 — M5: constant paths `A::B` (read, write, and definition-position names)

**Decision.** Admit constant paths with **one head `[:cpath, base_or_nil, name]`** (read)
plus **`[:cpath_asgn, base_or_nil, name, expr]`** (write). `base` is `nil` for a top-level
`::B`, else an arbitrary expression node (usually a constant, but `expr::B` is legal). This
retires the M3/C19 deferral of namespaced superclasses and definition-position paths.

**Representation & consumers.**
- `desugar.rb`: `desugar_cpath` / `desugar_cpath_write`; `const_def_name` (class/module
  name) now returns a String *or* a `[:cpath,…]` node (`class A::B`, `class ::B`).
- `rubycore.rb`: `cpath`/`cpath_asgn` heads; `const_name_error` lets a class/module name
  be a String or a cpath node.
- `render.rb`: `cpath_str` renders `(base)::Name` / `::Name`; the base is **parenthesized**
  so any expression re-parses — `[V]` `(A)::B` is behavior-identical to `A::B` and valid in
  definition position (`class (A)::B`), so read and definition share one renderer.
- `linearize.rb`: the base and the assignment RHS are operand positions (a jump in either
  hoists via `hoist`).

**Value & eval order.** `A::B = v` yields the RHS natively (assignment result), so no temp
is needed; eval order is base-then-RHS, matching CRuby `[V]`.

**Deferred:** `A::B ||= v` / `A::B += v` (`constant_path_or_write_node` /
`constant_path_operator_write_node`) — need `defined?`-style guards; their own step.

**Result (measured).** in-fragment **1048 → 1085** (+37), 80.7% → **83.5%** of parseable,
**0 disagree / 0 harness-error / 0 AST-idempotence failures**; seed `35_constant_path`
(relative/nested/top-level reads, definition-position reopen, path assignment eval-order,
non-constant base). Export: two auto-encoded heads (`Export::VERSION` stays 4; Lean decoder
adds them on migration). Next: `...` forwarding (31), regex (16), single-RHS massign (15),
`alias_method` (15), `redo` (11), interpolated symbol (6), `undef` (6), `for` (6).

## C28 — M6: the long tail (keyword heads, regex/symbol, `...` forwarding, single-RHS massign)

**Decision.** Clear the remaining non-`eval` histogram in one batch, mixing new heads (only
where irreducible) with desugarings:

- **`redo`/`undef`/`alias`/`for`** — four small keyword heads. `redo` joins the
  `definitely_jumps?` set. `undef foo, bar` → `[:undef, [names]]`; `alias new old` →
  `[:alias, new, old]` (both `alias_method_node` for methods and
  `alias_global_variable_node` for `$g`; static names). `for x in coll` → **`[:for, targets,
  coll, body]` kept as a head rendered back to `for`** — a `coll.each { |x| … }` desugaring
  would wrongly make `x` block-local, but the `for` index **leaks** to the enclosing scope
  (`[V]`); the head sidesteps that. Multi-target `for a, b in` supported (simple targets).
- **regex** → `Regexp.new(source, opts)` (**no head**): plain source is a literal String
  (`[V]` `Regexp.new(unescaped, opts)` reproduces `.source` + `.options` exactly for `/`,
  metachars, `\d`, flags); interpolated `/a#{e}/` reuses the string-interp concatenation;
  `opts` packs IGNORECASE=1/EXTENDED=2/MULTILINE=4. The literal-regex-`=~` named-capture-to-
  local magic is not modeled (the round-trip flags any reliant program — none did).
- **interpolated symbol** `:"a#{e}"` → `(interp string).to_sym` (**no head**). The interp
  concatenation was factored into a shared `interp_concat` (now also handles
  `embedded_variable_node` `#@x`/`#$g` and nested `interpolated_string_node` from adjacent
  literal concatenation).
- **`...` forwarding** — `[:pfwd]` param node + `[:fwd]` arg marker, both rendered `...`
  (`def f(...); g(...); end`, incl. a leading required `def f(a, ...)`).
- **single-RHS massign** `a, b = x` → the temp array is `Array.try_convert(x) || [x]`
  (`[V]` exactly matches Ruby's `to_ary`-or-wrap coercion; `x` bound to a temp so
  `try_convert` fires once), retiring the C15/C17 single-RHS deferral. This shares the
  existing lefts/rest/rights distribution.
- **subjectless splat `when *arr`** → `[*arr].any?` (truthiness; the array-splat coercion),
  completing `case` (C26 left this one deferred).

**Interface.** All new heads (`redo`/`undef`/`alias`/`for`/`fwd` + the `pfwd` param) are
additive to the v4 export format (no further break); `Export::VERSION` stays 4 with an
expanded comment. `--sut lean` remains red until the model adopts v4.

**Result (measured).** in-fragment **1085 → 1198** (+113), 83.5% → **92.2%** of parseable,
**0 disagree / 0 harness-error / 0 AST-idempotence failures**; seeds `36_keywords`,
`37_regex_symbol`, `38_forwarding_massign`. What remains is dominated by the intentionally
out-of-scope forms (string `eval`/`class_eval`/`instance_eval` ≈56, top-level `return` 6,
un-parseable 5) plus a small tail (indexed/attr op-assign, destructuring params/targets,
numbered params `_1`, `__LINE__`, do-while, flip-flop, backtick x-strings, dynamic
alias/undef names) picked up in C29.

## C29 — M7: the final mop-up (op-assign, destructuring, do-while, `$1`) + documented out-of-scope gates

**Decision.** Clear the remaining cleanly-modelable tail and give every genuinely
out-of-scope form an explicit, self-describing gate. **All desugarings below use existing
heads except do-while.**

- **Indexed/attr op-assign** — `a[i] += v`, `a[i] ||= v`/`&&=`, `a.b += v`, `a.b ||= v`/
  `&&=` (6 Prism nodes). The receiver and every index are cached in temps (evaluated once,
  eval order preserved); the value is the new element/attr value (short-circuit result for
  `||=`/`&&=`). Retires the C14/C19 indexed-op-assign deferral. **Harness-caught bug:** a
  *splat index* `a[*a] += 1` — binding `*a` to a temp wraps it into an array and indexes by
  the wrong value; fixed by caching the splatted array and re-splatting the temp
  (`test_syntax_108`).
- **Numbered block params** `{ _1 + _2 }` — the body's `_1`… reads render verbatim and Ruby
  re-detects them, so the param list is just emptied (no representation needed).
- **do-while** `begin … end while C` — a new `[:dowhile, body, cond]` head (run-once, a
  plain `[:while]` can't express it; `until` negates the cond). Retires the C19 deferral.
- **Single-target / nested destructuring** — the massign distribution was refactored into a
  recursive `distribute`/`assign_target`: a nested target `(a, b), c = …` recursively
  coerces its slice (to_ary-or-wrap) and distributes into sub-targets; an implicit-rest
  `a, = x` / `{ |a,| }` is treated as an anonymous discard-rest. Destructuring **block
  params** `|(a, b)|` become a `[:pdestr, [sub-params]]` param node rendered back as
  `(a, b)` (so the block still auto-splats).
- **`rescue *classes`** — a splat in the rescue exception list (`arg_node` + bare `*(x)`
  render).
- **`$1`/`$&`** (numbered/back reference) → gvar reads rendered verbatim (`$~` etc. already
  arrive as ordinary gvar reads).

**Explicitly gated (documented, not silently unhandled).** `__LINE__`/`__FILE__`
(source-location reflection — the value changes when the program is re-rendered onto
different lines), backtick x-strings (spawn an external process — out of scope, cf. the
`eval` gate C10), and the flip-flop operator (stateful per-instance control — deferred).
The gate reasons now surface directly in the `bin/coverage` histogram.

**Still deferred (enumerated):** `case x in pat` pattern matching (`case_match_node` /
`match_predicate_node` — a large sublanguage, its own project), dynamic
`alias`/`undef` names (`alias :"a#{x}" b`), and `A::B ||=`/`+=` (constant-path op-assign,
needs `defined?` guards).

**Result (measured).** in-fragment **1198 → 1227** (+29), 92.2% → **94.5%** of parseable,
**0 disagree / 0 harness-error / 0 AST-idempotence failures**; seeds `39_opassign_misc`
(incl. the splat-index regression), `40_destructuring`, `$1`/`$&` in `37`. All new heads
(`dowhile`) + param node (`pdestr`) are additive to the v4 export. **The remaining 72
non-in-fragment programs are the genuinely-unsupportable / deferred set** — string
`eval`-family (52), top-level `return` that bypasses the observation wrapper (6),
un-parseable (5), plus the small documented-gate tail above (≈9). This is the practical
coverage ceiling of the round-trip harness on bootstraptest.

## C30 — String interpolation lowers to `rb_obj_as_string`, not `Kernel#String` (bugfix)

Interpolation `"#{e}"` (and `"#@x"`, dynamic symbols, regex sources) was lowered to
`[:send, nil, "String", [e], nil]` (`Kernel#String`), on the claim that `String(e)`
matches CRuby's `rb_obj_as_string`. It does **not**: `Kernel#String` coerces via
`to_str` *first* (`rb_check_convert_type`), which dispatches through `method_missing` or
a user-defined `to_str`, whereas interpolation uses `rb_obj_as_string` = "a String (or
subclass) verbatim — a redefined `String#to_s` is NOT called — else `to_s`", and never
touches `to_str`. So `String(o) != "#{o}"` for an object with `method_missing`/`to_str`.

[V] `class C; def method_missing(n,*a); "mm-#{n}"; end; end; puts("#{C.new}")` →
CRuby `#<C:…>` (to_s) but the old desugar `mm-to_str`. Also `class S<String; def to_s;
"X"; end; end; "#{S.new("hi")}"` → `hi` verbatim (to_s not called). Found by tier-1
fuzzing once `method_missing` generation landed (difftest N22/N23).

Fix: new `as_string(e)` helper lowers to `t = e; String === t ? t : t.to_s` (`t` a
`fresh` temp bound once; `String ===` is a C-level `Module#===` type check, no user
dispatch) — matching `rb_obj_as_string` on all three cases. Uses only
seq/if/vasgn/var/send/const, so the Lean model consumes it unchanged (`Module#===`
already modeled for `case/when`). No `Export::VERSION` bump (same heads, different
shape). Round-trip: **1267 agree, 0 disagree, 73/73** (unchanged; a few more cases join
the benign `[ok*]` render-unstable-but-AST-idempotent set). difftest: tier-0 vs desugar
**1227 agree, 0 disagree**; tier-0 vs lean **686 agree, 0 disagree**.

## C31 — a `-0.0` literal desugars to `-@(0.0)`, not `[:flt, -0.0]`

The RubyCore JSON export encodes floats as JSON numbers, and JSON / Lean's
`JsonNumber` cannot carry a negative zero (its mantissa is a signless `Int 0`), so
`[:flt, -0.0]` would reach the Lean model as `+0.0` and `(-0.0).inspect` would
wrongly print `0.0` (a disagreement, once Float rendering exists — L45). Fix
(`desugar.rb`, `float_lit`): a negative-zero float literal is emitted as
`[:send, [:flt, 0.0], "-@", [], nil]`, which round-trips through the model's
(correct) `Float#-@`. Semantically transparent (`-0.0` = `-(0.0)`); the desugar
round-trip renders it back to a `-0.0`-valued expression, so the desugar difftest
is unaffected. Only negative zero is special-cased; all other float literals stay
`[:flt, v]`.

## C32 — `implicit_node` (Ruby 3.1 hash/keyword shorthand) resolves through Prism

`{x:}` / `foo(x:)` parses to an `AssocNode` whose *value* is an `ImplicitNode`. Prism has
already done the local-or-method resolution for us: `ImplicitNode#value` is either a
`LocalVariableReadNode` or a `CallNode`, chosen by the same rule the interpreter uses. So
the desugaring is one line — `when :implicit_node then node(n.value)` — and is exactly the
`x: x` expansion, with the *resolved* reading of `x`.

Rejected alternative: re-deriving the resolution ourselves from the key name (emit
`[:var, :local, k]` if `k` is in scope, else a vcall). That duplicates Prism's scope
tracking in the desugarer for no gain and would drift on the edge cases (a local
introduced by a block param, a shadowed method name).

Rationale for doing it first: it is the single biggest front-end gate in the Homebrew
corpus — **332 of 962 files** (~2,412 uses) — and it is the *only* thing blocking three of
the eight files of the version+vulnerability slice (`version.rb`, `vulns/vulnerability.rb`,
`vulns/identify.rb`); the other five already desugared. See
[`../../homebrew/PLAN.md`](../../homebrew/PLAN.md) W1/M1.

New rule name `implicit` (RULES 74→75). No new RubyCore heads, no `Export::VERSION` bump —
the output is an ordinary `[:hash, …]`/`[:kwargs, …]` pair whose value is a `var` or `send`
the Lean model already consumes.

Seed `corpus/seeds/41_implicit_hash.rb` covers: hash-literal and keyword-argument
positions, a resolution to a local and one to a method (`def name = "c"; { name: }`),
mixing with explicit pairs, and the eval-order obligation (a shorthand whose resolution is
a call fires exactly once, in source order).

**Result (measured).** Seeds 41/41 agree, rule coverage 75/75. bootstraptest
**1227 agree, 0 disagree, 0 harness-error** (unchanged — no bootstraptest program uses the
shorthand, so this is a pure additive extension). All 8 slice files now desugar.

Not in scope here (separate gate, not needed by the slice): `**` inside a *hash literal*
(`assoc_splat_node` in `desugar_hash`; the call-argument form already works). 155 uses
corpus-wide.

## C33 — regex literal fidelity: the `n` flag, `/o` compile-once, and gated encoding flags

`desugar_regex` lowered `/…/` to `Regexp.new(src, opts)` with `opts` carrying only
`i`/`x`/`m`. Two of the remaining flags are observable, and one of them is on the Homebrew
slice's critical path.

**`/n` → `Regexp::NOENCODING` (32).** Measured: `vulns/purl.rb`'s
`/[^A-Za-z0-9\-._~:]/n` was the *only* regex in the eight slice files whose
`Regexp.new(unescaped, opts)` reconstruction differed from the literal (86 literals + 28
interpolated, 1 mismatch). Adding bit 32 closes it. [V] `Regexp.new("a", 32) == /a/n`.

**`/u`, `/e`, `/s` gate.** These fix the *encoding* of the pattern, which the integer
option word cannot express — `Regexp.new` would need a source String already in that
encoding. Silently dropping them would be a fidelity hole, so they raise `Unsupported`
with a self-describing reason. Zero uses in the Homebrew corpus (1,133 regexes measured),
zero in bootstraptest.

**`/o` → a gensym'd global cache.** `/…/o` compiles the literal once, at first evaluation,
and thereafter returns *that same object* without re-running the interpolations. This was
being dropped, which is wrong on three observables: interpolation side effects, object
identity, and staleness when the interpolated value changes. It is not academic —
`version.rb` uses it **8 times** (`/\A#{AlphaToken::PATTERN}\z/o` and siblings), i.e. once
per `Token` subclass, and it is 24 uses corpus-wide.

The desugaring is `$g ? $g : ($g = Regexp.new(…))` with `$g` a fresh `$__dt_rxN`. A
*global* is the right cache, not a local or an ivar: CRuby's cache is per literal **site**
and shared program-wide (not per receiver, not per thread), and a distinct site gets a
distinct gensym. The emitted shape is exactly what `logic_write` produces for `$g ||= e`,
so the rendered program re-desugars to itself (AST idempotence holds), and a `Regexp` is
never nil/false so the truthiness test is a faithful "already compiled?".

Rejected alternative: a hidden per-site *constant*. Constants are cref-scoped, so a `/o`
inside a class body would need a name mangled with the cref, and an unset constant read
raises rather than returning nil (the reason `const ||=` is still deferred, C-earlier).

No new RubyCore heads and no `Export::VERSION` bump — the output uses `if`/`var`/`vasgn`
on the gvar namespace, all already modeled.

**Result (measured).** Seed `corpus/seeds/42_regex_flags_once.rb` (flag round-trip via
`Regexp#options`, `/o` call-count + `equal?` identity + staleness, and the non-`/o`
contrast) agrees. Seeds **42/42**, rule coverage 75/75. bootstraptest **1227 agree, 0
disagree** — unchanged, and provably unaffected: measured 0 uses of `/o` and 0 of `/n` in
the corpus.

## C34 — safe navigation `recv&.m` was being dropped (bugfix)

`x&.to_h` desugared to a plain `[:send, x, "to_h", …]`: the `&.` was read off the Prism
node and discarded. The bug hides in plain sight, because for any method `nil` does *not*
answer both CRuby and the model raise the same `NoMethodError` — it only shows for a
method `nil` **does** answer, and `NilClass` answers a dozen of them. `nil&.to_h` is
`nil`; `nil.to_h` is `{}`.

Found while running the Homebrew-slice corpus (difftest N36): `vulns/identify.rb` ends
`registry_package(url)&.to_h`, and the model reported `{}` for a URL that should identify
nothing.

The desugaring binds a temp and wraps the *whole* send:

```ruby
t = recv; t.nil? ? nil : t.m(args)
```

Two things that shape are chosen for, both verified: the receiver is evaluated **once**,
and when it is nil the **arguments are not evaluated at all**. So it cannot be
`recv && recv.m(args)` (double evaluation) and it cannot be a guard around an
already-evaluated argument list. It is also not `&&`: the test is `nil?`, not truthiness,
so `false&.to_s` really does call `to_s` [V].

New rule name `safe-nav` (RULES 75→76); no new RubyCore heads and no export bump — the
output is `seq`/`vasgn`/`if`/`send`, all already modeled. Safe-navigation *op-assign*
(`a&.b += 1`) stays gated, as before.

Seed `corpus/seeds/43_safe_navigation.rb`: the nil-responder cases, the truthiness
contrast, the once-only receiver and unevaluated arguments (marker-printing), chaining,
block form, and statement position.

**Result (measured).** Seeds **43/43**, rule coverage 76/76; bootstraptest **1227 agree,
0 disagree** (unchanged — no bootstraptest program uses `&.` on a nil-responding method).

## C35 — a block's parse-time locals ride in a fourth slot (`[:block, params, locals, declared, body]`)

`homebrew/HANDOFF.md`'s first known wrong answer, and the one the handoff said starts here
rather than in Lean. It was right.

```ruby
f = -> { a = 1; 0 }
a = 0            # the *first* textual assignment to `a` is inside the block, so
f.call           # Ruby made the block's `a` block-local at parse time
puts a           # CRuby  0     model  1
```

Ruby decides local scoping **lexically, at parse time**: a name whose first assignment in
the text is inside a block is local to that block even when the enclosing scope assigns it
later. The model decided it **dynamically** — the block body wrote the captured frame if a
slot for that name existed there when the body ran — and the two only diverge when the call
is *deferred past* the outer assignment, which is why an `each` in the same shape agreed and
only a stored-and-called-later Proc separated them.

Nothing in the runtime heap can recover the answer; the whole point is that it differs from
what the heap shows. The exported AST had nowhere to put it either (`[:block, params,
locals, body]` — `locals` is only the explicit `|params; locals|` list). **Prism has already
computed it**: every scope node carries `locals`, the set of names that scope binds, decided
at parse. `declared_locals` takes that set less the parameters and less the explicit
block-locals, and the block node gained a fourth slot for it (export `VERSION` 4 → 5; the
Lean decoder accepts both shapes, so a v4 AST still decodes).

**Why a separate slot rather than widening `locals`.** At runtime the two are identical —
both are names the block frame binds itself, and the Lean decoder merges them. They differ
for `defined?`, which CRuby answers **statically**: an explicit `|;x|` is `"local-variable"`
before any assignment, while an implicit one is nil until the assignment is passed
textually. Prism encodes that difference for us — the early reference parses as a *call*
node and the later one as a local read — so the model gets it right from the node shape
alone (L72), but only as long as `render.rb` does **not** emit these names as `|;x|`. It
does not. Re-parsing rendered source recomputes them, so the round-trip is still a fixpoint.

`_1`…`_9` are excluded: Prism reports numbered parameters as scope locals, and no
declaration slot may name them (C29 keeps them verbatim).

**Measured.** 48 hand-written scoping shapes probed against CRuby, all agreeing — the defect
itself and its `each` twin, `rescue => e`, multiple assignment, splat assignment, `for`,
`while`, op-assign in both orders, interpolated assignment, nested blocks and lambdas,
`define_method`, `instance_eval`, block parameters shadowing, and `defined?` before and after
the textual assignment. `_1` and the pattern-matching binder were checked against the
pre-change build (`git stash` + rebuild) and are unrelated: the first is a **pre-existing
wrong answer** (the model answers nil for `_1`, recorded in `homebrew/HANDOFF.md`), the
second a pre-existing gate.

## C36 — numbered parameters get a real param list (bugfix)

C29 desugared `{ _1 + _2 }` to a block with **no** parameters, reasoning that the body's
`_1`… render verbatim and Ruby re-detects them on re-parse. That is true of the render
round-trip and false of every other consumer: the Lean model bound nothing, so
`[1].map { _1 + 1 }` answered `NoMethodError: undefined method '+' for nil`.

It is a *silent* wrong answer rather than an honest gate because the reads desugar to
`[:var, :local, "_1"]` — Prism knows they are locals — and an unbound local reads nil. A
vcall would have raised. This is the C34 shape again: information read off the Prism node
and then dropped, invisible until something downstream needed it.

Prism's `NumberedParametersNode#maximum` is the arity, and `_1`…`_max` are exactly the
required parameters Ruby binds. The auto-splat follows from the arity rather than needing a
rule: `[[1,2]].map { _1 }` is `[[1, 2]]` (arity 1) and `[[1,2]].map { _1 + _2 }` is `[3]`
(arity 2) [V] — which is what a `[:preq, "_1"]`, `[:preq, "_2"]` list already means.

`render.rb` still emits no parameter list for them, and now has to say so explicitly:
`{ |_1| … }` is a syntax error in Ruby ("_1 is reserved for numbered parameter"). Re-parsing
recovers the same synthesized list, so the round-trip stays a fixpoint — the seeds and the
1,227-program bootstraptest corpus confirm it.

Found while probing the C35 scoping change: `_1` is a *scope local* in Prism's `locals` set,
which is why it had to be excluded from the new `declared` slot, and excluding it is what
prompted asking what the model did with it. Confirmed pre-existing (`git stash` + rebuild) —
the rule that keeps a session honest about what it broke.

## C37 — a range or regex literal must not consult a constant (bugfix)

`1..2` desugars to `Range.new(1, 2, false)` and `/b/` to `Regexp.new("b", 0)` — both since the
beginning, and both **behaviour-identical to the literal except for one thing nobody looked at**:
a literal is a parser node in Ruby and consults no constant at all, while a send over a bare
`Range` constant performs a lexical lookup that Ruby never performs. So any enclosing `Range` or
`Regexp` constant hijacks every literal in that scope:

```ruby
module M
  Range = 5
  def self.f = (1..2)     # CRuby 1..2; model NoMethodError: undefined method 'new' for 5
end
```

Not hypothetical, and not exotic: **the prelude's own sorbet shim defines `T::Range`** (as
`T::GenericType`, for `T::Range[Integer]`), so every range literal inside `module T` was already
broken — `undefined method 'new' for an instance of T::GenericType`. Found while writing L127's
`string_truncate_middle`, whose body is `s[0...27] + "..." + s[-30..-1]`.

Both lowerings now use a `cpath` with no base — `::Range`, `::Regexp` — which skips the lexical
chain and resolves on Object. Array, Hash, String and Proc literals were checked and need
nothing: none of them lowers through a constant.

**What is left open, and it is small.** `::Range` still reads a constant, so a program that
reassigns the *toplevel* `Range` would still be misread where CRuby's literal would not care.
Closing that means a dedicated AST head for the two literals — which is an export break, and
which would have to re-implement in Lean the endpoint check that L122 deliberately wrote as
prelude Ruby *because it dispatches*. Not worth it for a shadow nobody writes; recorded so the
trade is visible.

Rule coverage unchanged (`range->send` and `regex` already existed); seeds 43/43, bootstraptest
1227/0.
