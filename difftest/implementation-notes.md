# difftest — implementation notes (non-critical choices, for rollback)

Same convention as the harness's `../desugar/implementation-choices.md`:
every non-obvious implementation choice gets a numbered entry here and this file is
committed on each change, so any decision can be found and reverted. Load-bearing
*design* decisions live in [`../docs/testing/engine.md`](../docs/testing/engine.md) §Invariants; these are the
smaller calls.

## N1 — Tier 0 is repurposed as the conformance-corpus tier; bootstraptest is its first source

Tier 0 was originally sketched as "conformance suites from other languages,
AI-translated to Ruby". MRI's own `bootstraptest/` is a strictly cheaper first
occupant: already Ruby, already self-contained single-file programs, harvester
already exists (`../desugar/bin/harvest_bootstraptest`), no
translation or licensing questions. Translated foreign suites remain a future
tier-0 source, not a separate tier. (Refocus decision of 2026-07-07: corpora
covering the language's real distribution come before splicing/mutation.)

## N2 — Tier 0 has no pre-filter gate; the run-time control gate is the gate

Bootstraptest cases go straight into `run_case`, whose existing control gate
(parse check, timeout, determinism double-run) excludes unusable cases as
`CONTROL_INVALID` *with reasons* — consistent with "no silent caps" and with
the fact that the harvester already skips obviously out-of-scope files
(threads, `require`, `rand`, …). No separate validation pass to maintain.

## N3 — `run --tier 0` runs the whole corpus by default; `-n` takes a seeded random sample

`-n` therefore no longer has a global default of 100 in the CLI; tier 1
defaults to 100 when `-n` is omitted, tier 0 to "all". The sample is drawn
with `random.Random(seed)` and re-sorted by case id so reports stay in stable
order.

## N4 — The bootstraptest corpus stays unvendored (gitignored in the harness)

The difftest source points at the harness's harvested copy
(`../desugar/corpus/bootstraptest/`) and raises with the harvest
recipe when it is missing, rather than vendoring ~1300 upstream-derived files
into this repo.

## N5 — `manifest.json` rides along as provenance only

The harvester's per-case `expected` value is recorded in `TestCase.provenance`
for triage, but the differential verdict never uses it — the control (CRuby)
recomputes ground truth, which also keeps cases whose harvested `expected` was
approximate from producing false disagreements.

## N6 — Mixed campaigns live in `difftest/campaign.py`; the old tier-1 campaign module is subsumed

Per HANDOFF resolution (b): the campaign stays a Hypothesis property; the mix
is a strategy-level weighted choice between arms ("tier1" = fresh generation,
"tier0"/"tier3" = `st.sampled_from` a loaded corpus). `run --tier 1` is now
the `mix={"tier1": 1.0}` special case of `run_generative_campaign`;
`tiers/tier1/campaign.py` was deleted. The summary key changed from `"tier1"`
to `"campaign"` (now also carrying `mix` and `arm_counts`).

## N7 — Mix weights are quantized to thousandths; every arm gets ≥ 1 slot

The arm choice is `st.integers(0, 999)` against cumulative thresholds. Any
positive weight is rounded up to at least 1/1000 so a requested arm is never
silently dead (rounding drift is absorbed by the heaviest arm). A pure-tier-1
mix skips the arm-choice draw entirely, keeping shrink behavior and case ids
(`tier1-NNNNN`) identical to the old tier-1 campaign.

## N8 — Corpus draws in a mix get fresh `mix-NNNNN` ids; disagreements point back at the corpus

A corpus case can be drawn more than once per campaign, so each draw gets its
own case id with the original id in `provenance.corpus_id`. A disagreeing
corpus draw is reported as `campaign.disagreeing_corpus_case` and no
minimized-reproducer file is written (the case is already persisted and
small); only tier-1-origin disagreements land in `corpus/regressions/`.

## N9 — Mix weights are targets, not guarantees

Hypothesis draws integers non-uniformly (it biases toward shrink-friendly
values), so realized arm frequencies drift from the requested weights toward
the *first* arm in the mix spec — e.g. a requested 0.90/0.05/0.05 realized as
194/5/1 over 200 draws. This is accepted: the campaign's job is to interleave
sources, not to hit exact proportions, and the realized mix is always reported
as `campaign.arm_counts` in the summary. Write the heaviest arm first in
`--mix` so the bias reinforces rather than fights the intent. Revisit with an
explicitly seeded `random.Random` arm choice if exact proportions ever matter
(at the cost of the arm choice being invisible to the shrinker).

## N10 — Every control run executes in a fresh temp cwd

Discovered by the first full tier-0 run: bootstraptest cases create files in
the working directory (`zzz2.rb`, `b/foo`), littering the repo and letting
filesystem state leak between the determinism double-run and across cases.
`CRubyRunner.run` now runs each subprocess in its own
`tempfile.TemporaryDirectory`. The desugar SUT's *desugar* subprocess still
inherits the engine cwd (it only parses/rewrites, never runs the program);
the rendered program itself goes through `CRubyRunner.run` and is isolated.

## N11 — Tier "1.5": eval-order probes as a separate tier over the shared grammar

Eval-order conformance is a distinct **tier id** (`--tier 1.5`), not a per-tier
flag, so tier selection stays uniform (`--tier` is a string: `0`/`1`/`1.5`/`2`/`3`).
It is **structurally separate** from tier 1 and shares the grammar by *reuse, not
duplication*:

- `tiers/tier1/strategies.py` — the shared scope-aware generator, unchanged and
  probe-agnostic.
- `tiers/tier1_5/probe.py` — a pure **AST→AST transform** `add_eval_order_probes`
  that walks the tier-1 AST generically (`dataclasses.fields`) and wraps every
  leaf value-node (`IntLit`/`StrLit`/`SymLit`/`BoolLit`/`NilLit`/`LocalRead`) in a
  probe call `__t("<n>", leaf)`, prepending the prelude `def __t(l, v); puts(l);
  v; end`. The label counter is **local to the transform** (`itertools.count()`
  per program) — no module global, no flag threading.
- `tiers/tier1_5/strategies.py` — `programs()` = `tier1.programs().map(
  add_eval_order_probes)`. `Strategy.map` keeps shrinking intact (Hypothesis
  shrinks the underlying tier-1 AST and re-applies the pure transform).

The campaign is generic over a **registry of generative arms** (`tiers/__init__.py`
`GENERATIVE_ARMS = {"tier1": …, "tier1.5": …}`, arm-name → program-strategy
factory). `run_generative_campaign(gen_strategies=…)` treats any mix key in that
registry as generative (generate + `render_program`, id `{arm}-NNNN` when pure,
`mix-NNNN` in a mix) and anything else as a corpus arm. Both pure `--tier` runs
(`--tier 1.5` is just `mix={"tier1.5": 1.0}`) and `--mix` campaigns share this one
path, so **tier 1.5 is a first-class `--mix` arm** — e.g.
`--mix "tier1.5=0.9,tier0=0.1"`, or even `tier1=0.5,tier1.5=0.5` to run plain and
probed side by side. Adding a future generative tier is a one-line registry entry;
the CLI validates mix arms against `GENERATIVE_ARMS ∪ CORPUS_ARMS`.

`__t` prints the label and returns the leaf, so the stdout trace records the exact
left-to-right evaluation order of subexpressions. Labels are baked into the source
both control and SUT run, so a reorder/double-eval between them shows as a trace
difference and can never be a false positive (identical source → identical labels).
Because the walk is generic it wraps leaves the earlier in-generation approach
missed — notably **hash keys** and **index positions** — strictly broader coverage.

Validated: `--tier 1.5 --sut identity`/`--sut desugar` all-agree (desugar preserves
order); `--tier 1.5 --sut desugar --inject-bug` reliably finds and shrinks a
disagreement (naive `&&`/`||` double-evaluation prints a probe label twice) — the
probe has teeth. **Known gap (follow-up):** the tier-1 grammar has no writer-calls
(`a[i] = v`, `a.attr = v`) or side-effecting receiver/index — `Assign`/`OpAssign`
are locals-only and `Index` reads a literal array at a literal index. So tier 1.5
exercises operand order for calls/binops/logical/array/hash/interp/index, but not
the recv→index→rhs ordering of assignment-calls (covered for now only by seed 27
and tier-3 eval-order/010). Adding writer-call AST nodes to the shared grammar is
the high-value next increment — and both tiers would then benefit automatically.

## N12 — Classes/instances added to the shared tier-1 grammar (tier 1.5 inherits)

The tier-1 grammar previously had only top-level `def`/bare-call, so the whole
object model (the desugar M3 core and the Lean L2 fragment) went unexercised by
fuzzing. Added three AST nodes to the *shared* `tiers/tier1` grammar so both tier 1
and tier 1.5 (which is `tier1.programs().map(probe)` — N11) get them for free:
`ClassDef` (name + ivars + instance methods), `New` (`C.new(...)`), `MethodCall`
(`recv.m(...)`), plus `IvarRead` (`@x`). Scope-awareness (the prong-2 design, `../docs/front-end/method.md` 06 §4) is
preserved by extending `Env` with `classes`/`instances`/`ivars` so `.new`
arg-counts and receiver methods resolve and dispatch actually fires.

Termination-by-construction (HANDOFF invariant 4) is kept by two deliberate
constraints, mirroring the existing method-DAG discipline:
- **`initialize` is synthesized, pure** — one param per ivar, each stored straight
  into its slot; `.new` never runs arbitrary generated code, so it cannot recurse
  or livelock.
- **Strict class DAG** — a class's instance-method bodies see only *prior* classes
  (`classes=env.classes` at def time) and earlier same-class methods + top-level
  methods as bare self-sends; a class cannot instantiate or self-send into itself.
  Combined with pure ctors, the call/instantiation graph is acyclic and bounded.

Instance-holding locals use a dedicated pool (`o`/`p`/`q`, disjoint from the
value-local/loop/param pools) and are tracked in `Env.instances` **outside**
`Env.locals` — so they are only ever emitted as method-call receivers, never
op-assigned or read as bare values (which would leave a stale type or halt on
`NoMethodError`). Default `#<C0:0x...>` inspect output (incl. nested ivar objects)
is already address-normalized (`observation.py` `_ADDR_RE`), so instance output is
deterministic. Validated: 38 pytest green (parse+determinism properties now cover
the class grammar); `--tier 1 --sut identity` 150/150 agree; `--tier 1`/`--tier
1.5 --sut desugar` **150/150 · 100/100 agree, 0 unsupported, 0 disagree** (class
programs round-trip fully in-fragment through the harness).

## N13 — Blocks, inheritance, metaprogramming, writer-calls added to the shared grammar

Closed the four biggest generative-coverage gaps (tier 1 owns the grammar; tier 1.5
inherits every node via `.map(probe)` — N11). All additions preserve the two
load-bearing invariants: **termination-by-construction** (HANDOFF invariant 4) and
**scope-awareness** (the prong-2 design, `../docs/front-end/method.md` 06 §4, so dispatch fires instead of dying on
NameError). New pure-leaf nodes were registered in the tier-1.5 probe `_LEAVES`
(`BlockGiven`, `ConstRead`); every other new node is handled by the probe's generic
dataclass walk.

- **Blocks/procs/lambdas.** `yield`/`block_given?` in generated methods (yielders
  live in `Env.yielders`, kept OUT of `methods` so a plain call never hits them
  without a block → no `LocalJumpError`); block-carrying sends over bounded
  collections (`each`/`map`/`select`/… on literal arrays/ranges) and yielders;
  `->`/`proc`/`lambda` literals + `.call`; `&proc`/`&:sym` block-pass (only
  **non-strict** procs are `&`-passed — a strict lambda with a yield-arity mismatch
  would raise `ArgumentError`, so `procs` carries a `strict` flag; `&:sym` uses
  only universally-safe unary methods `to_s`/`inspect`/`itself`/`class`/`freeze`);
  and `next`/`break`/`return` jumps. Proc-vs-lambda jump divergence is left to tier
  3. Also lands `RangeLit` as a bonus.
- **Inheritance/super/modules/self-methods.** `class C < D`, `module M` +
  `include`/`prepend`, `def self.m` (called `C.m(...)`), and `super`/zsuper in
  overrides. `ClassInfo` now tracks *effective* instance methods (own + inherited +
  mixed) and `ctor_arity` (a subclass inherits its parent's `initialize`), so
  dispatch/`.new` arities stay correct. Strict DAG extended: superclass/modules are
  always *prior*; an override's body excludes its own name from bare-callables (so
  it never self-recurses — `super` reaches the parent instead).
- **Metaprogramming (heap mutation).** `send`/`public_send`, `respond_to?`,
  `instance_variable_get`/`set`, `attr_accessor`/`reader`/`writer`, `define_method`
  (→ instance method, registered), `define_singleton_method` (→ class method), and
  class reopening (`Env.update_class`). All resolve against the class `Env`, so the
  dynamic calls actually dispatch. Deferred (→ tier 3): string `eval`,
  `instance_eval`/`class_eval`, `alias`, `const_get/set`, per-instance singletons.
- **Writer-calls + multiple assignment.** `a[i] = v`, `a[i] ||= v` (containers held
  in a disjoint frozen pool `ix0..ix2`, so the target never gets reassigned to a
  scalar), `obj.attr = v` (paired with `attr_writers` from the accessor decls), and
  `a, b = …` / `a, *b = …`. Directly feeds the tier-1.5 eval-order probe's
  documented top gap (writer-call once-only obligations, N11).

**Termination bug found + fixed in the process:** `next`/`break` inside a
`WhileCounter` body target *that* loop and skip the renderer's manual `+= 1`
increment → infinite loop (surfaced as one `control_invalid: timeout` in a 500-case
run). Fix: a `while` body sets `in_block=False` (no `next`/`break` emitted there);
`times`/literal-block bodies are self-counting so they set `in_block=True` (safe,
and nested blocks re-enable jumps targeting themselves). `if`/`begin` are
transparent and inherit the flag correctly.

Validated: **38 pytest green**; 1000+-program parse+determinism sweeps per item
(0 parse-fail, 0 timeout, 0 nondeterministic); and per-item `--tier 1`/`--tier 1.5
--sut desugar` at 300–500 cases each — **0 disagree throughout** (unsupported rises
as expected where new surface outruns the desugar fragment: massign single-RHS,
kwargs, `define_method`, etc.).

## N14 — A SUT wall-clock timeout (control OK) is `sut_unsupported`, not `disagree`

`compare()` now classifies "SUT timed out, control completed within the limit" as
`SUT_UNSUPPORTED` (reason "sut timeout …") rather than `DISAGREE`. Rationale: a
wall-clock timeout is *inconclusive* — the model produced no answer, it did not
produce a wrong one — so it belongs in the same neutral bucket as an explicit
Unsupported gate. Genuine nontermination in the model is separately caught by its
step-fuel limit, which exits cleanly as Unsupported (exit 3) well before any
plausible wall-clock; so this policy only absorbs "correct but too slow" cases
(e.g. `100000.times{…}` — the interpreter needs ~18s, the default timeout is 10s).
Prevents the iterating-builtin work (Lean L32) from turning pre-existing
Unsupported stress tests (`test_proc_008`, the `yjit_30k_*` benchmarks) into
false disagreements. If the model diverged where CRuby terminates, this would
mask it as Unsupported rather than flag it — acceptable because fuel is the real
divergence guard; revisit if a faster interpreter makes fuel reachable in-budget.

## N15 — Tier-1 generation defects: flip-flop ranges and top-level `return` (yield fix)

An audit of tier-1 yield against the Lean SUT found ~⅓ of every run gated at the
**desugar** stage (before any semantics), from two generation defects:

- **Flip-flop.** A range literal that is the *direct* condition of `if`/operand of
  `!`/predicate of a ternary is parsed by Ruby as a stateful **flip-flop operator**,
  not a range (verified via Prism; `&&`/`||`/`==`/args/array/assignment positions
  are all safe). The generator drew `range` as a general `_expr` kind, so it landed
  as `if (1..3)` / `!(1..3)` → desugar gate `flip-flop operator`. Fix: a
  `no_range_head` flag on `_expr` drops the `range` kind at *that* level only
  (children recurse unrestricted — matches Prism's rule exactly), passed at the two
  risk sites (`If.cond`, `Not.expr`).
- **Top-level `return`.** The desugar's `@fn_depth` gate counts only real `def`/`defs`
  bodies, *not* `define_method`/`define_singleton_method` blocks. `_method_body` set
  `in_method=True` unconditionally, so it emitted `return` inside those blocks →
  desugar gate `top-level return`. Fix: `is_def` param on `_method_body`
  (`in_method=is_def`); the two `DefineMethod` call sites pass `is_def=False`, so a
  `define_method` body computes values without a lexical `return` (a nested block
  inside it still can't, since `in_method` stays False).

Effect (`--tier 1`, seed 7): vs **desugar** 166 agree/84 unsup → **250/250, 0 unsup**;
vs **lean** 124 agree/276 unsup → **143 agree**, 0 disagree (the residual lean gates
are its own unmodeled levers — `define_method`/`include`/`Range`/`attr_*`/`times` —
not desugar defects). 0 disagree throughout. These were fuzzer-fidelity bugs (the
flip-flops meant the generator was silently testing a *different* construct than
intended), not desugar/lean limitations.

## N16 — Param variety: optional/keyword/rest/kwrest/`...`-forwarding/destructuring (Lean Phase-2 coverage)

The audit's headline gap: the generator emitted only fixed positional required params,
so **none** of Lean's Phase-2 native param binding (optional defaults, keyword params,
`...` forwarding, destructuring) got any generative differential testing. Added:

- **Structured `Param` AST** (`ast.py`): `POpt`/`PRest`/`PKey`/`PKwRest`/`PBlock`/`PFwd`/
  `PDestr`, mirroring the RubyCore `PARAM_HEADS`. A `Param` is deliberately **not** a
  `Node`, so the tier-1.5 probe walk skips params (and any default expr they carry). A
  param-list element is `str | Param` (plain required stays a bare string — back-compat).
  `Call`/`MethodCall` gained a `kwargs: tuple[(name, Node)]` slot; `FwdArg` renders `...`.
- **Sig-aware call generation** (`strategies.py`): a `Sig` (reqpos/nopt/rest/req_keys/
  opt_keys/kwrest/fwd) describes a callable's shape; `_gen_call` produces a *compatible*
  call that never raises ArgumentError (optionals as a prefix, all required keywords
  supplied, `**kwrest`/`...` may take extra names). Sigs live in a **parallel `Env.sigs`
  registry** keyed by name — `env.methods` still stores `(name, reqpos)` as plain ints, so
  no existing merge/ClassInfo path changed type. Every call site consults `env.sig_for`,
  and `sigs` is threaded into `_method_body`, so method bodies also call varied methods
  compatibly. **Scope: top-level methods only** (`programs()` `varied`/`fwd` flavors);
  instance/class/module methods stay plain-required (their call paths are untouched).
- **popt defaults** read an earlier param when possible — exercises the lazy
  left-to-right callee-frame default-eval obligation (the desugar's seed-31 property).
- **`...` forwarding**: a `fwd` method forwards to a prior `*rest`+`**kwrest` **sink**
  (which absorbs any positional+keyword mix cleanly — no positional-hash degradation
  ambiguity), so forwarding is always well-typed.
- **`pdestr`**: a destructuring block param `|(da, db)|` via a new `destr` block-arg
  choice (lenient over scalars) + a `pairs` receiver (`[[..],[..]].each/map`) for real
  array destructuring. `_bound_of` flattens a param list to its bound locals.

Effect (`--tier 1`): vs **desugar** 300/300 across seeds 7/123/456/999 (0 unsup, 0
disagree); vs **lean** seed 7 197→**222**/500 agree (0 disagree). All param forms present
in a 400-sample scan (optional 118, rest 110, kwarg-at-call 106, keyword 83, kwrest 73,
destructuring ~98, `...` 4). Smoke tests `test_varied_params`/`test_fwd_forwarding`/
`test_destructuring_block` pin the semantics.

## N17 — `for` loops (index leaks to the enclosing scope)

Added `for var in coll; …; end` (`A.ForLoop`). Unlike a block param, the loop var
**leaks** to the enclosing scope (Ruby `for` semantics) — so it is registered as a
local *after* the loop, from a disjoint `FOR_POOL` (`fi`/`fj`). The collection is a
bounded literal array or small range, so iteration terminates by construction;
`next`/`break` are legal in the body (self-bounded). Exercises Lean's Phase-1 `for`
rule (the scope-leak). `--tier 1`: desugar 300/300 (seeds 7/456), lean 139/400,
0 disagree.

## N18 — `redo` + do-while (bounded so they terminate)

Two Phase-1 loop forms, both engineered to terminate by construction:

- **do-while** (`A.DoWhile`): `var = 0; begin; body; var += 1; end while var < limit`
  — runs the body at least once, bounded by the same counter discipline as
  `WhileCounter`. `next`/`break` disabled in the body (they'd skip the appended
  `+= 1` → infinite loop), matching the `while` treatment.
- **`redo`** (`A.RedoLoop` + `A.Redo`): a self-contained gadget
  `guard = 0; coll.each do |bx| guard += 1; redo if guard < limit; …body end`.
  The guard increments on every (re)entry and never resets, so total entries ≤
  `limit + len(coll)` — `redo` provably cannot spin forever. `redo` is emitted
  *only* inside this gadget (never as a free statement), and `guard` is frozen so
  random code can't clobber it. A 250-example CRuby run of every redo/do-while
  program produced **0 timeouts**.

`--tier 1`: desugar 300/300 (seeds 7/456/999), lean 141/400, 0 disagree.

## N19 — `alias`/`alias_method` + `undef` (method-table heap mutation)

Class-body method-table mutation, exercising Lean's Phase-1 `alias`/`undef` rules.
Rendered as **tail decls** (new `ClassDef.tail_decls`, emitted *after* the instance
methods) so the referenced method is already defined in the class body above them:

- **alias**: aliases an existing effective instance method to a fresh `ALIAS_POOL`
  name (registered as callable, same arity), randomly as the `alias new old` keyword
  or `alias_method :new, :old`.
- **undef**: defines a dedicated throwaway method (`UNDEF_POOL` = `ud0`) that is
  **never registered as callable**, then `undef`s it — so no body or main code ever
  invokes it (no NoMethodError risk); the mutation is a clean no-op observationally.

`--tier 1`: desugar 300/300 (seeds 7/456/999), lean 118/400, 0 disagree.

## N20 — Constant paths `A::B` (cpath read + cpath_asgn)

Exercises Lean's Phase-1 `cpath`/`cpath_asgn` heads and two-phase constant lookup:
- **class-body constants** (`ConstAssign`, `K0 = <literal>` in `decls`, tracked in
  `ClassInfo.consts`), read as `Cls::K0` via the new `_expr` `cpath` kind.
- **external assignment** (`ConstPathAssign`, `Cls::E0 = v`) — a `cpath_asgn` statement
  assigning a *fresh* external-const slot (`EXT_CONST_POOL`), registered on the class so
  later reads resolve, and each slot used once (no "already initialized" reinit).

Load-bearing gate: constant assignment is a **syntax error inside any block or method**
("dynamic constant assignment"). `in_block` is insufficient (a `proc`/`lambda`/`times`
body sets `in_block=False`/`True` inconsistently and is still a closure), so a dedicated
`Env.const_asgn_ok` flag is set False on entering *any* method/block/lambda/proc/`times`
body and left True only at static positions (top-level, class body, `if`/`while`/`for`/
`begin` — not closures). `cpath_asgn` is gated on it. `--tier 1`: desugar 300/300 (seeds
7/456/999/2024), lean 175/400, 0 disagree, 0 control_invalid (an early miss — cpath_asgn
inside a `proc` — is what surfaced the need for `const_asgn_ok`).

## N21 — Rich exceptions: typed/multiple rescue, else, ensure, `retry`, `raise Klass,msg`

`A.BeginResc` replaces the single-clause `begin/rescue` for generated code:
- **typed + multiple rescue clauses** over mutually-non-ancestor `EXC_CLASSES`
  (`RuntimeError`/`TypeError`/`ArgumentError`/`ZeroDivisionError`): an optional leading
  *non-matching* typed clause (skipped at runtime), an optional *matching* typed clause
  (single- or multi-class), and **always a final bare catch-all** so nothing propagates
  (any stray deterministic error from the body is caught) — which keeps `else`'s "ran
  iff no exception" observation clean.
- **`raise Klass, msg`** (`Raise.exc_class`) so a typed clause has something to match.
- **`else`** (runs iff no exception) and **`ensure`** (always) clauses, each with an
  observable marker line.
- **`retry`** (`A.RetryBegin`): a self-contained bounded gadget — `guard = 0; begin;
  guard += 1; raise if guard <= limit; …; rescue => e; …; retry; end`. The guard
  increments each attempt and the raise stops once `guard > limit`, so the begin
  succeeds after `limit`+1 attempts. No random body stmts (they might raise and make
  `retry` spin). A 400-example CRuby run of every retry/ensure/typed-rescue program:
  **0 timeouts**. `--tier 1`: desugar 300/300 (seeds 7/456/999), lean 114/400, 0 disagree.

## N22 — method_missing + `class << self` eigenclass

The last two object-model rules with no generative coverage:

- **method_missing** (A6): a class optionally defines `method_missing(name, *args)`
  returning a deterministic `"mm-#{name}"` (kept OUT of the callable set, reached only via
  missing dispatch). An `_expr` `mm_call` kind then sends a **never-defined** name
  (`MM_GHOST_POOL` = `ghost0`/`ghost1`) to an instance of such a class → dispatch falls
  through to method_missing. `ClassInfo.has_mm` + `Env.mm_instances` gate it to instances
  whose class actually defines it (else it'd be a NoMethodError). Coverage is modest
  (~1–2% of programs — an mm-instance must be in scope where an expr is drawn) but nonzero
  where it was previously **zero**.
- **`class << self` eigenclass** (A7): `A.EigenClass` renders `class << self; def esm0; …;
  end; end` inside a class body; the method becomes a class method (registered in
  `sinfos`, called as `C.esm0`). Exercises the `sclass` head (Lean L2c), distinct from the
  already-covered `def self.m`/`define_singleton_method`. Per-instance `class << obj` is
  left for later (class-level singleton methods are already covered three ways).

`--tier 1`: desugar 300/300 (seeds 7/456/999/2024), lean 120/400, 0 disagree. 14 render
smoke tests pass.

### N22 addendum — a real desugar bug found by method_missing (interpolation ≠ `String()`)

Generating method_missing surfaced a genuine **desugar** disagreement (tier-1 seed 314):
the desugar lowers string interpolation `"#{e}"` to `Kernel#String(e)`, but the two are
**not** equivalent. `String(o)` coerces via `rb_check_convert_type(:to_str)` — which
dispatches through `method_missing` — then falls back to `to_s`; real interpolation
(`rb_obj_as_string`) calls **only** `to_s`. So for an object defining `method_missing`
(or a real `to_str`), `String(o)` → `mm-to_str` while `"#{o}"` → `#<C:0x…>`. Minimal
repro: `class C; def method_missing(n,*a); "mm-#{n}"; end; end; puts("v=#{C.new}")`
(verified: CRuby interpolation and `String()` diverge, `respond_to?(:to_str)` is false).

This is a desugar-harness bug (interpolation should not lower to `String()`); a faithful
fix (`String === v ? v : v.to_s`, evaluating `v` once) belongs on the desugar side with
its own round-trip re-validation. Until then, the tier-1 generator keeps method_missing
classes out of **value-position `new`** (the only way an mm-object could reach
interpolation), preserving method_missing coverage via receiver-only instances while
staying 0-disagree. Recorded here as a genuine differential-testing find (the point of
the exercise), not swept under the rug.

**Resolved** by desugar C30 (interpolation → `rb_obj_as_string`, not `Kernel#String`); the
value-position `new` workaround is reverted in N25.

## N23 — Two latent generator bugs found by the broad-seed sweep (termination + inheritance)

A 17-seed robustness sweep (not just the 4 seeds used per-feature) surfaced two
pre-existing generator defects that the expanded vocabulary made reachable:

1. **`method_missing` is inherited** — `ClassInfo.has_mm` was a per-class coin flip, so a
   subclass `C2 < C0` (C0 defines method_missing) had `has_mm=False` and slipped a
   `C2.new` into value position (a massign RHS → local → interpolation → the N22-addendum
   `String()`/`to_str` divergence). Fix: `has_mm = own_mm or sup_ci.has_mm`.
2. **Unbounded mutual recursion via virtual dispatch** — instance-method bodies could
   self-call each other, and inheritance/override/shadowing let a low-rank inherited
   method call a name that dynamically dispatches to a high-rank subclass body that calls
   back up (e.g. `C2#im0` shadow → `dm0` → `im1` → virtual `im0`), giving `SystemStackError`
   (a disagreement, since the two runs blow the stack at different points). This was
   latent since the N13 object-model work. Fix: a **global name-rank invariant** —
   recursion-capable instance methods (`im`/`dm`/`rm`) are totally ordered (`_CALL_ORDER`)
   and a body may self-call only strictly-lower-ranked names (`_callable_ok`); module/attr/
   method_missing methods are sinks (never call back), always allowed. Because virtual
   dispatch preserves the *name*, every call chain strictly descends in rank → the
   per-object call graph is acyclic for any receiver, across inheritance/override/shadow.
   Replaces an earlier, insufficient "neuter only the override branch" attempt (it missed
   fresh-named methods that shadow an inherited method).

Validation: 17 seeds × 250 (incl. the failing 271) all 0-disagree/0-control_invalid;
400-example CRuby termination sweep 0 timeouts; 14 render smoke tests pass. Lesson
recorded: per-feature 3–4-seed checks are insufficient for termination/inheritance
interactions — run a broad-seed sweep before declaring green.

## N24 — `SystemStackError` is control-invalid (the oracle-side dual of the N23 fix)

N23 fixed the **generator** so it stops *emitting* unbounded mutual recursion. But a
non-terminating program that was already saved to `corpus/regressions` (or that slips any
future generator hole) still **false-disagrees on replay**: CRuby approximates
non-termination by overflowing its C stack (`SystemStackError`), and the stdout printed
*before* the overflow is stack-depth-dependent. Any SUT that adds a frame per call — the
desugar roundtrip wraps each call — overflows at a different depth and prints a different
prefix (observed: control 8733 lines vs desugar 6895 on the tier1-01274 family). The
exceptions *agree* (`SystemStackError` both sides); only the truncated prefix differs.

That prefix is not a stable semantic observable — the semantics say the program recurses
forever, so it has no well-defined final observation, exactly like a `timeout`. Fix:
`CRubyRunner.run_deterministic` now excludes a control run whose exception is
`SystemStackError` as `control_invalid` with a reason (the oracle-side dual of the N23
generator fix; single choke point, so both campaign and `replay` inherit it). Guarded by
`tests/test_control.py::test_stack_overflow_excluded`. The four bulky N23-family
reproducers were dropped from `corpus/regressions` (no longer disagreements; the unit test
is the cheaper, minimal guard).

**SUT-side dual** (`compare.py`): the gate above fires when the *control* overflows (and
`run_case` then skips the SUT entirely). The remaining corner is a program the control runs
to completion but the *SUT* overflows — the desugar roundtrip / model adds a frame per call,
so a deep-but-bounded recursion can tip over only on the SUT side. `compare` now maps that
(SUT `SystemStackError`, control did not) to `sut_unsupported` — a resource-limit artifact
of the extra frames, not a wrong answer; same neutral bucket as a `sut timeout`. Together
with the two-sided wall-clock timeout (which catches genuine hangs that grow no stack), this
gives an "either side" failsafe for both flavors of non-termination. Guarded by
`tests/test_compare.py::test_sut_stack_overflow_is_unsupported`.

## N25 — method_missing objects back in value-position `new` (N22-addendum resolved by desugar C30)

The N22 addendum kept method_missing classes out of value-position `new` as a *workaround*
for the interpolation ≠ `String()` desugar bug. Desugar **C30** fixed the root cause
(interpolation now lowers to `rb_obj_as_string` → `to_s`, not `Kernel#String` → `to_str` →
`method_missing`), so an mm-object flowing into `"#{…}"` agrees again. The workaround is
reverted: `_expr` draws `new` from all `env.classes` (not the `has_mm`-filtered subset).
Validation: 6-seed sweep (seed 1 × 400 + seeds 2–6 × 300 = 1900 examples) all
0-disagree/0-control_invalid vs desugar; the three C30 reproducers (tier1-01039/01173/01430)
replay as agree.

## N26 — Tier 4: the Sorbet corpus, taxonomized by design feature rather than by construct

The object of study for the Sorbet work is the *type system*, not the language, so
`corpus/sorbet/` is organized by which part of Sorbet's design a program probes —
`sig-basic`, `narrowing`, `assertions`, `untyped-boundary`, `escape-hatches`,
`structs-enums`, `generics` — mirroring §A of
[`../ruby-lean/AGENTS.md`](../ruby-lean/AGENTS.md) §Sorbet.
That is a different axis from tier 3's (dispatch, blocks/jumps, eval-order, …), which is
organized by Ruby construct, and both are right for their purpose.

Each program carries a sidecar declaring the expected outcome of **both halves**
(`static_expect: clean|errors`, `runtime_expect: value|sorbet_error|ruby_error`), so the
two-by-two is explicit and machine-checkable rather than living in prose. The
declarations are enforced by `difftest sorbet check` (N30), not decorative.

Programs `require "sorbet-runtime"` themselves rather than having the control wrapper
inject it: the corpus keeps tier 0/3's "self-contained single file" invariant, and the
control then exercises real runtime enforcement with no wrapper cooperation. Consequence
recorded rather than hidden — see N34 for what this does to the Lean SUT.

`--tier 4` runs the whole corpus; unlike tier 0 there is no `-n` sample, because every
program is hand-authored to probe one specific thing and sampling would lose the point
rather than save time (the corpus is 18 programs).

## N27 — `srb tc` output is parsed from its human format; a nonzero exit with no parsed errors is a tool failure

Sorbet exposes no machine-readable error format for `tc` — only `--metrics-file`
counters and the LSP protocol. The human output is parsed instead, keyed off the
trailing `https://srb.help/CODE` URL, which makes the error code unambiguous;
indented continuation lines (context, source snippets) are skipped.

Exit codes are *not* pinned (`srb tc` currently exits 100 on type errors, and this has
drifted across releases). The rule is: exit 0 ⇒ clean; nonzero **with** parsed errors ⇒
those errors; nonzero **without** parsed errors ⇒ raise `SorbetUnavailable`. A future
exit-code change therefore degrades loudly instead of silently reporting "clean".

`--no-config` keeps each check hermetic: the program plus Sorbet's built-in RBIs for `T`,
no surrounding project config or RBI payload. Right scope for a self-contained corpus.

## N28 — sorbet-runtime violations are classified by message shape, not by installing an error handler

`sorbet-runtime`'s default handlers raise a plain `::TypeError`, indistinguishable *by
class* from a genuine Ruby `TypeError` (`1 + "a"`). Telling them apart matters: one is
Sorbet's runtime backstop firing ("blame"), the other is the type-stuck outcome the
reachability checker hunts.

The robust-looking alternative — set `T::Configuration.call_validation_error_handler` to
raise a distinguishable class — was rejected because it **changes the program's
semantics**. A program under test may itself `rescue TypeError`, and the corpus
deliberately contains such a program (`sig-basic/002`: a locally-rescued sig violation is
a type-safe program, the "raised ≠ stuck" point of
`../type-safety-by-reachability.md` §2). Classifying after the fact leaves the observed
behavior untouched. The trade is that the pattern list in `sorbet.py` must track
sorbet-runtime's message wording; it is one list, in one place, covered by tests.

## N29 — sig-strip gates structural constructs instead of mangling them; iterates to a fixpoint; keeps the require

`ruby/sig_strip.rb` is the `e ⊑ e'` precision transform. Three choices:

- **Prism, not regex.** `sig do … end`, chained `.checked(:never)`, and nested assertions
  need real parse structure, and byte-range splicing guarantees everything untouched stays
  byte-identical — which is the whole premise of the probe.
- **Gate, don't mangle.** `T::Struct`, `T::Enum`, `T.absurd`, `T::Array[…]` in a value
  position are *not* annotations: the class hierarchy and the DSL-generated methods are
  part of the program's behavior. Removing them yields a *different program*, not a
  less-precise variant of the same one, so the stripper exits 3 with the surviving
  constructs named (3 of 18 corpus programs gate). Same discipline as every other
  fragment gate here: declare, never silently degrade.
- **Fixpoint, not edit ordering.** An edit's replacement is raw source text that may itself
  contain annotations (`T.must(T.cast(x, Integer))`), so the pass is iterated to a fixpoint
  (max 10) rather than ordering nested edits. Simpler and more obviously correct.

`require "sorbet-runtime"` is deliberately kept: the two variants must differ only in
annotation precision, and dropping the require would also change what is loaded.

## N30 — the gradual-guarantee relation needs a *third* run, because a rescued trap has no exception to key off

The obvious formulation of the escape clause — "licensed iff the precise run raised a
sorbet-runtime `TypeError`" — is wrong. A program may **rescue its own sig violation**
(`sig-basic/002`), in which case the two variants differ only in stdout, with no exception
anywhere. The published theorem (Siek/Vitousek/Cimini/Boyland, SNAPL 2015) does not cover
this: it is stated over a calculus whose blame outcomes cannot be caught and observed, and
real Ruby programs can do both.

So the clause is discharged by **attribution** instead. `sorbet.unchecked_variant` runs the
annotated program a third time with enforcement neutralized — two public knobs, because
they are two mechanisms: `T::Configuration.call_validation_error_handler` (sig
parameter/return/block checks) and `inline_type_error_handler` (the
`T.let`/`T.cast`/`T.must`/`T.assert_type!` family). Then:

- control == stripped → `AGREE`
- control ≠ stripped **and** unchecked == stripped → `AGREE_WEAKENED`: the entire
  difference is attributable to enforcement firing, which is exactly what the guarantee
  licenses
- otherwise → `DISAGREE`: the annotations changed behavior by some means *other* than
  trapping, which the guarantee forbids

The prelude is a single line so it shifts program line numbers by exactly one.
`AGREE_WEAKENED` is a distinct verdict rather than folded into `AGREE`, so licensed
weakenings are counted (a probe reporting "all agree" while quietly excusing half its
cases would be the "no silent caps" sin).

## N31 — a SUT may carry its own comparator, and it takes the case

`runner.run_case` now honors an optional `compare` attribute on the SUT,
`compare(control_obs, sut_obs, case)`; SUTs without one keep the default
"both implementations should produce the same observation" relation, unchanged.

The hook exists because `sig-strip` is a **metamorphic** SUT: the implementation is not
varied, the *program* is, so equality is the wrong relation. It takes the case (not just
the two observations) because the attribution run of N30 needs the source.

## N32 — the control scrubs its own temp-file path out of observations

Every program is written to a fresh `tmpXXXX.rb`, so anything reporting the script path —
`__FILE__`, a backtrace, and notably **every sorbet-runtime error message**
("Caller: /var/…/tmpshj155fk.rb:19") — differs between two runs of the *same* program.
Before this fix the determinism double-run rejected as `CONTROL_INVALID` every program
whose sig check fires, which is most of the Sorbet corpus.

That is nondeterminism the harness injected, not the program's, so `CRubyRunner.run` now
rewrites its own path (and `realpath`, since macOS `/var` → `/private/var` and Ruby
reports the resolved form) to `<program>`. Genuine nondeterminism is still caught. This
is a global control change, deliberately: the leak was never Sorbet-specific.

## N33 — finding: sorbet-runtime's wrapper is visible through reflection (a real gradual-guarantee violation)

Found by the probe on its first run outside the corpus, and kept as the probe's
**detection self-test** (`tests/test_gradual_guarantee.py`, the role `--inject-bug` plays
for the desugar SUT — a probe that never fires proves nothing):

```ruby
sig { params(x: Integer).returns(String) }
def f(x) = x.to_s
C.instance_method(:f).parameters
#  annotated: [[:req, :arg0], [:block, :blk]]
#  stripped:  [[:req, :x]]
```

The checking wrapper renames parameters and appends a block parameter, so a program that
reflects on its own signature behaves differently purely because annotations are present,
with nothing trapped. It is not licensed by the guarantee's escape clause (the unchecked
variant is still wrapped, so attribution correctly fails), and it is not exotic — keyword
splatting and DSLs that read `parameters` are ordinary Ruby. Deliberately kept *out* of
`corpus/sorbet/`, which holds programs where the relation is expected to hold, so the
corpus keeps its 0-violation ratchet.

## N34 — finding: the Lean SUT false-disagrees on all of tier 4, because `require` lies

Measured, not assumed: `run --tier 4 --sut lean` reports **17 disagree, 1 agree**. Every
disagreement is the same one — `NameError: uninitialized constant T`. The model's
`Object#require` is a no-op returning `true` (`Builtins.lean`, "the result is essentially
never observed"), which is true for an *inert* stdlib require and false the moment the
library defines something the program uses. So an honest "out of fragment" becomes a
**false wrong-answer**, which is the one classification this engine must never produce.

`type-safety-by-reachability.md` §10.4 already specifies the fix — an unknown `require`
target gates to `.unsupported`, a known one installs a mock from a manifest — and tier 0
would barely notice (1 of 1304 bootstraptest cases contains a `require` at all). It is
**not** done here because it is a model-semantics change that could affect the
typecheck-pipeline demos, whose linked programs rely on residual stdlib requires being
inert; that belongs with the mock-manifest work, not with harness scaffolding.

Until then: **do not put the `sorbet` arm in a mixed campaign against the Lean SUT**, and
read the 17 as "the model does not have sorbet-runtime", which is exactly what the
prelude-shim phase exists to change.

## N35 — sorbet-runtime's `Caller:`/`Definition:` lines are normalized out of exception messages

Every sorbet-runtime enforcement error carries its source location:

```
Parameter 'x': Expected type Integer, got type String with value "two"
Caller: prog.rb:19
Definition: prog.rb:14 (Object#stringify)
```

RubyCore carries no line numbers — the desugared AST has no source positions, by design —
so no model built on it can ever reproduce those lines. Without normalization the Sorbet
corpus cannot be compared against the Lean SUT at all: the three programs whose sig check
fires disagree on the suffix alone, with the message body identical.

The rule is deliberately narrow: **exception messages only**, and only lines matching
`^(Caller|Definition): `. Not applied to stdout, because a program that prints an
exception message itself would then have real output quotiented away. Within those limits
the risk of manufacturing a false AGREE is confined to text neither side can meaningfully
differ on. Guarded by `tests/test_observation.py`.

## N-checker — the `check` vs. `srb` relation (`checker_relation.py`)

Design notes for the checker difftest; the Lean-side notes are `../ruby-ruby-lean/notes/model/implementation-notes.md`
L87. Spec: `../docs/semantics/static-soundness-poc.md` §7.

- **Unclassified srb codes default to *type-relevant*, and that is the whole safety property
  of the module.** `EXCLUDED_CODES` is the only list; anything not in it counts. So a
  diagnostic nobody has classified, appearing on an accepted program, fires the accept zero
  and stops the run. The alternative shape — an allowlist of known type-relevant codes with
  unknown ones ignored — would turn the file into a place to park disagreements, which is
  the erosion the zeros exist to prevent. It also means no registry of srb's hundreds of
  codes is needed: the default does the work.
- **Two exclusions, both found by measurement rather than anticipated** (§7.1): 7006
  (unreachable / always-truthy — a reachability opinion) and 3002 (unsupported integer
  literal — an srb implementation limit). Each carries its reason in the source, because
  adding an exclusion narrows what the accept zero can catch and should never be a casual
  edit.
- **`check-undecidable` is distinct from `check-unknown`.** The first is "the pipeline
  broke", the second is "the checker looked and abstained". Conflating them would let
  desugar breakage read as honest abstention and quietly flatter the ratchet — the same
  distinction `FragmentChecker` already draws by returning `None` rather than `False`.
- **`check-model-bug` outranks `check-accept-disagreement`** when both apply. Both are real,
  but a model that disagrees with CRuby invalidates the ground the checker stands on, so it
  is the one to look at first.
- **The relation lives beside the existing two-by-two, not inside it.** `srb` × runtime keeps
  its seven cells untouched; the checker is a third axis reported separately. Crossing all
  three would give 18 cells and obscure the three numbers that actually matter.
- **Pinned-zero violations exit 1**, alongside the existing declaration-mismatch gate.
  Unsoundness witnesses deliberately stay findings rather than failures — the corpus exists
  to collect them — but a genuine `check`/`srb` disagreement is a bug in one of the two.
- **A `p0-fragment` corpus category exists because the harness was otherwise vacuous.** The
  22 pre-existing tier-4 programs are Sorbet-flavoured and all land in `unknown`, so every
  cell read 0 and the report looked like agreement when it was really silence. Six programs
  now populate four cells, chosen to pin the design decisions rather than to cover syntax:
  `001` (`if true then 1 else 2 end`) is the case that *forces* the 7006 exclusion — without
  it the accept zero fires on a correct program; `003` is the agree-on-verdict-not-reason
  coincidence; `004` (`1 / 2`) is why absent-from-the-table must mean no opinion.
- **`p0-fragment` is exempt from the `require "sorbet-runtime"` rule**, with a second test
  (`test_annotation_free_categories_really_are_annotation_free`) guarding the exemption so
  it cannot become a hiding place. These programs carry no annotations — they exercise the
  *static* checker — so there is no enforcement for the control to exercise. The exemption
  also buys something: they are the only tier-4 programs the Lean SUT can run, since it
  gates every other one on the `require`.
- **`check_expect` in the sidecar is optional but enforced where present.** Making it
  mandatory would turn every fragment widening into a 22-file edit on programs that predate
  the checker. Where declared it is checked, which catches a verdict silently flipping
  `accept` → `unknown` — a regression that breaks no pinned zero and would otherwise pass
  unnoticed.
- **The zeros were verified to fire, both ways.** `tests/test_checker_relation.py` drives
  each of the three into existence and asserts an unclassified srb code lands on the
  type-relevant side; end-to-end, deleting 7006 from `EXCLUDED_CODES` turns
  `p0-fragment/001` into an accept-disagreement and `sorbet check` exits 1. A pinned zero
  nobody has watched fail is not evidence of anything.
- **The fuzz arm generates Ruby *source*, not `Expr`.** Generating `Expr` would need an
  `Expr → Ruby` printer and trust in it; source reuses the existing desugar pipeline and
  guarantees `srb` and the checker read the same artifact.
- **Three intents, because one population cannot measure both directions.** `wellformed`
  must accept (anything else is a checker regression, tracked separately from relation
  violations so it cannot hide in the `unknown` count); `injected-literal` puts the bad
  operand under a **literal-rooted** receiver so `defTy` knows both types and the honest
  verdict is `reject` — the rate is `reject_recall`, the number that says whether `reject`
  earns its risk; `injected-local` puts the same operand under a *local*, where `unknown` is
  correct because `defTy` has no environment. Generating the third deliberately keeps the
  known incompleteness measured rather than assumed.
- **`srb` is batched for the fuzz arm and per-file everywhere else.** One process for the
  whole sample instead of one per program — 300 programs in ~26s. Safe *only* here:
  generated programs use nothing but top-level locals, which are file-scoped, so no two
  files can interact. The moment the grammar gains constants, methods or classes this must
  revert to per-file, and the docstring says so.
- **The grammar has no `while` and no comparison**, and a test asserts it. `builtinSig`
  carries `+ - *` only, so a loop condition cannot be typed and a terminating typed loop is
  inexpressible; `if` conditions could only be literals, which `srb` always flags 7006.
  Adding `Integer#<` unlocks both and is the top ratchet item — but it is a *checker*
  change, not a harness one: `int_bin_dispatch` is `Int → Int → Int` and a Bool-returning
  variant is needed, along with a `builtinSig_inv` that admits a non-`int` return.

## N-siggen — the type-directed generator (`sig_gen.py`)

Annotated Ruby, generated type-first. Spec: `../docs/semantics/static-soundness-poc.md` §7.

- **It is synthesis, not checking, and that is why it is cheap.** Terms are built downward
  from the type they must have, so the well-typed population is exact *by construction* —
  no inference, no join, no fixpoint, no subsumption decision anywhere. The temptation to
  resist is generating a program and then checking it: that is the hard problem, and it is
  the one we are trying to test. Standard technique (Palka et al. on GHC; QuickChick's
  generators-for-inductive-relations).
- **Approximation is confined to the ill-typed population.** A mutated program is only
  *intended* ill-typed; `srb` adjudicates. So a generator mistake shows up as an explicit
  generator-vs-`srb` cell rather than corrupting the check-vs-`srb` zeros.
- **`BUILTINS` is a second, independent transcription of Sorbet's RBIs**, and must never be
  `builtinSig`. If well-typedness were defined by the artifact under test, agreement would be
  guaranteed by construction. The two tables already disagree — Sorbet's `Integer#+` accepts
  `T.any(Integer, Float, Rational, BigDecimal, Complex)`, ours accepts `Integer` — and ours
  being narrower is incompleteness, which is allowed. A test
  (`test_generation_path_does_not_consult_the_checker`) enforces the separation by tokenising
  the generation functions and asserting they never name the checker. `run_siggen` is
  deliberately outside that set: it *records* the verdict for the report, which is not the
  same as letting the checker decide what is well typed.
- **Method names are prefixed with the sample id.** Toplevel `def`s land on `Object`, so a
  batched `srb --dir` run would otherwise have every program redefining `m0` — exactly the
  hazard `fragment_fuzz.srb_batch` warns about. Prefixing keeps batching legal and cannot
  affect typing.
- **`sigil` and `coverage` are coupled** [V]: at `# typed: strict` every unsig'd method draws
  7017, so partial coverage requires `# typed: true`. The CLI rejects the bad combination
  rather than silently producing a population rejected for reasons unrelated to types.
- **`Object` sites are never mutated.** Nothing is ill-typed against `Object`, so
  `incompatible` returns `None` there and the mutator skips those sites — otherwise the
  generator emits programs it wrongly believes are broken.
- **Exactly one mutation per program**, recorded by kind, so a program `srb` accepts anyway is
  a clean candidate finding rather than a pile of confounded breakages. `by_mutation` in the
  summary reports catch rate per kind, so a kind `srb` never catches stands out instead of
  being averaged away.
- **CRuby runs only where it can change a verdict**: an intended-ill-typed program `srb`
  accepted (does it really fail?), or one *our* checker accepted (the model-bug zero).
  Everywhere else it would cost a process per program to confirm what `srb` already settled.
- **Only `gen-typed-rejected` fails the run.** A generator emitting programs it wrongly
  believes are well typed invalidates every other number in the report. The unsoundness cells
  are *findings*, the same stance `sorbet_check.py` takes on `unsoundness-witness`.
- **`checker sample` prints programs and nothing else**, and deliberately skips
  `require_toolchain`: eyeballing a population should work with no `srb`, no CRuby and no
  Lean binary present. It also means `--count` had to become `default=None` and be resolved
  per-subcommand (4 for `sample`, 60 for the checking arms), rather than saddling a display
  command with a count sized for a batch run.
- **`--intent` over-generates before filtering.** Returning however many programs happen to
  fall in the requested slice would make `--count 3 --intent illtyped` silently show fewer
  than three; an unknown intent lists the real ones rather than printing nothing.
- **The footer goes to stderr, after an explicit `stdout.flush()`**, so `> out.rb` stays
  clean while the terminal still shows it *after* the programs it describes. Every emitted
  line is a `#` comment or program text, and method names are sample-prefixed, so a
  redirected multi-program dump is still loadable Ruby.

## N35 — `tier1/strategies.py` split by grammar category

1,087 lines in one file, and W4b (`homebrew/PLAN.md`) adds regex literals, the
`String` pattern methods, `<=>`/`Comparable` chains, `T::Struct` and abstract/override
hierarchies to it. Split first, per the plan's milestone M3 and its file-size norm:

| file | lines | contents |
|---|---|---|
| `tier1/env.py` | 245 | the name pools, `_callable_ok`/`_CALL_ORDER`, and `Sig`/`ClassInfo`/`ModuleInfo`/`Env` — the scope record that is prong-2's central design feature |
| `tier1/exprs.py` | 356 | literals, calls, operators, `_method_param_spec`, lambdas, blocks |
| `tier1/stmts.py` | 275 | assignment, control flow, exceptions, `_method_body` |
| `tier1/classes.py` | 193 | class/module definition and reopening |
| `tier1/strategies.py` | 87 | `programs` — the public entry point, unchanged |

**The one wrinkle: expressions and statements are mutually recursive** (a block body is a
statement sequence; a statement contains expressions). Rather than merge the two
categories back into one file, `_block_body` imports `_stmt_seq` *inside the function*. A
deferred import is the standard Python answer to a genuine cycle, it costs one dict lookup
per call in a generator that is already doing Hypothesis draws, and it keeps the category
boundary the plan asked for.

Every other cross-module use is acyclic: `exprs` → `env`, `stmts` → `exprs`/`env`,
`classes` → `stmts`/`exprs`/`env`, `strategies` → all.

**No behaviour change, checked by re-running the same seed.** `run --tier 1 -n 200
--seed 7 --sut lean` gives **182 agree / 18 unsupported / 0 disagree** both before and
after — identical, which is the strong form of the claim: the split did not perturb the
Hypothesis draw sequence, so the generated corpus is the same corpus.

## N36 — the Homebrew-slice corpus: RSpec examples as tier-0 programs (W4a)

`homebrew/PLAN.md` M5. Homebrew's own suite for the version + vulnerability slice is
**360 examples** across 8 spec files; this turns them into plain-Ruby programs the model
can consume, and runs them as `difftest run --tier slice`.

**Why a transform and not a runner.** Tier 0 compares CRuby against the model *on the same
program*, so the corpus has to be programs — no RSpec, no `expect`, no metaclass tricks.
And the interesting question is not "does Homebrew's suite pass" but "do the two executors
agree", so each expectation becomes **two** printed observations: the actual value and the
matcher's verdict. A model bug that changes a value is then caught even where the verdict
would agree either way. Both are wrapped, so one broken expectation cannot hide the rest.

**Three stages, each owned by the tool already good at it.**

1. `linker` (W3) builds the library prefix: a spec says `require "version"`, the linker
   turns that into one self-contained program.
2. `difftest/ruby/rspec_harvest.rb` parses the spec with Prism and rewrites every
   `expect(…).to matcher` **by byte offset**, so an `expect` nested in an `each` block is
   handled by the same rule as a top-level one. Ruby parses Ruby — the LK1 division of
   labour.
3. `difftest/tiers/tier0/rspec_harvest.py` assembles `prefix + helpers + memos + body`,
   writes a manifest, and writes a **skip report**.

**Matcher vocabulary handled**: `eq`, `eql`, `equal`, `be(x)`, `be > x` and friends,
`be_nil`, `be_a`/`be_an`/`be_kind_of`, `respond_to`, `include`, `match`,
`contain_exactly`, `have_attributes`, the `be_foo` → `foo?` predicate form, block-form
`raise_error`, and `not_to` for all of them — plus **`be_detected_from`**, a matcher the
spec file defines itself and which carries **102 of the 360 examples** (it means
`described_class.detect(url, **specs) == actual`).

**Three things the emitted program needs that Homebrew supplies from its boot path**, all
recorded rather than invented: `require "sorbet-runtime"` and Homebrew's own
`class Module; include T::Sig; end` (`extend/module.rb:5`); `extend/blank.rb` linked in
(11 files, in-tree, no effects — `version.rb` calls `String#blank?`); and
`utils/output.rb` included **verbatim** rather than linked, because every `require` in it
is inside a method body and linking would follow them into the 227-file cycle the slice
exists to avoid. Verbatim keeps it upstream code rather than a mock of ours.

**Validation gate.** Every emitted program is run under CRuby at harvest time; one it
cannot execute is deleted and reported as a skip, so the corpus never contains a case that
would sit at `control_invalid` forever.

**Result (measured): 355 harvested, 4 skipped, all 4 reported** —
`version_spec.rb:328` and `:911` reach constants outside the slice (`URI`,
`HOMEBREW_CELLAR`); `purl_spec.rb:23` uses the `all` matcher; `vulnerability_spec.rb:456`
uses `allow` (a stub). No silent truncation: 355 + 4 = 359 of the 360 `it`/`specify`
calls, the last being one nested inside the `matcher` definition block rather than a group.

**One byte-offset bug worth recording**, because it is the kind that produces plausible
garbage: Prism's offsets are **byte** offsets and these spec files contain em dashes, so
slicing the source by *character* index silently shifted every rewrite after the first
(`expect` became `e__exp`). `String#byteslice` throughout.

**State against the ratchet.** The corpus is **generated, not vendored** (each program
embeds ~20 KB of upstream Homebrew; `corpus/homebrew-slice/` is gitignored, same treatment
as bootstraptest), so no committed corpus disagrees. Generated and run today,
`--tier slice --sut lean` is **352 disagree** — every one of them the *same* W2c gap:
`NameError: uninitialized constant T::Helpers`, because the prelude's `T` shim has the
assertion family and `sig` but not `T::Helpers`/`abstract!`/`override`/`T::Struct`. That is
M6's work, and this corpus is the thing that measures it.

## N37 — the domain-input corpus: fuzzing the slice's *inputs* (W4d)

`homebrew/PLAN.md` M8. The premise from §W4d: for this slice the highest-value fuzzing is
not random ASTs but random **inputs**. A random program mostly exercises the machine; a
random version string exercises the tokenizer, the comparison chain, the URL parsers and
the regex engine — which is where the model and CRuby can actually differ.

**Grammar-based, not character-random.** The shapes come from the ones the spec suite
already contains: dotted numerics, `-rc1`, `_1_2`, `R13B`, date stamps, platform suffixes,
prerelease and build metadata, and the ten forge-URL templates. A uniformly random string
lands in the same "no match" arm every time and tests nothing.

**Batched, not one program per input.** Each program carries a library prefix (~25 KB from
the linker) plus a literal input array and prints one line per input, so 10,000 inputs cost
200 subprocess pairs rather than 10,000 — while the comparison stays per line. The batch
is **50**: at 250 the two Version-heavy harnesses overran the SUT timeout (control 0.1 s,
model 10 s+), which the batch exists to amortize the prefix, not to maximise.

**Five harnesses**, each printing every intermediate value (rescued, so a raise is an
observation rather than the end of the program): `version` (construct, render,
major/minor/patch, self-compare), `semver` (compare against a fixed point and against
itself), `purl` (parse, re-render), `identify` (forge URL → OSV key), and **`pairs`** —
which runs `Version.new(a) <=> Version.new(b)` **and** `Semver.compare(a, b)` on the same
pair and prints both. That last one is W4e's disagreement search reduced to a difftest
case; here it is being used for the other question (does the model agree with CRuby), but
the same programs answer both, and the control output already shows the two orderings
parting company on generated pairs.

    difftest domain-fuzz --brew <path> -n 10000
    difftest run --tier domain --sut lean --timeout 30

**Result (measured): 200 programs / 10,000 inputs, 200 agree, 0 disagree.** That is
`homebrew/PLAN.md` M8's gate, and criterion 1 of the initiative's definition of done for
the executable half of the slice.

Generated, not vendored (`corpus/domain-fuzz/` is gitignored), same as the other two
Homebrew corpora. One prelude gap fell out of the first run: `Array#zip`.

## N38 — the slice's three `control_invalid` cases are `#hash` values, and they stay that way

`difftest run --tier slice` reports `{agree: 351, sut_unsupported: 1, control_invalid: 3}`.
The one `sut_unsupported` is L117's byte-array-payload row. This entry is about the other
three, because "control_invalid" reads like a corpus defect and it is not one.

**All three are `Object#hash` *value* assertions** — `pkg_version_spec.rb:67` ("returns a
hash based on the version and revision"), `version_spec.rb:289` ("hash equality"), and
`purl_spec.rb:142`'s second expectation. `CRubyRunner.run_deterministic` runs the control **twice**
and rejects the case when the runs differ (`control.py:180`); CRuby seeds `hash` per process,
so they differ every time:

    L67.0 -1387840817511769067 true   |   L67.0 -2788053335422320650 true

**Note the `true` on both sides.** Every *predicate* in all three examples agrees across
runs; only the integer printed beside it moves. So the examples are not nondeterministic —
the **observation** is, because `__exp` prints the value as well as the predicate outcome.

**And no model work could fix them.** The model gates these too (`unmodeled method
Array#hash` / `String#hash`); the engine simply validates the oracle before consulting the
SUT, so they are classified on the control's failure. More to the point, *no* value the model
computes can agree with a per-process random seed — a faithful `hash` does not exist here.
These three are permanently outside **value-level** difftest, for a property of Ruby rather
than a deficiency of the model.

**Deliberately not fixed, and it costs nothing real.** `#hash` is *defined* four times in the
slice (`version.rb:66,705`, `pkg_version.rb:62`, `purl.rb:59`) and **called by nothing except
the three examples that test it** — of 355 harvested programs exactly 3 assert on `.hash`,
and they are exactly these. The CVE-matching path does not reach it: `vulnerability.rb`'s two
`uniq` calls (`:87`, `:111`) are both `T::Array[String]`, and the model's `uniq` compares
structurally through `valueEql` rather than dispatching `#hash`. So this is assertion-only
code, off the real code path, and the headline finding is unaffected.

**The fix, when it is worth doing, is here and not in Lean.** Have `rspec_harvest.py` emit a
predicate-only `__exp` for a hash-valued expectation. The observation becomes deterministic,
the three examples become tests of the hash **contract** (equal objects ⇒ equal hashes,
`h[v2]` finds `v1`'s entry) — which is what they actually assert — and any deterministic
model `hash` satisfies it. That is 3 recovered examples and a checkable property in place of
an unfalsifiable value. It needs `Object#hash`/`String#hash`/`Array#hash` in the model, which
do not exist today.

*One inaccuracy to clean up with it:* L118's `byteStrAwareBids` lists `String#hash` and
`Object#hash`, neither of which is a modeled bid. The list only ever filters, so they are
inert — but they imply a rule that is not there.

## N39 — W4b/W4c: the slice's own feature set, as tier-1 generation heads

`PLAN.md` §9 recorded criterion 1's generated half as done at M8 (W4d, the domain
generator). It was not: **W4b and W4c had not been started**, and the tier-1 grammar
generated *nothing* the version + vulnerability slice leans on — `grep` for `Regex`, `scan`,
`gsub`, `Comparable`, `<=>` or `Struct` across `tiers/tier1/` returned zero hits. So the
generated half of criterion 1 was exercising control flow and the object model over a slice
whose whole content is regexes and orderings.

New `tiers/tier1/slice_heads.py` (+ `A.RegexLit`, `A.RegexInterp`, `A.GvarRead`):

* **`regex_probe`** — a regex literal with the whole `String`/`Regexp`/`MatchData` surface:
  `=~`, `match`, `match?`, `[0]`, `captures`, `to_a`, `pre_match`, `post_match`, `names`,
  `named_captures`, `size`, `scan`, `sub`, `gsub` (both the replacement and the **block**
  form), `split` with and without a limit, `tr`, and the `$~`/`$1`/`$&` views.
* **`comparable_probe`** — a class that `include Comparable` over one ivar, then `<=>`, the
  five operators, `between?`, `clamp`, `sort`/`sort_by`/`min`/`max`, and the `<=>`-returns-nil
  arm that makes `<` raise `ArgumentError` (the `vulnerability.rb:202` shape).
* **`regex_interp_probe`** — an interpolated literal reached repeatedly inside a loop, with
  and without `/o`. This is **W4c**'s remaining pair of obligations.

**Two design decisions.** *Probe blocks, not `_expr` heads*: a depth-limited regex head
would generate patterns against random strings, where nearly every match fails and every
program tests the same "no match" arm — so each family draws a pattern together with
subjects it was written for and prints every intermediate. *The pattern pool is bounded by
the engine's feature set* (W4b's own wording), with backreferences a deliberate 1-in-4 share
because D2 lets `matchBR` gate and swamping the head with gates would cost most of the head.

**W4c needed no tier-1.5 change, and that is the point.** §9 called for "extending the
tier-1.5 generator with `<=>`/`Comparable` argument-order probes" — but tier 1.5 *has* no
generator: it is `tier1.programs().map(add_eval_order_probes)`, a generic AST→AST transform.
Extending tier 1 **is** extending tier 1.5. Both operands of every generated comparison are
now probe-wrapped, including `@v` and `o` inside the user's own `<=>` body, so the trace
records the evaluation order through Comparable's dispatch.

### What it found: six wrong answers, none of them gates

The heads paid for themselves on the first run. **Every one was a wrong answer** — the class
the ratchet cannot catch, in code that had been green for weeks. The fixes and their probe
evidence are `ruby-lean/notes/model/implementation-notes.md` **L120**; in brief:

1. `split` pushed `nil` for an unmatched capture group (`["", "1", "2", nil]` for
   `["", "1", "2"]`);
2. the `split` limit was spent on a separator it had already decided to skip
   (`"abc".split(//, 2)` → `["abc"]`);
3. the zero-width skip rule tested offset 0 rather than *the current field start*
   (`"aab".split(/a*/)` → `["", "", "b"]`);
4. the prelude's block-form `sub`/`gsub` looped over a **shrinking subject**, re-anchoring the
   pattern at every step (`"12".gsub(/\A\d/) { "X" }` → `"XX"` for `"X2"`);
5. `String#index` with a Regexp raised `NoMethodError` instead of answering an offset;
6. `Symbol` had `include Comparable` with **no `<=>`**, so `:k < :v` raised where CRuby
   answers `true` — the `include` had been inert since it was written.

Plus the backref globals, which no builtin was maintaining: `scan`/`sub`/`gsub` must leave `$~`
at their last match, and `split` with a Regexp must *clear* it.

(6) is worth its own note for what it says about the method: it is **not a regex bug and not in
any head's feature area**. Adding heads perturbs the draw sequence, so a new head finds old
bugs in the parts of the grammar it never touches.

### Measured

tier 1 at n=250 × seeds 1/2/3 and n=200 × seed 7: **0 disagreements**. tier 1.5 at n=200 ×
seeds 7/1/2: **0 disagreements**. The other four corpora unchanged and green (see the
`PLAN.md` §9 table). `[:v, :k].sort` still *gates* — `Array#sort`'s `SortKey` covers numerics
and strings only — which is safe and left alone.

### Not fixed, and recorded rather than left implied

*(Also L120; kept here because it is the seventh thing the heads exposed.)*

**`$~` is frame-local in CRuby and a plain global in the model.** `def inner; "zz".match(/z/);
end` followed by `$~` in the caller answers `"a"` (the caller's own earlier match) in CRuby
and `"z"` in the model. A **wrong answer**, not a gate, and unreachable by every current
corpus (the heads put matches at top level; no generated method body contains one).

It is recorded rather than fixed because the fix has a real design tension, not because it is
hard: making `$~` a frame slot would mean a prelude-implemented `sub`/`gsub` could no longer
set its *caller's* `$~` — which CRuby's C implementations do — so frame-local storage needs a
companion "set the caller's match" primitive to avoid trading this wrong answer for another.
`homebrew/slice-gates.md` carries it with the other known gaps; it belongs near the top of
that list, because unlike the rest of them it is a wrong answer.

## N40 — two heads for *where* a value lives: `$~`'s frame and a Range's endpoints

Two tier-1 generation heads written as **witnesses first**, each red before the model fix it
exists for (L121, L122) and green after. Both target the same blind spot in the W4b heads
(N39): those generate every operation at **toplevel**, in one frame, over well-typed operands —
which is precisely where a per-frame rule and a global one, or a validated constructor and an
unvalidated one, are indistinguishable.

**`regex_scope_probe` — regex operations inside method bodies.** Ten generated callees do a
regex operation and return their *own* `$~[0]`; the driver seeds the caller's frame with a
two-group match first, then re-reads `$~` and `$1` after the call. Three axes, one per way a
frame can fail to own its last match: a callee's match must not be visible to its caller; the
callee must see its own, *including* through the prelude-Ruby `sub`/`gsub`/`index` and
`Regexp.last_match`, which are C functions in CRuby and write their caller's frame; and a
block's match belongs to its **lexically** enclosing method — hence the stored-proc pair
(`mk` builds a proc, `run` calls it from elsewhere and sees nothing [V]), which is the one case
the frame stack cannot answer and `captured` can. It found the L121 defect on ten lines per
probe.

**`range_probe` — endpoint pairs a range refuses to be.** The grammar's ranges are all
`Int..Int`, the one shape where every arm of CRuby's endpoint check agrees. This head draws from
a pool that separates them — cross-type, symbol, one-nil, both-nil — plus a generated class
whose `<=>` answers `0`, `nil` or `"junk"`, since the check *dispatches* and all three answers
are distinct arms. Both `Range.new(lo, hi, extra)` and the literal, since they are separate
paths in the desugarer; `extra` is drawn from truthy non-Bools too.

That class is given a **fixed `inspect`/`to_s`**, obeying this module's no-address rule (N38) —
and that constraint is what found L122's third defect: with a deterministic repr, the model's
failure to dispatch a user `inspect` for a range's endpoint became a plain textual disagreement
instead of address noise the observation would have normalized away.

**A pre-existing defect surfaced too, and it is not mine to claim as found by design.** Adding a
head shifts hypothesis's draw stream, so tier 1.5 generated programs it never had before and
came back with a disagreement on its 149th draw — `Integer + obj` / `Integer % obj` where `obj`
supplies `coerce` through `method_missing`. (The report's 164 `disagree` rows are that one
program plus its shrink trail; the campaign stops at the first disagreement. N41 has the exact
numbers and what they cost.) CRuby calls it and raises
`TypeError: coerce must return [x, y]` on a bad answer; the model raises
`TypeError: C can't be coerced into Integer` without ever calling it. Confirmed pre-existing by
`git stash` + rebuild, on the same repro, before touching anything. The runner's own minimizer
left the case at `corpus/regressions/tier1.5-00930-minimized.rb`; it is **open**, and N41 pins it
so it runs on every `difftest run --tier regressions` instead of waiting to be re-drawn.

The general lesson is N39's, sharpened: a new head does not only test the rule you wrote it for.
It re-rolls the dice for every *other* head in the program, and a green tier is partly a
statement about which programs were drawn.

## N41 — the regressions corpus was write-only, and that is how a known defect hid behind a green ratchet

`campaign.py` has filed a minimized reproducer to `corpus/regressions/` on every
shrunk disagreement for as long as the shrinker has existed. **Nothing read the
directory.** No tier loaded it, `cmd_replay` had to be pointed at a path by hand,
and 16 files had accumulated there without ever being executed a second time.

The cost was not hypothetical, and it is measurable to the draw. N40's `coerce`
defect was found by the tier-1.5 campaign of 2026-08-14 on its **149th draw of a
200-draw budget** (`arm_counts: {tier1.5: 149}`, `stopped_early_on_disagreement:
true`). One extra generation head later, the next tier-1.5 run drew all 200 and
came back **0 disagreements over the same live defect**. Both runs were reported
honestly. Assuming that day's generator produced the shape at roughly 1 draw in
150 — a one-sample estimate, so treat it as an order of magnitude — a 200-draw
campaign misses it about **a quarter of the time**. A ratchet with a 25% chance of
being green over a filed bug is not a ratchet.

**The tier.** `difftest run --tier regressions` runs the corpus **whole** — no
sampling, ever; that is the entire point — and reconciles each case's observed
verdict against a `status` it declares in its sidecar:

| status | expected | otherwise |
|---|---|---|
| `open` | DISAGREE (`still_open`) | `unexpectedly_fixed` — **fails** |
| `fixed` | AGREE (`held`) | `regressed` — **fails** |

Both directions matter and only one of them is the classic regression check. The
other — a known-open case that starts agreeing — is bookkeeping falling behind
reality, and making it a *failure* is what forces the sidecar to be updated
instead of the corpus quietly rotting into a pile of stale `open`s.

Three design points worth defending:

1. **`still_open` must not redden the run.** A filed defect disagrees by design;
   if that counted as failure the corpus could not hold one, which is the whole
   feature. So this tier computes its own exit code rather than inheriting
   `cmd_run`'s "any disagreement is red" rule, and `report.md` grew a section
   explaining the gap between the verdict table (`disagree: 1`) and the verdict
   (`0 failures`). A reader who sees only the table would be misled, so the table
   is no longer the last word on this tier.
2. **A gate is not a fix.** `sut_unsupported` on an `open` case means the wrong
   answer became a refusal — an improvement, but not one this harness can verify
   as a fix, and marking it `fixed` on that basis would retire a live defect. It
   reports `gated`: neither pass nor fail, and printed every run so it cannot be
   forgotten. One of the 16 is in exactly this state.
3. **`regressions` is not a mix arm.** A campaign stops at its first disagreement,
   so an expected-to-fail corpus would end every mixed run on its first
   known-open case.

**The filing side got the other half.** A bare `.rb` records nothing about *what
it was filed for*, so even a human opening it had to re-derive the defect from the
program. `_file_regression` now writes a sidecar alongside: status, arm, seed, the
diff, and both observations. It **never overwrites a status a human has set** — a
re-filed case whose guard silently reverted to `open` would stop guarding.

**Triaging the 16-case backlog is the immediate payoff, and it is larger than the
tier's own cost.** First run: **14 `unexpectedly_fixed`**, 1 `gated`, 1
`still_open`. So fourteen defects found in earlier sessions had been fixed at some
point in L1xx with their reproducers never re-run — fourteen regression guards
that existed on disk and protected nothing. They are now sidecar'd `fixed` and
checked every run. Their notes are honest about the limit of this: the specific
defect each was minimized for was never recorded and is not reconstructible from
the program, so what they assert is "this agreed on 2026-08-14 and must keep
agreeing", which is all a regression guard ever asserts anyway.

`tests/test_regressions.py` covers both failure directions explicitly, because a
pinned-failure mechanism that cannot go red is indistinguishable from an empty
directory — which is precisely the state being fixed here. Verified end to end by
flipping the two statuses and observing exit 1 with `regressed` and
`unexpectedly_fixed`, then flipping them back.

## N42 — a `coerce` head, six hand-filed guards, and two campaigns of the same tier disagreeing about the same model

The witnessing half of L123 (the model now runs CRuby's `coerce` protocol). Three
artifacts, and one accident worth more than any of them.

**1. `coerce_probe`, a tier-1 generation head.** Three drawn axes, because they select
genuinely different CRuby paths and the model got each wrong: *who supplies `coerce`* (a
`def`, a `method_missing`, nothing, a `respond_to?` that vetoes, a `respond_to_missing?`
that vetoes), *what it answers* (a good pair, a pair that divides by zero, nil, a scalar,
one element, three, a pair of **Strings**), and *which operator* (eleven of them, plus
`divmod`, `between?` and `clamp`). The String pair is the one that shows the operator is
re-dispatched: `0 + o` then raises out of `String#+`, about operands the program never
wrote.

No Float anywhere, per `slice_heads.py`'s rule; the Float half of the same message rule is
pinned in the corpus instead, where the observation is a fixed string. The object gets a
fixed `inspect`/`to_s` for N38's reason — `clamp` can *return* it.

**2. Six hand-filed `coerce-*.rb` guards** in `corpus/regressions/`, 143 observed lines,
each with a `fixed` sidecar. The corpus README always allowed hand-filing; this is the
first use of it. They exist because the head cannot: a head's program is drawn, and a
drawn program can gate (see below), while these are chosen and every one of them runs.

**3. The pinned case closed.** `tier1.5-00930-minimized` — the defect
`homebrew/HANDOFF.md` led with — came back `unexpectedly_fixed`, which is N41's second
direction firing exactly as designed, and its sidecar is now `fixed`.

**The accident.** Two tier-1 campaigns ran against the same binary at the same time (a
backgrounded run I believed dead, plus its replacement). One drew all 250 programs and
reported **0 disagreements**; the other stopped at draw 170 on a real one and shrank it to
`tier1-00555-minimized`. Same model, same generator, same minute. N41 argued that a green
generative tier is partly a statement about which programs were drawn; this is that
argument as an experiment, run by mistake, with the two arms disagreeing.

The defect it found is unrelated to `coerce` and **pre-existing** (`git stash` + rebuild +
the same repro, per the handoff's rule): a Proc or lambda body's assignment to a name that
becomes an outer local only *later in the text* writes the outer local. Ruby decides that
lexically at parse time — the block's `a` is block-local because no `a` existed at the
point the block was written — and the model decides it dynamically, by whether a slot
exists in the captured chain when the body finally runs. Characterized to the boundary:

```ruby
f = -> { a = 1; 0 }   # a = 0 comes *after* → CRuby prints 0, the model 1
a = 0
f.call
puts a
```

An `each` block in the same shape **agrees**, by accident of timing: it runs before the
outer assignment, so no slot exists yet. Only a stored-and-called-later Proc separates
them. The exported AST has nowhere to record it (`["block", params, [], body]` — the
desugarer does not mark which assignment targets were new at parse time), so the fix
starts there, not in Lean. Filed `open`; it is `homebrew/HANDOFF.md`'s new named wrong
answer.

**One lesson from writing the head, which cost a rebuild to see.** As first written it
would have witnessed *nothing* on the pre-fix model: it emits `n ** obj`, the old model
gated on that, and a gate refuses the **whole program** — so all six sample draws came
back `GATE`, not `DIFF`, and the fifteen wrong lines behind them were invisible. Removing
the two gating operators from one sample turned it red immediately. A head is a witness
only in a model that gates nowhere else in the same program, which is an argument for
short heads and for the hand-filed guards above.

## N43 — pinning a defect whose correct answer contains an address

The witnessing half of L124 (how a message names a class). Three hand-filed cases, and one
corpus-shape problem solved.

**The problem the handoff named.** An anonymous class's messages carry an *address* in
CRuby (`#<Class:0x…> can't be coerced into Integer`), and N38's rule is that an observation
must be process-independent. `HANDOFF.md` concluded the case would have to assert a
**predicate over** the message — `$!.message.include?("Class:0x")` — a shape the corpus did
not contain, and called that the harder half of the defect.

It is not necessary. The program can **normalize the address itself**:

```ruby
def norm(s) = s.gsub(/0x[0-9a-f]+/, "0xADDR")
```

and then assert the *whole* message. That is strictly stronger than a predicate — it pins
the wording, the class-vs-module choice and the nesting (`#<#<Class:0xADDR>:0xADDR>` for an
instance of an anonymous class), not just the presence of an address — and it needs no new
machinery, only `gsub` with a Regexp, which the W2a engine has had since L101. Any future
defect whose answer is address-shaped should be filed this way.

Two details cost a cycle each. The address must be normalized in the **exception class
name** too (`e.class.to_s`), not only the message, because an anonymous exception class *is*
an address form. And the first draft bound its classes to **constants** — which *names* an
anonymous class (L72), so every message read `Anon can't be coerced` and the file asserted
the opposite of what it was for. It uses locals now, with two deliberate constant cases at
the bottom to pin the naming rule itself.

**The three cases.**

| case | status | pins |
|---|---|---|
| `anon-class-names.rb` | `fixed` | 27 lines: the coercion/relop/NoMethodError/FrozenError/constant/superclass messages, `Exception.new` with no message, the default repr of an instance, the four prelude messages that used `.class.name`, and `Array#to_h`'s element index |
| `eigen-names.rb` | `fixed` | 24 lines: an eigenclass's own name for each kind of attached object, the `rb_obj_class` sites where a singleton method must *not* change the message, and the one — NoMethodError's receiver — where it must |
| `anon-eigen-lazy-name.rb` | `open` | what L124 left: CRuby recomputes an eigenclass's name, the model fixes it at creation |

`Array#to_h`'s missing element index (`wrong element type Integer at 1 (expected array)`)
was found *while writing the first file* — the fourth session in a row where the guard for a
known defect turned up an unrelated one. `Enumerable#to_h`'s otherwise-identical message has
no index [V], which is why the fix is on `Array#to_h` alone.

**No generation head this time, deliberately.** The tier-1 grammar draws no `Class.new`, no
`singleton_class` and no `def obj.x`, so a head would have meant three new generator axes to
witness a family that three hand-filed files pin exactly. The heads earn their cost where the
*inputs* vary (N39's regexes, N42's coerce shapes); here the variation is in which message
rule is reached, and that set is enumerable. Recorded so the absence reads as a choice.

## N44 — two guards for the sorbet shim's message rule, and one for the literal shadow

Hand-filed, in the N43 shape (the file normalizes what it must and asserts the rest whole).

* **`sorbet-describe-obj.rb`** — 23 lines pinning `T::Types::Base#describe_obj` as the gem
  implements it: nil/true/false with no value clause, `with value <inspect>` otherwise,
  truncation at 60 characters to `27 + "..." + 30`, a user `inspect` printed rather than
  hashed, the same rules reached through a **`sig`** (parameter, return, `checked(:never)`),
  and the `T::Struct` prop message, which is a *different* rule (plain inspect, no truncation)
  and is asserted separately for that reason. Deliberately absent: a value whose `inspect` is
  the default, which the gem describes with its per-process `hash` and the model now gates on
  (L127) — a gate anywhere refuses the whole program, so it cannot share a file with the twenty
  lines that answer.
* **`range-regex-literal-shadow.rb`** — a module defining `Range = 5` and `Regexp = 5`, then
  seven literals inside it (range, exclusive, endless, a slice, a regex, an interpolated regex,
  and a `case … when 1..9`). Every one of them used to resolve the shadowing constant (C37).
  `.begin` rather than `.first(2)` on the endless range, because `Range#first` with an argument
  is unmodeled and one gate would have hidden the file.

Two shapes worth reusing. A message the gem appends a `Caller:` source-location line to is fine
in an *exception* observation (the engine normalizes it) and **not** fine when the program reads
`$!.message` as a value — `split("\n").first` is the fix, and `String#lines` is not modeled.
And `T.let(…)` inside a `show` block is the cheapest way to probe a type-error message: it needs
no class, no sig, and no static checker.

## N45 — the four known wrong answers become four executable cases

`HANDOFF.md` §Known wrong answers has been the list of defects the ratchet cannot see. Prose is
the wrong medium for that list — N41 is the whole argument — and this closes the gap: every entry
now has a case in `corpus/regressions/`, so the next session opens with
`difftest run --tier regressions --sut lean` and a red-to-green target rather than a
re-derivation from a paragraph.

| case | status | reproduces |
|---|---|---|
| `tos-not-a-string.rb` | `open` | 8 wrong answers, 4 controls |
| `integer-conversion.rb` | `open` | 10 wrong answers, 5 controls |
| `pureok-eigenclass.rb` | `open` | 6 wrong answers, 3 controls |
| `sorbet-hash-gate.rb` | `open` → reports `gated` | nothing yet, by design |

The tier now reports **26 held, 4 still_open, 2 gated**, and still exits 0: a `still_open` case
disagrees by design. It goes red if one of these starts *agreeing* (someone fixed it and the
sidecar is now a lie) or if a `fixed` case regresses.

**Writing the cases changed two of the entries**, which is the argument for writing them before
fixing rather than after:

* `Integer(obj)` was filed as a wrong error *class*. It is also a wrong *answer*: CRuby tries
  `to_int` then `to_i` before raising, so `Integer(obj)` answers `5` for an object with a `to_i`
  where the model raises — and a **control line** in the same file, `Integer(2.9)`, turned out to
  raise too where CRuby answers `2`. One message defect became ten wrong answers.
* `pureOk` and the eigenclass was not in that section at all: it was in `slice-gates.md`'s
  gates list, described as something pure repr "would ignore". It does not "would" — it answers,
  wrongly, in `p`, in an Array, in a Hash, in a Range and as an ivar. Three sessions of being
  described rather than executed. It is defect 3 now.

Three shapes worth reusing:

* **Rescue every observation.** The first draft of `tos-not-a-string.rb` printed
  `"label => #{obj}"` directly, and the wrong value escaped into the *enclosing* interpolation
  (`"label => " + 1` is a TypeError), so the program died on line 1 and pinned one defect instead
  of eight.
* **Keep gating shapes out of an `open` case.** `puts obj` gates, and a gate anywhere makes the
  tier report `gated` for the whole file — which pins nothing. The gating lines are named in the
  sidecar as the check to add *with* the fix.
* **File the gate too, separately.** `sorbet-hash-gate.rb` pins nothing today and says so. It
  exists because a gate nobody filed is a gate nobody revisits, and if it is ever closed the case
  starts testing itself.

Each sidecar carries the shape of the fix, not just the defect — where the code is, what the two
halves are, which control must stay green. The next session should not have to re-derive that
either.

## N46 — the advisory tier (R1): the decision core over arbitrary `JSON.parse` output

`nontrivial-target.md` §6 rung R1, and `HANDOFF.md`'s first next-step. W4d generates the slice's
*string* inputs; this generates its other one — the advisory Hash that `vulns/match.rb` hands
`Vulnerability.new` straight out of `JSON.parse` of an HTTP body, with no schema validation of the
record.

`difftest advisory-fuzz --brew <path> -n 800`, then `difftest run --tier advisory --sut lean`.

**The domain is the JSON algebraic datatype**, per §5.1: nested Hash/Array/String/Integer/Float/
bool/nil with String keys. Generation is *skeleton plus mutation*, not uniform random — a random
JSON value fails the `sig` on `initialize` and tests nothing past it, whereas an OSV skeleton with
*k* nodes retyped, deleted, wrapped or unwrapped is how a hand-edited advisory-database entry
actually goes wrong. Each program carries its mutation log as a comment, so a red row names its own
cause. The eight seed cases are `nontrivial-target.md` §3's six witnesses plus its two
out-of-family outcomes (`KeyError`, the silent `:affected`).

**One advisory per program, deliberately unbatched** — the opposite of the domain tier's choice, and
for a reason that tier does not have: a gate refuses the *whole* program, and §3.3 predicted this
corpus would find gates the harvested one never touches. One shape per program means a gating shape
costs its own rows and nothing else, so the gate count is a measurement rather than a loss. It was
the right call: 24 of 106 programs gated.

**First run: 82 agree, 0 disagree, 24 gated**, over 794 (advisory × version) pairs. Two things worth
separating, exactly as §8's risk row asks:

* **No disagreement.** On every shape the model can execute, it matches CRuby — including all six
  witnesses, which is what makes them Direction-A certificates rather than CRuby anecdotes.
* **23 of the 24 gates are two rules**, and they are the two §3.3 named from the probes:
  `Array#[] non-int index` (17) and `unmodeled method Integer#[]` (6). Both arrive the same way —
  `Array(hash)` yields `[[k, v], …]` and the code then indexes it with `"type"` — so a single
  container-shape malformation reaches both. The 24th is a timeout.

The observation is normalized twice for N38: addresses, and sorbet's `Caller:`/`Definition:` lines,
which carry the program's own temp path. The blame *outcome* is kept — §5.4 calls it a licensed
outcome, so a change to it must be visible — and `Object#hash` is never printed.

## N47 — `--timeout` never reached the SUT

R1's last gate was a timeout, on a program the model runs in 13 s. `--timeout 180` did not help,
and the reason is that it never could: `make_sut` built every SUT with `CRubyRunner()` and no
argument, so the flag bounded the **control** and left the model on the runner's own 10 s default.

The failure mode is the bad kind. A model run slower than 10 s came back `sut_unsupported` —
reported as a **gate**, indistinguishable in `difftest gates`' histogram from a construct the model
refuses — and the one knob that looks like it should fix it did nothing. Any number this repo has
quoted as a gate count could have contained slow programs; the histogram's `sut timeout` row is the
only place it was visible, and only if someone read it.

`make_sut(kind, inject_bug, timeout)` now threads the flag through, and the default is unchanged at
10 s, so no existing figure moves unless a recipe passes `--timeout`. R1's is
`--timeout 120`; with it the tier is **106 agree, 0 disagree, 0 gated**.

### What it means for the numbers, measured

Threading the flag through makes **tier 0 read 993 at `--timeout 120` and 992 at the 10 s
default**, and neither is wrong: tier 0 carries **three or four bootstraptest programs sitting on
the timeout boundary** (`test_yjit_145`, `test_yjit_30k_ifelse_001`, `test_yjit_30k_methods_001`,
`test_proc_008`), and *which* of them completes depends on machine load. Three consecutive runs of
the same binary reported 4, 4 and 3 timeouts.

So **tier 0's agreement count is ±1 and always has been**, for a reason that has nothing to do with
the model. Two consequences:

* Quote it with its timeout. `HANDOFF.md`'s recipe uses the default, so the figure there is **992**.
* **A one-case move in tier 0 is not evidence of anything** — diff the gate sets, not the counts.
  This session's real +1 was `test_yjit_190` (`Array#[]= non-int index`, closed by L134), and the
  way to know that rather than guess it is `set(gates_before) - set(gates_after)`. The same
  instruction `HANDOFF.md` gives for gate conditions applies to timeouts: read the per-case
  outcomes.

The general lesson is the one already in `HANDOFF.md` about checks that pass by producing no
output: a flag that is accepted, does nothing, and produces a plausible-looking result is worse
than one that errors.

## N48 — the five boot stubs get their upstream sigs

`homebrew/HANDOFF.md`'s "clear the cheap fragment rows", second half; L138 is the first. The
harvested corpus supplies five methods both executors run because Homebrew loads them from a boot
path the control does not have (N36, L112): `Utils::Output::Mixin#odebug`, `Object#blank?`,
`#present?`, `#presence`, and `Pathname#stem`. None carried a `sig`, so each was a `missing-sig`
row in `--fragment` — a row that says "this method's parameters and return are `T.untyped`", which
is criterion 2's exclusion. Since the stubs are copies of upstream code, and **every one of the
five is annotated upstream**, the rows were ours.

Each sig is now upstream's, verbatim and cited: `utils/output.rb:32`, `extend/blank.rb:20,26,46`,
`extend/pathname.rb:186`. Copying rather than inventing is the same discipline the stub bodies
already follow — a stub that deviates from upstream makes the model answer something the control
cannot.

**They are enforced, which is the point and also the risk.** `sorbet-runtime` is modeled (L80), so
these sigs are checked at runtime in *both* executors. Two of the four are shapes the shim had never
been asked for on this path — `T.anything` and `T.self_type` in
`sig { returns(T.nilable(T.self_type)) }` — and a probe of all five together agreed with CRuby
before the corpus was rebuilt, which is the order to do this in.

**One observable change, and it is confined.** `odebug`'s sig is `.void`, so the method now returns
`T::Private::Types::Void::VOID` instead of `nil` — in both executors, identically. N36's argument
that the stub cannot affect a comparison still holds: `odebug` is reached from one rescue path in
`in_interval_permissive?` and its value is discarded there. If a future slice program ever *uses*
the return, this is where to look.

Re-harvested (355 harvested, 4 skipped, unchanged) and re-run: slice **351 agree, 0 disagree**, 1
gated, 3 `control_invalid` — the baseline exactly. tier-4 25/0, tier-0 992/0.

## N49 — the control wrapper had no `__as_string`, so the `desugar` SUT was unrunnable

`desugar` C38 gave interpolation's cold arm a **call** — `t.__as_string` — and put the one-method
support layer in `Observe::WRAPPER`, "so both sides see it and neither can be advantaged by it."
The difftest control wrapper (`control.py:_WRAPPER`) never got the same treatment. It is the thing
that runs *both* the control program and the `desugar` SUT's rendered core, and it defined no
`__as_string`, so every rendered program whose interpolation took the non-String arm died with
`NoMethodError: undefined method '__as_string'`. One line reproduces it:

```
puts "x#{1}"
control: stdout 'x1\n'    sut: NoMethodError undefined method '__as_string' for an instance of Integer
```

The failure mode is the bad kind, for the same reason N47's was. It presents as a **DISAGREE**, not
as a harness error — the engine's loudest possible verdict, pointing at the desugarer. A tier-1.5
campaign came back 58 disagreements in 108 cases and auto-filed a 300-line "minimized reproducer"
against a front end that was not wrong about anything. Only the *interpolation-of-a-String* cases
agreed, which is why the failure looked data-dependent rather than structural.

`_WRAPPER` now prepends `_SUPPORT`, a verbatim copy of `Observe::SUPPORT`. Placement follows the
existing rule (N36, L112): shared runtime support lives in the wrapper both executors go through,
not in one side's prelude. The `lean` SUT was never affected — the model's own prelude defines
`__as_string` — which is why the recent report directories are all `-lean` and this sat unnoticed.

After the fix, `desugar`: tier 0 **1232 agree, 0 disagree** (71 gated, 5 `control_invalid`, 1
`harness_error`), tier 1 500/0, tier 1.5 300/0, tier 3 68/0 (2 gated), tier 4 28/0.

**Two things this run turned up and did not fix.**

- `--inject-bug` **does not detect anything on tier 1**, which is the command the README documents
  as the engine's end-to-end detection self-test. The flag is plumbed correctly and the SUT really
  does double-evaluate (`t(nil) && 5` prints its marker twice), but tier-1's `&&`/`||` operands are
  effect-free — `(x && [ix0, x, ix0])`, `(nil && m1())` — so the second evaluation is unobservable:
  300/300 agree. On **tier 1.5**, whose operands are `__t(…)` probes, it fires immediately (97
  disagreements). The self-test recipe should be `--tier 1.5 --inject-bug`.
- `corpus/regressions/sorbet-hash-gate.rb` disagrees under `desugar` only in a line number:
  `Caller: <program>:40` vs `:18`. `render_core` emits one line, so every sorbet-runtime message
  that embeds a source location differs by construction. `_scrub_program_path` quotients out the
  harness's own temp path for exactly this reason; whether to extend it to line numbers is a real
  oracle-weakening decision (it would hide a genuine "raised from the wrong place") and is left open.
