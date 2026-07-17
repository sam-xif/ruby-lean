# difftest — implementation notes (non-critical choices, for rollback)

Same convention as the harness's `../harness/desugar-dt/implementation-choices.md`:
every non-obvious implementation choice gets a numbered entry here and this file is
committed on each change, so any decision can be found and reverted. Load-bearing
*design* decisions live in [`HANDOFF.md`](HANDOFF.md); these are the smaller calls.

## N1 — Tier 0 is repurposed as the conformance-corpus tier; bootstraptest is its first source

Tier 0 was originally sketched as "conformance suites from other languages,
AI-translated to Ruby". MRI's own `bootstraptest/` is a strictly cheaper first
occupant: already Ruby, already self-contained single-file programs, harvester
already exists (`../harness/desugar-dt/bin/harvest_bootstraptest`), no
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
(`../harness/desugar-dt/corpus/bootstraptest/`) and raises with the harvest
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
(`recv.m(...)`), plus `IvarRead` (`@x`). Scope-awareness (prong2-design §3) is
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
**scope-awareness** (prong2-design §3, so dispatch fires instead of dying on
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
