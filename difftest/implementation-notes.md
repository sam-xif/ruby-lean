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
[`../docs/semantics/types-and-preservation.md`](../docs/semantics/types-and-preservation.md).
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

Design notes for the checker difftest; the Lean-side notes are `../lean/implementation-notes.md`
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
