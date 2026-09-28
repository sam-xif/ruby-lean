# Lean model — hand-off

## Active conformance goal (2026-09-28, L281)

The user wants known semantics issues fixed first, then progress toward full
CRuby bootstrap conformance. Proof repair is explicitly deferred. The goal
remains active and incomplete. L276–L281 changes are uncommitted; checker/proof
files and ratchet floors remain untouched. Existing unrelated paper/ and wasm
upstream-bug files remain untouched. All validation processes have terminated.

L281 fixes the known eager-namespace discrepancy: plain `class T; end` now works.
Core boot registers optional programs from prelude/features/*.rb; native require
executes them in a fresh main/Object top-level frame. Interp/Require.lean,
requireK and Machine loading/completed/attempted feature lists model cache,
reentry, failure with preserved effects, retry and completed dependencies.
Feature state stays shared across Enumerator contexts. Pathname stays core:
CRuby 4.0.5 boots pathname.so even without gems; pathname.rb is a cached wrapper.
The old, nonexistent Pathname#to_str was removed.

Runtime library source origin is carried by Frame/Closure.libraryOrigin and
MethodDef.fromPrelude, independently of boot-only preludeMode. Optional bodies
must not silently suppress user callbacks. The smaller Forwardable body exposed
a callback-order mismatch; require with user definition hooks now explicitly
gates. require-definition-hooks.rb records this new open boundary. Full library
source and ordinary alias/singleton-definition callback fidelity remain work.

JSON installs its real generator mixin hierarchy. Standalone CLI boots core only;
LeanSUT passes --preload-json to match the existing control wrapper. Trace/fuel
flags compose in either order. Generated optional API inventories come from
isolated oracle subprocesses (scripts/cruby_feature_names.rb). ClassPayload's
libraryNamespace tag follows canonical library paths independently of Ruby
names, including pre-existing aliased modules. Missing library/dependency APIs
and loader globals gate rather than produce false negative reflection answers.

The scope audit also repaired const_get/const_defined?: inherit=false now limits
lookup to the receiver, modules fall back to Object when inheritance is enabled,
arity is checked, and root NameErrors omit the spurious Object:: prefix. User
const_missing hooks/scoped-string names remain explicit gates.

Final build PASS (92 jobs). Bootstrap: **1,081 agree / zero disagree /
222 unsupported**, five invalid controls and old test_syntax_115 harness error.
Every source/verdict is unchanged from L280. Regressions: **85 held / two gated /
zero failures** (87 total); all old sources/verdicts unchanged. Tier 1 n=300
seed20260927: **219 agree / 81 unsupported / zero disagree**, unchanged.
Final reports: difftest/reports/20260928-012417-{tier0,tier1,tierregressions}-lean/.

Eight new fixed programs: require-{lazy-namespaces,user-class,cache,top-level,
reopen-module,library-behavior,json-ancestry} and constant-reflection-scope.
One new open/gated program: require-definition-hooks. Focused replay: 60 cases,
40 agree / 20 explicit gates / zero disagree, including all 28 Sorbet cases
(25 agree / three old gates). Three standalone core-only programs agree.
`python3 ruby-lean/scripts/check-feature-loading.py` compares identical source
bodies under actual CRuby require and a test-only Lean registration entry point:
exception/reentry/scope/cache, throw/ensure, and surviving completed dependencies
all agree. This does not add a production filesystem loader.

Front-end: 45 seeds plus nine new programs, **54 agree / zero disagree**,
AST-idempotent, six old render-only instabilities. Both generated files match
regeneration; CLI flag ordering and git diff --check pass. No proof build,
typed gate or commit attempted. Temporary focused/standalone evidence lives in
/private/tmp/conformance-l281-{focused,standalone}.{py,json}; full records and
reproduction commands are in implementation-notes L281 and difftest N55.

Next work, preserving the full objective:

1. The old sorbet-hash-gate remains open; do not invent a process-specific hash
   or weaken the comparator. The new require-definition-hooks gate requires
   callback/source fidelity, not a flag suppressing hooks. Full Sorbet runtime
   fidelity remains partial (including model-only helper/type namespaces).
2. Older known semantic leads still come first: legacy for bypasses each,
   destructureBind needs checked to_ary, and reflective alias/undef/attr/mixin
   mutation needs a frozen-state audit. File is still an old module-shaped stub.
3. Current bootstrap gates include 39 string eval, 10 TracePoint, seven block
   param shapes, six each of class_eval strings, top-level return, binding/local
   reflection and String#setbyte; five each of instance_eval strings, timeouts,
   object_id, RubyVM and top-level define_method. Historical out-of-scope labels
   do not complete the objective. Re-measure before selecting a batch.
4. Loader boundaries remain general path resolution/require_relative, custom
   feature-name conversion, loader globals, source-position conflict diagnostics,
   complete upstream bodies and missing library APIs. Current features have no
   Rational/Complex literals; future runtime compilation/retry needs fresh
   literal-site namespaces. Other L280 Enumerator and L279 numeric gates remain.

## Previous batch (2026-09-28, L280)

The user wants known semantics issues fixed first, then full CRuby bootstrap
conformance. Proof repair is explicitly deferred. The goal remains active and
incomplete. L276–L280 changes are uncommitted; checker/proof files and ratchet
floors remain untouched. Existing unrelated paper/ and wasm upstream-bug files
remain untouched. All validation processes have terminated.

L280 adds native Enumerator/Generator/Yielder payloads and resumable execution
in RubyCore/Interp/Enumerator.lean. Boot ids are Enumerator 41, Generator 42,
Yielder 43, main 44. Ctl.send queues ordinary native-to-Ruby dispatch. Execution
saves control/continuation/activation stacks, exception and missing-call context,
and active Enumerator; heap, frames, globals, output and literal cache stay shared.
A native Closure.enumYield callback suspends at the actual yield, without replay.
Internal each starts a fresh traversal; external iteration dispatches the
Enumerator's own each (including overrides), then resumes its saved context.

Next/peek/value variants/feed, hidden StopIteration results, size callbacks,
restart after errors, nested iterators and checked rewind are modeled. Rewind
uses the existing checked-call protocol (response hooks/method_missing), then
abandons the fiber without running ensure. Native Hash insertion locks also
remain after abandonment, even after CRuby GC: Machine.abandonedHashIterations
retains them. Normal completion/break/exception release live locks. Hash cursors
skip deleted entries and reread values; Array each/each_index/map use live cursors;
Integer.times advances without eagerly allocating List.range.

String#scan yields incrementally with captures, zero-width advance and match
slots. Frame.matchAlias preserves native external root sharing when first resumed
at top level; first resume from an ordinary method gets an isolated slot. Heap
writes increment Object.revision; scan gates receiver writes during suspension
(including reverted writes/ivars) and high-byte binary Strings. Generator/Yielder
and Class#new/allocate use native payloads plus ordinary initialize dispatch.
Module.new's native constructor arm was missing and is now supplied.

The prelude has Kernel#loop, Enumerable inclusion and Chain block operations.
Uninitialized Chain checks are covered. Native Kernel#itself and super's missing/
shadow-native checks fix the newly reached test_yjit_152 closure/method duality.
Namespace constant inventories in CRubyNames prevent new core classes from
turning unmodeled nested constants into false NameErrors/reflection negatives.

Final build PASS (90 jobs). Bootstrap: **1,081 agree / zero disagree /
222 unsupported**, five invalid controls and the old test_syntax_115 harness
error. **+33 agreements over L279, no losses**, all sources unchanged. Regressions:
**77 held / one old gated / zero failures** (78 total). Tier 1 n=300 seed20260927:
**219 agree / 81 unsupported / zero disagree**, unchanged sources/verdicts.
Final reports: `difftest/reports/20260928-005837-{tier0,tier1,tierregressions}-lean/`.

Nine new regression programs: enumerator-{allocation,context,dispatch,external,
internal,mutation,rewind,scan-chain} and kernel-itself-super. Final focused replay:
41 agree / one string-class_eval gate over 42 cases. Deterministic seed20260928
probe: 166 agree / eight explicit gates / zero disagree over 174 fragments
(including 150 action sequences). Saved scripts/results:
/private/tmp/conformance-l280-{focused,generated,super}.{py,json}.
Front-end: 45 seeds plus nine new programs, **54 agree / zero disagree**,
AST-idempotent, six old render-only instabilities. Both generated files match
regeneration; git diff --check passes. No proof build/typed gate/commit attempted.

Next work, preserving the full objective:

1. The old sorbet-hash-gate remains open. Do not invent a process identity hash
   or weaken the comparator. Another verified loading discrepancy: `class T; end`
   works in plain CRuby but raises TypeError in the model because the prelude
   eagerly installs Sorbet's T module without require. Lazy feature loading is
   needed; the control's JSON ancestry pollution remains a separate issue.
2. Re-measure current gates before selecting the next group. String eval,
   optional/keyword/destructuring block parameters, top-level return, binding,
   String#setbyte, forwarding, const_missing and runtime reflection remain work.
   Historical out-of-scope labels do not complete the user's objective.
3. Enumerator gates remain: custom method-name/to_int size conversions, copy
   hooks/singleton classes and clone options, reentrant resume, Chain blockless
   wrapping/rewind, other blockless prelude methods, scan receiver mutation and
   public Fiber APIs. CRuby 4.0.5's Chain.each wrapping has a surprising TypeError
   on size; do not guess a simpler descriptor. test_yjit_307 remains a resource
   limit around a million-element argument list, not an agreement.
4. Older audit leads remain: legacy for bypasses each dispatch, destructureBind
   needs checked to_ary, and reflective alias/undef/attr/mixin mutation needs a
   frozen-state audit. Numeric constructor/component-operation gates from L279
   remain. Future runtime compilation needs fresh literal-site namespaces.

## Previous batch (2026-09-28, L279)

The user wants known semantics issues fixed first, then full CRuby bootstrap
conformance. Proof repair is explicitly deferred. The goal remains active and
incomplete. L276–L279 changes are uncommitted; no checker/proof files or ratchet
floors were changed. Existing unrelated paper/ and wasm upstream-bug files remain
untouched. All validation processes have terminated.

L279 adds native frozen Complex values, exact/signed-zero imaginary literals,
numeric constructors, arithmetic, coercion/equality and representation. New files:
RubyCore/Complex.lean and Builtins/Complex.lean. Boot.complexId is 40; mainId is 41.
The literal cache is now Machine.numericLiterals, shared by Rational and Complex,
with the existing separate program/prelude site namespaces. Export's additive
imag head transports Float components as flt_bits; a JSON number loses -0.0.
C40 explains the front-end changes. Prelude defines Complex.rect/rectangular,
undefined new/allocate, Kernel.Complex and a __coerce_quo twin. The name inventory
and generated prelude match regeneration.

Complex construction must preserve CRuby's exact-zero versus Float-zero rules;
Complex(c) preserves identity, but not every two-argument zero case does. Division
uses scalar ratio-based operations in the observed order, preserving intermediate
rounding and applicable Rational-to-Integer canonicalization. Coerced Complex
#/ dispatches quo. Moving master complex.c differs from the installed CRuby 4.0.5
in constructor details; trust the executable probes.

The allocator test also repaired method reflection: an actual undefined/private
method-table entry decides respond_to?/method_defined?; CRuby shadow/mixin names
are consulted only on a lookup miss. Six new fixed regression programs cover the
Complex rules and this visibility repair. Pure comparisons involving an overridden
Complex/component equality or hash method conservatively gate, including collection
operations and hash literals. Repr gates component to_s/inspect/to_str overrides.
Rational#coerce of Complex gates: CRuby can produce a nested Rational numerator,
outside the normalized integer-numerator payload.

Final build PASS (88 jobs). Bootstrap: **1,048 agree / 0 disagree / 255 unsupported**,
five invalid controls and the existing test_syntax_115 harness error (1,309 total).
Exactly 22 new agreements over L278, no losses: test_literal_suffix_021–042.
Regressions: **68 held / zero failures / one old gated** (69 total). Tier 1 n=300
seed20260927: **219 agree / 81 unsupported / zero disagree**, with all sources and
verdicts unchanged. Final reports:
`difftest/reports/20260928-002138-{tier0,tier1,tierregressions}-lean/`.

Targeted generated probe: 244 agree / 23 explicit gates / zero disagree across
267 fragments (seed20260928); /private/tmp/conformance-l279-generated.json and
conformance-l279-generated.py. Twelve more mixed large-divisor cases agree; ten
hook/coercion boundary cases explicitly gate, in
/private/tmp/conformance-l279-boundaries.json. Front-end: 45 seeds plus six new
programs, 51/0, AST-idempotent; full bootstrap 1,232 agree / zero disagree / 77
gates, no harness errors. Six seed and 27 bootstrap render-only instabilities are
unchanged. git diff --check passes. No proof build or typed gate was attempted;
no commit was made.

Next work:

1. The sole old open regression remains sorbet-hash-gate. Its source scrubs the
   gem's process-specific hash, but the shim gates before producing the message.
   Do not invent a matching CRuby identity hash or weaken comparison.
2. **Enumerators** are a large next group: 22 blockless Integer.times gates plus
   five enum_for gates. Native iterator selection is in Interp/Dispatch.lean;
   most other blockless iteration gates live in prelude/prelude.rb. Model receiver/
   method/arguments and continuation/resume behavior, not just test outputs.
3. Other groups: 50 string eval variants; seven optional/keyword/destructuring
   block-parameter cases; six top-level returns; six String#setbyte; five itself.
   Historical out-of-scope labels do not finish this active objective.
4. Numeric limits remain explicit: string/custom/keyword construction, remaining
   Numeric/Complex methods, nonfinite Complex arithmetic, effectful component
   operations/representation, Rational#coerce of Complex, and clone options.
   Future runtime compilation must supply fresh numeric-literal namespaces.
5. Earlier audit leads remain: legacy for bypasses each dispatch; destructureBind
   needs checked to_ary; reflective aliases/undef/attr/mixins need a frozen-state
   audit. Requiring json in the control adds a module to Object.ancestors that
   the standalone model lacks; complete wrapper ancestry equivalence is unresolved.

## Previous conformance batch (2026-09-28, L278)

The user wants known semantics issues fixed first, then full CRuby bootstrap
conformance. Proof repair is explicitly deferred. The goal remains active and is
not complete. L276–L278 changes remain uncommitted; no checker/proof files or
ratchet floors were changed. The existing untracked paper/ and wasm upstream-bug
files were left alone. All validation processes have terminated.

L278 adds exact native Rational literals and a frozen normalized payload,
numeric constructors, arithmetic, coercion/equality, rounding and Float conversion.
Literal identity is cached by compilation unit/site; distinct sites remain distinct.
C39 documents the front-end head/render/export changes. Rational.lean and
Builtins/Rationals.lean carry the numeric rules. Boot.rationalId is 39; mainId is
now 40. Native `1 / rational` bypasses coerce. Rational.new/allocate are undefined
in the prelude, and class allocation interception now honors actual new lookup.
The CRuby name generator now preserves its curated stdlib constants list.

Rational.to_f follows the **64-bit CRuby** Fixnum/Bignum conversion paths, including
intermediate rounding. Do not replace it with just exactFractionFloat: the pinned
large-fraction witness differs by one ulp. See the L278 implementation record.
Frozen method definitions were also repaired: direct singleton def, def inside a
singleton-class body, and define_singleton_method reject a frozen attached object.
New eigenclasses inherit freezing; freeze propagates to an existing eigenclass.
Other reflective mutation paths still need a frozen-state audit.

Final executable build PASS (84 jobs). Bootstrap: **1,026 agree / 0 disagree /
277 unsupported**, five invalid controls and the existing test_syntax_115 harness
error (1,309 total). Exactly 22 new agreements over L277, no losses:
test_literal_146, test_literal_suffix_001–020 and 045. Regression status tier:
**62 held / zero failures / one gated** (63 total). Tier 1 n=300 seed20260927:
219 agree / 81 unsupported / zero disagree; same sources/verdicts as L277.
Final reports: `difftest/reports/20260928-000430-{tier0,tier1,tierregressions}-lean/`.
Five new rational regressions pass. An additional seed-20260928 probe agrees on
150 Float conversions and 80 exact arithmetic fragments; source/results:
/private/tmp/conformance-l278-generated-numerics-final.json.
Frontend: 44 seeds + five rational programs round-trip (49/0), AST-idempotent.
Full front-end bootstrap had 1,231 agreements, zero disagreements, 77 gates and
one transient source no-observation in test_load_002; that unchanged case passed
an isolated rerun. Generated prelude matches regeneration; git diff --check passes.
No proof rebuild or typed gate was attempted, and no commit was made.

Next work:

1. The sole old open regression is still sorbet-hash-gate. Its source scrubs the
   process-specific gem hash, but the shim refuses before emitting the message.
   Do not invent a matching CRuby identity hash or weaken comparison.
2. **Complex: 22 current bootstrap gates.** Native imaginary literals still lower
   through an overridable Complex call. Fix literal construction, exact Rational
   components and identity together; C39/Rational are a starting point. Then
   Enumerators (22 blockless times + five enum_for) are another large group.
3. Other large groups: 50 string eval variants; seven optional/keyword/destructuring
   block params; six top-level returns; six String#setbyte; five Object#itself.
   Historical "out of scope" labels below do not finish the user's new objective.
4. Rational's remaining explicit gates include string/custom/non-finite/keyword
   constructor conversion, digit-precision rounding, non-Integer powers, fdiv and
   other Numeric methods, clone options, and effectful component repr. Runtime
   compilation, when added, needs fresh literal-unit namespaces.
5. L277's legacy for path still bypasses ordinary each dispatch; destructureBind
   still needs an audit for effectful to_ary. Frozen aliases/undef/attr/mixin paths
   also deserve an audit; L278 only claims the method-definition paths it tests.
6. A separate control-environment issue was observed: requiring json in the
   wrapper adds JSON::Ext::Generator::GeneratorMethods::Object to Object.ancestors,
   unlike the standalone model. The Rational test asserts its three relevant
   ancestors; full wrapper/model ancestry equivalence remains unresolved. No
   comparator or wrapper change was used to conceal that difference.


## Previous conformance batch (2026-09-27, L277)

Previous goal turns made verified progress. The user wants the known semantics
issues addressed first, then full CRuby bootstrap conformance; proof repair is
explicitly deferred. The goal remains active. Changes from L276/L277 are uncommitted.
No checker/proof files or ratchet floors were changed. Existing unrelated untracked
paper/ and wasm upstream-bug files remain untouched.

L277 closes to-ary-gates and impure-repr-gates. Splat and lenient block-argument
conversion now suspend for checked to_a/to_ary. Hash#to_a has native pair allocation.
Redo retains the existing block activation and its local/parameter writes. Frozen
errors render via Interp/Frozen.lean, including class.to_s, inspect, result.to_s and
recursive-inspection protection. Obs.observe runs the reference wrapper's final
inspect and exception class/name/message sends, preserving stdout and captured heap.
Main supplies the observation fuel. See the complete L277 implementation record.

Executable build PASS; final regression-status tier PASS: 57 agree / 0 disagree /
1 unsupported (58 total), all 57 fixed statuses held. Tier 1, n=300, seed 20260927:
219 agree / 0 disagree / 81 unsupported; all 300 sources and verdicts match L276.
Reports: `difftest/reports/20260927-234449-{tierregressions,tier1}-lean/`.
Final bootstrap: 1,004 agree / 0 disagree / 299 unsupported, five invalid controls
and the existing test_syntax_115 harness error (1,309 total). Report:
`difftest/reports/20260927-234449-tier0-lean/`. Four new agreements, no lost ones:
test_method_216, test_yjit_294 (splat); test_yjit_237/242 (frozen Struct setters).
All checks terminated. git diff --check passes. Prelude comments were updated and
the regenerated artifact is byte-identical. No proof rebuild/typed gate was attempted.

Next work:

1. The sole open regression is sorbet-hash-gate. Its Ruby source explicitly scrubs
   the gem's process-specific object hash, but the model's Sorbet shim gates before
   supplying the message. Do not invent a matching CRuby hash or weaken the comparator.
   A faithful treatment of identity hashes/observable nondeterminism is still needed.
2. Continue the full bootstrap objective. Its largest semantic groups beyond eval
   are Rational/Complex (43 cases, primarily exact literals and class queries) and
   Enumerators (22 blockless times, plus enum_for). Final observation can now dispatch
   custom numeric repr. Numeric literals need exact values and native construction
   semantics; do not merely special-case the literal test outputs.
3. Optional/keyword/destructuring block params still gate (seven bootstrap cases).
   The new separation between conversion and enterClosure can support full binding;
   preserve the distinct lambda/proc and checked-conversion protocols.
4. The legacy `for` path still enumerates Array payloads / integer Range endpoints;
   it does not yet use normal each dispatch. Pure destructureBind is another place
   to audit for effectful to_ary. These were not silently declared fixed by L277.
5. The historical eval/TracePoint/VM/etc exclusions below are remaining work under
   the user's new objective, not evidence of full conformance. Re-measure current
   reports before selecting the next cases.


## Previous batch (2026-09-27, L276)

The user asked to fix open semantics regressions first, then drive toward full
CRuby bootstrap conformance; proof repair is explicitly deferred. The goal remains
active. Worktree changes are uncommitted (the typed gate must pass before a commit).
Existing untracked paper/ and wasm upstream-bug files were left alone.

L276 fixes all three live regression disagreements: delayed singleton-class naming,
String#+ implicit to_str conversion through method_missing, and super in a custom
method_missing. See the latest implementation-notes entry. The conversion state
machine now serves both to_proc and to_str. Machine.missingReason mirrors CRuby's
execution-context reason, including nested-call overwrites. ClassPayload.attached
makes singleton-class rendering use the current heap. No checker/proof files changed.

Verified executable build and full regression tier: 47 agree / 0 disagree /
3 unsupported (50 total), no status failures. Tier 1, n=300, seed 20260927:
219 agree / 0 disagree / 81 unsupported. L275 block-pass guards now have fixed
sidecars; new guards cover string conversion and method-missing dispatch. Reports:
`difftest/reports/20260927-233122-{tier1,tierregressions}-lean/`.
Final full bootstrap: 1,000 agree / 0 disagree / 303 unsupported, five invalid
controls and the existing test_syntax_115 harness error. Report:
`difftest/reports/20260927-233122-tier0-lean/`. Only test_method_211 changed verdict
(unsupported → agree); no prior agreement was lost. All test processes terminated.
No proof rebuild or typed gate was attempted; the executable alone was rebuilt.

Next work, preserving the full objective:

1. Three open regression programs still gate; a gate is not a fix. The semantics
   gaps are impure-repr-gates.rb (frozen-error receiver inspect and final-result
   inspect; uncaught custom exception messages are a related commented witness),
   and to-ary-gates.rb (effectful to_a for splat and to_ary during block binding).
   The third, sorbet-hash-gate.rb, names an object's process-specific hash in a gem
   error message. Do not silently weaken the comparator to call it agreement.
2. The shared checked-conversion continuation in Interp/BlockPass is a starting
   point for splat/binding conversions, but their nil handling and resume operations
   differ from both to_proc and strict String conversion. Preserve those protocols.
3. Obs.observe still purely calls inspectP and gates custom final inspect/message.
   Main runs observe after Interp.run; an effectful observation needs real sends on
   the completed machine, matching difftest/control.py's wrapper and its exception
   and stdout order. Frozen-error rendering separately needs a suspended builtin.
4. Re-measure bootstrap gates from the current report. The preceding full run's
   largest groups: 50 string eval variants, Rational 25, Complex 18, blockless
   times/Enumerator 22 (+ enum_for 5), optional/keyword block parameters 7,
   top-level return 6, String#setbyte 6. Historical out-of-scope labels are not
   completion of the user's new full-conformance objective. Old summaries below
   this section remain historical.


## Current block conversion repair (2026-09-26, L275)

`&e` now dispatches to_proc after evaluating the call's receiver/arguments/keywords.
Proc/nil bypass lookup; defined methods (including private ones) precede response hooks.
Missing conversion follows checked method_missing handling and validates the Proc result.
The old Symbol-only allocator bypass is removed (§F56). Native Symbol#to_proc retains its
capture-free closure. Interp/BlockPass and KontFrameBlockPass contain the protocol/proofs.
Two regression files cover conversion effects, response hooks, mutation and exits.
MRI tier 0: 999 agree / 0 disagree (+1), 304 unsupported, five invalid controls and
the existing harness error. Full regressions: 42 agree, three unchanged dfa5116 disagreements,
three unsupported. test_method_217 now agrees (nested calls during to_proc).
Full quiet ratchet GREEN (94 fragment, 254 agree / 0 disagree); metatheory and
standard-axiom audit PASS. No live builds. Logs: /private/tmp/ratchet-blockpass-*.log.
Rung 096 typing still needs native capture-free required/rest closure entry; do not reuse
literal-block capture/one-required-parameter facts for this different path.


## Current map repair (2026-09-26, L274)

Array#map/collect now resolve native markers through ordinary lookup, with a live
IterKind.arrayMap cursor and result accumulator. Previously the prelude's Enumerable
implementation incorrectly dispatched an overridden each (§F54). The snapshot native
fallback is removed. Regression array-map-native.rb covers dispatch, mutation and exits.
The checker admits attached each (clink 227); map typing is next and needs native dispatch
readiness, accumulator transport and final Array allocation in addition to each's caller
restoration. It must prove this reached path, not the old miss fallback.
Validation: focused replay 3/3; MRI tier 0 unchanged at 998 agree / 0 disagree;
full quiet ratchet GREEN (252/0); metatheory and standard-axiom audit pass.

## Current iterator repair (2026-09-26, L273)

Array#each now uses IterKind.arrayEach arrayId index, rereading the live array payload
and length after every yield. The old entry-time snapshot missed append and retained
removed/replaced elements (ratchet §F53). Existing block continuations retain all exit
behavior; native iteration bypasses length/[] overrides. Regression: array-each-live.rb.
Other native iterator families were unchanged in L273. Clink 227 subsequently admitted
attached each blocks using the all-fuel loop contract and two-activation caller framing.
Validation: focused replay 2/2; MRI tier 0 remains 998 agree / 0 disagree (same 305
unsupported, 5 invalid controls, 1 existing harness error); full quiet ratchet GREEN
(252 agree / 0 disagree); metatheory and standard-axiom audit pass.

## Current dispatch repair (2026-09-26, L272)

Proc call/[]/yield/=== now resolve native markers through ordinary lookup, preserving
user overrides, aliases, visibility, undef and super. Tombstones cannot reach native
fallbacks. See ratchet found-issues §F51. The newly reachable equality cases exposed §F52:
Object/true/false/nil === now test identity before dispatching ==; other scalar === aliases
retain their original equality implementation. Both families have regression files in
`difftest/corpus/regressions/`. Prelude.lean is regenerated. The checker’s closure pilot
uses explicit native dispatch facts; general callable admission remains work in progress.

Validation: tier 0 is 998 agree / 0 disagree, with 305 unsupported, 5 invalid controls
and the existing test_syntax_115 harness error. Focused replay 5/5; full quiet ratchet
GREEN (252 agree / 0 disagree); metatheory and standard-axiom audit pass.

> ## ⚠️ CURRENT STATE (2026-08-03) — read this block, then skip to §"Open threads"
>
> Everything dated earlier in this file (and the 2026-07-30 banner it replaces) is
> **historical**; numbers below are the measured current ones.
>
> - **`--sut lean` is GREEN. Tier-0 baseline: 940/1304 agree, 0 disagree**
>   (722 → 940 in the 2026-08-03 batch). Tier-1 fuzzing (n=400, seed 7) 371 agree /
>   0 disagree; tier-3 and regression replays clean. Concolic suite 28/28. All ten
>   `Proof/` files build, axiom-clean.
> - **What landed (see `implementation-notes.md` L62–L73):**
>   - **A prelude** — the core library written *in RubyCore* (`prelude/prelude.rb`,
>     generated into `RubyCore/Prelude.lean`, loaded by a two-phase boot). Enumerable
>     (~36 methods), Comparable, `Range#each` (Range is now a full collection), Hash's
>     Enumerable overrides, `BasicObject#!=`. **This is the mechanism to reach for
>     when a builtin is missing**: a few lines of Ruby, not a new `IterKind`.
>   - **Reflective metaprogramming** — `define_method`, the `*_eval`/`*_exec` block
>     forms, `prepend`, `alias_method`, `singleton_class`, ivar/const reflection,
>     `Class.new`.
>   - **`defined?`** (the old largest gate), **class variables**, `Array#[]`/
>     `String#[]` slices, **`catch`/`throw`**, `redo` in a block, **payload-core
>     subclassing** (`class MyString < String`), full `zsuper` param shapes,
>     **visibility** (`private`/`protected`/`public`, enforced at dispatch),
>     `Kernel`/`Numeric` in the ancestor chain (so `ancestors` is byte-exact).
> - **Top remaining tier-0 gates** (356 total): string `eval` family (48,
>   permanently out of scope), `Rational`/`Complex` (43), blockless `Integer#times`
>   i.e. `Enumerator` (22), `Regexp` (20), `Struct` (16), dynamic keyword keys (14),
>   `TracePoint`/`File`/`RubyVM` (22, out of scope). Re-measure rather than trust
>   this: `difftest run --tier 0 --sut lean`, then read `reports/<latest>/cases.jsonl`.
> - **The next structural lever is *dispatching repr*, not more builtins.**
>   `Struct` and `Rational` are both blocked on the same thing: their `inspect`/`==`
>   cannot live in the prelude because defining those names flips the global
>   `reprPure` flag (L7) and every `puts` in every program would gate. Making
>   `p`/`puts`/interpolation dispatch `to_s`/`inspect` (moving them into the prelude
>   over a printing primitive) retires that flag and unlocks ~59 cases plus every
>   user class with a custom `to_s`. See `../docs/model/fragment.md` §Fragment.
> - **Two traps to know before touching the step function** (L73): a `partial def`
>   or a `String.endsWith`/`startsWith` on the dispatch path is **not
>   kernel-reducible** and silently breaks every `Proof/` file while the difftest
>   ratchet stays green. Dispatch on literal-list membership instead, and build the
>   proofs (`lake build RubyCore.Proof.T5Loop …`) as part of a batch.

Fresh-context hand-off for the Lean interpreter work begun 2026-07-07 (mirrors
Read `README.md` first for layout/build;
`implementation-notes.md` (L1–L12) for revertable decisions; this file for
state, the coverage assessment, and what happens next.

## State

Built and green: the L0 slice of `../docs/semantics/lean-model-sketch.md` §3–4
runs as a difftest SUT (`--sut lean`). Pipeline: Ruby source → desugar
(`../desugar/`) → RubyCore JSON (`lib/export.rb`, versioned) →
`rubycore` binary → Observation JSON. Two fragment gates compose (desugar's
and the model's); binary exit 3 = Unsupported, exit 1 = model bug
(`MODEL-BUG:` prefix in the engine — never silently absorbed).

Corpus status at hand-off, all with **0 disagreements**:
- **tier 0 (full bootstraptest): 372/1304 agree** (up from 295 after L1
  blocks; rest gate at desugar/model, 7 control-invalid, 1 pre-existing
  control-side harness error `test_syntax_115`)
- tier 1 fuzzing (n=300, seed 11): 214 agree / 86 unsupported
- regression + tier-3 replay: clean (incl. `blocks-jumps/000`)

**L1 (blocks/procs/lambdas) is now implemented in the executable stepper**
(export v3; `impl-notes L16`): literal blocks + `yield`, `block_given?`,
`&blk` capture, block-pass `&e`/`&:sym`, `proc`/`lambda`/`->`/`Proc.new`,
`Proc#call`, and non-local control (`next`/`break`/`return`) with the
proc-vs-lambda `return` distinction and shared-scope locals — all validated
above. The `Step` relation/proofs were **not** touched (still the L0
control-core PoC). Builtins that *yield* (`Array#each`/`map`, `times`,
`Hash.new{}`) stay `Unsupported` — a pure builtin cannot push a block frame.

Bugs already caught and fixed by the loop (each was a real semantics error):
`$!` visibility during ensure-of-unmatched-region; unmodeled `String#getbyte`
shadowing a toplevel `def getbyte`; missing rest-param binding; zero-arg
builtins silently ignoring args; coercion/comparison error messages using
class name where CRuby uses inspect for special constants — and the mirror
image on `String#<` (inspect where CRuby uses class name for non-special
operands, mix-00579). Fuzzing found the last two; minimized reproducers are
committed in `../difftest/corpus/regressions/`. The lesson generalizes: one
operand-description rule (`coerceDesc`) governs all coerced/comparison
messages — special constants by inspect, everything else by class name.

## Coverage assessment (what "L0" cashes out as)

**By node head** — most RubyCore heads evaluate:
- Handled: `int flt str sym true false nil self const casgn send if while def
  array hash splat return break next retry begin seq`, `var`/`vasgn` for
  local/ivar/gvar, and (L1) `block yield blockpass` + `&blk` capture params.
- Gated: `class module sclass defs super zsuper` (L2), `cvar`.

**Partial gates inside handled heads:** hash-splat and anonymous-splat
operands; Float *rendering* (arithmetic works — Ruby needs shortest-roundtrip
output, Lean's `Float.toString` is `%f`-style); the vcall/fcall NameError
ambiguity (RubyCore conflates them, their error classes differ); and the
builtin library surface itself — a slice of each core class.

**By throughput:** of the bootstraptest cases that survive the desugar, the
model now fully executes 372 (up from 295 after L1 blocks). The model-side
gates break down roughly: class/module/singleton definitions (L2), unmodeled
methods/constants, iterating builtins that yield, tail of specific builtins
(`Array#[]` slices, Float
formatting, `Rational`/`Complex` constructors, …).

**The load-bearing fidelity mechanism** (understand this before growing the
fragment): a partial model must know what it *doesn't* implement.
`RubyCore/CRubyNames.lean` — generated from the pinned oracle by
`scripts/gen_cruby_names.rb` — holds per-class method/singleton name sets and
toplevel constants. Dispatch uses it to (a) gate when an unmodeled CRuby
builtin would shadow a resolved method, (b) gate exists-but-unmodeled misses,
(c) raise byte-exact `NoMethodError` only on genuine total misses. The
companion `reprPure` flag gates pure-repr consumers (`puts`, `p`, `String()`,
container `inspect`) once a user `def` shadows a repr-sensitive method. These
two policies are why partial coverage yields `Unsupported` rather than silent
disagreement — preserve them as the fragment grows.

## Next steps for the semantics (in intended order)

1. **Desugar M2 (params + `yield`) — upstream, biggest lever.** 544/1304
   cases never reach Lean. Plan already written:
   the desugarer's M2 params+yield batch, since landed (migrate the flat
   `[String]` param slot to structured param nodes). The Lean `parseParams`
   ("*"-prefix convention) must migrate in lockstep — the export is
   versioned (`Export::VERSION`), so bump it when the shape changes.
2. **L1: blocks + `yield` + proc/lambda jumps — DONE** (`impl-notes L16`;
   executable stepper only, `Step` untouched). The sketch's §1.1/§1.2 payoff
   realized: generative jump targets = frame identity, `captured` chains in the
   frame store, targeted `retJ`. Remaining L1 tails (opportunistic): block
   frames for iterating *builtins* (`Array#each`/`map`, `times`) — needs a way
   for a builtin to request a block-frame push (or model them as RubyCore
   methods); `redo`; multi-arg `Symbol#to_proc` edge cases; `Proc#curry`/
   `arity`/`===` (currently gate).
3. **L2: object-model definition forms** (`class`/`module`/`sclass`/`defs`,
   `super`, eigenclasses) — ~171 gated cases. Classes as ordinary heap
   objects is already the heap's shape; these heads are "push a class-body
   frame with fresh cref/self + heap mutation". Includes migrating const
   lookup off the flat-Object namespace (artifact 03's two-phase rule).
4. **`inductive Step` + metatheory** — the definition of record
   (PROJECT_PLAN §7). Author it against `stepFn` (the helpers are
   deliberately non-mutual single transitions, so rule extraction is
   mechanical), then `step_deterministic` and `stepFn` soundness/completeness.
   **A proof-of-concept slice of this is now done** (`RubyCore/Proof/`, off the
   default target; `../docs/model/metatheory.md`, implementation-notes L13–L15): an
   inductive `Step` over an effect-light control-core fragment with
   `Step.sound`, `Step.complete`, `Step.adequacy` (function–relation adequacy
   on the fragment), `Step.deterministic`, and a `Step.heap_monotone`
   preservation invariant — all axiom-clean (`#print axioms` shows only
   propext/Classical.choice/Quot.sound). It validates that the
   interpreter-first design admits real theorems and that rule extraction is
   mechanical (soundness = one uniform `cases`+`simp`). Refreshed against the
   current stepper (control core now covers `redo`/`dowhile`; L13).
   **Type-safety metatheory landed** (`RubyCore/Proof/TypeSafety.lean`; L51):
   the `invariant_sound` progress/preservation theorem of
   `type-safety-by-reachability.md` §4, proved over the *full* transition
   relation `SmallStep m m' := stepFn m = .next m'` (so it applies to real
   programs — dispatch/classes/blocks — not just the control core), plus the
   Direction-A execution certificate (`run_value_type_safe`, the `q_learning`
   coverage story) and a fully-discharged Direction-B invariant demo. Remaining
   for a *relational* dispatch metatheory: extend the inductive `Step` to `send`
   (fold `invoke`/`Builtins.run` as a trusted oracle), then `return`/frames and
   `begin` — but note `invariant_sound` already does NOT need this, since it is
   formulated over `stepFn` directly.
5. **Opportunistic, any time:** Float shortest-roundtrip formatting (contained;
   unlocks ~5 tier-0 cases and all float observations); more builtins driven
   by the `Unsupported` histogram (`Rational`/`Complex` are the top names);
   the sketch §5 export cross-check (render→parse→desugar→export ≟ export) in
   the harness test suite.

Ratchet discipline carries over from the desugar: after any change, tier-0
full + tier-1 + regression replay must stay **0 disagree**, and agreement may
only go up (baseline now **940**). At batch boundaries also build the `Proof/`
files and run `../concolic` (28 tests) — the ratchet does not notice a
kernel-reducibility regression (L73).

---

## C-1 — SUPERSEDED AND DELIVERED THROUGH THE JUDGMENT LAYER (2026-08-26, same day)

> The section below is kept as written for its tactical records (the four wrong
> turns are still traps). Its *task* is done, by the re-scoping
> `docs/semantics/judgment-layer.md` argued for rather than by the `chk` port it
> describes: the invariant is stated over the inductive `Judge`
> (`RubyCore/Proof/Judgment/`, J18–J27), `judge_sound_cert` is the composed
> theorem with `hctl`'s role filled by a derivation, and `egEven` — the
> `_certified` corollary below parks on C-1 — is proved **unconditionally**
> (`Proof/Judgment/Cert.lean`, and again from a data certificate in
> `Proof/Judgment/Adequacy.lean`). The `chk_table_ret` rung was abandoned
> deliberately (judgment-layer.md §5); `chk` remains the coverage tier.

## C-1 (historical) — the one open premise of `validate_sound` (2026-08-26)

`validate` no longer calls `infer`; `#check @infer` does not elaborate from
`RubyCore.Cert.Validate`. The composed certificate theorem is
`Proof/Cert/Sound.lean`'s

```lean
validate_sound_of_ctl (h : validate c p = true) (ha : ⟦c.rowAssn⟧)
  (hctl : CtlOk (c.table p) { cls := "Object" } [] [] (Machine.init p)) :
  ∀ r, ReachableResult (Machine.init p) r → ¬ typeStuck r
```

axiom-clean, no `infer` in the statement (that is what L268's `initiation_ctl`
factoring is for). **`hctl` is the only thing open.** Closing it is C-1:
restate `CtlOk`/`KontOk` over `chk` and repair `Mono`/`Locals`/`Preservation`.
`docs/semantics/certificate-language.md` §10.5–10.6 is the design account;
`ruby-lean/RubyCore/Cert/implementation-notes.md` V9–V20 is the decision record.

### Start here, and do not re-derive these

1. **`chk.induct` exists** (V19) — `chk` and its eight helpers are one `mutual`
   block with fuel decreasing on *every* call. Do not "simplify" that back into
   the callback (`Rec`) form: a recursive call passed as a higher-order argument
   makes the induction principle underivable, and all twenty of
   `Proof/Static/Mono.lean`'s laws are `induction … using infer.induct`.
2. **The motive map is in `Proof/Cert/Mono.lean`** and cannot be read off the
   file. Motives 3/5/7 (`chkSeq`/`chkElems`/`chkArgs`) have identical types, so a
   swapped assignment *type-checks* and only the IH shapes reveal it — same for
   1/10 (`chkOpt`/`chkRecv`). Measured, twice.
3. **The immediate next task**: `chk_table_ret` is one uniform tactic away from
   green. Motives 4 and 8 (`chkPairs`/`chkKwEntries`) need their three-link IH
   chain applied *explicitly*; `simp_all` diverges there (max steps → max
   recursion → `isDefEq` heartbeats, and at 40M it does not terminate in ten
   minutes). Everything else closes.
4. **Do not build a bridge back to `infer`.** One was written and deleted: it
   makes the headline theorem depend on the function the pivot exists to retire.
   Two findings from it are kept in `Cert/Frag.lean` §5 and are load-bearing —
   `defFreeF` must be a *fragment* condition (otherwise the two checkers take
   different promotion branches and **both accept**), and a literal-block send
   needs a receiver (`infer`'s `lambda` arm ignores `ctx.selfCls`).

### Four tactical facts, each of which cost a wrong turn

* `split at h`, not `cases`, on a scrutinee that is not a hypothesis.
* A generic `VarKind`/`Option` payload blocks the head match and makes `split`
  re-open all 47 arms; split those at the *pattern*. Where the enclosing pattern
  must stay a wildcard, name the computation instead (that is `chkOpt`/`chkRecv`).
* `absurd h (by simp)` is not a finisher — it elaborates and leaves its side goal
  open, so `first` treats it as a success. Twenty-six arms failed silently that
  way. Use `simp at h; done`.
* **Macro bodies are hygienic.** An `ih`/`hr` written inside a `local macro`
  refers to a fresh `ih✝`, and the failure mode is a `first` branch that never
  fires. Three wrong turns. Pass them as parameters.

### Ratchets as of this handoff

`lake build` 94 jobs green; `scripts/check-proofs.sh` **OK**; difftest tier-0
`--sut lean` 1304 ran / **992 agree** / **0 disagree** / 306 unsupported. Note
992 exceeds the 940 baseline recorded above and this initiative added no
interpreter behaviour — the baseline line is stale, but the delta was not
attributed, so it is left as written rather than silently updated.
