# Lean model — hand-off

## Static proof revalidation (2026-09-30)

The active ascent repaired Static/Decls dispatch simplification and corrected
iterK exact transparency for shared Hash-lock unwind. The kernel counterexample
and the new IterUnwindInert premise are in ../books/Books/Metatheory/Typing/Infer/IteratorUnwind and
../../unsoundness.md. No runtime changes; check-proofs.sh and boot/axiom probes
pass (/private/tmp/ascent-metatheory-repair.log). The active typed gate is green
at 22/99 clinks, 49/261 accepts and 254 CRuby agreements, zero disagreements
after the subsequent admissions. Final batch audit: /private/tmp/ascent-final-metatheory.log.
Earlier entries below are historical.

## Scoped run_pushK restoration (2026-09-30)

The subsequent user request was to make run_pushK pass while leaving other
proofs alone. The complete root-framing chain rebuilds against the dynamic-state
model. lake build Books.TypeSoundness.Conformance.Core.Answer passes, with the unchanged run_pushK
statement and proof and only standard Lean axioms. Log:
/private/tmp/runpushK-targeted.log. KontFrameBase separates its continuation
interface from Frame's unrelated conformance imports; Frame re-exports it.
No runtime change or broader proof repair was needed. The full typed gate is
still not claimed green. See books/notes/type-soundness/implementation-notes.md for the record.

## Dynamic continuation state (2026-09-30)

The four avoidable whole-continuation observations now use explicit dynamic
state. The user requested one commit per family and no tier 0 regressions, and
explicitly deferred failing proof repairs. Runtime validation and tier 0
preservation are the commit checks for this task. The full typed gate remains
failing; no checker, admission, comparator or testing floors changed.

- 7d5a002 — block-call lifetimes: execution-local liveBreakScopes; closure entry
  reads tokens and blockCallK expires them on return/unwind. Forwarding preserves
  identity; dead tokens invalidate break alone. Enumerator save/restore and new
  producer isolation preserve execution lifetimes.
- 6ec295f — Object inspection: execution-local objectInspections; callback guards
  include String conversion, with one entry released by objectInspectK on every
  return/unwind. The selection hook still runs before recursion detection.
- 68f6ab8 — FrozenError rendering: execution-local frozenInspections; only
  inspect/to_s phases acquire/release guards, after initialization. Earlier
  phases leave ambient guards intact.
- Hash iteration (final family): shared hashIterationLocks;
  each callback owns one entry and iterK releases one on return/unwind. Execution
  switching retains all shared locks. Rewind abandons cleanup and retains those
  entries. Nested iterations and independent producers preserve each other's
  locks. Empty/exhausted iteration acquires none.

Continuation detachment retains this dynamic state. ContextFree permits all
four marker families and excludes only catchK. hasCatcher is the sole remaining
runtime whole-continuation scan. HashLockFree is a compatibility predicate for
state preservation, now proved for every tail. The old block-scan obstruction
is retained against a named legacy helper, alongside repaired runtime controls.
The empty-catch-tags characterization of ContextFree is restored. Full framing
and type-judgement proof migration remains deferred, as requested.

Validation: lake build rubycore and scripts/probes/dynamic-contexts.lean pass.
Controls cover detached state, inert markers, normal/unwind cleanup, duplicate
counts, execution save/restore and shared abandoned locks, with standard Lean
axioms only. The RootFrame leaf and isolated catch-tag equivalence also check.
Four permanent dynamic-* regression programs preserve Ruby behavior at callback,
forwarding, recursion, ensure, suspension, isolation and abandonment boundaries.

Every family preserves all 1,309 tier 0 sources/verdicts: 1,096 agree, zero
disagree, 207 unsupported, five old invalid controls and one old harness error.
Their regression replays preserve every previous verdict. The final Hash replay
has 218 cases: 217 agree and the same old sorbet-hash gate; its new guard agrees.
The final tier 0 matches both the preceding commit and the initial baseline.
Evidence and complete per-case comparisons:
difftest/reports/20260930-dynamic-{block,inspect,frozen,hash}/.
The fresh pre-change tier 0 baseline also matches archived L299.
Unrelated proof-changes.md, paper/ and wasm upstream-bug files remain outside
these commits.

The following checkpoints are historical; their old continuation exclusions
and pending runtime proposals have been superseded by the changes above.

## Authorized proof repair checkpoint (2026-09-30)

The user authorized correcting false helper contracts while preserving public
soundness theorem statements, and requested a clear audit in the root
`proof-changes.md` **without committing that file**. The historical obstruction
below is resolved as an authorization question, not by pretending the old helper
was true. No runtime/checker behavior or gates have been weakened.

The complete Metatheory target and `./scripts/check-proofs.sh` now pass,
including the headline axiom audit and boot-heap probes. The root-execution
framing chain is complete and the legacy KontFrame import paths now re-export
that corrected helper API. Fresh class/module structural metatheory also builds.
No new trust axiom, sorry, native_decide proof, skipped target, or lowered gate
has been introduced. The constants probe explicitly loads sorbet-runtime for
its optional T rows, while the core-name probe still measures core boot.

Denote and the full typed ratchet remain RED. Boot readiness, root-run
decomposition, primitive dispatch and native ZeroDivisionError construction now
pass. The stack-only composition interface requires RootClean at entry and answer
boundaries; ContextFree still excludes block-call and inspection markers as well
as catch and Hash-iteration markers. Required-argument method entry now models
definition/super/library metadata and explicitly excludes block-defined methods
and for-loop targets. Downstream method return/body composition and ordinary-code
metadata propagation remain incomplete. Other blockers are class/module lexical
lookup, queued declaration/constructor callbacks, closure frame allocation and
capture preservation, and FrozenError's effectful initialization/inspection.

On 2026-09-30 the user authorized all changes needed to handle the main-singleton
admission bug, preserve top-level theorem statements, and continue the repair in
small commits. The eight-name top-level guard and regression controls are now
applied. Rational/Complex/Enumerator global-constant protection was already
committed. No further approval is needed for necessary metadata/helper repairs
within this task. Keep the detailed proof-changes.md audit uncommitted.

Latest logs: /private/tmp/proof-checkpoint-metatheory.log (PASS),
/private/tmp/proof-checkpoint-green-targets.log (235 jobs, PASS),
/private/tmp/proof-checkpoint-targets.log (BoundedPrimitive blocked by MethodReturn),
and /private/tmp/proof-checkpoint-gate.log (FAIL before agreement).
The user requested another checkpoint after discussing the continuation design.
This checkpoint is not completion of the repair; proof-changes.md remains
untracked and excluded from the commit.

### Design constraint for the next runtime change

The user requires decomposable continuation runs whenever Ruby semantics admit
such a model; accepting avoidable whole-continuation probes is not the preferred
repair. Catch/throw support can remain outside the typed fragment for now.

The proposed block-break repair is an explicit lifetime token: a fresh call id
stored in the closure, an execution-local set of live ids, and the existing
blockCallK boundary responsible for expiration on normal return or unwinding.
Closure entry reads the live set instead of scanning kont. A detached answer-run
inherits the live set even when the matching marker is in its omitted outer
continuation; a targeted escape is delivered to that continuation afterward.
Forwarding preserves identity; a dead token invalidates break, not an otherwise
normal Proc call. Ensure ordering and Enumerator suspension/restoration must
preserve the lifetime semantics. Prove correspondence and framing before removing
blockCallK from ContextFree's exclusions. This is a design proposal only: no
lifetime-token runtime changes are included in this checkpoint.

## Historical statement-preserving obstruction (2026-09-29)

The latest user request is to make **all proofs green without modifying theorem
statements**. This adds a constraint to the earlier repair work below. No existing
statement or runtime definition was changed in this follow-up.

`../books/Books/Metatheory/Controls/StatementObstruction.lean` proves the negation of the exact existing
`callClosure_frame` statement (copying `pushK`/`frameR` because `KontFrame` does
not compile). A closure with `breakScope := some 7` acquires that break target
when `[.blockCallK 7]` is appended before entry; appending after entry leaves its
target `none`. Lean checks the counterexample with only `propext`/`Quot.sound`.
Thus the complete request is impossible for the current semantics with every
statement fixed. The user was asked whether false helper statements may be
repaired while keeping public soundness statements; the user subsequently
authorized that repair as recorded above.

The independent `T5.dispatch_progress` proof was repaired without altering its
statement: unfold the constructor-aware resolved-shadow check and cover hidden
for-callback method entry. Targeted builds of T5, T5Loop, Demo and DriftControls
pass; dispatch_progress, dispatch_not_typestick and t5_loop_type_safe have only
standard Lean axioms. The full Metatheory build still fails in Static.Decls,
KontFrame, RootFrameBuiltins and RootFrameComplex. The full typed gate remains
red (including Books.TypeSoundness.Denotation.Ext's local-alias drift); no commit was made.

## Proof repair active against L299 (2026-09-29)

The user has now requested all type proofs and the soundness theorem green.
Work is in progress; the earlier stop request below closed conformance work,
not this new proof task. Do not start another runtime conformance increment.

Read the latest proof-repair entry in `implementation-notes.md`. Foundational
proofs and the current completion inversion are repaired. `DriftControls`
retains the false old claims, and `RootFrame` proves the three Enumerator
switching laws for a frame action that follows saved root executions. The
root-frame builtin primitives, state helpers, closures and small protocol entries
also compile. The replacement uses `ContextFree` to account for all native
whole-stack observations. Numeric and higher dispatch proofs are in progress;
remaining work includes integrating that action, transporting the new name /
alias invariants through the type proofs, and rebuilding the full soundness
chain. No full green gate, proof audit, or repair commit exists yet.

## Conformance goal — closeout at L299 (2026-09-29)

The user requested: "Close out the current task and commit, then stop."
L299 closes the current dup increment. Pause the overall conformance goal after
this commit and resume only on a new user request; full conformance is incomplete.
No Regexp implementation work is included in this increment.

L299 adds native dup argument validation and private initialize_dup/initialize_copy
dispatch. It shares core allocation with clone, drops the source's singleton
state before hook lookup and preserves the hook's final frozen state. All 42
probes agree, repairing 20 disagreements and 13 gates without losing the nine
previous agreements. Five native-dup-* guards preserve every probe, with the
Integer override isolated. L298's 67 clone/copy source/verdict pairs hold.
L276–L299 are separate increments.

Final validation (closed 2026-09-29): model build passes (104 jobs), with no
later runtime edits. Full bootstrap: 1,309 cases, 1,096 agree, zero disagree,
207 unsupported, five existing invalid controls and the old test_syntax_115
harness error. Every source/verdict matches L298. Regression replay: 213 cases,
212 agree and one old sorbet-hash gate; all 208 earlier sources/verdicts hold.
Tier 1 (300, seed 20260927): 226 agree, 74 gates, all sources/verdicts unchanged.
Frontend seeds plus new guards: 51 agree, all AST-idempotent; six old render-only
instabilities plus one benign native-dup-copies rendering instability. Standalone
and feature loading: three agreements each. Whitespace checks pass. Evidence and
before/after comparisons are archived in
`difftest/reports/20260928-incremental-L299/`. No checker, proof, comparator,
normalizer or floor changes; proof repair remains explicitly deferred.

The typed gate was rerun and remains red at HeapFacts className/lookup proof
drift; its captured error log exactly matches L298. Proof repair stays deferred.

The batch Metatheory audit also failed (NotDone/KontFrame); the axiom scan
was not reached. The captured proof-audit.log is archived.

All runtime campaigns and proof audits are terminal.

If resumed, next known failures remain Regexp literal freezing and site identity,
recorded in L298's probes/next-audit.json. Static literal sites need distinct
cache identities; runtime Regexp.new must remain mutable. Dynamic literals and
/o also need native frozen results. The frontend currently lowers literals to
Regexp.new and export.rb recognizes a constructor-shaped tree, even for manually
written constructors; preserving real literal provenance is necessary before
adding caching. Only read-only investigation has begun in those files.

Other open work: Hash#default, Array.new(array), general String#-@ interning,
permanent ASCII-name encoding, Integer#chr's ASCII encoding, namespace path
ordering/copy/removal, singleton clone, specialized native copy hooks, Random
state, const_missing and native method removal/Kernel ownership. Unrelated paper/
and wasm upstream-bug files remain untouched. Proof repair stays deferred.

## Previous batch (2026-09-28, L298)

L298 repairs native clone keyword handling and copy initialization hooks. New
Interp/Copy.lean validates options, allocates mutable core copies with ivars,
sends private initialize_clone/initialize_copy and applies final freezing after
normal return. String/Array/Hash native copy methods use checked conversion;
String rechecks frozen state afterward, Array/Hash do not. Error diagnostics
inspect unknown keys and call class to_s normally. Immutable objects reject
freeze:false; aliases/super and Enumerator options follow the native entry.

The 41-probe audit has 35 agreements and six gates: 30 disagreements and three
old gates become agreements, with two earlier agreements preserved. One prior
disagreement exposes the old Hash#default gate because its skipped hook now runs;
it is not counted as repaired. Five other existing gates remain. Extra 26:
24 agree, one old Range-subclass constructor gate and the Regexp literal-frozen
failure. Five native-clone-* programs preserve all 59 agreeing probes. All 33
L297 name probes now agree. L276–L298 are separate commits.

Final validation: model build passes (104 jobs), with no later runtime edits.
Full bootstrap: 1,309 cases, 1,096 agree, zero disagree, 207 unsupported, five
existing invalid controls and the old test_syntax_115 harness error. Every source
and verdict matches L297. Regression replay: 208 cases, 207 agree and one old
sorbet-hash gate; all 203 earlier sources/verdicts hold. Tier 1 (300, seed
20260927): 226 agree, 74 gates, every source/verdict unchanged. Frontend seeds
plus new guards: 51 agree, all AST-idempotent, six old render-only instabilities.
Standalone and feature loading: three agreements each. Whitespace checks pass.
Build logs, before/after focused probes, combined-source validation, full report
comparisons and the next audit are archived in
`difftest/reports/20260928-incremental-L298/`. No checker, proof, comparator,
normalizer or floor changes; proof repair remains explicitly deferred.

The typed gate was rerun and remains red at HeapFacts className/lookup proof
drift; its captured error log exactly matches L297. Proof repair stays deferred.

The batch Metatheory audit also failed (NotDone/KontFrame); the axiom scan
was not reached. The captured proof-audit.log is archived.

All runtime campaigns and proof audits are terminal.

Next known failures are preserved in probes/next-audit.json (script beside it):
12 cases, nine disagreements and three agreements. Six cover Regexp literal
freezing and static-site identity, including dynamic literals and /o freezing.
Three cover skipped dup initialization hooks and immediate dup positional arity.
Two further clone probes verify singleton methods added during the hook freeze
with their copy, and String hooks initially see an ASCII-8BIT empty shell.
Runtime Regexp.new remains mutable and agrees. Do not implement regex literal
identity by pattern equality: separate literal sites must stay distinct.

For dup, reuse the new core-copy machinery but preserve its separate protocol:
private initialize_dup calls initialize_copy, no freeze keyword, singleton state
is omitted, and invalid immediate arity must raise. Original singleton clone and
namespace/Random copying remain gates. Other native payloads currently preserve
default copies only while both hooks resolve to defaults; custom hooks need
uninitialized native allocation/state before they can be modeled honestly.

Still open: Hash#default (exposed by the clone hook audit), Array.new(array),
general String#-@ / frozen-literal canonicalization, permanent ASCII-name encoding,
Integer#chr's ASCII encoding, competing namespace path ordering, set_temporary_name,
namespace copy/removal, const_missing, native method removal/Kernel ownership and
Random/Regexp overrides. Full conformance remains incomplete. Unrelated paper/
and wasm upstream-bug files are untouched; proof repair remains deferred.

## Previous batch (2026-09-28, L297)

L296 and L297 are separate increments: native fresh String#b copies, then frozen
cached Module#name identity. The latter shares equal native paths, keeps old name
snapshots through permanent promotion and preserves identity across heap writes
and optional-feature loading. Native to_s/inspect remain fresh and mutable.
Seven name-cache-* guards retain 32 agreeing probes. The 33-case audit repairs
29 disagreements and one temporary-name encoding gate; one old clone keyword
failure remains. All seven disagreements in the original 14-case name audit are
also repaired; its five gates remain. L276–L297 have separate commits.

Final validation: model build passes (102 jobs), with no later runtime edits.
Full bootstrap: 1,309 cases, 1,096 agree, zero disagree, 207 unsupported, five
existing invalid controls and the old test_syntax_115 harness error. Every source
and verdict matches L296. Regression replay: 203 cases, 202 agree and one old
sorbet-hash gate; all 196 earlier sources/verdicts hold. Tier 1 (300, seed
20260927): 226 agree, 74 gates, all sources/verdicts unchanged. Frontend seeds
plus new guards: 53 agree, all AST-idempotent; six old render-only instabilities
plus one benign name-cache-reads rendering instability. Standalone and feature
loading: three agreements each. Whitespace checks pass. Build logs, before/after
probes, combined-source validation, comparisons and the next audit are archived
in `difftest/reports/20260928-incremental-L297/`. No checker, proof, comparator,
normalizer or floor changes; proof repair remains explicitly deferred.

The typed gate was rerun and remains red at HeapFacts className/lookup proof
drift; its captured error log exactly matches L296. Proof repair stays deferred.

The batch Metatheory audit also failed (NotDone/KontFrame); the axiom scan
was not reached. The captured proof-audit.log is archived.

Next known semantic failure: native clone keyword handling. The 16-case
`probes/next-audit.json` (script beside it) records eight clone disagreements,
six general String interning disagreements, one singleton-copy gate and one
agreeing positional-hash rejection. Object, Array, Hash, String and binary String
clone(freeze: false/true) enter the positional-Hash/zero-arity path. Immediate
values silently ignore freeze:false instead of raising; unknown/invalid keyword
validation and subclass initialize_clone hooks also disagree. Repair the native
copy protocol (aliases/super and effectful initialize_clone/initialize_copy),
not just the arity list. Default no-keyword cloning has an agreeing name probe.

General String#-@ and frozen-literal canonicalization remain known wrong answers.
The old String#-@ comment that sharing is unobservable is false. A complete pool
must share Unicode and temporary native names in both allocation orders, preserve
metadata/subclass rules and represent the US-ASCII distinction: A.name shares
with -A.name.dup, but not with -"A" or -"A".b. Permanent ASCII-name encoding still
gates honestly. Competing namespace paths, Integer#chr's ASCII encoding,
set_temporary_name, namespace copy/removal, const_missing, native method-removal/
Kernel ownership and Random/Regexp overrides remain open conformance work.

No running campaigns remain. Unrelated paper/ and wasm upstream-bug files are
untouched. Full conformance remains incomplete; proof repair is deferred.

## Previous batch (2026-09-28, L296)

L296 makes String#b native and always returns a fresh mutable base String.
It fixes binary receiver aliasing and bypasses the exposed __as_binary wrapper.
Four binary-copy-* guards preserve 20 agreeing probes; String#[]= still gates.
L276–L296 are separate increments.

Final validation: model build passes (102 jobs). Full bootstrap (1,309):
1,096 agree, zero disagree, 207 unsupported, five existing invalid controls and
one old test_syntax_115 harness error. All source/verdict pairs match L295.
Regressions (196): 195 agree and one old sorbet-hash gate; all earlier sources
and verdicts hold. Tier 1 (300, seed 20260927): 226 agree and 74 gates, unchanged.
Frontend seeds plus new guards: 50 agree, all AST-idempotent, six old render-only
instabilities. Standalone and feature loading: three agreements each. Generated
Prelude.lean reproduces exactly; whitespace checks pass. A final rebuild and
focused replay pass after comment cleanup and removal of a duplicate membership
entry; neither cleanup changes behavior. Evidence is archived in
`difftest/reports/20260928-incremental-L296/`. No proof, checker or floor edits.

The typed gate was rerun and remains red at the existing HeapFacts className/lookup
proof drift. Its log is archived; proof repair remains explicitly deferred.

Next: restore `/private/tmp/conformance-l297-name-cache.patch` with git apply.
It adds native frozen Module#name caching and preserves L296's native b entry.
Do not restore the whole saved Heap.lean: its pre-L296 method table is stale.
The prepared `/private/tmp/conformance-l297-focused.py` has 28 probes, including
one old String#clone(freeze: false) arity failure. Add cached-name binary-copy
coverage and retain that failure as separate work. General String#-@ interning,
permanent ASCII-name encoding, and the L295 competing-namespace-path ordering
boundary remain open. Proof repair remains explicitly deferred. Unrelated paper/
and wasm upstream-bug files are untouched; full conformance remains incomplete.

## Previous batch (2026-09-28, L295)

L295 fixes permanent namespace-name propagation, including the preserved
constant-nested-name failure. ClassPayload.namePermanent distinguishes temporary
paths; nameConstant and setNamespacePath run after binding and before callbacks.
Frozen/private descendants, ancestor cycles, overwritten constants, Object-scoped
declarations and native singleton-class prefixes are covered. Eight namespace-*
regression programs retain 47 agreeing probes. L276–L295 are separate increments.

Final validation: model build passes (102 jobs). Full bootstrap (1,309 cases):
1,096 agree, zero disagree, 207 unsupported, five existing invalid controls and
the old test_syntax_115 harness error. Every source/verdict pair matches L294.
Regression replay (192): 191 agree and one old sorbet-hash gate; all 184 earlier
sources/verdicts hold, and eight new guards agree. Tier 1 (300, seed 20260927):
226 agree, 74 gates, all sources/verdicts unchanged. Frontend seeds plus new guards:
54 agree, all AST-idempotent; six old render-only instabilities plus one benign
rebind-hook rendering instability. Standalone and feature loading: three agreements
each. Whitespace checks pass. Reports, build log, before/after probes and the
symbol-order witness are archived in difftest/reports/20260928-incremental-L295/.
No runtime edits after the final build. No checker, proof, comparator or floor
changes; proof repair remains explicitly deferred.

The 28-case focused audit moved 19 disagreements to agreement. Four other wrong
answers now gate explicitly on competing namespace paths: CRuby picks a path
using its process-local symbol-ID table order, which the model does not carry.
This is not counted as a conformance repair. In the archived order witness,
merely prefixing `p :A` changes M::A into M::Z. Preserve the boundary until that
ordering is modeled; do not guess newest/oldest/alphabetical order. The extra
30 probes have 25 agreements, two ordering gates and three existing gates.

Immediate next known semantic issue: Module#name allocates a fresh mutable String
instead of returning its cached frozen name. The focused name-read-identity and
name-boot-name-identity probes preserve two disagreements, including a temporary
name snapshot across permanent promotion. Audit native arity, aliases, encoding,
identity and representation snapshots before repairing it. Integer#chr's ASCII
encoding error from the L293 audit also remains open. Other known work includes
set_temporary_name, namespace copying/removal, const_missing, the old native
method-removal/Kernel ownership limitations and Random/Regexp overrides.

The batch Metatheory audit also failed (NotDone/KontFrame); the axiom scan
was not reached. The captured proof-audit.log is archived.
The next Module#name audit is archived as probes/next-name-audit.json (script
beside it); it adds arity, aliases, interned path identity and encoding probes.
Proof repair remains deferred; the typed gate is not claimed green. Unrelated
paper/ and wasm upstream-bug files remain untouched. Full conformance is incomplete.

## Previous batch (2026-09-28, L294)

The incremental-commit request is handled: L276–L294 each have separate commits.
The last pending work was split into L293 (Unicode String inspection) and L294
(native const_set validation/conversion). L294 checks names before frozen writes,
executes checked to_str and diagnostic inspection, preserves native aliases/super
and uses a Unicode start-character table verified against all scalars. Seven
const-set-* regression programs retain all 53 agreeing focused probes. Binary
high-byte names/diagnostics and native-method-removal inventory cases still gate.

Final validation: model build passes (102 jobs). Full bootstrap: all 1,309 cases,
1,096 agree, zero disagree, 207 unsupported, five existing invalid controls and
one old test_syntax_115 harness error. All source/verdict pairs match L293.
Regression replay: 183 agree and one old sorbet-hash gate (184 total); all 177
old sources/verdicts hold and seven new guards agree. Tier 1 (300, seed 20260927):
226 agree and 74 gates, every source/verdict unchanged from L292. The 47 prior
constant probes now have 43 agreements, three gates and the unchanged recursive
namespace-naming disagreement: three gates and the invalid-name disagreement
become agreements, with no losses. Unicode generation verifies/reproduces exactly.
Reports, build log, focused probes and frontend diagnostics are archived in
`difftest/reports/20260928-incremental-L294/`. No runtime changes after the final
model build. Proof repair remains deferred and the typed gate is not claimed green.

Frontend: 51 agreements and two diagnosed harness failures, with AST idempotence
preserved. Invalid quoted Symbols are rendered as invalid bare Symbol syntax;
Symbol#to_s replacement breaks the frontend JSON observer. Exact source programs
agree under the differential wrapper. These are recorded limits, not green checks.
No frontend, checker, proof, comparator or floor changes.

Next known wrong answers: recursive namespace naming (constant-nested-name in the
archived prior-constants probes) and Integer#chr ASCII encoding (L293's initial
regression audit). Constant removal, namespace copying, const_missing, the old
method-removal/Kernel ownership limitations and Random/Regexp overrides remain
open. Do not conflate this commit with encoded Symbol identity or a full encoding
model. Proof repair remains deferred; the existing HeapFacts className/lookup
failure is not repaired. Unrelated paper/ and wasm upstream-bug files are untouched.
The batch proof audit also failed to build Metatheory (NotDone/KontFrame);
its axiom scan was not reached. The captured proof-audit.log is archived.
Full conformance remains incomplete.

## Previous batch (2026-09-28, L293)

The user requested separate commits for every completed increment. L276–L292
already have individual commits. L293 isolates the Unicode String inspection
fix from the pending native const_set work. The Unicode generator verifies every
scalar against CRuby 4.0.5; the regression covers controls, supplementary-plane
escapes, nested/subclass inspection and explicit binary strings.

Validation: lake build rubycore passes (102 jobs). All 1,309 bootstrap cases ran:
1,096 agree, zero disagree, 207 unsupported, five existing invalid controls and
the old test_syntax_115 harness error. Every source/verdict pair matches L292.
Regression replay: 176 agree and the one old sorbet-hash gate (177 total); all old
sources/verdicts hold. Frontend: 47 agree, AST-idempotent, with the six old
render-only instabilities. Generator verification/reproduction and whitespace
checks pass. Reports and logs: difftest/reports/20260928-incremental-L293/.
Proof repair remains deferred; the typed gate is not claimed green.

Next: finish and separately commit native const_set validation/conversion, whose
pending implementation is preserved under /private/tmp/ruby-lean-commit-current/.
Constant descendant naming remains a known wrong answer. The new initial audit
also records Integer#chr's existing ASCII encoding error (0.chr/127.chr render
with Unicode rather than byte escapes); preserve that witness for a separate fix.
No proof, checker, comparator or floor changes. The previously recorded proof
failure remains deferred. Unrelated paper/ and wasm upstream-bug files are untouched.
Full conformance remains incomplete.

## Previous batch (2026-09-28, L292)

Continue toward CRuby conformance, fixing known semantics issues first. Commit
each increment separately and run the full bootstrap differential suite before
each commit. Proof repair remains explicitly deferred. L276–L291 are committed
separately; historical uncommitted-status statements below are superseded by
those commits. Unrelated paper/ and wasm upstream-bug files remain untouched.

L292 routes constant writes through private const_added dispatch, after naming
and binding and before inherited/class bodies. Callback errors retain writes,
while the original class identity survives binding replacement. Constant rescue
targets now use their lexical namespace and callback/frozen protocol, with $!
installed before the hook. Seven const-added-* regression programs retain all
39 agreeing probes. Model L292 and difftest N66 record the boundary.

Final validation: model build passes (100 jobs). Full bootstrap (1,309 cases):
1,096 agree, zero disagree, 207 unsupported, five existing invalid controls and
the old test_syntax_115 harness error. Every source/verdict pair is unchanged
from L291. Regression replay (176 cases): 175 agree and one old sorbet-hash gate;
all 169 old sources/verdicts hold and seven new guards agree. Tier 1 (300 cases,
seed 20260927): 226 agree and 74 gates, every pair unchanged. Previous 576 probes:
551 agree and 25 gates, every verdict unchanged. Frontend 53 agree and remain
AST-idempotent, with six old render-only instabilities. Standalone and feature
loading: three agreements each. Generated Prelude/CRubyNames and whitespace
checks pass. Reports, build log and probe snapshots are in
`difftest/reports/20260928-incremental-L292/`. No runtime edits after the final
build; proof repair remains deferred.

Next known wrong answers are preserved in /private/tmp/conformance-l292-extra.json:
constant-invalid-string-name accepts x, A::B and the empty name; constant-nested-name
leaves descendant names temporary after their parent acquires a permanent name.
Address those first. The mixed name-validation probe gates later on non-String
arguments and must not conceal its earlier invalid writes. const_set aliases and
checked name conversion, remove_const, and frontend compound constant writes also
remain recorded gates. The raw non-UTF-8 source literal still fails export; the
runtime 255.chr default-hook test agrees. CRuby also accepts Unicode constant
names such as É, ǅ and Aé; avoid treating ASCII-only validation as complete.
Both const_set and remove_const call a supplied to_str before the frozen check.

The prior native method-removal shadow/Kernel ownership limitations, namespace
copying, const_missing, and Random/Regexp replaced initializers remain open. Keep
the old sorbet-hash gate explicit. No comparator, checker, proof or floor changes;
the typed gate has a known HeapFacts className/lookup failure and is not green.
Full conformance remains incomplete.

## Previous batch (2026-09-28, L289)

Full conformance remains active/incomplete. L288 and L289 made verified progress;
L276–L289 are uncommitted. No checker/proof/floor edits, typed gate or commit.
Proof repairs remain explicitly deferred; unrelated paper/ and wasm files untouched.

L289 adds native checked Object#inspect in Interp/Inspect.lean, a private default
instance_variables_to_inspect hook, buffered field names with live values/filter,
ordinary nested rendering and a continuation recursion guard. Ivar reassignment
keeps insertion order. Pure repr checks hook purity and cycles. Old Object slow
twin removed. Explicit binary/immediate gates remain. Model L289 / difftest N63.

Final reports20260928-083226: bootstrap1309 =1095 agree /0 disagree /208 unsupported,
five invalid controls and old syntax115 harness-error; tier1 n300 seed20260927 =226
agree /74 gates. Every old source/verdict unchanged. Replay141 =140 agree /one old
sorbet-hash gate; all135 old pairs held, six new guards agree. Previous414 =398 agree /
16 gates unchanged. Focused29 =26 agree /three old gates; extra32 all agree.
Frontend52 agree, AST-idempotent, six old render-only instabilities. Standalone3 /
loading3, build100 jobs, generated cmp and whitespace checks pass. All L289 sessions
ended. No Lean changes after final build. Evidence /private/tmp/conformance-l289-*.
Proof audit FAILED exit1 at lake build Metatheory, NotDone/KontFrame in tail, no
axiom scan; log l289-proof-audit.log. No repairs.

Immediate next work: /private/tmp/conformance-l290-repr-alias-audit.{py,json,log}
contains seven disagreements. Pure repr treats any builtin alias as its original
renderer. Validate resolved native renderer IDs for the actual payload, including
undefined/removed methods, and make resolved Object#to_s independent of subclass
payload/twins. This is adjacent to L289 but is not fixed by it. No L290 source edits
at this boundary. Then /private/tmp/conformance-l290-class-audit.{py,json,log} has
nine disagreements /seven old gates: inherited skipped for new/named classes,
subclassing Class wrongly allowed, wrong Module-superclass wording, uninitialized
Class/Module initialization protocols and replaced initializers. Named constants
exist before inherited; Class.new remains anonymous until later assignment.
Inherited runs before the body; failures retain the named class binding.
Primary object.c rb_class_initialize/rb_mod_initialize_exec confirms class initialize
returns its class, Module initialize nil, hook before body. The broader open scope
from preceding handoffs remains active; don't invent the old Sorbet hash.

## Previous batch (2026-09-28, L288)

Full conformance remains active and incomplete. L288 made verified progress:
five confirmed for disagreements plus custom/private each gates now agree. No
checker/proof/floor edits, typed gate or commit. L276–L288 remain uncommitted;
proof repair is explicitly deferred. Unrelated paper/ and wasm files untouched.

For now sends ordinary explicit each with a hidden callback, shares enclosing
locals through Frame.localAlias while keeping fresh control frames, converts
multiple targets through checked to_ary and queues ordinary assignments. Captured
callbacks preserve scope and safe return/break, support block eval/define_method.
The frontend retains one-target comma destructuring with an optional fifth field.
MethodDef.fromBlock and dmFrameK retain define_method control semantics independently
of capture erasure: break/next/return local, redo without rebinding/defaults.

Final reports20260928-082327: bootstrap1309 =1095 agree /0 disagree /208 unsupported,
5 control-invalid /1 old syntax115 harness-error. Tier1 n300 seed20260927 =226 agree /
74 unsupported. Every source/verdict unchanged from L287. Replay135 =134 agree /
one old sorbet-hash gate, all129 old sources/verdicts held; six new guards agree.
Previous351 =337 agree /14 gates, unchanged. Focused20 =19 agree /old Proc#arity
gate; extra43 =42 agree /old top-level-return gate. Frontend52 agree, AST-idempotent,
six old render-only instabilities. Standalone3/loading3 agree. Build98 jobs,
generated cmp and whitespace checks pass. All L288 validation sessions ended.
Model notes L288, difftest N62, frontend C41; evidence /private/tmp/conformance-l288-*.

Required proof audit FAILED exit1 at lake build Metatheory; NotDone/KontFrame in
captured tail, axiom scan not reached. No repairs. Log l288-proof-audit.log.

Next confirmed priority: Object#inspect skips Ruby 4's checked
instance_variables_to_inspect hook. Original failing for probe is preserved in
/private/tmp/conformance-l289-inspect-known.json; loop-only variant ends in nil.
Audit11 =nine disagreements /one agreement /one old reflection gate; extra oracle17
pins semantics. Hook returns nil or Array (otherwise TypeError), called before
recursion check. Iterate buffered ivar names in insertion order, reading values
and the selection Array live. Reassignment must not reorder an existing ivar.
Current pure renderer skips hooks; Object#__inspect_slow calls Ruby instance_variables/
get overrides incorrectly. Use checked conversion continuation plus native inspector.
No L289 source edits at this recorded boundary. Other scope remains below.

## Previous batch (2026-09-28, L287)

Full CRuby conformance remains active and incomplete. This turn made verified
progress: all seven confirmed parameter-destructuring failures are repaired, and
five bootstrap plus seven seeded generated programs move from gated to agree.
L276–L287 changes remain uncommitted. No checker/proof/floor source edits, typed
gate or commit; proof repair is explicitly deferred. Unrelated paper/ and wasm
upstream-bug files remain untouched.

Nested formal binding now advances through Kont.paramBindK and the shared checked
conversion protocol (ConversionCall.paramDestructure). Actual Arrays bypass to_ary;
missing/nil conversion expands the original scalar, invalid results raise TypeError.
Private methods, response hooks, missing handlers and nonlocal exits are ordinary
transitions. Each expansion snapshots values before nested callbacks and assigns
trailing slots only from the unconsumed tail, padding short inputs with nil. Later
parameters read the live heap. Method positional/keyword defaults run BEFORE nested
conversion; component names are nil in that phase and shadow captured define_method
locals. Blocks/procs/lambdas share the binding queue, retaining strict/lenient
arity and redo/return/next behavior. Synthetic slots use inaccessible names, avoiding
collisions with __destr_0. Optional/keyword/forwarding closure forms still gate.
The old executable destructureBind helper is removed; no proof repair attempted.

All reports20260928-080526:bootstrap1309 =1095 agree / zero disagree /208
unsupported, five invalid controls and the old test_syntax_115 harness error.
Gains exactly test_block_037/038/039/040 and test_massign_008. Tier1 n300
seed20260927 =226 agree /74 unsupported, seven gains. Replay129 =128 agree /one
old sorbet-hash gate. Every old source is unchanged; no prior agreement lost.
Previous301 =287 agree /14 gates, every verdict unchanged. Focused20, extra29,
147-call shape matrix and permanent4 all agree. Frontend49 agree /zero disagree,
AST-idempotent with six old render-only instabilities. Standalone3 and identical-
source loading3 agree. Final build98 jobs passes; both generated files match
regeneration and whitespace checks pass. All validation sessions terminated;
no pending builds or tests and no source edits after final build except docs.
Model notes L287 and difftest N61 record the full results. Evidence:
/private/tmp/conformance-l287-*.

Required proof audit FAILED exit1 during lake build Metatheory; NotDone and
KontFrame in captured failed-target tail; axiom scan not reached. Log:
/private/tmp/conformance-l287-proof-audit.log. Repairs remain deferred.

Next confirmed priority: legacy for bypasses each and snapshots Array contents.
/private/tmp/conformance-l288-for-audit.{py,json,log}: five disagreements (Array
each override, live growth, live replacement, to_ary, break binding), two old gates
(custom/private each), one scope agreement. for-oracle and for-escape-oracle logs
pin CRuby details: call ordinary explicit each (private each raises), return its
normal result, share enclosing locals/block/match scope, and honor live iteration.
Single-target for takes the FIRST yielded argument; multi-target for destructures
all yielded values. Body yield/block_given? refers to the enclosing method block.
Escaped for callbacks must raise LocalJumpError for stale return/break targets;
naively pushing an old enclosing method frame id would revive a dead return scope.
A captured block reports lambda? false and arity1/-1 for single/multiple targets.
Start at Interp/Kont.lean's forStartK/forBodyK and Send.lean's forBind/forStep. The
old implementation's comment that for evaluates to its collection is too broad:
overridden each can return a different value. No L288 source edits yet.

Continue full scope after that: Class/Module/Random/Regexp/Array constructor
protocols, constant/ancestry/mixin hooks, generic dup/clone callbacks, File stub,
Kernel owner folding, repeated inclusion identity, Sorbet/loader fidelity, and
remaining bootstrap eval/TracePoint/reflection/RubyVM gates. Do not invent a
process-specific hash to bypass the sole old sorbet-hash gate.

## Previous batch (2026-09-28, L286)

The full CRuby conformance goal is active and incomplete. This turn made verified
progress: L286 fixed the native-error-initialize defect left by L285. L276–L286
remain uncommitted. No checker/proof/floor source edits, typed gate or commit.
Proof repair remains explicitly deferred. Unrelated paper/ and wasm upstream-bug
files are untouched.

Native VM errors now initialize through ordinary private dispatch, retaining $!
and bypassing new/allocate/exception; native NameError/NoMethodError/KeyError keep
their deliberate direct initialization. FrozenError initializes its mutable prefix
BEFORE inspecting and appending; callback message replacement, mutations, frozen
checks and exceptions are respected. StopIteration initializes inside the producer
on first completion, then from the original's live raw message inside the caller
on later resumes. Uncaught throw sends tag/value/raw format to initialize and
inspects its live tag lazily at message time. Native metadata survives copies.
Nondefault printf formats, non-String throw format conversion, cause/backtrace and
other native metadata remain partial. See model L286, difftest N60 and semantics
README §§04.5/04.7.

Verified full baseline20260928-075300:bootstrap1309 =1090 agree / zero disagree /
213 unsupported, five invalid controls and the old test_syntax_115 harness error.
Tier1 n300 seed20260927 =219 agree /81 unsupported / zero disagree. All old
source/verdict pairs unchanged from L285. Final replay075806 =124 agree / one old
sorbet-hash gate / zero failures (125 programs); all120 old sources/verdicts held.
The full1309 run preceded only a final native tag/value copy correction; final
binary replay of all23 bootstrap sources mentioning copy/throw =17 agree /six
old gates, unchanged. Extra27 all agree, expanded permanent5 all agree. Focused24
=22 agree /two old gates; Previous250 =238 agree /12 old gates, with the known
native-error-initialize disagreement now agree and every other verdict unchanged.
Frontend50 agree /zero disagree, AST-idempotent, six old render-only instabilities.
Three standalone and three identical-source loading checks agree. Final model
build98 jobs PASS; generated cmp and whitespace checks pass. All processes ended.

AGENTS.md proof audit ran and FAILED exit1 at lake build Metatheory; NotDone and
KontFrame appear in the captured failed-target tail, axiom scan not reached.
No repairs. Log /private/tmp/conformance-l286-proof-audit.log. The executable
model checks pass; metatheory does not. Evidence: /private/tmp/conformance-l286-*.

Next confirmed known-bug priority: method parameter destructuring. Audit
/private/tmp/conformance-l287-binding-audit.{py,json,log} has seven disagreements /
one agreement. Private/public/nested to_ary are skipped, nil converters lose
side effects, invalid converters fail to raise TypeError, and short inputs reuse
leading values in trailing slots. CRuby evaluates optional defaults BEFORE these
conversions (the default-order probe pins this); current pure destructureBind is
folded into pre-default binding in Interp/Dispatch.lean. Repair the binding pipeline
with effectful checked conversion and correct nonoverlapping positional slicing.
No L287 source edits yet. No new fixed guards claim these still-failing cases.

Continue full scope after that: native Class/Module/Random/Regexp constructors,
legacy for/each, constant/ancestry/mixin hooks, generic dup/clone callbacks, File
stub, Kernel owner folding, repeated inclusion identity, Sorbet/loader fidelity,
and remaining bootstrap eval/TracePoint/reflection/RubyVM gates. Do not invent a
process-specific hash to bypass the one old sorbet-hash gate.

## Previous batch (2026-09-28, L285)

The full conformance goal is active and incomplete. L276–L285 changes are
uncommitted; no checker/proof/floor edits or typed gate. Proof repair is explicitly
deferred. Unrelated paper/ and wasm upstream-bug files remain untouched.

L285 fixes Ruby-level raise/exception dispatch, checked String conversion,
mutable exception messages and Exception#exception copy callbacks. Payload.exc
holds Value (nil = class-name default). Exception#to_s returns actual Strings
unchanged; other messages go through checked to_str then to_s. Those messages
make pure repr defer. Raise/fail retain response hooks and custom missing handlers;
Exception.exception constructs directly, independently of overridden new. The old
userInit? shortcut is removed. Boot exception classes and anonymous class/module
results realize eigenclasses for inherited singleton methods. Message-only native
NameError/NoMethodError/KeyError/FrozenError initializers delegate to super in
prelude and return self; metadata forms gate. Instance exception copies through
initialize_clone/initialize_copy, applies the original's current frozen state
after callbacks, then replaces its raw message without initialize. Singleton
copies, cause/backtrace/metadata and Exception#== remain gated.

Final model build PASS (98 jobs). Final reports share 20260928-074001:
bootstrap **1,090 agree / zero disagree / 213 unsupported**, five invalid
controls and the old test_syntax_115 harness error; every source/verdict unchanged
from L284. Tier 1 n=300 seed20260927: **219 agree / 81 unsupported / zero disagree**.
Regression replay: **119 agree / one old sorbet-hash gate / zero failures**, 120
programs. All old sources/verdicts held. Five new permanent programs agree,
including five additional clone callback/freeze cases. Focused24 all agree;
extra19 = 18 agree / one old equality gate; five copy edges agree. The separate
native-error-initialize row is a confirmed next-work defect, not a fixed case.
Previous201 replay (before the final copy-edge fix): unchanged 190 agree / 11 gates.
Frontend50 agree / zero disagree, AST-idempotent with six old render-only
instabilities. Three standalone core-only and three identical-source feature-
loading checks agree. Prelude and CRubyNames match regeneration; whitespace check
passes. Initial full suite 073446 also held all sources/verdicts.

All validation processes have terminated. The AGENTS.md-required proof audit
ran and FAILED during lake build Metatheory (exit 1); its captured tail names
RubyCore.Proof.NotDone and RubyCore.Proof.KontFrame among failed targets. The axiom
scan was not reached. Log: /private/tmp/conformance-l285-proof-audit.log. No proof
repairs were attempted, as requested. Model implementation-notes L285 and difftest
N59 contain the final results. The executable model checks pass; metatheory is not
green. No typed gate or commit. Continue with the next known semantics issue.

Next known-bug priority: native VM errors bypass user initialize in the model.
The oracle audits /private/tmp/conformance-l286-{native,frozen}-oracle.py/log pin
these distinctions: TypeError, ArgumentError and ZeroDivisionError invoke
initialize(message), without keywords/block, and preserve the surrounding $! while
it runs. Native VM NameError/NoMethodError deliberately DO NOT invoke initialize;
a blanket raiseErr rewrite would be wrong. FrozenError initializes a mutable
prefix String BEFORE inspecting its receiver and appending the result; callbacks
can replace the exception's message, mutate the shared prefix, or raise before
inspection. The live message representation now makes that protocol expressible.
raiseErr currently allocates and jumps (Interp/Support.lean); Frozen.lean renders
the whole message before raising. No L286 source edits yet.

Other known leads: Class/Module/Random/Regexp initialization/allocator protocols,
unchecked destructureBind to_ary, legacy for bypassing each, constant/ancestry/
mixin hooks, generic dup/clone callbacks, File's module-shaped stub, Kernel owner
folding and repeated inclusion-node identity. Full Sorbet/runtime loader fidelity
and bootstrap eval/TracePoint/reflection/RubyVM gates remain unfinished. Do not
invent a process-specific hash to bypass the sole old sorbet-hash gate.

## Previous batch (2026-09-28, L284)

The full CRuby conformance goal remains active and incomplete. Known semantics
bugs have priority; proof repair is explicitly deferred. L276–L284 changes are
uncommitted. No checker/proof/floor edits, typed gate or commit. Unrelated paper/
and wasm upstream-bug files remain untouched.

L284 fixes Class#new's undef-initialize defect and related dispatch bypasses.
Native construction/allocate now follow resolved method IDs after lookup and
visibility, including aliases and super. Interp/Construct.lean allocates plain,
String/Array/Hash/Exception, Proc and Enumerator instances and queues an ordinary
reflective initialize send, preserving arguments/keywords/block and missing-method
behavior. Native new does not send an overridden allocate. Core initializers
return self; BasicObject owns its zero-argument nil-returning initialize. String
and Hash reinitialization preserve contents, with frozen/arity checks matching
CRuby; Hash default lambdas validate arity. Array block initialization observes
live receiver mutations and control flow. Proc.new preserves same-class closure
identity or copies into a subclass, and calls initialize. Proc.allocate raises
TypeError. Six immediate classes now undefine singleton new in the prelude.

Closure.breakScope and Kont.blockCallK bind literal-block break to its original
call, including native constructors and explicit super literals. Forwarding
through initialize, helpers and Proc#call preserves that boundary; ensures run
while unwinding, detached Proc break raises LocalJumpError, lambda break stays
local. Fresh tags reserve frame-store slots without adding activations. Keyword
packets also survive undef/visibility/ordinary/super misses into method_missing.

Final bootstrap report 20260928-071903-tier0-lean: **1,090 agree / zero disagree /
213 unsupported**, five invalid controls and the old test_syntax_115 harness error.
Exactly three gains over L283: test_flow_045, test_proc_030, test_proc_031. No lost
agreements or source changes. Same-stamp tier 1 n=300 seed20260927: **219 agree /
81 unsupported / zero disagree**. Same-stamp replay: **114 agree / one old
sorbet-hash gate / zero failures**, 115 programs. All old sources/verdicts unchanged.

Eight new permanent regression programs all agree. Focused 66 new individual
probes: 62 agree/four explicit gates. Previous 135 cases: unchanged 128 agree /
seven gates, including 28 Sorbet cases (25 agree/three old gates). Three standalone
core-only programs and three identical-source feature-loading protocols agree.
Front-end: 45 seeds plus eight new programs, 53 agree/zero disagree, AST-idempotent;
six old render-only instabilities plus constructor-blocks.rb. Prelude and CRubyNames
match regeneration; git diff --check passes. Final build passed 98 jobs, including the comment-only rebuild
(/private/tmp/conformance-l284-final-build.log). All validation processes terminated.
Details: implementation-notes L284, difftest N58, /private/tmp/conformance-l284-*.

Next priority: the old raise C interception still uses userInit? and bypasses the
exception protocol. The read-only /private/tmp/conformance-l285-raise-audit.py
confirms seven disagreements, three gates and two agreements; JSON/log include
exact sources and observations. Undef initialize still silently succeeds under
raise; missing initialize must reach method_missing. CRuby sends exception even
when private, independently of an overridden new, and validates its result.
Instance exception cloning preserves ivars and bypasses user initialize.
/private/tmp/conformance-l285-exception-oracle.py/log also pin checked to_str
before exception for one argument, respond_to? hooks, live exception message
objects, nil/default messages, frozen cloning and alias raise. No L285 source
edits yet; repair this known bug family next.

Other constructor limits: Class/Module/Random/Regexp factories retain their
argument-dependent legacy path and now gate replaced initializers; native
uninitialized payloads/protocols need work. Explicit super block-pass and
Hash#default= remain gated. Other known leads remain unchecked destructureBind
to_ary, legacy for bypassing each, constant/ancestry/mixin hooks, frozen writes
outside audited paths, File's module-shaped stub, Kernel owner folding and
repeated inclusion-node identity. The old sorbet-hash gate must not be bypassed
with invented process-specific hashes. Full Sorbet/runtime loader fidelity and
bootstrap eval/TracePoint/reflection/RubyVM gates remain unfinished.

## Previous batch (2026-09-28, L283)

The user wants known semantics issues fixed first, then progress toward full
CRuby bootstrap conformance. Proof repair is explicitly deferred. The goal
remains active and incomplete. L276–L283 changes are uncommitted; checker/proof
files and ratchet floors remain untouched. Existing unrelated paper/ and wasm
upstream-bug files remain untouched. All validation processes have terminated.

L283 fixes the nested-definition target bug and related scope errors.
MethodDef.definee captures nested def/alias/undef's lexical target; Frame.defmod
holds that target, while methodOwner independently anchors super. define_method
retains the block's definitionFrame separately from capturedFrame/local erasure.
Ordinary blocks share defining visibility, including retired scopes and later
changes. Eval blocks start fresh public definition contexts, retaining lexical
constant scope. Ordinary methods start public and ignore bare visibility changes;
macros use visibility only for the matching class/eval target. Top-level def is
private by default and honors public; top-level define_method is public.

Top-level cref is empty, with Object as fallback. Constants search lexical scopes
before ancestors of the innermost scope; modules can fall back to Object.
Qualified class bodies retain real surrounding nesting. Block eval preserves
constant/class-declaration and class-variable scope while rebinding def targets.
New class declarations check frozen namespace state; reopening existing nested
classes is allowed. Class variables skip singleton lexical scopes and reject
reads/writes with no enclosing ordinary class/module. defined? alone can still
inspect Object's class variables.

Main-only native methods no longer contaminate Object's inventory. Generated
crubyMainSingletonNames is separate, core boot realizes main's eigenclass, and
native entries have ordinary lookup/visibility. Main# macros share reflection
protocols; include targets/returns Object. inspect/to_s use main-aware primitives.
Top-level define_method now works, with receiver/arity/body checks and explicit
Proc precedence over a block. Method/UnboundMethod bodies remain gated. Mixin
macros validate one module argument and required arity before frozen writes;
nil/true/false diagnostics use literal names. Full multi-module/hook protocols
remain incomplete. Forwardable no longer needs a special synthetic capture frame:
ordinary helper method frames now carry its correct lexical definee.

Final build PASS (96 jobs). Bootstrap **1,087 agree / zero disagree /
216 unsupported**, five invalid controls and the old syntax harness error.
Exactly five gains over L282: test_yjit_275,277,278,279,280 (top-level
 define_method), no lost agreements or source changes. Regressions **106 held /
one old gated / zero failures** (107 programs); all old sources/verdicts unchanged.
Tier 1 n=300 seed20260927: **219 agree / 81 unsupported / zero disagree**,
all sources/verdicts unchanged. Final reports:
`difftest/reports/20260928-065807-{tier0,tier1,tierregressions}-lean/`.

Nine new fixed programs cover definition targets, define_method scope/protocol,
visibility, constants, frozen declarations, main macros, class variables and
mixin arguments. The 43 focused scope cases and all nine combined permanent
programs agree. Prior 92-case replay is unchanged: 85 agree / seven explicit
gates / zero disagree, including all 28 Sorbet programs (25 agree / three old
gates). Three standalone core-only programs and all three identical-source
feature-loading checks agree. Front-end: 45 seeds plus nine new programs,
**54 agree / zero disagree**, AST-idempotent with six old render-only
instabilities. Both generated files match regeneration; git diff --check passes.
No proof build, typed gate or commit. Details/reproduction are implementation-notes
L283 and difftest N57; temporary evidence is /private/tmp/conformance-l283-*.
The interim 065253 suite completed normally after lost tool handles were checked
against live OS PIDs; it was not restarted while still running.

Next work, keeping the full objective:

1. A final read-only audit confirmed the older Class#new bug: `class NoInitializer;
   undef initialize; end; NoInitializer.new` succeeds in the model but raises
   NoMethodError in CRuby. Evidence: /private/tmp/conformance-l283-next-constructor.json.
   userInit? treats an undef tombstone as a user body. Preserve normal initialize
   and method_missing dispatch after allocation; simply filtering it and falling
   through to newImpl can still silently succeed. Fix this and add regression
   coverage next, including custom method_missing, aliases and payload subclasses.
2. Other known leads: unchecked destructureBind to_ary, legacy for bypassing each,
   constant/ancestry/mixin hooks (including literal const_missing), frozen writes
   outside audited paths, the File module-shaped stub. Kernel ownership folding
   and repeated inclusion-node identity remain structural limits. Constructor
   protocol and method-source binding still need broader fidelity.
3. The sole old regression gate remains sorbet-hash-gate. Do not invent a
   process-specific hash or weaken comparison. Full Sorbet runtime remains partial,
   including model-only namespaces. Loader path resolution/require_relative,
   loader globals, source-position diagnostics and missing library APIs remain.
   Future runtime source compilation/retry needs fresh literal sites.
4. Bootstrap gates still include string eval, TracePoint, block param shapes,
   top-level return, binding/local reflection, String#setbyte, object_id, RubyVM,
   four timeouts and others. The five top-level define_method gates are now fixed.
   Historical out-of-scope labels do not complete the objective; re-measure before
   selecting the next bootstrap batch.

## Previous batch (2026-09-28, L282)

The user wants known semantics issues fixed first, then progress toward full
CRuby bootstrap conformance. Proof repair is explicitly deferred. The goal
remains active and incomplete. L276–L282 changes are uncommitted; checker/proof
files and ratchet floors remain untouched. Existing unrelated paper/ and wasm
upstream-bug files remain untouched. All validation processes have terminated.

L282 fixes the open require-definition-hooks regression. Interp/Mutation.lean's
MethodEdit queue commits one write then dispatches the ordinary Ruby callback;
definitions/aliases/attrs/define_method, removals, undef and singleton variants
share it. Hooks can raise, freeze or mutate a later method; prior effects remain.
Default private hooks live on Module/BasicObject. Only boot suppresses callbacks.
Module#freeze and reflective method/mixin/constant writes check frozen state.
Initialization instance names are private even through aliases and attributes.
Constant visibility uses own names, partial effects and the correct return value.

MethodDef.visibilityOnly represents live inherited visibility changes. Calls and
aliases resolve the current ancestor body; reflection/visibility/undef see the
entry even when that body disappears. Same-visibility edits are no-ops. Module
aliases and visibility macros use Object fallback; remove/undef do not. Modeled
Kernel I/O/conversion/reflection names folded into Object now have private
visibility. Alias superName and superScope preserve original names and class
lookup context (module aliases use their eventual host). This repairs the old
bootstrap test_yjit_145 timeout, including alias-of-alias. Ancestors still
has the older module-identity deduplication; full inclusion-node fidelity remains.

Forwardable now matches upstream 1.4.0 method declarations/order and supports
ordinary load-time method hooks, failure/retry, reentry and frozen namespaces.
Interp/Forwardable.lean compiles simple method/ivar/constant accessor expressions
into a Proc with a real def and ... forwarding. Keyword/block dispatch and
generated method hooks use the ordinary interpreter. Default generated definee
matches the helper's lexical module. This is a Forwardable-specific compiler,
not general string eval. General accessor expressions, source-position warnings,
source/eval/conversion overrides and missing caller locations explicitly gate.
Overridden String#freeze during loading gates because frozen literal compilation
must not silently call a user method. Other libraries retain partial-body hook
boundaries. Native singleton shadow checks respect actual user overrides and
class-aware constructors; an overbroad interim constructor guard was repaired.

Final build PASS (96 jobs). Bootstrap **1,082 agree / zero disagree /
221 unsupported**, five invalid controls and the old syntax harness error.
Only test_yjit_145 changes from L281: timeout to agree; all sources unchanged,
no lost agreements. Regressions **97 held / one old gated / zero failures**
(98 programs); all old sources unchanged, require-definition-hooks now fixed.
Tier 1 n=300 seed20260927: **219 agree / 81 unsupported / zero disagree**,
all sources/verdicts unchanged.

Final reports:
- difftest/reports/20260928-063421-tier0-lean/
- difftest/reports/20260928-063421-tier1-lean/
- difftest/reports/20260928-063351-tierregressions-lean/

Eleven new fixed regression programs cover callbacks, partial mutations, frozen
writes, live visibility, alias/super, constant mutation and Forwardable behavior.
Focused 92-case replay: **85 agree / seven explicit gates / zero disagree**,
including all 28 Sorbet programs (25 agree / three old gates). Four extra
visibility-body/super/error-message probes agree. Three standalone core-only
programs agree. The permanent identical-source check-feature-loading.py passes
its three feature-loading protocols. Front-end: 45 seeds plus 12 changed/added
regression programs, **57 agree / zero disagree**, AST-idempotent, seven
render-only instabilities (six old seeds plus forwardable-delegation).
Prelude/CRubyNames regeneration comparisons and git diff --check pass.
No proof build, typed gate or commit attempted. Details and reproduction commands
are in implementation-notes L282 and difftest N56; temporary evidence uses
/private/tmp/conformance-l282-* (focused JSON includes exact sources/results).

Next work, preserving the full objective:

1. Known semantic leads first. Generic nested def inside a singleton method still
   uses the method owner as definee: `class C; def self.make; proc { def x; 1; end };
   end; end; C.make.call` should define C's instance x. The Forwardable compiler's
   scoped fix does not repair generic def/Proc scope. Distinguish lexical definee
   from super's method owner, and audit define_method/class_eval/reified blocks.
2. Other old leads: legacy for bypasses each; destructureBind has unchecked to_ary;
   constant/ancestry/mixin hook protocols remain incomplete; File is a module-shaped
   stub. Continue the frozen/reflection audit beyond the paths covered here.
   Kernel ownership folding and repeated inclusion nodes remain structural limits.
3. The sole old regression gate is sorbet-hash-gate; do not invent a process-specific
   hash or weaken comparison. Full Sorbet runtime remains partial, including
   model-only helper/type namespaces. Loader path resolution/require_relative,
   loader globals, namespace-conflict source positions and missing library APIs
   remain work. Future runtime source compilation/retry needs fresh literal sites.
4. Current bootstrap gates: 39 string eval, 10 TracePoint, seven block param shapes,
   six each of class_eval strings/top-level return/binding or local reflection/
   String#setbyte; five each of instance_eval strings/object_id/RubyVM/top-level
   define_method; four timeouts remain. Historical out-of-scope labels do not
   complete the objective. Re-measure before selecting the next batch.

## Previous batch (2026-09-28, L281)

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
>   `../books/Books/Metatheory/` files build, axiom-clean.
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
>   kernel-reducible** and silently breaks every `../books/Books/Metatheory/` file while the difftest
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
   **A proof-of-concept slice of this is now done** (`../books/Books/Metatheory/`, off the
   default target; `../docs/model/metatheory.md`, implementation-notes L13–L15): an
   inductive `Step` over an effect-light control-core fragment with
   `Step.sound`, `Step.complete`, `Step.adequacy` (function–relation adequacy
   on the fragment), `Step.deterministic`, and a `Step.heap_monotone`
   preservation invariant — all axiom-clean (`#print axioms` shows only
   propext/Classical.choice/Quot.sound). It validates that the
   interpreter-first design admits real theorems and that rule extraction is
   mechanical (soundness = one uniform `cases`+`simp`). Refreshed against the
   current stepper (control core now covers `redo`/`dowhile`; L13).
   **Type-safety metatheory landed** (`../books/Books/Metatheory/Reachability/TypeSafety.lean`; L51):
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
only go up (baseline now **940**). At batch boundaries also build the `../books/Books/Metatheory/`
files and run `../concolic` (28 tests) — the ratchet does not notice a
kernel-reducibility regression (L73).

---

## C-1 — SUPERSEDED AND DELIVERED THROUGH THE JUDGMENT LAYER (2026-08-26, same day)

> The section below is kept as written for its tactical records (the four wrong
> turns are still traps). Its *task* is done, by the re-scoping
> `docs/semantics/judgment-layer.md` argued for rather than by the `chk` port it
> describes: the invariant is stated over the inductive `Judge`
> (`../books/Books/Metatheory/Typing/Judge/`, J18–J27), `judge_sound_cert` is the composed
> theorem with `hctl`'s role filled by a derivation, and `egEven` — the
> `_certified` corollary below parks on C-1 — is proved **unconditionally**
> (`../books/Books/Metatheory/Typing/Judge/Cert.lean`, and again from a data certificate in
> `../books/Books/Metatheory/Typing/Judge/Adequacy.lean`). The `chk_table_ret` rung was abandoned
> deliberately (judgment-layer.md §5); `chk` remains the coverage tier.

## C-1 (historical) — the one open premise of `validate_sound` (2026-08-26)

`validate` no longer calls `infer`; `#check @infer` does not elaborate from
`RubyCore.Cert.Validate`. The composed certificate theorem is
`../books/Books/Metatheory/Cert/Sound.lean`'s

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
   `../books/Books/Metatheory/Typing/Infer/Mono.lean`'s laws are `induction … using infer.induct`.
2. **The motive map is in `../books/Books/Metatheory/Cert/Mono.lean`** and cannot be read off the
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
