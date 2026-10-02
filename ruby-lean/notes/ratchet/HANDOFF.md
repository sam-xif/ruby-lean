# Active ascent (2026-10-01)

97/100 clinks, 105/261 production validateD accepts (prefix 17), 46/46 negatives
rejected, 254 CRuby agree/0 disagree. Ordinary calls and all seven recursive rules
are permanently enabled alongside
ordinary definitions and the existing literal/local/sequence/primitive/branch/
bare-name/collection providers. Full gate: /private/tmp/ascent-class-sites-gate.log.
Metatheory: /private/tmp/ascent-class-sites-metatheory.log.

Repair uses the original MethodState body/frame/return and MethodArgs accumulator
proofs. MethodResolve follows actual bounded lookup through main's singleton
prefix then Object. DefsOk excludes main-native selectors, derived on installation
from existing topDeclClassesB. OrdinaryMethodCode now pins normalized definee;
MethodDefineeControls retains the old guard's checked-body NoMethodError witness.
Main-prefix and metadata controls remain mandatory; see ../../unsoundness.md.
Native fidelity shadows retain unsupported in top_method_stepSpec, while ordinary
entry consumes the original checked body. New proofs build under a second and
use only standard axioms. Validator controls cover zero/one arguments, older
method retention, wrong type/arity/result, reserved names and missing companion/
body rules. The bridge probe proves identity-call boot runner safety.

Recursive (060) now accepts. The existing strict execution-bound induction is
unchanged; BoundedMethod/BoundedCall carry rootClean, ordinary binding metadata,
provenance, real prefix lookup and native shadow outcomes. The mandatory gate
builds/imports the existing RecursiveDerivations factorial proof and its complete
recursive positive/negative controls. Removing any one of the seven recursive
rules rejects its production trace. New bounded proofs build under a second.

ClassRules preflight: /private/tmp/ascent-class-preflight.log. Actual fresh class
entry queues const_added then inherited, after anonymous registration/naming and
an attached metaclass; the former stepFn_class_fresh jumped straight into the legacy
freshClsMachine and was false (repaired below). ClassHookControls measures complete legacy boot
accepts and unrestricted-checker accepts that raise nil+1 in either callback.
MainReady now rejects those worlds using classHooksQuietB; first own entries
above Object must be native, defined and non-visibility-only. ClassHooks proves
real fuel-bounded lookup from that predicate and preserves it across writes.
Generic write/publication helpers take ClassHookWriteOk; Object is outside the
prefix, including when defining const_added/inherited. Real boot and those
production definitions pass the controls. See ../../unsoundness.md.

ClassRegistration now proves actual registration/naming and the first queued
callback step via the existing model lemma, plus named allocator readiness.
MainSiteWrite.ivarOnly carries all added readiness fields. Both are mandatory
gate prerequisites.

ClassHookDispatch adapts existing native definition-hook dispatch, retaining
unsupported fidelity shadows. ClassCallbacks now composes both real callback
steps and their continuations into the existing freshModFrame body/return
RunSpec. These are mandatory gate prerequisites.

ClassHeapActual now proves actual named/attached reads, exact cached metaclass
allocation, ClsGrow, ChainsIn, saturation, old ancestors/method tables, callback
guard preservation and allocator readiness. ClassEntry.stepFn_class_fresh is
repaired to the actual first queued callback successor and is mandatory.

ClassNamesActual repairs the old named-growth argument's fresh-id premise for
an attached anonymous metaclass, proves actual NamesOk/fuel saturation and old
display-name retention, and is mandatory.

ClassConstantsActual, ClassReadyActual, ClassDataActual and ClassCoreActual now
repair constant/live/root-name retention, ClassReady, DataPres, caller framing
and CoreOk by reusing the original Subclass transfers and generic type induction.
They are mandatory prerequisites with axiom probes.

ClassDispatchActual, ClassQueriesActual and ClassPayloadActual repair inherited
lookup/shadows, primitive dispatch/errors, all three query capabilities and
String/Array/Hash payloads. The attached metaclass's native singleton-name check
is explicit in general dispatch; kernel-checked table coverage supplies it for
all existing query selectors without a new guard. These modules are mandatory.

ClassFrameActual, ClassMethodsActual, ClassScopeActual and ClassNameEntryActual
now repair the real callback-body frame, empty locals/ivars, self type/live bound,
saved frames, installed class/definition/exact tables, inherited definition hook,
lexical ClassScopeAt and name absence. Scope uses main's actual cref=[]; DefsOk
retains its main-singleton selector exclusion. All four are mandatory.

ClassConstScopeActual and ClassTablesActual now repair real lexical constant
resolution and first-order constants/paths/nested-class transfers. Fresh own
constants fall through to Object's retained ancestor lookup; all new/old global
lookup cases and fresh-metaclass missing-constant fallback are proved. Existing
ClassTablesFrame premises remain unchanged. Both modules are mandatory.

ClassMetadataActual now retains constant-table-invariant old metadata projections
(map/any/bind), including allocator readiness/module flags. ClassMainActual
repairs main-site preservation with all 17 readiness fields, lookup/name/bare/
missing/constant/new-dispatch capabilities. Both are mandatory. Use an outgoing
heap variable plus equality to the actual heap to avoid deep record unfolding.

ClassDeclaredActual, ClassAllocatorsActual and ClassChainsActual now repair
existing declarations/own names/ordered chains, old allocator readiness, global
name growth, the fresh plain allocator, and empty-header selector/root-chain
publication. Fresh readiness uses Object's inherited flags. All are mandatory.

ClassStateActual.state now proves the full actual class-body StateOk (mandatory).
ClassHeaderStateActual.header publishes classHeaderCtx over it (mandatory).
ClassRunActual.class_actual_runSpec composes the whole actual class run (mandatory).
classDecl is enabled (classReachB guard discharges reachability).
memberDef, newDefault, callMethodSig, vcallMethodSig, ivarRead, initDef, newInst and InitJudge
(intLit/var/ivarAsgn/seq/ignoreResult/Seq.*) enabled (Constructor/NewInstActual).
moduleDecl enabled (Module/ModuleDeclActual). singletonDef/callSingleton(Implicit)
enabled (Singleton/SingletonRulesActual). Remaining big blockers: flow (closures:
literal now sets breakScope/pushes frame copy/blockCallK), scalarIvarAsgn
(frozen-receiver path runs inspect), subclassDecl. Denote/Controls/ConstructorControls still cites the removed constructor_body_entry.

Old instance_constants_old assumed an explicit Object fallback; current ordinary instance resolution follows ancestors instead.
Check the new-binding case with Object reachability/module fallback rather than
reusing that false simplification; existing ClassChains can supply physical
Object membership when the declared static ancestry resolves.

Retain ClassHeaderRun's original conformance/return structure. ClassRules currently
imports constructor/instance/singleton providers too; preflight also found missing
MainReady fields in SubclassMain, changed lexical constants in
SubclassConstants/MainReturn, positive DefsOk names in SubclassMethods, and binding/
entry metadata in singleton/constructor/instance rules. Class clinks stay gated.
AllocationReadyControls measured a complete legacy boot accept with Object
allocatorUnavailable=true: a checked fresh-class/new program raises TypeError.
It also measures attached/uninitialized/unavailable native construction failures
under the complete old PlainAllocator guard. PlainAllocator now requires
plainAllocationReadyB, with a metadata projection and preserved Ext/method/ivar
transports. MainReady.classFlags pins Object ancestryReady/allocatorUnavailable
for actual inheritance; real boot passes. The new controls are mandatory.
Use those facts to repair fresh class and subclass allocation; OrdinaryClass.plain
and Subclass.plain still need their new readiness premise. Actual registration
reads flags from its parent, while the legacy composite supplies defaults. Do not alter the interpreter
to restore the legacy composite. MethodChecked still
imports the historical Full bridge; BodyDispatch/FlowDispatch retain lookup drift.
Run Lake builds sequentially; concurrent rebuilds previously raced .olean files.

The entries below are historical checkpoints.

# Default active typed ratchet (2026-09-30)

run_typed_ratchet.sh now checks the active Bridge soundness theorem and reports
only enabled, certified clinks and production validateD accepts as climbed.
Disabled clinks/declined positive rungs are ascent, not gate failures. The default
retains checker/registry controls, generated-source freshness, fresh corpus
emission, Sorbet/upstream drift and negative controls, and CRuby agreement.
SoundnessAudit rejects axioms outside propext, Classical.choice and Quot.sound.

The former full-coverage gate is preserved as --full-corpus, with all historical
floors and audits intact. --clink-rebuild remains the proof/controls-only shortcut.
Denote/Report/Active uses actual indexed checker traces for gated dependencies;
no AST or hint-name guessing enters acceptance or progress. The default emits
fresh temporary corpus outputs so filtered runs do not count cached rungs.

Validation: the full default gate passes with 7/99 clinks, 8/261 corpus rungs,
46/46 negatives rejected and 254 CRuby agreements, 0 disagreements. Filtered
corpus runs also pass. Nonstandard axiom, wrong hint, negative-accept, Sorbet drift
and new upstream-error controls are rejected; --full-corpus still refuses a
partial registry. Policy/providers remain the seven-literal profile. Logs:
/private/tmp/active-ratchet-default-gate.log, active-ratchet-agreement-gate.log,
active-ratchet-controls.log and active-ratchet-full-audit-refusal.log.

# Generic validator/Bridge gating (2026-09-30)

Ascent now explicitly includes adding the clink to `clinkProfile`, making
`clinkEnabled rule = true`, alongside its proof/provider, required companion/body
admission and controls. See AGENTS.md §What counts as climbing a rung. A proved
but gated rule remains unclimbed in the active ratchet.


validateD now checks a constructor-derived rule trace rather than literal source
evidence. Ratchet/Audit covers all 99 constructors in all 17 authoring families.
Recursive, initializer, cached/rechecked and uniform callback-body premises carry
indexed traces. AuditBridge derives active certification from the same metadata;
the original Bridge endpoints and safety statements remain intact.

The authored checker moved to Check/Raw; generated Audit checker modules add
proof-indexed metadata. Regenerate with python3 scripts/generate_audited_checker.py
after editing Raw or its body/cache helpers. Both gates check freshness. The
literal-specific modules are removed. The shared seven-literal profile remains
unchanged; enabling compound rules no longer needs hand-written validator or
Bridge cases. Semantic providers and every premise rule must be enabled.

Validation: the seven-clink rebuild gate and main Bridge pass with standard
axioms. A temporary all-enabled checker policy passed the existing
Ratchet.Controls.DerivControls suite, including method/cache/class/callback cases.
Temporary ten-rule (sequence + last/cons) and nine-rule (cons disabled)
profiles also pass the rebuild gate and original runner-safety theorem. The
actual validate-one accepts one/two-element sequences with cons enabled; with
cons disabled it accepts only the one-element case. Sequence companion proofs
now live with their Sequence provider, avoiding unrelated Primitive/Hash imports.
The original seven-rule policy and providers were restored. Logs:
/private/tmp/generic-validator-{bridge,gate}.log and generic-full-checker-controls.log, generic-sequence-gate.log and
generic-sequence-no-cons-gate.log.
The full historical corpus gate still requires complete coverage with floors
intact. The entries below are historical checkpoints.

# Actual validator/Bridge gating (2026-09-30)

The user clarified that the desired endpoints are validateD and Bridge.lean,
not a separate literal-only API. Ratchet/ClinkPolicy is the shared pure policy;
Denote/Clink/Policy exports compatibility names. validateD now requires literal
source-rule evidence, policy permission and raw check success. The active seven
literals are accepted with matching hints; gated literals and compound/flow
wrappers are rejected by the production endpoint and adapters.

Bridge.lean proves the original validateD_safe, validateD_safe_boot and
validateD_safe_run statements with only active clinks and dependency imports.
The generic authoring-DJudge completeness helpers moved to Bridge/Full; their
existing consumers import that optional full-registry module. Bridge/Literal
is a compatibility wrapper around the original endpoints. No runtime or safety
statement changes; no new axioms. Current evidence supports the seven direct
literals. To admit a compound rule, extend its restricted evidence and bridge
case, including companion rules and checked/rechecked bodies. Enabling its clink
alone does not rebuild its checker evidence.

Run ./scripts/run_typed_ratchet.sh --clink-rebuild. It builds the actual bridge,
validator controls, ratchetd/validate-one and real runner-safety witnesses.
The full historical corpus audit still refuses partial coverage with original
floors intact. The entries below record the earlier separate-endpoint approach.

# Minimal semantic rebuild profile (2026-09-30)

The user requested selective clink gating and chose a minimal initial profile.
Policy.lean enables seven literals; 92 other constructors are gated. The full
census remains 99. ActiveProofs.lean imports only Context; FullProofs.lean retains
the former complete provider set. intLit anchors non-vacuity.

Run ./scripts/run_typed_ratchet.sh --clink-rebuild: PASS. Registry soundness,
literal validator controls, and Denote/Bridge/Literal's final runner-safety
theorem use only standard Lean axioms. validateActiveLiteralD requires ordinary
validateD acceptance, a direct literal hint, and an enabled literal rule.
The ordinary gate refuses this partial profile before the unrestricted checker
safety bridge. The existing validateD/pipeline remain unrestricted; no runtime,
corpus floor, comparator or full-gate check was weakened.
The three shared Integer dispatch simplifiers needed strCmpDefer?/strCmpTwin?
unfolding for the minimal base to compile; no other proof family was advanced.

To resume, add an exact rule name in Policy.lean, import its provider in
ActiveProofs.lean, repair that rule/dependencies and rerun the subset check.
Missing/wrong enabled proofs are errors. Disabled proofs never enter the registry.
Target's unavailable projections are False, with registration rejecting every
constructor that mentions one in a premise or conclusion. See Clink/README.md
for details. Restore clinkProfile := none and import FullProofs only when all
rules have been revalidated; the complete ratchet retains its original floors.

The literal bridge imports only the active registry, literal checker and boot
facts with their dependency closure. Its macro emits only active clink references;
disabled cases close from contradictory permission evidence. The final theorem
is validateActiveLiteralD_safe_run, for the actual Semantics.run at arbitrary
fuel. The probe checks each literal's acceptance against the active policy and
an accepted Integer program through that final theorem. A temporary Integer-only
profile (one active, 98 gated) also passes; the seven-literal profile is restored.
Compound rules still require a restricted derivation/body-checking witness before
the subset validator can admit them. The complete Bridge remains separate.

Logs: /private/tmp/clink-rebuild-{registry,final}.log;
/private/tmp/clink-full-profile-refusal.log. Pre-existing untracked files remain
outside this work. The following checkpoints describe the previous full profile.

# Scoped run_pushK restoration (2026-09-30)

The user requested run_pushK alone after the four dynamic-state changes, leaving
other proof repairs deferred. lake build Denote.Sem.Core.Answer passes (80 jobs),
including the full root-framing chain and run_pushK's standard-axiom audit.
Its statement and proof are unchanged. Log: /private/tmp/runpushK-targeted.log.

KontFrameBase holds the interpreter-only continuation definitions, re-exported
by Frame. AnswerBase/Decompose no longer pull in type-conformance transport;
SafeKont imports Frame explicitly to preserve its former API. This separates
the run equation from the unrelated BuiltinConformance failures encountered in
the initial build. No runtime, checker or admission changes were made.
The full typed gate and downstream typing proofs remain outside this task.

# Proof-repair checkpoint (2026-09-30)

The user requested a checkpoint commit of the current proof repair after being
informed that the full typed gate is still red. This explicitly authorizes the
checkpoint despite the normal green-before-commit rule. The original task is
not complete, and this checkpoint does not claim the soundness chain builds.

The complete Metatheory target and `scripts/check-proofs.sh` pass, including the
axiom audit and boot-heap probes. The replacement root-execution framing chain
reaches stepFn; legacy KontFrame paths now re-export the corrected helper API.
Boot readiness and answer-based root-run decomposition now pass. Ordinary method
entry and entry with a supplied block model the actual frame metadata and require
explicit exclusion of block-defined methods and for-loop targets. Fresh-site
producers retain the new after-builtin bound; singleton/inherited method writes
carry native exception-initializer preservation. Several consumers remain blocked
by failing dependencies, so those edits are checkpointed without a green claim.

Latest validation: the method-entry, block-entry, Answer, Boot and TopMethodInstall
batch passes (235 jobs); `scripts/check-proofs.sh` passes. The full typed gate
still fails at the proof-build stage before CRuby replay. BoundedPrimitive is
blocked by MethodReturn; class/module sites and controls are blocked by their
lexical-lookup and entry dependencies. Remaining work includes method return/body
composition, method-code metadata propagation, declaration/constructor callbacks,
closure frame allocation and capture preservation, and effectful frozen errors.
Logs: `/private/tmp/proof-checkpoint-{green-targets,targets,metatheory,gate}.log`.
See `../model/HANDOFF.md` for the continuation-design direction.

The user subsequently authorized the necessary main-singleton correction and
continued end-to-end repair in small commits on 2026-09-30, while retaining all
top-level theorem statements. The main-name guard and regression controls are
applied; further metadata/helper repairs are authorized within that task.
No corpus floor or gate may be weakened. The detailed root proof-changes.md
audit remains uncommitted at the user's request.

# Historical typed-fragment checkpoint (2026-09-27, clink 246 / model L275)

Native Symbol conversion/entry/forwarding now have semantic proofs in
Rules/Closure/Symbol and SymbolBody. Guarded native dispatch includes Symbol#to_proc;
reserving the name withdraws that capability. Allocation preserves full StateOk.
callClosure's actual required/rest frame allocates its rest Array, has no capture
fallback, and forwards every remaining argument through the real splat path.
The all-fuel body contract consumes the underlying callee StepSpec. Return lemmas
project certified framing and recover uncaptured caller locals after the block pop.
Mandatory SymbolClosureControls covers the native path and its negative assumptions.

Full quiet gate GREEN: unchanged fragment 94/261, checker reach 95, 99 rules,
72 worked proofs, zero owed/exempt, 254 agree / 0 disagree. Metatheory and
standard-axiom audit PASS. New proof modules build under two seconds; no proof
exceeded five minutes or raised a resource limit. Logs:
/private/tmp/ratchet-symbol-entry-{gate,audit}.log. No live builds.
Paused after clink 246 at the user's request; do not continue until asked.

Next: 096 still needs map integration and source admission. MapArrayContract assumes
one required formal; adapt it to the proved native entry rather than changing the model
or substituting a lambda. Discharge Integer#to_s's call, preserve the typed accumulator,
and restore full caller StateOk after both pops. Symbol entry reads lexical metadata
from frame zero, not necessarily the active caller; its body proof uses only the two
bound locals and explicit dispatch. Do not assume attached-block ClosureScopeEq.
Sorbet 0.6.13405 gives map(&:to_s) Array[String], rejecting missing selectors (7003)
and missing forwarded arguments (7004). Then 097 is stored-lambda block passing.

Previous model repair (clink 245):

Before typing 096, measured §F56: &:symbol bypassed overridden/private/undefined
Symbol#to_proc. Interp/BlockPass now runs conversion through lookup and continuations,
including the checked response-hook/method_missing path; invalid results raise TypeError.
Native Symbol#to_proc has one capture-free allocator. No checker rules or admissions change.
New framing proofs cover conversion and its exception boundary; two regression programs
exercise side effects, argument order, keywords, overrides, missing hooks and mutation.

Next: type 096 on the repaired path. Native Symbol closures have captured=none and
required/rest formals; attached iterator proofs currently assume a captured caller and one
required formal. Prove native conversion readiness, capture-free entry, rest allocation,
the underlying Integer#to_s send, and caller restoration before adding a source judgment.
Then 097 is stored-lambda block passing. Keep every new judgment tied to measured Sorbet.

Full quiet gate GREEN: fragment 94/261, checker reach 95, 99 rules, 72 worked proofs,
zero owed/exempt, 254 agree / 0 disagree. Metatheory and standard-axiom audit PASS.
MRI tier 0 improves to 999 agree / 0 disagree, 304 unsupported. Both new regressions
agree; three unrelated regression mismatches reproduce identically at dfa5116.
New framing module builds in 674ms; no five-minute proof or new resource limit.
Logs: /private/tmp/ratchet-blockpass-{gate,audit,tier0,regressions}.log. No live builds.

Previous admission (clink 244):

Explicit named-&b source calls now pass validateD, admitting 095, 157 and new 261.
DMethodFlow/Seq join DJudge's mutual
group; DFam has seventeen fields and the shared Certify script covers fourteen mutual
families. The new source rules interpret every body premise through that same registry.
Semantic families/rules moved to Judgment/MethodFlowRules, avoiding a bridge import cycle.

BoundCallbackCache retains all-code body certificates and rechecks every declaration after
context changes. Source blocks get parameter types only from those checked signatures;
actual body/result/capture checks are unchanged. Branch cache equality includes explicit
block domains/results. srb_sigs now preserves named block signatures separately from value
types; the emitter uses those declarations and never chooses them from a callback call.

The checker falls back to existing DMethod rules only when every local type is fixed and
code-independent, with first-order output guards and conservative alias loss. New corpus 261
copies b, clears b, calls the copy, clears it, then yields: the live method-frame block remains
available, and both invocations write a captured Integer. Together with 095 it supplies real
whole-corpus coverage for all eleven new rules. No coverage exemption was added.

Mandatory controls cover successful aliases/overrides, forged children/domains, wrong arity,
hidden captured retyping, missing/stale caches and context refresh. All 53 pipeline controls
pass, including uncalled wrong domains and unchanged definition hints across different actual
callbacks. No model defect or runtime change was required.
Sorbet 0.6.13405 rejects 261's final yield after b=nil (7003), equating it with a call on
the overwritten local. CRuby 4.0.5 and the model retain the method-frame block and agree on
total=12. The new rung records that measured Sorbet rejection, like the implicit-yield rungs.

Next: rung 096 (symbol-to-Proc block passing), then 097 (stored lambda block passing).
Measure the actual model/CRuby/Sorbet path before adding a judgment. Current named-&b admission
is a lone named block formal with zero positional method arguments and one-argument callback
calls; primitive/yield fallback requires no remaining symbolic callback-valued locals.

Full quiet gate GREEN: fragment 94/261, checker reach 95, 99 rules (42 expression + 57
companion), 72 worked proofs, zero owed/exempt, 254 agree / 0 disagree. Metatheory and
standard-axiom audit PASS. Floors raised. Logs: /private/tmp/ratchet-boundadmit-{gate,audit}.log.
No live builds. New proof modules build under a second; RuleAudit takes 25 seconds.

Previous foundation (clink 243):

FlowDefine/FlowDispatch/FlowSource now compose the all-code explicit-block body certificate
with real source installation, DefsOk lookup, literal block allocation, &b entry and return.
Allocation proves native Proc class separately from payload/code; the shared finishSend proof
handles lambda/proc/new overrides and re-establishes lookup after allocation for new.
Source calls recover capture slots from LocalFacts and restore full caller conformance.

Mandatory BoundSourceControls proves exact 095 from boot plus lambda/proc/new overrides.
Four further whole-source proofs cover copied/restored aliases, receiver sequences and saved
receivers, with captured writes for every initial Integer and a renamed callback parameter.
The 095 proof's Expr matches the pipeline AST. CRuby 4.0.5/model agree on 6/6/6/6 and
12/12, 5/5, 5/5, 12/12. Sorbet 0.6.13405 accepts all except its special new call (7035).
No new runtime defect or model change. These are semantic source proofs, not validateD admission.

Next: join DMethodFlow/Seq to the mutual judgment/registry, add source definition/call rules,
cache complete explicit-block certificates, and emit/check 095. Keep definition checking
independent of actual callback code/captures, context-refresh checks and zero coverage exemptions.
Every new rule needs real whole-corpus coverage, including alias/sequence/nil/write paths;
the staged embed constructor has no executable path yet. Preserve existing implicit blocks.
Before registry imports, move the semantic family definitions out of FlowBridge to an acyclic
Judgment module; FlowDefine/FlowSource currently import that staged bridge. Mirror BodyCallRule
for the source-call constructor so both body premises cross the shared registry family.

Full quiet gate GREEN: unchanged fragment 91/260, checker reach 94, 88 rules, 70 worked,
zero owed/exempt, 253 agree / 0 disagree. Metatheory/standard-axiom audit PASS. Logs:
/private/tmp/ratchet-boundsource-{gate,audit}.log. New modules build under a second; no live builds.

Previous foundation (clink 242):

checkBoundCallbackBody now checks lone named-&b definitions without actual callback code,
captures or call values. MethodLocalTy keeps fixed first-order types and an opaque callback
type; instantiation retains the exact code-only closure type. Capture invalidation is proved
code-independent and matches envAfter. Certificates quantify over every ClosureCode.

Staged DMethodFlow/Seq interpret through SemMethodFlow; embedded DMethod crosses its existing
registered bridge. The executable checker supports Integer/nil/local leaves, assignment,
flat sequence and one-argument call/[] from an identity-proved receiver. It checks exact
argument types, not subtyping. Primitive/yield branches and ordinary method parameters are
not implemented here. The old implicit-block checker is unchanged.

Mandatory controls reject forged hints, missing/overwritten receivers and wrong signatures;
five checker-produced bodies feed real boot calls with captured writes for all initial
Integers. Sorbet 0.6.13405 accepts an uncalled Integer-domain body and rejects its String-domain
counterpart (7002). The checker has no actual callback with which to specialize either body.
No runtime defect or model change was needed. validateD still declines explicit &b definitions.

Next: whole-source definition/lookup/literal-block dispatch from CheckedBoundCallbackBody,
then mutual registry/cache/emitter integration and 095 admission. Preserve full declared-domain
checking and whole-corpus coverage of each newly registered rule. Counts/floors are unchanged.

Full quiet gate GREEN: fragment 91/260, checker reach 94, 88 rules, 70 worked,
zero owed/exempt, 253 agree / 0 disagree. Metatheory/standard-axiom audit PASS. Logs:
/private/tmp/ratchet-boundbody-{gate,audit}.log. New modules build under a second; no live builds.

Previous foundation (clink 241):

SemMethodFlow now threads CallbackFacts (method locals equal to the actual supplied block)
and a result-identity flag separately from Env. Scalar/variable leaves, assignment, flat
sequence and general receiver call/[] are proved. Assignment removes only its target's old
fact and records the result's proved identity. A fallback from arbitrary SemMethod drops
all aliases; its output closure types alone cannot recover identity.

MethodRunWith carries these facts without weakening MethodResultOk. The shared checked
callback and native invoke proofs now expose CallbackFramed as a value postcondition, so
callbacks preserve method aliases even while writing the captured caller. FlowCall saves
receiver identity before a flow-typed argument and retains the argument's outgoing aliases
after callback return. FlowEntry supplies the singleton &b alias at real enterUserMethod.

Mandatory CallbackAliasControls proves copy→wipe→repeated calls, restoring b from its copy,
an arbitrary receiver sequence returning the copy, and overwriting a copy inside an argument.
Body proofs quantify over every matching CheckedCallback; boot instantiations perform stable
captured writes for every initial Integer. A nil-typed local cannot satisfy the alias contract.
Sorbet 0.6.13405 accepts all four probes; CRuby 4.0.5/model agree on 12/12/5/5/5/5/12/12.
All new modules build under a second with standard axioms. No model change was needed.

Next: connect these flow facts to definition-side syntactic method checking and the registry,
then cache/emitter/source admission of 095. Keep complete declared-domain checking independent
of actual callbacks. Explicit entry's Env contains cb.code; the new uniform semantic body
controls demonstrate code independence but are not an executable definition checker. Existing
SemMethod yield/primitive rules remain available through the conservative embed; preserving
aliases across those operations needs the corresponding postcondition proof. No floor changes.

Full quiet gate GREEN: unchanged fragment 91/260, checker reach 94, 88 rules, 70 worked,
zero owed/exempt, 253 agree / 0 disagree. Metatheory/standard-axiom audit PASS. Logs:
/private/tmp/ratchet-callbackalias-{gate,audit}.log. No live builds.

Previous foundation (clink 240):

Explicit &b entry and actual call/[] execution now have semantic proofs. BodyBoundCall
tracks MethodCallbackReceiver (the actual frame block plus native Proc class) through
MethodEffects, saves it before arbitrary SemMethod argument evaluation, and composes
real invoke/callClosure/blkFrameK. checked_callback_method_run now permits any break
owner. Code-only closure types alone identify neither the value/capture nor native lookup.

BoundEntry proves enterUserMethod's real &b predeclaration/binding, complete singleton
EnvOk at the exact closure-code type, and entry/body/return composition. BodyEntry factors
enterBindings without weakening any frame or state contract. Mandatory BoundCallbackControls
proves direct call, receiver-local overwrite, [] and a yielding argument from boot, all with
stable captured writes and every initial Integer. A prior nil overwrite refutes the binding
contract. New modules build under a second with only the standard axioms.

CRuby 4.0.5/model agree on direct/overwrite/copy/bad-binding/captured-write probes
(6/6/6/missing/5/5) and bracket/nested-callback probes (5/5/10/10). Sorbet 0.6.13405 accepts
the valid typed versions and rejects a call after b=nil (7003). No new runtime defect.

Next: binding identity tracking through general method-body typing, then definition/cache/
checker/emitter/source integration for 095. SemMethod's plain Env does not carry actual
block-reference identity. The explicit entry environment also depends on cb.code; retain
uniform declared-domain checking when designing that extension. Do not treat code-only
closure typing as identity, silently re-read b after arguments, or bypass native dispatch.
Current semantic controls do not admit 095 or change any floor.

Full quiet gate GREEN: unchanged fragment 91/260, checker reach 94, 88 rules, 70 worked,
zero owed/exempt, 253 agree / 0 disagree. Metatheory/standard-axiom audit PASS. Logs:
/private/tmp/ratchet-boundcall-{gate,audit}.log. No live builds.

Previous admission (clink 239):

Rung 094 is now accepted by validateD. DMethod/DMethodAll/DMethodSeq share DJudge's
mutual group and join DFam; defBlock and DFlow.callBlock consume uniformly checked method
bodies and independently checked actual callbacks. All 88 rules (41 expressions + 47
companions) are registered. The shared Certify macro supplies identical recursor cases to
the ordinary and method bridges; BodyBridge now interprets the latter through the registry.

CallbackCache stores exact context/spine/code/signature proofs. Definitions and scope exits
recheck old callback bodies at unchanged domains; branch cache equality includes block
signatures. Calls check source parameter shape, callback result, physical capture slots and
the outgoing caller fixed point. The emitter proposes scalar block results from definition
bodies alone, preserving positional/result annotations; call values never specialize them.

New corpus 260 combines method-local nil→Integer retyping with repeated writes to a same-named
outer capture. Worked registry proofs for 094/260 cover all method constructors; the zero
unexercised ceiling stays intact. Mandatory controls reject forged source/signature hints,
wrong callback results/arity, captured type changes and stale caches; later-definition replay
and lambda/proc/new overrides pass. Sorbet 0.6.13405 accepts 260's explicit typed &b counterpart;
implicit 094/260 retain expected Sorbet rejection (5082/7035/7003). CRuby/model print 4/3.

Next: explicit &b binding and Proc dispatch inside the method (095). Current source calls
have zero method arguments and a required-positional literal callback; yieldOne uses one
argument. Blocks retain a first-order fixed caller environment, and calls drop LocalFacts.
No new model defect was exposed. Keep declared-domain checking independent of actual calls.

Full quiet gate GREEN: fragment 91/260, checker reach 94, 88 rules, 70 worked proofs,
zero owed/exempt, 253 agree / 0 disagree. Floors raised; metatheory/axiom audit PASS.
The shared bridge builds in about two seconds, RuleAudit in 19. No live builds.

Previous foundation (clink 238):

Clink 238 proves the complete definition/implicit-literal-block source path. BodyDispatch
resolves installed ordinary methods before and after reification, including lambda/proc/new
interception, then enters the uniformly checked body with the actual callback. BodySource
uses LocalFacts to derive physical capture ownership and returns full caller StateOk.
BodyDefine requires the complete signature-domain body proof before installation; the
shared top_definition helper preserves the existing ordinary defDecl interface.

Mandatory CallbackSourceControls proves exact 094 from boot, plus lambda/proc/new overrides
and repeated captured writes for every initial Integer. No entry-state or lookup assumption
is supplied. All five proofs use only standard axioms; the module builds under a second.
CRuby 4.0.5/model agree on 30/4/3/30/30/30. Sorbet 0.6.13405 accepts annotated twice,
lambda/proc overrides and stable captured writes, rejects a String callback result (7005),
and applies its constructor rule to the user new probe (7035). This is documented separately
from the model's actual dispatch. No new runtime defect was found.

Next: integrate DMethod into DJudge's mutual group/DFam and register definition/call rules
with worked corpus coverage, then wire the checker and emitter for 094. Keep the zero
unexercised ceiling; controls alone do not satisfy corpus coverage. Existing source proofs
are semantic and do not yet make validateD accept 094. Explicit &b syntax/entry remains
unsupported. No runtime, registered-rule or floor change is claimed.

Full quiet gate GREEN: unchanged fragment 89 / checker reach 93, 77 rules, 68 worked,
zero owed/exempt, 252 agree / 0 disagree. Metatheory/axiom audit PASS. No live builds.

Previous foundation (clink 237):

Clink 237 adds CheckCallbackBody with proof-producing expression/list/sequence checking.
Deriv.defBlock carries proposed positional/block/result signatures; yieldArgs carries only
argument certificates. Every literal, name, arity and primitive type claim is rechecked.
CheckedCallbackBody pins the complete declaration at its required-positional input domain,
block signature and result. No caller locals or argument values enter definition checking.

CertifiedMethod optionally retains an ordinary DJudge proof for every callback code. This
allows existing array typing when all elements are ordinary; a yielding element has no such
proof and is declined. Assignment's default-code decision is justified by callback_capStale,
which proves that guard independent of the code. All other context/spine guards remain.

BodyChecked interprets a checked artifact and proves its actual zero-positional method entry.
All six MethodTypingControls boot proofs now consume executable-checker artifacts, including
repeated/nested captured writes, string allocation, saved arrays and division escapes.
Mandatory CallbackBodyCheckControls pins forged hints/signatures, whole-domain rejection,
fuel/arity/plainness, wire decoding and unchanged top-level rejection. Sorbet 0.6.13405 accepts
uncalled `yield(value)` at Integer and rejects a nilable domain (7002). New modules build
under a second; boot controls about five seconds, standard axioms only.
Full quiet gate GREEN: unchanged fragment 89 / checker reach 93, 77 rules, 68 worked,
zero owed/exempt, 252 agree / 0 disagree. Metatheory/axiom audit PASS. No live builds.

Next: definition installation/lookup and source calls with implicit blocks (094), then &b
binding/admission. checkCallbackBody currently requires positional-only definition syntax;
an explicit &b is rejected. The six entry proofs still begin after dispatch, with actual
block allocation. DMethod remains staged: retain the zero unexercised ceiling and add it to
DJudge's mutual group/DFam only with whole-program coverage. No new validateD acceptance yet.

Previous foundation (clink 236):

Clink 236 stages DMethod/DMethodAll/DMethodSeq: ordinary, assignment, flat sequence,
primitive send and one-argument yield, plus list companions. The signature uses argument
types and return type, with no callback code, local parameter names or captured environment.
Ordinary premises quantify over every callback code; BodyBridge interprets them through
djudge_context and proves all nine new constructors semantically by mutual induction.
SemMethodBody instantiates a derivation at any matching CheckedCallback; a bare arrow
still supplies no safety proof. Registry remains 77 rules (40 expressions + 37 companions).

MethodTypingControls derives all six source bodies syntactically and takes their boot
proofs through this bridge. The same twice derivation also admits a callback with different
code, parameter name and captures. Sorbet 0.6.13405 accepts the uncalled annotated bodies
and rejects the uncalled String-operand body (7002); a renamed block parameter is accepted.
New modules build under a second; controls about five seconds, standard axioms only.
Full quiet gate GREEN: unchanged fragment 89 / checker reach 93, 77 rules, 68 worked,
zero owed/exempt, 252 agree / 0 disagree. Metatheory/axiom audit PASS. No live builds.

The first gate refused registration because these rules have no worked whole-program corpus
witness yet. Keep the zero unexercised ceiling. Registry's dUncarriedJudgments names all three
staged families, preventing a raw premise from bypassing DFam; a negative control pins this.
Next: executable definition-body checking, installation/dispatch and &b binding, then complete
source admission. Move DMethod into DJudge's mutual group when definition/call constructors
depend on it, add all three DFam fields and certify them with whole-program coverage.
No new validateD acceptance yet.

Previous foundation (clink 235):

Clink 235 adds SemMethod.prim for every existing DPrim row, allowing yielding receivers and
arguments. BodyPrimitive derives receiver-type retention from MethodEffects.firstOrder,
then reuses primitive_frame and full caller restoration at actual dispatch. BodyOrdinary's
RunSpec.methodOrdinary handles arbitrary ordinary entries; the existing expression wrapper
delegates to it. MethodActivation.reCtl and RunSpec.inMethod package that boundary.

BodyLists defines SemMethodAll and SemMethodSeq, with proved flat-sequence execution and
the final empty marker. Argument companions retain plainArgB; primitive rows currently have
zero/one argument. MethodTypingControls now uses the actual flat mixed body and proves
YieldBody.twice (`yield(1)+yield(2)`) through general source rules. Generic call/boot controls
also cover `yield(1).to_s.length`, a saved array indexed by yield, and division raising
ZeroDivisionError. Every initial captured Integer is covered for all fuel. Sorbet 0.6.13405
accepts the annotated probes and rejects a String right operand (7002); CRuby/model output
4/3, 1/1, 20/1, zero/0. New modules build under a second; expanded controls about five seconds.
Full quiet gate GREEN: unchanged fragment 89 / checker reach 93, 77 rules, 68 worked,
zero owed/exempt, 252 agree / 0 disagree. Metatheory/standard-axiom audit PASS. No live builds.

Next: syntactic method-body judgment and definition checking, then installation/dispatch,
&b binding and checker/emitter admission. Semantic source composition now covers the 094
body; no new validateD acceptance is claimed. CheckedCallback must come from a checked body,
not a Proc arrow's partial-return denotation. Keep uncalled definitions checked too. The
current entry is zero-positional, main caller, same owner/cref and absent superName/capture.

Previous foundation (clink 234):

Clink 234 supplies the general semantic source layer. MethodPres retains caller slot domains,
both scopes and actual Proc payloads across MethodEffects. BodyContext packages CheckedCallback
(exact code, checked body, activation guards/capture fixed point) and MethodActivation (original
caller anchor, full method/caller states, scope and actual callback/capture). after derives the
next activation from MethodResultOk, so a later yield may follow arbitrary method-local writes.

SemMethod proves ordinary expression embedding, binary sequence and real method return.
BodyAssign adds assignment around any SemMethod expression with the existing closure/alias/
context guards and unchanged ivar spine. BodyYieldOne evaluates a checked argument before the
actual callback; Plain excludes splat/kwargs/fwd syntax. yieldInt is now its specialization.
BodyEntry proves zero-positional method entry/call for an arbitrary SemMethod body. It checks
superName=none alongside owner/cref and the actual entry's params/capture/declared metadata.

Mandatory MethodTypingControls constructs source proofs for local retyping around two yields
and for `yield(total = yield(1))`, then proves real allocation/entry/return from boot for any
initial captured Integer. Both method and caller can write total independently. Sorbet 0.6.13405
accepts both; CRuby/model print 4/3 and 2/2. A nil argument is rejected by Sorbet (7002).
New modules build in about a second, controls under four seconds, using standard axioms.
Full quiet gate GREEN: unchanged fragment 89 / checker reach 93, 77 rules, 68 worked,
zero owed/exempt, 252 agree / 0 disagree. Metatheory/axiom audit PASS. No live builds.

SemMethod is semantic only; none of these examples is a new validateD acceptance.

Previous foundation (clink 233):

Clink 233 embeds ordinary SemSafeCtxA and checked source yields into MethodRunSpec.
BodyOrdinary derives caller StateOk after ordinary method expressions using the current
caller environment and a framing origin before method allocation. MainReturn's new internal
atStack_frame helper accepts the caller's FrameOk independently of saved scope metadata;
the old return interfaces are preserved. CallbackResultOk.methodResult retains both states.
BodyYield proves required-callback execution and source yield with an Integer argument.
RunSpec.bindMethod and MethodRunSpec.seq handle actual continuations and escaping raises.

Mandatory MethodBodyControls proves a checked captured Integer write followed by insertion
and nil-to-Integer retyping of a same-named method local, then the real method return.
Sorbet 0.6.13405 accepts this typed &b probe; CRuby/model agree on return 7 / caller total 1.
No runtime/rule/floor changes. New modules build in about one second with standard axioms.
Full quiet gate GREEN: fragment 89, checker reach 93, 77 rules, 68 worked proofs, zero
owed/exempt, 252 agree / 0 disagree. Metatheory and axiom audit PASS. No live builds.

The original caller anchor must persist through composition; CallbackFramed describes only
the suspended interval of one callback, not a whole method with local writes.

Previous foundation (clink 232):

Clink 232 establishes the general effect/run target for methods with callbacks. MethodEffects
composes ordinary Framed and CallbackFramed. MethodEffects.project restores ordinary caller
framing from before method allocation, requiring origin.frames.size ≤ active method id.
It preserves the original frame prefix while allowing fresh method locals and callback writes.
BodyRun defines MethodResultOk/MethodRunSpec with typed caller AND method state on values,
all-fuel safety and MethodEffects. Step, answer, bind/bindSpec and methodReturn are proved.
These live in Rules/Method so the judgment layer does not import rule proofs.

Mandatory MethodEffectsControls mixes real writes to method and captured caller, then inserts
a new method local. It proves the distinct reads/slots and full original-caller framing.
It refutes Framed at the method, CallbackFramed over the whole body and a caller anchor that
already contains the method. Normalizing intermediate machines avoids repeated reduction;
new proofs remain under default limits. No runtime/rule/floor change; metrics remain 89/93,
77 rules, 68 worked, zero owed/exempt. Full quiet gate GREEN (252 agree / 0 disagree);
metatheory and standard-axiom audit PASS. New modules build in under a second. No live builds.

The clink 231 twice pilot is the execution-path regression. Sorbet accepts mixed
method-local retyping and stable captures:
`first=nil; first=yield(1); second=yield(2); first+second`, with typed &b; CRuby/model print 4/3.

Clink 231 proves the actual 094 body and post-dispatch method entry with checked callbacks.
StateOk_reframe_block supports an independently typed actual block; its existing scopes
wrapper retains the old interface. callbackMethodCtx records exact code-only block typing
and method identity. CallbackResultOk.methodState restores the active method's full state
after a callback, including stable/code-only closure locals. An absent block type cannot
describe a method with a block; the new mandatory control rejects that false conformance.

YieldInt handles source Integer arguments and retained Proc descriptors. YieldBody.run
composes `yield(1) + yield(2)`, saved result, native addition and method return for all fuel.
BlockEntry's requiredBlockFrame includes blk AND callBlk. YieldCall.call supplies actual
enterUserMethod entry, caller capture ownership and full method conformance. Mandatory
YieldMethodControls allocates blocks and proves arithmetic and captured-write variants
from boot (arbitrary initial Integer for the latter). CRuby/model print 30, 4, 3 as expected.
No new judgment/admission; fragment 89, checker reach 93, rules 77 and worked proofs 68.

Next: a general method-body effect contract, then definition checking, installation/lookup,
source-call composition, &b binding and checker/emitter admission. CallbackFramed describes
a suspended method across ONE callback; its active-frame equality cannot describe arbitrary
method-local assignments. Both the method's own locals and callback capture writes must be
allowed while restoring the original caller on return. Do not weaken existing Framed or
replace the generic judgment with a hard-coded rule for the twice pilot.
Validation: full quiet gate GREEN (252 agree / 0 disagree); metatheory and standard-axiom
audit PASS. New proof modules build in about three seconds or less. No live builds remain.

Clink 230 adds an entry/return proof layer for yield across an ordinary method. §F55 is
a proof-contract obstruction: the runtime already agrees with CRuby on repeated yield
updating an outer Integer while preserving a method local. CallbackFramed preserves the
complete method frame, projects Framed to the captured caller and pins its slot domain.
CallbackCaller derives required-arity block entry, full caller return and the next-call
invariant from a checked body and a capture-type fixed point. typed_yield_continue composes
actual doYield/blkFrameK with a continuation receiving both frames' guarantees. methodReturn
pops the method marker. TypedYieldControls is mandatory and proves a source yield with a
captured write for all fuel, refutes ordinary method isolation and rejects method damage.
No new judgment or corpus admission; metrics below remain unchanged.
Full quiet gate GREEN and metatheory/standard-axiom audit PASS. New proof modules build
in under a second. No live builds remain.

Next: compose callbacks with ordinary expressions in a method-body contract, then definition
checking, attached-block dispatch and &b binding. Do not put yield directly under the old
SemSafeCtxA method framing: method_isolation_false is the counterexample. Existing arrow
denotations give partial-return typing, not call safety. Sorbet 0.6.13405 accepts stable
captured Integer writes with typed &b, rejects type changes (7001) and nil yield arguments
(7002); exact 094's missing block annotation has its expected Sorbet rejection.

Latest admissions: 092-block-map-to-s and 093-block-doend-with-block-local. Fragment 89,
checker reach 93, 77 registered rules (40 expressions + 37 companions), 68 worked proofs,
zero owed/exempt. Safe prefix remains 17; 018 is correctly rejected.
Final full quiet gate GREEN (252 agree / 0 disagree); direct validate-one checks accept
092/093. Metatheory and standard-axiom audit pass. No live builds remain.

Clink 229 registers DFlow.map through SemFlow.map and djudge_certified. mapBlock carries
only receiver/body derivations. FlowCheck derives parameter types from the checked Array,
checks the exact body and takes its result type for the output Array. It enforces native
selector/name readiness, main scope, first-order input/result types, capture ownership,
stable context/spine and closureReturnEnv = caller Env. The emitter shares setup/restoration
with each while returning Array[body result] for map/collect. MapCheckControls and 45
pipeline controls cover type independence, chained maps, captures, shadowing and rejection.
MapDerivations proves exact 092/093; CorpusSafety and RuleAudit include them. Four floors
are raised. Native map/collect use model L274's repaired lookup/live cursor (§F54).

Next frontier: 094 yield, 095 &block parameter, 096/097 block-pass, or 100 higher-order
method arguments. 094 calls a method that adds yield(1) and yield(2); 095 calls a typed
Proc captured as &b. Both need a typed block across an ordinary method activation, beyond
the current main-caller native iterator path. Measure Sorbet before extending judgments.
Nested map (101) still needs captured block-caller conformance and flow-aware body hints.
Do not widen closureMainB or rescue this in the emitter without the corresponding proof.

Sorbet 0.6.13405 --no-config: Integer→String map returns Array[String]; Integer→Integer
collect and stable captured Integer writes return Array[Integer]. Captured Integer→nil
is rejected (7001). DFlow.map's docstring cites the clink 228 measurement.

MapArrayContract uses fuel induction over the live cursor and typed accumulator. Shared
IteratorCaller entry/return facts (Caller.lean) preserve capture ownership and caller types;
each now uses the same proof. typed_map_step transports prior results via relative Framed
and the current result via FirstOrder, then array_alloc_result proves final allocation.
MapStart/MapDispatch/FlowMap reach L274's real native marker, with map/collect rows guarded
by nameFreeN in StateOk.dispatchMethods. SemFlow.map requires one required parameter, no
arguments, main scope, first-order input/result types, stable body context/spine and a
closureReturnEnv fixed point. TypedMapControls proves exact 092 plus collect, allocation,
shadowing and dispatch controls. Clink 229 adds registry/checker/emitter acceptance.
Clink 228 validation: full quiet gate GREEN with unchanged floors and 252/0 agreement;
metatheory and standard-axiom audit pass. New proofs take about a second each.

Clink 227 registers DFlow.each through SemFlow.each and djudge_certified. eachBlock hints
contain only receiver/body derivations. FlowCheck derives the parameter type from the
checked array, rechecks the exact source body, checks scope/spine stability and outgoing
capture types, and verifies closureReturnEnv = caller Env. The emitter proposes this hint
and restores the caller under shadowed names. Required-parameter arity is one, arguments
are empty, and explicit block-pass/other iterator names remain outside this rule.

LocalFacts.afterEffect preserves already bound slots across ordinary embedded expressions
using Framed.bindings, while dropping origins and exact slot domains. This was necessary
for a captured write after evaluating an array literal: discarding every slot fact rejected
`total = 0; [1].each { |x| total = total + x }`. Presence is proved from input facts and
framing, never inferred from EnvOk or a nil read. Each's final facts remain unknown.
EachCheckControls and 33 pipeline controls cover return/element independence, stable
captures, parameter/block-local shadowing and rejections. EachDerivations proves 091 through
the arbitrary registry family; Safety's predictor and RuleAudit cross-check it. All four
changed floors are locked in MainTyped/SemLadder; agreement remains 252/0.

Clink 226 proves the complete attached each source through SemFlow.each in
Rules/Iterator/FlowEach. TypedEachControls.source/source_boot instantiate the exact 091
program with all-fuel safety and full output conformance. StateOk's primitiveDispatchB
now combines nativeDispatchB (the old builtin/Proc rows) with eachDispatchB: when each is
free, Array lookup must miss. ArrayPayloadOk already fixes the dispatch class. Overrides,
inherited overrides and undef tombstones fail the new guard; reserving each withdraws it.
All heap/context producers retain this capability, including fresh classes/modules,
method installation and name reservation. Start proves caller conformance after allocating the inert iterator;
Dispatch reduces actual invoke to startIter; FlowEach reifies the attached block and uses
the receiver's final LocalFacts to classify captures. No extra loop/return premise remains.

Clink 227 connects the DFlow constructor, registry, checker and emitter. The semantic rule
requires one required parameter, first-order elements, the existing main-scope guard,
activation-stable/nonalias entry types, activation-stable outputs, and a closureReturnEnv
fixed point. Capture ownership uses fr.captureNames? on withoutNames shadow Γb; capture
facts come from receiver evaluation. Output facts are unknown. Do not replace the guarded
native miss with a payload-only or name-provenance assertion.

Clink 224 measured Sorbet's each contract: Integer parameter, original Array[Integer]
result despite a String body, captured type changes rejected. Zero parameters are accepted
and a second parameter is NilClass. The one-required-parameter semantic pilot is in
Rules/Iterator/Each; no new judgment/checker admission is claimed.

Clink 225 discharges the loop contract in Iterator.TypedEach. typed_each_step consumes
caller StateOk at popMethodFrame m, live array denotation, current capture, CaptureSlots,
activation-stable/nonalias entry types, stable outgoing types, and a checked body. The
closureReturnEnv fixed point enforces Sorbet's stable captured types. The body result is
discarded; the original array is returned. First-order elements survive arbitrary certified
body effects, including live payload growth. Iterator.Entry proves full block StateOk;
ReadReturn/ReturnEnv/ReturnState restore full caller state after both pops, including hidden
parameter values, captured writes, fresh body locals and alias erasure. Escapes preserve
caller framing without requiring a value-state postcondition. Controls instantiate the
Integer arithmetic body and a hidden nil caller slot, and reject changed capture types.

Clink 226 establishes typed_each_step's initial facts through actual dispatch and source
composition. An initial pushed iterator leaves an extra frame in the store even after pop;
iterator_push_caller_state accounts for it, including code-only closure-valued locals.
No StateOk is required or valid in general on the inert iterator itself.

§F53 exposed a model defect before rule admission: each snapshotted its arguments. L273
adds IterKind.arrayEach o index and reads the live payload/length after every yield.
Append/removal/replacement, nested loops and block exits agree in focused replay. Other
native iterator families are unchanged; check their fidelity before reusing this proof.
EachArrayContract carries an explicit live receiver/cursor invariant P. eachArrayStep_spec
uses fuel induction through actual blkFrameK/iterK/frameK, permitting unbounded growth.
Clink 225 derives its body entry, invariant restoration and caller conformance premises.
Iterator.FrameReturn supplies caller Framed/metadata after both pops. Do not impose
Framed on the intermediate iterator activation: IteratorFrameControls refutes its isolation
clause with an ordinary captured write. The relevant caller is popMethodFrame m, with the
iterator frame retained in the store; its id need not be fresh on later iterations.
Current formal loop uses one required
parameter; Sorbet's zero/additional parameter shapes need binding proofs too.

Clink 223 generalizes callClosure_required to both modes: exact required arity prevents
Proc autosplat, padding and truncation. The actual frame/continuation keep cl.lam. Native
dispatch is selector-specific for call/[] and guarded independently in StateOk; no runtime
change is needed. DFlow.requiredCall and its existing registry proof now accept both modes
and selectors. The emitter proposes Proc literals and calls, while the checker rechecks
their exact bodies at actual argument/live capture types. Wrong arity, unsafe types and
non-value jumps remain rejected; Ruby's lenient Proc arity is outside this Sorbet contract.
Worked proofs cover 089/090, and 21 pipeline controls exercise array/positional arguments
and rejection boundaries. Counts are locked in MainTyped/SemLadder; no new rule was added.

Clink 222 admits general required-parameter lambdas through validateD. DFlowAll is the ninth
mutual family; all twelve DFam interpretations, registry rules and bridge cases carry its
premises. FlowCheck reconstructs parameter types from checked arguments with exact arity,
rechecks the exact stored body at final caller types, and computes the shadowed return env.
Flow literals now retain code-only closure types; CurrentProc separately proves capture and
dispatch. Dropping creation-time capture claims permits stored captured lambdas while live
body checking still rejects changed-to-nil arithmetic. The emitter saves receiver code before
arguments and restores caller types under parameter/block-local names. requiredClosureCall
contains only derivation hints; no code, parameter type, origin or slot claim is trusted.
Worked registry proofs cover 088/098; 15 pipeline controls include receiver overwrite, earlier
arguments, shadowing and live captures. Counts are locked in MainTyped/SemLadder floors.

Clink 221 proves general required-parameter source calls. FlowArgs threads LocalFacts
through arbitrary-length arguments, retains earlier first-order values and a saved receiver,
and lets the final call change the outgoing caller environment. FlowSend evaluates the
receiver first and retains its exact descriptor/capture/dispatch through those arguments.
RequiredFlowCall checks the body at actual parameter types plus live caller captures, then
merges the caller/body return environments from clink 219. Block locals are shadowed too;
activationReturnB permits output aliases because return projection erases them.
RequiredFlowControls proves the exact 088 source, an argument-created capture, receiver-local
overwrite during arguments, and an earlier Integer argument surviving a later nil write.
Clink 222 connects these semantic proofs to judgment/checker/emitter admission and uses
code-only flow literal types to admit 098's stored capture. 097 still passes a block,
099 returns a lambda, 105 uses explicit return, and 107 deliberately mismatches arity.

Clink 220 strengthens ProcPres with exact dispatch-class retention alongside its payload
field. All Framed producers discharge both; CurrentProc.framed now carries a saved receiver
across arbitrary certified arguments. djudge_saved_proc_dispatch exposes it through the
bridge. activationStable_framed transports first-order/code-only closure types through
body effects, supplying the preserved-caller half of clink 219's return obligation.
Clink 221 supplies argument flow and general required-call composition. Native method
readiness still comes from the final StateOk; checker integration remains next.
No new callable shape is admitted yet. Future Proc eigenclass creation needs a weaker
effect-aware dispatch contract; current singleton rules operate on class objects.
For argument flow, adapt MethodArgs.startArgsKeep using RunWith's result postcondition.
Its finish callback needs output indices independent of the final argument state: the
block body can change caller-local types. Thread LocalFacts through every argument;
ordinary SemAllCtxA erases the origin/ownership facts needed by the final call.

Clink 219 computes closureReturnEnv from preserved caller types under parameter/block-local
names and projected body types elsewhere. Both parts erase aliases; withoutNames removes
all shadowed entries before capture ownership is classified. ReturnEnv proves full EnvOk,
including omitted nil slots; ReturnState attaches it to the actual block continuation.
ClosureReturnEnvControls combines a hidden nil caller slot, a changed capture, and an alias
to a disappearing body local, and rejects returning the parameter's type for the caller.
Clink 220 supplies saved Proc dispatch retention; general receiver/argument flow and
required-parameter calls remain next. Admission counts remain unchanged.

Clink 218 adds FramePres.shadows: an initially bound active name protects the value
of every saved same-named slot. BindingsPres makes it compose; local writes prove it,
and ordinary/constructor/current-closure returns retain it. djudge_shadows exposes it
for every certified answer. ShadowReturn proves a parameter/block-local name recovers
the caller's original value, including a hidden nil slot. ClosureShadowControls refutes
using slot/owner preservation alone and allows a different captured name to change.
Clink 219 supplies the merged return environment; general receiver/argument evaluation
and required-parameter calls remain next.
087's no-shadow projection remains intact; no new callable shape is admitted yet.
Sorbet 0.6.13405 infers untyped parameter/result for `->(x) { x + 1 }`, rejects wrong
arity, and accepts a String argument. The body must be checked at actual argument types.
ShadowPres does not apply to arbitrary Ruby: an older escaped closure can write a hidden
caller slot. The measured witness and the future effect obligation are in clink 218's notes.

Clink 217 adds DFlow/DFlowSeq to DJudge's mutual family and every registry interpretation.
The eight-family bridge proves all flow rules, including ordinary body premises. Check/FlowCheck
builds their proofs and calls the ordinary checker with smaller fuel for stored bodies;
Deriv.flow starts with unknown facts. The untrusted emitter proposes literal/call hints,
and call-time checking rederives types from exact source code at live caller bindings.
ClosureCheckControls covers body/return mismatches, arity/locals, copied/overwritten bindings,
unknown effects, forged origins, selector reservation and changed live capture types.
FlowDerivations adds 087's worked proof and exercises all flow companions through 006/031.
RuleAudit checks the corresponding syntax predictions against proof terms. Limits remain:
zero arguments, no block locals, main caller, activation-stable environments, first-order
results, and origins forgotten after ordinary effects/calls. General arity/return ownership
is next; do not weaken these guards to rescue an emitter candidate.

Clink 216 supplies the compositional semantic contract for local-flow checking.
RunWith carries a value postcondition through actual continuations; SemFlow threads
LocalFacts and result origin separately from Ctx. Literal, read, assignment, sequence
and zero-argument lambda call proofs compose. LocalFacts also tracks known-bound slots:
unknown complete slot layout no longer prevents calls whose output names are all bound.
FlowCall checks activation-stable types, main scope, native lookup, current capture,
and a body proof at live types; return projection is explicit and forgets origin facts.
ClosureFlowControls proves both stored call and copy/overwrite/call from unknown slots.
This supplied the contracts used by clink 217's judgment and checker integration.

Clink 200 proves actual lambda/proc creation for arbitrary parameters, block locals and
bodies. Sem/Closure/Reify retains the complete Closure and proves Ext, StateOk, capture
reads and creation self. Rules/Closure/Literal consumes name freedom at real lookup,
proves the source step, exact result metadata and all-fuel creation safety. Both files
ride the gate through ClosureLiteralControls. No callable judgment is admitted yet.

Clink 201 replaces Ty.clos's unused index with ClosureCode: exact supported params,
block locals, body and lambda mode. Ratchet/Lang/ExprEq is the old structural comparator
moved below Ty, with its soundness proofs. ClosureCode stores reflexive-comparison evidence,
so its BEq/DecidableEq are lawful despite conservative syntax coverage. The syntax bridge's
comparator proves ClosureMatches about the real payload; denM and closB now require it.
Existing allocation/local/control transports preserve it. Sem/Closure/Value proves full
EnvOk capture (including shadowed bindings) and reified_den; SemSafeCtxA.closureLiteral
returns the code-bearing type, and ClosureValueControls.stored_literal composes ordinary
assignment. No DJudge rule, emitter change or callable admission yet.

Clink 202 proves callClosure_required_lambda for arbitrary required-positional arity,
block locals, body and optional self/defmod overrides. requiredClosureFrame_getLocal gives
the actual parameter/block-local/capture lookup order. CaptureLive makes the finite live
parent chain explicit; reification extends that chain and frame pushes preserve it.
The body lookup consumes the extra frame's lookup fuel, retaining the old capture budget.
Controls exercise shadowing, argument order, arity, metadata and scope overrides.

Clink 203 strengthens EscOk to allow only non-type-error raises. All registered clinks
and the bridge prove the stronger contract; djudge_escape_only_raise exposes it for arbitrary
contexts and checked bodies. §F50's old witness remains as legacy_next_result; the actual
ResultOk rejects next and all other untyped jumps. Method/constructor/super continuations
now eliminate those impossible branches. Rules/Closure/Return proves the real blkFrameK
value/escape steps and composes a body RunSpec. Its caller framing (all answers), caller
StateOk (values), and first-order result premises are explicit; it does not assume isolation.

Clink 204 factors StateOk_reframe_scopes out of the existing ordinary-frame theorem,
retaining its old interface. Ctx.withoutRuntimeScope drops only runtimeMain/Class/Singleton
permissions, whose predicates require captured = none. ClosureScopeEq pins captured
self/block/cref/defmod to the conformant source; self/block types and lexical values remain.
Scope proves full StateOk transport. Environment proves parameter/block-local/capture
precedence with complete first-order, non-alias captures. State attaches full conformance
to callClosure's real next machine. ClosureStateControls instantiates a current capture
and boot entry, and refutes MainReady at a captured frame and EnvOk [] from an empty spine.
Constant lookup agreement is explicit when dropping the method frame; it is not inferred.

Clink 205 adds ProcPres to Framed and proves it for allocation, initialization, ivar writes,
method installation and class/module/subclass creation. djudge_saved_proc exposes exact
descriptor retention for every certified answer. Sem/Closure/Transport retains code, and
transports a full closure denotation given first-order capture/self types and unchanged
reads. An empty capture/self contract needs only ProcPres. ProcPresControls rejects code
replacement and shows that captured writes can invalidate typing despite retained payloads.

Clink 206 adds requiredClosureFrame_envOk_of_transport and requiredClosureFrame_state_of_env;
the old first-order APIs remain wrappers. Rules/Closure/Current derives complete capture
facts from the caller when cl.captured is its current uncaptured activation. Parameters,
block locals and all captured bindings must be non-alias and carry explicit type transport.
ClosureStoredControls proves actual allocation/assignment, payload lookup and full entry
for any supported zero-argument lambda body, retaining f at its exact closure type. The
boot Integer instance is non-vacuous under bootOkB. A dangling-capture control shows that
equal heaps/code do not transport arbitrary closure types across a frame push.

Clink 207 adds CapturePath and strengthens FramePres: saved frames retain every field
except locals, and frames outside a live capture chain remain unchanged. Liveness makes
path membership stable across frame growth. Local writes, composition, ordinary returns
and constructors prove the stronger contract. Rules/Closure/FrameReturn derives full Framed
after popping a closure that captures its uncaptured caller, plus saved caller metadata.
currentClosureFrame_runSpec discharges the block continuation's framing premise; caller
StateOk remains explicit. Controls reject saved-self and unrelated-local damage admitted
by LegacyFramePres, and prove that a real captured write changes caller x from 1 to 7 while
retaining Framed. No frozen-local assumption is used.

Clink 208 adds prelude-mode preservation to Framed and InitFrame; djudge_phase exposes it
for every certified answer. Ext and heap equality do not imply phase equality: Framed's
heap transports now consume it explicitly (rfl auto-parameters at concrete operations).
SavedFrame.frameOk_saved and EnvOk.reframe_uncaptured separate metadata/reads from value
transport. Instance/MainReturn's old API wraps restore_main_state_of_metadata, which accepts
changed caller locals and an independent outgoing environment. Closure/MainReturn discharges
full runtime StateOk restoration and composes the block continuation from a body RunSpec
plus outgoing caller EnvOk. Write proves that an unshadowed bound capture writes the actual
caller frame. ClosureReturnStateControls proves full Integer-to-nil caller conformance and
its boot instance, and rejects a prelude-mode flip.

Clink 209 adds BindingsPres to FramePres: old bindings cannot disappear, and every saved
frame retains exactly its old slot domain. Real setLocal can introduce slots only at its
active start; a different owner must already bind the written name. Composition and all
return paths retain the contract; closure_saved_bindings recovers every caller slot domain,
and djudge_bindings exposes it for arbitrary certified answers. CaptureBindingControls
rejects inserting a nil slot into a saved frame (allowed by the previous contract), permits
real captured writes/new active locals, and proves that empty and x=nil callers both satisfy
EnvOk [] yet the same body assignment updates only the latter caller.

Clink 210 adds OwnersPres to FramePres. For a live source capture chain, every owner lookup
within the source fuel budget returns the same frame after evaluation. setLocal_owner_mono
shows that an owner distinct from the fallback start remains selected with more fuel;
this proves real writes preserve ownership while permitting new active locals. Composition
transports liveness using retained capture links; ordinary returns use saved frames, and
constructor/current-capture returns use the restored uncaptured root. djudge_owners exposes
the contract. ReadReturn proves that a bound caller name unshadowed at entry cannot become
shadowed, and its body read equals its returned caller read after arbitrary Framed bodies.
Controls show binding-domain preservation alone admits shadowing, reject it with OwnersPres,
and permit nested writes, fresh locals and a real captured-write/read return.

Clink 211 adds FrameSlots for exact physical domains and its uncaptured assignment/return
transport. EnvReturn's weaker CaptureSlots classifies only names typed in the body output;
captureEnv retains caller-owned bindings and de-aliases them. closure_projected_env proves
complete outgoing EnvOk from that classification, unshadowing entry and per-type transport
for retained names only. ProjectedReturn composes full main StateOk and block RunSpec without
an independent outgoing environment. Controls retain a nil caller slot changed to Integer,
remove a fresh body local, and reject an alias to that discarded name. StoredReturn proves
full caller restoration retaining f's exact closure type; assignment supplies its physical
binding, so no complete input slot domain is assumed. The boot instance consumes body
conformance/framing; it is still a return theorem, not a whole-call admission.

Clink 212 composes actual local receiver evaluation, Proc dispatch, required-lambda entry,
certified body and block return. StorePrefix executes creation/assignment while retaining
the concrete allocated capture identity, then composes a state-specific continuation.
ClosureCallControls proves the whole `f = lambda { 1 }; f.call` source safe for all fuel
(and any Integer literal), with full caller conformance. Its generic body contract retains
f's exact type; it does not infer activation facts from Ty.clos or admit a checker rule.
Controls distinguish lambda/proc extra-argument behavior. A §F51 witness showed the old
Proc dispatch bypassed singleton `call`: CRuby returns 7, the model returns the body’s 1.

Clink 213 / model L272 fixes §F51: native Proc call/[]/yield/=== markers use ordinary
lookup and visibility, including aliases and super. Undef bypasses native fallbacks;
super rejects a tombstone. Proc#=== retains its native alias despite call overrides.
Call now requires ProcCallReady and the receiver's actual dispatch class. Ext preserves
readiness, allocation supplies the class, and procCallReadyB is checked at boot alongside
bootOkB. The whole-source theorem is state-specific under that explicit heap condition.
The broader replay exposed §F52: === must test identity before dispatching ==. Native
Object/true/false/nil markers now do so; scalar aliases retain original equality builtins.
Both repaired families have persisted CRuby regressions. Pure builtin proofs exclude Proc
markers by reduction; SuperOk now requires undefined=false, retained by its transports.
Full quiet gate GREEN (252 agree / 0 disagree), metatheory and standard-axiom audit pass.
Model replay: focused 5/5; tier 0 has 998 agree / 0 disagree, 305 unsupported, 5 invalid
controls and the existing test_syntax_115 harness error. Admission counts are unchanged.

Clink 214 adds Ratchet.Static.LocalFacts and its LocalFactsOk conformance: optional
exact physical slots and local Procs captured from the current activation with Proc
dispatch class. Allocation, store, assignment and copy have proved transfers; unknown
effects discard claims. Overwriting a source binding retains the copied closure's origin.
TrackedCall derives the whole zero-argument call from these facts, exact Env code,
ProcCallReady and the body proof, including projected main return. ClosureTrackingControls
proves a copied-binding call for all fuel and distinguishes wrong-frame captures, nil
slots, overwritten bindings and a native-table override. Entry/pop type transport remains
explicit. No DJudge/emitter change yet.
Full quiet gate GREEN (252 agree / 0 disagree); metatheory and standard-axiom audit pass.

Clink 215 carries native Proc#call lookup in primitiveDispatchB/StateOk, gated by
nameFreeN κ "call". dispatchMethods contains both pure primitives and the interpreter call
marker; primitiveMethods remains pure-only. Existing heap/context transports retain the
new row, and djudge_proc_call exposes it at certified value states. ProcCallReady now
states the actual resolved owner and shadow check. The whole stored-program proof is
SemSafeCtxA again; its boot theorem needs only bootOkB. No separate Proc boot premise remains.
Full quiet gate GREEN (252 agree / 0 disagree); metatheory and standard-axiom audit pass.

Next: thread mutable LocalFacts through checked evaluation, then register callable
admission. Native dispatch already follows from conformance and the name guard.
Scope/Pos cannot carry the local facts unchanged:
assignments replace origins, captured body writes need ownership-aware effects, and calls
need a proved outgoing fact record. The record currently describes current captures;
arbitrary escaped captures still need their own activation identity and scope contracts.
Entry now has full conformance under the named scope/liveness/environment premises, but
Ty.clos does not yet supply those premises. The stored-f pilot retains its higher-order
binding using ProcPres.empty_capture_den. General capture types still need transport.
EnvOk.capture is one-way:
its lower-bound spine does not supply EnvOk's absence clause for unmentioned names.
Framed.procs now retains a saved Proc's descriptor across argument evaluation;
Framed.firstOrder still excludes clos, and FieldsPres carries only first-order ivar facts.
Current-capture environments now have an entry contract; arbitrary captures still need
complete-environment and captured-value transport facts, not only a lower-bound spine.
FramePres.isolated applies only to uncaptured activations. For direct current captures,
closure_pop_framed now restores framing without assuming the caller's locals are unchanged.
closure_pop_metadata retains its non-local fields. closure_projected_main_state now restores
full main-caller StateOk with a derived outgoing environment; phase is retained by Framed.
The body may update/introduce locals; captureEnv projects its output rather than reusing it
at the caller. The entry guard forbids overlapping parameter/block-local shadowing, which
still needs effects preserving the hidden caller value. Non-main restoration remains open.
BindingsPres retains saved domains; OwnersPres now excludes new shadowing of an existing
owner along a live chain. closure_bound_read connects body/caller reads for unshadowed bound
slots of an uncaptured caller. CaptureSlots now accounts for new body locals without requiring
an exact whole-frame domain. EnvOk's absence clause means nil reads, not physical absence:
filtering body output to the incoming caller environment loses hidden nil slots that a
captured assignment may change. Do not infer CaptureSlots from EnvOk. The stored-f pilot
derives its one needed binding from assignment; general captures still need slot/identity
tracking and per-type activation transport. Aliases are fully peeled with deAlias because
their target may be a discarded body local, including under nested sameAs wrappers.
The unused ClosuresOk/closTblOk table machinery remains legacy, with F49's counterexamples
retained explicitly. The old index-free denotation is now named LegacyIndexDen in controls.

Sorbet 0.6.13405 infers T.proc.returns(Integer) for lambda { 1 }, rejects an extra call
argument, but accepts the changed-capture TypeError probe. CRuby agrees with the model
on that probe and on the arity/block-local distinctions. Controls now reject wrong code,
params, locals and mode; same-type capture writes preserve typing and changed-type writes
invalidate it. Type examples explicitly use RubyCore.Expr now that Ty imports Ratchet.Expr.

DPrim.intGt checks Integer > Integer at Boolean. primitiveMethods now pins Integer#>
in StateOk; the proof uses real dispatch and preserves the full machine contract.
ModuleCompareDerivations proves the whole 084 program for every Integer argument.
Controls cover signs, equality, large values, argument order, wrong type/arity/result,
and a replaced Integer#> method. Sorbet 0.6.13405 reports Boolean for the annotated
Integer comparison and rejects String or missing arguments. No emitter change was needed.

ImplicitCallShape is a syntax guard for bare calls and receiver-less sends, not a body
judgment. SingletonLookupRun recovers real own-table dispatch from class-ref conformance;
SingletonImplicit retains self across arguments and preserves the actual vcall/implicit site.
callSingletonImplicit registers that semantic contract. checkImplicitSingleton consumes exact
context/code body artifacts, including at refresh; it never substitutes an instance method or
a different receiver's singleton. The emitter resolves implicit singleton signatures separately
and routes `x` through lookup inside class scopes rather than the main-only missing-name rule.

SingletonImplicitDerivations independently proves 080 for every Integer value result. RuleAudit
now carries syntactic singleton-body scope through its prediction, independently of extraction.
Controls cover both spellings, arguments, wrong arity/results/domains, another receiver's code,
local-read confusion and same-named instance/singleton rows. Pipeline controls additionally
exercise renamed `x` calls and inferred arguments. Sorbet 0.6.13405 accepts bare and parenthesized
calls in singleton bodies and rejects a bare call to a required-argument method (clink 198).
Inherited singleton lookup and recursive singleton body assumptions remain outside this rule.

Clink 197 extends the untrusted missing-signature proposal policy to required scalar
parameters. infer_definition tries complete domains in deterministic order (Integer, String,
Boolean, Float, Symbol, nil), bounded at 4096 tuples. Each attempt has separate emitter state;
known callee signatures constrain calls inside the body. The complete body determines its
return proposal before later calls. Neither call values nor caller argument types select a
candidate. Unsupported declared signatures remain declined. Ambiguous bodies get one scalar
signature; polymorphism, richer domains and search beyond the bound remain completeness gaps.

ModuleParamDerivations independently proves all of 078 for every String argument. The body
proof quantifies over the whole String domain before the argument is introduced. Controls
reject nullable/any proposals even with a String call, wrong-domain calls and uncalled bad
bodies. Source probes cover local aliases, typed callee dependencies, conflicting uses and
explicit T.untyped annotations. Sorbet 0.6.13405 leaves the result T.untyped and accepts an
Integer argument to `"hi " + value`; CRuby raises TypeError, and validateD rejects that call.

moduleDecl now joins DJudge, the registry, bridge, Deriv decoder and checker. It checks the
body with separate locals and an empty module header, then refreshes cached bodies after
restoring the caller. It retains the real body result and grants no allocator. ModuleDerivations
independently proves the whole 077 program for every Integer result; CorpusSafety and RuleAudit
cross-check its concrete program and rule set. ModuleCheckControls covers forged names/results,
uncalled bad bodies, arity, reopening, allocator/subclass rejection, separate locals and old
singleton calls after another module. Same-selector singleton declarations remain restricted.

Clinks 189–195 prove fresh module entry/header/body/return with full StateOk and caller
restoration. CoreOk retains Module ancestry (§F46); StateCore retains ModuleBase name/hook/
constant-fallback facts (§F47); ClassQuerySite retains direct Module dispatch (§F48). All are
checked at boot and preserved by existing transports. ModuleHeader publishes metadata without
allocator permission; ModuleBodyRun reuses the real ClassActivation frame continuation.
SemSafeCtxA.moduleDecl consumes only a body proof and moduleRuleB's syntax/type guards.

Sorbet 0.6.13405 accepts 077 but reveals M.foo as T.untyped and even accepts treating its
Integer result as String. It reveals NilClass for a module expression ending in 7, whereas
CRuby 4.0.5 and the model return 7. The checker uses the proved body result. Sorbet rejects
outer-local reads in modules and an uncalled Integer singleton body declared String.

selfRead consumes incoming selfTy conformance. CheckedBody keeps its declared result proof
and an optional CheckedResult from the body before nominal widening. resultAt selects only
one of those proofs; all call routes consume it without rechecking bodies at argument values.
Refresh still uses original annotations, and branch signatures also compare refined types.
The emitter proposes known initialized-instance result hints, which cannot pass on nominal
evidence alone. SelfResultDerivations independently proves 076 for every Integer. Rule prediction
now records erased result class annotations as well as scoped parameter domains.

defDecl now uses topDeclClassesB: either no classes, or non-root class names and a selector
other than new. TopMethodInstall preserves existing code, singleton rows, own selectors,
and allocator facts through the real Object write; RootNames excludes hidden root aliases.
The existing emitter maps known initialized-class parameter annotations to inst field domains;
075's proof checks that entire domain, never a particular argument. Nominal-only, empty-field
and nullable receiver controls still decline. No emitter or model change was needed.

scalarIvarAsgn replaces an existing Integer/Float/Symbol/nil field while preserving its
spine. ScalarPres proves universal first-order preservation across nested aliases; ScalarState
restores full conformance. It does not weaken Framed. Boolean replacement fails that contract
because TrueClass observes true versus false (§F45). FrozenError ancestry is now checked
by primitiveErrorsB; the actual frozen assignment path safely raises it. ScalarWriteDerivations
covers every initial Integer, and controls cover aliases, bad annotations and frozen receivers.

073 remains admitted with own singleton definitions/calls, implicit new and same-class
nominal result conversion. SingletonCache rechecks full annotated bodies after table changes;
calls consume exact context/code artifacts. Inherited singletons remain open, and explicit
self.new still has only its semantic proof. Nominal conversion only forgets information;
it cannot recover exact receivers or initialized fields from a nominal annotation.

See clinks 177–204 and AGENTS.md. Older text below is historical.

# ratchet — hand-off note (2026-09-10)

> **EMERGENCY EXIT INVOKED, clink 64** — see `implementation-notes.md` §EMERGENCY EXIT for the
> statement and the evidence. In one line: the ladder counts one rule at a time and 26 of the 35
> remaining rules only come out *together*, at the end of a layer that is several sessions long,
> so three consecutive sessions of verified work have left the number at 48. The recommended fix
> is a **ladder** change, not a proof change — count **conditional rungs** (`StepSound →
> Obl.Judge.if'` is a real theorem and the layer hypothesis is already a named `Prop`), which
> would have counted most of clinks 62–64 without weakening anything.

> **Superseded again, 2026-09-10 (clink 63): `enterUserMethod` is PROVED, and the "one
> transcription away" note below is wrong about the transcription.** Hand-splitting the
> conditions does not work — see `Denote/Sem/notes.md` §The nineteenth stall point (nine `let`s,
> a nine-field projection literal, and `generalize … at h` silently abstracting nothing because a
> hand-written `match` is a fresh matcher constant). What works is
> `Denote/Sem/StepAct.lean`'s **mirror gated by `rfl`**: the same function with its five
> machine-touching stages named, `enterUM_eq` by `rfl`, walk in 18 s. **Read that file's header
> before touching any other `Interp/` let-chain**, because `finishSend`, `invokeDispatch`,
> `startArgs`, `tryReflect` and `evalExpr` are the same shape.
>
> **`tryMixin` and `defineAttr` landed too, so stage 2 is complete except `enterClassBody`**
> (deprioritised — declaration family), **and stage 4 is thirteen of fifteen**
> (`Denote/Sem/StepReflect.lean`).
>
> **Stage 4 is complete and `Step.dispatchMiss` is proved — the miss path is closed.**
>
> **The resume point is the twentieth stall point** (`Denote/Sem/notes.md`): `Builtins.run` answers
> four ways and three carry a machine, but every walk under it (`builtins_run_locals`,
> `builtins_run_cap`, `Step.builtins`) is stated over **`.ok` alone** — so a builtin that *raises*
> is outside the layer, and `invokeDispatch` cannot be closed. Try (1) first: generalise the
> statement over the result (`∀ r, Builtins.run … = r → LocalsSame m (mOf r)`) and re-run the
> existing `builtin_arms`/`cap_norm` tactics; that is one measurement rather than a new walk. After
> that the **dispatch spine** (`invokeDispatch`/`invoke`, then stage 3's `finishSend`/`startArgs`)
> is unblocked for the first time. Read `Denote/Sem/StepReflect.lean`'s header first: it lists the
> two relation-level corrections (`PreAct` is false across `defineMethod`; `PayKeep` is the
> interface for `eigenclassOf`) and the ordering rule's fifth and sixth costumes.
> `PreAct` (`StepSupport.lean`) is the transport every allocating-then-pushing helper needs, and
> the six `methodIn` bridges are on file, so a new caller of `enterUserMethod` costs one line.
> **The ladder is unchanged at 48/83 and none of this moves it directly.**

> **Superseded in one respect, 2026-09-10 (L269, clink 62): `BuiltinsSeal` is PROVED.**
> This file's resume point was "re-attempt the `Builtins` layer walk". That walk is done —
> `Denote/Sem/BuiltinsCap*.lean`, all six dispatchers plus `Builtins.run`, axiom-clean, seconds
> each — and `builtinsSeal`/`builtinsFramesWF` close the eighteenth stall point: `Sealed` survives
> `Builtins.run`. Read `implementation-notes.md` clink 62 and `Denote/Sem/notes.md` §The second
> walk (eight tactic measurements) before starting anything else in this layer; the two that
> transfer are *put the arm's shape in a `rfl`-provable hypothesis and leave the conclusion
> first-order* and *a `simp` in a 600-arm walk is a search, not a step*.
>
> **The new resume point is the next step of the same layer**: `Sealed.push`/`pop`/
> `alloc_closure` at the *interpreter*'s six frame pushes, `ClosuresOk`'s exactness component
> (the sixteenth stall point sized it; note it needs a third escape for a closure a *builtin*
> created), and then the per-arm `stepFn` walk. After that come jump-freeness and the `frameK`
> decomposition, which the fifteenth stall point argues cannot be sequenced apart. **The ladder
> is unchanged at 48/83 and none of this moves it directly** — `if'`/`ifNoElse`/`begin'` and the
> 22 call rules come out at the end of the whole layer, not in stages.
>
> Also new: `found-issues.md` **§F22**, a third independent reason `Judge.casgn`'s obligation is
> false (`constAsgnOk`'s guard list is not the set of class names a `Ty` can carry, and `Regexp`
> is outside it). Not reachable. It means `casgn` is two fixes away, not one.

## The 2026-09-08 note, unchanged below


> Written after clink 60 so a fresh-context agent can pick up the **semantic
> ratchet** without re-deriving the last session. Read [`AGENTS.md`](AGENTS.md)
> §Semantic ratchet status first, then `Denote/Sem/notes.md` in full; this file
> is only the resume point and the one correction that arrived after the clink
> was written.

## Where the ladders stand

| Ladder | Reads | Script |
|---|---|---|
| Ladder reach (*the headline*) | **18 rungs** -- the leading run meeting their recorded target; frontier `019-to-s-call`, one `DPrim` row away | `scripts/run_typed_ratchet.sh` |
| Agreement | **252 agree, 0 disagreements** over the sig-stripped programs | same, step 3 |
| Clinks (*what the judgment may contain*) | **9 of `DJudge`'s 12** rules, each carrying an answer-typed proof **and** an invariant proof; 3 owed | `scripts/run_denote.sh`, or `lake exe semladder` |
| End-to-end safety | **8 corpus rungs** proved `StuckFree bootMachine <program>` at every fuel; **7 of 9 rules exercised** (`var`/`vasgn`, §F30) | `run_typed_ratchet.sh` step 4, or `lake exe semladder build` |

**Clink 68 deleted the old ladder**, so the three rows above are all of them. Gone: `Judge`
(83 rules), `chk`, `Rungs.lean`'s 177 derivations, `ChkSound.lean`, `corpus-untyped/`,
`Denote/Rules/`'s 48 value-shaped obligations, and `SemJudge` itself. 41 Lean files, ~14k
lines, from 110 files and ~42k. `AGENTS.md` §What was deleted lists it with reasons, and
everything from `AGENTS.md` §LEGACY onward is history for a judgment that no longer exists.

`Ratchet/Check/Check.lean`'s `check` **returns the derivation**, so its type is the soundness
statement and the Lean typechecker is the oracle. Rungs **001-008** are derivable in the
certified judgment (`DJudgeC dclinks`) and each has an **end-to-end safety theorem** in
`Denote/Safety.lean` — `StuckFree bootMachine <program>`, at every fuel, at the real
booted machine. Rungs 009-018 are checker coverage only.

Safety cannot go stale: it is a **field of the clink target** (`SemSafeA = SemJudgeA ∧
SafeUnder`), so `dregistry_safe` is unconditional at every registry size and a rule cannot
join `DJudgeC` without proving it. The field is the **invariant**, not whole-program safety:
`SafeUnder` says a machine evaluating the expression under a continuation that accepts its
type (`DKontOk`, indexed by the answer type) is safe — quantified over the continuation, so it
composes to sub-expressions, which the whole-program reading did not. `dregistry_safe` is that
statement at `DKontOk.nil`. Three gates keep the *count* honest too — the list carries
the programs and the theorem is proved over it; `semladder build` compares each theorem's
`Expr` against the program the pipeline built for that rung; and every registered rule must be
exercised by a covered rung or named in `unexercised`. That last one found §F30 on its first
run: `var` is proved and registered, and no covered rung reads a local.

The four owed rules (`vasgn`, `seq`, `prim`, `if'`) are all behind **`RunAPushK`** -- the
answer-level counterpart of `run_pushK`, stated as a named `Prop` in
`Denote/Judgment/JudgeA.lean` §4 and unproved. Read that section before starting: it prices what
each of the four needs *besides* the lemma, and three of them need nothing (`if'`'s join
soundness is already proved, in `Denote/Ty/Join.lean`).

## The resume point, in one paragraph

The semantic ladder is halted, and **not** because a rung is hard. All 36
remaining rules sit behind one of four unbuilt layers (`Denote/Sem/notes.md`
§Where the remaining 36 rules sit). The layer that gates the most —
`if'`/`ifNoElse`/`begin'` directly, and the 22 call rules through
jump-freeness — is the **locals layer**, and its invariant `Sealed`
(`Denote/Sem/Locals.lean`) is not preserved by `Builtins.run`.
`Denote/Sem/StepLocal.lean`'s `not_BuiltinsSeal` is the refutation.

## …and the correction that came after the clink

Clink 60 read that as an invariant redesign. **Probing against CRuby says it is
a bounded model-fidelity fix instead** (`found-issues.md` §A6, and the probe
results appended to the eighteenth stall point):

```
:upcase.to_proc.binding          # => ArgumentError (C-level Proc)
:upcase.to_proc.source_location  # => nil
```

CRuby's `Symbol#to_proc` proc has **no binding at all**, so the model's
`captured := 0` is a capture edge the reference semantics does not have —
forced by `Closure.captured : Nat` (`RubyCore/Heap.lean:136`) where
`Frame.captured` is already `Option FrameId`
(`RubyCore/Machine.lean:57`). `Sealed.clos` reads exactly that field.

**So: try the `Option` first, then re-attempt the `Builtins` layer**, before
designing a joint frame-graph/control-state invariant. **And add a third clause
while you are there** — see the next section. Two construction sites
(`Builtins/Strings.lean:449` and `Interp/Support.lean:448` — the `&:sym`
`coerceToProc` path builds the same closure, so the fiction is not confined to
the `Builtins` layer), ~4 readers in `RubyCore/Interp/`, 14 files in
`RubyCore/Proof/`, 12 in `Denote/`. It changes the *machine*, so the whole
difftest and all 47 rungs have to be re-verified.

`not_BuiltinsSeal` stands either way: it is a theorem about `Sealed` and
`Builtins.run`, both definitions in this repo, so fidelity does not bear on its
truth. What moved is the prognosis.

## What the `Option` fix does and does not buy (enumerated 2026-09-08)

Every writer of the two things `Sealed` reads was enumerated; the model is small
enough for this to be exhaustive (`Denote/Sem/notes.md`, the eighteenth stall
point's third subsection).

- **Closures close.** Three `.proc` allocations exist. `reifyBlock` captures
  `m.stack.headD 0` — the current frame, which is *on the stack*, so
  `Sealed.stack` discharges it and it was never a problem. The other two are the
  `:sym.to_proc` fiction and go to `none`.
- **Six `frames.push` sites**; four default `captured` to `none`. Of the two that
  set it, `callClosure` reads a `Closure` from the heap (that is what
  `Sealed.clos` is for) and **`enterUserMethod` reads
  `MethodDef.capturedFrame`, which `Sealed` does not mention at all.**
- **So a third clause is needed**, over methods installed in the heap.
  `define_method` is the writer, and the hazard is real on both executors:
  `x = 1; Object.send(:define_method, :setx) { x = 2 }; def g; setx; end; g; x`
  is `2` under CRuby *and* the model.
- **The third clause is closed**, which is the point: `reflectDefineMethod` takes
  its `capturedFrame` from a closure already in the heap, so `Sealed.clos`
  discharges it. Every other `MethodDef` writer either defaults the field to
  `none` or copies an already-installed method. J33's capture erasure makes it
  vacuous for any body that reads no local.

**Verdict:** `Sealed` + the `Option` + a `MethodDef` clause is three clauses that
discharge each other, with no writer left over — the control state does not have
to enter the invariant after all. Not a proof: it says no arm is blocked in
principle, and the per-arm `stepFn` walk is still the work. Measure the new
clause at the booted machine (`Denote/Sem/Core/Boot.lean`, `MethodsExact`'s shape)
before writing it down.

## DONE (2026-09-08, L266) — and one thing it does **not** cover

**Implemented.** Read the box at `Denote/Sem/notes.md` §The decision for how the
work differed from the plan (three departures, two of which changed a definition's
*shape* rather than its parenthesisation). Re-verification, all green: difftest
tier 0 1304/992 agree/**0 disagree**, corpus agreement 254/254, `checkrungs`
177/177 + 145/145, `run_ratchet.sh` **178/254** (unmoved), `semladder` **47/83**
(denominator still 83), `lake build` clean in both packages, no `sorry`.

**`not_BuiltinsSeal` is retired.** It was a true theorem about two definitions in
this repo, and L266 changed one of them: `Symbol#to_proc`'s Proc now captures
`none`, so `Sealed.alloc`'s premise holds for it. `toProcSealsB` (`#guard`ed)
replaces `toProcBreaksB`. `BuiltinsSeal` itself is still **stated and unproved** —
one builtin measured is not the layer walked, and re-attempting that walk is the
resume point now.

**Baseline finding, unrelated and not fixed:** `lake build Metatheory` is red at
HEAD, three pre-existing breaks — `found-issues.md` §A7. One of them
(`startArgs_lambda`) is a *false statement*, not a broken script.

---

**The original decision, for the record (2026-09-08):** `Closure.captured` becomes `Option FrameId` (matching
`Frame.captured`, which always was one) and the two `:sym.to_proc` construction
sites take `none`. Eight sites in the model proper, listed in
`Denote/Sem/notes.md` §The decision, plus the `cl.captured` statements in
`RubyCore/Proof/Static/{Konts,Locals,Iter,LambdaArrow}.lean` and in
`Denote/{Apply,Local,Ext}.lean` + `Denote/Sem/Locals.lean`. Behaviour-preserving
(`callClosure` keeps reading the same frame via `.getD 0`; only the pushed block
frame's own `captured` becomes `none`, and the body's free names are its own
parameters). **Changes the machine**, so difftest and all 47 rungs need
re-verification.

**TRACKING — this is not a general fix.** It is right for exactly the two sites
where the model *invents* a Proc for a Symbol. When `&obj` learns to dispatch a
**user-defined `to_proc`** — `coerceToProc` gates it today ("block-pass of a
non-Proc (to_proc dispatch is L2)") — the Proc returned is an ordinary
`reifyBlock` closure over a real frame and it *will* capture. The `none`
shortcut neither breaks nor helps there; `Sealed.clos` carries it like any other
user closure. **Explicitly out of scope right now.** Re-read
`found-issues.md` §A6a and `Denote/Sem/notes.md` §The decision before assuming
the seal still closes once L2 lands.

**Rejected alternative**, recorded so it is not re-proposed: keep `captured := 0`
and discharge the allocation with a lemma that unfolds `Symbol#to_proc` and shows
its closure body mutates nothing in whatever frame it names. It does not
discharge `Sealed` as stated (that clause is about the capture *graph*, so you
would first have to weaken it to "…or this closure is inert" — and that escape
is what drags the unconditional `stack` clause into control-state territory), it
does not generalise to the user-defined `to_proc` above, and it leaves the
fidelity gap standing for every future proof to pay again. Full reasoning in
`Denote/Sem/notes.md` §The decision.

**Also drafted, not implemented:** the **`MethodDef` arm** of `Sealed` — the
third clause, its `FramesWF` twin, what consumes it (`Sealed.push` at
`enterUserMethod`), and the writer-by-writer argument that it is closed. Both it
and the existing `clos` clause are **vacuous at the booted machine** (0 capturing
methods, 0 Procs — `lake env lean probes/measure_captures.lean`), so the arm
costs no vacuity risk.

## Two things worth not re-deriving

- **The seal is guarding a real hazard.** `x = 1; f = lambda { x = 2 }; def
  g(p); p.call; end; g(f); x` is `2` under CRuby *and* under the model, while
  the same shape with a `to_proc` proc leaves `x` at `1` on both. So the
  sixteenth stall point's witness is genuine and `Symbol#to_proc` is not an
  instance of it.
- **`Judge.if'` is not the cheapest remaining rung**, despite `semladder`
  listing it first (it prints the inductive's constructor order). All six
  narrowing type-lemmas are proved and `stateOk_narrow_then`/`_else` are
  assembled, but `if'` is blocked *twice*: by the `&&` sandwich's `thenOnly`
  refinement (the locals layer) and by the eleventh stall point, where
  `joinEnv` synthesizes an alias nobody promised. There is no cheapest
  remaining rung.

## Reproducing the probe run

```sh
cd ruby && python3 ruby-lean/probes/seal_fidelity_probes.py   # writes /tmp/probes
cd difftest && uv run python -m difftest replay /tmp/probes --sut lean
```

20 programs, 17 agree / 2 disagree / 1 gate against CRuby 4.0.5. The two
disagreements are §A6b (`Symbol#to_proc` is not identity-stable — CRuby interns
per symbol) and §A6c (the zero-argument `ArgumentError` message); the gate is
`Proc#arity`, unmodeled.

## Two working rules, each paid for twice

**Write the layer's target down as a named `Prop` before proving the layer under
it.** `FrameLocal.lean`'s 532 lines were proved for a target that was never
stated, and the target turned out to be false. The same lesson is what
`not_KontFrame` bought in clink 52.

**Let the transport lemma write a rule's premises and its outgoing environment.**
Before authoring a `DJudge` constructor, find the `Denote/Sem/` lemma that carries
`StateOk` across the machine change the rule makes (`StateOk_reCtl`,
`StateOk_ext`, `StateOk_setLocal`, `StateOk_ivarWrite`); its hypotheses are the
premises and its conclusion's environment is the outgoing one. `var` and `vasgn`
were both authored without doing this and both obligations refused to close
(`found-issues.md` §F29). It is a rule of thumb, not a checked invariant: the
stronger version — *never re-type an existing entry* — is false for Ruby
(`031-reassign-different-type` is `x = 1; x = true; x`). Full statement, with why
it makes the **next** rule's proof simpler, in `Ratchet/Check/Check.lean`
§Authoring a rule.

ClassInstanceConstantsActual repairs old constant equality with an explicit
Object-chain/module-fallback premise; ClassSitesActual repairs the original
old/fresh InstanceSite, MetaReady and ModuleBase transfers. Mandatory witness
ConstantReachControls.old_site_not_preserved shows current global equality alone
does not imply future global visibility (BasicObject-only chain, copied globals).
This is a generic preservation counterexample, not an accepted type-error witness.
ClassChains.root_tail derives reachability when static ancestors resolve; the
current plainClassTablesB guard does not ensure that resolution. Establish the
needed all-sites premise before assembling body StateOk/admitting class clinks.
