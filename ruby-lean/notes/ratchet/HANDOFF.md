# Current resume point (2026-09-26, clink 226 / model L273)

Latest admissions: 089 and 090. Fragment 86, checker reach 90,
75 registered rules (40 expressions + 35 companions), 65 worked theorems, no exemptions.
The safe prefix remains 17; 018 is correctly rejected. Next frontier: 091-block-each-int,
`[1, 2, 3].each { |x| x + 1 }`, followed by map (092/093). The each source proof is complete;
its registry/checker/emitter admission is next. Measure Sorbet before new rules.

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

Next: add a DFlow each constructor with the premises of SemFlow.each, wire all DFam/registry
cases, a checked derivation hint, checker body rechecking and untrusted emission. Register a
worked derivation of 091 and raise measured floors only after acceptance. The semantic rule
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
Next: registry/checker/emitter integration. Current formal loop uses one required
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
