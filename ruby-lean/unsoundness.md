# Hash iterator transparency (2026-09-30)

The legacy static RetTransparent/NxtTransparent predicates admitted every
iterK. Their unwind lemmas claimed that return, next and raise only pop the
marker and change control. That claim is false after shared Hash insertion locks:
a hashEach marker with hashIterationLocks = [0] removes 0 on unwind.
RubyCore/Proof/Static/IteratorUnwind.lean's hash_unwind_not_transparent is a
kernel-checked counterexample using raise; the same cleanup precedes all jumps.

Restrict exact transparency to IterUnwindInert (all kinds except hashEach).
RetOk/RaiseOk/NxtOk skip premises inherit that correction. KontOk's admitted
iterator uses ignore and retains its proof. This is a stale auxiliary static
judgment, not evidence of a Sorbet bug or an active validateD unsound accept.
No runtime or top-level safety theorem changes.

# Uncaptured local reads can still alias (2026-09-30)

getLocal_uncaptured formerly used RootUncaptured alone to equate a lookup with
the active frame's own locals. MethodAliasControls.alias_refutes_uncaptured_read
kernel-checks a two-frame witness: frame 0 captures none, aliases frame 1, and
has no x; frame 1 binds x=7. getLocal reads 7, while the former direct read is nil.

Require the active frame's localAlias = none in that lemma and caller-local
restoration. StateOk already supplies this premise, and FramePres preserves it
on return. No active typing rule or accepted program is restricted. This is a
false auxiliary lookup lemma, not a demonstrated Sorbet or validateD soundness bug.

# Ordinary metadata admitted alternate formal binding (2026-09-30)

ordinaryMethodCodeB omitted fromBlock and forTargets. MethodCodeControls retains
its eight-clause legacy guard and a passing required-Integer body check for y+1.
The same MethodDef carries a for callback's binding plan [z,y] with one argument
7. Actual enterUserMethod then overwrites y with nil, and Interp.run reaches a
type error. Both premises and the runtime result are mandatory evaluated controls.

OrdinaryMethodCode and its Boolean guard now require fromBlock=false and
forTargets=none; the soundness projection proves both fields. Controls reject
either alternate mode independently and retain ordinary-code acceptance.
This concerns the semantic metadata judgment over arbitrary runtime records;
no accepted source program or Sorbet counterexample has been demonstrated.

# Frozen definitions escaped ordinary conformance (2026-09-30)

FrozenDefinitionControls preserves the complete former boot-state check. It
accepts the boot heap with Object frozen and FrozenError#initialize replaced by
a fromPrelude-marked body executing nil+1. Defining the trivial method bump
then runs that initializer and reaches a type error. Method provenance alone
does not constrain this callback. This refutes the old semantic definition
obligation over StateOk; defDecl remains gated, so it is not an active validator
accept or a demonstrated Sorbet bug.

MainReady now requires Object to be unattached and unfrozen. Its Boolean guard,
heap-extension and method-write proofs preserve both facts. The old state
counterexample is rejected; the real boot machine remains accepted. Ordinary
definition safety can therefore follow the real queued method_added protocol
without entering untyped FrozenError callbacks. Supporting frozen definitions
requires a separate callback contract rather than assuming provenance is safety.

# Source definition was no longer a one-step value (2026-09-30)

The former step_def_install equation skipped runMethodEdits and its queued
method_added send/marker, even when the hook was native. MethodDefinitionControls
observes the first step's send, the native callback's intermediate nil and the
final symbol after continuation resumption. The replacement equation follows
that protocol and definition_hook_runSpec proves its answer contract. The
source record also follows definee, libraryOrigin and all initialization-name
privacy overrides. This repairs an off-target interpreter equality; it does
not exhibit a Sorbet bug or an active validateD unsound accept.

# Library provenance escaped ordinary source conformance (2026-09-30)

MethodOriginControls preserves the complete former boot-state guard. It accepts
the real boot machine with only currentFrame.libraryOrigin set to true. A source
def then constructs fromPrelude=true, which fails ordinaryMethodCodeB even for
the trivial Integer body. This refutes the former outgoing ordinary-code
contract; it does not demonstrate a type error or a Sorbet soundness bug.

MainReady now requires libraryOrigin=false. FrameScope transports that field,
and the existing local-write, heap-extension, method entry/return and reframe
proofs preserve it. The legacy witness is rejected while the real boot passes.
The repaired definition proof uses the real queued callback contract, so defDecl
can be admitted without pretending that user phase alone establishes provenance.

# Main's leading dispatch class can shadow a checked definition (2026-09-30)

Denote/Controls/MethodPrefixControls.lean measures a complete bootStateB accept
after adding bump to main's leading dispatch class with builtin
Module#method_added. The unrestricted checker accepts the sequence def bump=1;
bump(), but execution from this state raises ArgumentError: that native hook
expects one argument and wins lookup ahead of Object's checked zero-arg body.
The legacy top_method_runSpec incorrectly supplied MainReady.chain to a lemma
requiring Object first. Actual main has its own dispatch class before Object.

This is a semantic call-judgment countermodel over an accepted arbitrary state,
not a source-program error from the real boot or a demonstrated Sorbet bug.
Production validateD still rejects the sequence because callSig is gated.
Before call admission, conformance must reject forged prefix entries, positive
definition records must exclude main-native names, and lookup must follow the
real prefix. Preserve the genuine main-native names already excluded by
topDeclClassesB.

MainReady now carries mainOwnNamesB: the complete legacy state guard still
accepts the witness, while the current guard rejects it. The real boot bound
passes. Heap growth preserves it, and generic method writes explicitly establish
MainPrefixWriteOk when the context requests main's world. Object writes prove
separation from main's exact ancestor chain. Positive-name and activation
metadata checks still precede call admission.

# Ordinary owner metadata did not pin activation definee (2026-09-30)

MethodDefineeControls preserves the ten-clause legacy ordinary-code guard. A
method with owner Object and definee NilClass passes it. Its checked Integer
body defines inner=1 then calls inner(); activation installs on NilClass while
lookup uses main, so execution raises NoMethodError. This is an arbitrary
semantic-descriptor countermodel, not a source/Sorbet error from real boot.

OrdinaryMethodCode and its Boolean guard now require definee.getD owner to equal
the expected owner. Both absent definee and explicit matching definee remain
valid. The source-definition proof supplies the fact from its real record.
DefsOk also excludes mainSingletonNames, matching the existing topDeclClassesB
checker guard. Lookup proves the leading singleton entry absent before resolving
Object; native fidelity shadows retain the interpreter's unsupported outcome.
The existing checked-body, activation and caller-restoration proofs then discharge
ordinary call safety. MethodDefineeControls is mandatory in the gate.
