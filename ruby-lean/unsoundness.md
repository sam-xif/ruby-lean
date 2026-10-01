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
