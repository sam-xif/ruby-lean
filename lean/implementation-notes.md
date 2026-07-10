# Lean model — implementation notes (decisions L1–L12)

Non-critical choices, recorded for rollback per the workspace convention
(cf. `../harness/desugar-dt/implementation-choices.md` C1–C20,
`../difftest/implementation-notes.md` N1–N8). Load-bearing *semantics*
decisions live in the sketch and README, not here.

- **L1 — interpreter before `Step`.** The sketch names `inductive Step` the
  definition of record; we built `stepFn` first so the model could meet the
  difftest engine on day one (the sketch's own §4 argument). `Step` will be
  authored against `stepFn`, then the adequacy theorems.
- **L2 — heap = dense `Array Object`,** ObjId = index (not AssocList as
  sketched). O(1) get/set, allocation appends, ids never reused. Swap back
  behind the Heap interface if extensional proofs prefer AssocList.
- **L3 — frame store = `Array Frame`,** FrameId = index; stack is
  `List FrameId`. Matches the sketch's store/stack split; blocks (L1) will
  use `captured` chains into this store.
- **L4 — builtins keyed by string bid `"Owner#name"`,** registered in H₀
  method tables as `MethodDef` with `builtin := some bid`, so user defs
  shadow builtins through ordinary lookup. Alternative (closure table)
  rejected: strings keep `Boot` data-only and diff nicely.
- **L5 — lookup-miss trichotomy** (dispatch fidelity): (a) name exists in
  CRuby per generated tables (`CRubyNames.lean`) but unmodeled →
  `Unsupported`; (b) total miss with explicit receiver or args → real
  `NoMethodError`, byte-exact message; (c) bare implicit zero-arg send →
  `Unsupported` (RubyCore conflates vcall/fcall; their error classes
  differ). Same split for constants via `crubyToplevelConstants`.
- **L6 — shadow checks**: user-method resolution gates if CRuby defines the
  name on a class *between* receiver's class and the resolved owner
  (test_yjit_120's `String#getbyte` vs toplevel `def getbyte`). Class-object
  receivers additionally consult generated *singleton* name tables
  (`Hash.ruby2_keywords_hash`), except when our lookup resolved to a builtin
  (our class-aware `Class#new` subsumes the common singleton constructors).
- **L7 — `reprPure` flag**: a user `def` of to_s/inspect/==/eql?/message/
  to_str flips it; pure-repr consumers (`puts`, `p`, `String()`, `inspect`
  of containers) then answer `Unsupported` for plain objects/main rather
  than print a wrong default. Direct sends self-correct via lookup.
- **L8 — Float policy**: arithmetic modeled; any *rendering* of a Float
  (to_s/inspect/interpolation/final result) gates — Ruby requires
  shortest-roundtrip formatting, Lean's `Float.toString` is `%f`-style.
  Implementing Ryū-style output is a contained future work item.
- **L9 — `$!` model**: set on rescue entry (restored on handler exit to the
  value saved at entry) and during `ensure` bodies running for an in-flight
  raise (restored after). Not yet set during bare propagation through
  frames — unobservable at L0 (no reads outside rescue/ensure survive the
  fragment gate).
- **L10 — fuel**: default 5M steps; `RunResult.outOfFuel` is distinguished
  from `stuck` (sketch §5) and maps to `Unsupported "out of fuel"` at the
  SUT boundary (never a fake timeout).
- **L11 — `stuck` ≠ `Unsupported`**: a stuck machine exits 1 with a
  `MODEL STUCK (bug)` banner and the Python adapter prefixes `MODEL-BUG:` —
  never silently absorbed into the fragment gate.
- **L12 — zero-arg builtin arity list** (`zeroArgBids`): extra args to
  zero-arg builtins raise `ArgumentError … expected 0` (test_yjit_090);
  optional-arg builtins instead gate their with-arg forms individually.
