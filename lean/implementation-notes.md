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
- **L13 — metatheory PoC lives under `RubyCore/Proof/`, off the default
  target.** `Step.lean` (relation + `Step.sound`/`Step.deterministic`),
  `Adequacy.lean` (`Step.heap_monotone`, `Step.complete`, `Step.adequacy`),
  `Demo.lean` (`example`s: non-vacuity, a concrete 5-step reduction of `1;2`
  to the value `2`, adequacy on a real `init`). They are part of the
  `RubyCore` lib glob but *not* imported by `Main`, so `lake build` (the
  `rubycore` exe) never touches them; build with
  `lake build RubyCore.Proof.Adequacy RubyCore.Proof.Demo`. Rationale for the
  separation: this is a **proof of concept** — first evidence the interpreter-
  first architecture admits real theorems — and is expected to be reworked (or
  scrapped and re-derived) when L1/L2 change the machine shape, so it is kept
  physically apart from the SUT. Deps audited via `#print axioms`: only
  `propext`/`Classical.choice`/`Quot.sound` (no `sorryAx`, no `native_decide`).
- **L14 — fragment is an effect-light *control core*, not full L0.** `Step`
  covers literals, `var`/`vasgn` (local/ivar/global — ivar with a `ref` self,
  always true at toplevel), `seq`, `if`, `while`, `break`/`next`, and jump
  propagation past neutral konts. Deliberately excluded (each is "no `Step`
  exists", matching `stepFn` → `.unsupported`/`.stuck`/`.done`): `send`/
  dispatch, `return` (needs a method frame from a send), `begin`/`rescue`/
  `ensure`, `class`/`module`/`def`, `const`/`casgn`, arrays/hashes, class
  variables, and the frozen-immediate `@x=` path. This is a proof-technique
  PoC, so fragment *membership* (`InFrag`) is narrow by design; the theorems
  quantify over all configs in it, not over whole real programs. Next
  extension is `send`: fold `invoke` (and `Builtins.run`) into the relation as
  a trusted oracle — `Step` gets a constructor `invoke … = .next m' → Step …`
  — so the dispatch machinery is proved adequate without re-proving the
  axiomatized builtin library. `return`/frames and `begin` unwinding follow.
- **L15 — proof-tactic choices** (revertable). *Soundness* is one uniform
  `cases h <;> simp_all […]` with a **full-unfold** simp set (`stepFn`,
  `evalExpr`, `applyKont`, `unwind`, `withCtl`/`withKont`, `pop`, the frame
  setters, `currentFrame`, `bindIvar`, `allocStr`/`Heap.alloc`): each
  constructor's image is *definitionally* what `stepFn` returns, so every case
  closes by reduction. Partial unfold desyncs the two sides (one keeps
  `pop m rest` folded while the other expands and rewrites `m.ctl` via the
  hypothesis) — unfold `pop` too or nothing. *`strLit`* inlines the
  `objs.push` allocation in the constructor rather than carrying a
  `allocStr m s = (v, m')` Prod equation, which `simp` handles far more
  cleanly. *Determinism* is a 3-line corollary of soundness + `.next`
  injectivity (`stepFn` is a function). *Completeness* uses the `realize`
  helper: name the constructor whose shape matches, and soundness + injectivity
  force its target to equal the executable's `m'` — so each case is
  `exact realize hs (.someCtor …)` after a structural `cases`.

- **L16 — L1: blocks/procs/lambdas (executable stepper only).** Consumes
  export **v3** (block-locals slot, `yield`/`blockpass` heads, `&blk` capture
  params). Design (artifact 04, sketch §1.1/§1.2):
  - **A Proc is a heap object** (`Payload.proc (Closure)`, new bootstrap class
    `Proc`, `Boot.procId := 29`, `mainId → 30`). `Closure` holds `params`,
    `locals`, `body`, `captured` (defining FrameId), `home` (the return-scope),
    and `lam`. Its `inspect`/`to_s` are address-based ⇒ gated (`pureOk` false).
  - **Frame identity = generativity.** `Frame` gains `captured`/`home`/`lam`.
    `getLocal`/`setLocal` walk the `captured` chain, so a block mutates
    enclosing locals by reference (shared-scope semantics) and its own
    params/block-locals shadow. Block frames are `FrameKind.block`.
  - **Non-local control is targeted.** `Jump.retJ` carries a target FrameId;
    `frameK`/`blkFrameK` consume it only on a match, else pop and propagate —
    so a non-lambda block `return` reaches its `home` method (not the yielder),
    a lambda returns from itself, `break` becomes a return from the method the
    block was passed to (`brk` target on `blkFrameK`; `none` ⇒ detached-proc
    `LocalJumpError`), and `next` ends the block. `home`/return-target =
    `returnTarget` at the *defining* frame, so a `proc { return }` created
    inside a lambda returns from that lambda [V test_proc_024].
  - **`doReturn` checks target liveness at the return site**: a detached-proc
    return whose home already exited raises `LocalJumpError "unexpected
    return"` *there* (rescuable), not after unwinding past the handler
    [V tier3 blocks-jumps/000].
  - **Binding:** lenient for blocks/procs (pad nil, drop extras, auto-splat a
    single Array across ≥2 positionals), strict for lambdas (arity error).
    `Symbol#to_proc` / `&:sym` build a lambda-like closure `->(x,*a){x.m(*a)}`
    so it does **not** auto-splat an Array receiver.
  - **Dispatch:** `proc`/`lambda` (implicit) and `Proc.new` with a literal
    block *capture* (don't call); `Proc#call/()/[]` are intercepted in
    `invoke` (a pure builtin cannot push a frame); `Class#new` with a block
    gates (block would be silently dropped). Iterating builtins that yield
    (`Array#each`/`map`, `Integer#times`, `Hash.new{}`) stay `Unsupported`.
  - `CRubyNames.lean` **regenerated** with `Proc` + every bootstrap exception
    subclass added to the gen script's `FOLD`, so unmodeled `Proc#curry`,
    `NameError#receiver`, … gate instead of mis-raising `NoMethodError`.
  - Result: tier-0 bootstraptest **295 → 372 agree, 0 disagree**; tier-1
    (n=300) 214/0; regressions + tier-3 replay clean.

- **L17 — L2a: the object model — `class`/`module` definitions + `Class#new`.**
  Executable stepper only; the `class`/`module` heads no longer gate. Design
  draws on Essence-of-Ruby's object calculus (classes are ordinary heap objects;
  a class body is *evaluation in a frame whose self and cref are the class*) but
  stays desugar-first: no new evaluation machinery beyond a frame kind + two
  konts, everything else is heap mutation (the central bet).
  - **A class body is a frame** (`FrameKind.classBody`, new): `enterClassBody`
    opens (or creates) the named class object and runs the body with
    `self = defmod = the class`, under an ordinary `frameK` boundary, so a `def`
    inside installs on the class via the existing `defmod` path and the class
    definition's value is the body's last expression [V]. Creation allocates a
    `.cls` object (`klass` = Class, or Module for `module`); reopening checks
    class/module agreement (`"{name} is not a {class|module}"`) and, for a
    `class` with an explicit superclass, superclass match (`"superclass mismatch
    for class {name}"`) — all byte-exact [V]. The superclass expression
    evaluates first under a new **`classDefK`** kont; a non-Class value raises
    `"superclass must be an instance of Class (given an instance of {C})"` [V]
    (nil/true/false superclass gates — CRuby phrases those as "given nil").
  - **`Class#new` with a user `initialize`** can't be a pure builtin (it must
    push a frame), so it is intercepted in `invoke` (like `Proc#call`): allocate
    the instance, then run `initialize` under a new **`newK inst`** kont that
    discards `initialize`'s result and yields the instance (`new` = allocate ∘
    initialize ∘ return self). `enterUserMethod` was factored out of dispatch so
    `new` reuses the exact param-binding/frame-push path. A class with *no* user
    init falls to the `Class#new` builtin (unchanged); extra args there now hit
    the default `BasicObject#initialize` arity error [V]. Subclasses of a
    payload-core class (String/Array/…/Exception) inherit an allocator we don't
    model → **gate** (`payloadCoreClasses` in Builtins), never a wrong-payload
    object.
  - **Constants are cref-scoped** (artifact 03's *inheritance* phase):
    `constSetIn`/`constLookupFrom` write/read on the current `defmod` and walk
    its ancestors (bottoming out at Object = the toplevel namespace). So
    `class C; K = 2; end` no longer clobbers a toplevel `K` [V
    test_constant_cache_003]. The *lexical* phase (cref nesting) is not modeled
    at L0; `defmod` is the innermost enclosing class. `casgn` and class-name
    registration both route through `defmod`.
  - **`method_missing`** (artifact 02 §4): a genuine total miss (after the
    CRuby-shadow gates) dispatches a *user* `method_missing` with `(:name,
    *args)` + the block; the default (none modeled) is the existing byte-exact
    `NoMethodError`. Factored the default into `missNoMethod`.
  - **Frozen `@x=`**: assigning an ivar on a frozen `ref` self now raises
    `FrozenError "can't modify frozen {C}: {inspect}"` [V test_yjit_068]
    (previously mutated silently). The object-`inspect` embeds a fake address,
    but the obs layer normalizes `0x…`, so it agrees.
  - **Equality-dependent builtins gate on a user `==`**: `Array#include?`/`index`
    lean on default value-equality, which a pure builtin can't override, so they
    gate when an operand's class defines a user `==` (`Builtins.hasUserEq`)
    [V test_yjit_138]. Same shape as the `reprPure` gate, for equality.
  - **Still gated (L2b/L2c):** `super`/`zsuper`, `defs` (`def self.m`/`def o.m`),
    `sclass` (singleton class), eigenclasses, class variables (`@@x`), and
    `Class#new` with a *block*.
  - **Metatheory PoC kept green** (off-target; L13). Two pre-existing L1 rots
    surfaced and were fixed: `setLocal_heap` (setLocal was rewritten for the
    captured-chain walk and no longer routes through `setCurrentFrame`). The new
    frozen-`@x=` split is reflected by a second ivar-assign rule
    `asgnKIvarFrozen` (fires only when `inspect` is pure; the impure subcase
    gates, so completeness closes it by contradiction) + `raiseErr_heapSize` for
    `heap_monotone`. Still axiom-clean (`#print axioms`:
    propext/Classical.choice/Quot.sound only).
  - Result: tier-0 bootstraptest **372 → 428 agree, 0 disagree**; tier-1 (n=300,
    seed 11) 214/0; regressions (7) + tier-3 (16) replay clean.
