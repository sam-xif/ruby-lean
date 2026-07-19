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

- **L18 — L2b: `super`/`zsuper`.** Executable stepper only; the `super`/`zsuper`
  heads no longer gate. Two additions carry it (artifact 02 §2):
  - **The frame remembers its method name** (`Frame.meth`, new; set by
    `enterUserMethod`, which now takes `mname` — also `"initialize"` for
    `new`-dispatch and `"method_missing"`). `doSuper` reads the *enclosing method
    activation* (`methodFrameOf`, so `super` works from inside a block too): it
    re-dispatches `f.meth` starting **strictly after `f.defmod`** in
    `self`'s ancestor chain (`ancestors …|>.dropWhile (· != defmod)|>.drop 1`),
    keeping the same `self`. A user hit re-enters via `enterUserMethod` (so
    `super` chains); a builtin hit runs `Builtins.run`; a miss raises the
    byte-exact `NoMethodError "super: no superclass method '{m}' for {recv}"`
    [V] (`receiverDesc` form).
  - **`zsuper` (bare `super`) forwards the *current* parameter values**, not the
    original args: `zsuperArgs` re-reads the enclosing method's formal params
    from the method frame's locals (a `*rest` param spreads its array), matching
    CRuby [V: `def m(x); x=x+1; super; end` forwards the reassigned value].
    Explicit `super(args)` evaluates its args left-to-right under new
    `superArgK`/`superSplatK` konts. Both forms forward the method's block
    (`methodBlk`) unless a literal block is written on `super` itself.
  - **Gated (L2b tails):** `super`/`zsuper` with a `&`-block-pass or explicit
    block, and `zsuper` under a param shape beyond L2b (kwargs — not yet admitted
    upstream anyway).
  - **Still gated (L2c):** `defs` (`def self.m`/`def o.m`), `sclass`, eigenclasses,
    `@@cvar`.
  - Result: tier-0 bootstraptest **428 → 447 agree, 0 disagree**; tier-1 (n=300,
    seed 11) 214/0; regressions (7) + tier-3 (17) replay clean.

- **L19 — L2c: singleton methods + eigenclasses.** Executable stepper only;
  `defs` (`def self.m`/`def o.m`) and `sclass` (`class << o`) no longer gate.
  The heap already carried an `eigen : Option ObjId` slot and `classOf` already
  consulted it — L2c fills it in (artifact 01 §5).
  - **`eigenclassOf` (lazy, fuel-bounded)** gets/creates an object's eigenclass
    and wires its superclass to realize the metaclass chain: a regular object's
    eigenclass superclasses its real class (ordinary methods still resolve); a
    class/module's *metaclass* superclasses the metaclass of its superclass, so
    **class methods are inherited** (`B < A ⇒ B.cm` finds `A`'s), bottoming out
    at `Class` so `new`/`name`/… still resolve. Because `classOf` (used for
    dispatch) reads `eigen` but can't allocate, `enterClassBody` **eagerly**
    builds the chain when a class is created — otherwise `classOf(B)` would fall
    back to `Class` and miss inherited class methods [V test_method_216-family].
  - **`def RECV.name`** (`defsK` kont): eval RECV, then install the method on its
    eigenclass; **`class << OBJ`** (`sclassK`): eval OBJ, then run the body in a
    `classBody` frame whose self/cref is the eigenclass (so `def m` inside is a
    singleton method, and `def self.` / `class << self` inside a class body both
    reach the class's metaclass). Both flip `reprPure` on a repr-sensitive name.
    A singleton on an immediate (`def 1.m`) gates.
  - **`Object#class`/`instance_of?` skip the eigenclass** via a new
    `realClassOf` (dispatch keeps using `classOf`) — `o.class` is the real class,
    not `#<Class:o>` [V].
  - **Splat now gates on a user `to_a`**: `*obj` for a non-Array whose class
    defines a user `to_a` is a side-effecting dispatch a pure `spread` can't run
    → gate (previously masked because `def obj.to_a` itself gated at L2b) [V
    test_method_216]. Same shape as the `hasUserEq` / `reprPure` gates.
  - **Still gated:** `@@cvar`, `include`/`prepend`/mixins (MRO), `alias`,
    class macros (`attr_reader`/`define_method` — metaprogramming, deferred).
  - Result: tier-0 bootstraptest **447 → 468 agree, 0 disagree**; tier-1 (n=300,
    seed 11) 214/0; regressions (7) + tier-3 (17) replay clean.

- **L20 — export v4 decoder unblock via legacy param lowering (Phase 0).**
  The desugar side bumped `Export::VERSION` 3→4 (structured param nodes +
  additive heads; `../harness/desugar-dt/implementation-choices.md` C25–C29),
  which the v3-gated decoder rejected outright — `--sut lean` was fully red.
  This entry restores the SUT with **zero new stepper semantics**, so it can't
  regress the modeled fragment; the real param-binding work is Phase 2.
  - **Version gate** (`Syntax.lean` `program`): accept `v == 4`. A mismatch
    (e.g. a future v5) stays a plain decode `fail` → exit 1.
  - **Param slot: decode the node array, lower the three modeled kinds to the
    legacy sigil-string convention** `parseParams` already consumes
    (`preq name → name`, `prest name → "*"++name` / null → `"*"`,
    `pblock name → "&"++name` / null → `"&"`). The five genuinely-new binding
    kinds (`popt`/`pkey`/`pkwrest`/`pfwd`/`pdestr`) decode to an `unsupported`
    error. `Expr.def'/block/defs`, `MethodDef.params`/`Closure.params`,
    `parseParams`, and the synthetic `["__recv","*__rest"]` builtin params are
    **untouched** — the lowering is invisible below the decoder.
  - **`unsupported` helper** (`Syntax.lean`): a decode-time fragment gate that
    emits `.error "UNSUPPORTED: …"`. `Main` maps that prefix to engine exit 3
    (Unsupported, out of fragment), distinct from a genuine malformation, which
    stays a `fail` → exit 1 (`MODEL-BUG`). This is the first time gating happens
    at *decode* rather than *step* time — prior versions decoded every head and
    gated in `stepFn`.
  - **Additive heads gated** (explicit arms before the catch-all, so a truly
    unknown head is still a hard `fail`/exit 1): `kwargs`, `fwd`, `cpath`,
    `cpath_asgn`, `defined`, `redo`, `undef`, `alias`, `for`, `dowhile`.
    `case`/`when`, regex, and interpolated symbols desugar away (no new head)
    but emit sends the model gates via `CRubyNames` — 0 disagree preserved,
    coverage just doesn't grow there.
  - Result: tier-0 bootstraptest **468 → 493 agree, 0 disagree** (ratchet
    re-baselined to 493; the rise over the old 468 is desugar in-fragment
    growth 852→1227 landing in the already-modeled slice). `harness_error:1`
    (control-side `test_syntax_115`) and `control_invalid:7` are pre-existing.

## Milestone A — Phase 1 new heads (L21–…)

Grinding the v4-migration Phase 1: cheap additive heads that were gated
Unsupported in Phase 0, each a heap-mutation or a small stepper rule (project
bet: prefer heap mutation over new evaluation rules). Small-step throughout —
we do **not** adopt the big-step style of *Essence of Ruby* (APLAS'14) or the
desugaring-then-big-step of RIL (DLS'09); those papers inform the surface
coverage and desugaring targets, not the machine shape. Ratchet discipline:
0 disagree at every commit, agreement only up (baseline 493).

- **L21 — `class`/`module` scoped name (`class A::B`) gated at decode, not a
  hard fail.** The `class`/`module` decoder read its name via `asStr`; M5 now
  emits a `class A::B` name as a `["cpath", base, name]` node, so `asStr`
  hard-failed → exit 1 `MODEL-BUG` on 13 tier-0 cases (`class A::B; end`).
  These were surfaced (never silently absorbed) but wrongly classed as a model
  bug — the stepper simply does not model scoped *definition* names yet. New
  `defName` helper: bare-string name → `.ok`, anything else →
  `unsupported "scoped definition name (cpath in class/module)"` (exit 3, out
  of fragment). Non-mutual with `expr` (does not recurse into the cpath base).
  Removes 13 spurious MODEL-BUGs; scoped definitions become honest Unsupported
  until `cpath`/`cpath_asgn` land (L2x below). No agreement change expected
  (these programs were already not agreeing). **Superseded by L24** — the
  `defName` gate was removed once scoped definitions gained real support; the
  only remaining gate is `class A::B < Sup` (scoped def *with* an explicit
  superclass, rare, gated at decode).

- **L22 — `dowhile` reuses the existing `while` konts.** `begin body end while
  cond` (M6/M7 `[:dowhile, body, cond]`) evaluates `body` under the existing
  `whileBodyK cond body` continuation, which already sequences "after body →
  eval cond (`whileCondK`) → loop" and whose `unwind` arm already routes
  `break`→loop-exit and `next`→re-test-cond. So the run-once loop needed **no**
  new kont and no new `unwind` case — one `Expr.dowhile` head + one `evalExpr`
  arm. Verified `[V]` against CRuby incl. `next`/`break`/`false`-cond.

- **L23 — `undef`/`alias` as method-table heap mutation, with an `undef`
  tombstone.** `alias new old` copies the *current* resolved `MethodDef` for
  `old` (via `methodOn`, walking ancestors) under `new` on the current definee —
  an independent copy, so a later redefinition/undef of `old` does not affect
  `new` `[V]`. `undef n₁,…` installs a **tombstone** (`MethodDef.undefined`, new
  field defaulting false) per name: the entry exists so the ancestor walk stops
  there — blocking an *inherited* definition — but dispatch treats it as a miss.
  A plain delete would be wrong: `undef` of an inherited method (bootstraptest
  `test_method_109/110`) must raise `NoMethodError`, which a delete-from-own-
  table can't achieve. Dispatch (`invokeDispatch`) checks `md.undefined` on a
  hit and routes to the new shared `dispatchMiss` helper (extracted from the
  old `| none =>` branch — CRuby-shadow gating → `method_missing` → byte-exact
  `NoMethodError`); the genuine-miss branch now calls the same helper.
  `undef`/`alias` of a *non-existent* target raises `NameError` "undefined
  method '…' for class 'C'" / "for module 'M'" (byte-exact `[V]`); an
  eigenclass definee (address-dependent name) gates Unsupported. Both evaluate
  to `nil` `[V]`. A tombstone is treated as "not defined" by a subsequent
  `undef`/`alias` of the same name (→ `NameError`).

- **L24 — `cpath`/`cpath_asgn` + scoped `class`/`module` definitions.** Full
  scoped-constant support (artifact 03 §5), superseding L21's gate:
  - **Read `A::B`** (`Expr.cpath (base : Option Expr) name`): evaluate `base`
    (its own expr, so `A::B::C` nests for free), require it be a class/module
    (`cpathContainer`; else `TypeError "<inspect> is not a class/module"`),
    then `constLookupFrom` its namespace (ancestors). Miss → `NameError
    "uninitialized constant A::B"` (base's `className` + name). `base = none`
    (`::B`) reads the flat toplevel (Object), mirroring the plain-`const`
    unmodeled-vs-miss split.
  - **Assign `A::B = e`** (`Expr.cpathAsgn`): eval base **then** rhs (`[V]`
    order), `constSetIn` the base namespace, yields rhs. `::B = e` writes Object.
  - **Scoped defs** `class/module A::B … end` (`Expr.scopedClass`/`scopedModule`,
    base `Option Expr`): decode branches on whether the name node is a string
    (→ plain `class'`/`module'`) or a `cpath` node (→ scoped). Eval base →
    `enterScopedClassBody` opens/creates `name` inside that namespace, with the
    class name the full path `A::B` (so `A::B.name == "A::B"` `[V]`) and a new
    class superclassing `Object`. `class A::B < Sup` (explicit superclass) and
    absolute `class ::B` gate Unsupported (rare, not in corpus).
  - New konts: `cpathK`, `cpathAsgnK`, `cpathAsgnValK`, `scopedClassDefK`.

  **Ratchet (L21–L24, Phase-1 heads):** tier-0 bootstraptest **493 → 522 agree,
  0 disagree, 0 MODEL-BUG** (re-baselined to 522). One fidelity bug caught by
  the ratchet and fixed before commit: `alias some_method binding`
  (`test_yjit_352`) aliases the real-but-unmodeled `Kernel#binding`; the
  not-found path now consults `crubyShadow` and gates Unsupported rather than
  raising a spurious `NameError` (same split dispatch uses). `harness_error:1`
  (`test_syntax_115`) and `control_invalid:7` are pre-existing.

- **L25 — `for … in … do … end` iterating an `Array` natively.** `for tgts in
  coll; body; end` (`[:for, [[kind,name],…], coll, body]`). The loop variable(s)
  bind in the **enclosing** frame — `for` pushes no block frame, so `setLocal`
  leaks naturally (`for x in […]; end; x` is the last element `[V]`). Because
  the model gates `Array#each` (a pure builtin can't push a block frame), `for`
  cannot desugar to `.each`; instead the stepper iterates an `Array` payload
  directly (`forStartK` snapshots the element list; `forBodyK` is a loop marker
  in `unwind` — `break v` → `for`'s value is `v`, `next` → next element). `for`
  evaluates to its **collection** on normal exit `[V]`. Multiple targets
  destructure each element array-wise (an `Array` positionally; a scalar into
  the first target, rest `nil` — massign semantics `[V]`). Gated: a non-`Array`
  collection (`Range`, still unmodeled — the `(1..n)` cases gate here now
  instead of at decode) and any non-local target. New konts `forStartK`,
  `forBodyK`; helpers `forBind`/`forStep`.

- **L26 — `redo` in `while`/`dowhile`/`for` loops.** New `Jump.redoJ` (argless,
  like `retryJ`); `Expr.redo'` emits it. In `unwind`, a loop marker re-runs its
  **body** without re-testing the condition or advancing: `whileCondK`/
  `whileBodyK` → eval `body` under a fresh `whileBodyK`; `forBodyK` → eval `body`
  under the same `forBodyK` (same element still bound in the frame). `redoJ`
  propagates through `begin` regions via the existing `beginBodyK`/`ensureK`
  catch-alls, so `redo` inside nested `begin…ensure` correctly runs the ensures
  before restarting (bootstraptest `test_flow_043`: `[:ok, :ok2, :last]` [V]).
  **Gated:** `redo` in a **block** (`blkFrameK` carries no body expr — block
  invocation is driven by `callClosure`; the `1.times{…redo}` / `m{…redo}` cases
  stay Unsupported) and `redo` crossing a method boundary. `frameK`/`blkFrameK`
  gained explicit `redoJ` arms.

## Phase 2 — native param binding (L27–…)

The v4 handoff's Phase 2: replace the Phase-0 sigil-string param lowering with a
proper `Param` inductive and per-kind binding. Landed incrementally, each its own
ratchet.

- **L27 — `Param` inductive groundwork (no semantic change).** `def`/`block`/
  `defs`/lambda params are now `List Param` (mutual with `Expr`, since `popt`/
  `pkey` carry default expressions) instead of the sigil-string `List String`.
  - **Decoder:** `param` decodes all eight `PARAM_HEADS` into `Param`
    (`req`/`opt`/`rest`/`key`/`kwrest`/`block`/`fwd`/`destr`); no more decode-time
    gating of the five new kinds. Block-**locals** stay plain strings (`strList`)
    — only params became nodes. `Expr`/`Param` derive `Repr`/`Inhabited` via
    `deriving instance` after the `mutual` block.
  - **Threading:** `MethodDef.params`, `Closure.params`, `Kont.defsK.params`,
    `PendingBlk.lit.params`, and `reifyBlock` all carry `List Param`; the two
    synthetic builtin methods use `[.req "__recv", .rest (some "__rest")]`.
  - **Binding unchanged for now:** `parseParams` (the sigil splitter) is replaced
    by `classifySimple : List Param → Option SimpleParams`, which lowers a list
    using only `req`/`rest`/`block` to the legacy `(pre, rest?, post, block?)`
    shape and returns `none` if any `opt`/`key`/`kwrest`/`fwd`/`destr` is present.
    `enterUserMethod`/`callClosure`/`zsuperArgs` gate Unsupported on `none`
    (bind-time, vs. the old decode-time gate) — so **agreement is unchanged**;
    this commit is a pure refactor that unlocks per-kind binding in L28+.
    Anonymous `*`/`&` lower to name `""` (parity with `"*".drop 1`).

- **L28 — `popt` optional param defaults (native binding in `enterUserMethod`).**
  New `classifyFull : List Param → Option FullParams` (`pre`/`opt`/`rest?`/`post`/
  `block?`; still gates keyword/`kwrest`/`fwd`/`destr`). `enterUserMethod` now:
  - **Arity** `[V]`: with `*rest`, `n ≥ required`; else `required ≤ n ≤ required +
    nopt`. Expected string: `"{required}+"` with rest, `"{required}..{required+nopt}"`
    with optionals, plain `"{required}"` otherwise (byte-exact `ArgumentError`).
  - **Distribution** `[V]`: `pre` from the front, `post` from the back, the middle
    `args[np : n-npost]` fills the **leftmost** optionals (`filled =
    min nopt middle.length`); a `*rest` absorbs the surplus; the remaining
    (rightmost) optionals are omitted and take defaults.
  - **Default evaluation** `[V]`: omitted defaults are evaluated **lazily,
    left-to-right, in the callee frame, only for omitted params**, via a
    `optDefK` kont chain pushed above the method's `frameK`. Each default is
    bound (`setLocal`) before the next is evaluated, so a later default sees an
    earlier one (`b = a+1, c = b*2`). Only `pre` + already-filled optionals are
    in the frame while defaults run; **rest/post/block bind *after* all defaults**
    (carried in `optDefK.post`), because a Ruby default cannot see a trailing
    required / rest / block param (referencing one raises `NameError`).
  The no-optional path reduces to the previous binding exactly (parity), so this
  only adds coverage. Blocks (`callClosure`) and `zsuper` still use
  `classifySimple` — a block/zsuper with optionals gates for now (later
  increment). **Residual gap (noted):** a pathological default that references a
  *later* (post/rest/block) param reads an unbound local (→ `nil`) rather than
  raising CRuby's `NameError`; not observed in corpus/fuzzing, revisit if it
  surfaces.

- **L29 — `pkey`/`pkwrest` keyword params + the `kwargs` call-site marker.**
  Full keyword arguments, spanning call site, a threaded keyword channel, and
  callee binding with Ruby-3 separation.
  - **Call site:** new `Expr.kwargs (List KwEntry)` (`KwEntry.pair key val` /
    `KwEntry.splat e`; mutual with `Expr`/`Param`); a dynamic (non-symbol) key
    gates at decode. It only occurs as the last send/super/yield arg. `startArgs`
    detects it and runs `startKwargs`, evaluating pair values (and `**h`
    splats — hash entries merged, first-position/last-value dedup via `kwAdd`)
    left to right (`kwPairK`/`kwSplatK` konts), producing a `List (Value × Value)`
    keyword bundle that rides a new `kw` channel through `finishSend`/`invoke`/
    `invokeDispatch`/`blkCoerceK`/`enterUserMethod` (default `[]`).
  - **Ruby-3 separation** `[V]`: a callee with **no** keyword params receives the
    bundle as one trailing positional `Hash` (empty bundle vanishes) —
    `appendKwHash`; used for builtins, `method_missing`, and no-kw user methods.
    A callee **with** keyword params consumes the bundle as keywords.
  - **Callee binding (`enterUserMethod`, `classifyFull` extended with
    `keys`/`kwrest?`):** provided keywords bind directly (visible to defaults);
    missing required → `ArgumentError "missing keyword(s): :a[, :b]"`; unknown
    (no matching `pkey`, no `**kwrest`) → `"unknown keyword(s): …"` (both
    singular/plural byte-exact `[V]`); `**kwrest` collects leftovers into a Hash;
    keyword defaults are lazy, in-frame, left-to-right, **after** positional-opt
    defaults, reusing the `optDefK` chain.
  - **Gated:** keyword args to a `Proc#call`, to `super` / `yield`, and any
    block/`zsuper` with keyword params (those still go through `classifySimple`).

- **L30 — `...` argument forwarding (`def m(...); g(...); end`).** Reuses the
  P3 keyword/rest/block machinery instead of a bespoke bundle. `classifyFull`
  expands a `Param.fwd` to a synthetic `*__fwd_rest, **__fwd_kw, &__fwd_blk`
  (three reserved locals), so a `(...)`-method captures all positional args, all
  keywords, and the block on entry via the existing binding. New `Expr.fwd` (the
  `["fwd"]` call-site marker): `startArgs` reads those three locals directly (no
  evaluation — `forwardBundle`) and dispatches `acc ++ __fwd_rest` positionals
  with the `__fwd_kw` keyword bundle and `__fwd_blk` block via `invoke`. `g(1,
  ...)` prepends the leading args. Gated: `...` to `super`/`yield` (rare).

- **L31 — `pdestr` destructuring params (method params).** `def m((a, *b),
  c)` — a destructuring param occupies one positional slot and array-destructures
  its arg. `classifyFull` replaces each `Param.destr` with a synthetic
  `__destr_k` required name (so the pre/opt/rest/post scan is unchanged) and
  records `(name, subs)` obligations in `FullParams.destrs`. After positional
  binding, `enterUserMethod` reads each synthetic slot's value and expands it via
  `destructureBind` (recursive, `partial`): coerce to an array (elements if an
  `Array`, else wrap `[v]`), bind leading positionals from the front, `*rest` the
  middle, trailing from the back, nested `(…)` recurse — massign semantics `[V]`
  (short array → `nil` fill; scalar → wrap). Expanded bindings join Phase A
  (visible to defaults); synthetic names are dropped. With this,
  `classifyFull` handles all eight `PARAM_HEADS`, so **method params never gate on
  shape** any more. **Gated (follow-up):** block/`{|(a,b)|}` destructuring —
  `callClosure` still uses `classifySimple` (lenient block arity + auto-splat is a
  separate binding path); block destructuring stays Unsupported for now.

## Iterating builtins that yield (L32–…)

The top remaining lever: builtins like `Array#each` / `Integer#times` that *call a
block* per element. A pure `Builtins.run` cannot push a block frame, so these were
gated. The fix is a stepper-level mechanism, not a builtin.

- **L32 — native block-iteration mechanism + `Array#each` + `Integer#times`.**
  Mirrors `enterUserMethod` (push a `break`/return-target frame) + the `for` loop
  (a per-element continuation), reusing `callClosure`/`blkFrameK`/`frameK`/
  `unwind` wholesale:
  - `startIter` pushes an activation `Frame` (the iterator call itself) under a
    `frameK fid`, then runs `iterStep`.
  - `iterStep` (non-recursive; the loop is driven by the `iterK` kont) either
    delivers the final value (`.value` flows into `frameK fid`, popping the
    iterator frame) or pushes an `iterK` and `callClosure`s the block for the next
    element with `brk = fid`.
  - `iterK` folds the block's result per `IterKind` (`ignore`/`collect`/`fold` —
    L33 uses the latter two) and calls `iterStep` for the next element.
  - Control-flow falls out for free: `break v` in the block → `blkFrameK`
    converts it to `retJ v fid` → propagates past `iterK` (unwind catch-all) →
    `frameK fid` returns `v` from the iterator call; `next v` → block value for
    that element; `return` → still targets the block's home method (past `fid`).
  - **Dispatch hook:** `tryIterator` runs only on a lookup **miss** (in
    `dispatchMiss`, before the CRuby-shadow gate) and only when a **block** is
    present — so a user override wins, and a blockless `each` stays gated (it would
    be an Enumerator). `each` on any `.arr` payload (incl. inherited), `times` on
    an `Integer`. `retVal` (ignore-kind) is the receiver [V].

  Two latent gaps that `each`/`times` *exposed* (they were masked while the loop
  gated) are now gated cleanly rather than disagreeing:
  - **`const_missing`** — `A::FOO` on a base defining `self.const_missing` invokes
    the hook in CRuby; `cpathK` now gates ("const_missing hook") instead of
    raising a spurious `NameError` (`test_class_046`).
  - **standard mixins not in the ancestor chain** — a user method monkey-patched
    onto `Enumerable`/`Comparable` and called on an `Array`/`Hash`/`Integer`/… is
    resolvable in CRuby (those classes include the module) but not in the L0 heap
    (no MRO). `mixinShadow`/`stdMixins` gate such a miss ("method via unmodeled
    mixin …") instead of `NoMethodError` (`test_jump_011`). Superseded by MX1.

- **L33 — `map`/`collect`, `each_with_index`, `inject`/`reduce`, `Hash#each`.**
  All reuse the L32 mechanism via `IterKind`: `map`/`collect` = `collect` (gather
  block results into a new Array); `each_with_index` = `ignore` with two-element
  per-iteration arg lists `[e, i]`; `inject`/`reduce` = `fold` (block gets
  `acc :: [e]`, result becomes the next `acc`) — `inject{}` seeds with the first
  element and folds the rest, `inject(seed){}` folds all, empty+no-seed → `nil`;
  `Hash#each`/`each_pair` = `ignore`, yielding one allocated `[k, v]` array per
  entry (block `|k,v|` auto-splats, `|pair|` gets the array). `tryIterator` gained
  the call `args` (for `inject`'s seed). Block form only — `inject(:sym)` (no
  block) is not intercepted and gates as before.

## Mixins (L34–…)

- **L34 — `include` (MRO) + `self.included` hook + `extend`.** `ClassPayload`
  gains `includes : List ObjId` (most-recent-included last). `ancestors` now
  splices each class's `include`d modules in just above it (most-recent-first,
  modules-of-modules expanded via `modAncestors`), de-duped keeping the first
  occurrence — **identical to the old superclass walk when `includes` is empty**,
  so behaviour-preserving on the mixin-free fragment. `tryMixin` (in
  `dispatchMiss`, miss path so a user override wins): `include M` (single module,
  class/module receiver) appends `M` to `includes` and fires `M.included(recv)`
  if defined (via `enterUserMethod` under a new `includeK` kont that yields the
  receiver); `obj.extend(M)` mixes `M` into `obj`'s eigenclass (its instance
  methods become singleton methods). Both return the receiver. **Known limitation
  (not include's fault):** a mixin method that references a *nested* constant
  (`P::CM`, e.g. `Parameterizable`'s `base.extend(ClassMethods)`) needs
  lexical-cref constant lookup, which L0 approximates by `defmod` — so such a
  reference still misses. `extend` with an `extended` hook gates.

- **L35 — class macros + reflection: `attr_*`, `method_defined?`, `send`,
  `respond_to?`.** All via `tryReflect` (dispatchMiss miss path, user override
  wins) except `send` (in `invoke`, needs re-dispatch):
  - `attr_reader`/`attr_writer`/`attr_accessor` synthesize getter (`@x`) / setter
    (`x=`, body `@x = __v`) `MethodDef`s on the class and return the defined names
    as symbols (`[:x, :x=, …]`, Ruby-3 [V]).
  - `method_defined?(:m)` — instance-method presence on the class (own/inherited
    user method, or a CRuby builtin via `crubyShadow`); `respond_to?(:m)` — same
    on a receiver (`lookup` or `crubyShadow`); both take a Symbol or String.
  - `send`/`public_send`/`__send__` re-dispatch the first arg (Symbol/String) on
    the receiver with the rest — handled in `invoke` (now `partial`, since it
    self-calls; `StepResult` derives `Inhabited`), gated behind a `send` user
    override check. The `public_send("#{k}=", v) if respond_to?("#{k}=")` pattern
    (Parameterizable#set_parameters) now runs [V].

  Ratchet caught three MX2 bugs, fixed before commit: (1) accessor bodies must use
  the `@`-prefixed ivar name (`@x`, not `x`) — the desugar stores ivars with `@`;
  (2) `respond_to?`/`method_defined?` must also count methods on user-reopened
  standard mixins (`Kernel` universally, `Enumerable`/`Comparable` per class —
  `mixinDefines`/`stdMixins`, `Kernel` added to `stdMixins`); (3) `respond_to?`
  gates when the method isn't found and the receiver has a user
  `respond_to_missing?` (which can run arbitrary code) rather than guessing
  `false`.

## Lexical constants (L36)

- **L36 — cref-scoped constant lookup (artifact 03 §4).** Constant resolution was
  `constLookupFrom defmod` (inheritance phase only, keyed on the dispatch owner),
  which loses the lexical scope for `def self.m` in a module (owner = eigenclass,
  not the module). Now `Frame` and `MethodDef` carry a `cref : List ObjId` (the
  enclosing class/module bodies, innermost first): the toplevel is `[Object]`; a
  class/module body pushes `k :: enclosing.cref`; `def`/`defs` capture
  `currentFrame.cref` (so a singleton method keeps its lexical module even though
  its owner is the eigenclass); method/block frames inherit it (blocks via the
  captured frame). `const` lookup is now two-phase: the **lexical** phase
  (`constOwn` on each cref scope, innermost first) then the **inheritance** phase
  (`constLookupFrom defmod`, ancestors) then the toplevel/unmodeled split. A
  superset of the old lookup ⇒ behaviour-preserving on tier-0 (flat agreement),
  while resolving nested constants like `Parameterizable::ClassMethods` — which
  unblocked the ai4r q_learning/SOM drivers past the `included`→`base.extend(
  ClassMethods)` `NameError` (they now reach the next real gate, `Hash#merge`).

## Core-library tail for the ai4r drivers (L37+)

- **L37 — `Hash#merge` (non-mutating, variadic, blockless).** The first builtin
  in the demand-driven core-library tail that `bin/lift ai4r` gates on (blocks
  q_learning + both multi-node/single SOM drivers via
  `parameterizable.rb`'s `get_parameters_info.merge(...)` and `som.rb`'s
  `@init_weight_options.merge(distance_metric:, rng:)`). Folds each Hash argument
  into a copy of self, later keys overriding: an existing key keeps its position
  but takes the new value, a new key is appended — CRuby's order semantics,
  reusing the `Hash#[]=` update-or-append rule. **Not modeled:** the
  conflict-resolution *block* form (`merge(o){|k,old,new| …}`) — a pure builtin
  in `run` never receives the block, the same known limitation as `Hash#fetch`'s
  block form; the drivers never use it. A non-Hash argument gates (`Unsupported`)
  rather than risk emitting a wrong `TypeError` message. Registered in the `hashId`
  boot table (`Heap.lean`).

- **L38 — `Hash#each_key` / `Hash#each_value` iterators.** Added to the `.hsh`
  branch of `tryIterator` (Interp.lean) next to `each`/`each_pair`: `each_key`
  yields the key alone per entry, `each_value` the value alone, both returning
  the hash. Block-driven like the other native iterators (a blockless form would
  be an Enumerator, still gated). Gated q_learning + both SOM drivers via
  `parameterizable.rb`'s `get_parameters_info.each_key { … }`.

- **L39 — module/class reopening reuses the existing object; nested names are
  qualified.** Two coupled bugs in `enterClassBody` (unscoped `class`/`module
  NAME`), both surfaced once the SOM drivers reached `Ai4r::Som` after L38:
  1. **Reopening allocated a fresh object.** Reopen detection used
     `constLookup name` (flat *toplevel* only), so `module B` inside a reopened
     `module A` never found the existing `A::B` — it created a duplicate and
     `constSetIn`-clobbered `A::B`, so `first.equal?(A::B)` was `false` (CRuby:
     `true`) and `class TwoPhaseLayer < Layer` in a reopened `Ai4r::Som` raised a
     spurious `NameError: uninitialized constant Layer`. Fix: look up `name` in the
     **current innermost namespace only** — `constOwn defmod name`. This is
     deliberately *not* the lexical cref walk used for constant *reads* (L36):
     verified against CRuby, `class Foo` nested in `M` creates `M::Foo` and does
     **not** reopen a lexically-visible `::Foo`. At the toplevel `defmod` is
     `Object`, so it coincides with the old flat lookup (behaviour-preserving there).
  2. **Nested classes got a bare `name`.** A newly-created nested class/module took
     `name` unqualified, so `A::B::TwoPhaseLayer.to_s` was `TwoPhaseLayer` (CRuby:
     `A::B::TwoPhaseLayer`). Fix: qualify with the enclosing namespace
     (`{className defmod}::{name}`) unless `defmod` is Object. Mirrors
     `enterScopedClassBody`'s `fullName`.

- **L40 — arity `ArgumentError` lists required keywords.** CRuby's wrong-number-of-
  arguments error names the method's required keywords when it has any, e.g.
  `wrong number of arguments (given 1, expected 0; required keywords: a, b)`. The
  suffix lists **all** keyword params without a default — *even ones the caller
  supplied* — because the positional-arity check fires before keywords are bound
  (tier-3 `kwargs/004`: `c:` is listed though `c: 3` was passed). Names are **bare**
  in this suffix (no leading `:`), unlike the standalone `missing keyword: :a`
  message. Singular `keyword`/plural `keywords` per count. Fixed the three tier-3
  kwargs disagreements surfaced by the L39 ratchet.

- **L41 — `Hash.new(default)` (static default value).** Added a `hashDflt :
  Option HashDefault` field to `Object` (`HashDefault := val Value | prc ObjId`);
  a field with a default, so no existing `.hsh` match site changes. `Hash.new(v)`
  allocates an empty hash with `hashDflt := val v`; `Hash#[]` on a miss returns the
  default value instead of `nil`; `Hash#dup` copies the default. The `prc`
  (default_proc) variant is created/consulted in L42 — reaching a `prc` default in
  the pure `Hash#[]` builtin gates (the proc call needs a frame). Unblocks the
  inner `Hash.new(0.0)` q-table of the q_learning driver (final rendering still
  gates on Float#inspect).

- **L42 — `Hash.new { |h,k| … }` default_proc.** The block form of the L41 default:
  `Hash.new { block }` stores `hashDflt := prc <blockObj>` (created at the
  `Class#new`-with-block site in `finishSend`, which otherwise gates). On a `[]`
  *miss*, `invoke` now intercepts a hash receiver whose default is a `prc` and calls
  the proc with `(h, key)` via `callClosure` — its result is the value of `h[key]`,
  and the proc may mutate `h` (e.g. the auto-vivifying `h[k] = Hash.new(0)`). A
  present key, or a `val`/absent default, falls through to the ordinary builtin. This
  is the closure-on-miss mechanism a pure builtin can't provide (mirrors how
  `tryIterator` drives blocks). Unblocks q_learning's `Hash.new { |h,k| h[k] =
  Hash.new(0.0) }` q-table.

- **L43 — `Kernel#rand` as a deterministic placeholder for the *unseeded* RNG.**
  `rand` → `0.0` (Float in [0,1)); `rand(n)` (n>0) → `0` (Integer in [0,n)); other
  forms gate. This is sound for the differential tester precisely because CRuby's
  unseeded `rand` is itself nondeterministic: any program whose *output* depends on
  `rand`'s value differs between CRuby's two determinism runs → `control_invalid`
  (excluded), so a fixed value can never produce a recorded disagreement. Meanwhile
  output-*independent* uses execute correctly — q_learning's `rand < @exploration`
  with `exploration: 0.0` always takes the exploit branch (`0.0 < 0.0` is false, as
  is CRuby's `rand < 0.0`). Load-bearing invariant: **seeded** RNG (`srand`,
  `Random.new(seed)`) stays UNMODELED and therefore *gates* — so a program CRuby
  runs deterministically via a seed cannot silently diverge from this placeholder;
  it stops at a clean `Unsupported` instead. If seeded determinism is ever needed,
  it requires a faithful CRuby-compatible Mersenne Twister, not this stub.

- **L44 — `max_by` / `min_by` iterators (Array + Hash).** Two new `IterKind`s
  (`maxBy`/`minBy`) that keep the element whose block value is extreme. The block
  result comes back to `iterK` without its source element, so `iterK` gained a `cur`
  field (the element currently yielded, `= a.head`); the accumulator holds
  `[bestElem, bestKey]`. Comparison is numeric only (`Builtins.numOrd?`); a
  non-numeric block value gates (a general `<=>` dispatch over objects isn't
  modeled, as with `sort`/`min`/`max`). Ties keep the earliest element (strict
  improvement replaces), matching CRuby. Wired into `tryIterator` for arrays
  (`each1` elements) and hashes (`[k,v]` pairs). Completes the q_learning driver:
  `@q[state].max_by { |_, v| v }.first` now runs — **q_learning agrees byte-exact
  with CRuby** (`Best action from s1: b`), the 4th of 7 ai4r drivers to pass.

- **L45 — `Float#to_s`/`#inspect`: shortest round-tripping decimal (supersedes the
  L8 gate).** New `RubyCore/FloatFmt.lean`: Burger–Dubois free-format Dragon4 over
  the raw IEEE-754 bits (`Float.toBits`) with exact `Nat`/`Int` bignum arithmetic —
  Lean's `Float.toString` is lossy fixed 6-digit `%f`, unusable. Produces the
  shortest decimal that round-trips, with round-half-to-even boundary inclusivity
  and carry propagation on a rounding overflow. `layoutFloat` then applies CRuby's
  `flo_to_s` layout, whose fixed-vs-scientific rule was derived empirically (not the
  folklore `decpt ≤ 15`): for `decpt > 0`, fixed iff `decpt ≤ max 15 (ndigits-1)`
  (so `decpt = 16` is fixed only with a genuine fractional digit, e.g.
  `1364804082905693.5`, else scientific like `1.0e+15`); for `decpt ≤ 0`, fixed
  while `decpt > -4`. Specials: `Infinity`/`-Infinity`/`NaN`, `0.0`/`-0.0`, always a
  fractional digit, sci exponent `decpt-1` zero-padded to ≥2. Wired into both `.flt`
  arms of `Repr` (inspect + to_s), so `puts`/`p`/interpolation/final-result/direct
  sends all format correctly. Validated against CRuby over 2037 random+edge doubles
  (0 mismatches). Unblocks **som_data** (byte-exact) and is the prerequisite float
  layer for the SOM training drivers. Depends on desugar **C31** (see below) so a
  `-0.0` literal reaches the model as a real negative zero.

- **L46 — `Random.new(seed)` + `Random#rand`: CRuby-compatible MT19937.** New
  `RubyCore/MT.lean` ports MT19937 exactly (validated against the classic
  `init_by_array` test vector `1067595299` and CRuby `Random.new(42).rand` =
  `0.3745401188473625…`). Ruby seeds a 32-bit-fitting integer with
  `init_genrand(seed)` (NOT `init_by_array`, which is only for bignum seeds — a
  subtlety found empirically), and `rand` with no argument draws a 53-bit double
  `((a>>5)*2^26 + (b>>6)) / 2^53` from two tempered outputs. A `Random` boot class
  (`randomId := 30`, `mainId` → 31) holds its MT state in a new `Payload.rng`
  variant; `Random.new(int)` (in `newImpl`) seeds it, `Random#rand` (no arg) draws
  and writes the mutated state back to the heap. **Unseeded** `Random.new` and
  `rand(n)` gate (the former is nondeterministic — cf. L43; the latter is Ruby's
  separate bounded-draw algorithm, unused by the drivers). This is the RNG the
  seeded SOM driver variants need so their weights match CRuby bit-for-bit.

- **L47 — `Kernel#require` / `require_relative` are no-ops returning `true`.** In a
  linked program the internal `require_relative`s are already inlined; a residual
  `require "benchmark"`/`require "yaml"` (stdlib) just needs to not gate. Returns
  `true` (CRuby's first-load result); the value is essentially never observed. A
  library actually *used* after such a require still gates on its own methods, so
  this cannot manufacture a wrong answer for modeled code.
