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
- **L13 — metatheory lives under `RubyCore/Proof/`, off the default target.**
  `Step.lean` (control-core inductive `Step` + `Step.sound`/`Step.deterministic`),
  `Adequacy.lean` (`Step.heap_monotone`, `Step.complete`, `Step.adequacy`),
  `TypeSafety.lean` (the type-safety-as-reachability metatheory — see L51),
  `Demo.lean` (`example`s: non-vacuity, a 5-step reduction of `1;2`, adequacy on
  a real `init`, and the type-safety demonstrations of L51). They are part of the
  `RubyCore` lib glob but *not* imported by `Main`, so `lake build` (the
  `rubycore` exe) never touches them; build with
  `lake build RubyCore.Proof.TypeSafety RubyCore.Proof.Demo`. Rationale for the
  separation: kept physically apart from the SUT so a machine-shape change never
  reddens the difftest binary. **Refreshed against the current stepper** (was
  written pre-L2; the `Jump` type gained `redoJ`): the control core now also
  covers `redo`/`dowhile` (the third loop jump + do-while), `Step.complete`'s
  `cases j`/`FragJump`/`FragExpr` updated accordingly. Soundness is definitional,
  so the pre-existing rules stayed faithful without change. Deps audited via
  `#print axioms`: only `propext`/`Classical.choice`/`Quot.sound` (no `sorryAx`,
  no `native_decide`).
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

- **L48 — `Math` module (`sqrt`/`exp`/`log`) + `Range` class.** `Math` is a boot
  constant (`mathId`); its functions are special-cased in `invoke` on the receiver
  id (they are singleton fns; no eigenclass machinery at boot) and map to
  `Float.sqrt`/`exp`/`log`, coercing Int→Float and gating domain errors
  (`sqrt`/`log` of ≤0). `Range` is a boot class (`rangeId`) with a new
  `Payload.range lo hi excl`; range literals already desugar to
  `Range.new(lo, hi, excl)` (`newImpl` builds the object). Modeled methods:
  `first`/`begin`, `last`/`end`, `exclude_end?`; `inspect`/`to_s` render
  `lo..hi`/`lo...hi`. Needed for SOM's `Math.sqrt` distances and `range: 0..1`
  weight bounds.

- **L49 — numeric + array builtins for the SOM path.** `Integer#to_f`/`Float#to_f`
  (identity), `Float#to_s`/`#inspect` now route through the L45 formatter (the
  Builtins arm had still gated — direct/interpolation `.to_s` bypassed the Repr
  wiring), `Float#to_i`/`#to_int`/`#truncate` (exact truncation toward zero via the
  IEEE bits, no lossy Float→Int), `Float#**` (`Float.pow`, Int/Float exponent),
  `Float#%` and mixed `Integer#% Float` (float modulo `x - y*(x/y).floor`, sign of
  divisor). `Array.new(n)`/`Array.new(n, default)` (the block form gates),
  `Array#each_index`, `Array#[]` with a **Range** slice (endless `a[1..]`, bounded,
  exclusive, negative indices), and splat of an integer Range (`[*(1..5)]` → `spread`
  expands it). `Module#private`/`protected`/`public` are **not** modeled — they gate
  (visibility enforcement is out of L0, and bootstraptest checks it, so a no-op would
  produce wrong answers). To keep the miss trichotomy honest for the new modeled
  classes, `scripts/gen_cruby_names.rb` now includes `Range` (+ `Enumerable`) and
  `Random`, so an unmodeled Range/Enumerable method (`map`/`each`/`to_a`/…) gates as
  `Unsupported` rather than mis-raising `NoMethodError`.



- **L50 — the SOM *training* drivers stay gated (visibility, then a fuel wall).** SOM
  now has every *value-level* feature it needs: the seeded MT19937 RNG (L46, validated
  against CRuby reference draws), `Math`/`Range` (L48), and the float pipeline (L45/L49)
  were confirmed correct on a small seeded SOM (`initiate_map` + `global_error`) that
  agreed byte-exact with CRuby *while visibility was a no-op*. But `som.rb` runs a bare
  `private` at class-definition time, and visibility is deliberately **not** modeled at
  L0 (L49: a `private` no-op gives wrong answers on bootstraptest's enforcement checks,
  so `private` gates). So every SOM program now stops at `Unsupported "Module#private"`.
  Even past that, `som_single`/`som_multi_node` train ~250 epochs — hundreds of millions
  of small-step transitions the functional interpreter can't finish in any practical
  budget (5M steps alone >2 min). Both blockers are neutral gates, **not** disagreements
  (the 0-disagree invariant holds). Unblocking SOM execution needs (a) real visibility
  enforcement — mark `private`d methods, raise only on an *external* call, so SOM's
  internal self-sends still run — and (b) an interpreter-throughput fix. Deterministic
  seeded/no-Benchmark example variants are a local recipe under the *gitignored* fetched
  `vendor/ai4r/examples/som/`, not committed.

- **L51 — type safety as reachability, proved over the full stepper**
  (`RubyCore/Proof/TypeSafety.lean`; realizes `type-safety-by-reachability.md`
  §3–4). The stretch result: a program is "type-safe" iff the **type-stuck
  outcomes are unreachable** from `Machine.init` — no new type system.
  - **Bad-state predicate.** `typeStuck : StepResult → Prop` fires only on the
    *terminal* `uncaught exc` whose class `isA` a member of `typeErrorFamily`
    (`NoMethodError`/`ArgumentError`/`TypeError`, closed under subclassing via
    `isA`). Load-bearing faithfulness: a rescued `NoMethodError` is a transient
    `raiseJ`, never an `uncaught` outcome, so `respond_to?`-fallback/duck-typing
    idioms are type-safe (more precise than a type system). A bare `NameError`
    is deliberately *not* in the family (its ancestors miss all three).
  - **Transition relation choice (the key decision).** Reachability ranges over
    `SmallStep m m' := stepFn m = .next m'` — the **full** executable relation,
    NOT the partial control-core inductive `Step`. A subset relation reaches
    *fewer* states, so safety over it would not transfer; formulating over
    `stepFn` is both the sound choice and why the metatheorem applies to real
    programs (dispatch/classes/blocks) including `q_learning_extended`. The
    inductive `Step` is bridged in by `Step.subset_smallStep` (= `Step.sound`).
  - **The metatheorem.** `invariant_sound` (progress/preservation): any `I` with
    Initiation `I (init p)`, Consecution `∀ m m', I m → SmallStep m m' → I m'`
    (preservation), Safety `∀ m, I m → ¬ aboutToTypeStick m` (progress) proves
    *no reachable outcome is type-stuck*, all inputs / unbounded fuel. Proved
    once (short induction on the `Reaches` RT-closure); per program an untrusted
    engine supplies `I` and the trusted validator re-checks the three locals.
  - **Direction A (execution certificate).** `run_value_type_safe`:
    a run terminating in a value reaches a `done` outcome, never type-stuck — a
    self-certifying witness for that input (`run_value_reaches_done` connects the
    fuel iterator to `Reaches`). This is the certificate `bin/demo-qlearning
    --extended` produces for `q_learning_extended` (the interpreter executes it
    to a value, byte-exact with CRuby). Note: dispatch is `partial def invoke`,
    which doesn't reduce definitionally, so a real program's certificate comes
    from *executing* the trusted stepper, not an in-kernel `rfl`.
  - **Direction B demo (`Demo.lean`).** `while true do nil end` proved type-safe
    for unbounded fuel + all inputs via a hand-supplied five-state inductive
    invariant (`loopInv`) discharging init/cons/safe — the whole Direction-B
    pipeline in miniature. (Control-core programs can only raise `FrozenError`,
    which is outside the type family, so the fragment itself never type-sticks;
    the loop demo shows the machinery on an unbounded run.)
  - Axiom audit: `propext`/`Classical.choice`/`Quot.sound` only.
  - **Concrete q_learning proof (`QLearningTypeSafe.lean`, opt-in, NOT
    axiom-clean).** Answers "prove the *actual* q_learning_extended type-safe via
    the run-to-value lemma." `run` iterates `stepFn`, whose dispatch bottoms out
    in `invoke` — now a well-founded `def` (L52), so it *reasons* symbolically but
    compiles to `Acc.rec`, which the kernel's whnf does not reduce; so `rfl`/
    `decide` still cannot *evaluate* a concrete dispatching run (verified). The
    only in-proof way to evaluate one is `native_decide` (compiles + runs the
    interpreter), which adds `Lean.ofReduceBool` + the compiler to the TCB — the
    single `..._native.native_decide.ax_1_1` axiom. Kept in its own file, OUT of
    the axiom-clean core. The bridge `runsToValue_type_safe` (runs-to-value ⇒
    type-safe, via `run_value_type_safe`) is itself axiom-clean; only the
    concrete `qlearning_runs_to_value`/`qlearning_type_safe` carry the
    native-decide axiom. The 8 KB linked AST is embedded as a JSON string literal
    (byte-identical to `bin/demo-qlearning --extended`'s input).

- **L52 — `invoke` de-`partial`ized to a well-founded `def` (enables Direction-B
  dispatch proofs).** A `partial def` is *opaque in proofs* (no equational
  lemmas; `unfold`/`simp` fail — verified), so symbolic reasoning about ANY
  dispatch step was impossible, blocking the type-safety invariant approach
  (`type-safety-by-reachability.md` §4) for every real program. `invoke`'s ONLY
  self-recursion is the `send`/`public_send`/`__send__` unwrapping
  (`args = nameArg :: rest`, recurse on `rest`), so it is well-founded on
  `args.length`; `invokeDispatch`/`invokeMaybeNew` (its `where` helpers) and
  `enterUserMethod`/`callClosure`/`Builtins.run` never recurse back into it.
  Changed `partial def invoke` → `def invoke` + `termination_by args.length` /
  `decreasing_by simp_wf`. **Behavior-preserving** (same logic, same compiled
  code): tier-0 `--sut lean` stayed **722 agree, 0 disagree** after the change.
  Now `invoke.eq_def`/`invoke.eq_1` exist and dispatch steps can be reasoned
  about — the prerequisite for the T5 object-model invariant proof. (Note: WF
  recursion compiles to `Acc.rec`, so this does NOT make `rfl`/`decide` evaluate
  concrete runs — L51's native_decide caveat stands; the win is *symbolic*
  reasoning, not kernel evaluation.) `destructureBind`/`modAncestors`/`Repr.*`
  stay `partial`, but are off the T5 path (no destructuring params, mixin-free
  classes, no `puts`/`==`/`to_s` in the proof-relevant fragment).

- **L53 — T5 object-model dispatch-progress core (`RubyCore/Proof/T5.lean`).**
  First increment of the T5 (`class_hierarchy`) calibration toy
  (`type-safety-by-reachability.md` §9.1). `dispatch_progress`: a config poised
  to dispatch `recv.m` (zero-arg, `recvK`) takes a step *to the method
  activation* — not `dispatchMiss`/`NoMethodError` — provided the heap's method
  table resolves `m` on `recv` (hypotheses `hlook`/`hb`/`hu`/`hbtw`/`hsing`,
  simple params). `dispatch_not_typestick`: hence `¬ aboutToTypeStick`. This is
  the "receiver responds to `m`" store-typing clause (§4.2), proved over the real
  `stepFn`/`invoke` (`rw [invoke.eq_def]` then drive `invoke.invokeDispatch`) —
  the first proof to exploit L52. **Axiom-clean** (parameterized over the heap
  facts). The hypotheses have the shape of `lookup`/`crubyShadow` results, which
  — after L55 made `Boot.initHeap` kernel-reducible — are now discharge-able by
  **`decide`, axiom-clean** (no `native_decide`). Planned increment 3: a
  conditional `invariant_sound` loop assembly (`cons` via `dispatch_progress`,
  `safe` off the "no type-family raise in flight" clause), its resolution
  hypotheses discharged by `decide` over the reducible reachable heaps — a fully
  axiom-clean Direction-B proof (a builtin-dispatch loop `while true; 1.succ; end`
  is the simplest instance: heap stays `initHeap`, no frame growth).

- **L54 — concrete T5 programs + Direction-A verdicts (`RunCert.lean`,
  `T5Concrete.lean`, `type-safety-demos/`).** Two runnable T5 sources: `t5_safe.rb`
  (base + `Dog`/`Cat` subclasses, all respond to `speak`, receiver from a mixed
  array) and `t5_buggy.rb` (`Rock` lacks `speak`). Both reproduce CRuby
  byte-for-byte in the model (safe → prints + `nil`; buggy → `NoMethodError:
  undefined method 'speak' for an instance of Rock`, after printing `woof`).
  Because both terminate, Direction A (§3) gives immediate verdicts by execution:
  - `RunCert.lean` (**axiom-clean**): `runsToValueB`/`runsToTypeErrorB` (parse +
    decode + run, classify the outcome) and the bridges `runsToValueB_type_safe`
    (value ⇒ type-safe) / `runsToTypeErrorB_unsafe` (uncaught type-family ⇒ a
    type-stuck outcome is reachable, the run is the counterexample), plus
    `isTypeErrorB` (decidable mirror of `isTypeError`). `TypeSafety.lean` gains
    `run_uncaught_reaches`/`run_typeError_unsafe` (the disprove-direction duals of
    `run_value_reaches_done`/`run_value_type_safe`).
  - `T5Concrete.lean` (**opt-in, native_decide**): `t5_safe_type_safe` (proved)
    and `t5_buggy_unsafe` (disproved) — the booleans are discharged by
    `native_decide` because *running* the program is not kernel-reducible
    (`invoke`'s `Acc.rec`, L55 — NOT the boot heap, which now reduces), each
    adding one isolated `ofReduceBool` axiom; the bridges stay axiom-clean.
  This is the prove-AND-disprove milestone for concrete T5 by execution. The
  Direction-B *invariant* proof of the unbounded loop (which does not run the
  program; object-model core = `T5.dispatch_progress`) is the separate next step.

- **L55 — `Boot.initHeap` made kernel-reducible (unblocks axiom-clean Direction
  B).** The boot heap used `classTable.toArray.qsort` + an `Id.run do … for …`
  build loop; `Array.qsort` is opaque to the kernel, so `rfl`/`decide` got stuck
  on ANY concrete boot-heap fact (`lookup Boot.initHeap (.int 1) "succ"` did not
  reduce), forcing `native_decide` for the object-model facts a Direction-B
  invariant proof must discharge. Replaced with a **structural insertion sort**
  (`Heap.sortById`/`insertById`, reducible) + pure **`List.foldl`** construction
  (no `Id.run`/`for`). **Behavior-preserving** — ids are distinct so the sort
  order is identical; tier-0 `--sut lean` stayed **722 agree, 0 disagree**. Now
  `lookup`/`ancestors`/`classOf`/`crubyShadow` over `initHeap` reduce, so
  boot-heap resolution facts are **`decide`-able, axiom-clean** (verified:
  `(lookup Boot.initHeap (.int 1) "succ").isSome = true` closes by `decide` in
  ~0.2 s; example in `T5.lean`). This removes the boot-heap blocker for a full
  Direction-B `invariant_sound` proof from `Machine.init` (resolution hypotheses
  discharged by `decide`, no `native_decide`). What still needs `native_decide`
  is *running* a program: `invoke` is a well-founded `def` compiling to `Acc.rec`,
  which the kernel's whnf will not evaluate (verified: `run 50 (init (1+2))`
  still won't `decide`). So: **invariant reasoning = axiom-clean; execution =
  native_decide** — a clean and permanent split. (Making `invoke` structurally
  recursive on a fuel param would let runs reduce too, but is not needed for
  Direction B and would re-touch the SUT; deferred.)

- **L56 — first axiom-clean Direction-B proof: an unbounded dispatch loop is
  type-safe (`RubyCore/Proof/DispatchLoop.lean`).** `while true do 1.succ end` —
  diverges, dispatching `Integer#succ` every iteration — proved to never reach a
  type-family `uncaught`, for unbounded fuel, by `invariant_sound` over a
  seven-shape inductive invariant. Does NOT run the program (contrast the
  Direction-A `native_decide` certificates); it is the object-model invariant
  reasoning the design doc (§4) calls the substantive obligation, over the real
  interpreter, and it is **axiom-clean** (`propext`/`Classical.choice`/`Quot.sound`
  — no `native_decide`), which is exactly what L52 (`invoke` reasoning-amenable)
  + L55 (`initHeap` reducible) unlocked. The machine is constant except
  `(ctl, kont)` (succ allocates nothing / pushes no frame), so the six control
  transitions close by `rfl` and the one dispatch transition (`step_F`) by
  unfolding `invoke.eq_def` then `rfl` (the `Integer#succ` lookup reduces over the
  now-reducible `initHeap`). `set_option maxRecDepth 100000` (deep reduction over
  `initHeap`). Scaling to the user-class T5 loop reuses this assembly + adds
  method-frame shapes (frame store grows across calls → the invariant loosens to
  "`frames[0]` fixed, active frame characterized") and swaps `step_F` for a
  `T5.dispatch_progress`-style step; no new blockers.

- **L57 — the actual T5 (`class_hierarchy`) loop proved type-safe, Direction B,
  axiom-clean (`RubyCore/Proof/T5Loop.lean`).** `while true do x.m end`, entered
  with a **user class `A`** defined (method `m ↦ 0`) and `x` an `A`-instance,
  proved to never reach a type-family `uncaught`, for unbounded fuel, by
  `invariant_sound_from` over a nine-shape inductive invariant `J`. The
  user-class analogue of `DispatchLoop` (L56); the genuinely new ingredient is
  **frame-store growth** — each `x.m` pushes a method activation frame that
  `frameK` never reclaims (it pops the activation *stack*, not the frame
  *store*), so `frames` grows unboundedly. `J` therefore does NOT pin `frames`:
  it keeps `0 < frames.size ∧ frames.getD 0 = F0` (frame 0, holding `x`, is
  stable — `getD0_push` carries it across a push) plus an existential frame id in
  the two mid-method shapes. All object-model facts are over a concrete
  class-bearing heap `Hstar` (`initHeap` + class `A` + instance, built by
  reducible `alloc`s), so resolution closes by `rfl`/`decide` — **axiom-clean**
  (`propext`/`Classical.choice`/`Quot.sound`, no `native_decide`), thanks to L52
  (`invoke` reasoning-amenable) + L55 (`initHeap` reducible). Key sub-lemmas:
  `dispatch_step` (the `x.m` step: `rw [invoke.eq_def]; rfl`, resolving `A#m` in
  `Hstar` and pushing the activation), `getLocal_x` (reads `x` from frame 0 over
  abstract/grown `frames`), `getD0_push`. Consecution + safety both fall out of a
  single `stepJ` (progress+preservation). `invariant_sound` was generalized to
  `invariant_sound_from` (any start config) so the proof starts at the loop head,
  isolating the object-model reasoning from the boot phase (class/`new` setup —
  finite/Direction-A territory, orthogonal). Gotchas logged: multi-line record
  `{x with …}` updates trip the parser (single-line them); use `abbrev` not `def`
  for the syntactic shapes (`bodyE`/konts/`prog`) so they unfold uniformly under
  `simp`/`rfl`; `getD 0 = F0` needs `rfl` not `decide` (no `DecidableEq Frame`).

- **L58 — Phase-1 witness finder: random (Plausible) search for type errors
  (`RubyCore/Search/Random.lean`).** Realizes the first de-risking step of
  `type-safety-by-reachability.md` §8 — *find* counterexamples that refute
  `typeSafe?` by running the semantics on generated inputs. **It works:**
  `nilDispatch` (T2 `nil_dispatch`: `def f(x); x<5 ? 1 : nil; end; f(N).succ`)
  yields `failed [n := 7]` at seed 42 (witness set is all `n ≥ 5`); the control
  `alwaysSafe` (`N.succ`) reports `success` — no false positive.
  - **New dep:** `plausible` @ `v4.31.0` (matches `lean-toolchain`) in
    `lakefile.toml`. Dev-only and **cleanly separated**: neither `RubyCore.lean`
    (the lib root) nor `Main` imports `Search/`, so `lake build`/the `rubycore`
    exe never touch it; verified the tier-0 ratchet is unchanged (**722 agree, 0
    disagree**). Revertable: drop the `[[require]]` + the `Search/` dir.
  - **Search is UNTRUSTED; the verdict is certified.** A reported witness is
    replayed through the trusted `run`/`stepFn` (`native_decide`, since runs are
    not kernel-reducible — L55) and fed to the new axiom-clean bridge
    `Proof.runTypeStuck_unsafe` (`RunCert.lean`: `runTypeStuck (run …) = true →
    ∃ r, ReachableResult … ∧ typeStuck r`), giving real theorems
    `nilDispatch_unsafe` / `narrowNeedle_unsafe`. A bogus witness dies at replay,
    so the search needs no soundness argument ("the certificate is the trace",
    §3). Only the replay carries `ofReduceBool`; the bridge is axiom-clean.
  - **Honest limitation, demonstrated (motivates Phase 2):** `narrowNeedle`
    (type-stuck only at `n = 123456789`) is **NOT found**, even at a 20× budget
    (`numInst := 2000, maxSize := 10000`) — undirected sampling can't hit a
    needle behind a narrow guard. A concolic engine solves
    `pathCondition ∧ n = 123456789` and derives the input directly. Recorded so
    a `success` verdict is never misread as safety: it means "no witness within
    these bounds" (the `VERIFIED(k)`/UNKNOWN split of
    `bounded-effect-checking.md` §3); *proving* safety is Direction B (L56/L57).
  - `outcomeAt` keeps the **frontier** visible (`unsupported`/`outOfFuel` are "we
    could not say", not evidence of safety). Searches run at elaboration via
    `#eval` (informational — they never fail the build) and are seeded
    (`randomSeed := some 42`) for reproducibility. API gotcha: `Testable.checkIO`
    needs the goal wrapped as `NamedBinder "n" (∀ n : Int, …)` — the `plausible`
    *tactic* adds those decorations automatically, the programmatic API does not.
  - [V] CRuby agrees on the demo: `undefined method 'succ' for nil
    (NoMethodError)`.

- **L59 — fragment-coverage audit (2026-07-30) and the doc-staleness lesson.** The
  planning docs had drifted badly from the built model: `type-safety-by-reachability.md`
  §9.0/§10.2/§10.3 still called call-site kwargs the "#1 construct blocker" and listed
  the reflection predicates and `attr_*` as pending (all three shipped); `lean/README.md`
  §Fragment listed `Array#each`/`map`, `Integer#times`, `Hash.new{}`, `attr_reader`,
  `include`, kwargs and Float formatting as *gated* (all work); `lean/HANDOFF.md` still
  warned `--sut lean` was RED with a 372/468 baseline (green, 722). All corrected, and a
  dated "current snapshot" block now fronts `HANDOFF.md` and `ruby/AGENTS.md`.
  **Audit method, repeatable — prefer it over reading prose:**
  1. *Feature probe:* write a one-line snippet per feature, run
     `harness/desugar-dt/bin/export-json f.rb | lean/.lake/build/bin/rubycore`, and read
     exit 0 (works) vs exit 3 + the gate reason. Fast, unambiguous, and it catches exactly
     this kind of drift.
  2. *Prioritize by measurement, not by prose:* `cd difftest && uv run python -m difftest
     run --tier 0 --sut lean`, then histogram the gates:
     `python3 -c` over `reports/<latest>/cases.jsonl` counting `"reason"` values. The
     result reordered the build plan — the top three actionable gates (`defined?` 36,
     `zsuper` 29, `Array#[]` slice 28) are **not** the Enumerable methods the docs
     recommended doing first.
  Caveat to carry: counts are *first-gate-hit*, so unblocking one reason can reveal
  another behind it — treat them as an upper bound on immediate gain, not additive.
  **Standing instruction: re-run this audit before planning model work, and update the
  snapshot blocks in the same commit.**

- **L60 — S1 of the concolic **symbolic shadow machine** (`RubyCore/Concolic/Shadow.lean`,
  wired into `ConcolicMain.lean`).** Implements `docs/semantics/concolic-dataflow.md` D2/S1:
  the tracer now emits each branch condition as a **term over the symbolic inputs**, so the
  concolic engine no longer has to re-derive dataflow by walking the AST. Verified on
  `derived.rb` (`n = $__in0; x = n*3+7; if x == 100`): the emitted condition is
  `eq(add(mul(inp 0, lit 3), lit 7), lit 100)` — precisely the constraint z3 needs.
  - **No `stepFn` changes** (the whole point). The shadow observes `(m, m')` pairs: `stepFn`
    is deterministic and dispatches on `(ctl, kont-head)`, so the pre-state says which rule
    fires and `m'` shows the result. Tier-0 `--sut lean` unchanged: **722 agree, 0 disagree**.
  - **No taint flag** (KLEE's discipline): concrete ⟺ the term is `lit`. `mkUn`/`mkBin`
    constant-fold at construction, so fully-concrete arithmetic collapses to a literal for
    free and `hasInput` answers "is this flippable?" structurally. Rejected the earlier
    `Term(expr, tainted)` shape — a flag can desync from the term it describes.
  - **The `mirror` is the load-bearing trick.** It runs parallel to `m.kont` and stores only
    what the machine's kont does *not* already expose. Since the kont is fully visible,
    `asgnK`/`ifK`/… need no payload; only `argsK` does (it accumulates argument *values*
    whose *terms* must ride along). `realign` resizes the mirror from the observed kont
    depth, so **unmodeled konts are automatically safe** — they contribute `opaque`, i.e. no
    constraint, never a wrong one.
  - **Self-check (the property the design rests on).** Every term assigned to `ctl` is a
    claim that evaluating it at the concrete inputs equals the value the machine just
    produced; on mismatch we drop to `opaque` and record a frontier note. **Validated
    adversarially:** deliberately mis-mapping `*` to `add` produced
    `SELF-CHECK FAILED at *: term=3 machine=0 (term dropped)` and `cond: null` — precision
    lost, soundness preserved, no wrong constraint emitted. This is what converts "the
    shadow drifts as the model grows" from a silent-correctness risk into a visible
    precision report.
  - **Inputs are the reserved globals `$__in0`, `$__in1`, …** (design §6.5), preloaded by
    the tracer via `--inputs 31,7`, so **no AST rewriting** is needed. Chosen because Prism
    parses `$__in0` unambiguously as a gvar read (a bare identifier would be a *vcall*) and
    it exports as `["var","gvar","$__in0"]` — name-distinctive, so recognition needs no node
    identity. Rejected: substituting `__input__ → ["int", n]` (a literal `31` elsewhere is
    then indistinguishable from the input — unsound); a new `Expr` head (touches the SUT).
  - Scope: integer arithmetic/comparison (`+ - *`, `< <= > >= == !=`, `-@`/`succ`/`pred`),
    locals, globals, `if`/`while` conditions. `/`/`%`/`**` stay `opaque` (K7). Next: S2
    param binding at method entry (dataflow through calls), then S3 (engine consumes terms,
    delete the AST walk). Note S1/S2 are less separable in Ruby than in a C-like language
    because **arithmetic is dispatch** — `n * 3` is a send, so S1 already needed the mirror.

- **L61 — concolic coverage for the *nil-bug class*: input-independence tracking +
  directed nil-risk goals.** Driven by measurement: a census of ai4r's nil-returning
  guards found **`.empty?` first (5 of 14)**, then `==`, `.length`, `.nil?` — so the
  work was aimed at collection predicates, not strings (`==` against a string/symbol
  literal is the *smallest* category in ai4r, 16 vs 128 for collection+class
  predicates).
  - **`SymTerm.conc` — a third state, and the load-bearing idea.** `opaque` conflated
    *"unmodeled type"* with *"may depend on the input"*. Splitting out `conc`
    ("input-**independent** value of a type we don't model") lets the shadow do
    something previously impossible: read a **concrete fact off the machine and freeze
    it as a `lit`**, soundly, because that fact is identical on every run. Concretely,
    `[:s1,:s2,:s3].length → lit 3`, which makes the ubiquitous bounds guard
    `i < arr.length` solvable even though the array itself is unmodeled.
    Soundness discipline: `conc` is established only for literals and arrays whose
    elements are all const; arithmetic mixing `conc` yields `opaque`; and the frozen
    read is restricted to a **short whitelist** (`length`/`size`/`count`) of zero-arg
    deterministic Int-returning methods. That whitelist is load-bearing — the
    self-check **cannot** catch a wrongly-frozen literal, since it only validates the
    current run, so `rand`-like or address-dependent methods must never appear.
  - **Directed `DispatchRisk` goals — a mechanism branch-flipping cannot substitute
    for, stated in its general form.** The bad state is *"the receiver could be a class
    that does not define the sent method"* — a reachable `NoMethodError`;
    `nil.to_sym` is merely its commonest instance. This must be a **goal, not a flip**,
    because the bad class typically arises with **no branch at all** (out-of-range
    index, `Hash` miss, guarded `nil` return): `i = 0` and `i = 3` traverse *identical*
    branches, so no amount of path exploration reaches it.
    Mechanism: values carry a **nil-guard** — a boolean term true exactly when the
    value is `nil` — which propagates through locals; at **every send site** the shadow
    asks the *semantics* (`lookup heap Value.nil mname`) whether the alternative class
    defines the method, and if not emits `DispatchRisk {source, meth, badClass, guard}`.
    The engine then solves `pathCondition ∧ guard`.
    Two verified properties: (a) on an off-by-one guard (`i <= len` for `i < len`) it
    derives `i = 3` — `goal[NilClass#to_sym via nil_source] → [3]` — confirmed by the
    Lean observation path and CRuby; (b) **precision**: changing the sent method to
    `to_s`, which `NilClass` *does* define, raises **no risk at all** and yields no
    witness. That (b) holds *because* the check consults the model's own method table
    rather than a heuristic is what keeps it false-positive-free (cf. K9).
    Correctness detail worth preserving: the nil-guard is **cleared at every step**
    (`ctlNil := .opaque` in `s0`) and re-established only by rules that mean it — a
    stale guard would be attributed to an unrelated receiver and manufacture a false
    positive. `BinOp` gained `or` to express the guard as one term.
  - `symStep` now returns `(SymState × Option BranchEvent × Option NilRisk)`; the
    trace gains a `nilrisks` array. Ratchet unchanged (**722 agree, 0 disagree**);
    25 concolic tests pass.
  - **Hash miss as a second nil source** (2026-08-01). `h[k]` yields `nil` when `k`
    is none of the keys and the hash has **no default** — the same shape as an
    out-of-range index, and again with no branch. When the hash is input-independent
    and its keys are integers, the shadow emits the guard
    `k ≠ k₁ ∧ … ∧ k ≠ kₙ` (hence `BinOp.and`); everything else stays `opaque`.
    Required tracking hash *literals* as `conc`, mirroring `hshKeyK`/`hshValK` the way
    `arrK` was already mirrored. **Verified:** seeded with a *valid* key (so the goal
    must do the work) the engine derives a non-key and finds the error; **precision
    control:** give the hash a default and no risk is raised at all, because the
    shadow asks the heap (`hashDflt`) instead of assuming a miss means `nil`.
    Two deliberate bail-outs, both "no constraint rather than a wrong one": a
    non-integer key (`:sym` keys are not expressible as terms yet) and a hash whose
    contents are input-dependent.
    *Gotcha logged:* `(match … with | a => x | b => y, none, none)` parses
    ambiguously — bind the match to a `let` (or build the tuple outside) instead.
  - **Not yet:** `@q[state].empty?` — a Hash predicate over *mutated heap* state with
    *symbol* keys — remains `opaque` (both bail-outs above apply). That needs
    theory-of-arrays over the object store
    (`docs/semantics/concolic-dataflow.md` §8.2) plus symbol-valued terms, and is the
    remaining blocker for the ai4r q_learning natural trigger
    (`typecheck-pipeline/findings/`).

## The prelude — core library written in RubyCore (L62–…)

- **L62 — the prelude mechanism: two-phase boot + `fromPrelude` + a
  RubyCore-level gate.** The iterating-builtin machinery (`tryIterator`,
  `IterKind`) is hardcoded per `(class, method)` pair and its five-constructor
  `IterKind` cannot express `select`/`find`/`group_by`/… without a new Lean
  constructor each — which is why the coverage histogram's tail reads as "a list
  of named builtins". The prelude inverts that: core-library methods are written
  **in Ruby**, desugared by the harness, and loaded into the heap before the
  program under test, so each new method costs a few lines of RubyCore rather
  than a Lean primitive — and lands *inside* the model, where Direction-B proofs
  and the concolic engine reach it for free.
  Four decisions, each revertable:
  - **Carried as export JSON, not a Lean `Expr` literal.** `scripts/gen_prelude.rb`
    desugars `prelude/prelude.rb` and emits `RubyCore/Prelude.lean` holding the
    exported RubyCore **JSON** as a chunked string literal; the model decodes it
    with the ordinary `Decode.program`. Rejected: emitting Lean `Expr` syntax from
    Ruby (a second AST encoder that would silently drift from `Export::VERSION`),
    and reading a JSON file at runtime (the SUT binary must be self-contained —
    difftest invokes it from anywhere). Cost: one JSON parse per process (~ms) and
    the prelude is not kernel-reducible, which is fine because the proofs use bare
    `Machine.init`.
  - **Two-phase boot, not a `.seq [prelude, program]` wrapper.** `Prelude.boot`
    runs the prelude from H₀ with `preludeMode := true`; `initWithPrelude` then
    builds a *fresh* machine on the resulting heap (`Machine.initOn`, carrying
    `globals`/`reprPure` forward). This keeps the program's own frame/kont/step
    numbering unpolluted, gives the flag a natural extent (phase 1 only), and is
    literally the "concrete boot heap" of `bounded-effect-checking.md`.
    `Machine.init` is untouched, so `Proof/` and `Search/` are unaffected.
  - **`MethodDef.fromPrelude` suppresses the L6 shadow gate for its own name.**
    Necessary, and measured: a *direct* `class Array; def select` resolves with an
    empty `between` chain and needs nothing, but the same method supplied via
    `include Enumerable` resolves to an owner *above* `Array`, so the L6 check
    fires ("unmodeled builtin would shadow: Array#select") — the mixin route is
    the whole point of a prelude. The rule is uniform: a prelude method *is* the
    model of the CRuby builtin of that name, so it suppresses the gate for that
    name only; the fidelity obligation moves into `prelude.rb`, where difftest
    checks it like any other model code. A *user* method shadowed by a real
    builtin still gates, so L6 is intact where it earns its keep.
  - **`Kernel#__unsupported__(msg)` — the prelude's gate.** RubyCore code cannot
    return `.unsupported`, so a prelude method that meets a form it does not model
    (the standard case: a blockless Enumerable call, which CRuby answers with an
    `Enumerator`) calls this builtin, which returns `BRes.unsupported msg`. Without
    it, prelude authors would have to *guess*, and the 0-disagree ratchet would
    become a coin flip.
  Authoring rules live at the top of `prelude/prelude.rb`. The sharpest one:
  **never define `to_s`/`inspect`/`==`/`eql?`/`message`/`to_str` in the prelude** —
  `reprPure` (L7) is a global flag, so one such `def` would make every `puts` in
  every program gate. That is what keeps `Rational`/`Struct`-style classes out of
  the prelude until L7 is refined to a per-class check.
  First content is `Comparable` (`< <= > >= between? clamp` over `<=>`), which also
  retires the "unmodeled constant Comparable" gate. Ratchet: **722 agree, 0
  disagree** — unchanged, as intended for a mechanism-only step.

- **L63 — prelude content: `Enumerable` (36 methods), `Range` enumeration,
  `Comparable` consumers, `Hash`'s Enumerable overrides — plus two fidelity
  fixes the prelude exposed.** All of it is `each`-based Ruby: one `each` per
  collection buys the module, so `Range` went from an opaque value to a full
  collection by adding *one* method (`Range#each`, a `while` loop over `succ`)
  and `include Enumerable`. Early exit inside the iteration block uses `return`
  (unwinds to the Enumerable method's frame) and `break` (returns from `each`) —
  both already modeled, and both load-bearing for `find`/`take`/`any?`.
  Fidelity decisions worth recording:
  - **Blockless Enumerable calls gate, they do not guess.** CRuby answers them
    with an `Enumerator`; every such method starts with
    `unless block_given? … __unsupported__(…)`. Same for the pattern-argument
    forms (`all?(Integer)`), which is why the methods take `*pat` and gate on a
    non-empty one instead of raising a wrong `ArgumentError`.
  - **`Hash` needs its own `select`/`reject`/`transform_*`/predicates**: CRuby's
    return a **Hash** and yield the key and value as *two* arguments, while the
    generic Enumerable ones yield the `[k, v]` pair as one. Verified against the
    oracle (`{a: 1}.select { |x| p x }` prints `:a`, not `[:a, 1]`), and the
    reason `include Enumerable` into Hash is safe: Hash's own methods (and the
    builtins `include?`/`member?`, which are *key* tests) sit lower in the chain.
  - **`sort`/`sort_by` are insertion sorts over `<=>` dispatch** — works for user
    classes and mixed comparables, and is *stable*, whereas CRuby's sort is not.
    Programs that observe tie order are therefore outside what this models
    faithfully; noted here rather than papered over.
  - **`Range#include?`/`member?` are restricted to numeric ranges.** For
    non-numeric ranges CRuby *iterates* (`('a'..'z').include?('cc')` is false)
    while `cover?` compares (true), so the non-numeric case gates.
  - `Object#===` (the `==` default) with `Range#===`/`Proc#===` overrides makes
    `case`/`when` over ranges and lambdas work; `Object#tap` came along free.
  Two fixes the prelude surfaced, both real bugs rather than gaps:
  - **`blockSensitiveBids` — blocks were being silently dropped by builtins.**
    `[3,1,2].sort { |a,b| b <=> a }` returned `[1,2,3]`: the builtin `Array#sort`
    ran and ignored the block, a *silent disagreement* the corpus had not hit.
    Dispatch now checks a list of builtins whose CRuby meaning *changes* with a
    block (`sort`/`min`/`max`/`sum`/`index`/`uniq`/`fetch`/`delete`/`merge`/`new`)
    and, when one gets a block, continues the ancestor walk above the builtin's
    owner (`lookupAbove`) to a prelude definition of the same name — so
    `sort {}`/`min {}`/`sum {}`/`index {}` now route to `Enumerable` and are
    *right* rather than gated. No prelude definition ⇒ gate. Builtins CRuby also
    ignores a block for (`length`, `to_s`, …) are deliberately not listed:
    gating those would be over-strict, and CRuby agrees with us there.
  - **`Range#inspect`/`#to_s` registered on `Range`.** `Repr` already rendered
    `.range` payloads, but the methods were inherited from `Object`, so the L6
    between-check fired ("unmodeled builtin would shadow: Range#inspect") on
    seven tier-0 cases that only wanted `(1..2).inspect`. Registering them with
    the right owner is the whole fix.
  - **`for … in` over a Range** now expands via `spread` (integer ranges) instead
    of gating on "non-Array collection" — 13 tier-1 cases.
  Ratchet: tier-0 **722 → 761 agree, 0 disagree**; tier-1 (n=300, seed 11) 0
  disagree. Tier-1's remaining gates are almost entirely metaprogramming
  (`define_method` 96, `prepend` 27, `define_singleton_method` 21,
  `alias_method` 9) — the next step, and the one Rails needs.

## Reflective metaprogramming (L64–L66)

- **L64 — `define_method` & friends: a method whose body is a closure.** One new
  field carries it: `MethodDef.capturedFrame : Option Nat`, the frame the body
  closes over. `enterUserMethod` puts it in the activation frame's `captured`
  slot, so free variables resolve up the defining chain exactly as in the block
  the body came from, while the frame stays `kind := .method` — which is what
  makes `self` the call-time receiver and `return` return from the *method*. No
  new evaluation rule, no new Kont: the "everything is heap mutation" principle
  held (artifact 02 §1).
  - Params come from the closure, so `define_method(:m) { |a, b: 2| }` gets the
    full structured-param treatment for free, with **method** arity (strict) —
    `A.new.m` with no args raises `ArgumentError` [V], unlike calling the proc.
  - `blk` is the subtle one: a `define_method` body is a *block*, so
    `block_given?`/`yield` inside it refer to the block of the scope where it was
    **defined**, not the call (`C.new.foo {}` → `false` [V], test_method_204).
    The frame therefore takes the captured frame's `blk`, and a new
    `Frame.callBlk` records the call's block for the two things that still need
    it: an explicit `&b` param, and `break` targeting (below).
  - Bare `super` from such a body has no formal parameter list to forward, and
    CRuby refuses rather than guessing: `RuntimeError "implicit argument passing
    of super from method defined by define_method() is not supported…"` [V].
  - `define_singleton_method` is the same code with the eigenclass as target;
    `alias_method` is `alias` with dynamic names (copy semantics, so a later
    redefinition of the original does not follow [V]).
  - Constants in the body resolve at the **definition** site: the MethodDef takes
    the captured frame's `cref`.
  - **Frame pre-declaration** (needed once bodies can close over a scope):
    `enterUserMethod` now seeds the frame's locals with every formal bound *after*
    the defaults (`rest`/`post`/`block`/`kwrest`) as nil, because those go through
    `setLocal`, which walks the `captured` chain — without pre-declaration a
    `*rest` param would clobber a same-named local in the enclosing scope.
- **L65 — `class_eval`/`instance_eval`/`instance_exec`, `prepend`, and the
  reflection surface.** All of it is `self`/`defmod` rebinding plus heap reads:
  - `callClosure` gained `selfOv`/`defmodOv`. `class_eval` rebinds both to the
    module (so `def` inside defines instance methods); `instance_eval` rebinds
    `self` to the receiver and the `def` target to its **eigenclass**, which is
    why `o.instance_eval { def m; end }` defines a singleton method [V].
    Everything else about the block frame (captured chain, `home`, `cref`, `lam`)
    is untouched, so free variables, `return` and constant lookup keep block
    semantics. `_exec` passes the caller's args; `_eval` passes the receiver.
  - **`prepend`** needed a real MRO slot: `ClassPayload.prepends`, spliced
    *below* the class in `ancestors`, so prepended methods win and `super` from
    them reaches the overridden definition (`[:M, :B]` [V]). 27 tier-1 gates.
  - `singleton_class`, `instance_variable_get`/`_set`/`_defined?`,
    `instance_variables`, `const_get`/`const_set`/`const_defined?`,
    `remove_method`/`undef_method`. Two fidelity details: `const_defined?` gates
    for a constant CRuby has but we don't model (the L5 split — a wrong `false`
    is worse than a gate), and `remove_method` raises CRuby's
    `NameError "method 'm' not defined in C"` [V] but treats an `undef`
    tombstone as *not* a definition (test_method_201) and gates when CRuby
    defines the method there and we don't (`BasicObject#method_missing`,
    test_method_211).
  - **`Kernel` and `Numeric` are now real boot classes.** `Kernel` is a module
    `include`d into Object (its methods still live on Object; the module is
    empty), `Numeric` is Integer's and Float's superclass and where the prelude
    mixes in `Comparable`. Payoff: `ancestors` is now byte-exact —
    `[Array, Enumerable, Object, Kernel, BasicObject]`,
    `[Integer, Numeric, Comparable, Object, Kernel, BasicObject]` [V] — where
    before it silently omitted them; `1.is_a?(Numeric)` is true; and a reopened
    `Kernel` resolves through the ordinary MRO instead of the `stdMixins` hack.
    That hack is now *harmful* where the module is really in the chain — it
    re-added methods an `undef_method` had removed (test_yjit_266) — so
    `stdMixins` shrank to the one class whose CRuby mixin we still do not splice
    (`Symbol`, now also handled by the prelude).
- **L66 — fidelity fixes the metaprogramming work exposed.** Each was a silent
  disagreement waiting for a corpus that reached it:
  - **`puts` must consider `to_ary` dispatch.** `Kernel#puts` flattens its
    arguments by calling `to_ary`, so an object with a user `to_ary` — *or a user
    `method_missing`*, which can intercept it — makes CRuby raise
    (`can't convert C0 to Array (C0#to_ary gives String)`) where our pure `puts`
    happily printed. A builtin cannot run a dispatch, so it gates
    (`mayDispatchToAry`). This was 169 tier-1 disagreements the moment `for … in`
    over a Range stopped gating early — a good illustration that un-gating one
    construct *reveals* rather than creates infidelity.
  - **`dup`/`clone` copy instance variables** (`str.dup` keeps `@ivar` [V]) —
    one `dupObj` rule for every payload, routed by the `#dup`/`#clone` bid
    suffix, `dup` dropping the frozen bit and `clone` keeping it. Gates where a
    copy needs more than the object: a singleton class, or a class/module payload
    (a duped class is anonymous, which our `name` field cannot express).
    `Object#dup`/`#clone` also retire the plain-object `dup` gates.
  - **`break` from a proc invoked via `#call`** is valid while the method the
    block was passed to is still active — CRuby's rule, not "always
    LocalJumpError". `blockOwner` finds that method by scanning the stack for the
    frame whose `callBlk` *is* this proc, and it becomes the `brk` target; a
    detached proc still raises `LocalJumpError` [V] (test_method_205).
  - **Symbol inspect of sigil names**: `p [:@a]` printed `[:"@a"]`. `simpleSymbol`
    now strips a leading `@@`/`@`/`$` before the identifier test [V].
  Ratchet: tier-0 **761 → 792 agree, 0 disagree**; tier-1 (n=300, seed 11)
  **114 → 242 agree**, 0 disagree.

## `defined?` and class variables (L67)

- **L67 — `defined?` (the largest single tier-0 gate, 36 cases) and `@@x`.**
  - **`defined?` is answered from the operand's *shape*, not by evaluating it**
    (artifact 03 §6): a new `Expr.defined` head plus a `evalDefined` dispatch that
    reads the frame/heap. CRuby's exact spellings, all [V]: `"nil"`, `"true"`,
    `"false"`, `"self"`, `"expression"`, `"assignment"`, `"local-variable"`,
    `"instance-variable"`, `"global-variable"`, `"class variable"` (note: no
    hyphen), `"constant"`, `"method"`, `"yield"`, `"super"`. Two easy-to-get-wrong
    ones the oracle settled: `defined?(1+1)` is `"method"` (it *is* a send), and
    `defined?(nil)` is `"nil"`, not `"expression"`.
  - **The two operands CRuby does evaluate** are a send's receiver and a cpath's
    base (`defined?(C.new.m)` really runs `C.new`), and *any* exception during
    that evaluation makes the whole `defined?` nil [V] — even a `RuntimeError`
    from `initialize`, not just NameError. Modeled with three konts:
    `definedRecvK`/`definedCpathK` (compute the answer from the evaluated value)
    over a `definedGuardK` marker that `unwind` consumes on a raise, yielding nil.
    A guard marker is exactly how `begin/rescue` already works, so this cost no
    new machinery.
  - **Two fidelity traps, both found by the corpus rather than by reasoning.**
    (a) `defined?(recv.m)` goes through **`respond_to?`** in CRuby, so a *user*
    override of `respond_to?`/`respond_to_missing?` is observable — and in
    test_yjit_023 it has a side effect (it nils out a local). A pure check cannot
    dispatch, so `definedMethod?` gates whenever a user override is in the chain.
    (b) `defined?(super)` must do the `super` *lookup* without calling — nil when
    there is no super method (test_syntax_130), with the usual L5 split when CRuby
    has one we don't model.
  - **Known divergence, deliberate:** the local-variable check is a *runtime*
    frame lookup (`Machine.hasLocal`), while CRuby's is the parser's static scope —
    so `x = 1 if false; defined?(x)` is `"local-variable"` in CRuby and nil here.
    Fixing it properly needs the desugarer to export declared-local sets; the
    corpus has no such case, and the alternative (gating every absent local) would
    forfeit all 36 cases.
  - **Class variables** (`ClassPayload.cvars`) came along because `defined?(@@a)`
    needs them: read walks the ancestor chain from the *lexical* scope
    (`cvarScope` = cref head), and assignment writes to the **highest** ancestor
    that already has the variable, so `class B < A; @@a = 9` updates `A`'s [V].
    Toplevel access raises CRuby's `RuntimeError "class variable access from
    toplevel"` — except `defined?(@@a)`, which is plain nil [V]. A
    singleton-class scope gates (CRuby shares the attached class's variables and
    we do not track attachment).
  Ratchet: tier-0 **792 → 815 agree, 0 disagree**.

- **L68 — `Array#[]`/`String#[]` slice forms.** `(start, len)` for both, plus
  `Range` and substring (`s["ell"]`) for String, via one shared `sliceRange`
  normalizer so the three CRuby nil-vs-empty cases are written once: a start past
  the end is nil but a start *at* the end is empty, a negative length is nil, and
  a count is clamped to what remains [V]. 28 tier-0 + 10 tier-1 gates for a
  contained builtin. Ratchet: tier-0 **815 → 842 agree, 0 disagree**.

## Non-local control: tagged unwinding (L69)

- **L69 — `catch`/`throw`, class-body-transparent `break`/`next`, and `redo` in a
  block.** Three gaps, one mechanism family (artifact 04 §3): the unwinder already
  had markers, so each was a new marker or a new marker *behaviour*, not new
  machinery.
  - **`catch`/`throw`** = one `Jump.throwJ (tag) (v)` + one `Kont.catchK (tag)`
    marker that consumes a throw whose tag is `equal?` and yields its value.
    `catch` lives in the miss path (like the iterators) because it must push a
    block frame, which a pure builtin cannot; a tagless `catch` allocates a fresh
    Object as the tag, as CRuby does, and passes it to the block.
    The one subtlety: with **no matching `catch`**, CRuby raises
    `UncaughtThrowError` *at the throw site*, so an enclosing `rescue` catches it
    [V] — unwinding first and raising at the top of the stack would have thrown
    that rescue away. So `throw` scans the kont stack for a matching `catchK`
    before jumping. (New boot class `UncaughtThrowError < ArgumentError`.)
  - **A class/module body is transparent to `break`/`next`/`redo`/`retry`**:
    `3.times { class C; break; end }` breaks out of the `times` block, and `next`
    continues the iteration [V] (test_flow_027/029 — 9 tier-0 cases). Both class
    bodies and method activations are `frameK`, so the arm now consults the
    frame's `kind`: `.classBody` pops and propagates, a method activation still
    gates (`break` in a method body is not valid Ruby).
  - **`redo` in a block** re-runs *that* invocation from the top with the same
    arguments, so `blkFrameK` now carries the `Closure` and the argument list and
    the `redoJ` arm simply pops the frame and re-enters `callClosure`. 18 tier-1 +
    4 tier-0 gates for two extra fields.
  Ratchet: tier-0 **842 → 865 agree, 0 disagree**.

## Payload-core subclassing and full `zsuper` (L70)

- **L70 — `class MyString < String` and the rest of the payload-core
  subclasses.** The representation was already right (a `Payload` and a `klass`
  are independent fields, and the builtins match on the *payload*), so what was
  missing was **allocation**: `Class#new` special-cased `k == Boot.stringId`
  rather than "has String in its ancestors", and a subclass therefore gated.
  Now:
  - `newImpl` dispatches on the **allocatable core ancestor**
    (`allocatableCore`: String/Array/Hash/Exception) and allocates with
    `klass := k`, so `MyString.new("abc")` is a `MyString` carrying a String
    payload — `length`/`upcase`/`+` and `inspect` all work through the ordinary
    builtins. `String.new("x")` (previously gated) came along for free.
    Proc/Range/Random/Integer subclasses still gate: their allocators need
    arguments no `new` can synthesize.
  - **Core `initialize` builtins** (`String#`/`Array#`/`Hash#`/`Exception#`, plus
    a no-op `Object#initialize`) *mutate* the already-allocated receiver, which is
    what makes the idiomatic subclass work:
    `class MyString2 < String; def initialize(s); super(s + "!"); end; end`. The
    allocate-then-initialize path in `invokeMaybeNew` gives such an instance the
    core class's **empty** payload up front, so `super` fills it in place.
  - **`raise C` / `raise C, msg` now runs a user `initialize`.** CRuby builds the
    exception via `C.new(…)`, so a subclass whose `initialize` supplies a default
    message must actually run — `raiseImpl` (a pure builtin) could not push that
    frame, so `invoke` intercepts and finishes through a new `raiseNewK` kont.
  - **`zsuper` param reconstruction generalized** (29 tier-0 gates): it used
    `classifySimple` (req/rest/block only), so a bare `super` in a method with an
    *optional* or *keyword* parameter gated — including the very common
    `def initialize(msg = "default"); super; end`. It now uses `classifyFull` and
    forwards positionals, filled optionals, the spread rest, post-params, keyword
    params re-bundled as keywords and a `**kwrest`'s entries; `doSuper` carries the
    keywords through. Destructuring params still gate (their synthetic slots are
    dropped after binding, so there is nothing to read back) as does a
    `define_method` body (CRuby raises there — L66).
  - **`!=` moved into the prelude** as `BasicObject#!= := !(self == other)`, and
    removed from every builtin table. In Ruby `!=` *is* the negation of `==`, so it
    must **dispatch**: a payload-comparing builtin gets `ma != "a_"` wrong the
    moment a subclass overrides `==` (test_yjit_115, the one disagreement this
    batch introduced). This is the prelude paying off as a *correctness*
    mechanism rather than a coverage one — the faithful definition is Ruby code.
  Ratchet: tier-0 **865 → 898 agree, 0 disagree**; tier-1 270/300, 0 disagree.

## Visibility (L71)

- **L71 — `private`/`protected`/`public`, enforced at dispatch.** `MethodDef`
  gained a three-valued `visibility` (replacing the unused `private'` flag) and
  `Frame` a `defVis`, which is what a **bare** `private` in a class body sets for
  the rest of that body. `def` reads it (and `initialize` is always private [V]),
  as does `attr_*`.
  - **The call site had to become first-class.** CRuby's private check is
    *syntactic*: `self.priv` is allowed (Ruby 2.7+) but `x.priv` is not — *even
    when `x` happens to be `self`* [V]. So the `implicit : Bool` threaded through
    the send konts became `SendSite := implicit | selfRecv | explicit | reflective`:
    only `explicit` is checked, `selfRecv` is decided syntactically at the send,
    and `reflective` is `send`/`__send__` (which bypass visibility, while
    `public_send` does not [V]). The Bool's other job — the vcall/fcall `NameError`
    split — now keys on `.implicit` alone, which is *more* precise than before:
    `self.nonexistent` no longer looks like a bare-name miss.
  - Protected passes when the **caller's** `self` is a kind of the method's owner,
    which is why the check lives at dispatch (where both are known) rather than in
    the method table.
  - Reflection follows: `respond_to?` answers false for private *and* protected
    unless `include_private` [V]; `method_defined?` covers public and protected,
    with `public_`/`private_`/`protected_method_defined?` asking for exactly one;
    and `defined?(obj.private_m)` is nil (it shares `visError?`).
  - `module_function :m` copies the method to the eigenclass **with the eigenclass
    as its owner** — without that, `super` inside the copy has no chain to continue
    (test_method_210: it must find `Object#foo`). A bare `module_function` (a
    body-wide mode) gates.
  - `private_class_method`/`public_class_method` are the same code with the
    eigenclass as target. `private_constant` is still gated (constant visibility
    would have to be checked in constant lookup).
  Ratchet: tier-0 **898 → 909 agree, 0 disagree**; tier-1 270/300, 0 disagree.

## Filling out the frontier (L72)

- **L72 — toplevel visibility, `Array.try_convert`, `instance_eval` on
  immediates, `Class.new`, `String#+@`/`-@`, and one exactness win on
  `defined?`.**
  - **A toplevel `def` is a *private* method of Object** [V] — which is why
    `public def m …` exists at all (8 tier-0 cases used it). `private`/`public`/
    `module_function` at toplevel receive `main`, not a class, so they now target
    Object. Consequence, and it is the faithful one: `0.some_toplevel_method`
    raises `NoMethodError: private method …` exactly as CRuby does.
  - **Visibility is checked *after* the shadow gate.** Ordering matters: a toplevel
    `def getbyte` lands on Object and is now private, but CRuby dispatches
    `"a".getbyte(0)` to the real `String#getbyte` — so the honest answer is
    Unsupported, not a NoMethodError about our own resolution (test_yjit_120).
  - **`Array.try_convert`** (16 cases; the desugar's single-RHS massign uses it):
    an Array is itself, otherwise CRuby *calls* `to_ary` — so `method_missing` can
    intercept — and demands an Array or nil back, else
    `TypeError "can't convert C to Array (C#to_ary gives String)"`. The dispatch
    result is validated by a new `tryConvertK` kont. This also makes
    `a, b = obj_with_to_ary` work.
  - **`instance_eval`/`instance_exec` on an immediate** is fine as long as the
    block does not `def` — only a *definition* needs the eigenclass an immediate
    cannot have (CRuby's `TypeError: can't define singleton`). A syntactic
    `definesMethod` scan of the block decides, so `1.instance_eval { self }` runs
    and the definition case still gates.
  - **`Class.new` / `Module.new`, anonymous classes, and constant naming.**
    `Class.new(sup)` allocates a class with an **empty** name; `Module#name`
    answers nil for it and `inspect`/`to_s` render `#<Class:0x…>` [V]. The block
    form is `class_eval`: allocate, then run the block with `self` and the `def`
    target rebound to the new class, discarding its value via `newK` (the block's
    last `def` returns a Symbol, which would otherwise *be* the result). And
    **constant assignment names an anonymous class** — `S = Class.new` makes
    `S.name == "S"`, `class Wrap; X = Class.new; end` makes it `"Wrap::X"` [V] —
    applied by both constant-assignment paths (`nameIfAnonymous`).
  - `String#+@`/`-@`: an unfrozen / frozen copy. Note a **verified-against-4.0.5
    deviation from the 3.x docs**: `(+str).equal?(str)` is *false* even for an
    already-unfrozen receiver, so `+@` always copies. (`-@` does not model
    fstring interning: `(-"x").equal?(-"x")` is true in CRuby, false here.)
  - **`defined?(local)` is now exact, not approximate.** L67 recorded a deliberate
    divergence for `y = 1 if false; defined?(y)`; a tier-3 case caught it as a real
    disagreement, and the fix was already in the data: the **desugarer only emits a
    `var local` node for a name the parser knows is a local** (an unknown bare name
    becomes a vcall `send`), which is *precisely* CRuby's static rule. So the
    answer is unconditionally `"local-variable"` — no runtime frame lookup, no
    divergence. A good example of the front end carrying information the model
    would otherwise have to guess at.
  Ratchet: tier-0 **909 → 940 agree, 0 disagree**; tier-1 (n=400, seed 7) 371
  agree, 0 disagree; tier-3 replay 54 agree, 0 disagree; regressions clean.

## Keeping the metatheory reducible (L73)

- **L73 — two kernel-reducibility traps, and the lesson.** The batches above broke
  every `Proof/` file, and *not* because the theorems became false: they became
  **unprovable by computation**. Both causes are worth remembering, because both
  are invisible to the difftest ratchet and only the proofs notice.
  - **`partial def` is opaque to the kernel.** `modAncestors` (the mixin expansion
    inside `ancestors`) was `partial`. That was harmless while no class in a chain
    had mixins — `[].flatMap _` reduces without touching it — but the moment
    `Object` included `Kernel` (L65), *every* ancestor walk went through it and no
    `rfl`/`decide` over a dispatch could reduce. It is now fuel-bounded on
    `h.objs.size`, exactly like `ancestors`'s own `go`.
  - **`String.endsWith` does not reduce either** (`example : ("a#b".endsWith "#b") = false := rfl`
    fails). The L66 dup/clone routing put it at the top of `Builtins.run`, so every
    builtin step became irreducible. Replaced with `dupBids`/`cloneBids` list
    membership, which is `String.beq` on literals and reduces fine. Rule of thumb
    for this codebase: **in the step function, dispatch on equality against literal
    lists, never on `String` prefix/suffix predicates.**
  - The mechanical updates: the `SendSite` argument in `recvK` literals, the
    boot-heap id shift (`Kernel`/`Numeric`/`UncaughtThrowError` pushed
    `T5Loop.clsA` from 34 to 37), `simp [Machine.init]` needing `Machine.initOn`
    now that `init` delegates, and two hypotheses added to
    `T5.dispatch_progress`: `md.visibility = .pub` and `md.fromPrelude = false`.
    Those two are an *improvement* to the statement — the theorem always depended
    on the method being publicly callable and on the prelude-shadow suppression not
    applying; now it says so.
  - Also worth noting for future debugging: Lean's `rfl` failure message prints the
    **un-reduced** goal, so it tells you nothing about where whnf actually stopped.
    The fast way to localise it is `#eval` of the same step (which uses the
    compiler, not the kernel): if `#eval` gives the expected answer, the problem is
    reducibility, not semantics — which is exactly how both traps above were found.
  Verified after the repair: all ten `Proof/` files build; `t5_loop_type_safe`,
  `invariant_sound`, `invariant_sound_from` depend only on
  `[propext, Classical.choice, Quot.sound]`; `../concolic` 28/28; tier-0 unchanged
  at **940 agree, 0 disagree**.

## `Hash#[]=` arity raises instead of gating (L74)

- **L74 — a wrong-arity `Hash#[]=` is an `ArgumentError`, not `.unsupported`.**
  `Builtins.lean`'s `Hash#[]=` matched `[k, v]` and sent every other shape to
  `.unsupported "[]=/arity"`. CRuby's `[]=` is a C function of arity 2, so a
  wrong arity is `ArgumentError: wrong number of arguments (given N, expected 2)`
  — checked *before* the receiver's payload, which is why the new arm sits
  outside the `.hsh` match and does not inspect the payload at all. Verified
  against CRuby 4.0.5 at arities 0/1/3/4: the message is uniform.
  - **Why this is more than fidelity.** `ArgumentError` is in `typeErrorFamily`
    (`Proof/TypeSafety.lean`), so gating here made a *reachable type-stuck
    outcome* invisible to the checker: the run reported "cannot say" where the
    correct answer is "this program is not type-safe, and here is the witness."
    Gates that shadow a bad-state class are worse than gates that shadow a value
    — they are silent where the whole point is to be loud.
  - **Found by**, and the motivating case: the DRuby hashslice reproduction
    (`../docs/druby-reproduction-plan.md`, `../typecheck-pipeline/findings/`).
    The call site `probe(0, h['a','b'] = 3, 4)` parses as three arguments to
    `Hash#[]=` — the exact shape — and hashslice's own variadic override is what
    *masks* it upstream. Dispatch decides whether this raises, so it is also a
    clean small instance of the object-model dependence the invariant must track.
  - Tier-0 is **unchanged at 940 agree, 0 disagree** (1304 total): no corpus
    program exercised the gate, so this is new reach rather than a repair.
    Whether other `.unsupported` arms similarly shadow type-family errors is
    worth a sweep — grep `unsupported` for arity/coercion sites — but is not
    done here.

## The tracer was running without the prelude (L77)

- **L77 — `rubycore-concolic` booted a bare heap, so the engine saw a *smaller*
  language than the SUT.** `ConcolicMain` built its initial machine with
  `Concolic.initMachine` (= `Machine.init`, i.e. `initOn Boot.initHeap`) while the
  SUT uses `Prelude.initWithPrelude`. Everything the prelude provides — Enumerable,
  Comparable, Range enumeration, the Hash overrides — was therefore **invisible to
  the concolic engine**, silently, since a gate just reads as `unsupported` on that
  run. Surfaced by running the engine on the full `objectgraph.rb`: the tracer
  gated on `Array#any?` where plain `rubycore` was perfectly happy.
  - Fixed with `Concolic.initMachineOn (base : Machine)`, which applies the input
    globals to an already-booted machine; the CLI calls `Prelude.initWithPrelude`
    first and reports a boot failure as a `stuck` outcome. `initMachine` is kept
    for tests that predate the prelude, with a docstring saying what it loses.
  - **Worth generalising:** any second entry point into the model needs the same
    two-phase boot. `initMachine` was written before the prelude existed and simply
    never got revisited — the failure mode is a coverage gap that looks like a
    frontier note, so nothing was going to catch it except running real code.
  - Knock-on: `test_closure_captured_local_is_visible_to_the_shadow` asserted "no
    input-dependent frontier note", which is now the *wrong signal* — with the
    prelude, `map`/`each` are Ruby code whose internals (`push`) legitimately note.
    Rewritten to assert the property directly: the branch condition inside the
    block is `eq (inp 0) (lit 7)`.

## `Array#&`/`Array#|` and `Class#allocate` (L77b)

- **L77b — three builtins the real `objectgraph.rb` needs**, each
  differential-tested byte-for-byte against CRuby 4.0.5.
  - **`Array#&` / `Array#|`** — set intersection/union. Both **deduplicate** and
    keep the receiver's order [V]: `[1,2,2,3] & [2,3,4]` is `[2,3]`,
    `[1,2,2,3] | [3,4,4]` is `[1,2,3,4]`. Element identity is `valueEql`, matching
    the existing `Array#-`. Registered on `arrayId` in `Heap.lean` — the arm in
    `Builtins.lean` is inert until the name is in the boot list, which is easy to
    forget and presents as "unmodeled method".
  - **`Class#allocate`** — the first half of `new`: an instance with the class's
    *empty* payload and no `initialize` call. Immediates have no heap
    representation, so CRuby raises `TypeError: allocator undefined for X` for
    Integer/Float/Symbol/NilClass/TrueClass/FalseClass [V]. **That error is
    load-bearing, not a detail**: ObjectGraph's `objectspace_loop` rescues exactly
    it (`detail.message =~ /allocator undefined/`) to skip un-allocatable classes,
    so the loop only runs at all if the message is right. Reuses the existing
    `allocatableCore`/`emptyCorePayload` helpers.
  - Tier-0 unchanged at **942 agree, 0 disagree** — none of the three is exercised
    by the bootstraptest corpus, so this is new reach rather than a repair.
    (`control_invalid` reads 5 rather than the 7 recorded earlier; that is the
    CRuby oracle side, which model changes cannot influence, and it is stable
    across repeated runs.)

## Concolic reach: strings, closure locals, observed domains (L76)

- **L76 — three shadow changes that together find two DRuby corpus defects
  automatically.** Motivated by a measurement (`druby-reproduction-plan.md`): the
  engine explored *one* input vector on an ObjectGraph-shaped program and stopped,
  because **every reachable corpus defect branches on a string**, and the shadow
  was integer-only.
  - **A string sort.** `SymVal = i Int | s String`; `SymTerm.slit`; `evalTerm`
    returns a `SymVal`. Only the well-behaved fragment is modeled — *equality
    against literals*. No concat/length/regex: those are what make SMT string
    reasoning brittle, and no corpus guard needs them. Mixed-sort equality folds to
    false, which is just Ruby (`1 == "a"`). Inputs are a heterogeneous vector;
    `--inputs` grew a JSON form (`'[31, "Numeric"]'`) and the element's JSON sort
    *is* its declared sort. String inputs are heap-allocated in `initMachine`.
  - **Closure locals.** `SymState.getLocal` looked up `(fid, name)` exactly, while
    `Machine.getLocal` walks the block-frame `captured` chain. So **every local read
    inside a block went `opaque`** — silently, since the frontier note fires only on
    input-dependent terms. `getLocalChain`/`getLocalNilChain`/`ownerFrame` now mirror
    the machine. This was the single biggest precision loss and it was invisible.
  - **`DomainFact` — observed comparison domains** (`search-and-proof.md`
    §2.3/§2.4). When an input is compared against something the shadow cannot
    express (`k.name == base_class_name`, where `k.name` is opaque), the *constraint*
    is lost but the **concrete value seen on this run** is not. Recording it gives a
    finite candidate domain; the engine tries each observed value plus one outside
    the set. Extended to `include?`/`index`/`key?`/… where the comparison happens
    *inside* the builtin and no `==` is ever observable — capped at 16 elements, and
    the cap is reported rather than applied silently.
  - **Why domain facts may be liberal where terms may not.** A `DomainFact` is a
    *candidate input*, never a path-condition constraint: every candidate is executed
    and its outcome comes from the semantics, so a wrong guess costs one iteration.
    That is why the receiver need not be proven input-independent here, while
    freezing a *term* would require exactly that. It is an under-approximation
    (§2.2) — missed witnesses, never false ones — and must never feed a safety claim.
  - Measured: **ObjectGraph** and **ai4r** defects both found with no human step,
    each seeded on the *safe* input so nothing hints at the answer. `../concolic`
    28 → 33 tests. Tier-0 unchanged at **942 agree, 0 disagree** (the shadow is not
    on the SUT path, but the whole build is green).

## vcall vs fcall: the `NameError` gate is gone (L75)

- **L75 — a bare identifier is its own head, so a missed vcall raises
  `NameError` instead of gating.** CRuby distinguishes three misses [V]:

  | source | error |
  |---|---|
  | `foo` (vcall) | `NameError: undefined local variable or method 'foo' for …` |
  | `foo()` (fcall) | `NoMethodError: undefined method 'foo' for …` |
  | `self.foo`, `foo(1)` | `NoMethodError: undefined method 'foo' for …` |

  RubyCore exported **both** `foo` and `foo()` as `["send",null,"foo",[],null]`,
  so `missNoMethod` could not attribute the miss and answered
  `.unsupported "vcall/fcall NameError ambiguity"`. That gate is now removed.
  - **The fix is additive, deliberately.** A new head `["vcall", name]` plus a new
    `Expr.vcall` and a new `SendSite.vcall` — *not* a sixth field on `send`. So
    every existing `send` node and the whole v4 corpus decode unchanged, and there
    is no format bump. Prism already carries the bit (`CallNode#variable_call?`);
    the desugarer simply stopped discarding it.
  - **A vcall is evaluated as exactly an implicit-self zero-arg send** —
    `startArgs … .vcall mname [] [] .none` — so dispatch, visibility exemption and
    `method_missing` are all inherited. `SendSite.vcall` differs from `.implicit`
    *only* at the miss. `defined?` treats the two arms identically; the
    local-variable case never reaches there (the desugarer emits `var`).
  - **Round-trip:** `render.rb` emits a vcall as the **bare** identifier. Adding
    `()` would silently convert it to an fcall and change the error — the one place
    where the renderer's habit of parenthesizing implicit sends would have been
    wrong. Safe against re-parse capture because desugar temps are `__dt_t<N>`.
  - **Why it was worth doing now:** `NameError` is the bad-state class for two of
    DRuby's five documented errors (ai4r, vimrecover — see
    `../docs/druby-reproduction-plan.md` §4.1). The gate meant the checker answered
    "cannot say" on both. ai4r's `return rule_not_found if !@values.include?(value)`
    (`id3.rb:283` at the 2009 tree) now reproduces byte-exactly in-model.
  - Measured: desugar tier-0 **unchanged at 1227** (round-trip oracle included);
    Lean tier-0 **940 → 942 agree, 356 → 354 unsupported, 0 disagreements**;
    `Proof/` builds and `invariant_sound`/`t5_loop_type_safe`/`run_value_type_safe`/
    `run_typeError_unsafe` remain `[propext, Classical.choice, Quot.sound]`;
    `../concolic` 28/28.
  - Note `NameError` is **not** in `typeErrorFamily` (NoMethodError ⊂ NameError, but
    a bare `NameError` is not a type error by our definition — `TypeSafety.lean` §1
    says so explicitly). Reporting ai4r/vimrecover therefore still needs the
    *pluggable bad-state family* of plan §4.1; L75 supplies the raise, not the
    verdict.

## L79 — `Module#method_added` fires on `def` (the hook sorbet-runtime's `sig` is built on)

`def` now dispatches `method_added(:name)` on the defining module after installing the
method, yielding the method name as before (new `methodAddedK` kont — same shape as
`newK`: run a call, discard its value, yield a fixed one). This is artifact 02 §6 in
action: a definition hook is *ordinary dispatch on the defining module*, not a new
evaluation rule.

Motivation is the Sorbet work — `sig` records a pending declaration and `method_added`
wraps the method that follows, so without the hook a `sig` cannot enforce anything — but
the gap was independent: CRuby fires the hook and the model silently did not, which is a
plain fidelity bug any `method_added` program would have caught.

**Two fidelity details, both found by checking against CRuby rather than assumed:**

1. **`Module#method_added` is a private no-op in CRuby, and it shadows.** A toplevel
   `def method_added(n)` defines an Object *instance* method, and Object comes *after*
   Module in a class object's ancestry — so CRuby's no-op wins and the hook never fires.
   Verified: CRuby prints nothing for that program. The model has no such no-op, so its
   `lookup` walked past where CRuby's sits; the rule therefore treats a resolution to
   Object/Kernel/BasicObject as "no hook".
2. **Skipped during prelude boot** (`preludeMode`). The prelude is model code loaded
   before any program, so no hook it installs can be legitimately observed at boot; the
   skip also keeps boot cost exactly unchanged.

**Known remaining gap:** CRuby fires `method_added` for `define_method` too, and the model
fires it only for `def`. The shim's re-entrancy guard is written as if it did (it must be,
or a future fix silently loops), and the one corpus program that redefines a sig'd method
with `define_method` (`escape-hatches/002`) agrees either way, since CRuby's hook finds no
pending sig there. Also not modeled: `singleton_method_added`, `method_removed`,
`method_undefined`.

Cost: one method lookup per `def` when no hook exists. Ratchet: tier-0 unchanged, all ten
`Proof/` files still build.

## L80 — the `T` prelude shim: Sorbet's runtime half as ordinary heap mutation

`prelude/prelude.rb` now carries a sorbet-runtime shim — `T.let`/`cast`/`must`/`unsafe`/
`assert_type!`/`bind`/`absurd`, the type constructors (`T.nilable`/`any`/`all`/`untyped`/
`class_of`/`type_parameter`/`proc`, `T::Boolean`, `T::Array[…]`/`T::Hash[…]`), the `sig`
DSL, and **runtime sig enforcement**.

Why in the model at all: the honest soundness statement for Sorbet is the *runtime*
three-outcome one (`types-and-preservation.md` §C.1 option 2), because the static half is
unsound by design. That statement only means something if the enforcement mechanism is
inside the semantics — otherwise the theorem has nothing to quantify over. With the shim
here, "sorbet-runtime raised a TypeError at a sig boundary" is an ordinary reachable
outcome of `stepFn`, so `typeStuck` / `invariant_sound` apply to it unchanged. And it is
§C.2 made literal: **a `sig` is heap mutation replacing a method-table entry with a
checking wrapper** — `alias_method` the original aside, `define_method` a validating
forwarder.

Decisions worth recording:

- **Messages match the gem byte for byte** (`Parameter 'x': Expected type Integer, got
  type String with value "two"`, `T.let: …`, `Passed \`nil\` into T.must`), because the
  difftest observation compares them. The one thing RubyCore cannot produce is the
  `Caller:`/`Definition:` suffix — the AST has no line numbers — so the engine normalizes
  those lines away on both sides (difftest N35).
- **Generics are checked as their bare class.** `T::Array[Integer]` validates only
  `is_a?(Array)`. Not a shortcut: it is exactly the runtime erasure of §A.6, and
  reproducing it is the point — `corpus/sorbet/generics/000.rb` depends on a heterogeneous
  array walking straight through.
- **`.checked(:never)` installs no wrapper** and `T.unsafe` checks nothing, faithfully.
  The shim reproduces the escape hatches rather than quietly closing them; a model that
  was *sounder* than Sorbet would be the wrong model.
- **`.void` returns the `VOID` sentinel**, because it is observable (`p` prints
  `T::Private::Types::Void::VOID`).
- **Toplevel `sig` installs its own hook.** In a class body `self` is the definee and
  `T::Sig#method_added` is already in the class object's singleton chain; at toplevel
  `self` is `main` and the `def` lands on Object, so `sig` installs a *singleton*
  `method_added` on Object (ahead of CRuby's `Module#method_added` no-op — L77 detail 1).
  The real gem installs hooks on the definee for the same reason.
- **No repr-sensitive method is defined** (authoring rule 3): the type objects carry
  `label`, not `to_s`, so `reprPure` stays on.
- **Positional param matching.** Sorbet requires a sig to list parameters in order, so the
  i-th declared name governs the i-th argument. A sig over a method with *keyword*
  parameters cannot be matched this way (no `instance_method(…).parameters` in the model),
  so it gates rather than guessing.
- **`T::Struct`/`T::Enum` gate at first use.** They are structural, not annotations — they
  define a hierarchy and generate methods — so ignoring them would change the program.
  Gating gives an honest Unsupported instead of a `NameError` that would read as a wrong
  answer.

Result: `difftest run --tier 4 --sut lean` goes from **1 agree / 17 disagree** to
**14 agree / 0 disagree / 4 unsupported** (T::Struct ×2, T::Enum, and `Enumerable#sum` on
mixed types — an unrelated pre-existing gap).

## L81 — Sorbet safety stated and proved (both directions), over the weakened bad state

`RubyCore/Proof/SorbetSafety.lean` makes the three-outcome runtime statement of
`types-and-preservation.md` §C.1 a formal object, and proves the reachability machinery
for it by **reusing `TypeSafety.lean` unchanged with the bad-state predicate weakened** —
the running "one engine, one metatheorem, a swappable bad state" thesis applied once more:

```
sorbetStuck r  :=  typeStuck r  ∧  ¬ isBlame …      -- blame is enforcement working
SorbetSafeFrom m₀ := ∀ r, ReachableResult m₀ r → ¬ sorbetStuck r
```

Proved, axiom-clean (`propext`/`Classical.choice`/`Quot.sound` only):
`sorbet_invariant_sound` (Direction B — an inductive invariant certifies Sorbet-safety),
`sorbetStuck_typeStuck` + `typeSafe_sorbetSafe` (the weakening only ever removes outcomes,
so existing type-safety certificates transfer), and the Direction-A execution
certificates including the new middle case, `run_blame_sorbet_safe`.

Three decisions worth recording:

- **The property is stated over the prelude-booted machine, not `Machine.init`.** Sig
  enforcement lives in the `T` shim, which is part of the prelude (L80), so a statement
  over `Machine.init` would be about a program running with no core library and no `T` at
  all — under which every Sorbet program raises `NameError` and the theorem says nothing
  about Sorbet. The first draft got this wrong; `SorbetSafe` now quantifies over
  `Prelude.initWithPrelude program = .ok m₀`.
- **Blame is detected by message prefix, not by class.** sorbet-runtime raises a plain
  `::TypeError` for enforcement failures, so blame is indistinguishable *by class* from a
  genuine Ruby `TypeError`. That is Sorbet's design choice, not a modeling shortcut, and
  it forces the same message-shape test the difftest classifier needs (difftest N28).
- **What is deliberately NOT claimed:** "srb accepts P ⇒ P is Sorbet-safe". That needs
  Sorbet's *static* judgment (`Δ; Γ ⊢ e : τ`, the T1–T3 staging of `type-judgments.md`),
  which does not exist yet. This file supplies the property such a theorem would conclude;
  `Types/Fragment.lean` supplies, executably, the scope it could have.

`RubyCore/Proof/SorbetConcrete.lean` applies it to real corpus programs through the booted
model (`native_decide`, as `T5Concrete` does — the metatheorems stay clean):
`sig-basic/000` certified Sorbet-safe by running to a value; **`sig-basic/001` certified
Sorbet-safe by *blaming*** — an uncaught `TypeError` that `TypeSafety.lean` counts as
type-stuck and that Sorbet-safety counts as a pass, which is the entire content of the
weakening; and `untyped-boundary/000` refuting Sorbet-safety with an uncaught
`NoMethodError` that is not blame — a program the fragment already excludes, so it refutes
nothing the fragment claims.

## L82 — the Sorbet fragment predicate (`RubyCore/Types/Fragment.lean`)

An executable, reason-carrying predicate defining *which programs a soundness theorem can
be about*, queried by `rubycore --fragment`. Two criteria: (1) every static-unsound
construct must be runtime-checked — which admits `T.cast`/`T.let`/`T.must` and excludes
`T.unsafe`, `.checked(:never|:tests)`, `T::Struct`/`T::Enum` (unchecked getters), and
parameterized generics (erased type arguments, §A.6); (2) no untyped code — every method
sigged, no `T.untyped`, no reflective definition/dispatch.

It is a *static* query: nothing runs, the prelude is not booted, so the answer is
independent of model coverage (the separate `.unsupported` gate). Over the corpus: 6/18
in-fragment, 3 in scope once intersected with srb acceptance, and — the property that
matters — **no unsoundness witness is in the fragment** (guarded by a difftest test that
first asserts the witness set is non-empty, so it cannot pass vacuously).

Implementation note: the "a sig precedes this def" flag is threaded through the single
traversal rather than split into a second pass, because the natural two-function shape
requires a same-size mutual call and has no termination measure.

## L83 — P0a of the static-soundness POC (`Types/Core.lean`, `Proof/StaticSoundness.lean`)

Design doc: `../docs/semantics/static-soundness-poc.md`. The nontrivial choices, and the
alternatives rejected.

- **The typing judgment is *defined by* the executable checker.** `infer Γ e = some (τ, Γ')`
  is the judgment; there is no separate `inductive HasType` to keep in agreement with it.
  This buys two things: no sync obligation between a `Prop` and the decision procedure, and
  **no completeness proof owed** — `none` simply means `unknown`, which is exactly the POC's
  verdict lattice. The cost is that the judgment is not usable for inversion in the pretty
  way an inductive would be; in practice `split at h` on `infer`'s own `match` does the job.
- **Environments thread input→output** (`Env → Expr → Option (Ty × Env)`). Ruby locals are
  *assigned*, not declared, so a non-flow-sensitive `Γ ⊢ e : τ` cannot type `x = 1; x`.
- **`envSet` replaces in place** rather than prepending a shadowing entry, so `Env` equality
  is canonical and therefore *usable as a check*. Both the `if`-merge (branches must agree
  on the environment) and the loop-stability condition are decided by `Γ₁ = Γ₂`, which a
  prepend-based representation would make false for environments that ought to be equal.
- **`while` requires environment-stability at `Γ`; `if` does not.** The loop re-enters its
  condition with whatever the body leaves, so without `infer Γ c = (_, Γ)` and
  `infer Γ body = (_, Γ)` there is no single environment to index `whileCondK`/`whileBodyK`
  by. This is the P0 stand-in for a fixpoint and is the one place the fragment is more
  restrictive than it needs to be. `if` needs no such condition: `ifK` is indexed at the
  *post-condition* environment, which falls out of `CtlOk`'s `.eval` case for free.
- **No separate `InFragment` predicate**, though the design doc §4 called for one. `KontOk`
  has no constructor for 43 of the machine's 48 `Kont`s and `infer` returns `none` off
  fragment, so the restriction is already carried by the typing relations. The whole ~40-way
  `Expr` case split is discharged by `cases e <;> try (simp only [infer] at hinf;
  contradiction)`.
- **`Flat`** (one frame, `captured = none`) is assumed, because `getLocal`/`setLocal` walk
  the captured chain and so reduce to nothing without it. Four lemmas ride on it
  (`getLocal_flat`, `setLocal_owner_zero`, `setLocal_frame`, `getLocal_setLocal`). **This is
  the entry to delete at P1** — `send` pushes frames and `Flat` becomes false. It is stated
  as a conjunct of `Inv` rather than baked into the other definitions precisely so that
  deleting it is a local edit.
- **Progress and preservation are bundled** into `StepOk : StepResult → Prop` (`.next` ⇒
  `Inv`, `.done` ⇒ `True`, everything else ⇒ `False`) so the 48-way `Kont` split and the
  40-way `Expr` split are each walked exactly once. `.uncaught` being `False` under `StepOk`
  *is* the progress obligation; `consecution` and `safety` are three lines each off it.
- **Proved against `stepFn`/`SmallStep`, not the inductive `Step` of `Step.lean`.** `Step`
  covers only the control core and would have to be extended (and its adequacy redone) for
  every fragment widening. Going through `invariant_sound_from` costs a larger case analysis
  and buys immunity from that — and the larger analysis is what the previous bullet makes
  cheap.
- **Examples are discharged by `simp` over equation lemmas, not `decide`.** `infer` is
  well-founded-recursive (three mutually recursive functions over `Expr`/`List Expr`/
  `Option Expr` with `sizeOf` measures), so kernel reduction sticks. `native_decide` would
  work but costs `ofReduceBool`, breaking the axiom baseline for no benefit at this size. If
  P1 programs get big enough that `simp` is slow, the fix is a structurally-recursive
  reformulation of `infer`, not `native_decide`.
- **`check_sound` is over `Machine.init`, `sound_from` over any `m₀` with `Inv`.** P0a's
  fragment issues no sends, so the prelude is inert and the no-prelude start is sound.
  Stating the general form separately means the prelude-booted start `SorbetSafety.lean`
  insists on is an *instance* at P0b rather than a restatement.

## L84 — P0b builtin conformance (`Proof/BuiltinConformance.lean`)

Discharging `builtinSig`'s entries against the interpreter. Choices:

- **Separate file, imported by nothing yet.** The conformance proofs are a distinct concern
  from the type system and are the risky half of P0b, so they land before the `infer`
  wiring and can be reverted without it.
- **`IntBuiltinResolves` is a hypothesis, not a lemma.** It bundles the heap facts a
  dispatch depends on (the table resolves the name to the bid; live, public, unshadowed,
  non-prelude). It cannot be proved in general — a program may reopen `Integer` and redefine
  `+` — so it is assumed here, forbidden by the fragment (§6, no class reopening), and
  discharged for the concrete booted heap elsewhere. **That discharge must not live in this
  file**: it is `native_decide`-shaped and would cost `ofReduceBool`, breaking the axiom
  baseline. Same split as `SorbetConcrete.lean` (L81).
- **`crubySingletonShadow` gets no clause.** It is `none` by computation for any non-`.ref`
  receiver (`Interp.lean:126`), so integer dispatch never needs the hypothesis. P1's object
  receivers will.
- **`lookup_int_const` (`rfl`).** `lookup` reaches the heap only via `classOf`, which is
  `Boot.integerId` for every `.int` (`Heap.lean:396`), so `IntBuiltinResolves` can be stated
  at the single witness `.int 0` instead of quantifying over all integers. Keeps the
  hypothesis first-order and makes it cheap to discharge concretely.
- **`int_bin_step` is parameterized by `bid` + `op` + a `Builtins.run` equation**, with the
  three entries instantiating it. Adding a table entry is then a `rfl` lemma plus a
  three-line instantiation — the ratchet step is deliberately trivial.
- **The `Builtins.run` layer is `rfl` and fast**; `simp [Builtins.run]` is *not* (it blows
  maxRecDepth, then heartbeats, on the 1582-line match). Follow L73's advice: `#eval` to
  check semantics, `rfl` to prove, never `simp` through `Builtins.run`.
- **The proof shape is copied from `T5.dispatch_progress`** — `rw [invoke.eq_def]` then
  `simp [invoke.invokeDispatch, …]` — because `invoke` is well-founded-recursive
  (`termination_by args.length`) and so does not reduce by `rfl`. One addition was needed:
  the `send`/`public_send`/`__send__` re-dispatch guard at the top of `invoke` does not fold
  on string literals under `simp only`, so it is passed in as a `(… || … || …) = false`
  hypothesis discharged by `decide` at each instantiation.
- **Conformance is stated at the `startArgs` level, not about `stepFn`.** First attempt
  phrased it as "`m.ctl = .value b`, `m.kont = argsK … :: rest` ⟹ `stepFn m = .next …`",
  which proves fine but does **not compose**: by the time `StaticSoundness.step_ok` reaches
  the `argsK` case it has already unfolded `applyKont` and generalized `m.kont`, so a
  `stepFn`-shaped lemma no longer matches the goal. Conformance is a fact about *dispatch*,
  and saying so is what makes it usable.
- **`startArgs_plain` is split from the dispatch lemma** even though both are "the send
  path": it needs no heap facts, and the preservation proof consumes the two at different
  `Kont` shapes. Its three `arg ≠ …` side conditions are `startArgs`'s own special cases
  (splat, kwargs, fwd — `Interp.lean:1832`), all of which `infer` already rejects, so the
  caller discharges them from the typing hypothesis rather than carrying them.

## L85 — P0b: wiring `send` into the checker and the proof

- **`TableOk` is a conjunct of `Inv`, not a hypothesis of `check_sound`.** Builtin
  resolution is a *heap* property, so preservation must re-establish it; it does so
  trivially, because no step in the fragment writes the method table. Keeping it inside
  `Inv` rather than on the theorem is what preserves the unconditional headline statement.
- **`tableOk_initHeap` is `rfl`.** The whole point: had the discharge needed `native_decide`
  the theorem would carry `ofReduceBool`. It needs `set_option maxRecDepth 100000` (the
  `rfl`s walk the boot method table) but nothing worse. For the *prelude-booted* heap at P1
  this will likely flip to `native_decide`, and then it must move to a separate concrete
  file (the L81 split), never into `StaticSoundness.lean`.
- **`IntBuiltinResolves` is stated at `.int 0`, not `∀ a`.** `lookup_int_const` (`rfl`)
  says resolution ignores the integer's value, since `lookup` reaches the heap only through
  `classOf`. Keeps the hypothesis first-order and the `rfl` discharge small.
- **Two new `KontOk` constructors, asymmetric on purpose.** `recvK` types the *argument
  expression* with `infer`; `argsK` types the *receiver value* with `ValueTy`, because by
  then the receiver is a value carried inside the kont and there is no expression left to
  infer from. Getting this backwards is the obvious trap.
- **`cases r` is needed for the send site.** `evalExpr` chooses `.selfRecv` vs `.explicit`
  by matching on the receiver *expression* (`Interp.lean:2582`). That match does not rewrite
  under `rw` or `simp only [site_explicit hr]` — the motive does not line up — so the only
  reliable move is to force it to compute. 40 goals, all discharged by one `try exact`, plus
  the `self'` case by contradiction with `infer`.
- **`dsimp only` before `rw` in the `applyKont` cases.** After `generalize hK : m.kont = K`
  and `cases hk`, the goal still holds an unreduced `match K with …`. Cases that finish with
  `exact` never notice (defeq does the work), but `rw` needs the iota reduction first. This
  bit twice; if a `rw` into an `applyKont` arm reports "did not find an occurrence" of a
  pattern that is plainly there, this is why.
- **Pin the machine when rewriting with a dispatch lemma**:
  `int_add_dispatch (m := { m with kont := k }) htab.1`. The implicit `m` is solved from the
  `IntBuiltinResolves m.heap …` argument, which pins it to the *outer* machine, while the
  goal is about the kont-popped one. The heaps are definitionally equal; the elaborator will
  not go looking.
- **`infer_send_inv` is a standalone lemma** rather than inline `split at`. The nested
  splits need `next`-bound names (`rename_i` miscounts and silently destructures the
  environment list instead), which is unreadable inside an already-large case analysis.

## L86 — the `reject` verdict as an independent second pass

- **Not a third value threaded through `infer`.** `infer`'s `none` conflates "outside the
  fragment" with "ill-typed", and splitting it would have touched all three functions in the
  `mutual` block, all nine `KontOk` constructors that reference an `infer`/`inferSeq`/
  `inferIf` equation, `CtlOk`, `infer_send_inv`, and every `absurd hinf` in `step_ok`.
  `check` instead consults `illTyped` only after `infer` has failed, so **`check_sound` did
  not change at all** — one line of `initiation` (`by simp` → `by split <;> simp`, because
  the `none` branch is now an `if`) was the entire proof cost.
- **`reject` has no theorem, by design.** It claims our *rules* refute the program, not that
  the program fails: a refuted call can sit on a dead branch. Its guard is the difftest
  direction `reject ⇒ srb rejects`, which is P2. Anyone tempted to strengthen it to "will
  raise a TypeError" should read `typed-portion-safety.md` §8.1 first — that is the
  *witnessed* verdict, a different (and cheaper) thing built on `run_typeError_unsafe`
  (`Proof/TypeSafety.lean:243`), not on syntax.
- **Three separate conservatism knobs, all pointing at `unknown`.** (1) `defTy` takes no
  environment, so locals have no unconditional type; (2) `tableRefutes` fires only when the
  method is *present* in `builtinSig`, because the table is deliberately narrow — `/` is
  absent but valid, and rejecting it would break the guard outright; (3) `illTyped` does not
  recurse past a node off the fragment's spine, so an unsupported construct hides everything
  under it. Knob (2) is the load-bearing one: it is the difference between "absent means no
  opinion" and an immediate difftest violation.
- **Verdicts were checked against a real `srb`** (0.6.13405, from the `sorbet` gem —
  `$(gem contents sorbet | grep bin/srb)`, run with a `sorbet/config` of `false` in a temp
  dir), not assumed. One nuance found that way and recorded in the examples: srb rejects
  `if false then 1 + nil else 0 end` with **7006 unreachable**, not 7002 — so we agree on
  the verdict but not on the reason, which will matter if the difftest ever compares
  diagnostics rather than accept/reject.
- **Examples live next to what they test**: verdict examples in `Types/Core.lean`,
  safety-bearing ones in `Proof/StaticSoundness.lean`. Two duplicates were removed from the
  proof file when the reject pass landed, and one of them (`1 + true`) had become *wrong*
  there — it asserted `unknown`.

## L87 — the checker difftest harness

Difftesting `check` against `srb`, per `docs/semantics/static-soundness-poc.md` §7.

- **`rubycore --check` is static, like `--fragment`.** No prelude boot, nothing executed, so
  the verdict is independent of model coverage — a program the interpreter cannot run still
  gets a checker verdict. That is the right call because `check` is a *static* artifact and
  conflating it with `.unsupported` would make the ratchet's `unknown` count meaningless.
- **The JSON carries the inferred type alongside `accept`, as a development aid only.**
  It is deliberately not a difftest signal: comparing inferred types against
  `T.reveal_type` tests neither direction that matters (`typed-portion-safety.md` §8, which
  replaced exactly that plan). Recorded here so nobody later mistakes the field for an
  oracle.
- **Mining the bootstraptest corpus was measured before being relied on, and it does not
  carry the harness.** 1304 programs → 21 accept, **0 reject**, 1190 unknown, 93 pipeline
  failures. Twelve of the 21 are empty or a bare literal. So mining supplies a small, real,
  *accept*-only sample and cannot exercise `reject` at all — which is the dangerous verdict.
  Generation is therefore not an optimisation, it is required. Recorded so the 1.6% is not
  re-derived later.
- **`# typed: true` is injected when handing a file to `srb`.** Bootstraptest files carry no
  sigil, and `srb`'s default is `# typed: false`, under which it checks essentially nothing
  — the comparison would be vacuous and would look like perfect agreement.
- **The srb-error exclusion list is closed, and an unknown code fails the run.** Two entries,
  both found by measurement rather than anticipated: **7006** (unreachable / always-truthy —
  a reachability opinion, not a type one) and **3002** (unsupported integer literal — an srb
  implementation limit). The alternative, recording unrecognised codes and continuing, makes
  the exclusion list a place to quietly park disagreements; that is exactly the erosion the
  pinned zeros exist to prevent.

## L88 — P1 scoping: the shim wall, measured

Before writing any P1 Lean, `rubycore --trace` was used to price sigs. The numbers decided
the milestone split, so they are recorded here rather than re-derived:

| program | steps |
|---|---|
| `require "sorbet-runtime"` + `extend T::Sig` | 13 |
| + `sig {...}` + `def f(a)` | 230 |
| + `f(2)` | 486 |
| + `f(3)` | 742 |
| the same `def`/call **unannotated** | 15 |

Registration ~217 steps; **every sig'd call ~256 more** (exactly 256, from the two-call
delta) against ~7 unwrapped. Those steps are the `T` shim (L80) running as ordinary
RubyCore — hashes, arrays, blocks, ivars.

- **This is why `Inv`'s technique does not stretch to sigs.** `Inv` works by *restriction*:
  `KontOk` has constructors only for admitted `Kont`s, and everything else is discharged by
  contradiction (L83). The shim leaves any small fragment on its first step, so `Inv` is
  false immediately after `sig` is evaluated. Widening the fragment cannot fix it — the
  shim touches essentially the whole language.
- **P1 therefore keeps the proved fragment sig-free** and spends its proof effort on
  *methods* (frames, `frameK`, per-frame locals, `Flat` deleted). That work is needed under
  every option, so none of it is wasted.
- **The intended successor is the two-machine argument**: prove `TypeSafe` for the
  *stripped* program and transfer to the annotated one. Note the conclusion weakens on
  transfer — the annotated program can raise blame where the stripped one cannot, so the
  annotated statement is `SorbetSafe` (blame carved out, `Proof/SorbetSafety.lean:76`), not
  `TypeSafe`. `difftest/ruby/sig_strip.rb` already implements the `e ⊑ e'` direction.
- **The sig *reader* is still built first (P1a) and is not blocked by any of this**, because
  reading a declared type off the AST is a static question. It just cannot feed `accept`
  until the machine-side story exists, so sig-bearing programs stay `unknown`.

## L89 — P1a, the sig reader (`Types/SigRead.lean`)

- **`SigTy` is deliberately wider than `Ty`, and `toTy` is the explicit bridge.** `Ty` is what
  the *proof* understands (three ground types); `SigTy` is what a *program can declare*.
  Conflating them would have forced `Ty` to grow for reasons the proof does not need, and
  would have made the reader silently lossy. `toTy` is partial and its `none` must be read as
  "cannot say", never as a default.
- **`render` reproduces Sorbet's surface syntax exactly**, so reader output is comparable
  against a generator's declaration string with no translation layer between them
  (`difftest/difftest/sig_gen.py`'s `Ty.render`). That is what makes the validation arm a
  one-line comparison instead of a mapping table nobody trusts.
- **Unrecognised links in the sig chain are skipped, not failed.** `.checked(:tests)`,
  `.override`, `.abstract`, `.type_parameters` modify enforcement or dispatch, not the declared
  types; refusing them would discard signatures we can read perfectly well. Verified: the
  `.checked(:tests)` case reads its types [V].
- **`ret = none` means `.void`**, which is Sorbet saying "no meaningful return" — not an
  absence of information. The JSON emits `null` for it, and the distinction matters because a
  `def` with *no sig at all* is omitted from the output entirely (the gradual boundary).
- **`collectSigs` threads the pending declaration rather than a flag.** `Fragment.lean` threads
  a `sigPrecedes : Bool` for the same adjacency problem (L82); carrying the decl itself is the
  same single traversal holding slightly more, and avoids a second pass whose natural
  two-function shape has no termination measure.
- **`DecidableEq` cannot be derived for `SigTy`** — the nested `List SigTy` defeats the
  handler. Nothing needs it, so it is dropped rather than hand-written.
- **The reader is validated against the generator, which is a real oracle**, not a
  self-consistency check: `checker siggen` chooses types *before* rendering them to Ruby, so
  agreement means the reader understood Sorbet's syntax. `difftest checker sigread` fails the
  run on any mismatch — a reader that garbles a declared type would poison every later typing
  decision. Measured: 80 signatures over 40 programs agree, and agreement holds at
  `--coverage {0.0, 0.5}`, `--sigil strict`, and `--loose 1.0` (all-widened types).
- **`undecidable` also fails the `sigread` run.** The generator only emits programs the
  pipeline can handle, so a desugar/decode failure there is a pipeline regression rather than
  honest abstention — unlike `checker fuzz`, where `unknown` is a legitimate outcome.

## L90 — P1b step 1: `Flat` deleted, and it was cheaper than L83 predicted

L83 flagged `Flat` (one frame, `captured = none`) as "the entry to delete at P1", and §8.1(2)
priced frame-store work as P1's dominant cost. Deleting it turned out to be small, for a
reason worth recording:

- **Two of `Flat`'s three clauses were never load-bearing.** `stack = [0]` and
  `frames.size = 1` were added so the `getLocal`/`setLocal` fuel recursions would reduce. They
  are not needed: `getLocal`'s fuel is `m.frames.size + 1`, *always* a successor, so
  `Machine.getLocal.go` unfolds once whatever the array size. Only `captured = none` on the
  **current** frame does any work.
- **`FrameOk` is therefore `stack ≠ [] ∧ curFid m < frames.size ∧ captured = none`.** The
  bound replaces `frames.size = 1` and is what `getD_set!_self` needs; a *stack* of frames
  satisfies it, which is the precondition methods need.
- **The `curFid` indirection is what made the rename mechanical.** Every lemma that said
  "frame 0" now says "frame `curFid m`", and the only new obligation anywhere is
  `curFid m' = curFid m`, discharged from stack equality by `simp [curFid, hs]`.
- **`LocalsOk_congr` gained a `stack` hypothesis.** With a fixed frame 0 it needed only
  `frames` equality; with `curFid` it needs the stack too, or the two sides name different
  frames. Callers pass `rfl` twice — the machines differ only in `ctl`/`kont`.
- **Only `initiation` needed real repair**, because `⟨rfl, rfl, rfl⟩` no longer typechecks
  against the new clauses; `simp [Machine.init, Machine.initOn]` discharges them.

Cost: one file, no change to `check`, no change to the axiom baseline, and the fragment is
byte-identical. Worth noting against L83's prediction — the frame-store cost is real but it
sits in the *env-stack* generalization (P1b step 2), not in local access.

## L91 — P1b step 2: `KontOk` indexed by an environment *stack*

Mechanical half of the method-dispatch generalization, landed on its own.

- **`KontOk : List Env → Ty → List Kont → Prop`.** Every existing constructor operates on the
  head and passes the tail through untouched, so the diff is `Γ` → `Γ :: Γs` throughout;
  `CtlOk` gains a `Γs` parameter and `Inv` an extra existential. `KontOk.nil` deliberately
  accepts *any* stack, including `[]` — that is what makes the toplevel case work.
- **[✗→] `frameK` was written and then removed from this commit.** Its case in `step_ok` is not
  merely unused, it is *unprovable*: popping an activation resumes the caller's locals, so the
  invariant must carry per-frame conformance (each frame against its own environment) before
  the constructor can be discharged. Adding a constructor whose case cannot be closed turns a
  green file red for no gain, so `frameK` now lands together with user dispatch — the only
  thing that produces one. The comment in place of the constructor says so, to stop the next
  person re-adding it in isolation.
- **What the deferred clause needs**, scoped while it was fresh: `FramesOk : List Env →
  Machine → Prop` requiring conformance frame-by-frame down the stack. The pop case is then
  free (a suffix of a conforming stack conforms), and the only real obligation is that
  `setLocal` leaves frames *other* than `curFid` alone — which needs stack entries to be
  distinct, true because a pushed frame id is `frames.size` and therefore strictly increasing,
  but an invariant clause rather than a theorem.
- Cost: one file, fragment byte-identical, axiom baseline unchanged. `Γs` is `[]` in every
  reachable configuration today, so this commit is pure preparation — its value is that the
  next diff is only the two new step cases.

## L92 — P1b step 3: per-frame conformance, and `frameK` proved

L91 deferred `frameK` because its case was unprovable without per-frame conformance. That
clause now exists and the case is closed.

- **`FramesOk : Array Frame → List FrameId → List Env → Prop`**, recursive down the stack,
  innermost first. Phrased over the **array and the stack** rather than over the machine, which
  is what makes it transport by `rfl` under `ctl`/`kont` updates: P0a needed `FrameOk_congr`
  *and* `LocalsOk_congr` and both are now deleted, as is `LocalsOk_setLocal`.
- **The `∀ g ∈ fids, g < fid` clause is what makes `setLocal` provably local.** `setLocal`
  writes at `curFid`; every frame below has a strictly smaller id, hence a different one, hence
  is untouched (`getD_set!_ne`). Distinctness is true of the real machine — a pushed id is
  `frames.size` — but it must be *carried*, so it rides in the invariant rather than being
  rediscovered. Equal lengths come free from the `_, _ => False` arm, which is why this also
  subsumes P0a's `stack ≠ []`.
- **`FrameOk` and `LocalsOk` survive as *derived* notions** (`FramesOk.frameOk`,
  `FramesOk.localsOk`), which kept the local-access lemmas and the `var` case of `step_ok`
  untouched. Deriving rather than replacing is why this refactor was one file and not three.
- **[✗→] `frameK` needs a *two-deep* environment stack**, `Γ :: Γ' :: Γs`. The one-deep version
  looks right and is wrong: `KontOk.nil` accepts any stack including `[]`, so
  `KontOk (Γ :: []) τ [frameK]` would be derivable, and popping it leaves a machine with no
  current environment for `CtlOk`. Requiring the caller's environment to exist is what makes
  the pop total. Found by the case failing to close, not by reading.
- **Two array lemmas were needed and neither is in core** under a guessable name:
  `getD_set!_ne` and `getD_push_lt`. `Array.getElem_setIfInBounds_ne` takes the bound as an
  explicit argument and its disequality the *other* way round (`i ≠ j`), and `simp only
  [Array.getD]` followed by `split` produces `getInternal` terms that `rw` cannot see through —
  use `dif_pos`/`dif_neg` with an explicit size-equality rewrite instead.
- **Ordering bite:** `FramesOk.setLocal` needs `envGet?_set`, which lived in a later section.
  The env lemmas moved up to §1.3. Worth knowing because the file's sections are otherwise in
  dependency order and this was the first exception.

Still no `def`/dispatch in the fragment: `Γs` is `[]` in every reachable configuration, so
`frameK` remains unproduced. What is now true is that the invariant *supports* activation
stacks and the pop is proved, so the remaining step is the two new `step_ok` cases plus the
`TableOk`-under-`defineMethod` heap lemma flagged last turn.

## L93 — `TableOk` under `defineMethod`: the chain, priced

P1b's last obligation, sized before being attempted. A user `def` mutates the method table
(`Interp.lean:2615`), so `Inv`'s `TableOk` conjunct must survive it. `TableOk` reaches the
heap through exactly two functions — `lookup` and `ancestors` — which decomposes it:

1. **`shape_defineMethod`** — `defineMethod` leaves every payload field except `methods`
   alone, which is what makes the rest possible since `ancestors` reads only
   `prepends`/`includes`/`superclass`.
2. **`ancestors` congruence** — a fuel induction over `ancestors.go` *and* a second over
   `modAncestors.go` (`Heap.lean:416`, `431`), because the chain walk splices included
   modules.
3. **`lookup` congruence** via **name-disjointness**: at every class in the chain,
   `methods.find? (·.1 == m)` is unaffected by prepending an entry named `name ≠ m`
   (`find?_filter_ne`). Avoids reasoning about *where* in the chain resolution lands, which
   the alternative condition ("the resolving class precedes `owner`") would force. The
   fragment supplies the side condition syntactically by forbidding a `def` of any name in
   `builtinSig`.
4. `IntBuiltinResolves_defineMethod` → `TableOk_defineMethod`.

**All four are now proved**, axiom-clean (`[propext, Quot.sound]` — not even
`Classical.choice`), and with no `native_decide` anywhere, which is what §8.4/L94 requires.

Traps found while proving (1), all in `Heap` internals rather than in the statement:

- `Heap.set` is `Array.set!`, so the `k = cls` case needs the in-bounds fact. It comes from
  `classPayload? k = some c` via the new `classPayload?_oob`; **`simp [Heap.set]` without
  splitting on the bound leaves an irreducible `if k < size`** in the goal.
- `classPayload?_oob` finishes with a bare `rfl` after `simp`: the goal reduces to a match on
  `default.payload`, and `simp` will not take the last step.
- The `Object` array lemma is stated separately from the `Frame` one in
  `StaticSoundness.lean`. Generalising over the element type was tried and was not shorter,
  because both need `Inhabited`-specific `default` reasoning.

**Alternative considered and rejected.** State `check_sound` from a machine with the `def`s
already installed (`sound_from`), discharging setup per-program by `native_decide` — the same
split P1d needs for sigs. It dodges the chain entirely but weakens the headline claim for
every method-bearing program, and these lemmas are reusable by any future heap-mutating step.
Worth paying for once.

## L94 — standing rule: no `native_decide` above a per-program leaf

`native_decide` discharges a goal by compiling and running it, putting the Lean **compiler and
runtime** in the trust base beside the kernel. Rule, adopted here rather than assumed:

> No `native_decide` in a metatheorem, and none anywhere on the path from `check` to
> `check_sound`. It may sit on a **leaf claim about one concrete program**, never on a theorem
> about all of them.

- **Inventory [V]: 8 tactic uses in 5 files**, all per-program — `SorbetConcrete` (3),
  `T5Concrete` (2), `QLearningTypeSafe` (1), `Search/Random` (2, and off the default target).
  Many other files *mention* it in prose; those are not uses, so grep for `by native_decide`
  rather than the bare word when auditing.
- **Each use mints its own axiom**, e.g.
  `sigBasic000_runs_to_value._native.native_decide.ax_1_1`. That is worth knowing: the
  audit is precise, `#print axioms` names the exact program-level fact that is
  compiler-trusted, and there is no single global `ofReduceBool` to hide behind.
- **The general lemmas above the leaves are clean** — `runsToValueBooted_safe` and
  `runsToSorbetStuckBooted_unsafe` are `[propext, Classical.choice, Quot.sound]` [V], as are
  `check_sound`, `sound_from`, `step_ok`, `int_add_dispatch`, `tableOk_initHeap`. The existing
  files already respected the rule; it just was not written down.
- **`tableOk_initHeap` is the model to copy.** A fact about a large concrete heap, proved by
  `rfl`. It only works because of L73's reducibility discipline, which is therefore not a
  historical curiosity but the thing that keeps the compiler out of the trust base.
- **[✗→] Two earlier notes offered `native_decide` as a fallback and must not be followed.**
  L85 said a prelude-booted `TableOk` "will likely flip to `native_decide`", and L93 offered a
  defs-installed start machine discharged the same way. Both are now closed off. The
  prelude-booted case in particular deserves a *measurement* first — `rfl` already handles the
  boot heap, so whether it handles the prelude-booted heap is unknown, not hopeless.


## L95 — closing the `defineMethod` chain: what the four links actually cost

Follow-up to L93, which priced the chain. It is closed. The estimate was roughly right about
*where* the work was and wrong about *how* the difficulty distributes: steps 2–3 were long but
mechanical once the right congruence shape was found, and every real fight was a Lean-side
detail rather than a semantic one.

- **Congruence is stated over a `ShapeAgree` hypothesis, not over `defineMethod`.** `ancestors`
  and `modAncestors` are congruent in *any* two heaps that agree on
  `prepends`/`includes`/`superclass` pointwise and have equal `objs.size`; `defineMethod` is
  then one instance. That generalisation cost nothing and makes the lemmas reusable by every
  future heap-mutating step — which was the argument for paying for the chain at all.
- **`modAncestors` needs a `funext` form.** `ancestors.go` uses `modAncestors h` *unapplied*
  as the function argument of `flatMap`, so the pointwise congruence will not rewrite there
  and `simp` reports the argument unused. `modAncestors_funext` is the version `simp` can use.
  This cost the most time of anything in the chain.
- **`lookup.go` needs a `dsimp only` before the `rw`.** After `cases h1 : … classPayload? k`
  the goal still holds `match some c' with …`; the rewrite target is under an unreduced iota.
  Same trap as L85's `applyKont` note, in a different function — worth treating as a general
  rule for this codebase: **after `cases` on a scrutinee, `dsimp only` before any `rw`.**
- **The `name`/`methods` field lemmas are three copies of one proof shape.**
  `shape_defineMethod`, `methods_find_defineMethod` and `clsName_defineMethod` differ only in
  the projection. Factoring over the projection was attempted and abandoned: the `k = cls`
  branch needs projection-specific `simp` sets (`find?_filter_ne` for one, nothing for the
  others), so the shared form was longer than three instances.
- **`TableOk_defineMethod` holds for *any* target class**, including `Integer` itself. Only the
  *name* has to differ from a tabulated builtin. That is a stronger statement than expected —
  the fragment does not need to forbid reopening `Integer`, only shadowing `+`/`-`/`*` — and it
  is what makes the side condition purely syntactic.

## L96 — P1b: `def` enters the proved fragment

The first actual widening since P0b. `def f; 1 + 2; end; 3 * 4` is accepted and
`egDef_safe` proves it type-safe, axiom-clean. Zero-parameter definitions only; calls come
next.

- **Three excluded names, each discharging an invariant clause rather than expressing taste.**
  `+`/`-`/`*` would shadow a tabulated builtin and break `TableOk`
  (`TableOk_defineMethod`); `method_added` would install the `def` hook. All three are
  syntactic, which is the point — the fragment predicate stays decidable.
- **The hook is excludable because the prelude installs it lazily.** `T.__toplevel_sig`'s
  `Object.define_singleton_method(:method_added)` (`prelude/prelude.rb:1187`) runs only when a
  toplevel `sig` is evaluated, so a sig-free program never has one and `lookup` misses —
  `rfl` on the boot heap [V]. Had it been installed eagerly on `Module`, every `def` would
  dispatch a hook and this milestone would have been impossible without P1d.
- **`NoHook` must be a pure *heap* fact, and `defmod` must live in `FrameConforms`.** Stating
  it as `lookup m.heap (.ref (curFrame m).defmod) …` is unprovable across `frameK`, which
  resumes a *different* frame whose `defmod` the invariant would know nothing about. Carrying
  `f.defmod = Boot.objectId` per frame fixes it, and pop then transports `NoHook` for free.
  Found by the `frameK` case failing after the clause was added — the same lesson as L92's
  two-deep env stack.
- **The body is checked even though nothing can call it.** Skipping the check would accept
  strictly more programs now and fewer once calls arrive, which is a ratchet *regression*.
  Accept only ever grows.
- **`Ty.sym` exists solely because `def` evaluates to the method name** (`Interp.lean:2624`),
  so a `def` in tail position needs a type. Nothing constructs or consumes one otherwise.
  It also has to be added to `Main.lean`'s `--check` type rendering — a non-exhaustive match
  there is a *build* failure, not a proof failure, and the proof file compiles happily without
  it. Check `lake build`, not just the file.

Tactic notes, both new:

- **`split` dives into the `MethodDef` literal's `visibility` `if`s.** The `def` branch has two
  outer conditions (`reprSensitive`, `preludeMode`) and two more buried inside the term. Case
  on the outer two with `by_cases` and let the inner ones ride — `hres` is quantified over the
  machine precisely so they never have to be resolved.
- **Quantify a helper over the *facts*, not over the `MethodDef`.** `∀ md, … → Inv …` leaves
  `md` an unsolvable metavariable when applied by `refine`, because nothing in the conclusion
  mentions it. Taking `TableOk m₀.heap` and `NoHook m₀.heap` as hypotheses instead fixes `m₀`
  from the goal first and forces each remaining unification.

## L97 — dynamic (non-symbol) keyword keys at a call site

`f("a" => 1)` / `delegate [:x, :y] => :version` is a brace-less keyword hash whose key is
an arbitrary expression rather than a static symbol. The decoder gated it
(`"dynamic (non-symbol) keyword key"`), which was #6 on the tier-0 `Unsupported`
histogram (14 cases) and the one thing stopping Homebrew's `pkg_version.rb` — a
version+vulnerability slice file — from decoding at all (`homebrew/PLAN.md` M1).

**Shape.** `KwEntry` gains `.dyn (key : Expr) (val : Expr)` alongside `.pair`/`.splat`.
The static-symbol case keeps its own constructor rather than being folded into `.dyn` with
a `[:sym, k]` key expression: `.pair` carries the key as a `String`, which is what the
parameter binder matches on, and collapsing them would push a runtime `Value` comparison
into every ordinary `k: v` call.

**Evaluation order.** Two konts, `kwDynKeyK` then `kwDynValK`: key first, then value,
entries left to right — the same order a hash literal uses. [V] verified against CRuby with
a marker-printing key/value pair (`f(m("k1") => m("v1"), m("k2") => m("v2"))` prints
`k1,v1,k2,v2` in both). Accumulation reuses `kwAdd`, so duplicate keys keep first position
and last value, and `**h` splats interleave correctly.

`Types/Fragment.lean`, `Types/SigRead.lean` and `Trace.lean` get the new case
(`SigRead.readKw` returns `none` — a `sig` with a computed keyword name is not a sig we
read).

**Result (measured).** tier-0 `--sut lean` **942 → 955 agree, 0 disagree** (13 of the 14
gated cases; the remaining one has a second gate behind this). Discriminating snippet
byte-identical to CRuby across string keys, symbol keys, a computed key, an array key,
`**`-splat interleaving, and the eval-order trace. All 8 slice files now decode.

**Not done here (deliberate).** `homebrew/PLAN.md` norm 3 says a workstream touching
`Interp.lean` (2,767 lines) should split it first. This change is +6 lines on the *send*
path, not the builtin-dispatch section W2d is scheduled to split; the split lands at M3,
before the regex work, as planned.

## L98 — `Builtins.lean` split into `Builtins/` — one class group per file

`RubyCore/Builtins.lean` was 1,582 lines, 1,290 of them a single `run` function: one
`match bid with` over every builtin rule, plus a 270-line `where` block. The regex API
(`homebrew/PLAN.md` W2a `Api.lean`) adds ~20 `String`/`Regexp`/`MatchData` rules to it, so
the norm — no file over 1,000 lines, split before you touch it (`PLAN.md` §4.3, milestone
M3) — bites here first.

**Shape.** `run` keeps only the two pre-match rules (the zero-arg arity check and the
uniform `dup`/`clone` rule) and hands off to a **chain**:

```
run → runObjects → runNumerics → runStrings → runCollections → runModules
        Object/Kernel/nil/bool   Integer/Float   String/Symbol/Proc   Array/Hash   Exception/Module/Class
```

Each file matches its own bids and its default arm calls the next; the last one is where an
unmodeled bid becomes `.unsupported s!"builtin {bid}"`. Imports run backwards along the
chain, so the dependency order is explicit and acyclic.

**Why a chain and not `Option BRes` + `orElse`.** A `BRes`-returning tail call unfolds in
one step and allocates nothing; an `Option`-returning stage plus `orElse` puts an extra
`Option` match between every builtin call and its result, on the dispatch path, in every
`rfl`-reducible leaf proof. L73's reducibility trap says do not put anything on the dispatch
path that costs kernel reduction for free.

**`Builtins/Support.lean`** holds what the rule files share: the payload accessors,
allocation helpers, `SortKey`/`BRes`, the numeric and string-ordering primitives, the bid
lists, and — the reason the split is possible at all — the former `where` helpers, promoted
to top level (`binArg`, `putsImpl`, `raiseImpl`, `newImpl`, `joinImpl`, `sortImpl`, …). A
`where` binding is not visible outside its own definition, so those had to move. The only
edit beyond relocation is **ordering them by use** (`putsGo` before `putsImpl`,
`raiseClass` before `raiseImpl`, `flattenAll` before `joinImpl`), which `where` did not
require.

**No behaviour change, and that is checked, not asserted.** tier-0 `--sut lean`
**955 agree, 0 disagree** — byte-identical to the pre-split run. `#print axioms` on
`invariant_sound`, `Static.check_sound` and `sorbet_invariant_sound`: `[propext,
Classical.choice, Quot.sound]`, unchanged. Every file is now under 600 lines
(48 / 206 / 149 / 228 / 392 / 138 / 569).

Still to split under the same norm: `Interp.lean` (2,767) — the next one, and the one the
regex *dispatch* touches.

## L99 — `Interp.lean` split into `Interp/` — one stage of the machine per file

The companion to L98, and the one the regex *dispatch* work needs: `RubyCore/Interp.lean`
was 2,767 lines. It is now 370, with five files behind it:

| file | lines | contents |
|---|---|---|
| `Interp/Support.lean` | 439 | `StepResult`; control/kont constructors, exception-region bookkeeping, parameter classification + binding, splat spreading, the return target, closure creation/invocation |
| `Interp/Dispatch.lean` | 568 | the ancestor walk, entering a user method or a class/module body, eigenclasses, visibility, `method_missing`, the iterating-builtin bridge, mixin hooks |
| `Interp/Reflect.lean` | 481 | the reflective metaprogramming core (`define_method`, `*_eval`, `prepend`, `alias_method`, `singleton_class`, ivar/const reflection, `Class.new`) + the lookup-miss classifier |
| `Interp/Send.lean` | 522 | `invoke`, `super`/`zsuper`, `finishSend`, `startArgs`/`startKwargs`/`doYield` |
| `Interp/Kont.lean` | 493 | `applyKont` and `unwind` |
| `Interp.lean` | 370 | `evalDefined`, `evalExpr`, `stepFn` |

**Why this cut is free.** The file's own header already recorded the load-bearing fact:
*"the helpers below are NOT mutually recursive: each performs exactly one transition —
evidence the machine really is small-step."* That means the definitions were already in a
topological order, so the split is five cuts along it and a linear import chain. Nothing
was reordered, renamed, or re-typed; each cut was pulled back to include the leading `/--`
doc comment of the definition it precedes.

Every file is now under 600 lines, and the parts a workstream touches are separable: the
regex API is a `Builtins/` rule file plus, at most, `Interp/Send.lean`.

**Checked, not asserted.** tier-0 `--sut lean` **955 agree, 0 disagree** — identical to
before the split. `#print axioms` on `invariant_sound`, `Static.check_sound` and
`sorbet_invariant_sound`: `[propext, Classical.choice, Quot.sound]`, unchanged.

With L98 this closes `homebrew/PLAN.md` M3 on the Lean side; `difftest/tiers/tier1/
strategies.py` (1,087) is the remaining offender and is W4b's to split.

## L100 — the regex engine: syntax, parser, matcher, and its own oracle (W2a)

The long pole of `homebrew/PLAN.md` (M4). Landed in the order the plan's risk table
prescribes — Syntax → Parse → matcher → oracle — with the Ruby-visible API (`Api.lean`)
still to come. New directory `lean/RubyCore/Regex/`, nothing over 400 lines.

**Scope is measured, not guessed.** The 86 regex literals of the eight slice files use:
bracket classes (53), `+` (49), `?` (44), `(?:…)` (32), interpolation (28), `\A` (28),
`\d`/`\w`/`\s` (26), `\z` (22), `$` (22), `*` (20), `|` (19), `.` (18), `{n,m}` (7),
backrefs (2), `(?!…)` (2), lazy (2), `^` (2), `(?i:…)` (2), `\Z` (1), `(?<name>…)` (1),
`(?=…)` (1). **Zero** uses of lookbehind, atomic groups, possessive quantifiers, `\b`,
POSIX bracket classes, `\p{…}`, `\x…`, or `\G` — each of which the parser therefore
*gates by name* rather than approximating. Resisting generalisation beyond this list is a
plan decision (§7), not laziness.

**`Syntax.lean`** — `inductive Regex`. Two flags are resolved at parse time rather than
carried at match time: `i` is pushed onto the leaves it reaches (so `(?i:…)`'s lexical
scoping needs no flag stack to unwind on backtracking) and `x` is purely lexical. `m`
survives only as a field of `any`. `^`/`$` are line anchors in Ruby *regardless* of `m`
(unlike Perl), so no flag reaches them.

**`Parse.lean`** — recursive descent, total, structurally recursive on a fuel `Nat` seeded
from the input length. Every failure is an `Except String` with a reason the caller turns
into the clean `Unsupported` gate; there is no path on which it guesses a pattern.

**`Match.lean`** — leftmost, greedy-first backtracking in CPS, **structurally recursive on
a fuel `Nat` computed from the input** (D1): no `partial def`, no `termination_by`, so the
definition reduces in the kernel and a per-program `rfl` leaf proof stays possible
(L73/L94). Fuel exhaustion is a **third outcome** (`MRes.oof`), distinct from "no match"
and propagated to the top — a matcher that reported "no match" when it ran out of fuel
would be a silent wrong answer, the one failure mode the ratchet cannot catch. Once
`bound_suffices` is proved the gate becomes dead code rather than a caveat.

**One real fidelity finding, and the reason the oracle exists.** The obvious reading of
"a repetition may not loop on an empty match" — refuse the empty iteration — is *wrong*.
CRuby **performs** the empty iteration, keeps its captures, and only then stops looping:
`/(a*)*/ =~ "aaa"` leaves `$1` as the empty match at offset **3**, not `"aaa"`, and
`/(a?)*b/ =~ "b"` sets `$1` to `""` rather than leaving it nil. That is the only
disagreement the first run produced, and it accounted for all eight of them.

**The oracle** (`scripts/rxcases.rb`, `scripts/rxprobe.rb`, `scripts/rxprobe.lean`). Cases
are `pattern ⇥ opts ⇥ input`; both sides print the same line format, so `diff` is the
test. Two populations: the slice's own harvested patterns (interpolations replaced by
plausible sub-patterns, since the desugarer builds a `Regexp.new` over a string anyway)
crossed with 60 version-, URL- and CVSS-shaped inputs; and a hand-written adversarial set
for the constructs where *backtracking order is the specification* — greedy vs lazy,
nested and empty-body repetition, capture restoration across backtracking, leftmost (not
longest) alternation, the anchors at string edges, `\Z` before a trailing newline, negated
classes, case folding, lookahead, and `(a+)+b` on a non-matching input (which must answer,
not hang). This needs none of the rest of the pipeline, so a failure is unambiguously a
regex bug.

**Result (measured).** **7,418 / 7,418 cases byte-identical to CRuby — 0 disagreements, 0
`OOF`, 0 parse gates.** The zero `OOF` is the empirical half of `bound_suffices`: the
computed bound sufficed on every case, including the exponential-looking one.

Not wired into `stepFn` yet, so the tier-0 ratchet is untouched by this commit (955 agree,
0 disagree). `Api.lean` is next, then `Relation.lean` + `Adequacy.lean` + `Bound.lean` as
W6 proof obligations.

## L101 — the Ruby-visible regex surface: `Regexp`, `MatchData`, `$~` and friends

L100's engine, wired into the model (W2a `Api.lean`). Three bootstrap classes
(`Regexp` 36, `MatchData` 37, `RegexpError` 38 — `mainId` moved to 39, since `initHeap`
allocates `classTable` densely and then `main`, so **`mainId` must stay last**; a comment
now says so), two `Payload` constructors, and one rule file
`Builtins/Regex.lean` at the end of the L98 chain.

**A `Regexp` stores its source and options, not a compiled `Rx.Regex`.** Each use
re-parses. That keeps `Payload` a plain data type — no `Regex` value has to sit inside
`Value` and be `Inhabited`/`Repr`-able — and costs a linear pass over a pattern that is,
in this corpus, tens of characters long. Revisit if a profile ever says so.

**One choke point.** Every pattern application goes through `runSearch`, which is the only
place the engine's three outcomes meet Ruby's two: a parse failure gates with the parser's
own reason (never an invented `RegexpError`, never a guessed pattern); `oof` gates as
`"regex: bound exhausted"` (never "no match"); `no`/`yes` become `nil`/a `MatchData`.
`Regexp.new` parses eagerly, so a bad pattern gates at construction, which is where CRuby
raises.

**`$1`…`$9`, `$&`, `` $` ``, `$'` are views of `$~`, not stored globals** (`matchGlobal`
in `Interp/Support.lean`). Storing them would make every *failed* match responsible for
clearing nine slots, and would still get `defined?($3)` wrong. Deriving them is what fixes
`bootstraptest/test_syntax_032` — the one disagreement this batch produced, and a good
one: it asks for `defined?($1..$4)` before and after `/(a)(b)/ =~ 'ab'`, so it is precisely
a test that the *arity of the last match* is visible through `defined?`.

**Implemented.** `Regexp#source/options/names/match/match?/=~/===/inspect/to_s/==/eql?/
hash`; `MatchData#[]` (integer, symbol and string keys) `/captures/to_a/named_captures/
names/begin/end/pre_match/post_match/size/length/to_s/inspect`;
`String#=~/match/match?/scan/sub/gsub/split`. `String#match` and friends are literally
`Regexp#match` with the arguments swapped, so they share the code path.

Two fidelity details that a plausible implementation gets wrong and the oracle caught:
a **zero-width match advances by one character** when scanning (so `"aaa".gsub(/a*/, "X")`
is `"XX"` and `"".scan(/a*/)` is `[""]`), and `split` drops **trailing** empty fields but
not leading or interior ones. `sub`/`gsub` with a backreference in the *replacement*
(`\1`, `\k<name>`) is its own sublanguage and gates rather than emitting the backslash.

**Result (measured).** tier-0 `--sut lean` **955 → 974 agree, 0 disagree** (the `Regexp`
gate was #4 on the histogram at 20 cases). The L100 regex oracle still 7,418/7,418. Two
discriminating scripts byte-identical to CRuby across the whole `Regexp`/`MatchData`
surface and the seven `String` methods. `#print axioms` unchanged on `invariant_sound`,
`Static.check_sound`, `sorbet_invariant_sound`.

## L102 — `String#to_i`, and the M4 gate

The last thing between the model and `homebrew/PLAN.md`'s **M4 gate** — "`Version.new(…)
.tokens` and `Semver.parse` match CRuby" — turned out not to be the regex engine at all but
a missing `String#to_i` (`Semver.parse` builds its record with `m[1].to_i`).

CRuby's `to_i` is lenient by design and the leniency is the specification: skip leading
whitespace, take an optional sign, then digits, and **stop at the first character that does
not fit**, with no match at all giving `0` rather than an error. `_` is a separator only
*between* digits, so it is a small scan and not a filter — `"1_0"` is 10, but `"_5"` is 0
and `"1__0"` is 1 [V]. Filtering underscores out (the obvious implementation) gets the last
two wrong.

**M4 gate met.** A transcription of the slice's tokenizer (`scan` over an interpolated,
`/i`-flagged alternation of `NUMERIC_WITH_DOTS | [a-z]+ | \d+`) and of `Semver.parse`
(anchored capture of major/minor/patch/prerelease/build, `to_i`, a nil result on a
non-match) runs in the model **byte-identical to CRuby**, including the `ALPHA`/`BETA`/`RC`
token patterns with their `{,2}` bounds.

tier-0 `--sut lean` **974 agree, 0 disagree** (unchanged by `to_i` itself — no tier-0 case
gated on it).

## L103 — retiring `reprPure`: purity is a property of the *class*, not the program

`Machine.reprPure` was a single global boolean, flipped to `false` the moment any user
`def` landed on one of `to_s`/`inspect`/`==`/`eql?`/`message`/`to_str` **anywhere**. After
that, `Repr.lean`'s pure rendering was inadmissible for every plain object in the program.
This is the blocker `homebrew/PLAN.md` W2b names: `Struct` and `T::Struct` need `inspect`
and `==`, and defining them in the prelude would have poisoned every `puts` in every
program. It is also, per the plan, ~59 unrelated tier-0 cases.

**The replacement** is `reprOverridden h sens k`: does `k`'s ancestor chain carry a
*non-builtin* definition of one of `sens`? Purity is then a per-value question, computed
from the heap, and `pureOk` recurses into containers with the elements' own classes. The
`reprPure` field, the six `if reprSensitive.contains name then …` flips in the `def` /
`define_method` / `alias` rules, and the authoring rule that kept the prelude from ever
defining `to_s` are all gone.

**Two sensitivity lists, not one — and this is load-bearing.** The first attempt used a
single list and *lost* three tier-0 cases, because it was over-strict in a way the global
flag had been accidentally right about: a user `to_s` does not change what `inspect`
prints (`Object#inspect` renders class and ivars), so `class Integer; def to_s; "x"; end`
must not make `p 1` inadmissible. `inspectSensitive = [inspect, message]` and
`toSSensitive = [to_s, message]`; `message` is in both because `Exception#inspect` is
built from it. `to_str` is in neither — it governs implicit *string conversion*, not
rendering.

**Result (measured).** tier-0 `--sut lean` **974 agree, 0 disagree** — the same as before,
which is the claim: this is a refactor of *when* the model may speak, and it neither gains
nor loses a case on a corpus whose programs mostly define nothing repr-sensitive. What it
buys is that the prelude can now define `inspect`/`==` on a class without consequence for
any other class, which is what `Struct` and `T::Struct` need.

## L104 — `private_constant`, for real

Carrying `private_constant` as a prelude no-op (the reading of `homebrew/PLAN.md` W1's
"parse and carry it") **disagreed**: `bootstraptest/test_constant_cache_005` and `006`
declare a constant private and then read it through `A::B`, expecting `const_missing`; the
model returned the value. That is the failure mode the ratchet exists to catch, so the
feature is modeled instead.

`ClassPayload` gains `privateConsts : List String`; `Module#private_constant` /
`#public_constant` are builtins that maintain it; and the `cpath` rule treats a private
name as a **miss**, so it takes the existing `const_missing`-else-`NameError` path.
Lexical lookup from inside the module is untouched, which is the whole point of the
feature. [V] CRuby distinguishes the two misses — `"private constant C::K referenced"`
rather than `"uninitialized constant C::K"` — so the rule does too.

`version.rb` declares nine private constants, so this is on the slice's critical path.
tier-0 unchanged at 974 agree, 0 disagree.

## L105 — `Struct` and `T::Struct`, in the prelude

`homebrew/PLAN.md` M6, and the payoff for L103: both classes need `inspect` (and `Struct`
needs `==`), which the old global `reprPure` flag made impossible to define anywhere in
the prelude. With purity now a per-class question they are ordinary prelude Ruby.

**Both are class factories, not core classes.** `Struct.new(:a, :b)` *returns a class*, so
the implementation is `Class.new` + `class_eval` + `define_method` — machinery the model
already had (L64/L66). That is this project's thesis made concrete: a "core class" that is
really a metaprogramming pattern costs prelude Ruby, not Lean rules.

Behaviours a plausible implementation gets wrong, each verified against CRuby:

* `Struct` with `keyword_init: nil` (the default) accepts **either** calling convention.
* `T::Struct` does **not** define `==` — two structs with equal fields are *not* equal
  [V]. Equality stays identity.
* `T::Struct#inspect` lists props **alphabetically** (`<I inc=true lower="1" n=3>`) while
  `#serialize` lists them in *declaration* order and **omits nil**.
* `T::Struct`'s prop-type error names the *non-nil* part of a nilable type ("need a
  `String`", not "need a `T.nilable(String)`").
* `abstract!` is not purely declarative: the abstract class itself cannot be instantiated
  (`RuntimeError: A is declared as abstract; it cannot be instantiated`), and
  `version/parser_spec.rb:7` tests exactly that. Subclasses can, so the generated `new`
  compares against the declaring class and otherwise allocates and initializes directly —
  rather than `super`, which from a `define_singleton_method` body would have to resolve
  through the eigenclass chain.

**Two model changes this needed.** `Class#superclass` (for inherited props), and
`X.new { … }` no longer being intercepted as an unmodeled "initialize block" when the
receiver has a **user** `self.new` — `Struct.new(:q) { … }` is exactly that shape, and the
interception was stealing the block before the user method could see it.

Also landed in this batch, all in the prelude: `Kernel#Array`, `Hash#compact`,
`NilClass#to_i`/`to_f`/`to_h`, `String#b`/`delete_prefix`/`delete_suffix`, `Array#fetch`,
and `File` restricted to its **pure path operations** (`basename`, `extname`, `dirname`,
`join`) with a `method_missing` that gates everything else by name — defining the constant
without that guard would turn `File.read` from an honest `Unsupported` into a
`NoMethodError`, which is a wrong answer rather than a refusal.

**Result (measured).** tier-0 `--sut lean` **974 → 990 agree, 0 disagree**.

## L106 — `Regexp.escape` / `.union` / `.last_match`, and `String#split` on a String

Class methods of `Regexp`, dispatched in `invoke` the way `Math.sqrt` already is: the boot
heap installs builtins as *instance* methods and these are singletons of the constant.

* `escape`/`quote` — backslash the pattern metacharacters and render control whitespace as
  its escape [V].
* `union` — `union(a, b)` and `union([a, b])` are the same call; a String member is
  escaped (it is a literal) and a Regexp member contributes its `to_s`, which is why
  `Regexp#to_s` renders `(?-mix:…)` rather than the bare source. `union()` is `/(?!)/`.
* `last_match` — `$~`, or `$~[n]`. It reads the same global the match rules write, so it
  cannot drift from `$1`. Calls the `MatchData#[]` builtin directly rather than
  re-dispatching, because `invoke`'s termination measure is `args.length` and a
  re-dispatch with the same argument would not decrease it.

`String#split` gained the **String separator**, which is a literal and therefore escaped
rather than compiled — otherwise `"a.b".split(".")` would split on every character. `" "`
is Ruby's awk-mode separator (runs of whitespace, leading whitespace ignored) and is its
own rule, and `""` splits into characters. That last one exposed a bug in the split loop:
a separator match ends the current piece at its *start* and the next begins at its *end*,
which for a zero-width separator coincide — the old code advanced by one and returned
`["a"]` for `"abc".split("")`.

## L107 — a sig with keyword parameters, and the shim's hidden alias

`__check_params` matched a sig's declared names *positionally* and gave up as soon as it
declared more names than there were positional arguments — "sig with more params than
arguments (keyword params?)". That gate accounted for **186 of the 355** Homebrew-slice
programs.

It does not need `instance_method(…).parameters`, which the model does not have: **the
call itself says which names arrived as keywords.** `__check_params_kw` walks the declared
names; a name that is a key in `**kw` is checked against that value, otherwise it consumes
the next positional argument, and a name that is neither is an optional parameter the
caller omitted — nothing to check. The wrapper's signature grows `**kw` and forwards it
(omitting it when empty, so Ruby 3 keyword separation is preserved).

**And a latent bug the gate had been hiding.** The hidden alias was `__t_unchecked_<name>`
— flat, so a subclass's alias *shadows its parent's*, and the parent wrapper's
`send(hidden, …)` dispatches back into the subclass's original body.
`Version::NullToken#initialize` (zero parameters) was receiving `Token#initialize`'s one
argument. The name is now qualified with the defining module.

## L108 — `super` from an aliased method searches for the *original* name

`alias_method :b, :a` then `super` inside `b` looks for **`a`** in the superclass [V]. The
model used the frame's `meth`, which was the name the method was invoked under, so `super`
searched for `b` and missed. The sorbet-runtime shim depends on this: it aliases a method
aside and the original body's `super` must still reach its parent — every `<=>` in
Homebrew's `Token` hierarchy is that shape.

`MethodDef` gains `superName`, set by `alias`/`alias_method` — but **only when the alias
lands on the module that defines the method**. Cross-module, CRuby resumes from the
original definition's position in the chain, which a single `defmod` cannot express when
that module has been included twice; `bootstraptest/test_yjit_145` is exactly that, so the
cross-module case keeps the old behaviour rather than a new wrong one.

Two consequences had to be untangled from the same field. `zsuper` reconstructs its
arguments from the running method's parameter list, which it found by looking `f.meth` up
in `f.defmod` — with `meth` now possibly an alias's original name, that finds a *different*
method (the wrapper), and `zsuper` reported CRuby's "implicit argument passing … from
`define_method`" error for an ordinary `def`. The frame now carries `runParams` and
`runFromDM` directly.

Also: a **user `self.new`** now wins over the `Class#new` interception. `T::Helpers#
abstract!` installs one (an abstract class must refuse to instantiate), and the
interception was allocating an instance without ever consulting it.

## L109 — `require` of an unmodeled library gates; stdlib constants gate too

`Object#require` returned `true` for everything (difftest N34). That is not a harmless
approximation: the program then runs on against constants the library would have defined,
and the first one is a `NameError` **where the control succeeded** — a disagreement rather
than a refusal. `require` now returns true only for features the prelude actually carries
(`sorbet-runtime`) and gates by name otherwise.

The same argument one level up: `URI`, `Forwardable`, `JSON`, `Date`, … are not in
`crubyToplevelConstants`, because that list is generated from a *bare* `ruby` process which
has not required them. So a reference to one raised `NameError` where the control had the
constant. `crubyStdlibConstants` is a short hand-maintained list folded into the same
unmodeled-constant check — the one part of `CRubyNames.lean` that is not generated, and
marked as such.

Also in this batch: `Float::NAN` / `Float::INFINITY` as real constants of the class object;
`Comparable#==`/`between?`/`clamp` (`==` was another casualty of the old `reprPure` flag,
and its absence was observable — Homebrew's `Version::Token` mixes in Comparable and its
specs compare a token to a String, which fell through to `Object#==` and answered false);
and the constant-miss `NameError` now qualifies with the **innermost cref**
(`uninitialized constant Homebrew::Vulns::Vulnerability::Version`, not `… Version`) [V].

**Result (measured).** tier-0 `--sut lean` **991 agree, 0 disagree**; tier-4 (Sorbet)
**14 → 25 agree, 0 disagree** — the N34 fix, which `difftest/implementation-notes.md` N34
had recorded as blocking that arm. Homebrew-slice **160 agree, 0 disagree, 192 gated**
(from 352 disagree when the corpus first ran). Regex oracle 7,418/7,418. Axioms unchanged.

## L110 — `sub`/`gsub` with a block; `Kernel#Integer`/`format`; `String#b` gates on non-ASCII

`homebrew/PLAN.md` M7's other half. `gsub(pat) { |m| … }` is what `vulns/purl.rb` and
`vulns/identify.rb` percent-encode and -decode with — 38 of the slice's programs — and a
builtin cannot serve it: it has to call back into the interpreter once per match.

So `sub`/`gsub` move into the **prelude**, and the two-argument replacement form stays a
primitive under a private name (`__sub_rep`/`__gsub_rep`) that the prelude delegates to.
The common path costs one extra send; the block path is an ordinary Ruby loop over
`match` + `pre_match`/`post_match`. It advances past a **zero-width** match by one
character, without which `"aaa".gsub(/a*/) { "X" }` does not terminate.

`Kernel#Integer(x, base)` (strict, unlike `String#to_i` — the whole string must be a
number) and `Kernel#format` (the `%d %s %x %X %o %b %%` directives with width and
zero-padding) came along with it, both in the prelude.

**`String#b` now gates on non-ASCII, and the reason is worth recording.** The model has no
encodings: a String is a sequence of *characters*. `Purl.encode` is
`component.b.gsub(/[^A-Za-z0-9\-._~:]/n) { |c| format("%%%02X", c.ord) }`, and for
`"café"` the answer must be `caf%C3%A9` — the two **UTF-8 bytes** — where a character-wise
model produces `caf%E9`. That was the last disagreement in the slice corpus. Gating is the
honest answer; making it right needs byte strings, which is a real feature and not a patch.

**Result (measured).** Homebrew-slice **160 → 210 agree, 0 disagree**, 142 gated. tier-0
unchanged at **991 agree, 0 disagree**.

## L111 — the arity/overload tail: `split` limits, `String#[]`, `chomp`, `to_f`, `try_convert`, Comparable failures

First batch of `homebrew/slice-gates.md`. Six rows, 34 gated examples, all verified against
the CRuby oracle with one probe script before a line was written.

**`String#split` with a limit, and with a capturing separator.** A positive limit caps the
field count, so the scan stops after `limit - 1` separators and the remainder is the last
field *verbatim* (`"  a  b  c ".split(" ", 2)` is `["a", "b  c "]`). `0` is "no limit, drop
trailing empties", negative is "keep them all". And a **capturing** separator contributes
its groups to the result — `"a1b".split(/(\d)/)` is `["a", "1", "b"]` — which the old
implementation silently dropped.

**`String#[]` with a non-index argument**: `s[/re/]`, `s[/re/, n]`, `s[/re/, "name"]`,
`s[/re/, :name]`. Each sets `$~` like any other match, and the capture selector reuses the
`MatchData#[]` rule rather than reimplementing name lookup. This lives in `Strings.lean`,
which can see `runSearch` because the L98 rule chain imports *forwards* (Strings →
Collections → Modules → Regex).

**`chomp(suffix)`** — and `chomp("")` strips **all** trailing newlines, not one [V].
**`String#to_f`** — the same lenient prefix parse as `to_i`, plus a fraction and an
exponent. **`Comparable#< <= > >=`** with a nil `<=>` now raise
`ArgumentError: comparison of X with Y failed` instead of gating: our gate was refusing a
case the model can answer exactly. `Y` is rendered the way coercion errors render it (value
for nil/true/false/Integer/Symbol, class name otherwise) [V].

**`String.try_convert` needed two konts, and the reason is a good one.** CRuby asks
`respond_to?(:to_str)` and only then calls `to_str`, and **both are dispatched**. Reading
the method table instead is not an optimisation, it is wrong on real code: Homebrew's
`Version` overrides `respond_to?` so that its `NULL` instance *hides* a `to_str` that would
raise, and `version_spec.rb:103` asserts `String.try_convert(Version::NULL)` is nil. The
table-reading version answered `NoMethodError`. So `strConvRespK` (decide on `respond_to?`'s
answer) and `strConvResK` (check `to_str` gave a String, else
`can't convert C to String (C#to_str gives Integer)`), with the falsy branch dropping the
result-check kont along with itself.

**Result (measured).** Homebrew-slice **217 → 238 agree, 0 disagree**; tier-0 unchanged at
**991 agree, 0 disagree**.

## L112 — `Pathname` and `URI`, restricted to their pure halves

The two biggest rows of `homebrew/slice-gates.md` (76 + 5 examples, and 81 once `URI` was
out of the way and `Pathname` became the next gate behind it).

**`URI` is one function.** `version.rb:351` calls `URI.decode_www_form_component(spec)`, and
that is the *only* `URI` use in all eight slice files. Pure string work: `+` → space, `%XX`
→ byte, `ArgumentError: invalid %-encoding (…)` on a malformed escape [V]. A `%XX` above
0x7F is a *byte* of a multi-byte character (`caf%C3%A9` is `café`), so that gates — the
byte-string limit again, not a new one.

**`Pathname` is a String wrapper.** `Version.detect` wraps its argument in `Pathname(spec)`
and asks for `to_s`, `basename`, `dirname` and `extname`; nothing in the slice touches the
filesystem through it. Modeled as exactly those, plus `to_str`/`to_path`/`sub`/`<=>`/`==`/
`inspect`, with `method_missing` gating everything else by name — the same guard `File`
uses, so `Pathname#exist?` refuses instead of answering. `Kernel#Pathname(x)` is idempotent
on a `Pathname` [V].

Both are added to `Builtins.modeledFeatures`, so `require "pathname"` / `require "uri"` are
faithful no-ops rather than L109 gates.

**One thing I got wrong, and it is worth recording as a rule.** I first put
`Pathname#stem` in the prelude too — `Version.detect` calls it. `stem` is **Homebrew's**
(`extend/pathname.rb:187`), not Ruby's, and modeling it there made the model answer
something the *control* could not: the harvested program has no Homebrew boot path, so
CRuby raised `NoMethodError: undefined method 'stem'` while the model sailed past. 79
disagreements, all of them the model being **too capable**.

The rule: the prelude models *Ruby*. Anything the target program's own environment supplies
belongs in the difftest harness's stub set, where both executors get it (N36's `blank?` is
the same case). `stem` moved to `PATHNAME_STEM_STUB`, copied verbatim from upstream.

**Result (measured).** Homebrew-slice **238 → 319 agree, 0 disagree**, 33 gated. tier-0
**991 agree, 0 disagree**; domain 200/200 at 10,000 inputs.

## L113 — `Float`/`Integer` rounding, `Forwardable`, `to_json`, and splatting a `MatchData`

Third batch off `homebrew/slice-gates.md`.

**`Float#round` is CRuby's `round_half_up`, correction and all.** Not "scale, round,
descale":

```c
f = round(x * s);                              // half away from zero
if (x > 0 && (double)((f + 0.5) / s) <= x) f += 1;
if (x < 0 && (double)((f - 0.5) / s) >= x) f -= 1;
```

That correction is why `2.675.round(2)` is **2.68** even though `2.675` is really
`2.67499999999999982…` in binary, and why `1.005.round(2)` is `1.01`. The naive version
gives `2.67` and `1.0` — it is exactly the sort of thing that looks right until an oracle
looks at it. `ndigits > 0` keeps a Float, `0` or negative yields an Integer [V]. `ceil`,
`floor`, `truncate` and `divmod` came with it, for both classes; `Integer#round(-1)` is half
**up** away from zero (`25.round(-1)` is 30).

**`Forwardable`** is `define_method` over a receiver expression — another metaprogramming
pattern rather than a library, so it is prelude Ruby and no Lean rules. The accessor may be
an ivar (`:@list`) or a method (`:inner`), which is the one thing to get right.

**`to_json`** is generation only, as a `__to_json` fold over each class. `JSON.parse`
**gates**: the slice never parses (its OSV records arrive as decoded Hashes), and a parser
we do not need is a parser we should not guess at.

**And a wrong answer, not a gate.** `pkg_version.rb` destructures a match with
`_, version, revision = *path.match(REGEX)`. `spread` had a fallthrough that wrapped any
non-Array as `[v]`, so splatting a `MatchData` bound the *MatchData* to the first target and
**nil to the rest** — and nothing downstream could tell, because a one-element spread is
perfectly well formed. CRuby splats via `MatchData#to_a`: the whole match, then every
capture, nil for one that did not participate. Fixing it needed a `spreadA` that can
allocate (the captures are fresh Strings), which is why `spread` had missed it — the pure
signature made the right answer unreachable and the wrong one silent.

**Result (measured).** Homebrew-slice **319 → 338 agree, 0 disagree**, and the gate count is
down from 135 at the baseline to **14**. tier-0 unchanged at **991 agree, 0 disagree**.

## L114 — `nonzero?` and the default `Object#<=>`

`nonzero?` returns **self** if non-zero and **nil** if zero — the idiom behind
`pkg_version.rb`'s `version_comparison.nonzero? || revision <=> other.revision`, which is
also `PLAN.md`'s headline line 202.

`Object#<=>` is `0` when the two are `==` and **nil** otherwise, and the nil is the point:
it is what lets `Comparable` degrade to "incomparable" rather than raise from the wrong
place. CRuby calls `rb_equal`, so a **user `==` participates** — a builtin cannot dispatch
one, so the rule answers from `valueEq` when nothing overrides `==` and **gates** when
something does, rather than quietly using the wrong equality. (Verified: a class with
`def ==(x) = true` makes `<=>` answer 0 for any argument.)

**Result (measured).** Homebrew-slice **338 → 339 agree, 0 disagree**, gates **14 → 13** —
and the 13 are now exactly the two structural rows of `slice-gates.md`: 10 dispatching repr
and 3 byte strings. tier-0 **991 agree, 0 disagree**.

## L115 — `try_convert` ×2, `Regexp.last_match` and `Object#<=>` move to the prelude

L111's `String.try_convert` was written in Lean as two `Kont` constructors, and that was the
wrong call — a rule whose whole difficulty is *"it has to dispatch"* is precisely a rule that
belongs in prelude Ruby, where dispatch is free. That is L62 and `AGENTS.md`'s first
load-bearing idea, and I violated both out of momentum (the adjacent `Regexp.escape` and
`Math.sqrt` singleton plumbing was right there in `invoke`).

**Removed from Lean:** the `String.try_convert` branch in `invoke`, the `Array.try_convert`
branch in `tryReflect`, the `Regexp.last_match` branch, the `Object#<=>` rule, and three
`Kont` constructors (`tryConvertK`, `strConvRespK`, `strConvResK`) with their `Machine` and
`Trace` cases. **Added to the prelude:** all four, as ordinary Ruby.

**One primitive was genuinely needed**, and stating why is the useful part.
`Object#__user_defines?(name)` answers *"does this object's dispatch chain carry a
non-builtin definition of `name`?"* — a fact about the method tables that the object language
cannot ask. It exists because CRuby's `rb_check_funcall` rule is subtler than "call it if
`respond_to?`":

* a class with a **custom `respond_to?`** is asked, and a false answer means "not
  convertible" without the method ever being called — this is why
  `String.try_convert(Version::NULL)` is nil (Homebrew's `Version` hides a `to_str` that
  would raise);
* otherwise the method is called if it is defined **or if `method_missing` can serve it** —
  so a `method_missing`-provided `to_ary` converts even though `respond_to?(:to_ary)` is
  false [V].

Both halves are observable and they *disagree*, and L111's version — which dispatched
`respond_to?` unconditionally — got the second one wrong. It answered nil where CRuby
converts. Nothing in the slice exercised it, so the ratchet never saw it; the probe written
for this move did.

**Two bugs found while doing it, both in code I had just written.**

1. The singleton-dispatch path gated on `crubySingletonShadow` **even for a successful user
   lookup**, and unlike the instance path it did not honour `fromPrelude`. So the prelude
   could not supply a class method *at all* — which is what pushed these three into `invoke`
   as special cases in the first place. One `if md.fromPrelude` fixes it, symmetric with the
   instance path's existing L62 exception.
2. `__user_defines?` first used `realClassOf`, which **skips the eigenclass**. The chain that
   matters is the one *dispatch* walks, which starts at the eigenclass:
   `bootstraptest/test_yjit_167` is `def obj.to_ary` on a single object, destructured by
   `a, b, c = obj`. Three tier-0 disagreements, caught by the ratchet immediately.

`Object#<=>` came along for the same reason: as a builtin it had to **gate** on a class with
a user `==` (L114), because CRuby calls `rb_equal`. In the prelude it is
`self == other ? 0 : nil` and the gate disappears.

**Result (measured).** tier-0 **991 agree, 0 disagree**; Homebrew-slice **339 agree, 0
disagree**, gates 13. Same numbers as before the move — which is the point: less machine, no
loss, and one latent fidelity bug removed.

## L116 — dispatching repr: the builtin defers to a prelude twin

`PLAN.md` W2b's other half, and the last non-encoding row of `homebrew/slice-gates.md`.

Pure repr (`Repr.lean`) renders a value without running Ruby. It cannot speak for a value
whose class — **or whose contents** — override `inspect`/`to_s`, because honouring that means
dispatching, and a builtin cannot push a frame. The slice's six `pkg_version_spec.rb` cases
are the recursive shape, which is the one that matters: `PkgVersion` has no `inspect` of its
own, so the *default* one renders its ivars, and one ivar is a `Version` whose class does
override `inspect`.

**The shape that works: defer to a twin under a different name.** Each repr builtin, on
finding pure repr inadmissible, dispatches `__inspect_slow` / `__to_s_slow` / `__p_slow` /
`__puts_slow` / `__print_slow` instead. The twins are prelude Ruby and recurse through
*ordinary dispatch*, which is exactly what was missing. Two primitives support them:
`__write` (append a String to stdout, no rendering) and `__addr_str` (the `0x…`, in
`Repr.fakeAddr`'s shape since the two render the same objects).

The different name is what makes it cheap. It shadows nothing, so **no purity answer
changes** and `Repr` stays the fast path for everything it can still handle; the check is
keyed on the resolved bid, so no other dispatch pays for it; and it needs no new `Kont`.
This is L63's "defer to the prelude" pattern applied to repr.

**Both alternatives I had written down fail on inspection, and it is worth saying why.**
Excluding prelude definitions from `reprOverridden` — the plan I recorded in
`slice-gates.md` — would make pure repr **lie** about `Pathname` and `T::Struct`, whose
prelude `inspect` it knows nothing about. And redefining `inspect` itself in the prelude
would make every class impure, which pushes `Obs`'s `result_repr` off a cliff: that is
computed *after* the program ends, where nothing can dispatch.

**Result (measured).** Homebrew-slice **339 → 345 agree, 0 disagree**, gates 13 → **7** (and
the 7 are byte strings and nothing else). tier-0 **991 agree, 0 disagree**.

**On the "~59 tier-0 cases" `PLAN.md` attributes to this.** They are now *unblocked*, not
fixed: the top of the tier-0 gate histogram is `Object#Rational` (25) and `Object#Complex`
(18), which were blocked because their `inspect`/`==` could not live in the prelude. They can
now — but they still have to be written. Dispatching repr was the prerequisite, not the work.
