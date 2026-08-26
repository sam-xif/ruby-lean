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

**`Array#join` was the site I first missed**, and it is the interesting one: it renders each
element with **`to_s`**, recursively through nested arrays, and `Version#major_minor` is
`[major, minor].join(".")` over `Token`s that override `to_s` — four of the slice's examples.
Adding it exposed a second bug: `pureOk` recursed into containers with a *hard-coded*
`inspectSensitive`, so an element overriding only `to_s` was judged pure and `join` gated
anyway. Purity now recurses with the **same** sensitivity it was asked about, since
`[x].inspect` uses `x.inspect` while `[x].join` uses `x.to_s`. `Range#inspect`/`#to_s` got
twins too.

**Result (measured).** Homebrew-slice **339 → 349 agree, 0 disagree**, gates 13 → **3**, and
the 3 are byte strings and nothing else. tier-0 **991 agree, 0 disagree**.

**On the "~59 tier-0 cases" `PLAN.md` attributes to this.** They are now *unblocked*, not
fixed: the top of the tier-0 gate histogram is `Object#Rational` (25) and `Object#Complex`
(18), which were blocked because their `inspect`/`==` could not live in the prelude. They can
now — but they still have to be written. Dispatching repr was the prerequisite, not the work.

## L117 — byte strings: the representation (step 1 of 2)

The last row of `homebrew/slice-gates.md`. `Purl.encode` is
`component.b.gsub(/[^A-Za-z0-9\-._~:]/n) { |c| format("%%%02X", c.ord) }` and must answer
`caf%C3%A9` for `"café"` — the two UTF-8 **bytes** — where a character-wise model answers
`caf%E9`. `Identify.decode` is the inverse and ends
`.force_encoding(component.encoding)`, so an encoding *tag* is needed, not just a byte view.

**Representation.** `Object` gains `binary : Bool := false`. When set, the invariant is that
every character of the `.str` payload is below 256 and **is** one byte. So `length`, `[]`,
`ord`, `each_char` and the matcher all operate per byte with no other change — which is
exactly what `encode` needs. A defaulted field on the *object* rather than on the payload,
because the payload constructor's arity is matched in ~40 places and an encoding is a
property of the object anyway.

**Landed (this commit).** `allocStrEnc`/`isBinaryStr`; `String#__binary?`, `#__bytes`,
`#__as_binary`, `#__as_utf8` primitives; `Integer#chr` above 127 now produces a one-byte
binary String instead of gating.

**`__as_utf8` gates on an invalid byte sequence, and that is a real limit, not a shortcut.**
A Lean `String` holds Unicode scalars, not bytes, so `"\x80".force_encoding("UTF-8")` — which
CRuby represents as a UTF-8-tagged string that happens to be invalid — has no faithful
representation here. Closing that needs the payload itself to become a byte array, which is
the ~40-site change this design was chosen to avoid. `identify_spec.rb:225` asserts
`decode("%80").bytes == [0x80]` in the same example as the `café` case, so that one example
stays gated on it.

**Still to do (step 2).** The prelude half: an `Encoding` class (`UTF_8`, `BINARY`, `name`,
`to_s`, `==`), `String#encoding`/`#force_encoding`/`#bytes`/`#b` over the four primitives
above, binary-aware `inspect` (`\xNN` for a byte ≥ 0x80 — `Repr` can read `(h.get o).binary`),
and `String#+` propagating the tag. See `homebrew/HANDOFF.md`.

**Ratchet at this commit.** tier-0 **991 agree, 0 disagree**; Homebrew-slice **349 agree, 0
disagree**, 3 gated. Unchanged — nothing yet *uses* the new primitives, which is why this is
safe to land as a step.

## L118 — byte strings: encodings, and what "nothing uses it yet" hid (L117 step 2)

The prelude half of L117 plus the observation half, which turned out to be the larger and
more interesting part. Closes **2 of the slice's last 3 gates** — `purl_spec.rb:68`
(`encode("café") == "caf%C3%A9"`) and `identify_spec.rb:219` — leaving only the `%80` row
L117 already argued is honest.

**L117 step 1 was not inert, and the first thing this commit did was find that out.**
"Nothing yet uses the new primitives, which is why this is safe to land" was wrong:
`Integer#chr` above 127 *did* use them, and `p 200.chr` answered `"È"` where CRuby answers
`"\xC8"`. A **wrong answer**, landed and green, exactly the failure mode the ratchet cannot
see — no corpus program inspects a synthesized high byte. The lesson is narrower than "test
more": a representation change is never inert once *one* rule can produce the new
representation, because `inspect` can then be reached from it. The probe that would have
caught it took four lines and was not written, because step 1 believed its own inertness
claim.

**So the design of this step is a safety net first and a feature second.** Three choke
points, in order of how much they buy:

1. **`Repr` renders the tag.** `escapeStringEnc binary` renders a byte `< 0x20` or `≥ 0x7f`
   as `\xNN` (upper case) rather than `\uNNNN`, with the named escapes (`\n`, `\e`, `\#{`)
   still winning — `(1.chr + 0xC3.chr).inspect` is `"\x01\xC3"` where UTF-8 `"\x01".inspect`
   is `"\u0001"` [V]. `inspect` reads `(h.get o).binary`, so arrays, hashes and ivars get it
   by recursion for free. A MatchData's flag records its **subject**'s encoding, since every
   String it hands back is a slice of that subject.
2. **`Repr.toS` refuses.** `to_s` hands back the *bytes*, and every consumer of the resulting
   Lean `String` — interpolation, `print`, `Array#join`, `%`, an exception message — has
   dropped the tag by construction. For a byte `≥ 0x80` that String would silently re-read
   the byte as a code point, so `toS` returns an Unsupported reason instead. One edit covers
   every one of those consumers; `putsGo`'s raw-payload fast path and `__write` repeat the
   check because they bypass `toS`.
3. **`Builtins.run` gates by allowlist.** A binary String holding a byte `≥ 0x80` reaches a
   rule only if the rule is named in `byteStrAwareBids`. This is deliberately a *list* and
   not a judgement: "does this rule handle the tag" is not a question 60-odd rules can be
   audited for once and trusted, and getting it wrong is a wrong answer rather than a gate.
   `<=>`/`<`/`include?`/`start_with?` are **excluded on purpose** — CRuby raises
   `Encoding::CompatibilityError` for a cross-encoding comparison involving a non-ASCII byte,
   and orders same-byte different-encoding strings by an internal encoding index
   (`"\xC3".b <=> "Ã"` is `-1` [V]) — so is anything that writes to stdout.

**Then the propagation, which is what makes the allowlist earn its place.** `okStrFrom m recv`
replaces `okStr m` at every String-producing rule whose bytes come from the receiver: `*`,
`[]`, `chars`, `reverse`, `upcase`, `downcase`, `strip`, `chomp`, `+@`, `-@`, `split`, `scan`,
`sub`/`gsub`, and every MatchData accessor. `dupObj` carries the tag too — it did not, so
`"café".b.dup` silently lost it.

**`+` and `<<` needed the real compatibility rule, and my first guess at it was wrong.** The
result takes the **receiver's** encoding unless *only* the argument holds a non-ASCII byte:
`"a".b + "b"` is ASCII-8BIT but `"a" + "b".b` is UTF-8, and `"".b + "café"` is UTF-8 [V]. I
had written "if either side is ASCII-only it takes the other's", which gets the both-ASCII
case backwards. Two non-ASCII operands with different tags raise
`Encoding::CompatibilityError`, a class the model does not have, so that refuses.
`<<` widens the receiver **in place** by the same rule.

**Equality had to learn the tag.** `"a".b == "a"` is true but `0xC8.chr == "È"` is **false**
[V] — the same single byte in our payload, different encodings. The check lives in
`strEqEnc`, the leaf `valueEq` and `valueEql` share, so `==`, `eql?`, `uniq`, and hash-key
matching all get it at once; `String#==` now goes through `valueEql` rather than comparing
payloads itself.

**The prelude half is the small part.** `Encoding` with `UTF_8`, `BINARY`, `ASCII_8BIT`
(`BINARY` *by identity*, matching CRuby [V]), `name`/`to_s`/`inspect`/`==`; and
`String#encoding`/`#force_encoding`/`#bytes`/`#each_byte`/`#b`, each one line over a
primitive. `force_encoding` needed **new** primitives (`__force_binary`/`__force_utf8`)
rather than L117's `__as_*`: it mutates and returns self, and retagging rewrites the payload
as well as the flag, so both have to move on the same object.

**US-ASCII is a third encoding, it is everywhere, and this commit refuses rather than guesses
about it.** CRuby gives US-ASCII to every String it *synthesizes* instead of reading from
source: `65.chr`, `1.to_s`, `:a.to_s`, `nil.to_s`, `[1,2].join`, `/a/.source`, `1.inspect`
are all US-ASCII while a literal is UTF-8 [V]. Tracking it means a third tag threaded through
~40 String-producing rules, which is a bigger job than this step and buys nothing the slice
needs. But answering `UTF-8` for all of them would be a wrong answer of exactly the kind
step 1 already made once.

So `String#encoding` answers only what the tag determines: `BINARY` for a tagged String,
`UTF_8` for one holding a non-ASCII byte (which no US-ASCII String can), and otherwise
`Encoding::UNDETERMINED` — one instance whose `name`/`to_s`/`inspect`/`==` all gate, and
which is still the right thing to hand to `force_encoding`, because re-tagging as UTF-8 or as
US-ASCII leaves the same bytes and `__force_utf8` gates on an invalid sequence in either
reading. That is what makes `Identify.decode`'s closing
`.force_encoding(component.encoding)` work while `p "abc".encoding` refuses. The residual is
recorded in `homebrew/slice-gates.md`: `equal?` against `Encoding::UTF_8` is still an
identity the model gets differently, and the fix for all of it is the third tag.

**Ratchet.** tier-0 **991 agree, 0 disagree**; Homebrew-slice **351 agree, 0 disagree, 1
gated** (was 349/3); domain-fuzz **10,000 inputs, 0 disagree**; tier-4 **25 agree, 0
disagree**; the W2a regex oracle **7,418/7,418 byte-identical, 0 fuel exhaustions**. The
gate histogram's byte-string rows are down to the single `%80` row.

## L119 — the metatheory had not compiled since L101, and now it builds in one command

`AGENTS.md` and `homebrew/PLAN.md` §9 both assert the metatheory as done and axiom-clean.
**14 of the 15 files in `RubyCore/Proof/` did not build.** Only `HeapFacts.lean` — the one file
that does not transitively import `Step.lean` — compiled. Found by following `PLAN.md` §4
norm 5 ("build the `Proof/` files at batch boundaries; a green ratchet does not mean the
proofs still work") for the first time in a while.

Three independent breaks, none of them deep, each a statement drifting away from the `stepFn`
it was written against:

1. **`Step.varGvar` vs `matchGlobal` (broken by L101, 24 commits earlier).** The constructor
   said a global read is `withCtl m (.value (m.getGlobal x))`. L101 made `$1`…`$9`, `$&`,
   `` $` `` and `$'` **views** of the last match, so `stepFn` now consults `matchGlobal`
   first — and the claim stopped being true for exactly those names. `Step.sound`'s
   `varGvar` case became unprovable, which took down `Adequacy`, `TypeSafety`
   (`invariant_sound`), `StaticSoundness` (`check_sound`), `SorbetSafety`, the T5 files and
   `RunCert` with it.
2. **`StaticSoundness` vs `reprSensitive` (broken by L103).** The `def` case still
   `by_cases`'d on `reprSensitive.contains name`, a constant L103 deleted when it retired the
   global `reprPure` flag for a per-class test. The proof was case-splitting on something that
   no longer exists.
3. **`T5Loop`'s hard-coded object id.** `def clsA : ObjId := 37` with a comment reading
   "id = `initHeap.size` = 37". `initHeap` is now **40** objects, so `clsA` pointed at an
   existing boot object and `dispatch_step`'s `rfl` could not close.

**The fixes, and why they are the honest ones rather than the quick ones.**

For (1) the cheap repair is to narrow `varGvar` with a side condition and move on. That
silently shrinks what `Step` *claims*: the relation would stop modelling `$1` reads, and
`Step.complete` — which is stated relative to a fragment predicate — would still typecheck
while covering less. So the hypothesis is the semantic one `stepFn` actually branches on
(`matchGlobal m x = none`), **and** `Adequacy`'s `FragExpr` now excludes those names
syntactically (`| .var .gvar x => ¬ isMatchView x`), with
`matchGlobal_eq_none_of_not_view` bridging the two. Completeness therefore still holds *and*
the fragment's boundary is written down where the reader can see it — the same treatment
`Step.lean` already gives send, rescue and class definitions.

The part that keeps it from happening again: **`isMatchView` is factored out of `matchGlobal`
itself**, so the proof and the interpreter test the same definition. A predicate duplicated
in the proof would drift exactly as the original claim did.

For (3), `clsA` is now `Boot.initHeap.objs.size` — computed, not written down. The boot heap
will grow again.

For (2) the dead case split is simply gone, and `int_bin_dispatch` (`BuiltinConformance`)
gained the hypothesis it had been assuming silently: L116 put a repr-twin deferral in front of
every builtin, and arithmetic never triggers it, but the *statement* has to say so. The three
instantiations discharge it with `simp [Builtins.reprDefer?]`.

**Axiom-clean, verified rather than asserted.** `invariant_sound`, `invariant_sound_from`,
`Static.check_sound`, `Step.sound`/`complete`/`deterministic`/`adequacy` and
`T5Loop.t5_loop_type_safe` each depend on `propext`, `Classical.choice`, `Quot.sound` and
nothing else — no `sorryAx`, no project-local axiom.

**The root cause was process, so the fix is a target and a script.** `Proof/` is off
`defaultTargets` for a good reason (it is slow and the SUT does not depend on it) and that is
precisely why it rotted. Added:

* a `Metatheory` lean_lib globbing `RubyCore.Proof.+`, so `lake build Metatheory` builds all
  15 files at once — it did not exist, and checking the metatheory previously meant knowing
  to build 15 modules by hand;
* `scripts/check-proofs.sh`, which does that *and* re-runs `#print axioms`, exiting non-zero
  on a failure or a `sorryAx`. One command, so norm 5 is cheap enough to actually obey.

*A method note, since it cost real time.* My first attempt at checking these ran
`timeout 3000 lake env lean <file>` in a loop — and macOS has no `timeout`, so every
invocation failed to launch, the `grep -c` counted zero errors from empty output, and I
briefly believed all 15 files were green. `lake build +RubyCore.Proof.X` is the command that
actually reports.

## L120 — six wrong answers in `split`, `gsub`, `index` and `Symbol`, found by the W4b heads

The model fixes forced by `difftest`'s new tier-1 generation heads (N39, which is the story of
the heads; this is the story of the bugs). All six were **wrong answers**, not gates: the
corpora had been green for weeks over code that answered incorrectly on inputs no corpus
generated. Each fix follows the same discipline — a `show(label) { … }` probe diffed against
CRuby *first*, then the implementation. The probes are worth reproducing when touching any of
this; they encode rules that are not guessable.

**1. `split` never returns `nil`.** An unmatched capture group in a separator contributes
*nothing* — it is not a `nil` element that trailing-trim removes later. `"a1b".split(/(\d)(x)?/)`
and `"a1b".split(/(x)?(\d)/)` are both `["a", "1", "b"]` [V], with the unmatched group in the
middle and at the front respectively. The old code pushed `nil`, which surfaced as
`["", "1", "2", nil]` for `Version`'s own `^(\d+)\.(\d+)(?:\.(\d+))?$`.

**2. The zero-width skip rule is "at the current field start", not "at offset 0".** A separator
match that is empty *and* begins where the previous match ended is not a separator:
`"aab".split(/a*/)` is `["", "b"]`, not `["", "", "b"]` [V] — the empty match at offset 2 is
skipped. Offset 0 is just that rule's special case at the front of the string, and testing for
it was the whole of the old rule.

**3. A positive limit counts *effective* separators.** `maxHits` pre-truncated the hit list to
`lim - 1`, which charged the budget for matches rule 2 then skipped: `"abc".split(//, 2)`
answered `["abc"]` instead of `["a", "bc"]`. The count moved inside the fold, which is also
where `cur` lives — the two rules are entangled and cannot be applied in separate passes.

**4. An empty subject splits to `[]`** whatever the pattern and the limit, `-1` included [V].

**5. The prelude's block-form `sub`/`gsub` re-anchored the pattern.** It looped over a
progressively shortened `rest`, so `\A` and `^` matched at *each remainder's* start:
`"12".gsub(/\A\d/) { "X" }` answered `"XX"` where CRuby answers `"X2"`. Rewritten over absolute
offsets into `self` via a new `String#__search_at(re, pos)` primitive — faithful precisely
because the engine's anchors are absolute (`Rx.Match`'s `.bos` is `pos == 0`), so a search from
`pos` does *not* re-anchor. Two things fall out for free: `$~` is now set per iteration, so a
block can read `$1`; and its spans are relative to the whole string.

This is the L110 design being wrong rather than incomplete, and it had been green since L110
because no corpus program `gsub`s with an anchored pattern.

**6. The backref globals had no owner.** `scan`, `sub` and `gsub` must leave `$~` at their
**last** match (nil when there were none), while `split` with a **Regexp** *clears* it and
`split` with a String leaves the previous match alone [V]. `Regexp#match`/`String#[]` were the
only rules maintaining `$~` at all, so after a `gsub` the program saw a stale match — the
quietest possible wrong answer. `setLastMatch` is the shared helper; it re-derives the group
*names* from the pattern, since `allMatches` drops them and `$~.names` would otherwise come
back empty.

**7. `String#index` with a Regexp raised.** `"abab".index(/b/)` was a `NoMethodError` on
`Regexp#length` where CRuby answers `1`. One line over `__search_at`, which also gets `$~`
right. `rindex` with a Regexp **gates**: a backward scan for the *last* match is its own
algorithm and approximating it would be a wrong answer of exactly the kind this entry is about.

**8. `Symbol` had `include Comparable` and no `<=>`.** So `:k < :v` raised
`ArgumentError: comparison of Symbol with :v failed` where CRuby answers `true` — the `include`
had been inert since it was written, and worse than inert. Symbol ordering is String ordering
of the names, and only Symbol compares to Symbol (`:k <=> 1` and `:k <=> "k"` are both nil [V]).
Four lines of prelude. `[:a, :b].sort` still **gates**, because `Array#sort`'s `SortKey` covers
numerics and strings only — a gate, and left alone.

**One regression of my own, caught by re-running the L118 probes.** The prelude's `gsub` now
calls `__search_at`, which was not in `byteStrAwareBids` — so L118's byte-string safety net
refused `Purl.encode("café")`, the very case L118 exists to answer. The net working as designed;
the allowlist just needed the new primitive. Worth knowing that L118's net will do this to every
future primitive that touches a String, which is the intended cost.

**Ratchet.** tier-0 **991 agree, 0 disagree** (byte-identical to before); Homebrew-slice **351
agree, 0 disagree, 1 gated**; domain-fuzz **10,000 inputs, 0 disagree**; tier-4 **25 agree, 0
disagree**; tier 1 at n=250 × 3 seeds and tier 1.5 at n=200 × 3 seeds **0 disagree**; the W2a
regex oracle **7,418/7,418**.

**Recorded, not fixed: `$~` is frame-local in CRuby and a plain global here.** A match inside
any method leaks to its caller — a wrong answer, unreached by every corpus. `homebrew/slice-gates.md`
carries it at the top of the known-gaps list, with the design tension that makes it more than a
one-liner: a `$~` frame slot would stop a *prelude-implemented* `sub`/`gsub` from setting its
**caller's** `$~`, which CRuby's C versions do.

## L121 — `$~` is frame-local, and the prelude's C-function stand-ins write their caller's slot

The first of the two wrong answers `homebrew/HANDOFF.md` left open, and the design tension it
warned about is real: the obvious fix breaks something else, so this is two mechanisms rather
than one.

**The defect.** CRuby keeps the last match in the **frame**. A callee's match is therefore
invisible to its caller, while a block shares its defining method's frame and so is visible.
The model kept `$~` in `m.globals`, where every match was visible everywhere:

```ruby
def inner = "zz".match(/z/)
"ab".match(/a/); inner; $~[0]   # CRuby "a"   model "z"  (before this entry)
```

**Storage.** `Frame.lastMatch : Value`, routed inside `Machine.getGlobal`/`setGlobal` rather
than at each read site. That choice buys three things: `matchGlobal` (the `$1`…`$9`/`` $` ``/`$'`
views, L101) reads `$~` through `getGlobal` and so needs no change; a user's `$~ = md` works;
and `Proof/Step.varGvar`'s statement — "a gvar read is a plain `getGlobal`" — stays *true*, so
the metatheory needed only one repair (`setGlobal_heap` is now two cases, not `rfl`, because one
branch writes `frames`).

**Which frame.** `Machine.matchFrameId`, three cases:

* a **block** resolves through `captured` — *lexically*. This is observable and the stack cannot
  answer it: a proc built in one method and `call`ed from another writes the frame it was
  **defined** in, so the calling method sees nothing [V]. When the defining frame is still on
  the stack, resolution continues from there, which is what keeps L120's "a block passed to
  `gsub` can read `$1`" working;
* a **match-transparent** activation resolves to the frame below it on the stack;
* everything else owns its slot.

**The tension, and the second mechanism.** `String#sub`/`#gsub`/`#index` and
`Regexp.last_match` are prelude *Ruby* (L110/L115) where CRuby has *C*, and a C function writes
its **caller's** backref. Under frame-local storage alone, the prelude `gsub` would have set
`$~` in its own frame and the caller would have seen nothing — trading one wrong answer for
another, quietly. `HANDOFF.md` proposed a `__set_caller_match` primitive called at the end of
those methods; what landed instead is a **marker at the top**: `__match_to_caller` sets
`Frame.matchXparent`, and every later read *and* write in that body resolves to the caller.

Three reasons the marker beat the write-through primitive, all found by trying the latter first:

1. `sub`/`gsub` have several exits (`return __sub_rep(...)` before the block path, the loop's
   `break`, the trailing re-search); a write-through call has to be on all of them.
2. It only fixes *writes*. `Regexp.last_match` **reads** `$~` and would have kept reading its
   own always-empty slot.
3. The builtins the prelude methods call (`__search_at`, `__sub_rep`, `__gsub_rep`) push no
   frame, so with the marker they write the caller's slot *by construction* — exactly the C
   behavior — instead of writing the prelude frame and needing a second copy.

A marker *call* rather than a Lean-side list of transparent method ids because a reader of
`gsub` has to be able to see it: transparency is the one property of the method not derivable
from its body. It is on `byteStrAwareBids` (L118) since it reads neither receiver nor argument —
without that, `"\xC8".b.gsub(...)` would have gated on the marker.

**`defined?($~)` came along.** It is `"global-variable"` **always**, match or not — unlike its
views, where `defined?($1)` with no match is nil [V]. The old code answered from `globals` and
happened to agree only because any match attempt put the key there; frame storage has no such
key, so the rule is now written down.

**The witness came first** (N40's `regex_scope_probe`), and it was red on ten lines per probe
before any of this — a callee's match overwriting the caller's, and `$1` nil where CRuby had the
caller's group. No corpus had reached it: the W4b heads put every match at toplevel, which is
the one place where one storage location and CRuby's per-frame one are indistinguishable.

## L122 — `Range.new` validates its endpoints, and two more defects that were hiding behind it

The second of `HANDOFF.md`'s two known wrong answers — `Range.new(1, "a")` built a range where
CRuby raises `ArgumentError: bad value for range`. It is small, as advertised. What it was
*covering* was not: writing a head to witness it turned up two further wrong answers in the same
few lines, neither previously suspected.

**1. The validation.** CRuby's `range_init` requires `lo <=> hi` to answer non-nil when both
ends are present. Probed, because none of it is guessable: only *non-nil* is required (an
endpoint whose `<=>` answers `"junk"` builds a range quite happily — the check is not "is this
an Integer"); a beginless or endless range skips the check entirely, so `(nil..nil)` is legal;
`<=>` is dispatched on the **left** endpoint, so `Range.new(D.new, 1)` succeeds where
`Range.new(1, D.new)` raises for a `D` answering 0; and a `<=>` that raises propagates.

It is prelude Ruby over a `__range_new_unchecked` primitive — the L115 shape, because the check
*dispatches*. Two things then fell out for free: the arity error comes out of the Ruby signature
(`Range.new(1)` → `wrong number of arguments (given 1, expected 2..3)` [V]), and
`Range.new(1, 2, 3)` is now exclusive rather than gated, since the primitive takes its third
argument by truthiness [V]. Ranges are also frozen now, literal and constructed alike [V].

**2. `inspect` of an endless range printed the nil.** `(1..nil).inspect` answered `"1..nil"`
where CRuby prints `"1.."`, and `(nil..2)` answered `"nil..2"` for `"..2"` — *except* that
`(nil..nil)` really is `"nil..nil"` [V]. `to_s` needs no case at all: `nil.to_s` is `""`, so
`(nil..nil).to_s` is `".."` and always was right. Fixed in both twins (`Repr.lean` and the
prelude's `__inspect_slow`), which is the L116 obligation — a rule in one twin only is a rule
that applies until the value stops being pure.

**3. `pureOk` did not recurse into a Range's endpoints.** So a range over an object with a user
`inspect` was judged pure, rendered by the Lean fast path, and printed the endpoint's default
`#<C:0x…>` — ignoring the override. `.arr`, `.hsh` and an object's ivars all recursed; `.range`
fell through to `| _ => own`. A Range is a container of two, and now says so.

Defect 3 is the same *kind* of miss as the eigenclass gap still on the known-gaps list, and it
was found the same way defect 2 was: by giving the head's endpoint class a fixed `inspect` so
its observations would carry no address (N38's rule), and then noticing that the model ignored
it. A head written to be process-independent found a bug *because* of that constraint.

## L123 — the numeric operators run the `coerce` protocol, and four wrong answers behind it

`HANDOFF.md`'s one open wrong answer: `0 + obj` never called a `method_missing`-supplied
`coerce`. The handoff's statement of the problem was right and its estimate of the size was
not — the snippet it gave is one corner of a rule the model did not implement **at all**.

**What CRuby does.** `Integer#+` is `rb_num_coerce_bin`: it asks the *argument* to `coerce`
itself and re-dispatches the operator on the pair that comes back. `numBin` instead decided
"not a number" from the class chain and raised. So an ordinary `def coerce` — not just a
`method_missing` one — was wrong too: `3 + Money.new(4)` raised `TypeError` where CRuby answers
`7`. A probe of 65 shapes against CRuby 4.0.5 put the count at **34 wrong answers in one file**,
and two more probe files took it to 57.

The three wrappers differ and all three are observable, which is why the prelude has three
entry points rather than one:

| wrapper | nothing answered | answered nil | wrong shape | answered a pair |
|---|---|---|---|---|
| `rb_num_coerce_bin` (`+ - * / % ** divmod`) | `TypeError: X can't be coerced into Integer` | `TypeError: coerce must return [x, y]` | same | re-dispatch |
| `rb_num_coerce_relop` (`< > <= >=`) | `ArgumentError: comparison of Integer with X failed` | same ArgumentError | **`TypeError: coerce must return [x, y]`** | re-dispatch, and a nil answer is the ArgumentError |
| `rb_num_coerce_cmp` (`<=>`) | `nil` | `nil` | **the same TypeError** | re-dispatch, nil and all |

The wrong-shape row is the one nobody would guess: the *forgiving* wrappers raise for it. [V]

**Shape of the fix.** A builtin cannot dispatch, so the failure path defers to a prelude twin —
L116's mechanism, generalized: `reprDefer?` and the new `coerceDefer?` are now both consulted
through one `deferTwin?`, which is also the single hypothesis `int_bin_dispatch` carries.
Deferral is keyed on "could a `coerce` possibly run" (`mayCoerce`), so two Integers, and every
argument whose class chain offers nothing, keep the Lean fast path and the Lean message.

Two decisions inside `mayCoerce` are deliberate and neither is obvious:

* a **prelude** `coerce` counts (a future `Rational` will have a real one) but a **prelude**
  `method_missing` does not — the only one is `Pathname`'s, which exists to *refuse*, so routing
  through it would turn today's correct `TypeError` into a gate;
* `==` is excluded from the protocol entirely. It does not coerce: `num_equal` hands the
  comparison to the argument (`rb_equal(y, x)`) and reduces the answer to a boolean, so
  `0 == obj` is decided by a user `==` and a returned `5` means `true` [V] — a wrong answer of
  its own, fixed by an `__eq_reverse` twin. It fires only for a **non-prelude** `==`: reversing
  into `Comparable#==` recurses (it calls `<=>`, whose default calls `==`) where CRuby's
  paired-recursion guard answers `false`, and `Pathname`/`Struct` answer `false` for a numeric
  argument anyway — so for those the model's existing `false` is already CRuby's answer, and
  the reversal would buy a fuel-exhaustion gate.

`__coercible?` is `rb_check_funcall`'s callability rule, one step past L115's. The step is a
`respond_to?` that answers **true** over a method nobody supplies: CRuby calls the default
`method_missing`, rescues the `NoMethodError` and reports "not callable" — so `0 + Yes.new`
is `TypeError: Yes can't be coerced into Integer`, not a NoMethodError [V]. A user
`respond_to_missing?` vetoes the `method_missing` route the same way. `__check_convert` (L115)
could not be reused: it folds "nothing answered" and "answered nil" into one `nil`, and
`do_coerce` raises differently for those two.

**Three more wrong answers, all found by probing around the fix.**

1. **`Comparable#clamp` had no `min <=> max` check** and compared with `<`/`>` instead of `<=>`.
   Latent before this work (`3.clamp(9, 1)` answered `9` where CRuby raises `min argument must
   be less than or equal to max argument`); *visible* the moment `<` started coercing, since
   `3.clamp(coercible, 9)` then coerced its way to a `true` and **returned the argument**. This
   is the L117 lesson again — a change is inert only until some other rule can reach it. It also
   had two definitions in `Comparable`, the second silently winning, and the dead one was the
   one with the Range gate; there is now one, over `*bounds` so that the Range form still gates
   rather than being read as "no upper bound", and a nil bound means unbounded on that side [V].
2. **`comparison of X with Y failed` was a second copy of the operand-naming rule**, written in
   Ruby in `Comparable.__desc`, and it rendered a Float argument as `"Float"` where CRuby shows
   `1.5`. It now goes through `__cmp_failed` → `coerceDesc`, one rule; `coerceDesc` was itself
   missing the Float case, which `numBin` could never reach because a Float argument coerces.
3. **`**` and `divmod` gated on a non-numeric argument** where CRuby raises the coercion
   `TypeError`. A gate, not a wrong answer — but it hid the *others*: a program containing
   `n ** obj` refuses as a whole, so the L123 head could not have witnessed any of this until
   `**` stopped gating. That is worth keeping: **a gate anywhere in a program hides a wrong
   answer everywhere in it**, so a head is only a witness in a model that gates nowhere else in
   the same draw.

`coerceFailed` exists so the operators that skip `numBin` cannot drift from it, and
`__coerce_failed`/`__cmp_failed` are primitives for the same reason — the message rule
(`coerceDesc`: a special constant by value, everything else by class) stays written once, which
is exactly what defect 2 above is the cost of not doing.

Guards: six hand-filed `coerce-*.rb` cases in `difftest/corpus/regressions/` (143 observed lines
between them) and the `coerce_probe` generation head (N42). The campaign-filed
`tier1.5-00930-minimized` — the case the handoff pinned — now agrees and its sidecar is flipped
to `fixed`.

## L124 — how a message names a class, in one place: anonymous classes, eigenclasses, and `rb_any_to_s`

`HANDOFF.md`'s second known wrong answer: an anonymous class (`Class.new`) is named `""` in
every message, so `0 + Class.new.new` said `TypeError:  can't be coerced into Integer` for
CRuby's `#<Class:0x…> can't be coerced into Integer`. The handoff called it "one Lean function,
not a protocol". That was right about the *shape* and wrong about the *size*, in the direction
the last three sessions have all been wrong in: probing the neighbourhood turned one wrong answer
into **five rules** — ~48 wrong answers counted by observed probe shape — in four groups,
of which only the first is about anonymous classes at all.

**1. `className`'s fallback (≈19 wrong answers).** `Heap.className` answered `c.name`, which is
`""` for a class with no constant bound to it. CRuby's `rb_class_name` renders such a class by
address, and *every* message built from a class name inherits that: the coercion `TypeError`, the
`comparison of X with Y failed` ArgumentError, `NoMethodError`, `FrozenError`, `uninitialized
constant C::X`, `superclass must be an instance of Class (given an instance of …)`, an
`Exception.new` with no message, `no implicit conversion of X into String`, and the default
`inspect`/`to_s` of an *instance* of one (`#<#<Class:0x…>:0x…>`, which was rendering as
`#<:0x…>`). The fallback therefore belongs in `className`, not at ~20 call sites, and
`fakeAddr` moved from `Repr.lean` down into `Heap.lean` so it can live there. `Repr.inspect`/
`Repr.toS` had a private copy of the same rule for their `.cls` branch; both now call `className`,
because a second copy of a message rule is L123 defect 2 all over again. `Module#name` still
answers `nil`: it tests `c.name.isEmpty` itself and does not go through `className`.

**2. The eigenclass's own name (12 more, and *not* an anonymous-class defect).**
`eigenclassOf` named the new class `#<Class:{className o}>`, and `className` answers `"Object"`
for a non-class id — so **every** singleton class of a plain object was named `#<Class:Object>`,
including for named classes: `Foo.new.singleton_class.to_s` answered `"#<Class:Object>"` for
CRuby's `"#<Class:#<Foo:0x…>>"`. CRuby names an eigenclass after the object it is attached to by
`rb_any_to_s`, which is now `Heap.anyToS`: `#<RealClass:0x…>`, **ignoring** any user
`to_s`/`inspect` and any ivars [V] — so it stays a pure heap function, which is what lets a
builtin use it. A class's metaclass keeps the `#<Class:Foo>` form, and it composes:
`Foo.singleton_class.singleton_class` is `#<Class:#<Class:Foo>>` [V].

**3. `classOf` where CRuby uses `rb_obj_class` (5 + 6 wrong answers).** With eigenclasses
correctly named, a second family became visible immediately — nine message sites read
`className h (classOf h v)`, and `classOf` returns the **eigenclass** when one exists. So
`def o.hi; end; 0 + o` said `#<Class:#<Foo:0x…>> can't be coerced` (and, before group 2,
`#<Class:Object> can't be coerced`) where CRuby says `Foo`. `coerceName`, `coerceDesc`, the
FrozenError, the three `superclass must be…` sites, `Class.new`'s, and the uncaught-exception
observation in `Obs`/`PreludeBoot`/`Search.Random` all take `realClassOf` now. This is the
argument for fixing a family rather than a case: five wrong answers that no probe of *anonymous
classes* would ever have reached were sitting one rule away, and they were invisible while every
eigenclass was misnamed the same way.

The one place CRuby *does* look at the eigenclass is `NoMethodError`'s receiver: when a singleton
class exists, the receiver is rendered by `rb_any_to_s` instead of `an instance of C` —
`def o.hi; end; o.zz` is `undefined method 'zz' for #<Foo:0x…>` [V]. The test is only "does a
singleton class exist", so `extend`, a bare `o.singleton_class` and a `def o.x` all trigger it,
and it ignores a user `inspect` (probed: six shapes, including a `String` and an `Array`
receiver). A *class* receiver keeps `for class Foo` even with singleton methods of its own.
`receiverDesc` also named an anonymous class receiver `for class ` with nothing after it.

**4. Four prelude messages used `.class.name` (4 wrong answers).** `Array.try_convert`'s
`can't convert X to Array (X#to_ary gives Y)`, `String.try_convert`'s twin, `Enumerable#to_h`'s
`wrong element type`, and the `__inspect_slow`/`__to_s_slow` twins. For an anonymous class
`Module#name` is `nil`, so `"…" + obj.class.name` raised `TypeError: no implicit conversion of
nil into String` — a *different* error, which is how the `to_ary` case first showed up. Ruby's
equivalent of `rb_class_name` is `Module#to_s`, and that is what these say now. Left alone
deliberately: `Struct#inspect`'s `self.class.name`, where the nil *is* the rule
(`#<struct a=1>` for an anonymous struct [V]), and the sorbet-runtime shim, which models
sorbet's own code rather than CRuby's.

**What is still open, and why it is not cheap.** The model fixes an eigenclass's name at
creation; CRuby computes it on demand. So for an anonymous class named *after* an instance's
eigenclass already exists, the two diverge — `k = Class.new; o = k.new; o.singleton_class;
K = k; o.singleton_class.to_s` is `#<Class:#<K:0x…>>` in CRuby and keeps the address form here.
Closing it means storing the *attached object* on the class payload and making `className`
recursive (fuel-bounded, since Lean cannot see that an attachment chain is finite) — a heap-shape
change and a reducibility risk on the dispatch path, for a shape this narrow. Pinned as an `open`
case instead (N43).

**Metatheory: one repair, caught by `check-proofs.sh` in one command** — the fourth session in a
row that number has been exactly one. `clsName_defineMethod` carried
`(classPayload? k).map (·.name)`, which no longer determines `className`: the fallback reads
`isModule` too. It now maps the pair. (§4 norm 5.)

Guards: `anon-*.rb` and `eigen-*.rb` in `difftest/corpus/regressions/`, which is where the
corpus rule this defect could not satisfy got solved — CRuby's own answer carries an address, so
the case asserts a **predicate over** the message rather than the message (N43).

## L125 — the model side of parse-time block scoping, and the `define_method` gate that fell with it

The Lean half of C35 (the desugarer half, and the defect itself, are recorded there —
`homebrew/HANDOFF.md`'s first known wrong answer: a Proc body's assignment wrote an outer
local Ruby had already made block-local, at parse time). Three changes, all small, because
the front end now supplies what the model could not compute.

**1. The decoder merges the new slot.** `[:block, params, locals, declared, body]` decodes to
the same `Expr.block` as before, with `locals ++ declared`. The two lists are *used*
identically — `callClosure` seeds both as nil in the block frame (`Interp/Support.lean`), and
that seeding is exactly what makes an assignment resolve in the block's own frame instead of
walking the `captured` chain. Keeping one list in Lean means no change to `Expr`, `Closure`,
`PendingBlk`, the `Proof/` tree or the concolic shadow store. The v4 four-slot shape still
decodes, so an AST exported before this change is not rejected.

The two lists differ only for `defined?`, and `defined?` never consults the frame: it reads
the *node shape* (L72 — a name the parser did not know to be a local arrives as a vcall, not
a `var local`), which is precisely CRuby's static rule. Verified both ways, since it is the
one place this could have gone wrong: `defined?(z)` before the textual assignment in a block
is nil, after it is `"local-variable"`, and `z = 1 if false; defined?(z)` is
`"local-variable"` with no assignment ever executed [V].

**2. `MethodDef.declared`, and the gate it retires.** `define_method`'s block becomes a method
body that *keeps its captured frame*, so a block-local there needs the same treatment one
frame kind over — otherwise an assignment walks out of the method and clobbers a same-named
outer local. The model had gated on it (`define_method with block-locals`), which was safe
while only explicit `|;x|` reached it and untenable once *every* local assignment in a
`define_method` block did. `enterUserMethod` already pre-declares the formals bound after
defaults, for this exact reason (L64); `md.declared` joins them, and the gate is gone. So the
change *closes* a gate rather than opening one: `Dm.define_method(:go) { x = 5; x }` runs now,
and `define_method` with an explicit `|;x|` runs for the first time.

**3. Nothing else.** No `getLocal`/`setLocal` change: pre-seeded nil slots already give both
the read and the write the right frame. That was worth checking rather than assuming — a read
diverges too (`f = -> { p a; a = 1 }; a = 7; f.call` prints nil in CRuby, and would have
printed 7), and the seeding covers it.

**Measured.** 48 scoping shapes probed against CRuby (listed in C35), all agreeing; two
pre-existing defects confirmed pre-existing on the stashed build rather than explained away —
`_1` (a wrong answer: the model answers nil where CRuby binds the argument, now in
`homebrew/HANDOFF.md`) and `case/in` (a gate). Full ratchet re-run: this change touches every
block in every program, which is the widest blast radius of the session.

## L126 — the stepper trace gets a window, because 825,259 steps do not fit in one

The playground (`ruby/playground/`) steps the model one `stepFn` transition at a time, over a
`--trace` mode that emits every configuration as JSON. It had **kept up with the model without
anyone maintaining it** — it is a *printer* over `stepFn`, not a second implementation, so
classes, `super`, yielding builtins, the prelude, regex and the reflective core all step
correctly today even though the playground's own README still described the July fragment.

What it had not kept up with is *scale*. Asked to step the linked Homebrew slice
(`homebrew/slice-driver/`, 2,151 lines), it showed the first 4,000 steps — all of them class
definitions — because the trace is a flat array from step 0 and the cap is 4,000. Measured:
the slice is **825,259 steps**, a snapshot is ~1 KB rendered, and a whole-program trace at
200,000 steps was **1.1 GB**.

Three additions, all in `Trace.lean` + `Main.lean`, none touching the observation path:

* **`--steps`** — run to termination emitting nothing, report the count and how it ended. The
  number a window is chosen against, and cheap: 825,259 steps in 0.34s, because the cost of a
  trace is the snapshots, not the stepping.
* **`--trace-from N`** — skip `N` steps, then emit the window.
* **`--trace-at SUBSTR`** — skip to the first step whose *rendered control* contains `SUBSTR`,
  then emit the window. This is the one that matters on a real program, where the step index of
  the thing you care about is not knowable in advance: `--trace-at "send .compare("` lands on
  the slice's first `Semver.compare` at step **50,765**, sixteen frames deep, with `a`/`b`
  bound in the top frame.

Matching the **rendering** rather than the machine is deliberate. `Trace` is a tooling view and
says so — lossy, non-gating, not the Ruby-faithful `Obs` the difftest reads — and a breakpoint
that reads the same text the user reads cannot disagree with what they are looking at. The
alternative (a structural predicate over `Ctl`) is a second thing to keep in step with `Ctl`'s
constructors, for a facility whose whole point is the string.

The window carries **`first_step`**, the absolute index of `steps[0]`. Without it two windows of
the same program render identically and both look like the beginning. A breakpoint that never
fires is not an error: zero steps, and a status saying how the program ended instead.

`playground/server.py` passes both flags through (`POST /trace` now also accepts
`{"source", "at", "from"}`; `POST /steps` is new), and `index.html` gains the two inputs, a
**count steps** button, and absolute step numbers. The old bare-source `POST /trace` still
works.

## L127 — the sorbet-runtime shim's type errors describe the value the way the gem does

The shim (L80) really does enforce: `sig` aliases the method aside and installs a wrapper that
checks every declared parameter and the return value, `T.let`/`cast`/`assert_type!`/`bind` check,
`T.must` rejects nil, `T.unsafe` is the one form that does not, generics are erased exactly as the
gem erases them, and `checked(:never)` skips the wrapper. That much was already true and is
difftested against the real gem by tier 4.

What was *not* right is how a failing check **describes the offending value**. Probed against
sorbet-runtime 0.6.13405 (`types/types/base.rb#describe_obj`), which has three rules and the shim
had none of them:

| the gem | the shim, before |
|---|---|
| `nil`/`true`/`false` print **no value clause** ("redundant to print class and value") | `…got type NilClass with value nil` |
| a value whose `inspect` is the **default** prints `with hash <obj.hash>` | `…with value #<Named:0x…>` |
| everything else prints `with value <inspect truncated to 27 + "..." + 30>` | untruncated |

plus the class named by `to_s` and not `name`, so an anonymous class raised
`TypeError: no implicit conversion of nil into String` from inside the error path instead of
naming `#<Class:0x…>`. That is the L124 rule one file over: I left the shim's `.class.name` alone
last session on the theory that it models sorbet's own code — and sorbet's own code interpolates
the class, which is `to_s`. **Reading the gem beats reasoning about the gem.**

Four wrong answers, then, all in the shim's message rule, all invisible to tier 4 because its 28
probes happen to violate sigs with Strings and Integers, whose `inspect` is neither default nor
long.

**The hash rule becomes a gate, not an answer.** `Object#hash` is per-process seeded — no
implementation has a stable answer, which is exactly N38's rule and why three tier-0 cases are
`control_invalid`. So a type error naming a default-`inspect` object now *refuses*
(`__unsupported__`) rather than inventing a number. It used to answer, wrongly. A gate here costs
the whole program, which is the price of not being able to produce the value at all.

**`__default_inspect?`** is a new primitive because the gem's test —
`obj.method(:inspect).owner == Kernel` — has no Ruby-level equivalent here (no `Method#owner`).
`__user_defines?` is the wrong question: it answers "is there a non-builtin definition", so an
`Array`, whose `inspect` is a builtin of its own rather than Kernel's, would come back as
"default" and the gem says otherwise. The primitive asks the method table for the owner directly.

Two traps inside the fix, both caught by the probe rather than by thought:

* `value == true` **dispatches `==` on the value**, so `T.let((1..2), Integer)` gated with
  `unmodeled builtin would shadow: Range#==`. The gem's `case obj when nil, true, false`
  dispatches on the *literal*. `value.equal?(true)` is exact and dispatch-free.
* `string_truncate_middle` slices with a range literal, and *that* is what turned up C37 — the
  prelude defines `T::Range`, so a range literal inside `module T` resolved the shim's own
  constant. The shim could not have been written this way before the desugarer was fixed.

The `T::Struct` prop message is a **different** rule and was checked separately: plain `inspect`,
no truncation, no hash substitution, addresses and all (the engine normalizes those) — only the
`.class.name` → `.class.to_s` half applies there.

Measured: 12 of 16 value shapes byte-identical to the gem, the other four the honest hash gate
(three objects and a `Proc`, whose `inspect` carries a source location the model cannot produce
either). tier-4 25/0 unchanged.

## L128 — pure repr asks the chain *dispatch* would walk, so a singleton `inspect` is visible

`pureOk` decides whether Lean's pure `Repr` may speak for a value, by asking `reprOverridden`
whether anything in the value's ancestor chain defines a repr-sensitive method. It asked with
`(h.get o).klass` — the **real** class — so a method defined on the *object* was invisible to it
and the pure path rendered the default `#<C:0x…>` while ignoring the override:

```ruby
o = Plain.new
def o.inspect = "SING"
p o          # CRuby  SING      model  #<Plain:0x…>
[o].inspect  # CRuby  "[SING]"  model  "[#<Plain:0x…>]"
```

The fix is one argument — `classOf h (.ref o)`, which starts at the eigenclass — and it is the
same miss `__user_defines?` had before **L115**, in the same function's other caller. Six wrong
answers in `difftest/corpus/regressions/pureok-eigenclass.rb`, in `p`, inside an Array, a Hash, a
Range, as an ivar of another object, and through `o.extend(M)`; the `to_s`-through-interpolation
control stays green because that was always an ordinary send. The second arm of `pureOk` (the
immediates) now says `classOf` too — for a value with no eigenclass slot the two are equal by
definition, so this is a no-op that keeps the arms from drifting.

The prelude twins needed **no** change: they were already dispatching, which is the whole point of
deferring to them, and the fix only widens *when* the deferral happens.

**The fix trades two wrong answers for two gates, both at `inspectP` call sites**, and this is
worth stating rather than discovering later. `inspectP`/`toSP` refuse when pure repr cannot speak,
and refusing is what they now do more often:

* `frozenErr` renders the receiver into `can't modify frozen Plain: <inspect>`. CRuby dispatches
  `inspect` there; the model gated already for a *class-level* override and now gates for a
  singleton one too, where before it answered `#<Plain:0x…>` — wrongly.
* `Obs.observe`'s `result_repr` is the same shape one layer out, and it is the architectural
  version of the problem: the final value is inspected **after the program has ended**, where
  nothing can dispatch, so `p o` at toplevel (which returns `o`) gates on the observation even
  though its stdout is now right.

Both were wrong answers before and are gates now, which is the direction the project's norms want
(§4.4), but they are new coverage holes: pinned as `difftest/corpus/regressions/impure-repr-gates.rb`
so the choice is visible and revisitable. Fixing them properly means letting the observation
*dispatch* — a synthetic `inspect` send on a machine that has already halted — which is a change
to the observation contract, not to a rule, and is not attempted here.

Measured: tier-0 991/0, slice 351/0 + 1 gated, tier-4 25/0, regressions 26 held + 1
unexpectedly-fixed (this defect) — every fixed-corpus number unmoved.

## L129 — a renderer never lets a non-String out: `rb_obj_as_string` / `rb_inspect` as one rule

`HANDOFF.md`'s first known wrong answer. Every C-level renderer in CRuby goes through one of two
functions, and neither can produce a non-String:

* **`rb_obj_as_string(obj)`** — a String is used verbatim (so a redefined `String#to_s` is *not*
  called), otherwise `to_s` is called, and **if the result is not a String the default
  `#<C:0x…>` form of the receiver is used** (`rb_any_to_s`).
* **`rb_inspect(obj)`** — `inspect`, and then `rb_obj_as_string` of **the result**. So `p Bar.new`
  for a `Bar#inspect` that answers `1` prints `1` [V]: it is the *result* that is coerced, not the
  receiver.

The model had the first two steps of the first function and none of the third, in two places: the
desugaring of interpolation (C30) and the prelude twins that render for `p`/`puts`/`print`/`join`
and the container `inspect`s. Eight wrong answers plus two gates in
`difftest/corpus/regressions/tos-not-a-string.rb`; the visible symptom was usually a `TypeError`
several steps downstream, because the non-String escaped into the enclosing concatenation.

**One rule, one definition.** `Object#__as_string` and `Object#__as_inspect` in the prelude are
the two C functions, and every twin renders through them instead of through a bare
`to_s`/`inspect`. The desugarer's cold arm calls the first one (C38 — which also explains why the
round-trip harness now carries a plain-Ruby twin of it), so there is no second inline copy to
drift.

**`Object#__any_to_s` is the one new primitive**, and it is a primitive for the reason
`Heap.anyToS` already gives: `rb_any_to_s` names the class through `rb_obj_class` +
`rb_class2name`, so it **dispatches nothing**. `"#{Foo.new}"` with a bad `Foo#to_s` *and* a
`def Foo.to_s` is still `#<Foo:0x…>` [V], which the obvious prelude spelling
(`"#<" + self.class.to_s + ":" + __addr_str + ">"`) gets wrong — and that spelling was what
`Object#__to_s_slow` and `__inspect_slow` were already using, so both now route through the
primitive too.

Note it is **not** `Heap.anyToS`, despite the previous handoff's claim that they are the same
function. That one is the *eigenclass-naming* rule, where a class argument is named by its path
(`#<Class:Foo>`); here a class is just an object of class `Class`, so `"#{Foo}"` with a bad
`Foo.to_s` is `#<Class:0x…>` [V]. Two rules that agree on plain objects and disagree on classes,
which is exactly the kind of thing a probe finds and a reading does not.

An **immediate** gates: CRuby prints the immediate's own VALUE (`#<Integer:0x…b>` for `5`, i.e.
`2n+1`), and reproducing that encoding — so that the observation's occurrence-order address
normalization stays honest — is not worth it for a program that has redefined `Integer#to_s` to
return a non-String.

**Two pre-existing defects found by probing the fix**, neither about a bad `to_s`:

* `Array#to_s` and `Hash#to_s` **are** `inspect` (`rb_ary_to_s` *is* `rb_ary_inspect`), so they
  render their contents with `inspect` and their purity test is *inspect*-sensitivity.
  `reprDefer?` asked the `to_s` list, so `{ a: BadInspect.new }.to_s` was judged pure, the Lean
  `Repr` ran, and `Repr` is the thing that cannot render an impure element — a **gate** on a
  program CRuby answers. `Range#to_s` is deliberately not moved: it really does use its
  endpoints' `to_s` [V].
* `Array#join`'s separator goes through `StringValue` (`to_str`), **not** `to_s`, so a String
  separator is used verbatim. `__join_slow` called `to_s` on it, and
  `class String; def to_s = 1; end; ["a","b"].join("-")` raised `TypeError: no implicit
  conversion of Integer into String` where CRuby answers `"a-b"`. It now uses the separator
  verbatim and gates on a non-String one, matching the pure `joinImpl`.

Measured: 29/29 shapes in the probe file identical, tos-not-a-string.rb identical (now a guard,
extended with the `puts`/`print` lines it had to omit while the defect was open, and with the two
above). Desugar corpus seeds 43/43 and bootstraptest 1227/0 — the support-layer injection
perturbs no reflective test. tier-0 991/0, slice 351/0, tier-4 25/0.

## L130 — `Kernel#Integer` is two rules wearing one name (and `Kernel#Float` is a third)

`HANDOFF.md`'s second known wrong answer, which its own entry undersold. The prelude's
`Integer` was `arg.to_s.strip`, then a digit loop — the happy path of the *String* rule, applied
to every argument. `rb_convert_to_integer` is two rules:

* **the argument is a String** (or answers `to_str`) → parse it, and this is the only argument a
  base may accompany;
* **anything else** → *convert* it: `to_int`, then `to_i`, and only if neither answers an Integer
  raise `TypeError: can't convert X into Integer`.

So `Integer(obj)` on an object with a `to_i` **answered 5** where the model raised, `Integer(2.9)`
is **2** where it raised, and every other non-String got `ArgumentError: invalid value for
Integer()` — CRuby's message for an unparseable String — instead of a `TypeError`.

The two failure messages differ and both are load-bearing [V]: a **missing** conversion is
`can't convert Plain into Integer` (with the argument named literally for nil/true/false and by
class otherwise — `Integer(:sym)` says "Symbol", the `coerceName` rule one file over), while a
`to_i` that answers a non-Integer is `can't convert C to Integer (C#to_i gives String)` — `to`,
not `into`. A `to_int` that answers a non-Integer is simply **ignored**, and `to_i` decides.

**The String half was wrong too, in three ways nobody had looked at**, because the default base
is **0** and not 10 — 0 means "read the prefix":

| | CRuby | model, before |
|---|---|---|
| `Integer("0xff")` | 255 | ArgumentError |
| `Integer("010")` | **8** | 10 |
| `Integer("1_000")` | 1000 | ArgumentError |

`__parse_int` is `rb_int_parse_cstr`: strip, sign, prefix (base 0 reads it; an explicit base
accepts only its own, so `Integer("0xff", 10)` is an error), then digits with **single** `_`
separators, never leading or trailing. `invalid radix N` for base 1 or > 36.

**`Kernel#Float` landed in the same pass** — it used to gate entirely (`unmodeled method
Object#Float`) — and it is *not* the same rule three times. Three differences, each verified
rather than assumed: it does **not** consult `to_str` (an object with only a `to_str` raises
`TypeError`), it takes no base, and its String grammar is **looser than a Ruby float literal** —
`".5"` is 0.5 and `"5."` is 5.0, both syntax errors as literals. Hexadecimal float strings
(`"0x1p3"` is 8.0) are a second grammar with their own rounding and refuse rather than answer.

**`exception:` is a real keyword parameter** on both, not a gate: without one the keyword arrives
as a positional Hash (Ruby 3's rule for a method that declares no keywords) and is read as the
*base*, so `Integer("zz", exception: false)` would answer wrongly rather than refuse.

NaN and Infinity refuse: they raise `FloatDomainError`, which is not a boot class here.
`Float#to_i`/`round`/`floor`/`truncate` already gate on them for the same reason, so this is one
coverage hole and not a new one — adding the class would close five shapes and is worth doing.

**Two more pre-existing defects, both found by the probe and neither about `Integer`:**

* **`__check_convert` did not consult a custom `respond_to_missing?`.** CRuby's
  `check_funcall_missing` tests it (with `include_private = true`) before entering
  `method_missing`, and deliberately only when the program has overridden it —
  `rb_method_basic_definition_p`, which is why the [V] fact in that helper's comment (a
  `method_missing`-provided `to_ary` converts *without* a `respond_to_missing?`) and this one are
  both true. Missing the clause made `Integer(obj)` on an object whose `method_missing` serves
  `to_int` raise from the **`to_str`** probe that runs first.
* **`String#to_f` answered `0.0` for a leading dot.** `parseFloatPrefix` bailed when the integer
  part was empty; `strtod` does not, so `".5".to_f` is 0.5 and `"-.5".to_f` is -0.5. Only "no
  digits anywhere" is the no-match case.

**`Object#respond_to_missing?` is a new builtin** — the default one, answering `false`, which
exists so a user override can call `super`. That is the idiomatic way to write one and it failed
with `super: no superclass method 'respond_to_missing?'`. A builtin and not a prelude `def`,
because `__user_defines?` cannot tell a prelude definition from a program's, and both rules that
consult this name (`__check_convert`, and `respond_to?`'s gate in `Interp/Reflect.lean`) mean "did
the *program* write one".

`super` inside a user **`method_missing`** is the same shape and is *not* fixed here: it needs
`BasicObject#method_missing` to exist as the builtin that raises `NoMethodError`, which would put
the model's whole dispatch-miss path through a method table entry. Pinned rather than attempted.

Measured: 36 of 38 probe shapes identical (the two are the `FloatDomainError` gate), the pinned
case a guard at 46 shapes. tier-0 991/0, slice 351/0, tier-4 25/0.

## L131 — everything an exception says goes through `to_s`, and the model had it backwards twice

Found by probing L128's fix, which is the third session running where the neighbourhood of a
named defect held more than the name did. CRuby has one rule here and the model had two wrong
halves of it:

* **`Exception#message` *is* `to_s`** (`exc_message` is one `rb_funcall`), and `rb_exc_inspect` is
  `#<Class: rb_obj_as_string(exc)>`. So a user `to_s` decides all three answers. As a Lean builtin
  sharing `to_s`'s arm, `message` read the payload: `E.new("boom").message` answered `"boom"` for a
  class whose `to_s` says `"OVER"`, and so did `inspect`. **Two wrong answers.**
* **A user `message` changes nothing** about `to_s` or `inspect` — but `message` was in
  `inspectSensitive` *and* `toSSensitive`, so the model **refused four shapes CRuby answers**
  (`inspect`, `p`, in an Array, through interpolation).

The lists were standing in for a sensitivity that is not expressible as a list entry: `to_s` is
repr-sensitive **for an exception value** and not for anything else. So it moved into `pureOk`'s
`.exc` arm, where it also covers an exception inside an Array, a Hash or an ivar, and `message`
left both lists. `Exception#message` is prelude Ruby (`def message = to_s`) — the only spelling
that dispatches — and `Exception#inspect` joins `reprDefer?`'s deferring bids with an
`Exception#__inspect_slow` twin that reproduces `rb_exc_inspect`, including its bare-class-name
answer for an empty message [V].

`message` does not coerce, either: a `to_s` answering `1` makes `message` answer **1** [V], which
falls out of L129's rule rather than needing one here.

**The uncaught-exception observation is a third instance of one architectural hole.** The control
observes `__exc.message`, which *dispatches*; `Obs.observe` read the `.exc` payload. The program
has ended, so nothing can dispatch — the same position `result_repr` is in. It now **refuses**
rather than answering the payload, which is a wrong answer traded for a gate, pinned as the third
entry in `impure-repr-gates.rb`.

**The mistake inside that fix is the one worth reading.** The first version asked
`reprOverridden ["to_s", "message"]` — and `reprOverridden` deliberately counts the **prelude's
own** definitions, because otherwise pure repr would lie about `Pathname` and `T::Struct`. The
prelude now defines `Exception#message`. So the gate was `true` for *every* exception and fired on
a plain `TypeError`: **three ratchet cases went from `held` to `gated`** in one run. The
observation needs the opposite question, and it is now a separate helper — `programOverridden`,
`fromPrelude`-excluding, the same distinction `mayCoerce` and `hasProgramEq` already draw. A
prelude definition is an *implementation* of a builtin, not an override; which of the two questions
a call site means has to be decided at the call site.

Measured: `exception-repr.rb` (30 shapes, red before and green after) held; regressions 30 held /
2 still_open / 3 gated with no case changing state; tier-0 991/0, slice 351/0, tier-4 25/0.

## L132 — `Integer#inspect` is `to_s`, base argument and all

Found by a tier-1 draw, and the reason it had never been drawn before is worth the sentence:
`[0, 0, 0].each_with_index(&:inspect)` hands the symbol proc **two** arguments, so it calls
`0.inspect(0)`. `Integer#inspect` *is* `int_to_s` in CRuby, so that answers
`ArgumentError: invalid radix 0`. The model had `Integer#inspect` in `zeroArgBids` — an arity error
— and `Integer#to_s(base)` was not implemented at all, so even the well-formed call gated.

**Confirmed pre-existing** by building the pre-session commit in a worktree, which is the norm and
which mattered here: a defect reached through `inspect` in a session that spent its length changing
repr looks exactly like a regression.

Writing the rule turned up four more shapes, none of them about the base itself [V]:

| | CRuby |
|---|---|
| `42.to_s(16.5)` | `"2a"` — the base goes through `NUM2LONG`, which **truncates** a Float |
| `42.to_s(Float::NAN)` | `RangeError: float NaN out of range of integer`, not a TypeError |
| `42.to_s(nil)` | `no implicit conversion from nil to integer` — lowercase, and different prepositions from every other operand |
| `255.inspect(16, 2)` | `wrong number of arguments (given 2, expected 0..1)` |

`intToBase` is fuel-bounded on the magnitude rather than `termination_by` (L73), and its digits are
**computed** (`baseDigit`) rather than indexed out of a string, so nothing on the path can panic or
block kernel reduction.

Probe 17/17 plus 5/5 on the error shapes.

### The other tier-1 finding, which is *not* fixed: implicit `to_ary`

The same round drew `a += C0.new()` for a `C0` whose `method_missing` serves `to_ary`. CRuby
converts through `rb_check_array_type`, so the `method_missing` **runs** — the program's own trace
records it — and a non-Array answer gets `can't convert C0 to Array (C0#to_ary gives String)`. The
model raises `no implicit conversion of C0 into Array` from a builtin that dispatched nothing, and
the side effect is lost.

Pre-existing (same worktree check), pinned as `tier1.5-01643-minimized.rb`, and left open on
purpose: this is exactly the shape L123 solved for `coerce` and L130 for `to_int`/`to_i`, so the
*rule* is known and the **site list** is the work — `Array#+`, `concat`, `Array()`, splat, `puts`,
massign. It should be the next session's first item, because every one of those sites is a silent
wrong answer today.

## L133 — implicit `to_ary` dispatches, and the site list really was the work

L132's closing section said the rule was known and the site list was the work. Both halves were
right, and the second half was bigger than the list it named: **four** of the six sites it listed
turned out to be answerable, one was already correct, one gates — and probing the fix found
**three more sites and two more rules** the list did not mention.

**The rule.** Every implicit Array conversion in CRuby is `rb_check_array_type`, which is
`rb_check_funcall(:to_ary)`. It **dispatches**, so three things a payload test cannot produce are
observable [V]:

* the `to_ary` body **runs** — including one a `method_missing` serves — and whatever it printed,
  printed;
* an Array answer is *used*: `[1] + Pair.new` is `[1, 7, 8]`, not a `TypeError`;
* a non-Array answer names the method — `can't convert C to Array (C#to_ary gives String)`, with
  **`to`**, against the `into` of the nothing-answered case.

The model's Array builtins tested the payload and raised `no implicit conversion of C into Array`
without calling anything: a wrong message *and* a lost side effect, at every site at once.

**The shape of the fix is L123's**, third time of asking (L123 `coerce`, L130 `to_int`/`to_i`): a
builtin that would have to dispatch defers to a prelude twin, keyed on "could a `to_ary` possibly
run", so two real Arrays never leave the Lean fast path. `toAryDefer?` joins `reprDefer?` and
`coerceDefer?` under the one `deferTwin?` hook — which is what `BuiltinConformance.lean`'s `simp`
set had to learn, and `check-proofs.sh` said so in one command.

| site | before | after |
|---|---|---|
| `Array#+`, `Array#concat` | wrong message, no dispatch | twin over `__to_array_type` |
| `Array#flatten` | element left unconverted — a **wrong answer** with no error at all | twin, keyed on `anyToAryDeep` over the receiver |
| `Array#join` | same, and **not on L132's list** — found by probing | twin, same key |
| `Kernel#Array` | prelude, but `respond_to?`-based: missed a `method_missing`'s `to_ary` and *used* a non-Array answer | `__check_array_type` then `to_a`, both `rb_check_funcall` |
| `Kernel#puts` | gated since L66 | the gate is **retired** — `toAryDefer?` routes to `__puts_slow` |
| massign (`a, b = obj`) | already correct | untouched — the desugarer lowers it to `Array.try_convert(x) \|\| [x]` |
| splat (`*obj`) | wrong answer for a `method_missing`-served `to_a` | **gate** |
| a block's auto-splat (`\|x, y\|`) | wrong answer — object to `x`, nil to `y` | **gate** |

The last two are honest refusals rather than fixes, and are pinned as `to-ary-gates.rb` so they
stay visible. Neither `spread` nor `callClosure` is a builtin, so neither has a twin to defer to:
closing them needs a way to run a send *in the middle of argument binding*, which is the same
machinery the observation wants (`homebrew/HANDOFF.md` §Known wrong answers 4). `Array#-`/`&`/`|`
convert too and were deliberately left alone: they gate on a non-Array argument today, and a gate
is not a wrong answer.

### The two rules found by probing the fix

**A `to_ary` that answers `nil` is a mismatch, not an absence.** `[1] + NilAry.new` raises
`can't convert NilAry to Array (NilAry#to_ary gives NilClass)`, and the first draft raised
`no implicit conversion` instead. The cause is that `rb_check_convert_type_with_id` (the *check*
form, behind `Array.try_convert` and `Kernel#Array`) short-circuits on a nil result, while
`rb_convert_type_with_id` (the *raising* form, behind `Array#+`) type-checks whatever
`rb_check_funcall` returned — so only `Qundef`, "not callable", produces `no implicit conversion`.
`__check_convert` collapsed those two into one `nil`, exactly as its own comment warned the
`coerce` path about (L123 kept `__coercible?` separate for this reason and I did not read why).
The repair is `__conv_callable?`, split out of `__check_convert` and now shared by both — the same
refactor `__coercible?` should eventually fold into.

**`Array#join` asks `rb_check_array_type` what "nested" means.** `ary_join_one` recurses into a
nested Array, and "nested" is the conversion, not `is_a?(Array)` — so `[Pair.new].join(",")` is
`"7,8"`. `__join_collect` tried `to_s` first, which is the wrong order: `to_ary` is asked before
anything renders.

**Probe: 40 shapes, then 51 more in the neighbourhood.** The first found 20 disagreements and left
5, all of them refusals. The second — written against the functions the *fix* introduced, per the
handoff's rule — found the two rules above plus three pre-existing gates worth naming: `Array.new`
with an Array argument, `flatten(n)`, and a recursive array (CRuby raises
`ArgumentError: tried to flatten recursive array` where `flattenAll` runs out of fuel and gates).
It ended at 48/51, the three being those gates.

**Two pinned defects came off the list**, and only one of them was the one being fixed:
`tier1.5-01643-minimized.rb` (the `Array#+` shape L132 filed) and `tier1-00950-minimized.rb`, which
had been `open`-but-`gated` since N41 on the `puts` refusal this note retires. Both sidecars are
flipped to `fixed`; the answering sites are guarded by the new `to-ary-dispatch.rb`.

## L134 — `NUM2LONG` over a subscript, and the 23 programs R1 lost to it

R1's first run (`difftest/implementation-notes.md` N46) came back **82 agree, 0 disagree, 24
gated**. 23 of the 24 gates were two rules — `Array#[] non-int index` (17) and
`unmodeled method Integer#[]` (6) — and both arrive the same way: `Array(hash)` yields
`[[k, v], …]` and Homebrew's code then indexes it with `"type"`. `nontrivial-target.md` §3.3 had
already named both from a hand-written probe; R1 measured what they cost.

They were **refusals where CRuby has a family of messages**, which is the shape §Criterion-1's
table calls "our own gate is wrong here". Closing them took one helper, `numIndex`, shared by
`Array#[]`, `Array#[]=`, `String#[]` and a new `Integer#[]`.

| subscript | CRuby |
|---|---|
| Integer | itself |
| finite Float | **truncates toward zero** — `[10,20,30][1.7]` is `20` |
| `Float::NAN` | `RangeError: float NaN out of range of integer` |
| nil | `no implicit conversion from nil to integer` … **or** `of nil into Integer` |
| String / Symbol / true | `no implicit conversion of X into Integer` |

**The nil row is two rows, and getting it wrong is a wrong answer rather than a gate.** The array
and string subscript paths are `rb_num2long`, which special-cases nil with lowercase wording and
different prepositions — the same oddity L132 found in `Integer#to_s`. `Integer#[]` is
`rb_to_int`, which says the ordinary thing. So `[1,2][nil]` and `5[nil]` raise *differently*, and
`numMsg` is a parameter rather than a constant because the first draft made them agree and was
wrong about one of them.

`Integer#[]` is `rb_int_bit_ref`: bit `i` of the **two's-complement** representation, so a negative
receiver sign-extends (`(-5)[1]` is `1`) and a negative index is `0`. `Int.fdiv`/`fmod`, not
`/`/`%`: Lean's `Int` division truncates toward zero, which gets every negative receiver wrong. An
index above 4096 answers the sign bit directly, which also keeps `2 ^ i` from being computed for an
astronomical `i`.

### Three arms still gate, and two of them are the interesting part

* **A subscript that could dispatch.** `rb_ary_aref1` tries `rb_range_beg_len` **before**
  `NUM2LONG`, so a non-Integer subscript is asked for `begin`/`end`/`exclude_end?` first and only
  then for `to_int` — `A[obj_whose_method_missing_answers_1]` is `[]`, not `A[1]`. That is four
  possible dispatches for one subscript, so `mayDispatchIndex` asks about all four and gates. It
  gated before too; nothing here turns an answer into a refusal.
* **A Float outside `long`.** The `RangeError` renders the float with `%g` — `1e+30`, where
  `Float#to_s` gives `1.0e+30`. The first draft answered with `rubyFloatRepr` and was wrong by two
  characters; a second float formatter for one message is worse than refusing, so it gates and says
  so. `NaN` is exact and is answered.
* **`Integer#[]`'s bit-field forms** (`255[0, 4]`, `255[0..3]`, both `15`). A Range argument had to
  be intercepted *before* `numIndex`, or it would answer `TypeError` where CRuby answers a number.

**Probe: 32 shapes, 2 → 23 agreeing, and the 9 that remain are all refusals.** Two of the three
gates above were found because the first build of this rule turned them into wrong answers — which
is the fourth session running where the neighbourhood worth probing was the rule just written.

**Result: R1 goes 82/24 → 106 agree, 0 disagree, 0 gated**, and tier-0 991 → 992.

## L135 — F0: the invariant at the prelude-booted heap, and the certificate that gets it there

`homebrew/PLAN.md` D6/D7 and `homebrew/widening-the-fragment.md` §3/§4. The static route's first
rung, and the one that could have closed the route in a session. It does not: **the heap half of
`Inv` holds at the prelude-booted heap**, measured, and there are now two theorems that reach it.

`Proof/StaticSoundness.check_sound` is stated over `Machine.init p`, whose heap is `Boot.initHeap`
— no core library. `static-soundness-poc.md` §5 says such a theorem "says nothing", and
`sound_from` was written so the prelude-booted start would be *an instance rather than a
restatement*. Nobody had produced the instance. `Proof/PreludeInv.lean` produces it.

**What has to survive phase 1 is only two of `Inv`'s four conjuncts, and that is the whole
structural point.** `FramesOk` and `CtlOk` at phase 2's start are re-established from scratch:
`initWithPrelude` builds a *fresh* toplevel frame (`Machine.initOn`) and carries over `heap` and
`globals` only, neither of which `FramesOk` reads. So `initiation` generalizes to `initiation_on`
— any heap satisfying `HeapOk := TableOk ∧ NoHook`, any globals — by changing nothing but the
statement. `CtlOk` moreover *cannot* hold during phase 1 (the prelude is 3,259 lines of what
`Types/Fragment.lean` excludes by design), which is why F0 is heap-half preservation and not
"run the invariant through the boot".

### The measurement first, because it is what decides D6

`scripts/heapok_probe.lean` boots the prelude and asks the four clauses directly. All four hold:
`+`, `-`, `*` each resolve on `Integer` to the tabulated builtin, `undefined = false`,
`visibility = .pub`, `fromPrelude = false`, `crubyShadow = none`; and `Object` has no
`method_added`, because the prelude installs that hook **lazily** from `T.__toplevel_sig` and a
sig-free program never evaluates one. Worth recording: `Integer`'s booted ancestor chain is
`[Integer, Numeric, Comparable, Object, Kernel, BasicObject]`, so the prelude *does* splice a
module into it — the shadow clause survives that because `Comparable` defines no `+`.

### Two routes, and why both are in the file

`HeapOk` is decidable — two `lookup`s and a `crubyShadow` on a fixed heap. What is unavailable is
deciding it *in the kernel*: `Prelude.program` is `Lean.Json.parse Prelude.json`, and
`Lean.Json.parse` does not kernel-reduce even on the input `"1"` (measured; it is
`WellFounded.fix`-shaped, the trap D1 and L73 already banned on the dispatch path and nobody had
asked of the prelude carrier), while L94 bans the `native_decide` escape.

* **The certificate route** (`inv_of_cert`, `check_sound_withPrelude`). `heapOkB : Heap → Bool`,
  with `heapOkB_sound : heapOkB h = true → HeapOk h`. The theorem's hypothesis is then *one Bool
  about the machine actually in hand*, decided by running it. No `ofReduceBool` appears anywhere:
  the Bool is a hypothesis, not a proof step, so the axiom baseline is unchanged.
* **The preservation route** (`heapOk_boot`, `check_sound_withPrelude'`). `run_heapOk` carries the
  heap half along a whole `run` given a **per-step** obligation `PreservesHeapOk`, re-basing the
  hypothesis at each step through `Reaches.head` so it never has to be strengthened to *all*
  machines — which would be false, since a program may reopen `Integer`. Nothing is checked at
  runtime; the residue is `PreservesHeapOk` over the machines phase 1 reaches, left as an
  **explicit hypothesis rather than an `axiom`**, per D8's rule that a trusted assumption must be
  an artifact and not a residue.

`PreservesHeapOk` admits `.done` alongside `.next`, which is what lets `run_heapOk` avoid inverting
`stepFn`: the boot's last step is `applyKont` on an empty continuation stack (`Interp/Kont.lean:20`,
the only `.done` in the interpreter), and proving *that* is the only `.done` producer would mean
walking all 47 `Kont` cases to show none of the others is one. Admitting it costs one disjunct in a
definition; the alternative cost a case analysis.

### `heapOkB` lives outside `Proof/`, deliberately

`RubyCore/HeapCert.lean`, imported by `RubyCore.lean`. Defining it next to the soundness lemma
would put it off the default build target, where the probe cannot see it — so the probe would
re-implement the predicate and could drift from the one the theorem is about. One definition, two
readers, and `scripts/check-proofs.sh` now runs the probe as a third section and fails on it.

It is **not** wired into `Prelude.boot`. A prelude that redefined `Integer#+` would be a legitimate
model change that breaks the static route only; refusing to *execute* would be the wrong response,
and the check belongs where the proofs are checked. Nothing the SUT reads changed in this note.

### What remains, and its size

`PreservesHeapOk` has to be discharged at every heap-writing site the interpreter has, and there
are **seventeen**: `Interp.lean:238,279`, `Interp/Dispatch.lean:173,509,526,540,571,572`,
`Interp/Kont.lean:103,490`, `Interp/Reflect.lean:87,193,200,310,317,359`,
`Builtins/Modules.lean:183`. One of them is already proved — `TableOk_defineMethod`, lifted here to
`heapOk_defineMethod` with the hook clause attached. The `setClassPayload` sites are the ones to
cost carefully: `include`/`prepend` change `ancestors`, so name-disjointness (`HeapFacts.lean`'s
route) is not enough on its own and the side condition becomes "the spliced module defines none of
the protected names".

## L136 — splitting `StaticSoundness.lean` before F1 touches it

`PLAN.md` §4 norm 3 and W6's standing instruction ("`StaticSoundness.lean` is 968 lines — split
before extending"). It had reached **971**, against a 1,000-line ceiling, with F1 about to add a
`KontOk` constructor and a consecution case per continuation — 11 of them for the class/const
rung alone.

The cut follows the file's own section numbering, so it is a move and not a redesign:

| file | was | lines |
|---|---|---|
| `Proof/Static/Locals.lean` | §1–§1.4 — `valueTy?`, `FrameConforms`, `FramesOk`, the array/local-access algebra, the environment lemmas | 320 |
| `Proof/Static/Konts.lean` | §2 — `KontOk`, `CtlOk`, `TableOk`, `NoHook`, `Inv`, the inversions, the `Inv` builders | 249 |
| `Proof/Static/Preservation.lean` | §3 — `step_ok`, the one case analysis | 295 |
| `Proof/StaticSoundness.lean` | §4–§6 — `consecution`, `safety`, `initiation`, `check_sound`, the worked examples, the axiom audit | 184 |

**The file kept its name deliberately.** `check_sound` is what everything downstream imports —
`Proof/PreludeInv.lean`, `check-proofs.sh`, and the AGENTS/PLAN prose that names it — so renaming
it would have made a mechanical split look like a semantic one in every diff that mentions it.

No statement changed and no proof changed; `check-proofs.sh` is green and axiom-clean, which for a
split is the whole test. One thing to know if you split another proof file this way: the
`set_option maxRecDepth 100000` at the top of the original is load-bearing in **all three** parts,
not just the one containing `tableOk_initHeap` — the boot-heap `rfl`s are elaborated wherever the
lemma is *used*, so each part carries it.

## L137 — the typing judgement becomes heap-relative, which is F1's prerequisite

`homebrew/widening-the-fragment.md` §6 rung **F1**, and `PLAN.md` W5 **T2**. Nothing about the
*type language* changed and no program's verdict moved; what changed is that every judgement in
`Proof/Static/` is now indexed by a `Heap`.

**Why it has to come first, as its own commit.** A nominal class type — `T.instance C`,
`T.class_of C`, `Sub` as the `ancestors` walk — cannot be a predicate on a `Value` alone: a
`Value.ref o` says nothing about what class `o` belongs to, and `classOf`/`className`/`ancestors`
all live in the heap. So `valueTy?` has to take a heap before `Ty` can grow an arm that reads one.
Doing the threading while every arm is still heap-*independent* is what makes the two changes
separable: this one is verifiable by `check-proofs.sh` alone, because if the threading were wrong
the existing proof would not close.

    valueTy? : Value → Option Ty              ⇒   valueTy? : Heap → Value → Option Ty
    FrameConforms Γ f                          ⇒   FrameConforms h Γ f
    FramesOk frames fids Γs                    ⇒   FramesOk h frames fids Γs
    KontOk Γs τ k                              ⇒   KontOk h Γs τ k
    CtlOk / Inv                                    unchanged in shape (they already had `m`)

**`KontOk` carries the heap for exactly one constructor, and that is the interesting part.**
`argsK` stores an already-evaluated **receiver** and a `ValueTy` fact about it, so a continuation
on the stack holds a claim about the heap. Every other constructor is heap-independent and the
index just rides through. That single case is what makes the transport lemmas necessary.

### `TypeAgree`, and why it is phrased over `classOf` rather than over the method table

The cost of the threading is that every heap-writing step now owes a *transport*: the `ValueTy`
facts already stored in frames and continuations must still hold in the new heap.
`Locals.lean` §1.5 states the condition as

    TypeAgree h h' := (∀ v, classOf h' v = classOf h v) ∧ (∀ k, className h' k = className h k)
                        ∧ (∀ k, (h'.classPayload? k).isSome = (h.classPayload? k).isSome)

— i.e. **exactly what a nominal `Ty` will read**, not what today's four ground types read (which is
nothing). `ValueTy.congr`, `FrameConforms.congr`, `FramesOk.heap_congr` and `KontOk.heap_congr`
transport across it, and `typeAgree_defineMethod` is the instance, assembled from
`HeapFacts.lean`'s `classOf_defineMethod`/`className_defineMethod`/`shape_defineMethod`.

**This is the part that is not inert** (L117/L118's rule: "this change is inert" is a claim to
test). The `def` case of `step_ok` really does now go through `FramesOk.heap_congr` and
`KontOk.heap_congr` rather than reusing `hfs`/`hk` directly — `hres` grew a fourth hypothesis for
it — and the reason to want that today is that it puts F1's real cost where it can be read:
`defineMethod` satisfies `TypeAgree`, and **`Heap.alloc` and an `includes` splice will not**. A
class definition allocates and a `include` rewrites the ancestor chain, so F1's `classDefK` and
`includeK` cases will have to establish a *weaker* agreement (new ids only, chain extended below
the owner) rather than reuse this one. Discovering that from a lemma statement is cheaper than
discovering it inside a 300-line case analysis.

### One elaboration trap worth writing down

`applyKont`'s `asgn` case steps to `{ m with kont := k }.setLocal x v`, and `hfs` is phrased over
`m`. The two agree definitionally, and before this note the application elaborated fine — but with
`FramesOk` heap-indexed the elaborator resolves `?m` from `hfs` instead of from the goal, and the
unifier then reports a mismatch between two definitionally equal machine literals. The fix is one
named instance (`FramesOk.setLocal (m := { m with kont := k })`). Expect the same wherever a lemma
about `m` is applied at a machine `applyKont` built by a structure update.

**Checks:** `check-proofs.sh` green and axiom-clean (all five headline theorems, including L135's
two); tier-0 `--sut lean` **992 agree, 0 disagree**, unchanged.

## L138 — `--fragment` reported `missing-sig` for six annotated methods

`homebrew/HANDOFF.md`'s "clear the cheap fragment rows", and it really was our bug rather than the
slice's. `Fragment.lean`'s `scanStmts` threads `sigPrecedes` down a statement *list*, because "every
method carries a `sig`" is a property of a sequence. Send **arguments** are scanned with
`sigPrecedes := false`, which is right for arguments — and wrong for exactly one shape:

```ruby
sig { params(version: String).returns(...) }
private_class_method def self.parse(version)      # vulns/semver.rb:45–46
```

`private_class_method def self.parse` is *one statement*, so the `sig` above it precedes the `def`
— but the `def` arrives at `scan` as the modifier's argument, and the modifier is a send. Six
methods were reported as unannotated: `self.parse`, `self.compare_prerelease`,
`self.compare_identifier` in `vulns/semver.rb` and `self.parse`, `self.valid_values?`,
`self.round_up` in `vulns/cvss.rb`. All six carry sigs upstream.

The fix is one branch: a `visibilityMod` (`private`, `public`, `protected`,
`private_class_method`, `public_class_method`, `module_function`) with an implicit-self receiver
passes `sigPrecedes` through to its arguments via a new `scanListSig`. Everything else is
unchanged, and a `visibilityMod` applied to *symbols* (`private :a, :b`) is unaffected because a
symbol has no `missing-sig` arm.

**Why this mattered more than six rows.** A `missing-sig` row says "this method's parameters and
return are `T.untyped`", which is the criterion-2 exclusion — so the report was claiming the slice
had six untyped methods it does not have, in exactly the two files whose *whole content* is the
`Semver.compare` half of §1's headline finding. `vulns/semver.rb` and `vulns/cvss.rb` now have one
violation each, and both are the erased-type-argument row the fragment admits by design.

Slice-wide, `--fragment` on a harvested program is down from 11 rows to **6**, and the remaining
six are honest: `T.untyped` (W8's two known jobs), `T::Array[…]`/`T::Hash[…]`/`T::Struct` (the
erased-container weakening `Fragment.lean` records), `alias eql? ==` and `instance_variable_set`
(real reflective uses in `version.rb`) — plus `__exp`/`__exr`, the corpus's own assertion helpers,
which are deliberately left alone: a **toplevel** `sig` installs the `method_added` hook
(`T.__toplevel_sig`), and adding one to every harvested program to fix a report row would change
the boot heap of all 355 of them.

**Note the standing distinction, which this does not resolve.** `Fragment.lean`'s fragment (the
Sorbet discipline: every method annotated, no unchecked escape) is *not* `infer`'s domain (what the
type system can type). They are two artifacts with two purposes, and F1 has to decide whether they
converge.

Checks: tier-0 992/0, slice 351/0 (+1 gated, +3 `control_invalid`), tier-4 25/0,
`check-proofs.sh` green and axiom-clean.

## L139 — D10 in `Fragment.lean`: the reflective family reclassified, four kinds instead of one

`PLAN.md` **D10** made executable. The old fragment excluded seventeen reflective sends plus the
`alias` and `undef` heads under one charge — *"installs or dispatches methods outside the sig
discipline (§C.2 type escape)"* — on the equality reading of the invariant. D10 replaces the
equality with a refinement (`homebrew/typing-a-mutable-method-table.md` §2), and once the invariant
is monotone in the method table that one charge is wrong three different ways at once: it excludes
additions that cannot hurt, it charges `instance_variable_set` with something it does not do, and it
says nothing about the one step that really is fatal.

**The single list becomes four, each with its own `Violation.kind` and reason line.**

| list | kind | members | verdict |
|---|---|---|---|
| `deferredSend` | — | `define_method`, `define_singleton_method`, `alias_method`, `prepend` | **admitted** |
| `removalSend` | `table-removal` | `remove_method`, `undef_method`, and the `undef` head | excluded — this is D10's boundary |
| `keySend` | `key` | `set_temporary_name`, `const_set` | excluded — breaks the *key*, not the table |
| `dynamicSend` | `dynamic` | `send`, `public_send`, `__send__`, `class_eval`, `module_eval`, `instance_eval`, `instance_exec`, `method_missing`, `respond_to_missing?` | excluded — unknown call target, hence untyped *result* |
| `stateSend` | `state` | `instance_variable_set`, `instance_variable_get` | excluded — state outside the declared types (§4.1) |

The `alias` head is now **admitted**, which is the substantive relaxation. Whether `alias eql? ==`
is an addition or a redefinition depends on the heap, not on the expression, and whether a
redefinition conforms is a question about *types* — so `scan` admits it and `infer` answers
`unknown` if it cannot show conformance (§3). Two exclusions are new: `undef_method` and
`set_temporary_name` were in neither list before, and both are steps §2's table says do not preserve
the invariant. So this commit relaxes and tightens in the same pass, which is the reason to measure
it rather than assert it.

**Measured over all 355 harvested programs, before and after** (`--fragment` on the cached ASTs,
same binary rebuilt from a `git stash` for the before-run):

| kind | before | after |
|---|---|---|
| `reflective` — `alias eql? ==` | 243 programs | **0** (admitted) |
| `reflective` — `instance_variable_set` | 142 programs | **0** (recharged) |
| `state` — `instance_variable_set` | — | 142 programs |
| `table-removal` / `key` / `dynamic` | — | **0, 0, 0** |

Rows per program go 7 → 6 at the mode, and the same on the *linked* slice program
(`homebrew/slice-driver`, 2,159 lines): 7 rows → 6. **No program becomes in-fragment** (0 of 355
before and after), and that is the honest shape of the result — what still excludes every harvested
program is criteria 1 and 2, not criterion 3: `T.untyped` (214), the erased containers (307 + 160 +
72), and `missing-sig` on the corpus's own `__exp`/`__exr` helpers (355, deliberate — L138 says
why).

**Zero `table-removal`, `key` or `dynamic` rows corpus-wide** is the measurement §2.1 owes D5. D10
introduces a new source of `unknown`, which is in tension with *"either verdict is a result;
`unknown` is not"*, and the defence is that the excluded class is empty on the target. That was
argued from the slice's source; it is now measured over the corpus that actually runs.

**`deferredSend` is consulted by nothing**, which is the point — it names what D10 admits — so it
would rot silently. A `#guard` checks the four lists are disjoint from it at elaboration, which
turns "admitted" into a fact the build enforces rather than a comment.

**Relaxing this file cannot break a proof, and that is worth recording.** No theorem in `Proof/`
quantifies over `inSorbetFragment`; `StaticSoundness.lean` plays the fragment role with
`CtlOk`/`KontOk` and its docstring says so. So `Fragment.lean` is a *report* today and the
hypothesis of a theorem tomorrow, and the safety net for the relaxation is `infer`'s domain (which
types none of these constructs, so `check` answers `unknown`) rather than the metatheory. F1a is
where the two artifacts have to be reconciled.

**Two gaps in criterion 3, named in the header rather than papered over.** Renaming is caught only
at the two named operations, so `K = Class.new` reaches the same hazard through a plain `casgn` —
deciding that syntactically means knowing the assigned value is an anonymous class, which is
§Known-wrong-answers 2's shape and F1a's problem. And a class that *defines* `method_missing` is
still admitted: §6 shows it fails in the safe direction (the call succeeds, the result is untyped),
so whether to exclude it until occurrence typing exists is a scheduling question the document
deliberately leaves open.

Checks: tier-0 **992/0** (flat — this file is off every execution path), `check-proofs.sh` green,
axiom-clean, F0's `heapOkB` certificate still true at the booted heap.

## L140 — F1a: the declaration table, and the invariant as a refinement of it

`homebrew/typing-a-mutable-method-table.md` §8's F1a, and the rung everything below F1 is
stated in terms of. Two halves, and the second is the one with content.

### The table (`RubyCore/Types/Decls.lean`, new)

`builtinSig : Ty → String → Option (List Ty × Ty)` becomes a lookup in a **static, per-class
declaration table**: `Decls` maps a class *name* to method names to `MethodDecl` (parameters,
return). `sigOf D τ mname` is what the rules now read, and `D` is threaded through `defTy`,
`tableRefutes`, `illTyped`, `infer`, `inferSeq`, `inferIf`, `KontOk`, `CtlOk`, `LoopOk` and
`Inv`. `check p` supplies `declsOf p`.

Three details that are decisions rather than mechanics:

* **The key is the class *name***, because `infer` cannot name an `ObjId` — `check` is a pure
  function of the program and object identities exist only in a heap. That is also why
  `set_temporary_name` and anonymous-class renaming are outside the D10 fragment: they change
  the key, not the table (§5, and §Known-wrong-answers 2 is where this stops being cosmetic).
* **`tyClassNames` returns a *list***, and `declFor` demands that every class a receiver of that
  type can have declares the method **identically**. `Ty.bool` is already two classes, so
  `T::Boolean` (W5 T4) gets its semantics here rather than needing a union in `Ty`. Requiring
  agreement rather than taking the first is the honest reading: a declaration that holds on only
  `TrueClass` supports no call site on a `T::Boolean` receiver.
* **`declsOf p` is a function of the program and constant today.** Nothing in `infer`'s domain
  declares a signature, so it returns `baseDecls` for every `p`. Threading it while it is constant
  is the same move L137 made for the heap: it separates the threading from the growth, so F1b's
  program-supplied declarations change `declsOf` and not the rules.

`Ty`/`Env` moved to `RubyCore/Types/Ty.lean` unchanged, because `Decls` needs `Ty` and `Core`
needs `Decls`. That is the first two files of the five `PLAN.md` W5 asks for.

### The invariant (`RubyCore/Proof/Static/Decls.lean`, new)

`Inv`'s heap clause was `TableOk` — *the three tabulated `Integer` builtins resolve, publicly,
live, unshadowed, not `fromPrelude`* — an **equality-shaped** fact about three names. It is now
`DeclsOk D`:

> for every method the declarations name, `lookup` resolves it to something conforming to its
> declared signature.

**What that buys, concretely.** Each entry decomposes into two clauses that behave differently
under a heap write, and the decomposition is the substance:

* **`ResolvesTo h recv mname bid`** — resolution. Heap-dependent, and the *only* thing
  preservation has to re-derive; `Proof/HeapFacts.lean`'s `defineMethod` chain discharges it.
* **`ConformsAt h τr mname bid d`** — conformance: on arguments of the declared parameter types,
  `bid` answers a value of the declared return type. Its two *conclusions* are heap-uniform
  (`∀ h'`), which is what makes it transport for free, while its hypotheses read the invariant's
  heap, which is where F1b's nominal types will need to read it.

Three consequences, all of them things §7 predicted and none of them free:

1. **The three `int_*_dispatch` rewrites in `step_ok`'s `argsK` case collapse into one
   `entry_dispatch`.** So does the `builtinSig_inv` inversion, which is deleted: it existed only
   because the table was small and closed, and pinning `τr = .int ∧ mname ∈ {+,-,*}` is exactly
   what a refinement invariant must *not* need. §7's *"the ~128 conformance lemmas become
   per-entry witnesses rather than a parallel obligation"* is now literally true — a new entry is
   a `ConformsAt` proof and nothing else.
2. **`DeclsOk_defineMethod` is D10's claim as a lemma**: the additive step preserves the
   invariant, with no side condition beyond not displacing a **declared** name. So `infer`'s `def`
   rule checks `declaresName D name = false` where P0 checked `name ≠ "+"/"-"/"*"`, which is the
   same three names for `baseDecls` and generalizes without a further thought.
3. **`TableOk` is kept, unchanged, and is now a *witness* rather than the invariant.**
   `tableOk_declsOk` is the bridge, and the direction matters: the invariant carries the general
   statement, `heapOkB`/`scripts/heapok_probe.lean` decide the concrete one. **F0 needed no
   restatement at all** — `check_sound_withPrelude` and `check_sound_withPrelude'` are unchanged
   apart from `Inv`'s index, and the certificate still checks the same `Bool`. `TableOk`, `NoHook`
   and `TableOk_defineMethod` moved from `Proof/Static/Konts.lean` into the new file with the rest
   of the heap conditions.

### Two things the proof discovered that the design did not

* **`ConformsAt` has to exclude `Object#raise`, and `send`/`public_send`/`__send__`.** With an
  abstract `bid`, `invoke` has a post-resolution branch for `raise` that does not return a value,
  and the send family reads the *first argument* as the method name. Both were implicit in
  `int_bin_dispatch` — discharged by `decide` on a concrete `bid` — and a general statement has to
  say them out loud. A builtin for which either is false does not belong in a declaration table.
* **`entry_dispatch` must case-split the receiver, and the fragment's own judgement is what
  closes it.** `invoke` has receiver-shape special cases *before* the resolved-builtin path (a
  class object reaches `invokeMaybeNew`; `Math` has its own arm), so an abstract receiver leaves
  them standing. Every one is a `.ref`, and `valueTy?` has no `.ref` arm —
  `valueTy_immediate`. **This is the first place F1b will have to change something rather than
  extend it**, and it is worth knowing now rather than inside a 300-line case analysis.

Also found and dropped: `ResolvesTo` looked like it would need a `crubySingletonShadow` clause
that `IntBuiltinResolves` does not carry, and does not — `invoke` consults that gate only when
lookup did *not* resolve to a builtin. Measured by the proof not using it, which is why the
clause and the two lemmas written for it were removed rather than kept "for F1b".

### Verification, and what it is worth

F1a is supposed to accept **no new programs**, so the check is that nothing moves:

* **`--check` over all 1,227 decodable bootstraptest programs is byte-identical before and
  after** — 21 accept (13 `Integer`, 5 `NilClass`, 3 `Boolean`), 1,204 unknown, 0 reject. The
  before-run is the same corpus of cached ASTs against a binary rebuilt from a `git stash`, which
  is the cheap form of the worktree rule.
* `check-proofs.sh` green, axiom-clean, `heapOkB` still true at the booted heap.
* tier-0 **992/0**, slice **351/0** (+1 gated, +3 `control_invalid`), tier-4 **25/0** — flat, as
  they must be for a commit that touches no rule.

That "nothing moved" is the whole verification available at this rung, and it is the same
argument L137 rested on: the evidence a threading commit is right is that the *existing* proofs
still close over the new statements. `step_ok` closing is a stronger signal here than it was
there, because the `argsK` case genuinely goes through the new uniform lemma rather than the
three old ones.

## L141 — F1b/T2: a class type, and `entry_dispatch` paying F1a's deferred bill

`homebrew/typing-a-mutable-method-table.md` §8's F1b, first commit — and specifically the thing
§8's own correction to its F1a row says has to come first: *"the declaration table's key is a class
**name**, and `Ty` still has no arm that carries one … so a user class having a type is still
ahead, and it is the first thing F1b needs."* This is that arm.

`Ty` gains `| cls (name : String)`, and `valueTy?` gains the `.ref` arm that ties it to the heap.
**Nothing constructs one yet** — `infer` has no `new`, no `classDef`, no `casgn` — so the commit
accepts no new programs, by the same design and with the same verification as L140. What it *does*
is discharge the obligation F1a deferred, which is the entire reason to land it separately.

### `plainRecv`, and why the refusal is in the definition rather than at the use site

`valueTy? h (.ref o)` is `some (.cls (className h (classOf h (.ref o))))` **iff `plainRecv h o`**:
the object has no eigenclass, and its payload is not `.proc`, `.hsh` or `.cls`. Those three are
exactly `invoke`'s receiver-shape special cases (`Interp/Send.lean:33–92`) — a Proc answers
`call`/`()`/`[]`/`yield` by running its closure, a Hash with a `prc` default answers `[]` by
running that, and a class object reaches `invokeMaybeNew` or the `Math`/`Regexp` singleton arms.
`eigen = none` is the fourth condition and is there for a different reason: dispatch resolves
through `classOf`, which *is* the eigenclass when there is one, so an object with a singleton
method would have its declarations read off a class other than the one its type names. It is the
same hypothesis `Proof/T5.lean`'s `dispatch_progress` carries as `heigen`.

Putting all four **inside `valueTy?`** rather than assuming them at the use site is the decision
here. An inversion principle is only as strong as the definition it inverts: `valueTy_immediate`
becomes `valueTy_shapes` (immediate **or** a plain ref), and the `.ref` disjunct hands over
`plainRecv h o = true`, which is what `entry_dispatch` case-splits on. A Proc, a Hash and a class
object simply have no type in this rung — a refusal, not an approximation, and nothing unsound
follows from a value having no type.

### The ground names are subtracted from the class arm's key set, and that is not a technicality

`tyClassNames (.cls n)` is `[]` when `n` is one of `Integer`/`TrueClass`/`FalseClass`/`NilClass`/
`Symbol`, and `[n]` otherwise. Without the subtraction, `.cls "Integer"` would read `Integer`'s
declaration row — and the two arms have **disjoint inhabitants** (`valueTy?` gives an immediate a
ground type and a `.ref` a class type, never both), so the invariant would owe an `EntryOk` for
that row over receivers the row was never about: objects of some class merely *named* `Integer`.
Nothing in the model rules those out, so the obligation would be **unprovable**, not merely
awkward. Subtracting makes the type useless instead of unsound, which is the right failure
direction, and `Sub` is what will fix it properly (an `Integer` receiver should be typed `.int`).
This is what turns `tableOk_declsOk`'s new `cls` case into a refutation rather than an obligation.

### What the bill actually was, against what L140 predicted

L140 said `entry_dispatch` is *"the first place F1b will have to change something rather than
extend it"*, and `homebrew/HANDOFF.md` §F1b said to **budget for a different argument, not a
case-analysis widening**, and specifically that it would want `crubySingletonShadow` back as a
`ResolvesTo` clause. Measured:

* **It is a case analysis after all.** `cases (m.heap.get o).payload`: three constructors are
  refuted by `plainRecv` in one line each, and the other eight go through the *same* simp set as
  the four immediate cases, unchanged. The receiver-shape special cases are still closed by the
  type judgement; what changed is that the judgement now has to say so out loud instead of having
  no inhabitant to say it about.
* **`crubySingletonShadow` did not come back.** That gate sits on `invoke`'s `md.builtin = none`
  branch (`Interp/Send.lean:246`) and `ResolvesTo` pins `md.builtin = some bid`, so F1a's
  measurement survives an abstract object receiver unchanged. The prediction was reasonable and
  wrong for the same reason F1a's original one was: **the gate is a fact about which branch runs,
  not about which receiver arrives.**

Where the cost did land was the transport condition, and L137 had already named the spot.
`TypeAgree` gains a fourth clause, `∀ o, plainRecv h' o = plainRecv h o`, because the `.ref` arm
reads `eigen` and `payload` and neither is determined by `classOf`/`className`/`classPayload?`-ness.
`ValueTy.congr` stops being `id` — it now uses three of the four clauses — which is exactly what
L137 threaded the heap in for and predicted would happen *here* rather than at the callers. The
instance is `plainRecv_defineMethod`, and note what it is **not**: not "the payload is unchanged",
since at `o = cls` it really does change, only that it stays a `.cls`, which is all `plainRecv`
asks. `objs_getD_set!_self` (`Proof/HeapFacts.lean`) is its one new supporting fact — the companion
of `objs_getD_set!_ne` at the *written* index, which the `defineMethod` chain had never needed
because until now nothing read the payload it writes.

### Verification

Same shape as L140's, because the claim is the same claim:

* **`--check` over all 1,227 decodable bootstraptest programs is byte-identical before and after**
  — 21 accept, 1,204 unknown, 0 reject, against a binary rebuilt from a `git stash`.
* `check-proofs.sh` green, axiom-clean (`propext`/`Classical.choice`/`Quot.sound` only), `heapOkB`
  still true at the booted heap.
* tier-0 **992/0**, slice **351/0** (+1 gated, +3 `control_invalid`), tier-4 **25/0** — flat.

### What this leaves for the next commit, precisely

A **producer**. Nothing gives a value the class type, so `EntryOk` at a `.cls` is vacuous today and
the arm is exercised only by the proofs. Giving it one means `classDef`/`Class#new` in `infer`,
which means an `alloc`, which is where the *other* half of L140's warning comes due: `ancestors_congr`
(`Proof/HeapFacts.lean`) requires `objs.size` to be **equal**, so an allocating step needs a
monotonicity lemma that does not exist. That is the F1b bill that is still unpaid, and it is now
the only thing between here and a user class having a type.

Also unpaid and now visible as a *shape* rather than a suspicion: `declaresName` is **name-global
across all classes**, so every row added to `baseDecls` refuses `def <name>` on every class. It is
sound and it is exactly P0's behaviour for three names, but it means F6's ~128 rows would refuse
`def to_s`/`==`/`each` program-wide. Relativizing it to the defining class is not cheap —
`DeclsOk_defineMethod` gets its side condition from `ResolvesTo_defineMethod`'s `mname ≠ name` over
an **arbitrary** `cls`, so a class-relative version is an ancestors-relative, heap-dependent
argument, i.e. the wrong side of the `ResolvesTo`/`ConformsAt` line L140 says to keep clauses off.
So `widening-the-fragment.md` §5.2's sixteen prelude signatures are **not** parallelisable from
F1b as `HANDOFF.md`'s list says; they are downstream of this.

## L142 — the producer rung's first bill: an unallocated `ObjId` had a type

`homebrew/HANDOFF.md` (ninth session) and L141's own closing section both name **one** blocker in
front of a producer for the class type: `ancestors_congr` (`Proof/HeapFacts.lean`) requires
`objs.size` to be *equal*, so an allocating step wants a fuel-monotonicity lemma that does not
exist. That is true. It is also **not the first bill an `alloc` runs into**, and the one in front of
it is smaller, is a latent defect rather than a missing lemma, and is fixed here.

### The measurement

`Heap.get` answers an out-of-bounds id with `default` (`Array.getD`), and a `default : Object` has
`klass = 0`, `eigen = none` and `payload = .none`. So `plainRecv` was **true out of bounds**, and
L141's `.ref` arm duly read a type off it. Measured at the boot heap
(`scripts/alloc_probe.lean`, kept as a check):

```
objs.size before = 40, after = 41, fresh id = 40
valueTy? h  (.ref 40) = some (Ty.cls "BasicObject")     -- before this commit
valueTy? h' (.ref 40) = some (Ty.cls "String")
classOf  h  (.ref 40) = 0  →  after alloc  9
```

**Every unallocated id was typed `.cls "BasicObject"`, and allocating changed its type.** That
refutes `TypeAgree`'s first clause (`∀ v, classOf h' v = classOf h v`) at the fresh id, so the
transport condition is **false for any allocating step** — not unproved, false — before any
question about `ancestors`' fuel arises. Nothing observes it today, because nothing constructs a
class-typed value and every `baseDecls` row is at a ground type; it is exactly the kind of defect
that becomes live in the commit that adds the producer.

### The fix, and why it is the same move L141 made

`plainRecv` gains `o < h.objs.size`. The lesson the ninth session recorded — *ask what the absent
case was proving, and whether it can be a hypothesis instead* — applies unchanged one rung later:
the side condition goes into the **judgement** rather than being derived at the use site. `ValueTy`
then implies the value is in bounds (`valueTy_ref_lt`, isolated so the transport lemmas can consume
it without unfolding `valueTy?`), which is what will let `TypeAgree` be relativized to ids the old
heap actually had — and `alloc` satisfies *that* definitionally, since `Array.push` does not touch
an existing index.

Cost: one clause, one lemma, and one line of `plainRecv_defineMethod` (`set!` preserves
`objs.size`, so the new clause transports for free). Nothing else in the tree needed repair —
`valueTy_shapes`, `ValueTy.congr` and `entry_dispatch` are untouched.

### Verification, and why the `--check` diff is not owed this time

`plainRecv` and `valueTy?` live in `Proof/Static/Locals.lean`, which is off `defaultTargets` and is
not linked into `rubycore`. No rule, front-end file, prelude line or *checker* function changed, so
`--check`'s answer cannot move and the byte-diff L140/L141 owed has no content here. What is owed
and was run: `check-proofs.sh` green, axiom-clean (`propext`/`Classical.choice`/`Quot.sound` only),
`heapOkB` still true at the booted heap; `scripts/alloc_probe.lean` exit 0; tier-0 flat.

### What the producer still owes, re-measured

The remaining bill, in the order an allocating step meets it — the point of writing it down is that
only the third item was on the list before:

1. ~~An unallocated id has a type.~~ This commit.
2. **`TypeAgree` relativized to `< h.objs.size`.** The definition and `ValueTy.congr` are the only
   real consumers of the `.ref` case, and item 1 supplies the in-bounds fact `ValueTy.congr` needs.
3. **`ancestors`/`lookup` preserved across a size-*increasing* heap.** `ancestors` takes fuel
   `h.objs.size + 1`, so `ancestors_congr`'s `hsz` is used twice as a fuel rewrite and nothing
   else. Either weaken it to `≥` plus a "the walk terminates within its fuel" side condition, or
   get termination from a heap clause — the superclass chain descending in `ObjId` is true by
   construction (a subclass is allocated after its superclass) and decidable at the boot heap, so
   F0's certificate could absorb it the way it absorbs `TableOk`. This is the item the handoff
   named, and it is third rather than first.
4. **`ConformsAt` cannot describe an allocating builtin at all**, and this one reshapes the rung:
   its conclusion is `∀ m, Builtins.run bid recv args m = .ok w m` — the machine **unchanged** —
   and `entry_dispatch` concludes `.next (withCtl m (.value w))` for the same `m`. `Class#new`
   allocates (`Builtins/Support.lean` `newImpl`). So `C.new` cannot be typed through the
   declaration table by an `EntryOk` witness; the producer has to be a **syntactic** rule in
   `infer` with its own consecution case proving the allocating step directly. Worth stating
   plainly because it means the producer is not "one more table row".

`DeclsOk` preservation across the alloc is the fifth item and is vacuous *only* while the produced
class has no declared rows — which is the inert shape L140 and L141 both used, and the shape the
producer commit should use too. The moment a row exists for a user class, `EntryOk`'s ∀-receiver
clause needs a resolving builtin for it, i.e. the user-method witness `HANDOFF.md` describes. So
the producer and that witness are two halves of one accept-rate change, not two independent
prerequisites.

## L143 — the producer rung's second bill: `TypeAgree` relativized, and a second bound it needed

L142's item 2, and it did not come alone. Relativizing the transport is the mechanical half; what
the commit is *worth* is the second out-of-bounds default it found, in the same shape as L142's and
one indirection further along.

### The relativization, and the clause that had to change shape

`TypeAgree` was four unrelativized equalities. Three become "at every id the old heap had":

```lean
def TypeAgree (h h' : Heap) : Prop :=
  (∀ o, o < h.objs.size → classOf h' (.ref o) = classOf h (.ref o)) ∧
    (∀ k, k < h.objs.size → className h' k = className h k) ∧
    (∀ k, k < h.objs.size → (h'.classPayload? k).isSome = (h.classPayload? k).isSome) ∧
    (∀ o, o < h.objs.size → plainRecv h o = true → plainRecv h' o = true)
```

The first clause also moved from values to ids, because `classOf` on an immediate is a
heap-independent constant, so the value form is derivable and was carrying nothing.

**The fourth clause is an implication, and that is forced rather than chosen.** `plainRecv` reads
`h.objs.size` — twice, after this commit — so a *growing* heap can turn a non-plain receiver plain,
and does exactly that for an object whose class is the id being allocated. An equality is therefore
false for `alloc`. Nothing needs the equality: transport carries facts *forward*, so what it needs
is that a receiver the old heap **typed** is still typed. Read the four clauses as *everything the
old heap could say about an id it had, it can still say* — the weakest thing `ValueTy.congr` accepts.

`typeAgree_alloc` is the payoff and is proved here rather than promised: one fact — `Array.push`
leaves every existing index where it was — discharges all four clauses.

### The second bill: `className` has an out-of-bounds default too

`ValueTy.congr`'s `.ref` case needs the transport at *two* ids: `o`, and the class `o` dispatches
through, because the arm's type is `className h (classOf h (.ref o))`. `className` answers out of
bounds with `"Object"` (via `classPayload? = none`). So for an object whose `klass` is the id an
`alloc` is about to hand out, the type moves from `.cls "Object"` to `.cls C` — **L142's defect
exactly, one indirection along, and relativizing to `o < h.objs.size` alone does not touch it.**

Fixed the same way, which is now the third application of the ninth session's lesson: the side
condition goes into the judgement. `plainRecv` gains `(h.get o).klass < h.objs.size`, and
`valueTy_ref_klass_lt` reads it back out for the transport. **A refusal has to be priced**, so
`scripts/alloc_probe.lean` now counts what the clause costs at the *prelude-booted* heap:

```
booted heap: 105 objects, 18 plain receivers, 0 refused for an out-of-bounds klass (want 0)
```

Zero, as a heap no rule can build ill-formed should be — but measured, because that is the number
this clause could get wrong, and the script fails if it ever moves.

### `TypeAgree.symm` is withdrawn, and its two callers now say which direction they need

A relativized, one-directional `TypeAgree` **is not symmetric**, and cannot be: the clauses are
about the left heap's ids, and the fourth is an implication that a heap typing *fewer* receivers
satisfies. L137's `TypeAgree.symm` is therefore deleted rather than weakened — its statement is
false for any growing step.

Both callers were `defineMethod` ones (`ConformsAt_defineMethod` and `DeclsOk_defineMethod`, in
`Proof/Static/Decls.lean`: `ConformsAt` reads its `ValueTy` hypotheses in the old heap while
`DeclsOk` states them in the new one, so F1a genuinely runs the transport backwards). A
method-table write proves four *unrelativized equalities*, so both directions come from one lemma —
`TypeAgree.of_equalities`, whose only job is to hand back the pair — exposed as
`typeAgree_defineMethod` and `typeAgree_defineMethod'`. **A growing step will not have that lemma
available**, which is worth knowing now: the producer's consecution case has to be arranged so that
the backward transport is never needed, or `ConformsAt` has to stop asking for it — which is item 4.

### Verification

Same argument as L142, and the same three checks: the only files touched are
`Proof/Static/Locals.lean`, `Proof/Static/Decls.lean` and a script, all off `defaultTargets` and
none linked into `rubycore`, so no rule, prelude line or checker function moved and `--check`'s
answer cannot. `scripts/check-proofs.sh` green and axiom-clean, `heapOkB` still true at the booted
heap; `scripts/alloc_probe.lean` exit 0 with the new count; tier-0 flat at **992 agree, 0 disagree**.

Notable non-event: the extra `plainRecv` conjunct required **no** repair in `entry_dispatch`, which
refutes `invoke`'s three receiver-shape special cases by `simp [plainRecv, hpl]` — a conjunct added
to a `&&`-chain whose last factor is already `false` is free.

### What the producer still owes

Items 3 and 4 of L142's list, unchanged, and now with the fifth named above: the backward transport
`ConformsAt` currently demands is a *growing*-step problem, so item 4 (`ConformsAt` past
machine-purity) and the shape of the producer's consecution case are one question, not two.

## L144 — the ancestor walk across a growing heap, and the clause `HANDOFF.md` proposed is false

L142's item 3: the blocker three consecutive sessions named. `ancestors` and `modAncestors` are
fuel-bounded rather than `partial` (L73 — a `partial def` is opaque to the kernel and every `rfl`
over a dispatch would get stuck), the fuel is `h.objs.size + 1`, and `ancestors_congr` therefore
requires the size to be **equal** — using that hypothesis twice, both times as a fuel rewrite and
nothing else. An allocating step had no ancestor congruence at all.

New file `Proof/AncestorsGrow.lean`; nothing existing changed.

### The measurement first, and it refutes the route

`HANDOFF.md` and L142 both proposed the same clause: **the superclass chain descends in `ObjId`** —
a subclass is allocated after its superclass, so the walk from `k` takes at most `k + 1` steps, any
fuel `≥ k + 1` agrees, and F0's `heapOkB` certificate can absorb the clause because it is decidable
at the boot heap. Forty lines of `IO` (`scripts/ancestors_probe.lean`) before any proof attempt:

```
non-descending edges (HANDOFF's proposed clause, want 0): 10
  include: Object (1) → Kernel (33)
  superclass: Integer (7) → Numeric (34)
  include: String (9) → Comparable (40)
  include: Array (11) → Enumerable (42)
  …
```

**It is decidable and it is false**, for a reason that is structural rather than fixable: the boot
heap's ids are *literals* (`Boot.objectId = 1`, `Boot.integerId = 7`) while `Kernel`, `Numeric`,
`Comparable` and `Enumerable` are **prelude Ruby**, allocated afterwards — so the classes with the
smallest ids are exactly the ones pointing at the largest, and no re-ordering of the prelude repairs
it while the boot ids are constants. The walk is also not only the superclass chain: `ancestors`
splices `includes`/`prepends` and `modAncestors` recurses through modules, which is what makes the
mixin edges count. Had this been proved rather than measured first, the failure would have arrived
at the end of an induction instead of in the first minute.

### What is true is *saturation*, and it is weaker than what was proposed

The fuel does not need the walk to be **short**. It needs it to have **finished** before the fuel
runs out, which is a different and directly checkable property: *one more unit of fuel changes
nothing*.

```lean
def Saturated (h : Heap) : Prop :=
  (∀ mo, modAncestors.go h mo (h.objs.size + 1) = modAncestors.go h mo h.objs.size) ∧
    (∀ k, ancestors.go h k (h.objs.size + 1) = ancestors.go h k h.objs.size)
```

Two clauses because there are **two fuels in one walk**: `ancestors.go` recurses on its own, and
the `modAncestors h` it splices in carries a second one — `h.objs.size + 1` again — which a growing
heap moves as well. Missing that is how a "one fuel lemma" turns into two, and reading
`ancestors_congr`'s statement does not show it; reading what its *body* rewrites does.

From saturation, `modAncestors_go_add`/`ancestors_go_add` give fuel-monotonicity at every larger
fuel by induction on the excess, and `ancestors_congr_grow` is the payoff: `=` becomes `≤`.
Axiom-clean (`propext`, `Quot.sound`).

**Saturation is not derivable from the shape agreement it sits beside**, and that is why it is a
hypothesis: nothing in the `Heap` type forbids a cyclic `include`, and a cyclic walk consumes all
its fuel, after which different fuels genuinely disagree. So it is a real clause, and it is carried
as one rather than smuggled in.

### The certificate, and why it is in `check-proofs.sh`

`saturatedB` decides `Saturated` at a heap in hand; `saturatedB_sound` is the reflection. The
out-of-bounds ids the `Bool` cannot range over are free (`classPayload?` is `none` there, so both
walks answer `[k]` at any positive fuel — `go_oob`), which is the same structure F0's `heapOkB`
has, for the same reason: `Prelude.boot` runs `Lean.Json.parse`, which does not kernel-reduce, and
L94 bans `native_decide`. **A hypothesis the harness can check beats an `axiom` and beats a proof
nobody has finished** (D1's trade for `bound_suffices`, L135's for F0).

So `scripts/check-proofs.sh` gained a fourth section. Without it the hypothesis could stop being
satisfiable — a prelude change that makes one walk fuel-sensitive — with every proof still green,
which is exactly the failure mode L119 was about. Measured: `saturatedB = true`, **0** fuel-sensitive
ids of 105 objects / 87 classes.

### What this covers, and the one case it does not

`ancestors_congr_grow` takes `ShapeAgree` **unrelativized**, and `shapeAgree_alloc_nonClass` says an
`alloc` of a **non-class** supplies it — including at the fresh id, where both heaps answer `none`.
That is the producer for `.cls C` values: `C.new` pushes a plain object.

Allocating a **class** (`classDef`, i.e. typing `class C … end`) does *not* supply it: the fresh id
has a shape in `h'` and none in `h`. That case needs one more clause — *no in-bounds object has an
edge pointing out of bounds* — after which the shape agreement can be relativized the way
`TypeAgree` now is (L143). The probe measures it: **0** out-of-bounds edges at the booted heap. So
it is a proof that is owed, not a fact in doubt, and it belongs to the `classDef` rung rather than
this one.

### Verification

`Proof/` and two scripts only, so `--check` cannot move (L142's argument). `check-proofs.sh` green
across all four sections, axiom-clean, `heapOkB` and `saturatedB` both true at the booted heap;
`alloc_probe.lean` exit 0; tier-0 flat at 992 agree, 0 disagree.

## L145 — what an allocating step leaves alone, and where resolution stops being about receivers

L143 relativized the type transport and L144 the ancestor walk. The third transport a producer's
consecution case owes is **resolution**: `DeclsOk`'s heap-dependent half is `ResolvesTo`, which reads
`lookup`, `ancestors`, `classOf`, `className` and `crubyShadow`. New file `Proof/HeapGrow.lean`, plus
two lemmas in `Proof/Static/Decls.lean` and a factoring in `Proof/Static/Locals.lean`.

### `PlainGrow`, and why its third clause is the interesting one

```lean
structure PlainGrow (h h' : Heap) : Prop where
  size    : h.objs.size ≤ h'.objs.size
  get     : ∀ o, o < h.objs.size → h'.get o = h.get o
  payload : ∀ k, h'.classPayload? k = h.classPayload? k
```

The first two are what any `push` gives. **The third is global — at every id, including the new
ones — and it is what a *non-class* allocation supplies**: at the fresh id both heaps answer `none`,
in one case because the object is not a class and in the other because it is not there.

That global clause is worth its restriction, because `classPayload?` is what `lookup`, `ancestors`,
`className` and `crubyShadow` *all* read. With it, every one of those congruences is unconditional —
no side condition saying the walk stays inside the old heap, no relativized `ShapeAgree`, no edge
locality. `lookup_go_grow` and `crubyShadow_grow` are two lines each for that reason.
`Saturated` (L144) enters at exactly one place, `ancestors`, and `PlainGrow.classOf_eq` is the one
function that needs the id to be an old one — the fresh id is precisely where `classOf` differs
(`scripts/alloc_probe.lean`).

Allocating a **class** breaks the third clause and nothing else. That is the honest scope statement,
and it is the same boundary `AncestorsGrow.lean` drew.

### A factoring that fell out, and it is the useful kind

`typeAgree_alloc` (L143) was proved about `h.objs.push obj` directly. Its proof never used the push:
every clause follows from *`get` agrees at old ids, and the heap grows*. So it is now
`typeAgree_of_get`, with `typeAgree_alloc` and `typeAgree_of_plainGrow` as corollaries — one line
each. **The type transport needs strictly less than resolution does**, and having the two hypotheses
side by side is what shows it.

### The lemma worth more than the file: resolution is about *classes*, not receivers

`ResolvesTo_grow` transports resolution across a `PlainGrow` for any receiver the old heap had. It
cannot say anything about the receiver the old heap did *not* have — the fresh object — and that is
the case the producer creates. Reading `ResolvesTo` to find out how bad that is turned up the
opposite:

```lean
theorem ResolvesTo_classOf (heq : classOf h recv' = classOf h recv)
    (hr : ResolvesTo h recv mname bid) : ResolvesTo h recv' mname bid
```

**`lookup` is `lookup.go` over `ancestors h (classOf h recv)` and the shadow chain is the same walk,
so `ResolvesTo` factors through `classOf` — two rewrites.** Consequence: *a new object of an existing
class carries no new resolution obligation*, because every receiver of a class resolves iff any one
of them does. So `DeclsOk`'s ∀-receiver clause is really a statement about **classes**, and an
allocation adds no class.

That is a fact about the *shape of the invariant*, not about allocation: the clause is
inhabitant-indexed where its content is class-indexed, and the fresh-receiver case is what makes the
mismatch visible. Restating it class-indexed is the next commit, and it is what will let `DeclsOk`
survive an allocating step **without** a hypothesis about which types the new object inhabits — the
alternative being an inert-only side condition that would have to be deleted again the moment a
declared row for a user class exists.

### What is still owed on `ConformsAt`, sharpened

Two problems, and they are the same problem:

1. its conclusion is `∀ m, Builtins.run bid recv args m = .ok w m` — the machine **unchanged** — so
   no allocating builtin can be a conforming entry (L142 item 4, and F6's ~128 rows);
2. its hypotheses read the invariant's heap, so transporting it across a growing step needs the
   **backward** type transport, which L143 showed does not exist for a growing heap.

Both are fixed by making conformance *heap-uniform* — quantify over the machine it runs in, and let
the answer's type be read in the **post** heap — which is also what removes `ConformsAt` from
`DeclsOk`'s heap-dependent half entirely. Not done here.

### Verification

`Proof/` only; `--check` cannot move. `check-proofs.sh` green across all four sections and
axiom-clean, `heapOkB` and `saturatedB` true at the booted heap; `alloc_probe.lean` exit 0; tier-0
flat at 992 agree, 0 disagree.

## L146 — conformance stops being heap-indexed, and `DeclsOk` survives an allocation

The producer's bill item 4. L142 stated it as *`ConformsAt` cannot describe an allocating builtin*,
which is true and is the second half; the first half is what L145 turned up — `ConformsAt`'s heap
index is what makes the invariant demand a **backward** type transport, and a growing heap has none.
Both are one change of statement.

### The change

```lean
-- before                                    -- after
def ConformsAt (h : Heap) (τr : Ty) …        def ConformsAt (τr : Ty) …
  ∀ recv args, ValueTy h recv τr → …           ∀ (m : Machine) recv args,
    ∃ w, ValueTy h w d.ret ∧                     ValueTy m.heap recv τr → …
      ∀ m, Builtins.run bid recv args m          ∃ w, ValueTy m.heap w d.ret ∧
             = .ok w m                             Builtins.run bid recv args m = .ok w m
```

The machine moves from *inside* the existential to the front of the statement. That is all, and it
was hiding in plain sight: the old form had a heap-**uniform** conclusion (`∀ m`) under a
heap-**dependent** hypothesis (`ValueTy h recv τr`), and the asymmetry was the whole cost.

**Nothing else moved.** `entryOk_int`'s proof changes by one line (`intro m` earlier, `hrun a y m`
instead of `fun m => hrun a y m`) because every hypothesis it used was a `valueTy_int` inversion, and
those are heap-independent. That is the evidence the index was carrying nothing: if a witness had
really needed the invariant's heap, this would have broken it.

### What the index was costing

* **~~`ConformsAt_defineMethod`~~ is withdrawn, not repaired.** Conformance mentions no heap, so a
  heap-writing step has nothing to re-establish. It is worth recording what that lemma *was*: the
  only consumer of `TypeAgree`'s backward direction — the one L143 had to supply specially via
  `TypeAgree.of_equalities`, and the one no growing step can supply. **Deleting the clause deleted
  the obligation.**
* `DeclsOk`'s heap-dependent half is now exactly `ResolvesTo`, which is what L140's split *said* it
  was. L140 achieved the split for preservation; this achieves it for the statement.

### `DeclsOk` across an allocating step

With conformance out of the way, `DeclsOk_grow` is resolution and nothing else, and its side
condition is the one L145 predicted in the form `ResolvesTo_classOf` consumes:

> every receiver the new heap types was already typed by some receiver of the same dispatch class.

That is exactly what a *fresh inhabitant of a declared class* forces, and it is honest: resolution is
a fact about a class, so a new object needs no new proof unless its class is new too. Note the
hypothesis that is **absent** — nothing about the backward type transport.

`DeclsOk_grow_ground` discharges it unconditionally when no declared type is a class type, via two
new inversions: a typed `.ref` has a *class* type (`valueTy_ref_cls`, so a ground-typed declaration
can only ever be about immediates) and an immediate's type is heap-independent
(`valueTy_immediate`). And `declsOk_baseDecls_grow` applies that to the table the model actually
carries — `declFor_baseDecls_cls` says `baseDecls` declares nothing at a class type, which is
`tyClassNames`' ground-name subtraction (L141) paying off a second time.

**So the producer's `DeclsOk` obligation is discharged today, for the table as it stands** — and the
reason it discharges is the reason the producer lands inert: nothing declares a row for a user class
yet. The moment one does, `DeclsOk_grow` is the theorem and its side condition is real work.
`declFor_baseDecls_cls` was also pulled out of `tableOk_declsOk`'s class arm, which now cites it
instead of repeating the computation.

### What is left of item 4

The half L142 named: `ConformsAt`'s conclusion still says the machine comes back **unchanged**, so an
allocating builtin — `Class#new`, and most of F6's ~128 String/Array/Hash/Regexp rows — still cannot
be a conforming entry. That is now a *conclusion*-side change only, and the pieces it needs are all
in place: `PlainGrow` for what the step leaves alone, `typeAgree_of_plainGrow` for the value
transport, `declsOk_baseDecls_grow` for the invariant. `entry_dispatch` is where it lands, because
the two branches produce different step results.

### Verification

`Proof/` only; `--check` cannot move. `check-proofs.sh` green, axiom-clean (the audit now names
`declsOk_baseDecls_grow` too), `heapOkB` and `saturatedB` true at the booted heap;
`alloc_probe.lean` exit 0; tier-0 flat at 992 agree, 0 disagree.

## L147 — resolution indexed by the class, and the last conditional leaves the producer's path

L145 observed that `ResolvesTo` factors through `classOf`. L146 removed conformance's heap index and
left `DeclsOk_grow` with one side condition — *every receiver the new heap types was already typed by
some receiver of the same dispatch class* — which was the honest form of an **inhabitant-indexed**
clause. This takes the L145 observation seriously and the side condition disappears.

### The change

```lean
-- before                                          -- after
∃ bid, (∀ recv, ValueTy h recv τr →                ∃ bid, (∀ k, TyClass h τr k →
          ResolvesTo h recv mname bid) ∧ …                    ResolvesAt h k mname bid) ∧ …
```

`ResolvesAt h k` is `ResolvesTo`'s clauses over `lookupIn h k` — the method-table walk *from a
class* — and `resolvesTo_of_resolvesAt` is the identity, because `lookup h recv m` is
`lookup.go h m (ancestors h (classOf h recv))` definitionally. `TyClass h τ k` names the dispatch
classes a type has: boot ids for the ground arms, and for `.cls n` a name **plus** the requirement
that the id really is a class — without which an out-of-bounds id would satisfy `.cls "Object"`
(`className` answers `"Object"` there) and the clause would demand resolution from a slot that does
not exist.

### Why it is the right indexing, not merely a nicer one

**The inhabitant-indexed clause cannot be preserved across an allocation.** A fresh object of a
declared class needs resolution; the only receiver-shaped hypothesis available is about receivers the
*old* heap had, and there may be none — a class can be declared before it has any instances. So the
clause is unprovable in general, and L146's side condition was that gap made explicit.

Class-indexed, the hypothesis transports:

* `TyClass` reads only `className` and `classPayload?`-ness, so it transports **backwards** across
  both steps — including at ids the old heap did not have, where both heaps answer `"Object"` and
  `none` (`TyClass_grow`, `TyClass_defineMethod`);
* `ResolvesAt` transports **forwards** with no receiver-side hypothesis (`ResolvesAt_grow`);
* conformance mentions no heap at all (L146).

`DeclsOk_grow` is therefore three lines and **unconditional**. `ValueTy` does not transport backwards
across a growing heap (L143) and never will — a fresh object *is* a new inhabitant. It is not a new
class, and that is the whole content of this commit.

### Four withdrawals, and they are the good kind

* ~~`DeclsOk_grow_ground`~~, ~~`declsOk_baseDecls_grow`~~ (L146) — scaffolding for the side condition
  that no longer exists.
* ~~`ResolvesTo_classOf`~~, ~~`ResolvesTo_grow`~~ (L145) — the first *is* the new indexing, so it
  became `rfl`; the second carried the receiver-in-bounds hypothesis that could not reach a fresh
  object.
* ~~`TypeAgree.of_equalities`~~, ~~`typeAgree_defineMethod'`~~ (L143) — and this one is the sequence
  worth keeping visible, because each step corrected the previous: L137 had `TypeAgree.symm` (true,
  the relation being four unrelativized equalities); L143 relativized the relation, making `symm`
  **false** for a growing step, and replaced it with both-directions-from-`set!`; L146 retired one
  caller; L147 retires the other. **The invariant's transport is now entirely forward.** What that
  machinery was paying for was the inhabitant-indexed clause — the clause was the defect.

### `plainRecv` gains a clause, the third time, and this one subsumes the second

The class arm's use site (`EntryOk.resolves`, instantiated at `classOf h recv`) needs the receiver's
dispatch class to *be* a class, so `plainRecv`'s L143 conjunct `(h.get o).klass < h.objs.size`
becomes `(h.classPayload? (h.get o).klass).isSome`. It **subsumes** the bound —
`classPayload?_isSome_lt` — so nothing was added, only sharpened.

The pattern is now worth naming, since it has happened three times (L142, L143, L147): **every one
of these clauses was found by asking what a later rung has to derive at the use site, and every one
was cheaper in the judgement than at the use site.** Priced as before, by measurement rather than
assertion: `scripts/alloc_probe.lean` reports **0 of 105** booted objects refused, 18 plain
receivers.

Two proofs got shorter as a consequence: `entryOk_int`'s resolution half is now `intro k hk; subst
hk; exact hres` — `TyClass h .int k` *is* `k = Boot.integerId`, so the `valueTy_int` inversion and
the `lookup_int_const`/`classOf_int` rewrites all went away — and `plainRecv_defineMethod` factors
through a new `plainRecv_congr`.

### What is left of item 4, unchanged

`ConformsAt`'s conclusion still says the machine comes back **unchanged**, so an allocating builtin
still cannot be a conforming entry. Every piece around it is now in place: `PlainGrow`,
`typeAgree_of_plainGrow`, `DeclsOk_grow` with no hypotheses about inhabitants, and `Saturated`
checked at the booted heap.

### Verification

`Proof/` and one script; `--check` cannot move. `check-proofs.sh` green and axiom-clean (the audit
names `DeclsOk_grow`), `heapOkB` and `saturatedB` true at the booted heap; `alloc_probe.lean` exit 0;
tier-0 flat at 992 agree, 0 disagree.

## L148 — the invariant carries saturation, and there is one heap certificate rather than two

`DeclsOk_grow` (L147) needs `Saturated` **at the heap the step starts from**, and only the invariant
can carry a fact there. So `Inv` gains a third heap conjunct, which means it owes what every conjunct
owes: initiation, and a proof for each step that writes the heap.

### The three obligations, and none of them was hard

* **Initiation at the boot heap.** `saturatedB Boot.initHeap = true` **by `decide`** — the boot heap
  is a literal, so the walk really does reduce in the kernel, in under a second. Worth stating
  because it is the *opposite* of the F0 situation: the prelude-booted heap is
  `Lean.Json.parse`-built and does not reduce (L135, L94), which is why the certificate route exists
  at all.
* **`defineMethod`.** `Saturated_defineMethod`: shape and size are both preserved, so `go` agrees at
  every fuel and saturation transports by three rewrites.
* **A growing heap.** `Saturated_grow`, and this is the interesting one — the fuel *changes*, so the
  proof is §1's fuel monotonicity rather than a rewrite. Both walks agree with the old heap's at any
  fuel (shape congruence needs no size hypothesis), and above `objs.size + 1` the old heap's answer no
  longer moves, so the new heap's does not either at its own larger fuel. Unconditional: it does not
  need the growth to be by any particular amount.

### One certificate, not two

`saturatedB` moved out of `Proof/` into `RubyCore/HeapCert.lean` and **into `heapOkB`**. Both moves
are for the reason `heapOkB` was put there in the first place: the probe must compute *the* predicate
the theorem is about, not a copy that can drift. `HeapOk` is now `TableOk ∧ NoHook ∧ Saturated`,
`heapOkB_sound` covers all three, and `check_sound_withPrelude`'s hypothesis is still **one Bool about
the machine in hand** — it just decides one more clause. `scripts/heapok_probe.lean` reports it;
`scripts/ancestors_probe.lean` keeps the per-class diagnostic and the record that the *descent* route
is false.

### What it cost, and what it did not

24 `inv_*` call sites gained a hypothesis and three `Inv` literals gained a component — mechanical,
and the build tells you where. Nothing about the fragment changed: `Saturated` is not a restriction on
programs. **No program can make it false** (nothing in the object model builds a cyclic `include`),
but nothing in the `Heap` *type* forbids one, which is exactly why it is a clause and not a theorem.

The `#guard_msgs` axiom guards earned their keep: the intermediate states of this commit had
`sorryAx` in `check_sound`, and the docstring mismatch said so on the next build rather than at the
next audit.

### Verification

`Proof/`, `HeapCert.lean` and two scripts. `HeapCert.lean` *is* linked into `rubycore`, but nothing
calls `heapOkB` on the execution path — it exists for the probes — so `--check`'s answer still cannot
move; the binary's behaviour is unchanged by a new unused `def`. `check-proofs.sh` green and
axiom-clean; `heapOkB` (now including saturation) and both probes true at the booted heap; tier-0 flat
at 992 agree, 0 disagree.

## L149 — the invariant survives an allocation, which is the producer's case minus the rule

`inv_grow_value`: **if `Inv` holds and a step allocates a plain object while leaving frames, stack and
`kont` alone, `Inv` holds afterwards.** That is the producer's consecution case with the rule removed,
and therefore the statement that says how much of the producer was never about the producer.

Every conjunct falls to a lemma of its own rung, which reads as a summary of items 2–5:

| conjunct | discharged by | rung |
|---|---|---|
| `DeclsOk` | `DeclsOk_grow` | L147 — class-indexed resolution |
| `NoHook` | `NoHook_grow` | this commit |
| `Saturated` | `Saturated_grow` | L148 |
| `FramesOk` | `FramesOk.heap_congr` ∘ `typeAgree_of_plainGrow` | L143 / L145 |
| `CtlOk` | `KontOk.heap_congr` ∘ the same | L143 / L145 |

The produced value's type is read in the **new** heap, which is the whole reason the transport had to
be relativized rather than proved unrelativized (L143): the fresh object has no type in the old one.

### `NoHook` gained a clause, and it is the same clause a third time

`NoHook` is `lookup h (.ref Boot.objectId) "method_added" = none`, and `lookup` on `Object` is a walk
from `classOf h (.ref Boot.objectId)` — which `PlainGrow` pins only for ids the old heap had. So
without `Boot.objectId < h.objs.size` the pathological case where `Object` *is* the id being allocated
is not excluded, and the hook lookup could change under an allocation.

So `NoHook` is now `Boot.objectId < h.objs.size ∧ lookup … = none`. That is the fourth instance of the
pattern L147 named (after `plainRecv`'s three): **the condition goes where the judgement can see it,
not where the use site would have to derive it.** `heapOkB` decides it, the boot heap satisfies it by
`decide`, `defineMethod` preserves it because `set!` does not resize, and an allocation preserves it
because sizes only grow.

### What the producer still owes, and it is now only what a rule can owe

1. the rule in `infer` (a type for `Class#new`/`.new`, and the fragment clause admitting it);
2. its consecution case: that the step lands in a machine `PlainGrow`-related to this one with frames,
   stack and `kont` untouched — `plainGrow_alloc` supplies the heap half for a non-class
   `Heap.alloc` — and that the value it produces has the type the rule assigns;
3. `Class#new` is not the only shape: `classDef` allocates a **class**, which breaks `PlainGrow`'s
   third clause and needs the relativized shape agreement (`AncestorsGrow.lean`'s header; the clause it
   needs is measured true, 0 out-of-bounds edges).

None of that is a transport, an invariant clause, or a heap fact. That is the whole result of items
2–5.

### Verification

`Proof/`, `HeapCert.lean`, one script. `check-proofs.sh` green and axiom-clean (the audit now names
`inv_grow_value`); `heapOkB`, `heapok_probe`, `ancestors_probe`, `alloc_probe` all green at the booted
heap; tier-0 flat at 992 agree, 0 disagree.

## L150 — three lemmas the producer's arc left behind

Hygiene, and the reason it is an entry rather than a silent tidy: **a lemma with no consumers is not
neutral.** It is a statement the next reader will find by grepping, and each of these three is *weaker*
than the thing that replaced it, so finding it is worse than not finding it.

* ~~`ResolvesTo_defineMethod`~~ — L147 moved its only caller (`DeclsOk_defineMethod`) to
  `ResolvesAt_defineMethod`. The receiver-shaped *predicate* `ResolvesTo` stays, because
  `entry_dispatch` reads it through `EntryOk.resolves`; nothing transports it any more.
* ~~`shapeAgree_alloc_nonClass`~~ (L144) — `plainGrow_alloc` (L145) says strictly more about the same
  step: the whole `classPayload?` function agrees, not only its `clsShape`. Two lemmas about one step,
  one of them weaker, is how a reader ends up proving the weaker thing.
* ~~`lookup_eq_lookupIn`~~ (L147) — a `rfl` bridge whose content is already in `ResolvesAt`'s docstring
  and whose *used* form is `resolvesTo_of_resolvesAt`.

Also fixed in `homebrew/HANDOFF.md`: constraint 2 cited `ResolvesTo_defineMethod`, which now does not
exist, and its argument is one step different after the class indexing — a class-relative
`declaresName` would have to say *the defining class is not among `k`'s ancestors*, which is
heap-dependent for the same reason as before. **L147's class indexing did not help there**, and that is
worth a sentence because the natural assumption is that it would.

Nothing else moved: `check-proofs.sh` green and axiom-clean, all three probes exit 0, tier-0 flat at
992 agree / 0 disagree. `Proof/` only.

## L151 — a producer at last, and it is the string literal rather than `C.new`

**The accept rate moves for the first time since F0.** `--check` over the 1,227 cached bootstraptest
ASTs goes **21 accept / 1,204 unknown / 0 reject → 36 accept / 1,189 unknown / 0 reject**: fifteen
programs, every one of them `unknown → accept`, none the other way. Five rungs of transport and
invariant work were inert on purpose; this is the first that is not, and the twelfth check is what
says so rather than an argument.

**The producer is `.str`, and choosing it over `C.new` is the whole content of the commit.**
`HANDOFF.md` §The next commit named `C.new` and priced it as *a rule plus a consecution case*, with
everything around it proved. Reading the interpreter against that plan says it is four further rungs,
none of them the producer:

1. **A class object has no `ValueTy`.** `evalExpr` on `.send (some (.const "C")) "new" [] none`
   pushes `recvK` and evaluates the receiver first, so the machine passes through
   `.value (class object)` — and `plainRecv` is **false** on a `.cls` payload, by design, because
   that is how `entry_dispatch` refutes `invoke`'s `invokeMaybeNew` arm. `CtlOk`'s `.value` case
   demands a type there and none exists. Typing `C.new` therefore needs a **new `Ty` arm** for class
   objects before it needs a rule.
2. **`.new` is a zero-argument send**, and `infer`'s send rule matches exactly `[arg]` while `sigOf`
   matches exactly `some ([τp], τret)`. Arity generalization touches every rule that reads `sigOf`
   plus the `recvK`/`argsK` constructors and their consecution cases — plausibly larger than the
   producer it is in service of.
3. **`newImpl`'s plain-object branch is guarded by facts about the class**, not about the send:
   no user `initialize` (else `invoke` intercepts and pushes a frame), no
   Exception/String/Array/Hash/`Class`/`Module`/`Random`/`Regexp`/payload-core ancestor, no user
   `self.new` on the eigenclass. Each is heap-dependent, so by this file's own four-times-measured
   rule they belong in the judgement — a `newableCls` predicate — not at the use site. Note a `def`
   can falsify it, so `infer`'s `def` rule would owe `name ≠ "initialize"` the way it already owes
   `name ≠ "method_added"`.
4. **`class'` is still behind the unproved clause** L149 named (*no in-bounds object has an edge
   pointing out of bounds*, measured true at 0 edges).

A string literal has none of that. `Builtins.allocStr` is one `Heap.alloc` of
`{ klass := Boot.stringId, payload := .str s }` — a single non-class allocation, no constant read, no
send, no dispatch, no continuation. So `plainGrow_alloc` supplies the step and `inv_grow_value`
(L149) supplies everything else, and the consecution case is **six lines**. That the case is this
short is the measurement L143–L149 were for.

**What the rule owes, and the one clause it needed.** `infer` types `.str _` at `.cls "String"` — a
claim about a *name* — while the step allocates an object whose class is the *id* `Boot.stringId`.
Something must join the two, and the invariant is where it is cheapest: **`StrClsOk`** —
*`Boot.stringId` is a class, and it is named `"String"`* — is `Inv`'s fourth heap conjunct, the same
put-the-condition-in-the-judgement move as `NoHook`'s bound (L149) a fifth time. Two halves, and
neither implies the other: `className` answers `"Object"` at an id that is not a class, so the name
clause alone is satisfied by an *absent* `String`, while `plainRecv` separately needs the allocated
object's class to *be* a class. Preserved by `defineMethod` (`setClassPayload` keeps the payload a
`.cls` with its name) and by `PlainGrow` (which pins `classPayload?` at every id, needing neither the
bound `NoHook_grow` needs nor saturation), decided by `heapOkB` — which is now eight conjuncts — and
true at the prelude-booted heap, measured rather than argued.

**`valueTy_alloc_fresh` is stated once for every producer that follows.** It is the *value* half
`inv_grow_value` deliberately left to the rule — `hv`, read in the **new** heap — and every producer
owes exactly it, differing only in which `klass` and payload it pushes. Its payload hypothesis is
three refutations rather than `plainRecv`'s own `match`, and the reason is worth carrying: **a
`match` written in a statement elaborates to a fresh matcher constant and will not `rw` against the
one the definition was compiled with.** Case-splitting the payload is the shape that composes, and it
is what `entry_dispatch` already does with the same three shapes.

**What the fifteen programs are, said plainly because the number flatters.** They are bare or
near-bare string literals (`?a`, `" "`). The corpus has no richer in-fragment program to offer,
because the fragment still has no blocks, no `def` body that returns a String and no method call on
one — so the binding constraint on the accept rate is the *rest* of the fragment, not the producer.
The rung's value is that the class arm of `Ty`, the `.ref` arm of `valueTy?` and the class arm of
`declFor` now have an inhabitant at all: `egStr`/`egStrSeq` in `Proof/StaticSoundness.lean` are the
first safety theorems about a heap the program itself grew, and `egStrSeq` is the first program that
transports a stored `ValueTy` fact across an allocation rather than across a `rfl` — which is
L143–L149's arc, run.

**No new rows.** `declFor baseDecls (.cls n) mname = none` (`declFor_baseDecls_cls`), so the produced
value can be assigned and passed and cannot be a receiver — the "land it inert" discipline
`HANDOFF.md` asks for, applied to a producer that is not `C.new`. A String row is *not* the obvious
next step and the reason is a third finding: `ConformsAt` would have to hold for **every** plain
receiver of a class merely *named* `"String"`, in **every** heap, and `Ty.cls` pins the name without
pinning the payload — so `String#==` conformance is false as stated, not merely unproved.

## L152 — zero-argument sends, and the first row whose arity is not one

The second of the four rungs L151 found in front of `C.new`, and the one that is independent of the
other three: `infer` types `.send (some r) m [] none`, `KontOk` gains `recvK0`, and `baseDecls` gains
`Integer#zero? : [] → Bool` so the machinery is exercised rather than merely present.

**A zero-argument send is a different *number of steps*, which is why it is a separate constructor.**
With an argument, `applyKont`'s `recvK` pushes an `argsK` and the dispatch happens a step later; with
none, it runs `startArgs … [] []`, which is `finishSend` — so the send completes **in the `recvK`
step itself** and the continuation must already be typed at the return type. `recvK0` therefore has
no `ValueTy` stored in it and, alone among the send constructors, does not read the heap.
`entry_dispatch` needed no change at all: it was already stated over an arbitrary `args`, and
`ValuesTy _ [] []` is `trivial`.

**`sigOf_declFor` was generalized from `[τp]` to any `params`** rather than duplicated — the two
cases are the same proof, and a second copy is the kind of near-duplicate L150 was about.

**Picking the row is where the measuring was.** Two independent constraints, and each rules out a
different candidate:

* **Constraint 2** — `declaresName` is name-global, so every row refuses `def <name>` *program-wide*.
  `def zero?` appears in **0** of the 1,227 bootstraptest programs, measured before the row was
  written rather than after the ratchet was run.
* **Resolution** — `ResolvesAt` requires `fromPrelude = false`, and `prelude/prelude.rb` defines
  `abs` **twice**. An `Integer#abs` row would be witnessable at the boot heap and *not* at the
  prelude-booted one, so it would pass `check_sound` and fail `check_sound_withPrelude`. Check both
  before adding a row; `scripts/heapok_probe.lean` now reports the fourth name so the second
  constraint is visible rather than rediscovered.

**Arity is carried by the declaration, not by the builtin.** `Integer#zero?` matches on the receiver
and ignores `args` entirely (`Builtins/Numerics.lean:296`), so `1.zero?(5)` runs fine in the model;
it is `params := []` plus `infer`'s new arm that make it `unknown`. There is an `example` pinning
that, because the alternative reading — that the builtin enforces arity — is the one a reader will
assume.

**Inert on the corpus, and that is the honest report.** `--check` is byte-identical to L151's
36 accept / 1,189 unknown / 0 reject: no bootstraptest program calls `.zero?` inside the fragment,
and — the part worth checking rather than assuming — **no program regressed** from the new
`declaresName`. The rung is exercised by `egZero` (`(1 + 2).zero?`), which is also the first accepted
program whose type comes from a declaration with a return type unlike its receiver's.

`entryOk_int_nullary` is `entryOk_int` with `ValuesTy` pinning the argument list to `[]` and the
return type a parameter. Note `f` must be given explicitly at the call site: elaborating the
`ValueTy _ (f x) τret` hypothesis first leaves it an undetermined metavariable, since nothing in that
statement pins the function.

Checks: check-proofs.sh green and axiom-clean, four sections plus the new `zero?` and `StrClsOk`
lines; three probes exit 0; tier-0 992/0.

## L153 — `NoHook` at every class, and the indexing that measurement chose

The third of the four rungs in front of `C.new`, and a prerequisite for `class` rather than for
`.new`: L149's `NoHook` fixes the receiver at `Boot.objectId`, which is all a fragment with no
`class` can ever define into. A class body's `def` installs on the class it is inside, so the clause
has to hold at *every* possible definee.

**The generalization has two candidate shapes and only one of them is true.** Forty lines of `IO`
against the prelude-booted heap, before writing any proof — the seventh session's lesson, applied
again:

| candidate | reading | at the booted heap |
|---|---|---|
| `∀ k, isClass k → lookup h (.ref k) "method_added" = none` | receiver-indexed: the walk `evalExpr` actually performs, through `k`'s **eigenclass** chain | **true**, 0 of 105 |
| `∀ k, isClass k → lookupIn h k "method_added" = none` | class-indexed: `k`'s own **instance** chain | **false** — 1 of 105 |

The counterexample is **`T::Sig`, which defines `method_added` as an instance method** — because
that is precisely how `sorbet-runtime` installs a `sig` (D9/D10; `T.__wrap`'s comment says so). It
does not fire, because the hook lookup is receiver-indexed at the class object and `T::Sig` is not on
any class object's eigenclass chain; but the class-indexed *statement* is false about it.

**This is L147's lesson with the answer the other way round, and that is the point.** L147 said: when
a clause quantifies over the values a type has, ask whether its content depends on the value or only
on its class — and there the answer was *the class*, which is why `ResolvesAt` exists. Here the answer
is *the receiver*, because a class object's dispatch chain is its eigenclass and not itself. **The
rule is to ask the question, not to prefer the answer**; picking by analogy with the last rung would
have produced a false clause, and the thing that caught it was running the predicate rather than
attempting the proof.

**What the shape buys.** `NoHook_grow` gets *shorter*: `PlainGrow` pins `classPayload?` at every id,
so the set of class objects is unchanged and there is **no fresh-id case at all** — where L149 needed
an explicit bound to rule out the pathological case of `Object` being the id allocated. The first
conjunct, `Object` is a class, replaces that bound with a strictly stronger fact at the same price:
it is what lets the `def` case *instantiate* the quantifier at the definee a toplevel `def` uses, and
being a class implies being in bounds (`classPayload?_isSome_lt`). Fifth time that trade has been
priced and taken.

`noHookB` reflects the clause into a `Bool` — bounded over `List.range h.objs.size`, sound because
`classPayload?` answers `none` out of bounds so every id outside the range is vacuous — and it
replaces the two literal conjuncts `heapOkB` had. `initiation` now goes through `noHookB_sound` at a
literal heap, the same shape `Saturated` has had since L148, rather than through one `rfl`.

`noHookB_sound` lives in `Proof/Static/Decls.lean` next to `NoHook`, **not** in `PreludeInv.lean`
beside its `saturatedB` sibling: `PreludeInv` imports `StaticSoundness`, and `initiation` needs the
lemma.

Checks: check-proofs.sh green and axiom-clean, with the probe now reporting the clause as a count of
offenders rather than one `Object` line; three probes exit 0; `--check` **byte-identical** to L152
over the 1,227 cached ASTs (36 accept / 1,189 unknown / 0 reject) — owed because `HeapCert.lean` is
linked into `rubycore`, so it was run rather than argued; tier-0 992/0.

## L154 — the frame's definee becomes a predicate, and a class body becomes expressible

`FrameConforms` carried `f.defmod = Boot.objectId`, with a comment saying why: *the definee is
`Object` for every frame in the fragment (no `class`, no `module`)*. True, and it makes a class-body
frame **inexpressible** — `enterClassBody` pushes a frame whose `defmod` is the class being opened,
so no amount of work on `class'` could have produced a machine `FramesOk` accepts. This is the last
of the four rungs L151 named that is *not* about allocation.

**The replacement is `(h.classPayload? f.defmod).isSome`, and it was found by reading what the
hypothesis was used for rather than by asking what would generalize.** The equation had exactly one
consumer — the `def` case, which used it to instantiate `NoHook` at the definee. L153 made `NoHook` a
quantifier over class objects, so what the `def` case needs of the definee is now precisely *that it
is a class*, and nothing else. Every other `defineMethod` lemma the case invokes — `DeclsOk`,
`Saturated`, `StrClsOk`, `TypeAgree` — was already stated `∀ cls` and needed no change at all. The
two rungs are one move split in half: generalize the clause, then generalize the thing that
instantiates it.

**It transports for free.** The new conjunct rides on `TypeAgree`'s **third** component — the
`classPayload?`-isSome agreement that has been there since L141 for `TyClass` — and the bound that
component needs comes from the clause itself, since `classPayload?` answers `none` out of bounds.
So `FrameConforms.congr` grows one rewrite and `FramesOk.heap_congr` is untouched.

Two places needed a hand where `simp` had been enough, and both are the same phenomenon — **a
predicate does not reduce where an equation did**:

* `FramesOk.setLocal`'s definee goal was `show (curFrame m).defmod = Boot.objectId`, closed by
  definitional unfolding. The `classPayload?` form sits under `setLocal`'s structure-update literal
  and will not `show`; rewriting backwards through `curFrame m = frames.getD fid default` is what
  composes. (L137's lesson about structure-update literals, in a new place.)
* `initiation` needs one `decide` — `Object` is a class at the boot heap — and `initiation_on` needs
  `NoHook`'s **first conjunct**, which is exactly what that conjunct was added for one rung earlier.

Inert in both artifacts: `--check` byte-identical to L153 (36 accept / 1,189 unknown / 0 reject), and
no rule, prelude line or front-end file moved. What it buys is not a verdict but a *shape*: the
invariant can now describe a machine whose current frame is a class body, which is the precondition
for `class'` having a consecution case at all.

**What is left for `class C; end`, priced by reading rather than by attempting** — the allocation
side, entire:

1. `TypeAgree`'s first clause relativized to plain receivers. `eigenclassOf` materializes eigenclasses
   on classes, and `classOf` reads `eigen`, so the clause is **false** as stated for a class that
   gains one. Only plain receivers ever need it (`ValueTy.congr`), so this is L143's relativization
   again, one clause along.
2. A `ClassGrow` relation. `PlainGrow`'s third clause — *nothing anywhere became a class* — is
   exactly what `class'` violates, and `ancestors_congr` under the weaker relation needs the
   *no in-bounds object has an edge pointing out of bounds* clause `scripts/ancestors_probe.lean`
   measures at **0** and nobody has proved.
3. `enterClassBody` allocates **more than one object**: the class, then `eigenclassOf`'s metaclass
   chain, which may realize eigenclasses for superclasses too. The transport is not a single `alloc`.
4. The reopen and `TypeError` branches. `constOwn h defmod name` may answer a non-class, and that
   branch is `raiseErr` — a `.jump`, which `CtlOk` refuses outright. Ruling it out needs a
   program-indexed heap clause in the D10 style: *for each class name the program defines, the
   enclosing namespace's constant of that name is absent or is a non-module class*. Absent is **not**
   preserved (the step sets it), so the disjunction is the weakest form that is.

## L155 — the toplevel-position flag, and the fact that makes it mean something

`homebrew/HANDOFF.md` §What is left item 4 wanted a *program-indexed heap clause* ruling out
`class'`'s `TypeError` branch. Reading `enterClassBody` (`Interp/Dispatch.lean:219`) against that
plan turns up something the plan had not separated: the branch is chosen by
`constOwn m.currentFrame.defmod name` — a lookup in the **current definee's own** constant table,
"NOT a flat toplevel lookup and NOT the full lexical cref chain", as the comment there says in as
many words. So before any clause about *which* constant, the invariant owes a clause about **whose
table**, and the only definee whose constant table an invariant can describe is `Object`.

That makes `class` a rule admissible in a **toplevel position and nowhere else**, and `infer` had no
way to tell the two apart. This commit gives it one, and gives the invariant the matching fact. It
is inert: no rule reads the flag yet.

**The flag is a parameter, not an index, and that is the whole content of the commit.** `infer`,
`inferSeq`, `inferIf` and `LoopOk` gain `(top : Bool := false)`; `check` passes `true`; `CtlOk` and
the four expression-storing `KontOk` constructors read the mode as **`Γs.isEmpty`** — the
environment stack the judgement already carries. `frameK` is the constructor at which that stack
pops, and it is *already* the constructor at which the definee changes, so the mode flips in exactly
the right place with no new index and no new constructor.

**The alternative was costed and rejected.** A genuine `Bool` index on `KontOk` needs, at the
`frameK` **pop**, the *caller's* definee — which `KontOk` cannot see, because it is indexed by
environments and not by frames. Recovering it costs a stack-*depth* index, and `Γs.length` already
is that index. Naming the mode `Γs.isEmpty` is the same observation taken seriously, and it is L147's
question asked of a different clause: *what is this actually indexed by?*

**What forced the propagation rule, which is not the one I first wrote.** The first version threaded
`top` through `.seq` only, on the theory that a `class` inside an `if` is not worth admitting. That
does not typecheck, and the reason is structural rather than a matter of taste: `CtlOk` reads the
mode off the environment stack, so a subexpression the machine evaluates **without pushing a frame**
is read back at the *enclosing* mode — and if the rule checked it at `false` while `CtlOk` demands
`Γs.isEmpty`, the two disagree at the toplevel and `inv_push` cannot be applied. So the flag
propagates through every subexpression evaluated in the same activation (`vasgn` rhs, `if`/`while`
condition and branches, send receiver and argument) and is blocked at exactly the two that are not:
a `def` body and, next commit, a class body. **The split is forced by where the machine pushes a
frame, which is the only place it could have been.**

* **`BottomObj` is `Inv`'s fifth conjunct**, and the first that is not about the heap: *the outermost
  activation's definee is `Object`*. `CtlOk`'s mode is `Γs.isEmpty`; `FramesOk` forces the
  environment stack and the frame stack to have equal length, so an empty tail means a **singleton**
  frame stack; and `BottomObj` names that frame's definee. Composed — `BottomObj_curFrame` — that is
  *toplevel mode ⇒ the definee is `Object`*, which is precisely what `constOwn` needs pinned.
* **It is its own recursion over the stack rather than a clause of `FramesOk`.** `FramesOk`'s
  four-way destructuring has nine consumers and a fifth conjunct in its `cons` arm would churn every
  one of them for a fact none of them uses. Three transport lemmas (`BottomObj_congr` over a `set!`
  that preserves definees, `_push`, `_cons`, `_tail`) cover every way the fragment touches
  `frames`/`stack`, and none mentions the heap — so the four heap-writing cases pay nothing.
* `FramesOk.mem_lt` is new and is the only thing the `push` transport needed: `BottomObj` reads
  frames by id, and a `push` leaves those reads alone exactly when the ids are already in bounds.

Verified inert: `--check` **byte-identical** over the 1,227 cached bootstraptest ASTs (36 accept /
1,189 unknown / 0 reject) against the pre-commit binary — owed here rather than argued, because
`Types/Core.lean` *is* linked into `rubycore`. `check-proofs.sh` green and axiom-clean; tier-0
**992 agree, 0 disagree**.

## L156 — reopening a class, and the first accepted program with a class body in it

The rung `homebrew/HANDOFF.md` priced at "five to eight commits" for `class C; end`, taken by the
**branch it did not separate out**. `enterClassBody` has three (`Interp/Dispatch.lean:236`):

| branch | condition | what it does | can `Inv` survive it? |
|---|---|---|---|
| **reopen** | `constOwn defmod name` is a class of matching kind | `pushFrame`, **no heap write at all** | yes — this commit |
| `TypeError` | it is something else | `raiseErr`, a `.jump` | no: `CtlOk` refuses `.jump` outright |
| allocate | it is absent | `alloc` + `constSetIn` + `eigenclassOf` | not yet: `PlainGrow`'s *nothing became a class* |

HANDOFF's four-item list is **entirely about the third**, and reading the second and third against
the first is what showed the first is one commit rather than a share of eight: the reopen branch
writes no heap, so all five heap conjuncts carry across by `rfl` and what remains is a frame push.
This is L151's lesson at a different rung — *when a rung is blocked, ask what else satisfies the same
obligation*. The obligation was "put a class body in the fragment"; reopening satisfies it and skips
the allocation side entire.

**What the rule is, and why each of its three side conditions names a branch rather than a taste.**
`infer` admits `.class' name none body` when `top` (L155 — the reopen lookup is the *definee's own*
constant table, and `Object`'s is the only one `Inv` describes), when there is no explicit superclass
(which would evaluate first through `classDefK` and then have to *match*, a `raiseErr` if it does
not), and when `name ∈ reopenableClasses`. The type is the **body's** type and the environment is the
caller's, because the class body runs in its own frame and `frameK` hands its value back.

* **`reopenableClasses` is a table, and every row is a proof obligation** — `baseDecls`'s discipline
  applied to a second kind of promise. `ClassOk` is what `Inv` carries, `classOkB` is what the
  certificate decides, and widening the list is a row plus a `decide`. `String` is the one entry
  because it is the only ground class the fragment can currently *produce a value of* (L151), so it
  is the only one where reopening will eventually buy a call site.
* **`ClassOk` is the D10-shaped program-indexed clause, in the only form that is preserved.** Not
  *absent or a non-module class* — HANDOFF proposed that disjunction and it is right that "absent" is
  not preserved — but **present and a non-module class**, which is what the reopen branch needs and
  what every step in the fragment leaves alone. Dropping the disjunct is what makes `ClassOk_grow`
  and `ClassOk_defineMethod` one-liners.
* **The `defineMethod` case is the one that is not free, and it is the case that matters**: a `def`
  in the body of the very class being reopened. `constOwn` reads `consts`, `defineMethod` writes
  `methods`, and `clsShape` does not carry `consts` — so `consts_defineMethod`/`constOwn_defineMethod`
  are new. Deliberately *not* a fifth field of `clsShape`: `ShapeAgree` is `ancestors_congr`'s
  **hypothesis**, so widening it would oblige every caller to supply agreement about a field the
  ancestor walk never reads.
* `isModule` needed no new lemma — `clsName_defineMethod` already carries it, because L124 put it
  there for the anonymous-class fallback. Reused rather than reproved, which is the L154 habit
  (read what a hypothesis already gives you before writing another).

**The consecution case is eleven lines**, and the shape is worth reading as the measurement L155 was
for: `infer_class_inv` hands back the mode, `FramesOk.stack_singleton` turns it into a singleton frame
stack, `BottomObj_curFrame` turns that into `defmod = Object`, `ClassOk` collapses the three-way
branch to `pushFrame`, and `KontOk.frameK` — which has existed since P0a and until now only ever
popped a *method* — types the class body's return with no change at all.

**Inert on the corpus, not inert in capability, and the distinction is the finding.** `--check` over
the 1,227 cached bootstraptest ASTs is **byte-identical** (36 accept / 1,189 unknown / 0 reject).

~~none of those programs reopens a core class~~ — **withdrawn, and measured instead.** That
explanation was inferred from the flat diff rather than checked, and it is wrong: **26** bootstraptest
programs reopen a core class and **7** reopen `String` specifically. They stay `unknown` for the
reason L151 already established — everything *around* the class body. `test_flow_004.rb` is the
representative case: it reopens `String` with a one-line `def`, then calls `''.respond_to?`,
`.lines.map { … }` with a block, and `break`. The binding constraint on the accept rate is the rest
of the fragment, not the class rule, which is exactly what L151 said about the string literal.

The general point, since this is the second time it has cost something: **a flat diff is evidence
that no verdict moved, and nothing more.** Attributing it to a property of the corpus is a separate
claim and needs a separate measurement — `grep -lE '^\s*class (String|Integer|…)' corpus/*.rb` is
the whole of it.

So the rung is witnessed by `egClassBody` in `StaticSoundness.lean` instead —

```ruby
class String
  def shout
    1
  end
end
```

— which is **the first program the checker accepts that has a class body in it**, and therefore the
first whose accepting run passes through a frame that is not the toplevel one. L151's lesson said an
accept-rate number flatters and you should report what the programs are; its converse is that a *flat*
number can hide a capability, and the answer is the same — put the program in the build.

What it still does not buy is the call: `"hi".shout` needs a row for `String#shout`, a row obliges
`EntryOk`, and `EntryOk` can today only be witnessed by a **builtin**. That is constraint 1, it is the
next commit, and this rung is what makes it reachable — a public user method on a class the fragment
can produce a value of, which is exactly what a toplevel `def` (private, on `Object`) cannot be.

`check-proofs.sh` green and axiom-clean, `heapOkB` — now including `classOkB` — still true at the
prelude-booted heap; tier-0 **992 agree, 0 disagree**.

## L157 — `EntryOk`'s user arm: the send that pushes a frame, and the prerequisite nobody had named

`HANDOFF.md` §constraint 1 — *`EntryOk` can only be witnessed by a builtin*, "the item on the most
paths, larger than any single item" — paid, as machinery. It lands **inert**, for a reason that is
this commit's real finding and is stated in full below.

**What the constraint actually was, in the code.** `ResolvesAt` pins `md.builtin = some bid` and
`ConformsAt` concludes `Builtins.run bid recv args m = .ok w m` — the machine back unchanged, in one
step. A method with `builtin = none` reaches `enterUserMethod`, which **pushes a frame**: the send
produces no value at all. So for any user or prelude method `EntryOk` was not unproved but **false**,
and the repair is a disjunction rather than a generalization.

* **`ResolvesUser`** is the user resolution clause, and every conjunct is a gate on `invoke`'s path
  to `enterUserMethod`, read off `Interp/Send.lean` in order — `builtin = none`, `undefined = false`,
  `visibility = .pub` (`visError?` at an `.explicit` site), the `crubyShadow` between-classes gate,
  and then three clauses that are not gates but *frame* obligations: `params = []` and
  `declared = []` (so the callee's environment is `[]`), `capturedFrame = none` (`FrameConforms`'s
  first clause), and `(classPayload? md.owner).isSome` (its definee clause, since the activation's
  `defmod` **is** `md.owner`).
* **`fromPrelude` is absent, and that is the point.** `ResolvesAt` needs `fromPrelude = false`
  because a prelude method has no `bid` to run. The user arm has no such need — a prelude-Ruby method
  *is* a `MethodDef` with `builtin = none` and passes every gate above. So D8's dominant category
  (`widening-the-fragment.md` §5.1: 153 of 285 prelude methods, 269 after F5) is now **expressible**,
  where `HANDOFF.md` recorded it as inexpressible.
* **`UserConforms` is the reflexive step**, and it is worth naming as one. Every obligation the
  invariant has carried until now is a fact about a Lean builtin, proved once and externally. This
  one is `infer D [] md.body = some (d.ret, _)` — the **checker's own verdict on a method body**, as
  a conjunct of its own soundness invariant. Sound (the recursion is on the heap, not on the proof)
  and unavoidable: the fact a user witness asserts is not about one step, so it cannot be a lemma
  about `startArgs` the way `ConformsAt` is.
* **`user_dispatch` is `entry_dispatch`'s sibling and had to be a second lemma**, exactly as
  §constraint 1 predicted: same hypothesis shape, different `StepResult`. It cost two things worth
  recording. The `simp` that unfolds `invoke` **and** `enterUserMethod` in one go exhausts the
  heartbeat budget — a nest of gate `match`es times a hundred lines of parameter binding — so the
  proof reduces the dispatch to a *named call* first and unfolds the callee second; each stage's
  search space is then small. And `crubySingletonShadow`, the gate three rungs have now predicted
  would come back on an object receiver, is free for the **third** time: it answers `none` unless the
  payload is `.cls`, which `plainRecv` refutes.
* **The unary send case refutes the user arm by arithmetic**, not by anything about dispatch:
  `UserConforms` requires `d.params = []` while the `argsK` declaration's is `[τ]`. A one-argument
  send is a builtin send, necessarily, until `enterUserMethod` binds parameters in the fragment.

**The finding: a program-supplied declaration is unsound without flow-sensitive declarations, and
that is why `declsOf` has had to be a constant function for four rungs.**

`Types/Decls.lean` has said since F1a that `declsOf` is "a function of the program, and constant
today", with F1b's `def` and W8's `sig`s named as what would make it non-constant. Making it
non-constant is not deferred work — **it is unsound as the invariant is currently shaped**, and
nothing in `PLAN.md` or `HANDOFF.md` records this:

    initiation : check p = .accept → Inv (declsOf p) (Machine.init p)

`Inv` carries `DeclsOk (declsOf p) m.heap`, and `Machine.init p`'s heap is `Boot.initHeap`. A row for
`String#shout` synthesized from the program's own `class String; def shout; …; end; end` obliges
`EntryOk` **at the boot heap**, where `lookupIn Boot.initHeap Boot.stringId "shout"` is `none`. The
obligation is false, `initiation` is unprovable, and no amount of work on the *witness* changes it —
the method does not exist until the program's own `def` step installs it, which is many steps after
`Machine.init`.

So the row cannot be a constant of the program; it has to come into force **at the step that
installs the method**. `infer` already threads exactly this kind of thing — `Γ` is flow-sensitive
because a local has no type until it is assigned — and a declaration is the same shape of fact one
level up. The change is to thread `Decls` in *and out* of `infer` beside `Env`, index `KontOk` by
the pair, and let `Inv` quantify the current table; the `def` step then both installs the method and
adds the row, and the row is satisfiable precisely because the method was just installed.

Two things that pricing turned up and that the next rung should not rediscover:

1. **`infer` is not monotone in `D`.** Adding a row makes `declaresName` true, which *refuses* a
   `def` of that name. So "the callee saw a smaller table" is not automatically a weakening, and the
   frame-return case needs care.
2. **The row is class-name-indexed, so it obliges *every* class of that name.** `TyClass h (.cls n) k`
   quantifies over classes named `n` (L147's class indexing, which is right for the reason L147
   gives). A `def` installs on one class object. So a program-supplied row also needs a **uniqueness**
   clause — *the class named `n` is unique* — which is decidable at both heaps and is a natural
   sibling of `ClassOk`. This is `HANDOFF.md` §Known-wrong-answers 2 arriving from a new direction:
   the declaration table's *key* is the fragile part.

**Verification.** The user arm is currently uninhabited — nothing constructs a `UserEntryOk` — so the
commit accepts no new programs, and `--check` over the 1,227 cached bootstraptest ASTs is
**byte-identical** (36 accept / 1,189 unknown / 0 reject). (L156's note carries a correction that
applies here too: the flat number is *not* evidence that the corpus lacks the construct.) That is L141's shape exactly: the
machinery lands, proved, one rung before the thing that inhabits it. `check-proofs.sh` green and
axiom-clean; tier-0 **992 agree, 0 disagree**.

## L158 — `--check`'s displayed type was computed by a second, un-flagged call

A one-line repair, recorded because the shape of the defect is worth knowing. `Main.lean` computes
the verdict with `Types.check prog` and the *displayed type* with a separate
`Types.infer (declsOf prog) [] prog`. L155 gave `infer` a `top` flag that `check` passes as `true`
and the default leaves `false`, so the two calls silently diverged: `class String; def shout; …; end`
returned `{"verdict":"accept"}` with **no type**, because the display call refused the very rule the
verdict call had used.

No soundness or verdict consequence — the field is documented as a development aid and explicitly not
a difftest signal — and no corpus figure moves (`--check` byte-identical, 36 / 1,189 / 0), because
the flag can only *add* acceptances and no bootstraptest verdict moved. But it is the kind of defect
that reads as a checker inconsistency to anyone looking at the output, which is what the field is
for.

**The lesson is about the shape, not the line.** A displayed value recomputed by a second call to the
same function is a duplicate of the decision, and a duplicate drifts the moment the function grows a
parameter. Found by being asked what `infer` does on a file with no driver code, and noticing the
class-body cases printed no type where a bare `def` printed `Symbol` — i.e. by *reading the output of
an example*, which is the same move `egClassBody` exists to enable.

## L159 — the symbol literal, and the first rung chosen by measurement

One line of `infer`, three lines of consecution, **281 slice nodes across all 8 files**, and
**36 → 38** on bootstraptest. It is the smallest rung in the initiative's history and it is the first
one picked by a measurement rather than by a plan.

`Ty.sym` has existed since P0 — a `def` evaluates to a symbol, which is what `.def'`'s rule returns —
so the type was there and only the rule for *writing* one was missing. Nothing had needed it, because
nothing had asked what the **slice** contains: `homebrew/fragment-gap.py` ranks `sym` third by node
count and joint-first by files blocked. The consecution case is the four immediate literals' case
verbatim; `evalExpr` answers `.value (.sym s)` with no heap write (`Interp.lean:127`), so the only
obligation is `ValueTy … .sym`, which is `rfl`.

Not added to `defTy`, following L151's precedent for `.str`: widening the **refutation** pass is a
separate decision under a separate guard (`reject ⇒ srb rejects` is a difftest direction, not a
theorem), and this commit claims nothing about `reject`.

**Two ratchets moved by different amounts, which is the reason to have both.** Slice blocking nodes
**3,027 → 2,746**, exactly the 281; slice method bodies fully in fragment **5 of 92, unchanged**. The
symbols are overwhelmingly in class-body `private_constant :X` calls and `sig` declarations, not
inside method bodies that were otherwise clean. A node-count ratchet measures progress through the
file; a method-body ratchet measures progress toward a *verdict*. They will disagree often and the
disagreement is information.

**And the tool needed updating in the same commit**, which is the maintenance discipline it was built
with: `SUPPORTED` is a hand-maintained copy of `infer`'s match arms, so a new rule means a new entry
*and* a new `--self-test` case. The first run after this rule landed still reported `sym` as MISSING,
which is exactly the drift the self-test exists to make loud rather than silent.

## L160 — the declaration table becomes a *threaded* judgement

`infer` returns `(Ty × Env × Decls)` where it returned `(Ty × Env)`, `KontOk` carries the
declarations as an **index** rather than a parameter, and `Inv` quantifies them existentially
instead of taking them as an argument. **No rule grows the table**, so `--check` over the 1,227
cached bootstraptest ASTs is byte-identical — 38 / 1,187 / 0, verified by diff and not by
comparing totals.

### Why this is not a refactor

`homebrew/PLAN.md`'s thirteenth-session entry recorded the finding: `declsOf` has described
itself as *"a function of the program, and constant today"* since F1a, with a program-supplied
row named as later work in two documents, and it **cannot** be that. `initiation` obliges
`DeclsOk` at the *boot* heap, and a row synthesized from the program's own `class C; def foo`
does not resolve there — the method does not exist until the program's own `def` step installs
it. So the row has to come into force **at that step**, which means the set of signatures a
call site may rely on is a function of *where in the program the call site is*.

That is exactly what `Γ` already is, and for exactly the same reason: Ruby locals are assigned
rather than declared, Ruby methods are installed rather than declared. Threading `D` beside `Γ`
is the repair, and the symmetry is the argument for it.

Three alternatives were priced and all three fail for the same reason, which is worth recording
because each looks cheaper:

1. **Scan the program up front** and hand `check` the full table. `initiation` then owes
   `EntryOk` for `String#value` at the boot heap. Unsound, and it is the original finding.
2. **Weaken `DeclsOk` to the rows that currently resolve.** The dispatch case needs `EntryOk`
   *at the call*, and can only get it from a clause the invariant carries; "currently resolves"
   is a fact about the machine, so the invariant has to be indexed by which rows are
   established — which is the threading, arrived at from the other side.
3. **Keep one fixed table and make the rows conditional.** Same thing again: the condition is
   the run's position.

### Four side conditions the shape forced, each a refusal rather than a convention

Every one of these is inert today — nothing grows the table — and every one is where the *next*
rung will break the build, which is the point (`HANDOFF.md` constraint 4).

* **`while`'s stability now covers the table.** `Γ₁ = Γ ∧ D₁ = D`, because a loop whose body
  declares a method puts a different table in force on the second iteration than the one the
  first was checked at, and there is no single index for the two loop konts. Same argument as
  `Γ`, same shape.
* **`if`'s join covers the table**, for the same reason `ifK` has one continuation.
* **A class body must leave the table as it found it.** This is the restrictive one, and it is
  restrictive on purpose: `KontOk.frameK` carries **one** table, so the frame it pushes and the
  continuation it pops into read the same declarations. The honest shape is two — a class
  body's `def`s are precisely the rows meant to escape — but the pop then owes `DeclsOk` at the
  caller's table from `DeclsOk` at the callee's, and **`DeclsOk` is neither monotone nor
  antitone in the table**: it is antitone in the *domain* (fewer rows, fewer obligations) and
  monotone in nothing, because `UserConforms` reads the table through `infer`, which
  `declaresName` makes non-monotone. That is the next rung's central problem and it is now
  stated rather than latent.
* **`UserConforms` requires the same of a method body**, and there the restriction is one we
  want anyway.

### The one place the order of `infer`'s own tests had to change

The unary send now reads `sigOf` **after** inferring the argument, not before. The three tests
are independent and each failure is `none`, so the verdict cannot move; what fixes the order is
the *continuation*. An `argsK` exists once both receiver and argument have run, so the table it
is indexed by is the one the argument left — and `KontOk.argsK`'s signature premise has to be
readable at that table. Reading `sigOf` at the earlier one makes the kont carry a fact about a
table no machine state is at, and the `recvK` consecution case cannot close.

**This is the generalizable observation of the commit**: with the table threaded, *where a rule
reads the table* is no longer free, because each continuation constructor is pinned to the
table in force at the moment that continuation exists. Two rules read a signature (`recvK0` at
the receiver's output table, `recvK`/`argsK` at the argument's) and the difference is not
stylistic.

### `SubDecls`, defined and deliberately unused

`Types/Decls.lean` gains `SubDecls F F' := ∀ τ m d, declFor F τ m = some d → declFor F' τ m =
some d` — stated over `declFor` rather than over the row lists, because the structural version
is false for the shape that matters (`declFor` on a two-class ground type demands *agreement*,
so a table can gain a row and support strictly fewer signatures). It is what the user-method
arm will want: a body is checked where it is written and called later, and re-checking it at
the bigger table is not available since `infer` is not monotone in the table.

It is **not** wired into `Inv` or `UserEntryOk`, and that is a decision rather than an
omission. The first draft of this commit put the slack in both, and the `def` consecution case
immediately failed for a reason the slack itself created: `DeclsOk_defineMethod` needs the name
undeclared in the *invariant's* table while the rule checks the *control's*, and `D₀ ⊆ F` gives
the implication the wrong way round. L145's lesson, a fourth time — **a clause that looks
necessary is a measurement, not a judgement.** Write the proof, keep the clauses it used.

### What `cases` does with an added index, since it cost half an hour

`KontOk` went from `inductive KontOk (D : Decls) : Heap → …` to `inductive KontOk : Decls →
Heap → …`, and every `cases hk with | @ctor …` alternative in `step_ok` changed arity — not by
one, and not uniformly. An `@`-alternative names **all** the constructor's fields in
declaration order, including those unification will discard; adding an index shifts every
name. The observable symptom is a binder silently taking the wrong field (`es : List Expr`
becoming `es : Decls`) and an error three lines later about something unrelated. Reading the
goal display in the failing case — which prints the introduced binders *with their types* —
is what settles it in one look; guessing the arity from the constructor's signature does not.

`KontOk.heap_congr` needed the same kind of repair for the same kind of reason: with the
declarations an index, `induction` reverts the `TypeAgree` hypothesis into the motive, so the
statement is now proved in the form that takes the agreement *after* the derivation
(`heap_congr'`) with the old signature recovered as a one-line wrapper.

### Checks

`lake build` clean; `scripts/check-proofs.sh` green and axiom-clean — `check_sound`,
`check_sound_withPrelude` and `check_sound_withPrelude'` all still
`[propext, Classical.choice, Quot.sound]`; `heapOkB`/`saturatedB` true at the booted heap;
`fragment-gap.py --self-test` all 19 cases; and the inertness diff run rather than argued,
since `Types/Core.lean` **is** linked into `rubycore`.

## L161 — `infer` is monotone in the declaration table, and that is what removes the slack

One lemma, `Proof/Static/Mono.lean`, and it is the piece that decides the *shape* of the
growing-table rung rather than a piece of it. Adds `defFree` to `Types/Core.lean` and proves

    SubDecls F F' → defFree e = true → infer F Γ e top = some (τ, Γ', F)
                                     → infer F' Γ e top = some (τ, Γ', F')

by the functional induction `infer` generates — 42 cases, no `sorry`, no fallback arm, axioms
`[propext, Quot.sound]`. Nothing calls it yet; `--check` is byte-identical (38 / 1,187 / 0).

### What it is for, and why it is the cheap route

`UserConforms` — the user-method arm of `EntryOk` — carries **the checker's own verdict on a
method body** inside the soundness invariant. That fact enters when the `def` step installs the
method and has to survive every later step, including the program's own later `def`s, which
grow the table. So preservation owes exactly the displayed implication.

L160 tried the alternative: carry the *smaller* table inside the witness, related to the
invariant's by `SubDecls`, and thread a second table through `Inv`/`CtlOk`/`KontOk`. Three
things went wrong, and the third is the one worth remembering:

1. The `def` case needs `declaresName` freshness at the **invariant's** table while the rule
   checks the **control's**, and `Fc ⊆ F` gives that implication the wrong way round.
2. `DeclsOk` is antitone in the table's *domain* and monotone in nothing, because the user arm
   reads the table through `infer`. So neither direction of a pop is free.
3. Both problems are the *same* problem seen from two ends — *is a fact proved at one table
   usable at another?* — and one lemma answers it once, where the slack answers it nowhere and
   spreads the question across three definitions.

**The generalizable form: when a design needs a fact to move between two indices, prove the
transport rather than widening the statement to hold at both.** The slack looks cheaper because
each individual site is a one-line `SubDecls.trans`; what it costs is that every site *has* to
have one, and the sites that cannot are only visible after the shape has propagated.

### `defFree`, and why the side condition is syntactic

`infer` is genuinely non-monotone at exactly one rule: `def`'s guard is
`declaresName D name = false`, which a bigger table falsifies. Every other rule reads the table
only through `sigOf`, and `SubDecls` was defined (L160) to carry precisely that. So the
hypothesis is *the expression contains no `def`* — and `class'` is excluded with it, not because
a class body is a declaration but because it **contains** them.

That is a real narrowing: a declared method's body may not define a method or reopen a class.
Ruby permits both and the slice does neither, so it is cheap on the target and it is now a
stated fragment restriction rather than an accident.

### Two mechanical findings, both about equation lemmas

* **A `def` with a catch-all arm has *conditional* equation lemmas**, so `simp [defFree]` makes
  no progress on any compound shape — the earlier-patterns-did-not-match side conditions are
  unresolved. `defFree.eq_def` unfolds to the whole `match` and loops under `simp`. The fix is
  seven hand-stated unconditional `@[simp]` lemmas (`defFree_if`, `defFreeAll_cons`, …), each
  proved by a single `rw [defFree.eq_def]`. Worth knowing before defining any predicate over
  `Expr`, since a 46-constructor inductive makes the catch-all arm mandatory.
* **`simp_all` inside a `by` that supplies an induction hypothesis's argument will rewrite the
  hypothesis itself.** In the `if` case it silently weakened `ihI`'s statement — deleting a
  conjunct of its conclusion — and the error surfaced as an unrelated unsolved goal two lines
  later. Extract the sub-facts with a named `simp only` and pass them explicitly.

### The tactic shape that made 42 cases tractable

Three uniform alternatives in a `first` chain close 30 of them: *refute the hypothesis by
computing `infer`*, *refute it using the branch facts* (`simp_all only`), and *the immediate
literals*. The remaining 12 are the rules — one per `infer` arm plus `inferIf`'s two and
`inferSeq`'s three — and they are written out. **Each alternative needs a `done`**; without it
`first` accepts a tactic that made progress and left goals, which reads as 41 failures with the
wrong error text.

And the case arities: an `@`-alternative of `cases`/`induction` names **all** the constructor's
fields in declaration order, including those unification discards. The reliable way to get them
is to read the *goal display* in a failing case, which prints the introduced binders with their
types; deriving the count from the constructor's signature does not work, as L160 also found.

## L162 — the activation stack learns its definee's *name*

`infer` gains a context parameter beside `top`, the environment stack becomes a stack of
**(class name, environment)** pairs, and `StackCtx` is the invariant clause that ties the static
name to the runtime frame's `defmod`. Inert: `--check` byte-identical at 38 / 1,187 / 0.

### Why a name, and why per frame

A declaration row is keyed on a class **name**, because `infer` cannot name an `ObjId`
(`Types/Decls.lean` has said so since F1a). So the `def` rule has to know which class it is
installing on, and the only thing that says so is the frame's `defmod` — which `FrameConforms`
knew was *a class* (L154) and nothing knew the name of.

Carried per-frame rather than for the current one, for the reason `FrameConforms` is: `frameK`
resumes a **caller's** frame, and the caller's context has to survive the pop. Pairing it into
the environment stack rather than adding a parallel index is what makes that free — the caller's
context is the second component of the list, not a fact the constructor has to be handed. The
alternative (`KontOk` indexed by a bare context, related at `frameK`) needs the pop to know a
fact the kont cannot see, which is the same shape of failure L160's `SubDecls` slack had.

`FramesOk` and `BottomObj` are **untouched**: `Inv` hands them `Γs.map Prod.snd` and `StackCtx`
`Γs.map Prod.fst`. That is `BottomObj`'s own docstring taken as advice — a further conjunct in
`FramesOk`'s `cons` arm would churn nine lemmas for a fact none of them uses.

### The finding that changes the plan: a toplevel `def` cannot carry a row

Pricing this rung meant reading `evalExpr`'s `def` arm (`Interp.lean:225`) rather than reasoning
from the rules, and it says:

```lean
visibility := if name == "initialize" then .priv
              else if m.currentFrame.kind == .toplevel then .priv
              else m.currentFrame.defVis
```

`ResolvesUser` requires `.pub`. **So a method defined at toplevel is private and can never
witness a row** — which is exactly CRuby's behaviour, and the reason `public def m …` exists at
all (L72). The plan had a cheaper intermediate rung in mind — a toplevel `def` keyed on
`"Object"`, needing no context stack — and it is not merely weak but *unwitnessable*. The first
row has to come from a `def` inside a class body, so the context stack is not avoidable.

**That is the ninth-session lesson applied one rung later**: price a rung by asking what the step
*does*, in order. Reading the interpreter took ten minutes; the intermediate rung would have
taken a commit to discover it was dead.

`defVis = .pub` therefore rides in `StackCtx` beside the name, because it is a fact about the
same frame and the same step needs both.

### `ClassOk` gains two clauses, one measured first

* **the constant's object is a class *named* `n`** — without it a class-body frame has a definee
  the invariant cannot name;
* **and it is the only one.** `TyClass h (.cls n) j` quantifies over *every* class object named
  `n`, so a row on `n` obliges all of them while a `def` installs on exactly one.

The second was measured before it was assumed (`scripts/names_probe.lean`, now part of
`check-proofs.sh`): at the prelude-booted heap **no two of the 87 class objects share a name**,
so the general uniqueness statement is true and the restriction of it to the table's own names is
what a row costs. 27 of the 87 are eigenclasses, which is the family L124 fixed and the one most
likely to regress — the probe reports the count so a regression is loud.

`className h Boot.objectId = "Object"` is folded into `ClassOk` too, rather than becoming a
seventh conjunct of `Inv`: `BottomObj` says the outermost definee is the Object *id*, `StackCtx`
needs its *name*, and `classOkB` decides both in one pass.

### Mechanical notes

* **`cases` alternative arities move again**, for the third time in three commits (L160, L161,
  here). Adding one index to `KontOk` shifts every `@`-alternative by one — except the ones where
  the new index unifies with a fixed outer variable, where it shifts by zero. There is no rule to
  memorise: read the failing case's goal display, which prints the introduced binders with their
  types.
* **`.unzip.1`/`.unzip.2` do not simp**; `.map Prod.fst`/`.map Prod.snd` do, via `List.map_cons`.
  The first spelling cost two rounds of "type mismatch on definitionally equal terms" before the
  second made the goals reduce.

## L163 — a `def` declares, and the first accepted program with a user-method call

```ruby
class String
  def shout
    1
  end
  "x".shout      # ⇒ accept, type Integer
end
```

`{"type":"Integer","verdict":"accept"}` — and the `Integer` is the return type of the program's
**own** `def`, read back at the call site through a row the `def` step put in the table. This is
the thing blocked since F1a, and `egUserCall` in `Proof/StaticSoundness.lean` is the checked
witness. CRuby and the model agree on `p "x".shout` (both print `1`), which `check_sound` does not
say and is worth having said.

Every rung since F1a is on this one path, which is the argument for having built them in that
order: the row is keyed on `"String"` (F1a's table), the receiver's type comes from the string
literal (L151), the call is a zero-argument send (L152) inside a reopened class body (L156), the
dispatch takes `EntryOk`'s **user** arm — **inhabited for the first time here**, L157 having built
it empty — the table is threaded (L160), the body's typing survives the program's later
declarations (L161), and the row's key is tied to the frame's definee by `StackCtx` (L162).

`--check` over the 1,227 cached bootstraptest ASTs is byte-identical at 38 / 1,187 / 0: no
bootstraptest program reopens a core class *and* calls the method it defines. Inert on the corpus,
not inert in capability — the L156 situation exactly, and the reason the capability is asserted by
a witness in the build rather than by a number.

### The four side conditions, and that each is a fact about the interpreter

A `def` adds a row only when all four hold. None is a matter of taste; each is a clause
`ResolvesUser` requires of the `MethodDef` `evalExpr` actually builds.

* **`¬ top`.** A toplevel `def` installs a **private** method
  (`Interp.lean:225`: `else if currentFrame.kind == .toplevel then .priv`) and `ResolvesUser`
  requires `.pub`. A row keyed at toplevel is *unwitnessable*, not merely weak. This killed the
  cheaper rung the plan had in mind (L162) and it is pinned as a checked `unknown`.
* **`name ≠ "initialize"`.** Private by the same rule, one line earlier.
* **`reopenableClasses.contains ctx`.** The row obliges **every** class object named `ctx`, and
  `ClassOk`'s uniqueness clause is stated at that table's names. Costs nothing: a class body is
  admitted for exactly those names anyway.
* **`defFree body`.** L161's hypothesis. The body's typing is carried in the invariant and has to
  survive later `def`s, and `infer` is monotone in the table only on `def`-free expressions.

### What the class-body rule's stability condition turned into

L160 made a class body require `Db = D` — a placeholder, since a class body's `def`s are exactly
the rows meant to escape. They now escape, and `KontOk.frameK` still carries **one** table: the
caller's continuation is typed at `Db` because that is what the rule *returns*, so the table the
frame pops into is the one the body ended at. No antitone step, no second index. That is worth
stating as a rule of thumb: **when a scope's output has to outlive the scope, make the scope's
rule return it rather than making the frame relate two of them.**

### The obligation, and where each half came from

`DeclsOk_addRow`: old rows survive by name-disjointness (as in `DeclsOk_defineMethod`) with their
*user* witnesses transported by `infer_mono`; the new row is one `UserEntryOk`. Two clauses of
`ClassOk` are spent on it and both were **measured before they were assumed**
(`scripts/names_probe.lean`):

* **uniqueness** turns `∀ k, TyClass h (.cls ctx) k → …` into the single class the step wrote to;
* **the chain starts at the class** makes the entry just written the one `lookup` finds. Not a
  technicality: `ancestors` puts `prepends` *before* the class (`Heap.lean:506`), so a prepended
  module defining the same name would shadow it and the row would be false. `ancestors String =
  [9, 40, 1, …]` at the booted heap.

`hground` keeps the row off the ground types, and it is the failure `tyClassNames`' own docstring
describes: a row on `"Integer"` would owe `EntryOk` at `.int`, whose inhabitants are immediates.
`reopenableClasses` membership discharges it by `decide`.

Two new heap lemmas, and they are the first **positive** ones about `defineMethod`
(`Proof/HeapFacts.lean`). Every previous lemma there says what a method-table write leaves
*alone*, because that is all a rung with a fixed table ever needed; a program-supplied row needs
the other direction — the name just installed is the one `lookup` finds.

### Maintenance note that will recur

`infer.induct`'s case **numbers** move whenever `infer` gains a branch: this commit's two new
`if`s in the `def` arm shifted eight of `Mono.lean`'s twelve explicit cases by one. There is no
way to name them stably. The recovery is mechanical and is worth doing the same way each time —
strip the explicit cases, restore the `trace "UNSOLVED-CASE"` fallback, read the case list off the
goal display, renumber, re-attach.

## L164 — `self` and `vcall`: the shape fourteen slice method bodies have

```ruby
class String
  def value
    1
  end
  def get
    value          # ⇒ Integer
  end
  "x".get
end
```

The implicit-self send, typed. This is the construct the *verdict* ratchet ranks first — **14 of
the slice's 92 method bodies are blocked by `vcall` alone** (`def hash = value.hash`,
`def affected? = state == :affected`, `def to_s = to_str`) — and every one of them is a
receiverless call to a user-defined accessor, which is exactly what L163's row is. It is the rung
after the rows for that reason, against a node count of 92 to `const`'s 868.

`egVcall` and `egSelf` are the checked witnesses. `--check` over the 1,227 cached bootstraptest
ASTs is byte-identical at 38 / 1,187 / 0 for the fifth commit running.

### `FrameCtx`, and why two facts rather than one

`infer`'s context parameter goes from `String` to a two-field structure:

* **`cls`** — the definee's class name, which is where a `def` here installs (L162);
* **`selfCls`** — `some c` when `self` in this activation is an *instance* of `c`.

They are different facts and the second is `none` in a class body, where `self` is the **class
object** — which `plainRecv` excludes and `valueTy?` gives no type at all. Bundling rather than
threading a second parallel list is the L162 lesson applied without having to relearn it: the two
change at exactly the same place, `KontOk.frameK`, where the environment changes too.

`StackCtx` gains the matching clause, and it is *carrying* rather than proving: `user_dispatch`
already has the fact as the send's own `ValueTy` on the receiver. What the clause buys is that the
fact survives the body's steps.

### The guard nobody would have predicted: `self` in receiver position

`infer` had no `self` rule at all, and `site_explicit` — *every send site in the fragment is
`.explicit`* — was true **because of that absence**. Giving `self` a type makes it false:
`evalExpr` picks the send site *syntactically*, so `self.foo` is a `.selfRecv` send and takes a
different path through `visError?` than the `.explicit` one `KontOk.recvK` describes.

So the two send rules now **exclude a literal `self` receiver**, and `site_explicit` is restated
over that guard. `vcall` covers the zero-argument case, which is the one the slice uses; `self.foo`
is `unknown`, and pinned as such.

**The transferable form: a lemma that holds because a rule is absent will break when the rule
arrives, and it will break somewhere else.** `site_explicit` is about the *machine*, is consumed
by two consecution cases, and has nothing to do with `self`'s type — the connection is that
`evalExpr` reads the receiver's *syntax*. Nothing in the type layer points at it.

### The dispatch lemmas generalize over the site for free

`entry_dispatch` and `user_dispatch` were stated at `.explicit`; a `vcall` dispatches at `.vcall`.
Both generalize with **no change to their proofs**, because the site is consulted only by
`visError?` and `md.visibility = .pub` passes it at any site. Worth recording as the cheap
outcome: the site is a fact about *which check runs*, not about *which method is found*, and the
predicates were already phrased over the latter.

Note what that means for the fragment's honesty: an implicit-self send in real Ruby *can* reach a
private method, and this rule does not exploit it — `ResolvesUser` still demands `.pub`. That is
incompleteness, in the safe direction.

### `vcall` is the only send case with no continuation

`evalExpr` answers `.vcall` with `startArgs m self .vcall mname [] []`, which is `finishSend`
(`Interp.lean:210`): the receiver is already a value, so there is nothing to evaluate first and no
kont to push. The consecution case is therefore `recvK0`'s **without** the `KontOk` constructor —
the dispatch happens in the same step as the expression. Three send shapes, three different numbers
of steps (`recvK` + `argsK`, `recvK0`, none), and each needs its own case for that reason and no
other.

### `UserEntryOk` pins the row's type to its key

The user arm gained `τr = .cls c`. Without it the callee's context is not recoverable at the call:
the arm's `c` is the class the body was *checked* in, the receiver's type is the class it *is*, and
the invariant needs them equal to say what `self` is inside the body. At the `def` step both are
`ctx.cls`, so the clause is a `rfl`. It also rules the user arm out at a ground type, which was
previously true only by nobody having put a row there.

**The inheritance caveat this exposes, stated because it is the next place it will bite**: `c` is
the *owner's* name, and a method inherited into a subclass is called on a receiver whose class is
not the owner. The fragment has no inheritance in `declFor` (`Sub` is deliberately absent, F1a), so
the two coincide today. Widening `declFor` to walk ancestors will make this clause false as stated,
and the fix is to type `self` at the receiver's class rather than the owner's — which is what Ruby
means anyway.

### The census got *less* favourable, on purpose

`fragment-gap.py`'s blocking-node count went **2,746 → 2,762**. Nothing regressed: `self` in
receiver position is now classified as blocking (16 occurrences), and `self`/`vcall` are reported
PARTIAL — blocking — even though an occurrence inside a method body of a reopenable class is
admitted, because the census cannot tell which it is from the node alone. **A ratchet that cannot
distinguish the admitted case from the refused one should count it as refused**; the alternative
reads as progress the checker has not made.


## L165 — an assertion language, and the faithfulness theorem that makes it free

`homebrew/assertion-language.md` R1's datatype half, plus §9's Layer 2 and the soundness
result §12 prices as R5. `PLAN.md` D11 records the decision; this records what it cost and
what came out different from the proposal.

Two files. `RubyCore/Types/Assn.lean` is Layer 3 — `ATy`, `ASig`, `Row`, `Assn`, `Store`,
`entail`, `dischargeNom`/`dischargeRow`, the printer — all decidable, all untrusted, and none
of it linked into any verdict. `RubyCore/Proof/Static/Assn.lean` is Layer 2: `denote` (`⟦·⟧`),
`RowsOk`, and four theorems.

### The result worth reading first, because it changes the shape of the rung

```lean
theorem denote_declAssn : denote D θ (declAssn D) h ↔ DeclsOk D h
```

An **`iff`**, over the artifact `Inv` already carries. §9.3 says the honest weak point of the
whole approach is that `⟦·⟧` is *"a definition, and nothing checks that it means what it is
supposed to"*. For the declaration fragment, this checks it — and then does something the
proposal did not anticipate:

`InvA` (the invariant with a *certificate* `P` where `DeclsOk F` stood) is proved **equal** to
`Inv`, so `assn_sound_from` is `sound_from ∘ invA_iff_inv.mp` and **not one consecution case
re-opens.** §12 prices R5 as *"large: every closed consecution case re-opens"* and constraint 4
says that cannot be done incrementally. Both are true of the R5 the document imagines — one
that *changes* `Inv`'s content. Neither is true of a re-notation whose faithfulness is proved,
because a proposition equal to the old one needs no new preservation argument.

**The transferable lesson:** *when a rung is priced as "re-open everything", ask whether the new
statement is equivalent to the old one rather than stronger.* The price is for strength, not for
notation, and this rung wanted only notation.

### Three departures from §6's grammar, each forced

1. **`Ty` did not gain a `var α` arm.** §6 writes one. Adding it re-opens every `match` on `Ty`
   in the metatheory — `TyClass`, `tyClassNames`, `valueTy?`, `Static/Mono.lean`'s 42 cases —
   for a constructor **no value can inhabit**. `ATy := nom Ty | var TyVar` lives in the
   assertion language only, so the nominal fragment of `Assn` mentions exactly today's `Ty`,
   which is what makes `⟦·⟧`'s atoms literally the existing predicates.

2. **`C ▷ n : σ` is keyed by `Ty`, not by a class name**, and this is the difference between a
   faithful map and a lossy one. §6 says the arm "is today's `Decls` entry" — but what `DeclsOk`
   quantifies over is `declFor D τ n`, keyed by a **type**, and the two are not in bijection:
   `Ty.bool` is *two* classes and demands they agree, while `Ty.cls "Integer"` is *no* classes
   at all (`tyClassNames` subtracts the ground names). A name-keyed atom expresses neither, so
   `denote_declAssn` would have been an implication one way and false the other.
   `Assn.declC c n σ := .decl (nomTy c) n σ` is the class-name spelling, kept because that is
   what §11 prints.

3. **`A * A`, `p.@x ↦ τ`, `C ▷ᵂ n`, `closed α` are absent, not stubbed.** §6.5 asks that they be
   *recorded* so a later grammar is not incompatible; the record is the document. A constructor
   with no `⟦·⟧` is new unchecked surface for zero benefit, which is the cost side of §1's own
   ledger.

### The enumeration, which is where the work was

`DeclsOk` quantifies over `declFor D τ n` for **every** `τ`, of which there are infinitely many
(`Ty.cls` takes a `String`). `declAtoms D` is a finite list. `mem_declAtoms_iff` — the
biconditional — joins them, and it rests on exactly three clauses of `tyClassNames`: the ground
arms are keyed at *their* class names; `.cls c` is empty when `c` is a ground name, so no `.cls`
atom duplicates a ground one; and every other `.cls c` with a declaration has `c` among the
table's keys, because `declOf?` reads `declsFor`, which reads `D.find?`. Getting the list right
is a fact about `tyClassNames`, not about assertions — which is why the enumeration is over
`declTys D` (four ground arms, plus one per table key) and not over the rows.

### `Row.insert` prepends, and that is `addRow`'s argument again

The first version placed entries **in order**, to make §8.1's normal form a property of the
representation. It was withdrawn: sorted insert needs a sortedness invariant threaded through
every recursion of `inferOpen` before monotonicity (L166) can be stated, and without it the
lemma is **false** — a prepended duplicate shadows a later entry at a different signature.
Prepend-shadowing is what `Types/Decls.lean`'s `addRow` does, for the reason it gives: `get?`
reads `List.find?`, which stops at the first hit, so the only fact any proof needs is
`List.find?`'s own equation. §8.1's normal form survives as `Row.normalize`, used by `render`,
which is where a canonical form is actually wanted — comparing and printing rows, not looking
them up.

### `entail_sound`, and the shape of its statement

§9.2's fourth owed item, and it needed one non-obvious move: `induction Q` reverts the three
premises (they mention `Q`), and every case then carries a *dependent* `match`. Stating them as
arguments after `∀ Q` — `entail_sound'` — makes each case introduce its own. **The shape of a
statement is doing real work whenever an induction reverts a hypothesis that mentions the
target.**

### What this does **not** prove, which is the first thing to say about it

**No new program is known not to type-stick.** `assn_check_sound`'s `¬ typeStuck` conjunct is
`check_sound` verbatim — a conjunction, not a chain — and `assn_sound_from` is `sound_from`
re-plumbed through `invA_iff_inv`. The set is exactly `{p | check p = accept}`, which is why
`--check` is byte-identical. The theorem's docstring said *"⇒ there is a certificate ⇒ no
reachable outcome is type-stuck"* and the second `⇒` was not a derivation; it has been rewritten
to warn against exactly that misreading.

What faithfulness buys is **negative**, and that is the honest framing: an equality cannot be
weaker than what it equals, so §9.3's failure mode — *"if `⟦p ~ n : σ⟧` is subtly weaker than
'this dispatch does not type-stick', the theorem stays true and stops being about anything"* — is
ruled out for the declaration fragment rather than merely argued against. A re-notation whose
faithfulness is unproved is precisely the thing that could quietly stop being about anything.

Also unproduced: **§9.2's third obligation**, `RowsOk P h → require(...) = some (β,_) → ¬ (that
send type-sticks)`. There is no such lemma. The equivalent fact is fused into `step_ok`'s case
analysis for the rules that already exist, which is where `safe` is discharged. Adequate for what
is built; worth knowing that the assertion language owns no does-not-stick lemma of its own.

### What is still unchecked, said out loud

`denote_declAssn` closes §9.3 for the **declaration** fragment. It says nothing about the
requirement and obligation arms, whose `⟦·⟧` is still a definition — mitigated only by §9.1's
own advice, that the atoms are `EntryOk` and nothing new. A reader who wants to attack this
should attack `denote`'s `req`/`obl` arms, and the honest answer is that they are the same
`EntryOk` at a substituted type.

### R2, stated and not taken

`declaresIn D c name` is in the file, with `declaresIn_of_declaresName` — the one direction that
is free. `infer` still reads the **name-global** `declaresName`, deliberately, and the reason is
now a measurement rather than a scheduling preference.

**R2 is worth ~nothing on the current fragment, and four minutes with the binary says so.**
`infer`'s `class'` rule admits only `reopenableClasses = ["String"]`, so a program in the
fragment **cannot contain two classes**:

```
class String; def a; 1; end; def b; 2; end; end   ⇒ accept
class String; def a; 1; end; def a; 2; end; end   ⇒ unknown   (same class — the class-relative
                                                    guard refuses it too)
class Integer; def q; 1; end; end                 ⇒ unknown   (not reopenable)
```

The entire difference class-relativity makes is `def <n>` on `String` for the four names
`baseDecls` puts on `Integer` (`+`, `-`, `*`, `zero?`). `HANDOFF.md` has called this *the
current binding item* for two sessions, reasoning from the slice's `to_s`-on-eight-`Token`-
classes shape — which is real and is gated behind the **allocating** `class'` branch, not
behind the ancestors argument. **A blocker measured on the *target* can be inert on the
*fragment*, and the fragment is what the rule runs against.** Swapping the guard is also a rule
change, hence constraint 4's atomic unit. What rows buy here is exactly what
§13.5 says and no more — the *obligation* becomes writable per `(class, name)`, which is what
`Assn.obl`/`dischargeRow` already are, so two classes each defining `to_s` do not collide in an
assertion. The heap-side argument (`ResolvesAt_defineMethod`'s `mname ≠ name` over an arbitrary
dispatch class, which a class-relative version has to replace with *the defining class is not
among `k`'s ancestors*) is untouched and still owed. L167's census then demoted it: `def`-with-
parameters blocks 67 slice bodies and this blocks none of the ones that are otherwise in reach.

`--check` is byte-identical at **38 / 1,187 / 0** over the 1,227 cached bootstraptest ASTs, and
this is the first rung in the initiative where that was **predicted from the code rather than
measured hopefully**: nothing in `Types/Core.lean` changed, and the new module is not imported
by anything on the verdict path.


## L166 — open self: typing a method body against an unresolved receiver, and proving it factors

`homebrew/assertion-language.md` §4.3, §7.2's row case, §7.3, §12 **R4**. The rung the ledger
ranks highest among those with a metatheory cost, because the fourteen `vcall`-blocked slice
bodies are all one shape:

```ruby
def hash
  value.hash          # `value` is a user-defined accessor with no declared row
end
```

`RubyCore/Types/OpenSelf.lean` types this **with no row for `value` at all**, and emits the row
it would need as a precondition on its own class. `RubyCore/Proof/Static/OpenSelf.lean` proves
the two theorems that make running it safe.

### The statement, and why it is the one that costs nothing

```lean
theorem inferOpen_factors (hsat : SatStore D θ stF) (hself : θ ctx.self = .cls ctx.cls) :
    Factors D θ stF ctx Γ e (inferOpen D Γ e ctx s)
```

unfolded at `.ok`: *if the open run succeeded and `θ` satisfies the residual store, then nominal
`infer` accepts the same expression at the substituted type.* **Open-self typing reduces to
nominal typing.**

So `infer` is untouched, `KontOk` gains no constructor, and `step_ok` gains no case.
`HANDOFF.md` constraint 4 — *you cannot land the checker first and the proof later* — does not
fire, because there is no new checker on the soundness path: `inferOpen` is a **front end** whose
every accept is re-derived as an `infer` accept. That is §8.4's certifying-not-trusted stance,
applied to the inference function rather than to the entailment, and it is the second time this
session that a rung priced as expensive turned out to want a *reduction* rather than an
extension (L165 is the first).

`userConforms_of_inferBody` is the payoff in the metatheory's own currency: `UserConforms` — the
clause L157 introduced and L163 first inhabited, *the checker's own verdict on a body inside the
soundness invariant* — is discharged by an open-self run plus a checked substitution.

### §7.5's owed lemma, and the definition it forced

`inferOpen_mono`: **the store only ever grows.** §7.5 states it as the reason `Σ₁ ⊎ Σ₂` can be a
plain union with no side condition, and names L161 (`infer` monotone in the table) as the shape.
It is needed in every case of the factoring theorem, because a subexpression's requirements must
still be readable at the store the whole body ends at.

It is also what forced `Row.insert` to prepend rather than sort (L165): with a sorted insert the
lemma is **false** unless a sortedness invariant is threaded through `inferOpen`, since a
prepended duplicate shadows a later entry. *A monotonicity lemma is a good test of a data
structure's operations — it fails first, and for the right reason.*

### What `inferOpen` does **not** do, and each refusal is `infer`'s, not rows'

* **`def` with parameters.** `infer`'s own `def` rule requires `params.isEmpty`, so §7.3's `Γ_b`
  has nothing to factor *to*: the theorem's conclusion would be about a nominal judgement that
  does not exist. `bodyReports` names the refusal `def-params` rather than letting it surface as
  an unbound local read — and that is the single largest number the new census reports
  (**67 of 112** slice bodies; see L167).
* **`def` and `class` inside a body.** `infer`'s `def` rule already requires `defFree body`
  (L161's `infer_mono` hypothesis), so a body that declares a method is outside the fragment
  already. That is what keeps `D` fixed across `inferOpen`, and therefore what lets the theorem's
  conclusion mention one table.
* **A literal `self` receiver.** Copied from L164 verbatim. An arm that differs from `infer`'s
  for no reason is an arm whose proof case has to be invented.

### The proof's mechanics, worth recording because they are reusable

The functional induction Lean generates for a mutual well-founded definition,
`inferOpen.induct`, is reachable as `induction Γ, e, s using inferOpen.induct (motive2 := …)
(motive3 := …)`. Two things made the ~50 cases tractable:

1. **State the conclusion as a predicate on the *result*** (`Factors`), not as three
   universally-quantified components. Twenty-odd arms answer `.missing` or `.outOfFragment`, and
   with the predicate they discharge *definitionally*; with `∀ τ Γ' s', … = .ok τ Γ' s' → …` each
   one needs its own contradiction.
2. **Write the residual cases as a `first` chain of name-free tactics.** `rename_i` names the
   induction hypotheses from the end; every side condition is `(by assumption)`, so no case's
   script depends on an inaccessible name. Ordering matters — a `split`-based alternative placed
   before the send cases will fire on them and produce a mess that the later alternatives cannot
   clean up.

### The lesson about `dsimp only`

`rw [h] at goal` where `h` rewrites a `match` scrutinee leaves the `match` unreduced, and the
*next* `rw` then fails to find its pattern. Every multi-step rewrite in this file needs a
`dsimp only` between the steps. Cheap once known and three wasted attempts before that.

`--check` byte-identical at 38 / 1,187 / 0.


## L167 — `--assn`, and the third ratchet that says which wall the slice is behind

`homebrew/assertion-language.md` §11 and §12 **R1**/**R3**. The cheapest benefit in §1's ledger
and the only one that wanted no metatheory at all — and it immediately corrected the plan.

### What `--assn` is

A second static query beside `--check`, over the same AST. Where `--check` is whole-program and
answers one word, `--assn` answers **per method body**, and an `unknown` **carries the atom it
wanted**:

```
homebrew/vulns/semver.rb  Version#hash
  accept : α2
  requires: Version ⊒ ⟨ value : () → α1 ⟩
  and:      α1 ~ hash : () → α2
```

That is §4.3's principal type, printed. Note the second line: a body whose return type is still a
*variable* is **not** a failure — it is a body whose type is determined by its precondition, and
saying so is the per-method-body gradient §1's ledger asks for. `BodyVerdict.acceptedUnder`
therefore carries an `ATy`, not a `Ty`; the first version carried a `Ty` and reported `def get;
value; end` as **blocked**, which is precisely the information-free `unknown` this rung exists to
retire.

`check`'s verdict is unchanged, and `--check` is byte-identical at 38 / 1,187 / 0.

### The third ratchet, and the finding

`fragment-gap.py` grew the number `HANDOFF.md` §Not on the critical path has been asking for
since the fourteenth session — *method bodies whose every send resolves* — except that it is not
computed by the tool at all. It is read out of `rubycore --assn`. **`SUPPORTED` has been wrong
twice from drift, and a ratchet computed by the artifact it measures cannot drift from it.**

On the slice, over 112 `def`s (the two hand censuses said 92, because they did not descend into
singleton defs or defs inside blocks):

| | |
|---|---|
| accepted, under a stated precondition | **16** |
| …of which unconditional (empty row) | 5 |
| refused with a named missing atom | 0 |
| out of fragment | 96 |

and the census of *why*, which is the finding:

```
67  def-params          9  send-0-args        4  send-with-block
 3  ivar                3  const              3  array
 2  selfRecv            1  super              1  send-2-args …
```

**`def` with parameters is 67 of 112 — three times every other blocker combined, and no document
in this initiative had it anywhere near the top.** The fourteenth session ranked by nodes and put
`const` first (868 nodes); the fifteenth ranked by method bodies freed and put `vcall` first (14).
Both were ranking *constructs inside bodies*. The ratchet that asks the checker directly says the
binding constraint is the **shape of the `def` rule itself** — `params.isEmpty`, in
`Types/Core.lean`, unchanged since P0 and never costed.

That is the third variant of the same process lesson, and the sharpest: **L159's was *measure the
thing the criterion is stated over*; L164's was *measure it with the ratchet that predicts the
verdict*; this one is *have the artifact compute the ratchet, because the copy will disagree with
it and the copy will be wrong.*** The tool's own `SUPPORTED`-based number for the same slice is
**5 of 92** — a deliberate understatement (it cannot tell a method-body `self` from a class-body
one), and a reader comparing 5 against 16 has no way to know which is the honest one without
reading both implementations.

### Why the number moved down mid-session, and why that is the report working

The first run of the census reported **18** accepted. It was wrong: two bodies took parameters
and never read them, so nothing in the body was outside the fragment even though `infer`'s `def`
rule refuses the definition. Naming the refusal at the `def` node (`def-params`) rather than
letting it surface as an unbound local read fixed the count to 16 **and** produced the 67 above.
*A census that classifies at the wrong node reports the right total and the wrong reason, and the
reason is the whole product.*

### Scope, stated

`--assn` reports; it does not decide. `bodyVerdict` runs `inferOpen`, whose accepts are backed by
`inferOpen_factors` (L166) **only once a substitution is supplied and checked** — the tool does
not solve for one, so an `accept` here is *"types under this precondition"*, not *"is safe"*. The
solver is the missing piece, it is Layer 3, and §8.3's bi-abduction is where it goes.

## L168 — `def` with parameters, open: the 67-body wall, and what was behind it

`homebrew/assertion-language.md` §7.3's `Γ_b`, and the item `HANDOFF.md` §The next commit named
after L167's ratchet reordered the work: **`def` with parameters is 67 of the slice's 112 method
bodies**, three times every other blocker combined.

It is landed the way R4 was — **untrusted front end, proved to factor, `check` untouched** — and
the census it produces is the finding, because it is not the one the 67 predicted.

### The wall was in the rule, not in the body, and the refusal said so

`bodyReports` refused a parameterised `def` with a comment that is worth quoting, because it is
half right:

> **A `def` with parameters is refused here, not by rows.** `infer`'s own `def` rule requires
> `params.isEmpty`, so §7.3's `Γ_b` — declared parameters, or fresh variables — has nothing to
> factor *to*: the factoring theorem's conclusion would be about a nominal judgement that does not
> exist.

True of the `def` **rule**. False of the **body** — and `inferOpen_factors` had said so since
L166, in its own statement:

```lean
theorem inferOpen_factors (D) (ctx) (θ) (stF) (hsat) (hself) (Γ : AEnv) (e : Expr) (s) :
    Factors D θ stF ctx Γ e (inferOpen D Γ e ctx s)
```

`Γ` is universally quantified. It always was; the empty environment was a *caller's* choice in
`inferBody`, not a hypothesis of the theorem. So binding each required positional parameter to a
fresh type variable and running the body in that environment factors through
`infer D (substEnv θ Γ_b) body`, a nominal judgement that exists today —
`inferBodyWith_sound`, whose whole proof is one instantiation of L166's theorem plus the two
`Option` destructurings that read `openParams`' answer. **Eleven lines, first attempt, axiom-clean.**

What still does not exist is the `def` rule that installs the row, and that is why the verdict has
its own constructor (`BodyVerdict.acceptedOpenParams`), its own JSON key (`open_params`) and its
own census column (`pacc`) instead of joining `accepted`. The distinction is exact and worth
keeping in that shape: `acceptedUnder` factors through `infer` **at the empty environment**, which
is the environment `infer`'s own `def` arm checks a zero-parameter body in, so it is one
substitution away from the judgement `check` uses; `acceptedOpenParams` factors through `infer` on
the **body** and through no `def` rule at all. Merging them would report an accept-rate the checker
does not have.

**Required positional parameters only.** The other seven arms of `Param` are refused **by kind** —
`def-params-opt`, `-key`, `-rest`, `-kwrest`, `-block` — because each is a different binding rule
in `enterUserMethod` (`Interp/Support.lean:452`) and an optional's default is an expression
evaluated in the callee frame, which is a second body rather than a type. Nine slice bodies are
behind those five kinds, and the census can now say which.

### The finding: 67 bodies were behind the wall, and 3 of them were behind only that

| | before | after |
|---|---|---|
| accepted (zero-parameter, precondition on its own class) | 16 | 16 |
| accepted with **parameters open** | — | **3** |
| refused with a named missing atom | 0 | 2 |
| out of fragment | 96 | 91 |

Five bodies moved, of the 67 the ratchet counted. The other 62 are still `unknown`, each now
reporting **the construct inside its own body** that stopped it, and the census that results is
almost unrecognisable beside L167's:

```
16  const           11  send-0-args      9  send-with-block   8  send-2-args
 8  return           6  array            4  ivar              4  send-1-args
 4  def-params-key   3  if               3  iasgn             3  super
 2  selfRecv         2  begin            2  def-params-rest   2  def-params-opt
 1  gvar             1  zsuper           1  def-params-kwrest 1  def-params-block
```

**`const` — which L167 measured at 3 and this file demoted twice on that basis — is 16 and back at
the top.** `send-with-block` is 9 rather than 4. `ivar` and `iasgn` together are 7 rather than 3.
Every one of those numbers went *up* when a blocker in front of them was removed, and that is the
lesson:

> **A census that classifies at the outermost node reports a blocker's count as an upper bound on
> what removing it buys — and simultaneously *understates* every blocker it hides.** `def-params`
> was worth 67 as a refusal and 3 as an accept, because it sat in front of sixteen other walls. The
> two are different questions and L167's table answered only the first.

That is the fourth variant of this initiative's recurring process lesson, and the first one that is
about *depth* rather than about which ratchet to read. The repair is not a different ratchet: it is
to read a blocker's count as *bodies this refusal is the outermost cause of* and to expect the
distribution behind it to be unknown until the refusal is lifted. There is no way to compute the
second number without lifting the first.

### Scope, stated as narrowly as L167's

`--assn` reports; it does not decide. An `accept (params open)` means *this body types, given these
parameter types and this precondition on its class*, with the substitution still unsupplied — and
in addition it means *no `def` rule accepts the enclosing definition*. `check` is byte-identical at
**38 / 1,187 / 0** over the 1,227 cached bootstraptest ASTs, which is the twelfth check and is what
"inert in the checker" is verified by.

### The checks

`check-proofs.sh` green (24 theorems, `propext`/`Classical.choice`/`Quot.sound` only — two new
`#print axioms` lines: `inferBodyWith_sound` and the end-to-end `egParam_nominal`); `--check`
byte-identical; `--assn` smoke 1,225 clean / 2 decode gates over the same ASTs; `fragment-gap.py
--self-test` all agree; desugar bootstraptest 1,227 agree / 0 disagree / 77 out-of-fragment. No
rule changed, so the execution tiers cannot move — but the binary relinked, so the two cheap ones
were run rather than argued.

### Also in this commit

`fragment-gap.py --assn-dump`: §11's report for **every** method body in the slice, one block per
`def`, in source order. The aggregate ratchet says how many; this says *which*, and it is the
artifact `homebrew/slice-verdict.md` is generated from.

## L169 — D12: the verdict is total, and the criterion is met by reading the guarantee correctly

`PLAN.md` D12 (and D13, which is a direction rather than a rung). The whole change is 60 lines of
Lean, two of them load-bearing, and it closes `PLAN.md` §1 criterion 2 — *`rubycore --check` returns
`accept` or `reject`, never `unknown`* — which L168's measurement had just priced at ~20 rungs and
two structural walls away.

### What was wrong, and it was a reading rather than a measurement

L168's report said a whole-fragment decision was unreachable and that `reject` was "not an
alternative route: it would claim the slice type-sticks". **That second clause is false**, and Sam's
correction is the whole of this commit: the soundness statement is **one-directional**.
`check_sound` says *`accept` ⇒ no reachable outcome is type-stuck*. Nothing anywhere says, or needs
to say, anything about a `reject`. So `reject` may honestly mean **the checker did not certify this
program** — a claim about the checker — and a rejected program may run perfectly. Completeness is not
part of the guarantee; it is the quality metric.

Once that is said, the criterion costs nothing:

```lean
def decisionOf (p : Expr) : Decision × Basis :=
  match check p with
  | .accept  => (.accept, .certified)
  | .reject  => (.reject, .refuted)
  | .unknown => (.reject, .uncertified)

theorem decision_accept_iff (p) : (decisionOf p).1 = .accept ↔ check p = .accept
```

`decision_accept_iff` is the two lines that matter: the reported `accept` is **the same predicate**
every existing theorem is stated over, so no theorem moved, and `decision_sound_withPrelude` is
`check_sound_withPrelude` composed with it. `decision_accept_certified` makes the pairing total the
other way — an accepting decision is never anything but `certified`, so a reader cannot see the two
disagree.

### The thing that had to be preserved, and would have been destroyed by a collapse

`unknown` and `reject` are **different facts** — *the fragment escaped* and *our rules refute this* —
and only the second has ever carried an obligation: `difftest/checker_relation.py`'s pinned zero
`check-reject-disagreement` (*"we rejected and srb found nothing"*). Collapsing them into one
reported word would have turned all 1,187 bootstraptest abstentions into violations of that zero and
retired the guard while leaving it in the report reading 0 — the exact failure mode
`test_every_pinned_zero_is_reachable` exists to prevent.

So the three-valued verdict is **retained as the basis**, `--check` emits all three fields
(`decision`, `basis`, `verdict`), and the guard is written into the docstring of the function that
must not be fed the wrong one. **Additive: no consumer breaks**, the tier-4 corpus's declared
verdicts keep their meaning, and the `verdict` column of the twelfth check is byte-identical.

| | |
|---|---|
| `--check` over 1,227 cached ASTs | 38 `accept`/`certified`, 1,189 `reject`/`uncertified`, **0 `refuted`**; the `verdict` field byte-identical at 38 / 1,187 / 0 |
| the eight slice files | `reject` / `uncertified`, every one |
| the linked slice program (2,159 lines, all eight files) | `reject` / `uncertified`, with 118 / 19 / 2 / 97 per-body assertion output |

**Zero `refuted` in either corpus is worth reading.** The refutation pass never fires on real code;
every reject we produce today is an abstention. That is the honest shape of the result, and it is why
the metric had to be restated rather than declared satisfied.

### What replaces the criterion

A checker that rejects everything satisfies D12 and is worthless, so §1 now carries the metric
instead: **method bodies certified-modulo-precondition (19 of 118 on the linked slice) and files
accepted (0 of 8)**, both read out of the binary. `homebrew/slice-verdict.md` is the tracker and the
triage: for `basis = uncertified` the assertion-language output names what stopped each body, which is
the *false-negative* triage §1's second bullet always asked for — a replayed counterexample trace is
owed only by a `refuted`.

### D13, and why it is here rather than in a rung

Sam's second instruction — build a type system that captures **Ruby's duck typing and control flow**,
and re-engage Sorbet later as a comparison or as a consumer of the facts we collect — is a plan
change, so it is D13 in `PLAN.md` §3 rather than an L-entry. Its immediate effect on the rung order is
recorded in `slice-verdict.md` §5: unions/nilable and occurrence typing move **ahead** of the
class-object arm of `Ty`, because the slice's remaining bodies are blocked by duck-typed idiom
(`case`/`when` narrowing, nilable returns, accessors with no declaration) rather than by missing
nominal machinery — and rows already type the last of those with no declaration at all.

### Checks

`check-proofs.sh` green, **25** theorems, `propext`/`Classical.choice`/`Quot.sound` only (one new
line: `decision_sound_withPrelude`); `--check` `verdict` byte-identical; `--assn` smoke 1,225 clean /
2 decode gates; `fragment-gap.py --self-test` all agree; `difftest` pytest 162 passed, **1
pre-existing failure unrelated to this commit** — `test_no_unsoundness_witness_is_in_the_fragment`
reports `escape-hatches/002.rb` (a `define_method` displacing a `sig`-checked method) as in-fragment.
It fails identically on the pre-commit tree, and it is the D10-era disagreement `HANDOFF.md` records
on purpose (`Fragment.lean` admits the metaprogramming; the *checker* is what refuses it) encoded as a
pre-D10 assertion. **Left failing and reported rather than weakened** — retargeting a safety guard at
`theorem_scope` is a decision, not a cleanup.

## L170 — the written receiverless call: one `SendSite` apart from `vcall`, and 11 slice bodies

`--assn`'s third ratchet ranked **`send-0-args` at 11 of the slice's 112 method bodies**, second only
to `const` (16) — and every one of those 11 is `foo()`, a receiverless call written with parentheses
where L164's `vcall` rule covers the bare `foo`. This commit is that arm, and the reason it is worth
recording is how *little* it cost against how the census ranked it.

### The finding: the two constructs differ by one constructor of `SendSite`

`evalExpr` sends both to the same place:

```lean
| .send none mname args pblk => startArgs m m.currentFrame.self .implicit mname [] args pblk
| .vcall mname               => startArgs m m.currentFrame.self .vcall    mname [] []   .none
```

and `startArgs … [] []` **is** `finishSend`, so with no arguments both dispatch *in this step* —
no continuation is pushed, and there is no `argsK` and no `recvK` in either chain. The only
difference the machine can see is the site, and `visError?` (`Interp/Dispatch.lean:325`) matches
`.explicit` alone; `missNoMethod` distinguishes `.vcall` for the *message*, which is a fact about a
miss and a miss is not reachable under the invariant. So:

* **no new `KontOk` constructor**, hence no `heap_congr'` case;
* **no new consecution argument** — L164's `vcall` case was already the whole of it, and both
  dispatch lemmas (`entry_dispatch`, `user_dispatch`) were generalized over `site` in that commit.

The commit therefore starts by *lifting* L164's case out of `step_ok` verbatim as
`inv_implicit_send0`, quantified over the site, and the `vcall` case becomes a five-line call to it.
The new `.send none mname [] none` case is the second caller. **That refactor landed green before the
rule existed**, which is the cheap way to find out whether a rung is really the same argument: if the
lift does not typecheck at an abstract site, the two constructs were not the same dispatch after all.

### What it cost, itemized

| | |
|---|---|
| `Types/Core.lean` | one `infer` arm, the `vcall` arm's body verbatim |
| `Types/OpenSelf.lean` | one `inferOpen` arm, the `vcall` arm's body verbatim |
| `Proof/Static/Konts.lean` | **nothing** |
| `Proof/Static/Preservation.lean` | the lift, plus a case that calls it |
| `Proof/Static/Mono.lean` | one case (`case25`), the `vcall` case verbatim — **plus a renumbering** |
| `Proof/Static/OpenSelf.lean` | **nothing** — `inferOpen_mono` and `inferOpen_factors` are uniform `| _ =>` tactics and the new arm is discharged by the `vcall` alternative already in the soup |

**The renumbering is the only tax, and it is worth naming as a recurring one.** `infer.induct`'s
cases are positional, so an arm inserted mid-match shifts every explicit `caseNN` after it.
`HANDOFF.md` records a recovery procedure (strip the cases, restore a `trace` arm, read the list off
the trace); there is a cheaper one, used here and recommended:

> **`#check @RubyCore.Types.infer.induct` prints the whole case list with binders and arities.** Read
> the shift off it — count the alternatives up to the new arm — instead of re-deriving it from
> compiler errors. This arm generates **three** cases (`selfCls = some c` × signature present /
> absent, and `selfCls = none`), so every explicit case number ≥ 25 moved by +3.

### The census re-ranked again, exactly as L168 said it would

`send-0-args` went to **0** and nothing else went down:

| | before | after |
|---|---|---|
| out of fragment | 91 | **90** |
| accepted (zero-parameter) | 16 | **17** |
| `return` | 8 | **16** |
| `send-2-args` | 8 | **10** |

**Eleven bodies were behind the refusal and one came out.** That is the third measurement of L168's
lesson and the first one where it was *predicted* rather than discovered: a census classifies at the
outermost blocking node, so lifting a blocker moves the bodies whose *next* blocker is already inside
the fragment and re-ranks the rest upward. Eleven bodies named `send-0-args` because it was the first
thing in them the checker met; ten of the eleven have a `return` or a two-argument send behind it.

Read the accept for what it is: `version.rb` gained one certified-modulo-precondition body, so the
false-negative metric (`PLAN.md` §1 as amended by D12) is **17 + 3 of 112**, and `check` still
answers `reject`/`uncertified` on all eight files — the two walls of `slice-verdict.md` §4 are
untouched by this and by anything else in §3.

### Checks

`check-proofs.sh` green, **27** theorems (two new lines: `inv_implicit_send0`,
`egImplicitCall_safe`), `propext`/`Classical.choice`/`Quot.sound` only. `--check` over the 1,227
cached bootstraptest ASTs: **38 / 1,187 / 0**, unchanged. The transition argument rather than the
totals, because this rung is *not* inert in the checker by design: the new arm intercepts a shape that
previously fell through to `| _ => none`, so it is **additive** — no program can lose an `accept` —
and an unchanged total of 38 therefore means **zero** transitions in either direction. `--assn` smoke
1,225 clean / 2 decode gates. `fragment-gap.py --self-test` all agree, with two new cases: `v()`
accepted inside a reopened `String`, and `foo(1)` still `unknown` (an argument pushes an `argsK` at
the `.implicit` site, which `KontOk.argsK` — stated at `.explicit` — does not describe; that is the
next rung, not this one). `shape_send`'s blanket *implicit-self send* refusal is split by arity so the
first ratchet stops reporting the 22 admitted nodes as blocking.

## L171 — the unary receiverless call, and `KontOk.argsK` gains a site *parameter*

`send-1-args` was 4 of the slice's 112 bodies after L170. This is that arm, and its content is one
word in an existing constructor.

### The finding: the continuation is the same one, at a different site

The explicit unary send reaches `.argsK recv .explicit mname [] []` **one step late** — `recvK`
evaluates the receiver first and `applyKont` pushes `argsK` when the receiver's value arrives. The
receiverless one pushes the *same* kont **immediately**, because the receiver is already a value (the
frame's `self`), at site `.implicit`. Nothing between the push and the dispatch reads the site:
`visError?` matches `.explicit` alone and `entry_dispatch` has been site-polymorphic since L164 — and
`step_ok`'s `argsK` case never mentions it.

So `KontOk.argsK` gained `{site : SendSite}` and the pattern became `.argsK recv site mname [] []`.
That is the whole `KontOk` change: **no new constructor, no new `heap_congr'` case, and the `argsK`
consecution case is untouched.** The only edit it forced was one more `_` in `step_ok`'s `@argsK`
binder list.

### What the rule's shape had to be, and why it is *not* the explicit rule's

There is **no `recvK` in this chain**, and that decides two things the explicit rule decides
differently:

* the argument is evaluated in *this* step, so the rule's answer is the environment **and table the
  argument leaves** — which is exactly what `CtlOk` then hands `KontOk.argsK`, whose Γ and `D` are
  one index each. No stability side condition is needed, and an earlier draft that added `D₁ = D`
  was withdrawn once the indices were lined up rather than guessed at;
* the signature is read at `D₁`, **after** the argument — L160's rule, and here it is forced rather
  than chosen, because `argsK`'s premise has to be readable at the table the kont is indexed by.

### And it accepts no new *programs*, on purpose

The receiver is `self`, so the row must be declared on the **definee's class**. `baseDecls` declares
only `Integer` rows, `reopenableClasses` is `["String"]`, and `infer`'s `def` arm requires
`params.isEmpty` — so **nothing in the fragment can supply a unary row on a reopenable class.** The
arm is inert in `check` for the L157 reason: it is a capability with no inhabitant yet, and the way to
see that is to ask what would have to *declare* the row rather than what would call it.

The capability is therefore asserted against `infer` directly, at a table with the row added by hand
(`Proof/StaticSoundness.lean`), together with the fact that two arguments are still `none`. `--check`
over the 1,227 cached ASTs is **byte-identical**, diffed rather than argued.

### Where it does move: `inferOpen`, which needs no row at all

The open-self front end records the requirement on `ctx.self` instead of reading the table, so the
slice's four `send-1-args` bodies move immediately. `Proof/Static/OpenSelf.lean` needed **one new
alternative** in the factoring tactic — the zero-argument-on-`var α` line with `← hself` in front,
because the receiver is `ctx.self` and the nominal rule reads `sigOf D (.cls ctx.cls)`.

| | before | after |
|---|---|---|
| out of fragment | 90 | **89** |
| refused with a named atom | 2 | **3** |
| `return` | 16 | **19** |
| `vulns/semver.rb` out of fragment | 1 | **0** |

`semver.rb`'s only `def` is now out of the *fragment* question entirely and into the *row* question
(`α0 ~ parse : (α2) → _`) — which is the first slice file with no out-of-fragment body, and the first
time the remaining obstruction on a whole file is a declaration rather than a rule.

### Checks

`check-proofs.sh` green, 27 theorems, axiom-clean. `--check` byte-identical against L170's capture.
`--assn` smoke 1,225 clean / 2 decode gates. `fragment-gap.py --self-test` all agree, two new cases
(`foo(1)` unknown for want of a row, `foo(1, 2)` unknown for want of a rule); `shape_send`'s
receiverless arm now admits arities 0 and 1.

## L172 — a literal `self` receiver, and the third `SendSite` parameter

`selfRecv` was 2 of the slice's 89 remaining out-of-fragment bodies. It is the third rung in a row
whose whole content is *this constructor's site index should have been a parameter*, and the third
time the answer was one word.

### What the exclusion actually was

F1b.11 excluded `self.foo` and the comment recording it was precise about why: `evalExpr` picks the
send **site** syntactically, so `self.foo` is a `.selfRecv` send while every other receiver is
`.explicit`, and `KontOk.recvK`/`recvK0` were *stated* at `.explicit`. The guard `if isSelf recv then
none` existed to keep `site_explicit` — *the site is always `.explicit` in the fragment* — true.

Read what the two sites differ by, and the exclusion evaporates: `visError?`
(`Interp/Dispatch.lean:325`) raises **only** at `.explicit`, so `.selfRecv` is the *permissive*
direction, and `ResolvesAt`/`ResolvesUser` demand `.pub` regardless. A public method dispatches
identically at both sites, and the dispatch lemmas have been site-polymorphic since L164. So:

* `KontOk.recvK` and `KontOk.recvK0` take `{site : SendSite}`;
* `infer`'s two `isSelf` guards are **deleted**, in both `infer` and `inferOpen`;
* `site_explicit` is **withdrawn**, struck through in place with the reason — the third lemma in this
  file's history (after `TypeAgree.symm` and `ResolvesTo_grow`) that was correct when written and made
  pointless by a sharper later statement;
* `infer_send_inv`/`infer_send0_inv` lose their `isSelf r = false` conjunct;
* `step_ok`'s two send cases keep the `cases r` — `evalExpr`'s match on the receiver *expression* still
  will not rewrite — but lose the refuted branch: `self` is one more uniform application of the same
  constructor.

**A class body still refuses `self.foo`, and for the right reason.** In a class body `self` is the
class object, `plainRecv` excludes a class, and `infer`'s own `self'` arm answers `none`. What refuses
it is the receiver's *type*, not the send site — which is the distinction the guard was blurring, and
it is asserted as a checked fact beside the accepting witness.

### The measurement, and it did not move the metric

| | before | after |
|---|---|---|
| out of fragment | 89 | **89** |
| `selfRecv` | 2 | **0** |
| `const` | 16 | **18** |

**The two bodies moved from `selfRecv` to `const`, and the total did not change.** That is the fourth
run of L168's lesson and the first time it netted zero: a census classifies at the outermost blocking
node, so lifting a refusal reveals the next one and the *ranking* changes while the *count* need not.
The rung is still worth having — `self.foo` is admitted, and the two bodies' remaining obstruction is
now named — but it is a reminder that **oof is a count of bodies, not of walls**, and the wall
underneath these two is the largest one left.

### Checks

`check-proofs.sh` green, 28 theorems, axiom-clean (`egSelfRecv_safe` added). `--check` over the 1,227
cached ASTs **byte-identical** to L171's capture (no bootstraptest program sends to a literal `self`
inside a reopened core class with a declared row). `--assn` smoke 1,225 clean / 2 decode gates.
`fragment-gap.py --self-test` all agree, two new cases (`self.v` accepted in a method body, `self.foo`
unknown in a class body); `shape_send`'s *explicit `self` receiver* refusal is deleted, so the first
ratchet's 16 nodes under it stop being counted as blocking.

## L173 — five of the six refused parameter kinds, bound from what the machine writes

L168 admitted `def` with **required positional** parameters and refused the other six *by kind*, so
the census could say which binding rule each body was behind. That bought the information; this
commit spends it. Nine of the slice's 89 out-of-fragment bodies were behind `key` (4), `rest` (2),
`opt` (2), `kwrest` (1) and `block` (1), and all nine are now typed.

### The soundness stance is unchanged, and that is the whole reason this is cheap

`inferBodyWith_sound`'s conclusion is `infer D (substEnv θ Γb) body … = some (τ.subst θ, …)` — a
statement about the **body**, in whatever environment the parameters give it. Its proof uses
`openParams … = some (Γ₀, s₀)` and `inferOpen_factors`, and **neither cares what `Γ₀` is**. So
widening `openParams` costs the theorem two lines of plumbing (it now threads an `OState` rather than
a bare counter) and nothing else: no `KontOk` constructor, no consecution case, no `infer` arm. The
nominal `def` rule still requires `params.isEmpty`, and the five binding rules in `enterUserMethod`
are still unpaid **for that rule** — which is the honest statement, and the reason these bodies keep
`acceptedOpenParams`'s separate constructor and separate census column.

### What each kind is bound to, read off `enterUserMethod` rather than guessed

`Interp/Dispatch.lean:96`–`119` is the authority, and it makes two of the five *more* precise than a
variable:

| kind | bound to | why |
|---|---|---|
| `req` | fresh variable | the caller's type is `θ`'s to choose (L168, unchanged) |
| `rest` | **`Array`** | `Builtins.allocArr` on the surplus, unconditionally — the one parameter kind whose type is *known* |
| `kwrest` | **`Hash`** | `allocHash` on the leftover pairs, likewise |
| `block` | fresh variable | `blk.getD .nil` is a `Proc` **or `nil`**, a union `Ty` cannot write |
| `opt x = d`, `key x: d` | **the default's own type** | the omitted-argument path really does bind it, so the default is typed here, in the environment built so far (a default may read an earlier parameter) |
| `key x:` (no default) | fresh variable | a required keyword, so exactly `req` |
| anonymous `*`/`**`/`&` | nothing | which is what the machine binds |

**`block` is the interesting refusal-that-isn't.** Binding `&b` to a fresh variable is not laziness:
if the body calls `b.call`, the requirement lands in the residual store, so `θ` ends up carrying the
*a block was given* precondition instead of the environment asserting a type the machine does not
guarantee. That is the under-determination in the right place.

**`fwd` and `destr` are still refused**, and for a reason that is not about cost: `...` binds three
*internal* locals (`__fwd_rest`/`__fwd_kw`/`__fwd_blk`) that no source expression can name, so there
is no environment to state; `destr` is a recursive massign against an argument shape no `Ty` records.
Neither occurs in the slice.

Two definitions were **withdrawn** with the refusal they explained — `paramKind` and `firstNonReq`,
struck through in place. `firstUnbound` replaces them and names only the two kinds that are left; a
body whose *default expression* escapes the fragment reports `def-params-dflt`, which is a different
fact and now distinguishable.

### The measurement: nine bodies moved and the total did not

| | before | after |
|---|---|---|
| out of fragment | 89 | **89** |
| `def-params-*` (five kinds) | 9 | **0** |
| `return` | 19 | 20 |
| `const` | 18 | 19 |
| `send-2-args` | 10 | **14** |
| `send-with-block` | 9 | 10 |
| `array` | 6 | 7 |
| `super` | 3 | 4 |
| `splat` | 0 | 1 |

**Third rung in a row where `oof` did not move**, and the pattern is now clear enough to state as a
rule rather than as a surprise:

> **A front-end lift moves the census's *ranking*, not its *count*.** L170 (11 bodies) netted −1,
> L172 (2 bodies) netted 0, L173 (9 bodies) netted 0. Every one of the 22 bodies behind those three
> refusals had a *second* blocker, and after three rounds the surviving blockers are exactly the ones
> that need machinery: `return` (20, a non-local exit channel in the invariant), `const` (19, a
> class-object arm of `Ty` plus a constant table), `send-2-args` (14, `ValuesTy` over a list of
> argument continuations), `send-with-block` (10, Wall 1), `array` (7, an allocating producer).

That is not a disappointing measurement, it is the useful one: **the fragment's remaining distance is
now 15 constructs and no cheap ones**, and the three cheap rungs were worth taking precisely because
they proved there is nothing else hiding behind them.

### Checks

`check-proofs.sh` green, 28 theorems, axiom-clean. `--check` byte-identical to L172's capture (the
change is entirely inside the untrusted front end; `check` does not call `inferOpen`). `--assn` smoke
1,227 clean. `fragment-gap.py --self-test` all agree. Seven new checked examples in
`Types/OpenSelf.lean` — one per binding decision above, because a binding read off the interpreter is
exactly the kind of claim that rots silently.

## L174 — the array literal: L151's producer with a list in front of it, and the first real oof movement in four rungs

`array` was 7 of the slice's 89 out-of-fragment bodies. It is the first rung since L170 whose census
count actually fell, and it fell by more than the blocker it lifted: **89 → 85**, with four of the
seven bodies landing on a *declaration* rather than on another construct.

### The rule is cheap for one reason, and it is worth naming

`Ty` has no `Array τ`. So the element types are **erased**, nothing is joined across the elements, and
the only thing the traversal owes is the *threading* — the environment and table the elements leave
behind. That is exactly `inferSeq`, which `continueArray` evaluates in the same left-to-right order
`evalExpr`'s `.seq` does, so the arm **reuses the existing third motive** instead of adding a fourth
mutual function:

```lean
| .array es =>
  match inferSeq D Γ es top ctx with
  | some (_, Γ', D') => some (.cls "Array", Γ', D')
  | none => none
```

and the erasure shows up in the metatheory as an *absence*: `KontOk.arrK` does not mention the
accumulated values at all.

```lean
| arrK {D D' h c Γ Γs τ τ' acc rest Γ' k} :
    inferSeq D Γ rest Γs.isEmpty c = some (τ', Γ', D') →
    KontOk D' h ((c, Γ') :: Γs) (.cls "Array") k →
    KontOk D h ((c, Γ) :: Γs) τ (.arrK acc rest :: k)
```

It is `seqCons`'s shape — `inferSeq` over stored program, an incoming table related to an outgoing one
— with a *fixed* answer type instead of the sequence's last. And `Builtins.allocArr` is
`Builtins.allocStr` with a different boot id and a different payload, so the allocation case is L151's
string literal verbatim: `plainGrow_alloc`, `valueTy_alloc_fresh`, `inv_grow_value`.

### `StrClsOk` became `LitClsOk`, and that is the shape to keep

L151's fourth heap conjunct was *the boot `String` id is a class named `"String"`* — the join between
a rule that claims a **name** and a step that writes an **id**. The array literal needs the same join
at `Boot.arrayId`, and there were two ways to get it: a seventh conjunct on `Inv` (which touches
`inv_value`/`inv_push`/`inv_eval`/`inv_grow_value`/`initiation`/`InvA`/`HeapOk`/`heapOkB` and every
call site that passes `hstr`), or **one conjunct per literal-allocating rule inside the clause that
already exists**. The second is a rename and four `.1`/`.2` adjustments:

```lean
def LitClsOk (h : Heap) : Prop :=
  ((h.classPayload? Boot.stringId).isSome ∧ className h Boot.stringId = "String") ∧
    ((h.classPayload? Boot.arrayId).isSome ∧ className h Boot.arrayId = "Array")
```

**The generalization is the point, not the saving.** Every future literal producer — `Hash`,
`Float`, a `Regexp` — is one more conjunct here and nothing else, and `heapOkB` decides it in the
same certificate. The rename is deliberate: a clause named for one literal invites a seventh
conjunct next time.

### A predicate that was vacuous because the head was out of the fragment

`defFree` had no `.array` arm, so the catchall answered `true`. That was correct while `infer` refused
`.array` and **wrong the moment it did not**: `infer`'s new arm threads the table through the elements
via `inferSeq`, so an element `def` really does change it, and `infer_mono`'s `D₀ = D` conclusion would
have been false. The build caught it — `Proof/Static/Mono.lean` stopped closing — which is
`HANDOFF.md` constraint 4 doing its job one indirection out from where that constraint is usually
quoted. The lesson generalizes:

> **When admitting a head, check every predicate whose value at that head was vacuous.** `defFree`,
> `elemsPlain`-style guards and the fragment gate are all "true because `infer` says `none` here"
> until they are not.

### And no splat guard is needed, which is the same argument the send rule makes

`continueArray` sends a `.splat` element to `arrSplatK`, which `KontOk` does not describe. Rather than
guard the rule, the consecution case recovers *not a splat* from the element's **own accepting
judgement** (`infer` has no `.splat` arm, so `absurd he (by simp [infer])`) — the `recvK` case's `hsp`
move, third use.

### The measurement, and why this one moved

| | before | after |
|---|---|---|
| out of fragment | 89 | **85** |
| `array` | 7 | **0** |
| refused with a named atom | 3 | **7** |
| `send-2-args` | 14 | 15 |
| `splat` | 1 | 3 |

**Four of the seven bodies became `needed:` lines, not new out-of-fragment lines** — `Array ~ hash`,
`Array ~ include?`, `Array ~ max`. That is the first time a rung moved bodies from *we have no rule*
to *we have no row*, which is a different and better wall: rows are F6's item, and a body sitting on
one has a fully typed spine.

`--check` moved for the first time since L151: **38 → 39**, one transition, `unknown → accept`, none
the other way. The program is `test_syntax_097.rb`, whose whole text is `[()]` — and that is the same
finding L151 recorded about its fifteen bare string literals, so it is worth repeating rather than
apologising for: **the corpus has no richer in-fragment array literal to offer**, because the binding
constraint is the rest of the fragment.

### Checks

`check-proofs.sh` green, **29** theorems, axiom-clean (`egArray_safe` added); `heapok_probe` prints the
new `LitClsOk` clause and still exits 0 at the prelude-booted heap. `--check` 39 / 1,186 / 0, read by
transition. `--assn` smoke 1,227 clean. `fragment-gap.py --self-test` all agree, two new cases
(`[1, 2]` accepted, `[1, *x]` unknown); `array` moved from `MISSING` to `PARTIAL` with the splat as its
only refusal. Three new checked examples in the build — the non-empty literal, the **empty** one (a
different number of steps: `continueArray _ [] []` allocates with no `arrK` pushed, which is why
`recvK0` is a separate constructor from `recvK` too), and the refused splat.

## L175 — sends at any arity: `inferArgs`, and `KontOk.argsK` grows an accumulator

`send-2-args` was 15 of the slice's 85 remaining out-of-fragment bodies, and it had been named as a
rung since L152 with its price already written down: *`ValuesTy` threaded through a **list** of
argument continuations rather than a single one.* That is exactly what it cost, and the rung is the
general one — **any positive arity**, not two — because `startArgs` is a loop and a fixed-arity rule
would have to be re-cut for three.

### The four pieces

1. **`inferArgs`, a fourth mutual function.** A send needs the arguments' **types**, in order, to
   match against the signature's parameter list, where an array literal (L174) and a statement
   sequence each need only the threading. So `inferSeq` cannot be reused and `inferArgs` is its own
   traversal — mirroring `startArgs`' loop arm for arm and refusing nothing by name, since `.splat`,
   `.kwargs` and `.fwd` have no `infer` arm.
2. **`KontOk.recvK` over a list.** `inferArgs D Γ (arg :: args) … = some (τs, Γ₂, D₂)` and
   `sigOf D₂ τ mname = some (τs, τret)` — the whole parameter list, read at the table the **last**
   argument leaves.
3. **`KontOk.argsK` grows an accumulator.** The kont stores already-evaluated values and unevaluated
   program, and the constructor now says so on both sides:
   ```lean
   ValueTy h recv τr → ValuesTy h acc τacc →
   inferArgs D Γ rest Γs.isEmpty c = some (τrest, Γ', D') →
   sigOf D' τr mname = some (τacc ++ τ :: τrest, τret) → …
   ```
   **The signature is split at the in-flight value's position**, which is the shape that makes each
   step a one-line rewrite: one value moves from `rest` to `acc`, and `τacc ++ τ :: τrest` moves with
   it by `List.append_assoc`. `ValuesTy_snoc` is the value half.
4. **`inferOpenArgs`, and `OArgs`.** The open front end needs the same traversal. Its answer is a
   *list* of types, so it cannot be an `OResult` — and the failure is kept as its own two
   constructors rather than wrapped, because §11's whole value is in **which** construct inside an
   argument stopped the body. A first draft wrapped the failure as `OArgs.bad (r : OResult)`; that
   made `OArgs.bad (.ok …)` a reachable *shape* the proofs had to refute, and it was withdrawn for
   the arms that cannot lie.

### The user arm is still refuted by arithmetic, and now at every arity

`step_ok`'s final-argument case refutes `UserEntryOk` because `UserConforms` requires
`d.params = []` while this declaration's is `τacc ++ [τ]` — and a snoc is never `[]`. So **a send
with arguments is a builtin send, necessarily, at any arity**, and the refutation did not get harder
when the list did. That is the same L152 argument with `[τ]` generalized, and it is worth noting that
it is the *shape* of the parameter list rather than its length that does the work.

### What the factoring proof cost, and the lesson about `simp_all`

`Proof/Static/OpenSelf.lean`'s two theorems are single uniform `| _ =>` tactics over ~60 cases, and
this rung added a fourth motive to both. `inferOpen_mono` took one line. `inferOpen_factors` took
five alternatives and one **non-obvious** fact:

> **`inferOpenArgs` must be kept *out* of the factoring proof's `simp_all` list.** Unfolding it there
> destroys the defining equation `inferOpenArgs D Γ₁ args ctx s₁ = .ok τs Γ' s'`, and the send
> alternatives need exactly that equation to push their store bound back to the *receiver*
> (`storeLe_subArgs`). Without it there is no route from `s₁` to the final store at all — the bound
> is not recoverable from anything else in the context.

So the traversal's own two cases split on the answer and unfold it locally, which is one alternative,
and the send cases keep their equation. Two residual side goals are discharged after the block rather
than inside each alternative — the `requireRow` step's own `StoreLe`, and the list equation the split
leaves behind — because folding them in made every alternative a different shape.

The other lesson is one this file has recorded three times in a different guise: **when a `simp_all`
does too much, the fix is to take a definition *out* of its list, not to add lemmas to it.** The two
minutes spent reading the failing goal's *context* (the equation was gone) beat any number of
attempts at strengthening the tactic.

### The measurement

| | before | after |
|---|---|---|
| out of fragment | 85 | **84** |
| `send-2-args` | 15 | **0** |
| `const` | 19 | **28** |
| `return` | 20 | 21 |
| refused with a named atom | 7 | **8** |

Fifteen bodies moved and one came out, which is the pattern by now — but read where they went:
**`const` is 28 of the remaining 84**, a third of the whole census and more than twice the next
blocker. The class-object arm of `Ty` plus a constant table is now unambiguously the binding item,
which is what D13 predicted would happen once the duck-typed spine was in.

`--check` is **byte-identical**: `baseDecls` has no two-parameter row, so no *program* can reach the
new arity yet — the L157/L171 situation, and the capability is asserted against `infer` at a
hand-built table instead.

### Checks

`check-proofs.sh` green, 29 theorems, axiom-clean. `--check` byte-identical to L174's capture.
`--assn` smoke 1,227 clean. `fragment-gap.py --self-test` all agree, with `shape_send`'s arity
refusal replaced by a *splat/kwargs/fwd* refusal and two new cases. Two new checked examples in
`Proof/StaticSoundness.lean`: a two-argument send accepted against a two-parameter row, and an arity
mismatch refused by the same list equality.

## L176 — `Decls` becomes a structure, so the constant table costs no index

`const` is 28 of the slice's remaining 84 out-of-fragment bodies — a third of the census — and
`HANDOFF.md` §The next commit prices it as **two** rungs, of which the cheaper is *a constant whose
value is a plain object needs a table threaded exactly as `Decls` is*. This commit is the threading,
landed **inert**, and the reason it is its own commit is the argument for its shape.

### Why the constants go in `Decls` rather than beside it

L160 made the declarations a **threaded judgement**: `infer` returns one, `KontOk` carries it as an
index, `Inv` quantifies it existentially, and `CtlOk` ties it to the program. A constant assignment
needs *exactly* that same threading, for exactly the same reason L160 gives — `initiation` obliges the
invariant at the **boot** heap, so a constant the program's own `casgn` creates cannot be in a table
fixed up front. That is the thirteenth session's finding about `declsOf`, restated at a different
table, and it is worth restating because the same trap is one document away from being fallen into
twice:

> **A table the program writes cannot be a function of the program alone.** `declsOf` was written
> program-indexed and returned `baseDecls` for four rungs; the repair was L160–L163. A constant table
> computed up front would repeat it exactly.

Given that, there were two shapes:

* a **parallel** `Consts` threaded beside `Decls` — which costs a new component in `infer`'s answer, a
  new index on three `KontOk` constructors (`seqCons`, `ifK`, `recvK`), a new existential in `Inv`, a
  new parameter on `CtlOk`, and a mention in every consecution case;
* **one more field on the value that is already threaded** — which costs a structure, four accessor
  rewrites, and nothing else.

The second is this commit. `Decls` was `abbrev Decls := List (String × List (String × MethodDecl))`;
it is now

```lean
structure Decls where
  rows : List (String × List (String × MethodDecl)) := []
  consts : List (String × Ty) := []
```

and `declsFor`/`declaresName`/`addRow`/`baseDecls`/`declTys` read `D.rows`. **Total churn: five
definitions and six `D.find?` → `D.rows.find?` rewrites in proofs**, which is the measurement the
choice was made on. Every `simp [declsFor, baseDecls, …]` in the corpus of checked examples still
computes, because `baseDecls` is still a literal.

### What is *not* here, deliberately

No `constTyOf`, no `addConst`, no `SubDecls` clause for the constants, and no `ConstsOk`. This file's
own norm — *write the proof, then keep the clauses it used* (L~150) — says an accessor with no consumer
is a speculative clause, and the cost of one is every future step that has to re-derive it. What the
commit claims is only that **the threading exists and is inert**, which is the L141/L157 stance: land
the shape, measure that no verdict moved, and let the rule that needs it come next.

The `consts` field being empty is also what makes the inertness argument short: `SubDecls` is stated
over `declFor`, which reads `rows`; `infer`'s `D₁ = D` stability tests compare a structure whose second
field never changes; and `DeclsOk` mentions `declFor` only.

### Checks

`--check` over the 1,227 cached ASTs **byte-identical** at 39 / 1,186 / 0. `--assn` smoke 1,227 clean.
`check-proofs.sh` green, 29 theorems, axiom-clean. `fragment-gap.py --self-test` all agree.

## L177 — the constant table's measurement, and it changed the clause before the clause was written

`HANDOFF.md` §The next commit prices `const`'s cheaper half as *a constant whose value is a plain
object needs a table threaded exactly as `Decls` is*. L176 landed the threading. This is the
measurement that has to come before the rule, and it is in this file for the reason the four earlier
probes are: **it moved the design.**

### The question, and why it is not the one the rung looks like

A constant *read* is not one table lookup. `evalExpr`'s `.const` arm is artifact 03 §4's two phases:

```
cref.firstM (constOwn h · n)  |>.orElse  (fun _ => constLookupFrom h defmod n)
```

— lexical over the frame's `cref`, innermost first, then inheritance over `ancestors h defmod`. So a
table keyed on the **name** alone is sound only if that whole walk, from every frame the fragment
admits, reaches the one class the table is about. Two things can break it, and both are real:

1. **Shadowing.** `X = 5` at toplevel writes `Object`'s constant table; `class String; Y = 7; end`
   writes **String's** — and the model gets both right (checked by running it: `5` then `7`). So
   shadowing is a possibility to be excluded, not a hypothetical.
2. **`Object` not being reachable.** The inheritance phase finds `Object`'s table only if
   `Object ∈ ancestors h defmod`.

### What the probe found, and the correction

> **The obvious clause is false.** *No class other than `Object` owns this name* fails at the
> prelude-booted heap: **five names are owned by both `Object` and `T`** — `Struct`, `Enumerable`,
> `Range`, `Hash`, `Array`. And `T` is the sorbet shim, which is what the slice's `sig` blocks are
> made of, so this is not an exotic collision waiting in some corner of the prelude.

The clause that is *true* is stated over the **reach**: nothing strictly in front of `Object` **on the
definee's own ancestor chain** owns the name. And that population is two classes wide:

```
ancestors Object = [Object, Kernel, BasicObject]                    Object at 0
ancestors String = [String, Comparable, Object, Kernel, BasicObject] Object at 2
classes strictly in front of Object on an admitted chain: {String, Comparable}
constants they own: 0
```

So the clause is a `decide` over **two** classes rather than over the heap's 87 class objects, and it
is discharged at 0. `T` is not on any admitted chain, which is why the five names are a *report* rather
than a failure — and the probe stops exiting 0 the moment `reopenableClasses` grows to something under
`T`, which is the regression it exists to catch.

**This is the fifth time a forty-line probe has changed a clause rather than confirmed one**
(`alloc_probe` L142, `ancestors_probe` L144, `names_probe` L162, `heapok_probe`'s L153 hook shape, and
now this), and the pattern in all five is the same: the clause that is easy to *state* quantifies over
the whole heap, the clause that is *true* quantifies over the population the fragment can actually
reach, and only a measurement tells you which. The general form, worth having in one sentence:

> **Before proving a clause, compute the set it quantifies over.** If that set is the heap, ask what
> the fragment can reach; the answer is usually much smaller, and the difference is the difference
> between a `decide` and an induction.

`scripts/consts_probe.lean` is in `check-proofs.sh` as its fifth measurement section.

### Checks

`check-proofs.sh` green with the new section, 29 theorems, axiom-clean. Nothing in the SUT changed, so
no verdict diff is owed — and none is claimed.

## L178 — L177's clause, carried: `ClassOk` gains `NoShadowBefore`

The measurement is L177's; this is the clause it produced, landed in the invariant and decided by the
same certificate `ClassOk` already had. Inert — nothing reads it yet, and the rule that will is the
next commit.

### The clause, and why it is stated over a chain rather than over the heap

```lean
def NoShadowBefore (h : Heap) (k : ObjId) : Prop :=
  Boot.objectId ∈ ancestors h k ∧
    ∀ j ∈ (ancestors h k).takeWhile (· != Boot.objectId),
      ∀ cp, h.classPayload? j = some cp → cp.consts = []
```

Both conjuncts are one half of *a constant read reaches `Object`'s table*: `Object` is on the chain,
and nothing gets there first. The `takeWhile` is the whole point — L177 measured that the population
it quantifies over is `{String, Comparable}` (which owns 0 constants) where the heap has 87 class
objects and five names owned by both `Object` and `T`. Stated over the heap the clause is **false**;
stated over the chain it is a `decide`.

It goes **into `ClassOk`** rather than becoming `Inv`'s eighth conjunct, and for the reason `ClassOk`'s
own docstring already gives about `className h Boot.objectId = "Object"`: it is the same kind of fact
as the rows around it and `classOkB` decides it in the same pass. Two instances — at `Boot.objectId`
(the toplevel frame's definee, `BottomObj`) and at each reopenable class's object (a method body's).
Those are exactly the two definees a fragment frame can have.

### What it cost

| | |
|---|---|
| `Proof/Static/Decls.lean` | the definition, `noShadowBeforeB_sound`, and **two transport lemmas** |
| `HeapCert.lean` | `noShadowBeforeB`, folded into `classOkB` at both instances |
| `Proof/Static/Preservation.lean` | four `.2` → `.2.2` and two `obtain` patterns |

The two transports are the interesting part, and each is one rewrite:

* **allocation** — `PlainGrow` pins `classPayload?` at every id and `ancestors_congr_grow` pins the
  walk (on `Saturated`, L144), so both conjuncts move by the rewrites `ClassOk`'s other clauses
  already use;
* **`def`** — `ancestors_defineMethod` for the walk, and `consts_defineMethod` for the payload. That
  second lemma was written at L156 *for `ClassOk`*, with a docstring saying it exists because a `def`
  in the body of the very class being reopened is the non-trivial case. It is the exactly-right lemma
  two rungs early, which is worth noting: **a lemma written for one clause because the author asked
  what the step touches tends to be the one the next clause needs.**

### Checks

`--check` **byte-identical** at 39 / 1,186 / 0. `check-proofs.sh` green, 29 theorems, axiom-clean —
and note `classOkB` is inside `heapOkB`, so F0's certificate now decides the new clauses too, at both
the bare boot heap (`by decide`, in `heapOk_initHeap`) and the prelude-booted one (`heapok_probe`,
which now prints them). `consts_probe` still exits 0.

## L179 — `--consts`, the fourth ratchet, and it withdrew this session's own sequencing advice

L176–L178 landed the constant table's three prerequisites — the threading, the measurement, the
`ClassOk` clause — on the strength of an ordering claim `HANDOFF.md` made twice: *`const` is two rungs,
do the constant table first, it is the cheaper half and it is precedented.* This is the measurement of
whether that is true, and **it is not** — cheapness was measured and **value was not**.

### The ratchet

`python3 homebrew/fragment-gap.py --brew … --consts` reports two things over the slice's real ASTs: the
constant **reads** by name, and every `casgn`'s **right-hand-side head**.

```
reads:  T 259   String 225   Integer 42   Token 24   Regexp 20   StemParser 20   Version 17  …
casgn:  45 × <send>      3 × <str>
```

Both halves say the same thing. The reads are dominated by **class and module names**, which a table
cannot type — they need a type for a class *object*. And 45 of the 48 assignments are initialized by a
**send** — `T.let(…)`, `Regexp.new(…)`, `%w[…].freeze`, `{…}.freeze` — whose receiver is a class name,
so tabulating the constant needs the class-object arm *first*. Three assignments are string literals.

> **The class-object arm of `Ty` is not the second half of `const`. It is the gate on all of it.**

### What this is an instance of

`HANDOFF.md` §Things I got wrong already records the shape twice — *a blocker that explains the symptom
will stop you looking for the one that explains the shape* — and this is its third instance, with a
twist worth stating separately because it is about **ranking** rather than about blockers:

> **Cheap and valuable are two measurements, and a rung needs both.** The constant table was priced
> honestly (it is cheap: `addRow`'s precedent, and L176 measured the churn at five definitions). What
> was never computed is what it *unblocks*, and the answer is 3 of 48. The two orderings disagree, and
> only the second one is about the metric.

It is also the fourth time this session that a census over the real ASTs has re-ranked the work
(L167's `def`-params, L168's re-rank on lifting it, L173's front-end lesson, and now this) — which is
why the report is a **flag on the tool** rather than a paragraph in a document. A number in prose is
remembered; a number the tool computes is recomputed.

### What survives, and it is not nothing

L176's threading (`Decls.consts`) and L178's `NoShadowBefore` are **needed either way**, because a
class-name read *is* a constant read through the same two-phase lookup: `Token.from(x)` reads the
constant `Token` through `cref.firstM (constOwn h · n)` and then the ancestor walk. The class-object arm
needs the same clause. So the three prerequisite commits are re-sequenced, not withdrawn — and
`HANDOFF.md` §The next commit now says so, with the boxed correction in place of the advice it
replaces.

### Checks

Nothing in the SUT or the metatheory changed; `--consts` is a new reporting flag on the census tool and
`fragment-gap.py --self-test` still agrees. No verdict diff is owed and none is claimed.

## L180 — the class-object arm, priced by measurement: the constructor is not the cost

L179 showed the class-object arm gates all 28 of the slice's `const` bodies. This is the measurement
that has to come before it, and — fifth in a row — it says the arm's cost is **not** where it looks.

### The question

The arm would be `Ty.clsObj n` = *the class object named `n`*. `EntryOk` is stated over
`∀ k, TyClass h τ k → ResolvesAt h k mname bid`, so the arm's `TyClass` must name **the id dispatch
walks from** — which for a `.ref` is `classOf`:

```lean
match (h.get o).eigen with | some e => e | none => (h.get o).klass
```

i.e. the eigenclass when one has been materialized, and `Class`/`Module` when one has not.

### The measurement

```
class/module objects: 87     with a materialized eigenclass: 27     without: 60
Object  ✓  #<Class:Object>   ancestors [45, 44, 3, 2, 1]…
String  ✓  #<Class:String>   Array ✓   Regexp ✓
Integer ✗  Class             ancestors [3, 2, 1, 33, 0]…
Float   ✗  Class             Hash  ✗   Symbol ✗
```

**Two findings, both about the clause rather than the constructor.**

1. **The eigenclass is not always there — and the split runs straight through the classes the slice
   uses.** `String`, `Array`, `Regexp` and `Object` have one; `Integer`, `Float`, `Hash` and `Symbol`
   do not, and dispatch for those goes through `Class`. So `TyClass (.clsObj n) k` cannot be *the
   eigenclass of the class named `n`* — that is not total, and stating it uniformly would be
   unprovable for 60 of 87 class objects. It has to be **whatever `classOf` says**, carried.
2. **Carrying it is the price.** `eigenclassOf` mutates `eigen` on an **existing** id, so a step that
   materializes `Integer`'s eigenclass moves `classOf (.ref Integer)` from `Class` to a fresh id and
   **falsifies any stored fact about it**. That is `HANDOFF.md` §What is not next item 1 —
   *`TypeAgree`'s first clause is false as stated because `eigenclassOf.go` mutates `eigen` on existing
   ids* — arriving at the class-object arm rather than at the allocating `class'` branch it was written
   for. It is also, read the other way, *why `plainRecv` excludes classes at all*: the exclusion was
   buying exactly this. Nothing in today's fragment materializes an eigenclass (`defs`, `sclass`,
   `singleton_class` are all out of `infer`'s domain), so the clause is establishable — but it is a
   clause, and it is the arm's real cost.

So the arm is: one `Ty` constructor (cheap), a `valueTy?` arm (cheap), a `TyClass` arm that names
`classOf` (cheap), and a **transport clause across eigenclass materialization** plus `entry_dispatch`
surviving `invoke`'s receiver-shape special cases for a `.cls` payload (the whole cost). Same shape as
the producer's bill (L142–L149): four items named, three of them small, and the pricing is what tells
you which.

### The ratchet the probe leaves behind

The probe is mostly a report — there is no clause to ratchet yet — but one fact today's design rests on
is checkable and is now checked: **no class object is `plainRecv`.** `valueTy?` types a `.ref` only
when `plainRecv`, and `entry_dispatch` discharges `invoke`'s three receiver-shape special cases from
exactly that. A class object that became `plainRecv` would make the dispatch lemma false and nothing
else in the build would notice. It is `check-proofs.sh`'s sixth measurement section.

### Checks

`check-proofs.sh` green with the new section, 29 theorems, axiom-clean. Nothing in the SUT changed; no
verdict diff is owed and none is claimed.

## L181 — which row the class-object arm needs first, and it is behind neither wall

L179 said the class-object arm gates all 28 `const` bodies; L180 priced the arm (the transport clause,
not the constructor). This is the third question in that sequence and the one that decides the *rung
after* it: **once a class object has a type, which declaration row does the slice actually read
through it?**

`--consts` now groups constants in receiver position by the method called on them, because the method
name decides which wall the row is behind:

```
123  ===        neither wall — a non-allocating `Module` builtin
 67  nilable    inside a `sig` block  ⇒ Wall 1
 56  new        Wall 2 — `ConformsAt`'s allocating conclusion
 42  let        Wall 1      27  untyped  Wall 1      17  must  Wall 1
 12  last_match             9  from                  8  any / fetch
```

**`===` is the largest by a factor of two, and it is the only large one behind neither wall.**
`String.===` alone is 71 and the six `Token` subclasses are another 38 — which is `case x when String`
and `when AlphaToken`, i.e. the `case`/`when` idiom, i.e. **exactly D13's occurrence typing**. So the
sequence the measurements pick out is:

1. the class-object arm (L180's price: a transport clause across eigenclass materialization, plus
   `entry_dispatch` surviving `invoke`'s `.cls` receiver arms — which fall through to `invokeDispatch`
   for every `mname ≠ "new"` outside `Boot.regexpId`/`Boot.mathId`, so the refusals are the
   `send`/`public_send`/`raise` kind `ConformsAt` already carries);
2. a `Module#===` row — non-allocating, so its `ConformsAt` is the shape that already works;
3. narrowing on it, which is D13's dependency and `nontrivial-target.md` §5.3's P1′.

And what *not* to start with, now with numbers: `.new` (56) is behind Wall 2, and the `T.*` family
(161 across `nilable`/`let`/`untyped`/`must`/`any`) is behind Wall 1 because every one of them is
inside a `sig` block. Between them that is 217 of the 337 receiver-position occurrences — so **two
thirds of `const`'s receiver uses are behind the two walls**, and the third that is not is `===`.

### The pattern these four measurements form

L177 changed a clause. L179 changed an ordering. L180 changed what a rung's cost *is*. L181 picks the
row. None of them is a proof, all four took under an hour, and each was written because the previous
one had already changed a design:

> **When a rung is large, the cheapest next move is usually a measurement, and the question to measure
> is "what does the artifact actually contain", not "will my clause hold".** Four for four this
> session.

### Checks

`--consts` is a reporting extension; `fragment-gap.py --self-test` still agrees. Nothing in the SUT or
the metatheory changed, so no verdict diff is owed and none is claimed.

## L182 — the shortest path to `const`, and why it is four rungs in a forced order

The last three entries are measurements; this is the plan they add up to, written down because the
sequencing is **forced** rather than chosen and because three of the four rungs move the census by
zero. `slice-verdict.md` §4a is the table; this is the reasoning.

### The chain

1. **A top type `Ty.any`**, with `subTy` at *argument positions only*.
2. **The class-object arm `Ty.clsOf n`** (L180's price: the transport clause across eigenclass
   materialization, not the constructor).
3. **A `Module#===` row** on that arm.
4. **Narrowing** on `===` — D13's occurrence typing.

### Why the order is forced, and it is rung 3 that forces it

`Module#===`'s signature is `(Object) → Boolean`. Give it a *concrete* parameter and `case x when String`
types only when `x` is already known to be a `String` — which is exactly the case the program is
testing. The row is useless rather than merely weak, so the top type is not an optimisation of rung 3,
it is its precondition. And rung 2 without rung 3 types no call site at all: a class object with a type
but no rows is L141's `Ty.cls` situation, which accepted no new programs for ten rungs.

### The trap in rung 1, and it is worth naming before someone falls into it

The tempting move is to make `ValueTy` a **relation** — `valueTy? h v = some τ` becomes
`ValueTy h v τ` with a `.any`/union arm — so a value can have several types. That is what
unions/nilable genuinely need (and `if`, and `begin`), and its price is real: `CtlOk`'s eval case has to
admit a *supertype* of what `infer` computed, which threads a `Sub` through all **39**
`inv_value`/`inv_push`/`inv_eval` call sites in `Proof/Static/Preservation.lean`.

**A top type at argument positions needs none of that.** The observation is that imprecision only has
to live where a *declared parameter* does:

* `ValuesTy` weakens from `valueTy? h v = some τ` to `∃ σ, valueTy? h v = some σ ∧ subTy σ τ` — and for
  a concrete `τ` those are the same proposition, so the three `baseDecls` rows' conformance proofs see
  an identical hypothesis;
* `KontOk.recvK`/`argsK` carry a pointwise `subTy` where they carry an equality, which for `argsK`
  means the *parameter* list is what gets split at the in-flight value's position rather than the
  inferred list;
* **`CtlOk` does not change at all** — the in-flight value keeps its exact type, and `inv_value` and
  friends keep their signatures.

23 `ValuesTy` mentions, few consumers. That is the whole of rung 1.

### Why this is written as a plan rather than built

Three of the four rungs move the census by **zero**, and the fourth needs all three. Landing rung 1 or
2 alone is legitimate (`HANDOFF.md`'s *land it inert* norm, and L141/L157/L171/L176 all did it) but it
is not progress on the metric, and the thing a reader needs before starting is *which* four and *why
that order* — which is what the last four entries measured and what this one records.

### Checks

Documentation only. `check-proofs.sh` green, 29 theorems, axiom-clean; `--check` unchanged at
39 / 1,186 / 0; `--self-test` all agree.

## L183 — the top type: rung 1 of four, and it costs `CtlOk` nothing

`slice-verdict.md` §4a's first rung, landed. `Ty` gains `any`, `subTy`/`subTys` compare an argument
against a **declared parameter**, and that is the whole of it. Inert in the checker by construction —
no row has an `any` parameter yet — and the capability is asserted by four checked examples at a
hand-built row.

### The design decision, restated because it is the whole point

There are two ways to admit imprecision, and they cost very differently.

* **Make `ValueTy` a relation** so a value can have several types. This is what unions and nilable
  need, and its price is that `CtlOk`'s eval case must admit a *supertype* of what `infer` computed,
  threading a `Sub` through all **39** `inv_value`/`inv_push`/`inv_eval` call sites.
* **Put the imprecision at the *declared parameter*** and nowhere else. `valueTy?` has no `any` arm,
  so nothing is ever typed by it; `infer` never answers `.any`; and the in-flight value keeps its exact
  type all the way to the dispatch.

L183 is the second, and it is what makes rung 1 small:

| | |
|---|---|
| `ValuesTy` | `ValueTy h v τ` → `∃ σ, ValueTy h v σ ∧ subTy σ τ` |
| `KontOk.recvK` | `sigOf … = some (τs, τret)` → `some (ps, τret)` **plus** `subTys τs ps` |
| `KontOk.argsK` | the split moves from the *inferred* list to the **parameter** list: `psacc ++ τp :: psrest`, with `ValuesTy h acc psacc`, `subTy τ τp`, `subTys τrest psrest` |
| `CtlOk`, `Inv`, `inv_value`/`inv_push`/`inv_eval` | **untouched** |

### The lemma that makes it inert, and it is one line

`subTy_concrete : τ ≠ .any → (subTy σ τ = true ↔ σ = τ)`. Every `baseDecls` row has concrete
parameters, so `entryOk_int`'s conformance obligation sees the proposition it always saw — the proof
gained exactly one `obtain` and one rewrite. That is the test of whether a weakening is really a
weakening: **if the old consumers need new arguments, the generalisation was in the wrong place.**

`subTys` is pointwise *and length-forcing*, so the arity check is unchanged: the top type widens a
**position**, never the list. Asserted (a two-argument call on a one-parameter `any` row is `none`).

### Where the extra bookkeeping actually landed

`KontOk.argsK`. It stores evaluated values and unevaluated program, and the signature is split at the
in-flight value's position; with subtyping the split has to be at the *parameter* list, so the
constructor now carries `psacc`/`τp`/`psrest` and three `subTy` facts instead of two type lists. Each
consecution step is still one rewrite — `subTys_cons_inv` peels the head parameter as
`inferArgs_cons_inv` peels the head argument, and the two move together. `subTys_nil_inv` closes the
last-argument case.

Two `Ty`-total matches needed an `any` arm and both are `False`-shaped rather than arbitrary:
`tyClassNames .any = []` (so `declFor` never answers at it and `DeclsOk` obliges nothing) and
`TyClass h .any k = False` (no value is typed `any`, so no receiver arrives with it). Those two lines
are what make the arm a *parameter* type and nothing else.

### What it does not buy, stated plainly

**Zero bodies.** No row has an `any` parameter, so `--check` is byte-identical at 39 / 1,186 / 0 and
the per-body census is unchanged at 84. It is rung 1 of the four §4a prices, and only rung 4 moves the
census — which is exactly what that section says and why it was written before this was built.

### Checks

`check-proofs.sh` green, 29 theorems, axiom-clean. `--check` byte-identical. `--assn` 1,227 clean.
`fragment-gap.py --self-test` all agree. Four new checked examples: an `any` row accepting an
`Integer`, the same row accepting a `String`, the arity check surviving, and a local bound through
such a call getting the *return* type (the assertion that nothing is typed `any`).

## L184 — the class-object arm's *type language*, and the split that stopped the rung from over-reaching

`slice-verdict.md` §4a's rung 2, **cut in half on purpose**. `Ty.clsOf n` — *the class object named
`n`* — exists, has a `TyClass`, and transports; what is deliberately not here is the **producer**
(`valueTy?` still gives a class object no type) and the **rows**. The cut is the finding, so it goes
first.

### Why the rung was split, and how the split was chosen

The natural rung is "add the arm, produce it, put a row on it". Attempting the producer first showed
what it costs, and it is not where L180's measurement pointed:

> **`valueTy?`'s `.ref` arm is inverted by four lemmas, and one of them stops being true.**
> `valueTy_ref_plain : ValueTy h (.ref o) τ → plainRecv h o = true` is *false* once a class object has
> a type, and its consumers are `valueTy_ref_klass_isSome`, `plainRecv_classOf`, `TypeAgree`'s fourth
> clause and `entry_dispatch`'s receiver split — the load-bearing chain L142–L149 took a whole session
> to get right. The producer is therefore a rung of its own, and `Locals.lean`'s own note says why in
> as many words: *an inversion principle is only as strong as the definition it inverts.*

So: the type language now, the producer and its transport next. That is `Ty.cls`'s history exactly —
L141 added the arm with no producer and L151 added the producer ten rungs later — and the reason to
repeat it is the same: the arm being present is what forces every *later* statement to be total over
it, which is where the surprises are.

### What landed

| | |
|---|---|
| `Ty.clsOf (name : String)` | keyed on the class's **own** name, because `infer` cannot name an `ObjId` |
| `tyClassNames (.clsOf n) = []` | **a decision, not a stub** — see below |
| `TyClass h (.clsOf n) k` | `∃ o, (classPayload? o).isSome ∧ className h o = n ∧ k = classOf h (.ref o)` |
| `TyClass_grow`, `TyClass_defineMethod` | one rewrite each, plus one real argument |
| renderers | `T.class_of(n)`, in `--assn` and in `--check`'s `type` field |

**`tyClassNames = []` is where the design decision is.** A row on `.clsOf "String"` is a *singleton*
method (`def self.m`); a row on `.cls "String"` is an instance method. They need different keys in one
table, and there are exactly two candidates:

* the **eigenclass's name** (`#<Class:String>`) — unavailable, because L180 measured 60 of 87 class
  objects with no eigenclass, so for most of them that name does not exist;
* a **prefixed** key (`"%class:" ++ n`) — arithmetically fine, but it obliges every consumer that
  quantifies over keys to know the prefix is unreachable, and `DeclsOk_addRow` is the one that asks:
  it must *refute* a row at a key it did not write, and `¬ (c = "%class:" ++ n)` does not follow from
  the hypotheses it has (`groundClassNames.contains c = false`).

Leaving it `[]` makes `declFor D (.clsOf n) mname = none` for **every** `D`, `n` and `mname` — asserted
as a checked fact — so `DeclsOk` obliges nothing and the key question belongs to rung 3, where the row
that needs it lives.

### The one real argument in the transport

`TyClass_grow` goes *backwards* (`TyClass h' τ k → TyClass h τ k`), so the witness `o` has to be shown
in `h`'s bounds. It is, and the reason is `PlainGrow`'s third clause — **nothing became a class**: the
witness is a class in `h'`, so it was one in `h`, so `classPayload?_isSome_lt` puts it in bounds. That
clause was added at L145 for the allocating producer's benefit and is doing a second job here, which is
the same observation L178 made about `consts_defineMethod`: **a clause written because its author asked
what the step touches tends to be the one the next arm needs.**

### Checks

`--check` byte-identical at 39 / 1,186 / 0; `--assn` 1,227 clean; `check-proofs.sh` green, 29 theorems,
axiom-clean; `--self-test` all agree. Two new checked examples (`declFor` is `none` at the arm, at every
name and in every table). **Zero bodies**, as §4a says of rungs 1–3.

## L185 — the class-object producer: `entry_dispatch` survives a class receiver

L184 landed the type; this is the **producer** and its transport, which L180 said was where the cost
is and L184's split confirmed by trying it the other way round. `valueTy?` now gives a class object a
type, `TypeAgree` gains a fifth clause, and `entry_dispatch` handles a `.cls` payload instead of
refuting it.

### `classRecv`, and the three refusals that make the dispatch case a `simp`

```lean
def classRecv (h : Heap) (o : ObjId) : Bool :=
  o < h.objs.size && o != Boot.regexpId && o != Boot.mathId && (h.classPayload? o).isSome
```

`invoke` intercepts a `.cls` receiver **three** times before `invokeDispatch`, and each interception is
answered by a refusal the judgement carries rather than by an argument:

| interception | refused by |
|---|---|
| `Regexp.escape`/`.quote`/`.union` — singleton methods dispatched by receiver *id* (L106) | `classRecv`: `o ≠ Boot.regexpId` |
| the `Math.sqrt`/`exp`/`log` family, likewise | `classRecv`: `o ≠ Boot.mathId` |
| `invokeMaybeNew`, which **allocates** instead of dispatching | `ConformsAt`: `mname ≠ "new"` |

That is `plainRecv`'s pattern for the fourth and fifth time — *a side condition a later rung has to
derive at the use site is cheaper in the judgement* — and it is what turns the class case of
`entry_dispatch` into one `simp` beside the plain one. The `new` clause costs nothing (no row is named
`new`) and `Class#new` is Wall 2's item regardless, since it allocates.

**`classPayload?` rather than a payload match**, and the choice is not cosmetic: stated that way the
`defineMethod` transport *is* `classPayload?_isSome_defineMethod` — the lemma `TypeAgree`'s third
clause already uses — instead of a fresh argument about payload shapes.

`eigen` is deliberately unconstrained, unlike `plainRecv`'s `eigen.isNone`. A class object legitimately
has one (27 of 87 do) and its presence is exactly what `classOf` reads; that asymmetry is why the
*type* is keyed on the class's own name while `TyClass` names `classOf`'s answer.

### The lemma that stopped being true, and what replaced it

> **`valueTy_ref_plain : ValueTy h (.ref o) τ → plainRecv h o = true` is false once a class object has
> a type**, and its four consumers are the load-bearing chain L142–L149 spent a session on. This is
> `Locals.lean`'s own lesson turned on itself: *an inversion principle is only as strong as the
> definition it inverts.*

The replacement is a **disjunction**, `valueTy_ref_inv`, with two arm-specific corollaries so that
every consumer says which arm it is about:

* `valueTy_ref_plain` survives, restated at `ValueTy h (.ref o) (.cls n)` — the type pins the arm;
* `valueTy_ref_class` is its twin at `.clsOf n`;
* `valueTy_ref_klass_isSome`/`_klass_lt` move from taking a `ValueTy` to taking a `plainRecv`, because
  that is what they were ever about;
* `valueTy_shapes`' fifth alternative becomes `plainRecv ∨ classRecv`;
* `valueTy_ref_cls` becomes a disjunction of the two type shapes;
* `user_dispatch`'s receiver type is **pinned to `.cls cn`** rather than abstract — every caller had
  that shape already (`UserEntryOk` requires `τr = .cls c`), and pinning it is what keeps a class
  *object* out of a lemma whose dispatch goes through `invokeDispatch`.

`ValueTy.congr` splits into two branches that read *different* clauses of `TypeAgree`: the plain one
needs `classOf` and `className` agreement at the **class** id, the class-object one needs `className`
at `o` itself — because its type is keyed on the object's own name. That asymmetry is the arm in one
sentence.

### What it does not do

**No `infer` rule produces a `.clsOf`**, so `--check` is byte-identical at 39 / 1,186 / 0 and the census
is unchanged at 84. `tyClassNames (.clsOf n) = []` still, so no row can be read through it. Rung 2 of
`slice-verdict.md` §4a is now complete — arm, producer, transport — and rung 3 is the key space plus a
`Module#===` row.

### Checks

`check-proofs.sh` green, 29 theorems, axiom-clean; `alloc_probe` exits 0 (it is the probe that would
notice a `ValueTy` arm typing something it should not). `--check` byte-identical; `--assn` 1,227 clean;
`--self-test` all agree. Four new checked examples: `String`'s class object is typed
`T.class_of(String)` at the booted heap, the two arms are disjoint there, and both special-cased
receiver ids are refused.

## L186 — is the row witnessable? Measured, and the hazard was real

Rungs 1 and 2 of `slice-verdict.md` §4a are built (L183, L184/L185). Rung 3 is the row they exist
for — `Module#===`, 123 of the slice's 337 receiver-position constant occurrences and the only large
population behind neither wall (L181). This is the measurement that has to come before writing it,
sixth in the sequence, and like the five before it the answer was not obvious.

### What `DeclsOk` obliges of a row on `.clsOf n`, and why neither half is about types

1. **`ResolvesAt h k "===" bid`** at `k = classOf h (.ref o)` — the eigenclass when there is one and
   `Class` otherwise (L180). Needs `lookupIn` to find a *builtin* with `undefined = false`,
   `visibility = .pub` and **`fromPrelude = false`**, and needs `crubyShadow` to answer `none` over the
   chain in front of the owner.
2. **`ConformsAt`** — `Builtins.run bid recv [b] m = .ok w m`, the machine unchanged.

### The hazard, and it is not hypothetical

> **`prelude/prelude.rb:44` defines `Object#===` in Ruby.** That makes it `fromPrelude = true`, which
> `ResolvesAt` refuses outright — and `Object` is on *every* class object's dispatch chain. So the row
> is witnessable only if `Module`'s builtin `===` comes **first**, which is an ordering fact about
> `ancestors` and nothing the type language can promise.

It does. Measured over all seven keyable class objects:

```
Array (class object 11): dispatch class 48 (#<Class:Array>)
  owner = 2 (Module)   builtin = some Module#===   fromPrelude = false   .pub
  chain before owner = [48, 45, 44, 3]             crubyShadow = none
Integer (class object 7): dispatch class 3 (Class)
  owner = 2 (Module)   … chain before owner = [3]  crubyShadow = none
the prelude's Object#===: builtin = none, fromPrelude = true      ← behind Module, never wins
ConformsAt's side condition: deferTwin? = false for all seven
```

Both shapes L180 found are covered — the four classes with an eigenclass and the three without — and
`Module` precedes `Object` on both. `Builtins/Modules.lean:37` gives the conformance half by
construction: `isA` reads the heap and writes nothing, so `run … m = .ok (.bool …) m` with the machine
unchanged, *provided* the receiver's `classPayload?` is `isSome` — which is `classRecv`'s own clause,
already carried by L185.

**Ratcheted rather than reported**, unlike L180's, because the thing it establishes is exactly the kind
a prelude change can silently reorder: it is `check-proofs.sh`'s seventh measurement section.

### The sequence, and what it is worth

Six probes, each written because the previous one had already changed something: L177 changed a clause,
L179 an ordering, L180 what a rung's cost is, L181 which row, L186 whether that row exists at all.
Every one of them is under an hour of `IO` and none is a proof. The pattern is now well enough
established to state as a working rule:

> **A rung's risk is almost never in the statement you are about to write; it is in a fact about the
> artifact that you are about to assume.** Measure that fact first. The measurement is cheap, and four
> of the six changed the design.

### Checks

`check-proofs.sh` green with the new section, 29 theorems, axiom-clean. No SUT or metatheory change, so
no verdict diff is owed and none is claimed.

## L187 — the key space turns out to be avoidable, and two measurements say so

L186 asked whether a `Module#===` row is witnessable at the seven *keyable* class objects. Two
extensions of the same probe answer the design question L184 left open — what key a singleton row
hangs off — by showing it does not need one.

### The measurements

* **All 87 class objects** resolve `===` to the `Module#===` builtin with `undefined = false`, `.pub`,
  `fromPrelude = false` and `crubyShadow = none`. Not just the seven: every id in the booted heap with
  a class payload, scanned.
* **The slice never writes `def ===`** — checked over all eight files.

### Why that removes the key space

L184 left `tyClassNames (.clsOf n) = []` because a row on `.clsOf "String"` (a singleton method) and a
row on `.cls "String"` (an instance method) need different keys in one table, and both candidate keys
cost something: the eigenclass's name does not exist for 60 of 87 class objects, and a prefixed key
obliges `DeclsOk_addRow` to know the prefix is unreachable.

**A row that is the same for every class needs no key.** `declFor`'s `.clsOf` arm can answer
`{params := [.any], ret := .bool}` at `"==="` directly — a *hard-wired* declaration rather than a
tabulated one. The first measurement is what makes that sound: the obligation becomes uniform over
every `n`, and the resolution holds uniformly.

The price is exactly two things, and the second measurement makes the first free:

1. **`declaresName` must report `"==="`.** `DeclsOk_defineMethod`'s side condition is `mname ≠ name`,
   and a hard-wired row is not in `D.rows` for `declaresName` to find — so without this a `def ===`
   would be admitted and the lemma's precondition would not cover the row. Refusing `def ===`
   program-wide costs the slice nothing.
2. **`DeclsOk` obliges `EntryOk` at every `.clsOf n`**, so the resolution has to become a heap
   conjunct — `ClassEqOk h : ∀ k, (classPayload? k).isSome → ResolvesAt h (classOf h (.ref k)) "===" "Module#==="`
   — decided by a bounded scan in `heapOkB` (`classOkB`'s pattern) and preserved across `alloc`
   (`PlainGrow` pins the payloads, `ancestors_congr_grow` the walk) and `defineMethod`
   (`name ≠ "==="`, from item 1).

`ConformsAt` needs no new clause at all: `Builtins/Modules.lean:37` answers `.ok (.bool (isA …)) m`
with the machine unchanged whenever the receiver's `classPayload?` is `isSome`, and that is
`classRecv`'s own clause, already carried by L185.

### The pattern, one more time

This is the second time in three commits that a measurement **removed** a design problem rather than
answering it. L179 removed an ordering (the constant table was cheap and worthless); this one removes a
key space (the row is uniform, so there is nothing to key). Both were found by asking what the artifact
contains rather than what the clause should say — and neither took an hour.

### Checks

`check-proofs.sh` green, 29 theorems, axiom-clean; `classeq_probe` now scans every class object and
exits 0. No SUT or metatheory change, so no verdict diff is owed and none is claimed.

## L188 — the path is six rungs, not four, and building two of them is what found the other two

`slice-verdict.md` §4a priced the path to `const` at four rungs. Rungs 1 and 2 are now built (L183;
L184/L185), and building them made two omissions visible. Both are recorded in §4a, corrected in place.

### The omission

`Ty.clsOf` types a class **object**. Nothing in the fragment ever *produces* one as an expression's
value, because **`infer` has no `.const` arm** — so `String === v` cannot be reached, and a
`Module#===` row would be a row nothing reads. The path needs two rungs between the arm and the row:

* **2a — `CrefOk`, a `StackCtx` clause confining a frame's `cref`.** `evalExpr`'s `.const` is artifact
  03 §4's two phases, and the *lexical* one answers: the read is `constOwn h Boot.objectId n` **iff**
  every class in front of `Object` on the frame's cref owns nothing. `Machine.init` sets
  `cref := [Object]` and `enterClassBody` prepends the class, so it holds in the fragment — but a
  **method** frame takes `md.cref` (`Interp.lean:228`), so `ResolvesUser` has to carry the clause and
  the `def` rule has to establish it from the defining frame. This is exactly the ripple L184's split
  chose not to take, arriving from the other direction.
* **2b — `infer`'s `.const` read**, restricted to `reopenableClasses`. Nearly free once 2a exists, and
  the reason is worth noting: **`ClassOk` already says what the rule needs.** Its per-name clauses are
  `constOwn h Boot.objectId n = some (.ref k)`, `className h k = n` and `(classPayload? k).isSome` —
  which is `ValueTy h (.ref k) (.clsOf n)` term for term, given L185's `classRecv`. A clause written at
  L156 to promise the *reopen branch* of `enterClassBody` turns out to be the class-object read's
  witness, which is the fourth time in this file a clause has done a second job it was not written for.

### And a design correction to rung 3, from the same reading

L187 concluded the `Module#===` row needs no table key because it is uniform in `n`. That is true and
it is the **wrong trade**: hard-wiring it in `declFor` obliges `EntryOk` at *every* `.clsOf n`, which
needs a universal heap conjunct (`∀ k, classPayload? k → ResolvesAt …`) plus its preservation. A
**third `Decls` field** (`srows`, keyed by class name) with **one** row on `"String"` is a single
decidable obligation instead — and `String.===` alone is **71 of the 123** `===` occurrences the row is
for. Uniformity was measured; *what it costs to exploit* was not, which is L179's lesson at a smaller
scale: **cheap to state and cheap to discharge are different measurements.**

### The general shape

> **A rung that looks like a type-language change is usually a frame or heap clause underneath.**
> `const` is not "add a `Ty` arm" — the arm was two commits and neither moved the metric. It is
> `CrefOk`, and `CrefOk` is `ResolvesUser` carrying a list.

### Checks

Documentation only. `check-proofs.sh` green, 29 theorems, axiom-clean; `--check` 39 / 1,186 / 0;
`--assn` 1,227 clean; `--self-test` all agree.

## L189 — the `.const` read: **oof 84 → 79**, and the measurement that should have come first

The census reports each body's **first** blocker. It says nothing about whether removing that blocker
frees the body, because the body may have three more. So the first thing this rung did was compute the
full blocker **set** per method body — which turned every earlier estimate in this file on its head:

```
bodies whose blocker set is a SINGLETON:   11 {const}   3 {super}   2 {cpath}   2 {return}
bodies whose set is a PAIR:                11 {const, return}   3 {ivar-asgn, const}   …
freed by removing {const, return}:         24        {const, return, zsuper}:  33
```

> **Eleven bodies have `const` as their *only* blocker.** Three commits earlier this file concluded the
> class-object arm "buys 0 bodies" — that conclusion came from reasoning about what a `const` needs
> (rows, narrowing) instead of measuring what the bodies contain. It was wrong, and the reason it was
> wrong is worth more than the rung: **a blocker count ranks what to lift; a blocker *set* ranks what
> gets freed, and only the second predicts the metric.**

And the second thing it got wrong: a body moving from *out of fragment* to **`needed: <atom>`** already
reduces the metric. `oof` counts bodies outside `infer`'s domain, not bodies that fail; a send on a
class-object receiver with no row is a `.missing`, which is a *row* question. Five of the eleven landed
there, as `T.class_of(String) ~ === : (α) → _` — the row L186/L187 measured witnessable.

### The rule, and the clause that made it cheap

```lean
| .const n => if reopenableClasses.contains n then some (.clsOf n, Γ, D) else none
```

One step, no continuation — the third rule in the fragment with that property, after `.self'` and
`.vcall`. What it needed was a way to know `evalExpr`'s **two-phase** lookup (lexical over the frame's
`cref`, then the ancestor walk) lands on `Object`'s table. Two clauses do it, and the second is where
the economy is:

* **`StackCtx`** gains `Boot.objectId ∈ f.cref` — a *membership*, deliberately, so that nothing needs to
  know what else is on the list. Established at all four sites: `Machine.init` sets `[Object]`
  (a `simp`), `enterClassBody` **prepends** (`mem_cons_of_mem`), and a method frame takes `md.cref`, so
  `ResolvesUser` carries it and the `def` step supplies it from the defining frame.
* **`ClassOk`** gains, per name, *`Object` is the **sole owner** of a constant of that name* — measured
  first (`consts_probe`: `String` has exactly one owner). With sole ownership, **any** cref hit is
  `Object`'s, whatever the cref is.

Together those make `constRead_sole` say the `orElse` is dead code: the lexical phase cannot miss
(`Object` is on the list) and cannot lie (sole owner). **So the rule needs nothing about `ancestors`
at all** — an earlier draft reached for L178's `NoShadowBefore` at the frame's definee, which would have
needed the definee placed among the keyable classes and a heap-dependent clause transported through
`StackCtx.heap_congr`. The membership is heap-independent, which is why it transports for free.

### And `reopenableClasses` grew from one name to eight, by decision procedure

`scripts/reopen_probe.lean` decides `ClassOk`'s seven per-name conjuncts for every plausible candidate.
Admitted: `String`, `Integer`, `Symbol`, `NilClass`, `TrueClass`, `FalseClass`, `Proc`, `Exception`.
**The refusals are the output worth reading**, and each is a real fact rather than a limitation:

| refused | why |
|---|---|
| `Float` | owns `NAN`/`INFINITY`, so `NoShadowBefore` fails on its own chain |
| `Array`, `Hash`, `Range` | **sole ownership** fails — `T::Array`, `T::Hash`, `T::Range` own those names too. L177's `T` collision, arriving as a refusal rather than as a hazard |
| `Regexp` | one of the two ids `invoke` dispatches a singleton family from (L106), excluded by `classRecv` |
| `Comparable`, `Kernel`, `T` | modules |

Five of the eight are the classes the *ground* arms of `Ty` denote, so the `def` rule gained a
`groundClassNames.contains ctx.cls = false` guard: `tyClassNames` subtracts those from the class arm's
range, so a row keyed on one would owe `EntryOk` over immediates. `DeclsOk_addRow` had that as a
hypothesis all along; this is the rule keeping it true, and it turned a `decide` in the `def` case into
`exact hdf.1`.

### The measurement

| | before | after |
|---|---|---|
| out of fragment | 84 | **79** |
| refused with a named atom | 8 | **13** |
| `reopenableClasses` | 1 name | **8** |

`--check` is **byte-identical** at 39 / 1,186 / 0, read by transition (zero, both ways). `const` is
still 23 — those bodies read `Token`, `Version`, `T`, `AlphaToken`: program classes that do not exist
at the booted heap (so `ClassOk` can promise nothing) and modules. That is the allocating `class'`
branch, not this rule.

### Checks

`check-proofs.sh` green with an eighth measurement section, 29 theorems, axiom-clean; `heapok_probe`,
`consts_probe`, `classobj_probe`, `classeq_probe` all exit 0 with the widened table. `--assn` 1,227
clean. `--self-test` all agree. Two new checked witnesses (`String` read inside a reopened `String`
body; `Token` refused).

## L190 — `--sets`, the fifth ratchet: the number that predicts a move

L189's first act was a measurement it should have taken three commits earlier, and this makes it a
tool so the next reader cannot skip it.

### What the existing ratchets do not say

The third ratchet (`--assn`) reports each body's **first** blocker, because `inferOpen` stops at the
first construct outside its domain. That number ranks *what to lift*. It does **not** predict a move,
because a body may have three more blockers behind the one it names — and this file priced the
class-object arm at "0 bodies" three times on exactly that mistake, then watched L189 move oof by 5
with one rule.

`--sets` computes the full blocker **set** per method body, and reports two things:

* **the singleton sets** — each is a body that *one* rung frees;
* **the marginal-value table** — for every set of up to three constructs, how many bodies it frees.

Measured after L189, over the slice's 120 method bodies (88 blocked):

```
singletons:  8 {const}   3 {super}   3 {return}   2 {cpath}
             1 {ivar-read}   1 {ivar-asgn}   1 {zsuper}
sets:       21 {const, return}     30 {const, return, zsuper}
            29 {const, cpath, return}   25 {const, ivar-asgn, return}
```

### The rule, stated so it is not lost again

> **A blocker count ranks what to lift. A blocker *set* ranks what gets freed.** They disagree, and
> only the second is about the metric. This is L168's lesson in its third form — the first was *a
> census classifies at the outermost node*, the second was *a front-end lift moves the ranking, not
> the count* — and the reason it kept recurring is that the cheap number was the one the tool
> reported.

Two corollaries the table makes visible and prose kept getting wrong:

* **A body moving from *out of fragment* to `needed: <atom>` already reduces oof.** The metric counts
  bodies outside `infer`'s domain, not bodies that fail. Four of L189's five went that way.
* **`{const, return}` is 21 bodies** — a quarter of the census — so the two are worth doing in either
  order but only worth *pricing* together.

### The caveat, stated in the code

`_body_blockers` is a hand-written mirror of `inferOpen`'s arms, exactly as `SUPPORTED` is of `infer`'s,
and it has the same drift risk — the one that made `SUPPORTED` wrong twice. So the report prints its
own body count beside `--assn`'s and says that a large gap means the mirror has drifted. The honest
fix is for `--assn` to report *all* blockers per body rather than the first, which needs `inferOpen`
to keep going past a failure; that is a real change to the front end and it is the next thing this tool
should be replaced by.

### Checks

Reporting only. `--self-test` all agree; `--check` unchanged; nothing in the SUT or metatheory moved.

---

## L191 — `@x = e`, and the transport for a heap write that allocates nothing

Out of fragment **79 → 78**, and one more `pacc` body (3 → 4). One singleton set retired
(`{ivar-asgn}`), and the rung's real yield is combinatorial rather than singular: `ivar-asgn`
appears in three of the top-five entries of L190's marginal-value table.

### The rule

`infer`'s `.vasgn .ivar` arm is a **guard plus the right-hand side's own answer**:

```lean
| .vasgn .ivar _ rhs =>
  match ctx.selfCls with
  | some _ => infer D Γ rhs top ctx
  | none => none
```

The guard is the whole design decision, and it is read off the machine rather than chosen.
`applyKont`'s ivar arm (`Interp/Kont.lean:35`) raises `FrozenError` in *two* branches — a frozen
`.ref` self, and an immediate self, since immediates are frozen — and a raise is a `.jump`, which
`CtlOk` refuses outright. So admitting the write means knowing `self` is a plain unfrozen
reference. `selfCls = some c` is exactly that, through two facts that were already in place:
`StackCtx`'s F1b.11 clause gives the frame's `self` the type `.cls c`, and `valueTy_ref_plain`
turns a class type into `plainRecv`.

**`plainRecv` therefore gained a fifth clause, `!frozen`** — and it is the fifth clause for the
fifth time the same reason: *a side condition a later rung has to derive at the use site is
cheaper in the judgement.* The knock-on was projection arity (`hp.1.1.2`, `hp.1.1.1.2`) and one
new hypothesis on `valueTy_alloc_fresh`, whose call sites pass `rfl` — a literal allocates
unfrozen.

**The environment does not move**, and the asymmetry that buys is worth stating: the invariant
tracks locals, not instance variables, so a write has nothing to record — while the matching
*read* `@x` needs a type to answer with, which would take a per-class ivar table this judgement
does not have. That is why `ivar-asgn` came in at this rung and `ivar-read` did not.

### The transport, which is the actual cost

`@x = e` is the **first admitted rule whose step writes the heap without allocating**. `PlainGrow`
is the wrong shape (nothing grows) and `TypeAgree` alone is not enough: `DeclsOk` reads the method
table and `ClassOk` reads the constant tables, and `TypeAgree` mentions neither.

So `Proof/HeapFacts.lean` gained a bundle,

```lean
structure IvarOnly (h h' : Heap) : Prop where
  size : h'.objs.size = h.objs.size
  klass eigen payload frozen : ∀ o, …
```

— *every field of every object the invariant can see, unmoved* — and `Proof/Static/Decls.lean` §8
transports the whole invariant across it: `noHook`, `saturated`, `litClsOk`, `classOk`,
`noShadowBefore`, `declsOk` (through `entryOk`/`resolvesAt`/`resolvesUser`/`tyClass`) and
`typeAgree`. Each is two lines, because whole `ClassPayload`s are pointwise *equal* rather than
merely shape-equal, so `ancestors`/`lookup`/`className`/`constOwn` are congruent by rewriting.

**The lemma is stated over the four fields rather than over `get`**, and that is the one thing
here that could not be borrowed: `typeAgree_of_get` needs `h'.get o = h.get o` at every in-bounds
`o`, which is *false at the written id* — the ivars differ. That difference is the entire content
of the new `typeAgree_of_fields`.

Three small facts fell out on the way: `objs_getD_set!_oob` (the third case of a `set!` read,
needed because `bindIvar`'s `self` is a `Value` and nothing in the fragment bounds the reference),
and `IvarOnly.lookupIn_eq`/`crubyShadow_eq`, which live in `Static/Decls.lean` rather than
`HeapFacts.lean` because `HeapFacts` imports only `RubyCore.Heap` and `crubyShadow` is `Interp`'s.

### What the delivery case is

One refutation and one transport, with no case analysis on the heap at all — the cheapest
heap-writing rule in the fragment, and cheap for a reason worth keeping: **the invariant is about
dispatch and names, and an instance-variable table is neither.**

### The renumbering, again

`infer` gained an arm, so `infer.induct`'s positional cases moved: the new arm is 15/16, and every
`Mono.lean` case at 15 or above shifted **+2**. Recovery was L189's cheaper procedure rather than
HANDOFF's `trace` one — `#check @RubyCore.Types.infer.induct`, pipe the pretty-printed type through
a paren-matching split, and read the alternatives off in order with their conclusion `Expr`
constructor. That prints the offset directly instead of inferring it from error messages.

### Checks

`lake build Metatheory` green; `check-proofs.sh` all theorems axiom-clean at
`propext + Classical.choice + Quot.sound`; `--check` **39 / 1,186 / 0** — the transition against the
stale `/tmp/check-after.txt` is L174's `test_syntax_097`, already accounted for, so this rung is
inert in the checker; `--assn` smoke 1,227 clean / 0 fail; `fragment-gap.py --self-test` all agree
(two new rows: the write inside a method body accepts, the same write at toplevel is `unknown`
because `selfCls` is `none` there). The interpreter is untouched, so no difftest tier can move.

---

## L192 — fourteen table rows, measured free

Out of fragment **78 → 76**, `needed:` 13 → 15. The cheapest rung in the file: **no proof
changed.** `reopenableClasses` gained the error class names, and `ClassOk` is already quantified
over that list, so the entire cost is `classOkB` still answering `true` at the booted heap.

### Why these names, and how they were found

The rung came out of a measurement, not a guess. `--sets`' singleton list said eight bodies were
blocked by `{const}` alone (eleven after L191 retired `ivar-asgn`), and the obvious next question —
*which constants?* — had never been asked. Answering it took ten lines:

```
Version#update_commit: ['ArgumentError', 'String']
Version#compare:       ['ArgumentError', 'String']
RegexParser#self.process_spec: ['NotImplementedError', 'String']
Version#to_str:        ['NoMethodError', 'String', 'T']
Version#head?:         ['HEAD_VERSION_REGEX']
CVSS#self.valid_values?: ['AC', 'AV', 'CIA', 'PR_UNCHANGED', 'UI']
Purl#==:               ['Purl']
```

So the eleven bodies are **four separate populations**, and only one of them is behind a wall:

* **error class names** (3 bodies) — boot classes, already in the heap, `raise ArgumentError, "…"`;
* **file-level constants** (`HEAD_VERSION_REGEX`, `AC`/`AV`/`CIA`/`UI`, 3 bodies) — need `casgn`
  and a constant *table*;
* **program class names** (`Purl`, `Semver`, `Token`, 2 bodies) — Wall 2, the allocating `class'`
  branch;
* **`T`** (2 bodies) — a module, which `ClassOk` refuses on three clauses.

The lesson is L190's again at one more remove: *a blocker set ranks what gets freed, but a blocker
**name** ranks what it costs.* `const` looked like one rung of 25 bodies and is four rungs of
wildly different price, the cheapest of which was free.

### Free, and measured free

`scripts/reopen_probe.lean` decides all seven `ClassOk` clauses per candidate name, so widening the
table is a `decide` rather than an argument (that is what L189 built it for). Fifteen candidates
were added to the probe; **fourteen pass all seven** and one — `IOError` — is refused because it is
not a constant of `Object` at the booted heap at all. That refusal is the probe doing its job: it
is the only one of the fifteen that would have been a wrong guess.

### A dead table found on the way

`fragment-gap.py` had **two** definitions of `REOPENABLE`, and the one below `shape_class` read
`{"String"}` — dead since L156 because the later module-level assignment won, and unnoticed because
the live copy happened to be right. Consolidated to one definition above its first reader. This is
exactly the one-table-two-readers hazard the file's own `SUPPORTED` comment warns about, and it is
worth recording that the warning was in the file while the bug was three lines below it.

### Checks

`lake build` and `lake build Metatheory` green; `check-proofs.sh` axiom-clean, `heapOkB` still
`true` at the prelude-booted heap (14 more `noShadowBefore` rows reported); `--check` **39 / 1,186 /
0**, byte-identical to L191's capture — the new rows widen `infer`'s `.const` and `class'` arms but
no bootstraptest program reads or reopens an error class at toplevel; `--self-test` all agree.

---

## L193 — `ValueTy` becomes a relation, and `if` gets a join

The rung L183 wrote down and declined. Its own docstring said so:

> Making `ValueTy` a *relation* so a value could have several types is the other design,
> it is what unions and nilable need, and it is deliberately **not** this one.

`--check` moves for the fourth time: **39 → 51 accept, 1,186 → 1,174 unknown, 0 reject**, twelve
transitions, all `unknown → accept`, none the other way. The out-of-fragment metric does **not**
move yet — that needs the open front end's `if` to join too, which needs `ATy` to be able to say
"nilable of a type *variable*", and that is the next commit rather than this one.

### Why the type language was the wall

L190's rule got one more remove at L192 (*a blocker name ranks what it costs*), and asking the same
question of the `if` refusals is what produced this rung. The seven bodies `--assn` reported at an
`if` are not one problem:

```
raise ArgumentError, "…" unless head?     -- one-armed if; arm is not nil
severity&.to_s&.upcase || "UNKNOWN"       -- &. and || are ifs with a nil arm
namespace = nil if namespace && …         -- one-armed if that BINDS A LOCAL
```

The first two are **type** joins. The third is an **environment** join, and it is deliberately not
here: merging `Γ` needs `Env` to become a lattice, and `KontOk`'s environment *equality* — read at
every `frameK` — does not yet tolerate that. So this rung is the type half, honestly scoped.

And it is not a niche: `T.nilable(…)` appears in a quarter of the slice's `sig`s, `return if c` is
two of the three singleton-`{return}` bodies, and `&.`/`||` desugar to exactly this shape. The
type language, not the rule set, was the binding constraint.

### Three definitions, and only three

1. **`Ty.nilable τ`** — the first arm inhabited by values of more than one shape. Not a general
   union: nothing in the slice needs one, and a general union needs a normal form to keep `Env`
   *equality* decidable, which the `if`-merge and the loop-stability condition both rely on.
2. **`subTy`** becomes recursive (`σ ≤ nilable τ` iff `σ` is `nilT`, is that nilable, or is `≤ τ`)
   and gains **transitivity**, which the old one-rule version never needed.
3. **`joinTy`** answers *only* the two cases the fragment produces — the branches agree, or exactly
   one side is `nil`. It is **not** a least upper bound, and answering `.any` for the rest would be
   actively wrong: `ValueTy h v .any` holds for *every* value, so an `.any` in an *inferred*
   position would let the checker forget what it knows. `.any` stays a declared-parameter type.

### Where the subsumption went, and where it did not

**`ValueTy h v τ` now reads *`v`'s exact type is below `τ`*.** `valueTy?` is untouched — it still
computes *the* type of a value — and every inversion still recovers it, because `subTy_atomic` says
`subTy σ τ` **is** `σ = τ` at every arm but `.any` and `.nilable`. That is what made the change
surgical rather than sweeping: `valueTy_ref_plain`, `valueTy_int`, `ValueTy.congr` and the rest all
survive with a `⟨σ, hσ, hs⟩` at the top.

Two statements did *not* survive, and both were quietly too strong:

* **`valueTy_ref_cls`** said *a typed `.ref` has a class type*. False now. Replaced by
  `valueTy_ref_not_ground`, which is the negative form its one prospective consumer
  (`DeclsOk_grow`) actually wanted and which survives the next widening too.
* **`valueTy_tyClass`** said *a receiver hands over its dispatch class*. False at a nilable — as it
  must be, since the receiver may be `nil`. It now takes the two `subTy_atomic` side conditions,
  and **no rule carries them**: `sigOf_atomic` reads them off the *existence of a row*, because
  `tyClassNames` is `[]` at both arms. That is the payoff for having given those arms `[]` rather
  than a name.

**`CtlOk`'s eval clause is the only other place a `subTy` appears**, and it has to be there: `infer`
answers the expression's own type while the continuation was registered at the join. The value
clause needs nothing, because `ValueTy` is already a relation.

### The one structural change: `KontOk`'s tail index is decoupled

Every `KontOk` constructor that pins its *tail's* type gained a `subTy … τw` premise and indexes
the tail at `τw`. That is a `KontOk.sub` constructor **inlined into each rule**, and the inlining is
the whole point: a standalone `sub` constructor leaves the kont unchanged, so `cases hk` in the
delivery case would not reduce and the proof would need well-founded recursion on the derivation.
Eleven constructors, one premise each, and `step_ok` still closes by `cases`.

Two lemmas fell out (`inv_eval_sub`, `inv_push_sub`) and one existing hypothesis widened
(`inv_implicit_send0`'s). The `ifK` delivery case is where all of it is spent, in one line per
branch: `subTy_trans (joinTy_sub hjoin).1 hsw`.

### A second dead table, found the same way as L192's

`Main.lean` had an inline match on *every* `Ty` arm to render the inferred type — a copy of
`Types.tyName`, so every new arm broke `Main.lean` and the two renderings had already drifted in
form if not in output. Replaced by the one function. L192 found `REOPENABLE` twice; this is the
same hazard in the other direction (two readers of one *concept*, no shared definition), and both
were found by a new arm breaking exactly one of the copies.

### Checks

`lake build` and `lake build Metatheory` green; `check-proofs.sh` all theorems axiom-clean at
`propext + Classical.choice + Quot.sound` — including `check_sound`, which is what makes the twelve
new acceptances *safe* rather than merely accepted, and there is a new named example
(`egNilJoin_safe`) that says so. `--check` **51 / 1,174 / 0** with the twelve transitions read
individually (`1 && 2 && 3 && nil`, `if true then 1 end`, `1if true` — all now
`T.nilable(Integer)`); `--assn` smoke 1,227 clean / 0 fail; `fragment-gap.py --self-test` all agree,
with three new rows pinning the join's *boundary* (one-armed `if` accepts, `nil` else-arm accepts,
`Integer`/`Symbol` arms still refuse). The interpreter is untouched, so no difftest tier can move.

---

## L193b — the open front end joins too

Out of fragment **76 → 74**, and the `if` line of the `--assn` histogram drops from **7 to 2**.
`--check` is byte-identical to L193: this commit moves the *open* judgement only.

### `ATy.nilOf`, and the one instantiation that forced `mkNilable`

The open front end joins against a type **variable** — `raise ArgumentError, "…" unless c` records a
row requirement on `self` whose return type is a fresh `α`, and the missing arm is `nil` — so it has
to be able to say *`α` or nil* before it knows what `α` is. Hence one new `ATy` arm.

The subtle part is not the arm, it is that the two joins have to **agree under substitution**, and
naively they do not:

```
joinATy (nom nilT) (var α)  =  nilOf (var α)      -- subst at θα = NilClass → nilable NilClass
joinTy  nilT       NilClass =  NilClass                                     -- ≠
```

One instantiation, and `inferOpen_factors` would have been false. `mkNilable` — `nilable nilT`
normalized to `nilT` — is what closes it, and `joinATy_subst` is the lemma that says so. Worth
recording as the shape of the hazard: *an open judgement and a nominal one can agree at every
example and disagree at one substitution*, and only the factoring theorem finds it.

A nilable **receiver** is refused, with its own label (`nilable-receiver`, one body): no row can
ever be promised on a type whose values may be `nil`, which is `tyClassNames .nilable = []`
arriving in the front end. What that position wants is *narrowing* (`x.nil?`, `if x`), W5 T3.

### `Option.map` instead of a `match`, and why

`inferIf` now ends `(joinTy τt τe).map (fun τj => (τj, Γt, Dt))` rather than matching on `joinTy`.
That is not style: the factoring proof has to rewrite `joinTy`'s *result* under the binder, and a
rewrite inside a `match` **scrutinee** is exactly the shape `rw` refuses ("motive is not type
correct"). One combinator, and `joinATy_subst` goes straight in. The `Option.map` form also removes
the join's own case from `infer.induct`, so `Mono.lean`'s positional numbers went back to L192's.

### Two hours lost to one wrong assumption, worth writing down

The join case would not close, and every attempt to fix it inside `inferOpen_factors`' uniform
`first` block failed. The assumption was that the goal reaching that block was the join equation.
It was not: at the moment `first` runs, the goal is still the whole `FactorsIf`, and it is the
*two-subexpression* alternative — which ends in `simp_all` — that reduces `inferIf` and leaves the
join equation **behind**, as a residual. `first` had already committed.

The diagnosis came from `all_goals (trace_state)` placed **after** the block rather than inside it:
inside, the case never printed, which is the fact that identified it. The fix is one line next to
the `StoreLe` residual that L175 discharged the same way, and the file already said why that shape
exists — *discharged here rather than inside the alternative, so the alternatives stay one shape
each*. The lesson is narrower and more useful than "read the goal": **in a `first`-chain proof, a
goal that never prints inside the chain is a goal the chain created.**

### Checks

`lake build` and `lake build Metatheory` green; `check-proofs.sh` axiom-clean; `--check`
**byte-identical to L193** (51/1,174/0) — the nominal rule's behaviour is unchanged, only its
spelling; `--assn` smoke 1,227 clean / 0 fail; `--self-test` all agree; `fragment-gap.py` **74** out
of fragment with `if` down to 2. Interpreter untouched.

---

## L194 — the read table and the reopen table are not the same table

**Out of fragment 74 → 74.** This rung moves no bodies, and it is committed anyway because it
separates two rules that had been sharing one obligation set, adds the one name that separation
admits at the boot heap (`Float`), and — the actual product — **prices the name that matters**.

### The two clause sets

`class C … end` and a read of `C` are different rules. The reopen must know the object is a class
and not a **module**, that its ancestor chain **starts at itself** (a `def` in the body has to land
where `lookup` finds it), and that nothing before `Object` on its chain owns a constant
(**`NoShadowBefore`** — a constant read *inside* the body has to reach the toplevel table). The read
of `C`'s own name needs none of those: only that the name is in `Object`'s own table, uniquely, at a
legal receiver, and that no other class object owns it.

Until now the read was built on top of the reopen's table, so it inherited three clauses it does not
use. `ClassOk` is now quantified over `readableClasses` with the reopen triple behind
`n ∈ reopenableClasses`. **One block, not two**, and deliberately: two blocks would double every
`ClassOk` transport (`_grow`, `_defineMethod`, `IvarOnly.classOk`), and the transports *are* the cost
of this predicate.

`scripts/reopen_probe.lean` now decides both sets per candidate — the fifth probe extension whose
output changed the design rather than confirming it.

### What `T` costs, which is the point of the commit

The measurement said `T` alone frees **six** method bodies: it is the slice's most-read constant by a
factor of five (259 occurrences, `T.let`/`T.must`/`T.nilable`) and, being a **module**, it can never
be reopenable — so the split above is exactly what would let it in. It passes all four read clauses
at the prelude-booted heap.

**And it cannot go in the table.** `T` is defined by `sorbet-runtime`, so it exists only at the
*prelude-booted* heap, while `check_sound` runs at `Machine.init p` — the bare boot heap, where
`decide (classOkB Boot.initHeap)` is what establishes `Inv`. A table entry naming an absent constant
makes `ClassOk` **false** there, and `check_sound` becomes unprovable. Measured, not guessed: adding
`T` turned that `decide` red immediately, and removing it turned it green.

The rule cannot dodge it either. `infer` is a pure function of the program, so it cannot ask whether
the constant is present; and weakening `ClassOk`'s clause to *present-and-good ∨ absent-everywhere*
does not help, because the absent case makes the read raise `NameError` — a `.jump`, which `CtlOk`
refuses. **Typing `T` requires the prelude, and any rule that types it unconditionally is unsound at
the boot heap.**

So the next rung is structural, and its shape is already visible in the code: **the readable-constant
table belongs in `Decls`**, whose unused `consts` field (added at L179 and never populated) is
exactly the slot. `Inv` already ∃-quantifies the table and carries `DeclsOk D h`, so no invariant
parameterization is needed — `declsOf p` keeps a boot-safe `consts` for `check_sound`, and the
`--assn` route, whose soundness (`inferBodyWith_sound`) is *already* parameterized by `D`, passes a
prelude-aware one. What moves is ~7 clauses from `ClassOk` into `DeclsOk`, plus that predicate's
three transports.

### `Float`, and why it is the only name this commit adds

`Float` owns `NAN` and `INFINITY`, so `NoShadowBefore` fails and it can never be reopened; reading
the *name* `Float` never enters a `Float` frame, so the read does not care. It is boot-safe, so it
goes in. `Comparable` and `Kernel` are free by the same measurement and are **not** added: nothing in
the slice reads them, and a row with no call site is the speculative clause L191 warned about.
`Array`/`Hash`/`Range` are refused — `T::Array` and friends own those names, so sole ownership fails
— and `Regexp` is refused because `classRecv` excludes its id (L106).

### Checks

`lake build` and `lake build Metatheory` green; `check-proofs.sh` axiom-clean, `heapOkB` true at the
prelude-booted heap and `classOkB Boot.initHeap` still `decide`-able; `--check` **byte-identical**
(51/1,174/0); `--assn` smoke 1,227 clean; `--self-test` all agree; difftest at baseline (tier 0
992/0, slice 351/0/1, regressions 35 held / 2 known-open). `fragment-gap.py` grew a `READABLE` set
beside `REOPENABLE`, which is the mirror of the same split.

---

## L195 — the constant table becomes a declaration, and `T` gets in

Out of fragment **74 → 69**, `needed:` 17 → 22, and `--check` **byte-identical**. L194 priced this
and said the slot already existed; this is the commit that uses it.

### The move

`.const n` no longer tests a global list. It reads `D.consts`:

```lean
| .const n => match constTy? D n with | some τ => some (τ, Γ, D) | none => none
```

and `DeclsOk` grew a second half:

```lean
def ConstOk (h : Heap) (n : String) (τ : Ty) : Prop :=
  ∃ v, constOwn h Boot.objectId n = some v ∧ ValueTy h v τ ∧
    (∀ j, (h.classPayload? j).isSome → j ≠ Boot.objectId → constOwn h j n = none)
```

**Three conjuncts where `ClassOk`'s block carried seven**, and the reason is that `ValueTy h v
(.clsOf n)` *already* says "a class-object receiver named `n`" — `classPayload?`, `className`,
`k ≠ regexpId`, `k ≠ mathId` are all inside it. The `.const` case of `step_ok` went from twenty lines
rebuilding that value judgement to **one line consuming it**. That is the signal the clause is stated
at the right level: L193's subsumptive `ValueTy` is what made it possible, two commits earlier and
for a different reason.

The third conjunct is L189's, unchanged and still load-bearing: sole ownership is what makes any
`cref` hit `Object`'s, whatever the `cref` is, so the rule still needs no frame clause beyond
`Object ∈ cref`.

### Why this admits `T` and a global list could not

`Inv` **already ∃-quantifies the table** and ties it to the heap with `DeclsOk`. So the boot-safe
table and the prelude-aware one are two *tables*, each sound at the heap it describes — where a
global list has to be true everywhere, including at `Machine.init p`, where `T` does not exist.

* `declsOf p = baseDecls`, whose `consts` is `readableClasses` mapped to class-object types.
  `check_sound`, `check_sound_withPrelude`, `check_sound_withPrelude'` and `--check` are **all
  unchanged**; `tableOk_declsOk` gained one hypothesis (`ClassOk h`, already a conjunct of `HeapOk`,
  so no caller had to find it) and reads the constant half out of it.
* `preludeDecls` adds `("T", .clsOf "T")`, and `--assn` reports against it — because the heap
  `--assn` describes *is* the prelude-booted one, the same heap the difftest SUT runs and `heapOkB`
  certifies.

**And the extra row is decided, not asserted.** `constsOkB` (in `Proof/` rather than `HeapCert.lean`,
because it has to call `valueTy?`) plus `constsOkB_sound`/`constsOk_of_constsOkB`;
`scripts/consts_probe.lean` runs it at the booted heap and `check-proofs.sh` fails on it. Measured:
`T` present, typed `.clsOf "T"`, solely owned — and `constsOkB` `true` for both tables.

### Three things the move forced, each worth knowing

1. **`SubDecls` now requires `consts` *equality*.** The `.const` rule reads a type *out of* the
   table, so an `F'` answering a different type at the same name would make `infer_mono` **false**,
   not merely unprovable. Nothing grows `consts` today (there is no `casgn` rule), so equality costs
   nothing — and `casgn` will have to say what adding a constant *means*, which is a real question
   about shadowing rather than a formality.
2. **`declAssn`'s denotation is `MethodRowsOk`, not `DeclsOk`.** `declAtoms` reads `D.rows`, so the
   assertion language has atoms for the method half only. `InvA` carries the constant half beside the
   certificate rather than inside it, and `invA_iff_inv` still holds. Giving constants an atom — so a
   *printed* assertion could carry one — is the assertion language's own next rung.
3. **`baseDecls` carries `consts` directly, not `{ baseDecls with consts := … }`.** Because `infer`
   reads `D.consts`, `EntryOk baseDecls` and `EntryOk` at an updated table are different
   propositions, and every `baseDecls` lemma would have had to be restated. Folding the field in
   (which meant moving `reopenableClasses`/`readableClasses` above it) made that churn vanish. Worth
   recording as a rule: **when a definition starts reading a field, structure updates of it stop
   being invisible.**

### Checks

`lake build` and `lake build Metatheory` green; `check-proofs.sh` axiom-clean and `consts_probe` now
decides both constant tables at the booted heap; `--check` **byte-identical** (51/1,174/0); `--assn`
smoke 1,227 clean; `--self-test` all agree; `fragment-gap.py` **69** out of fragment, `const` 22 → 17,
`{const}` singletons 8 → 5. Interpreter untouched.

---

## L196 — instance variables become a declared table, and `nilable` pays a second time

Out of fragment **69 → 65**, `needed:` 22 → 26, `--check` **byte-identical**. The whole `ivar` line
of the `--assn` histogram is gone: four bodies moved from *no rule* to *no declaration*.

### Both halves of the read are forced by the machine

```lean
| .var .ivar x =>
  match ctx.selfCls with
  | some c => match ivarTy? D c x with
              | some σ => some (mkNilable σ, Γ, D)
              | none => none
  | none => none
```

`selfCls`, because `evalExpr` reads the *frame's* `self` (`Interp.lean:139`) and the invariant knows
that object only by its class — which is why `IvarOk` is quantified over **every instance** of the
class rather than over a receiver. And **`mkNilable`**, because an unset ivar reads as `nil`:
`evalExpr` ends `.getD .nil`, so the type has to admit it. Answering `σ` would be unsound; answering
it *soundly* needs definite-assignment tracking through `initialize`, which is Wall 2's rung.

That is L193's `nilable` paying for itself a second time, in a rule that has nothing to do with `if`.
Worth recording as the shape of a good type-language rung: **it gets used by rules that did not ask
for it.**

### The write stopped being free, and that is the rung's real content

L191 admitted `@x = e` with no check on the value, and it *could*, because nothing in the invariant
claimed anything about instance variables. A row is exactly such a claim, so the write now checks
`subTy τ σ` when the ivar is declared — and an undeclared one is still free, because there is no row
to break.

`KontOk.asgnIvar` carries the conformance to the delivery, which is where `DeclsOk`'s third half has
to be re-established. **That half is the one `IvarOnly` cannot carry** — L191's transport says an
ivar write is invisible, and this clause is *about* ivars — so `IvarOnly.declsOk` was split into
`rowsAndConsts`, and the `@x = e` case proves the third half itself. Three sub-cases, and they are
exactly the three ways `bindIvar` can miss a row:

* **another object** — `bindIvar_get_ne`;
* **the same object, another name** — the head is `x` and the tail is the old list with `x` filtered
  out, so `find?_filter_ne` (written at F1a for the *method* table, reused here) reads the old value;
* **the written slot** — the classes agree because both name `sc`, so the row's type *is* the one the
  rule checked against.

### One clause fell out of `PlainGrow`

`IvarOk` quantifies over every object of a class, so an **allocation** could break a row by producing
an instance with a badly-typed `@x` — and nothing in `PlainGrow` bounded the fresh slots.
`freshIvars` is the new clause: every allocation the fragment performs is a *literal*, and a literal
has no ivars, so it is `rfl` at both call sites. It is a clause rather than a free consequence because
`Class.new` (Wall 2) is where it stops being one.

### Where the honesty is

* The **open** front end refuses a write to a *declared* ivar (`iasgn-declared`), because the nominal
  check is `subTy τ σ` and `τ` may be a type *variable* there. Nothing is lost today (no shipped
  table has an ivar row) and the fix is the constraint machinery the row mechanism already has.
* `baseDecls.ivars` is **empty**, so no shipped table takes the read rule's accepting branch. The rule
  is not unreachable-with-a-proof-attached — `step_ok` is quantified over every table — but the report
  side is pinned at a table that *has* a row (`bodyVerdictWith { baseDecls with ivars := … }` answers
  `T.nilable(Integer)`), because that is the branch a reader would not otherwise see. A shipped row
  would need what `T`'s needed: a certificate deciding `IvarOk` at the heap, in `constsOkB`'s shape.
* `SubDecls` now requires `ivars` equality too, for `consts`' reason: the read takes its answer *out
  of* the table.

### Checks

`lake build` and `lake build Metatheory` green; `check-proofs.sh` axiom-clean; `--check`
**byte-identical** (51/1,174/0) — with an empty ivar table both new arms refuse, so the checker
cannot move; `--assn` smoke 1,227 clean; `--self-test` all agree; `fragment-gap.py` **65** out of
fragment, and `_body_blockers` no longer counts `ivar-read`. One example had to be rewritten: a
`def`-default witness that relied on an ivar read being out of the fragment now uses a global read,
which is the kind of churn a widening should cause.

---

## L197 — a constant the table does not carry is a missing *declaration*

Out of fragment **65 → 48**, `needed:` 26 → 43, `--check` **byte-identical**. One arm of
`inferOpen`, and it is the third application of the same correction:

```lean
| .const n => match constTy? D n with
              | some τ => .ok (.nom τ) Γ s
              | none => .missing (.nom (.clsOf "Object")) ("::" ++ n) []
```

`infer` **has** a `.const` rule — L189 wrote it and L195 keyed it on `D.consts` — so a name the
table does not carry is refused by the **table**, not by the rule set. That is the category the
census counts separately, and reporting it as *out of fragment* was simply wrong once L195 moved the
table into `Decls`. The `::` prefix is `@`'s from L196: the atom vocabulary is method rows, so a
marker is what says which kind of declaration is wanted, and the receiver is `T.class_of(Object)`
because that is literally what `ConstOk` obliges (`constOwn h Boot.objectId n`).

### What it does not claim, stated because one name in the slice makes the difference visible

`Regexp` can **never** be declared: `ConstOk` wants `ValueTy h v (.clsOf "Regexp")` and `classRecv`
excludes `Boot.regexpId` (L106). So this reports a requirement that no heap satisfies.

That is not a new kind of dishonesty, and the reason is worth writing down rather than glossing:
**the `needed:` category has never claimed satisfiability.** `slice-verdict.md` §1 says an `accept`
reads *types under this precondition*, never *is safe*, and no solver supplies a `θ`; the same
reading applies to a requirement. `vulns/semver.rb`'s long-standing `α0 ~ parse : (α2) → _` has
exactly the same character — a row nothing supplies, which may or may not be satisfiable by any
builtin. Treating the constant case as special would be *less* honest than treating it like every
other missing declaration.

### What this leaves, and it is now clean

The remaining 48 are all genuinely **rule**-shaped, and the census reads as a to-do list rather than
a mixture:

```
21  return    10  send-with-block    4  super    3  cpath
 3  splat      2  if                 2  begin    1  gvar
 1  zsuper     1  nilable-receiver
```

And the `--sets` singleton list changed shape with it: **`{return}` is now 14 bodies** (it was 4),
because `const` is no longer co-blocking them. `return` is the next rung by a factor of three, and
the number to beat is 21.

`gvar` is the one remaining line that *could* be a declaration rather than a rule — `Decls.globals`,
the fourth table — but globals live in `m.globals` rather than the heap, so the clause cannot ride
`DeclsOk`'s transports and would need a new `Inv` conjunct. One body; not worth it yet, and recorded
so the next reader does not re-derive it.

### Checks

`lake build` and `lake build Metatheory` green; `check-proofs.sh` axiom-clean; `--check`
**byte-identical** (51/1,174/0) — only the open front end moved; `--assn` smoke 1,227 clean;
`--self-test` all agree; `fragment-gap.py` **48**, and `_body_blockers` no longer counts `const`.

---

## L198 — the frame-side bill for `return`, paid, with the rule still to write

Out of fragment **48 → 48**, `--check` byte-identical. This is F1b.2's shape again (L143–L149: *the
producer's bill, paid, with the rule still to write*), and it is committed for the same reason: the
four facts below are what a `return` rule consumes, each is now carried and preserved, and the one
thing still missing is **named precisely** rather than discovered later.

### What landed

1. **`FrameCtx.ret : Option Ty`** — the enclosing method's *declared* return type, which is what
   makes a `return e` rule local: it checks `e` against the declaration rather than against whatever
   the rest of the body will answer.
2. **`KontOk.frameK` carries the agreement** `∀ σ, cΓ.1.ret = some σ → subTy σ τ`: the callee's
   declared return sits below the type the caller's continuation expects. `subTy` and not equality,
   because L193's `CtlOk` already lets the continuation be wider.
3. **`KontOk.nil` carries `ret = none`** for the head context — *an empty continuation means no
   enclosing method*, so there is nowhere for a return to land. One `simp` at both `initiation`s.
4. **`StackCtx` gained `kind = .method ∨ c.ret = none`** — the whole frame-side cost.
   `returnTarget` (`Interp/Support.lean:349`) answers the stack head for every frame kind *except*
   `.block`, where it walks to the closure's home, so the rule needs to know the current activation
   is not a block — and `ret.isSome` is exactly when it needs to.

Together, (2) and (3) are what let `RetOk` be **derived from a `KontOk` derivation** rather than
carried as a separate `Inv` conjunct re-established at forty push sites. That was the design's whole
economy and it is now checked.

### The circularity that shaped `UserConforms`, and how it was broken

`return e` checks against `ctx.ret`, so a body containing one must be checked at a context that
already names the return type. But **the `def` rule computes the return type from the body** — it
cannot name it before checking. Fixing `UserConforms` at `some d.ret` would make `def` unable to
discharge its own row; fixing it at `none` would make (2) vacuous and `RetOk` underivable.

So `UserConforms` **carries** the context's `ret` existentially, with the agreement `∀ σ, r = some σ →
σ = d.ret`. `def` supplies `r = none`, which is precisely *this body contains no `return`*; a declared
signature (`PLAN.md` W8's `sig`) supplies `some d.ret`, and that is the rung at which a `return`
inside a *running* method becomes reachable. The rule and its consecution case are proved either way,
which is what keeps this honest rather than speculative.

### What is still missing, named exactly

**The kont/stack correspondence.** `doReturn` targets `returnTarget m`, and `unwind`'s `frameK fid`
case compares `target == fid` — so the consecution needs *the first `frameK` in the kont stack is
labelled with the frame stack's head*. It is true (every frame push pushes a `frameK` with the same
`fid`, and pops remove both) and it is **not currently stated anywhere**: `FramesOk`/`StackCtx` relate
`m.stack` to the environment stack, and `KontOk` never mentions `m.stack`.

Stating it is a new machine-shaped conjunct — `frameKLabels m.kont = m.stack` — independent of types
and cheap per step, but re-established at every push and pop, so about twenty sites. That is the next
commit's first task, and everything after it is mechanical: `RetTransparent`/`RetOk`, `CtlOk`'s
`.jump (.retJ v target)` arm, `KontOk.retValK`, `infer`'s `.ret` arm, and `unwind`'s consecution —
which is **thirteen short cases**, because `unwind`'s catch-all
(`Interp/Kont.lean:457`) propagates a `.retJ` through every kont the fragment admits except `frameK`,
and the two loop markers propagate it explicitly.

Recording the measurement that makes the last part cheap: the fragment stacks nine kont shapes plus
`frameK`, and **all nine fall through to that catch-all**. The expensive-looking half of the `return`
rung is the cheap half.

### Checks

`lake build` and `lake build Metatheory` green; `check-proofs.sh` axiom-clean; `--check`
**byte-identical** (51/1,174/0) — no rule changed, only what the invariant carries; `fragment-gap.py`
**48**, unchanged, which is the honest reading of a scaffolding commit.

---

## L199 — the kont/stack correspondence, which is the thing L198 named as missing

Out of fragment **48 → 48**, `--check` byte-identical. L198 ended by naming exactly one missing
fact; this commit adds it, and then finds the *next* one — which is the honest sequence for a rung
this size.

### The clause

```lean
def frameKLabels : List Kont → List FrameId
  | [] => [] | .frameK fid :: k => fid :: frameKLabels k | _ :: k => frameKLabels k

-- new conjunct of `Inv`, beside `BottomObj`
frameKLabels m.kont = m.stack.dropLast
```

One frame push writes both a stack entry and a `frameK`, and one pop removes both, so the two lists
move together. `dropLast` because the **bottom activation has no `frameK`** — `Machine.init` pushes
it and the continuation starts empty — and that asymmetry is where `dropLast_cons_ne` gets spent.

It sits **outside** `Inv`'s existential, beside `BottomObj`, for `BottomObj`'s reason: it mentions no
`Decls` and no `Ty`. That also made it cheap: the five `inv_*` helpers take it as a hypothesis and
the ~35 call sites pass either `hks` (the continuation is unchanged) or
`(by simpa [frameKLabels] using hks)` (a transparent kont was pushed or popped) — one line each.

**And reading it backwards is the payoff**: at the `frameK` delivery case it says `fid` *is* the
stack's head, which is precisely what `doReturn`'s target has to be matched against. That derivation
is now in the file (`hst2`/`hlab` in the `frameK` case).

### Also landed, stated and unconsumed

`RetTransparent`, `firstFrameK`, `RetOk`. `RetTransparent` is a **read-off of `unwind`**, not a
judgement: `unwind`'s catch-all (`Interp/Kont.lean:457`) propagates a jump unchanged, and its two
loop markers propagate a `.retJ` explicitly, so all nine kont shapes the fragment stacks are
transparent to a return and `frameK` is the one that is not. Measured, and it is what makes the
consecution's expensive-looking half cheap.

The `KontOk.retOk` induction — deriving `RetOk` from a `KontOk` derivation, which is what L198's two
new `KontOk` premises exist for — **goes through**: recursion on the kont list, one line per
constructor, `nil` discharged by `KontOk.nil`'s `ret = none`.

### What is still missing, named exactly (again)

**A `DeclsOk` at the table the deep `KontOk` carries.** `KontOk`'s constructors *thread* the table —
`seqCons`'s premise sits at `inferSeq`'s **output** table, not its input — so walking down a chain of
transparent konts to the `frameK` arrives at a table that is not the one `Inv` currently carries.
After the unwinding pops to that frame, `Inv` needs `DeclsOk` at *that* table, and `DeclsOk` is
neither monotone nor antitone in the table (`UserConforms` reads it through `infer`) — so it cannot
be recovered, only carried.

Two ways out, and the choice is a real one:

* **Carry it**: add `DeclsOk D h` to the `KontOk` constructors that change the table. Local, but it
  puts a heap predicate inside a judgement that has so far been heap-light, and every construction
  site pays.
* **Prove the chain is table-constant**: `UserConforms` already requires `defFree md.body`, and the
  class-body rule already carries stability conditions, so along every chain the fragment can build
  the table *is* constant. That is the smaller change and the better one, and it wants a lemma of the
  shape *`infer` on a `defFree` expression leaves the table alone* — which is `infer_mono`'s sibling
  and probably its proof.

`RetOk` is left in the file rather than deleted: the shape is right, the remaining obligation is one
clause, and deleting it would lose the measurement that `RetTransparent` records.

### Checks

`lake build` and `lake build Metatheory` green; `check-proofs.sh` axiom-clean; `--check`
**byte-identical** (51/1,174/0); `fragment-gap.py` **48**, unchanged — a scaffolding commit, said
plainly.

---

## L200 — `return`, and `CtlOk`'s `.jump` becomes inhabited

Out of fragment **48 → 48** (the *open* front end is the second half, next commit), `--check`
byte-identical. But the metatheory is complete: **`invariant_sound` now covers a `.retJ` in
flight** — the first jump the machine can produce inside the fragment — and it is axiom-clean.

### The one guard that made it possible

```lean
-- infer's `def'` arm, on the row-adding branch
… ∧ ctx.ret.isNone
```

L199 ended blocked on this: after the unwinding pops to the frame, `Inv` needs a `DeclsOk` at the
table the **deep** `KontOk` carries, and `KontOk`'s constructors *thread* the table
(`seqCons`'s premise sits at `inferSeq`'s **output**). `DeclsOk` is neither monotone nor antitone in
the table, so it can only be carried — or the chain has to be **table-constant**.

At `top = false` the only arm that grows the table is `def`'s row (`class'` needs `top = true`). So
refusing that row when the enclosing method declares a return type makes the table constant along
every chain inside such a body, and `infer_table_ret` (plus the three list-induction siblings) proves
it. The guard is **free** — no shipped table declares a return type (L198: `def` supplies `r = none`,
`some d.ret` waits for W8's `sig`) — and it refuses the *row*, not the program.

Recorded because it is the second time the shape has appeared: **a fact a proof needs from a
judgement is often cheaper as a guard on the rule than as a clause on the judgement.** L191 said the
same thing about `plainRecv`'s `!frozen`.

### What the rung is made of

* **`FrameCtx.ret`** (L198), the *declared* return type, which is what makes `return e` local.
* **`KontOk.frameK`'s agreement** (L198): `∀ σ, cΓ.1.ret = some σ → subTy σ τ`.
* **`KontOk.nil`'s `ret = none`** (L198): an empty continuation means no enclosing method.
* **`StackCtx`'s clause**: `(kind = .method ∧ cs ≠ []) ∨ c.ret = none` — the whole frame-side cost.
  `returnTarget` answers the stack head for every kind *except* `.block`, and `cs ≠ []` is what makes
  `infer_table_ret` applicable (its `top` is `Γs.isEmpty`).
* **`frameKLabels m.kont = m.stack.dropLast`** (L199) — one push writes both a stack entry and a
  `frameK`. Read backwards it says the `frameK`'s label *is* the stack's head, which is what
  `doReturn`'s target must be matched against.
* **`RetOk`**, indexed by the **callers'** environment stack rather than this activation's — the head
  is the frame the jump is about to leave and nothing about it survives the pop, which is what lets
  `skip` keep the index fixed while `KontOk`'s own head changes at every transparent constructor.
* **`KontOk.retOk`**, deriving `RetOk` from a `KontOk` derivation, so no `Inv` conjunct had to be
  added and re-established at forty push sites. That was the design's whole economy.
* **`KontOk.retValK`**, carrying a `KontOk` and *not* a `RetOk` — `RetOk` is defined over `KontOk`
  derivations, so the other choice makes the two mutually inductive.

### The rule, and why its answer type is free

```lean
| .ret e => match ctx.ret with
  | some σ => match e with
    | some e' => match infer D Γ e' top ctx with
                 | some (τ, Γ₁, D₁) => if subTy τ σ then some (.nilT, Γ₁, D₁) else none
                 | none => none
    | none => if subTy .nilT σ then some (.nilT, Γ, D) else none
  | none => none
```

The value never reaches this continuation — the machine jumps — so **any** answer is sound;
`KontOk.retValK`'s conclusion index is the *returned* type, not this one. `.nilT` is the honest
reading and it composes: `return X if c` joins with the missing `else`'s `nil` to `nilT` rather than
to a nilable.

### The consecution, and the measurement that made it cheap

Three cases. The `.ret` **eval** case is two machines — with an expression the step pushes
`jumpValK .retK`; bare, `evalExpr` calls `doReturn` outright and the *jump* is the new control. The
`jumpValK .retK` **delivery** creates the jump. And the `.jump` branch is the unwinding, which is
**two cases** rather than thirteen: `RetTransparent` is a read-off of `unwind` — its catch-all passes
a jump on unchanged and its two loop markers pass a `.retJ` on explicitly — so all nine kont shapes
the fragment stacks are one lemma (`unwind_ret_transparent`, nine `simp`s) and `frameK` is the only
real case. The expensive-looking half of this rung was the cheap half, as L199 predicted.

### What is left, and it is the *only* thing left

The **open front end**. `inferOpen` has no `.ret` arm, so the 21 bodies are still out of fragment.
The design is settled and it is the accumulator: `OState` gains `rets : List ATy`, `inferOpen`'s
`.ret` records the returned type and answers `.nom .nilT`, `inferBody` requires every recorded type
to equal the body's answer, and `Factors` gains a `retF : Ty` parameter with the premise
`∀ a ∈ s'.rets, a.subst θ = retF` — the same shape as the `StoreLe s'.st stF` premise it already
carries. `inferBodyWith_sound` instantiates `retF := τ.subst θ`.

### Checks

`lake build` and `lake build Metatheory` green; `check-proofs.sh` axiom-clean, **0 `sorryAx`**;
`--check` **byte-identical** (51/1,174/0) — the rule can only fire at `ctx.ret.isSome`, which no
`check` entry point produces; `--assn` smoke 1,227 clean; `--self-test` all agree.

## L201 — the open front end for `return`, and the premise that is a second `StoreLe`

Out of fragment **48 → 41**, `--check` byte-identical (51/1,174/0). `return` disappears from the
third ratchet's census; the `needed:` column goes 43 → 50, which is the whole story of the rung —
seven bodies stopped being refused for *no rule* and started being refused for *no declaration*.

The design is the one L200 wrote down, unchanged, and it landed in the shape it predicted.

### The accumulator

```lean
structure OState where … rets : List ATy := []

| .ret e => match e with
  | some e' => match inferOpen D Γ e' ctx s with
    | .ok τ Γ₁ s₁ => .ok (.nom .nilT) Γ₁ { s₁ with rets := τ :: s₁.rets }
    | r => r
  | none => .ok (.nom .nilT) Γ { s with rets := .nom .nilT :: s.rets }
```

and the check, at both body entry points:

```lean
| .ok τ Γ' s => if s.rets.all (· == τ) then .ok τ Γ' s else .outOfFragment "return-join"
```

**The check can only live here.** The pass meets a `return` before it knows the tail's type, and a
disagreement is `outOfFragment` rather than `missing`: no *declaration* would fix it — the two types
simply differ, and joining them needs a union this fragment does not have. That is the honest
verdict, and it is why the third ratchet's census is trustworthy at this rung: `return-join` would
show up as its own atom if any slice body had two disagreeing returns. None does.

### The bug the metatheory caught, before the proof was finished

Writing `inferOpen_rets` — `rets` only grows — printed a goal that could not close at the
`requireRow` arms. Five of them rebuilt the state as

```lean
{ st := st', fresh := s.fresh + 1 }        -- rets silently reset to the default []
```

instead of `{ s with … }`. Every `return` inside a method call's receiver or argument list was being
*dropped*, so a body like `def f; g(return 1); end` would have typed with an unchecked return. The
executable half was already green and the metric had already moved; the lemma is what found it. This
is the second time in this file a monotonicity lemma has paid for itself before its theorem did
(L175's `StoreLe`), and the reason is the same: **the lemma states the invariant the state's users
assume and the state's producers were never asked to keep.**

### `Factors` gains a second premise, and that is the entire proof

```lean
| .ok τ Γ' s' => StoreLe s'.st stF → (∀ a ∈ s'.rets, a.subst θ = retF) →
    infer D (substEnv θ Γ) e false
        { cls := ctx.cls, selfCls := some ctx.cls, ret := some retF } = …
```

Read the second premise beside the first: they are the same *kind* of hypothesis — a bound on the
arm's output that the arm's subexpressions inherit because the thing bounded only grows. So the
factoring theorem's uniform block needed exactly what L175's needed: four `rets_sub*` transports
(`rets_sub`, `rets_subIf`, `rets_subSeq`, `rets_subArgs`) built on four monotonicity lemmas
(`inferOpen_rets` and its three traversal siblings), and one extra argument at each IH site.

Two mechanical notes, both worth keeping because they will recur at the next premise:

* **`simp_all` sometimes discharges the new premise itself** and sometimes does not, so the IH is
  applied with two arguments in some cases and one in others. Every site is now
  `first | rw [ih X Y] | rw [ih X]`. Guessing which shape a case has is not worth a case number;
  offering both is free.
* **The nominal context in the conclusion is now `ret := some retF`**, so the three worked examples
  (`egRow_nominal`, `egParam_nominal`) and `inferBody_sound`'s statement carry it. With no `return`
  in the body nominal `infer` never reads `ctx.ret`, so this weakens nothing that held before.

### What `UserConforms` gets, and why the clause finally has both halves

L198 discharged the invariant's user-method clause with `r = none` — a row whose body contains no
`return`. It now discharges it with `r = some d.ret`:

```lean
⟨hp, hdf, ⟨substEnv θ Γ', some d.ret,
  by rw [← hret]; exact inferBody_sound hb hsat hself,
  fun _ h => by simpa using h.symm⟩⟩
```

and the clause's side condition (`∀ σ, r = some σ → σ = d.ret`) is `hret` itself — the hypothesis
that the body's inferred type *is* the declared return. So the open front end now discharges the
clause for bodies that return, which was the one thing L200 left owing.

### Checks

`lake build`, `lake build Metatheory` green; `check-proofs.sh` axiom-clean, **0 `sorryAx`**;
`--check` byte-identical (51/1,174/0); `--assn` smoke 1,227 clean; `--self-test` all agree;
slice-driver 72 lines IDENTICAL; third ratchet **41**.

## L202 — the float literal, and a singleton that was not a move

Out of fragment **41 → 41**. `--check` **51 → 52**, one transition (`test_literal_026`,
`unknown → accept`, type `Float`). Read those two numbers together, because the second is the
rung's whole delivery and the first is the finding.

### What the rung is

`Ty.float`, the fifth ground arm, and it is `.int`'s twin in every clause that mentions it:

| site | `.int` | `.float` |
|---|---|---|
| `valueTy?` | `some .int` | `some .float` — a float is an *immediate*, so no heap is read |
| `TyClass` | `k = Boot.integerId` | `k = Boot.floatId` |
| `tyClassNames` | `["Integer"]` | `["Float"]` |
| `groundClassNames` | `"Integer"` | `"Float"` — so `.cls "Float"` reads no row, by the disjointness argument `tyClassNames` states |
| `infer` | `some (.int, Γ, D)` | `some (.float, Γ, D)` |
| `declTys`/`declAtoms` | listed | listed |

Nine proof sites, every one of them a copy: `valueTy_tyClass`'s new case is `rfl` (both sides are
`Boot.floatId`), `valueTy_shapes` gains a disjunct and its two consumers one `inr` each,
`declFor_declaresName` one `key "Float" []`, `addRow`'s ground-name refutation and
`baseDecls`' `EntryOk` obligation one `simp` each, and `step_ok`'s `eval.flt` case is
`inv_value … (ValueTy.exact rfl)` — the same line as `eval.int`. **No new transport lemma**,
because the arm reads no heap.

One placement note worth keeping: the `infer` and `inferOpen` arms are written **immediately before
the catch-all**, not beside `.int`. The catch-all is one `induct` case, so inserting there shifts
exactly the cases after it — the catch-all itself and the three list motives — and the renumbering
was seven `caseNN`s in `Mono.lean` rather than fifty.

### The finding, and it is a correction to L201's own recommendation

L201's `--sets` reading said *`{flt}` is 3 bodies for a literal arm — the only cheap thing left*.
It was **0 bodies**, and the reason is visible in the two ratchets side by side:

> **`flt` never appeared in the third ratchet's census.** The census reports each body's *first*
> refusal, and for all three of those bodies the first refusal was a **needed declaration** — they
> were already counted in the 50, not in the 41. The mirror `--sets` walks knows only which
> *constructs* `inferOpen` lacks a rule for; it does not model the row and declaration lookups, so
> its blocker sets are coarser than the checker's verdicts.

State the rule that follows, because it is the fourth variant of the same lesson (L168, L189, L201):

> **Cross-read the singleton against the census.** A `--sets` singleton whose construct does *not*
> appear in the `--assn` census is a body already blocked on a declaration — the rung is a real
> widening, but the metric will not move. `{cpath}` 9, `{zsuper}` 9 and `{super}` 4 all *do* appear
> in the census (9 / 2 / 4), which is what makes Wall 2's 22 a prediction rather than a hope.

The rung was still worth committing on its own terms — a float literal is in the fragment now, the
`--check` ratchet moved for the first time since L174, and `Ty` no longer has a hole where the
slice's arithmetic lives. But it is booked at **0** against the goal.

### Checks

`lake build`, `lake build Metatheory` green; `check-proofs.sh` axiom-clean, **0 `sorryAx`**;
`--check` 51 → **52**, read by transition (one `unknown → accept`, no reverse); `--assn` smoke
1,227 clean; `--self-test` all agree (one new row, `1.5`); slice-driver 72 lines IDENTICAL; tier-0
992 agree / 0 disagree; tier-slice 351 agree / 0 disagree / 1 gated; third ratchet **41**,
unchanged.

## L203 — `::n`, and the cheapest five bodies on the board

Out of fragment **41 → 36**, `--check` byte-identical (52/1,173/0). Five bodies for **one table
read**, and the reason it was that cheap is worth stating precisely, because it is the same reason
L195–L197 were cheap and the census had been pointing at it for two sessions.

### The measurement that chose the shape

`cpath` was 9 of the 41 and the largest *priced* atom. `HANDOFF.md` had it filed under Wall 2 — "all
of them regex literals, which need `Class#new`". That was wrong, and one histogram says so: the
slice's 99 `cpath` nodes are

```
86  root ::Regexp        36  scoped T::Boolean     26  scoped T::Array    23  scoped T::Hash
 3  root ::Range          3  scoped T::Helpers     16  scoped <Tok>::PATTERN (8 × 2)
 1  scoped Float::NAN     1  scoped Version::Parser …
```

**86 of 99 are `['cpath', None, 'Regexp']`** — an *absolute* path with no base expression, which is
what a regex literal desugars to (`/re/` → `::Regexp.new("re", 0)`). An absolute path is not a
namespace walk at all:

```lean
-- evalExpr, the `.cpath none` arm
match constLookup m.heap name with | some v => .next (withCtl m (.value v)) | none => …
```

and `constLookup h n` **is** `constOwn h Boot.objectId n` — the same two-line lookup, spelled twice
in `Heap.lean` (576 and 599). So the rule is

```lean
| .cpath none n => match constTy? D n with | some τ => some (τ, Γ, D) | none => none
```

*the same arm as `.const n`*, reading *the same table*, with the cref walk deleted.

### What it does *not* need, which is the whole content

* **No new table.** `Decls.consts` is keyed on the name, and a name is what an absolute path is.
* **No new `DeclsOk` clause.** `ConstOk`'s first two conjuncts are exactly what this arm consumes.
* **`ConstOk`'s third conjunct is unused here.** Sole ownership (L189) exists to make a *relative*
  read land on `Object` whatever the cref is; an absolute read starts at `Object`. So the
  preservation case is `.const`'s with `constRead_sole` and the `StackCtx` cref clause both deleted —
  it is four lines and a `constLookup = constOwn` bridge.
* **No `KontOk` arm.** `scope = none` means no subexpression, so nothing is pushed.

### The scoped half, priced but not built

`A::B` pushes `.cpathK name` on the base's evaluation and then reads `constOwn` at the *container*.
It needs a second table keyed on the **pair** — `Decls.ivars`' shape, L196's rung verbatim — a
`ScopedConstOk` clause beside `ConstOk`, and one `KontOk` arm with its two consecution cases. It is
4 of the remaining 36 (`Float::NAN`, `Version::Parser`, two more) and the `T::` family, which is
where the `sig`s live. Next session's candidate, and a real one: the census now reads
`cpath 4` rather than `cpath 9`.

### Renumbering, and the recipe that survives it

Two arms went in this session (L202's `.flt`, L203's `.cpath none`) and each shifted `infer.induct`'s
tail: `.flt` by **1** (one case) and `.cpath` by **2** (the arm's internal `match` is two cases). The
seven explicit `caseNN`s in `Mono.lean` are the motive2/3/4 cases, all after the catch-all, so both
shifts hit all seven. `#check @RubyCore.Types.infer.induct` is **not** usable for this any more — the
pretty-printer truncates the telescope with `⋯` at this size — so the working recipe is now: *put a
new arm immediately before the catch-all, count the cases its own `match` creates, shift every
explicit case number at or above the catch-all's by that, rebuild, and read the arity mismatches.*

The `.cpath` hit case is discharged by a **new alternative** in the uniform block rather than by an
explicit case number, which is the durable form: it is `case39`'s three tactics with the name left to
unification, so the next constant-shaped rule costs nothing here.

### Checks

`lake build`, `lake build Metatheory` green; `check-proofs.sh` axiom-clean, **0 `sorryAx`**;
`--check` byte-identical (52/1,173/0) — no bootstraptest program reads an absolute path;
`--assn` smoke 1,227 clean; `--self-test` all agree (three new rows: `::String` accepts, `::Regexp`
is a missing *declaration*, `Float::NAN` is still out); slice-driver 72 lines IDENTICAL; third
ratchet **36**.

## L204 — the join absorbs a nilable, and the `return` check becomes subtyping

Out of fragment **36 → 35**, `--check` **52 → 56** (four transitions, all
`unknown → accept`, all typed `T.nilable(Integer)`, none the other way). **`vulns/cvss.rb` is the
second slice file with no out-of-fragment body.**

One rung, two halves, and they are the same defect seen from two sides: *the fragment's joins were
stricter than the judgement they factor into*.

### Half one — `joinTy`'s fourth case, which was already in the type language

```lean
-- before: three cases and then `none`
else if τ == .nilT then some (.nilable σ) else none
-- after
else if σ == .nilable τ then some σ
else if τ == .nilable σ then some τ
else none
```

The measurement that asked for it is one slice method:

```ruby
def self.severity(vector)
  score = base_score(vector)
  return if score.nil?
  if score >= 9.0 then :critical
  elsif score >= 7.0 then :high
  … end                      # no final `else`
end
```

The inner `elsif` chain answers `Symbol` on one arm and `nil` on the missing one, so it joins to
`T.nilable(Symbol)`; the *next* level up then has to join `T.nilable(Symbol)` with `nil`'s
`Symbol` sibling, and the three old cases refused it. **The least upper bound was already
expressible** — `nilable τ` — and `subTy` already admits both sides of it (`subTy_refl` for the
nilable, `subTy`'s third disjunct for the other). So this is not a widening of the type language,
it is the fourth case of a function that had three.

Written as two `if`s rather than a `match σ, τ` on purpose, and the reason is a bug the first
draft had: `match .nilable A, .nilable (.nilable A)` takes the *first* arm and answers `none`,
while the order-independent form answers the second. Two little structural lemmas
(`ne_nilable_self`, `ne_nilable_self2`) discharge the branches that have to be refuted, and
`joinTy_absorb`/`joinTy_absorb'` package the equation `joinATy_subst`'s two new cases need at a
type the tactic cannot name.

### Half two — `subATy`, and the check the nominal rule never asked for

L201 checked *every collected `return` type equals the body's answer*. The nominal rule asks for
`subTy τ σ`. So the open side was strictly stricter than what it factors into, and `severity` —
which returns `nil` from a guard clause and `T.nilable(Symbol)` from its tail — was refused for a
`return-join` that is not a disagreement at all.

```lean
def subATy (a b : ATy) : Bool :=
  if a == b then true
  else match b with
    | .nilOf b' => a == .nom .nilT || a == b'
    | .nom (.nilable τ') => a == .nom .nilT || a == .nom τ'
    | _ => false
```

Three cases beyond reflexivity, one per disjunct of `subTy`'s `nilable` clause, and the theorem
that makes them usable is `subATy_subst`: **sound at every `θ`**. That is the requirement the open
front end always imposes — it commits before a substitution exists — and it is why `subATy` is a
syntactic approximation rather than a call to `subTy` on the substituted types.

The metatheory change is one line of `Factors`:

```lean
| .ok τ Γ' s' => StoreLe s'.st stF → (∀ a ∈ s'.rets, subTy (a.subst θ) retF = true) → …
```

and it made the `.ret` case *easier*, because `subTy (τ.subst θ) retF` is now literally the premise
where before it was an equation the case had to turn into one. `rets_of_all` is two lines
(`subATy_subst ∘ List.all_eq_true.mp`), `rets_sub`'s four transports are untouched — the predicate
they push down is opaque to them, which is the property that made L201's design worth having.

### Checks

`lake build`, `lake build Metatheory` green; `check-proofs.sh` axiom-clean, **0 `sorryAx`**;
`--check` 52 → **56**, read by transition (four `unknown → accept`, zero reverse); `--assn` smoke
1,227 clean; `--self-test` all agree (two new rows pinning the join's new boundary: an `elsif`
chain accepts, an `elsif` with two unrelated arms still does not); slice-driver 72 lines IDENTICAL;
third ratchet **35**, and `if` drops 5 → 4.

## L205 — `C::n`, the fourth table, and the first `KontOk` arm since L175

Out of fragment **35 → 31** — all four remaining `cpath` bodies — and `--check` is byte-identical
(56/1,169/0), because `baseDecls.scopedConsts` is empty and no bootstraptest program declares one.

This is L196's rung at a different lookup, and stating the difference is the point:

| | `constTy?` (L195/L203) | `scopedConstTy?` (L205) |
|---|---|---|
| key | name | class name × name |
| the machine's read | `constLookup` = `Object`'s **own** table | `constLookupFrom` = the container's **ancestors** |
| the clause | `ConstOk` (+ sole ownership) | `ScopedConstOk` (+ the `private_constant` gate) |
| the kont | none — no subexpression | **`cpathK`** — the base is evaluated first |

### `ScopedConstOk`, and why both its quantifiers are there

```lean
def ScopedConstOk (h : Heap) (c n : String) (τ : Ty) : Prop :=
  ∀ o, (h.classPayload? o).isSome → className h o = c →
    ((ancestors h o).all fun a => match h.classPayload? a with
        | some cp => !cp.privateConsts.contains n | none => true) = true ∧
    ∃ v, constLookupFrom h o n = some v ∧ ValueTy h v τ
```

* **`∀ o`** for `IvarOk`'s reason: the rule is keyed on a *name*, and only `ClassOk`'s uniqueness
  clause ties a name to one id — over the *readable* names, not over every name a program can
  write. So a row claims something about every class object of that name at once.
* **The `private_constant` conjunct** because `.cpathK` consults that gate (L104) and the *rule*
  cannot see it. Same division of labour as `KontOk.asgnIvar`'s conformance premise: a heap fact
  the rule needs is carried by the declaration.
* **`constLookupFrom`, not `constOwn`**, because that is what the machine does — a constant
  inherited from a superclass *is* visible through `C::n`.

Three transports, each a copy of the constant half's: `scopedConstOk_grow` (every clause pinned by a
`PlainGrow` field, with `ancestors_eq` needing saturation), `scopedConstOk_defineMethod`, and
`IvarOnly.scopedConstOk`. Two new `HeapFacts` lemmas underneath them —
`privateConsts_defineMethod` (`consts_defineMethod` one field over) and **`constLookupFrom_congr`**,
an induction on the walk stated over an arbitrary pair of heaps because all three transports need
it.

### `KontOk.cpathK` — the first new continuation arm since L175

```lean
  | cpathK {D h c Γ Γs τ τw cname n σ k} :
      subTy τ (.clsOf cname) = true → scopedConstTy? D cname n = some σ →
      subTy σ τw = true →
      KontOk D h ((c, Γ) :: Γs) τw k →
      KontOk D h ((c, Γ) :: Γs) τ (.cpathK n :: k)
```

The in-flight value is the **base**, and the premise that matters is that its type is a class
object. Everything the *delivery* needs about the heap is in `DeclsOk`, so this arm carries no heap
fact — the difference from `asgnIvar`, which does, is that this rule reads the table where that one
writes the heap.

The arm cost exactly the four places `HANDOFF.md` constraint 4 says it must: `KontOk.retOk` (one
transparent case, and it needs no `_table_ret` composition because the arm does not thread the
table), `KontOk.heap_congr'`, `RetTransparent` (`.cpathK` is one of `unwind`'s catch-all shapes, so a
`.retJ` passes straight through), and `step_ok`'s two cases.

### A proof note worth keeping: a restated `match` is a different function

The delivery's `private_constant` gate could not be discharged by stating the equation

```lean
have hgate : ((ancestors m.heap o).any fun a => match … with …) = false := …
simp only [hgate]      -- "simp made no progress"
```

because **a `match` in a fresh syntactic position compiles to its own auxiliary definition**, so
`hgate`'s lambda and the goal's are not the same function even though they pretty-print identically.
The fix is to `split` on the machine's *own* `if` and keep the goal's term: the hit branch is then
closed by its own equation (`none = some cv` is absurd) and the miss branch by `ScopedConstOk`'s
first conjunct. Same lesson as L193's "`rw` inside a match scrutinee", one layer down.

### The trap, caught by the proof again

`defFree` needed a `.cpath` arm — **the fourth time** (`.array` L174, `.vasgn .ivar` L191, `.ret`
L200): the rule threads the table through the base, so a `def` in there really does change it and
`infer_mono`'s `D₀ = D` half is *false* with the catch-all's vacuous `true` left in place.
`infer_mono_all`'s new case is what found it, one minute after the arm was written. The rule is now
in `implementation-notes.md` four times; it belongs in `HANDOFF.md`'s constraint list.

### Checks

`lake build`, `lake build Metatheory` green; `check-proofs.sh` axiom-clean, **0 `sorryAx`**;
`--check` byte-identical (56/1,169/0); `--assn` smoke 1,227 clean; `--self-test` all agree (two
rows re-read: `Float::NAN` is now a missing *declaration*, and `x::NAN` is the new `cpath-base`
refusal); slice-driver 72 lines IDENTICAL; third ratchet **31**.

## L206 — the store learns equalities, and the join stops refusing

Out of fragment **31 → 30**, `--check` **byte-identical** (56/1,169/0) — the whole rung is in the
*open* front end, which is off the soundness path by construction (`inferOpen_factors` is what
connects it, and that theorem is what changed).

Read the census movement carefully, because the net −1 hides the rung's actual size: **`if` went
4 → 1** and `send-with-block` went **14 → 15**. Three of the four bodies the join was blocking
moved past it and hit a *block*. That is L170–L173's lesson again — *a front-end lift moves the
ranking, not the count* — and it is the reason to read `--sets` rather than the census when picking
the next rung.

### What was actually wrong

`joinATy α τ` was `none`. But the open front end's entire method is *record a requirement and let
the validator check it*, and "α must be Integer" is a requirement like any other. Refusing the body
was strictly weaker than what the checker can say.

```lean
structure Store where
  … ; eqs : List (TyVar × ATy) := []

def joinOpen (st : Store) (a b : ATy) : Option (ATy × Store) :=
  match joinATy a b with
  | some c => some (c, st)
  | none => match a, b with
    | .var α, _ => some (b, st.addEq α b)
    | _, .var β => some (a, st.addEq β a)
    | _, _ => none
```

and the payoff is visible in one `--assn` line:

```
class String; def f; if true then value else 1 end; end; end
  accept : Integer     store: String ⊒ ⟨ value : () → α1 ⟩ ∧ α1 = Integer
```

The body **types**, at `Integer`, under a precondition that now includes a *pin*. Before, it was
`out of fragment: if`.

### The equality is a different kind of atom, and the assertion language had to say so

`Store`'s other three fields are capability requirements — *this type can do that*. An equality is
not: it says the solver has no freedom left at `α`. Three consequences, each a small edit:

* **`Assn.eqv α a`** is a new atom, and its `denote` is the **first that does not mention the
  heap**: `θ α = a.subst θ`. That is exactly what `satStoreB` decides.
* **`entail` gained a fourth list** (`Assn.eqAtoms`) and a fourth conjunct, because an equality
  cannot be *derived* from a heap fact — the antecedent has to contain it. Without that,
  `entail_sound` would be false at the new atom, which is the kind of hole the four-list shape
  exists to prevent.
* **`StoreLe` and `SatStore` are pairs now.** `addEq` only prepends, so the `eqs` half is monotone
  for `rows`' reason, and `SatStore.mono`/`satStoreB_sound` are one component wider.

### The factoring theorem's join step

```lean
theorem joinOpen_subst (h : Store.joinOpen st a b = some (c, st'))
    (hle : StoreLe st' stF) (hsat : SatStore D θ stF) :
    joinTy (a.subst θ) (b.subst θ) = some (c.subst θ)
```

Where `joinATy` answered, this *is* `joinATy_subst`. Where it did not, the recorded equality makes
the **nominal join's first branch** fire — `θ α = b.subst θ`, so the two sides are equal and the
join is reflexivity. One sentence, and it is the whole soundness argument for the rung: *a refusal
became a condition on `θ`, discharged by the validator instead of by the checker.*

Two mechanical notes:

* The join now **grows the store**, so `inferOpen_mono` and `inferOpenIf_mono` gained a
  `joinOpen_mono` link, and the factoring theorem's join cases gained three composed hypotheses
  (`hle2`/`hle3`/`hr2`) before `simp_all` — the bounds the IHs need are one `joinOpen_mono` further
  away than they were, and `simp_all` cannot find a `trans` on its own.
* `joinTy_of_eq`/`joinTy_of_eq'` and `mkNilable_joinOpen` exist for `mkNilable_join`'s reason
  (L193b): the goal is a bare type equation at a variable the tactic cannot name, so the equation
  has to be handed over as a lemma and let unification supply the binder.

### Checks

`lake build`, `lake build Metatheory` green; `check-proofs.sh` axiom-clean, **0 `sorryAx`**;
`--check` byte-identical (56/1,169/0); `--assn` smoke 1,227 clean; `--self-test` all agree;
slice-driver 72 lines IDENTICAL; third ratchet **30**, `if` 4 → **1**.

## L207 — `FrameCtx.meth`, the channel `super` needs, and two findings that reprice the rung

Out of fragment **30 → 30**, `--check` byte-identical (56/1,169/0). An inert channel commit, and
L198 is its precedent: the field exists, nothing reads it, and `StackCtx` carries it so that the
rule can be written without re-establishing anything at forty push sites.

```lean
structure FrameCtx where … meth : Option String := none

-- StackCtx's seventh clause
(∀ mn, c.meth = some mn → (frames.getD fid default).meth = mn) ∧
```

Discharged vacuously at all four construction sites (both `initiation`s, the class-body push, and
`user_dispatch`'s), because every context today has `meth = none`. `StackCtx_congr` and
`StackCtx.heap_congr` each gained one agreement, `setLocal`'s case one more one-liner, and
`infer`'s `def` arm now sets `meth := none` **explicitly** — with the field added, `{ ctx with … }`
would silently inherit the *enclosing* method's name, which is not this body's. That is the same
trap `defFree`'s vacuous catch-all is (constraint 4's companion rule), in the record-update form.

### Finding 1 — the `superName` interaction is *not* an obstacle

`doSuper` looks the target up under `f.meth`, and `userFrame` sets `meth := md.superName.getD mname`
— so a rule that puts `some name` in the context owes *name = md.superName.getD mname*. That reads
like a problem and is not: `superName` is set **only by the alias rule** (`Interp.lean:277`), and a
plain `def` builds its `MethodDef` with the field at its default (`Interp.lean:227`). `alias` has no
`infer` arm, so inside the fragment the two names always agree, and the obligation is a *condition
on the witness* — a prelude method that happens to be an alias simply cannot witness the row, which
is sound.

### Finding 2 — `zsuper` needs a **second** channel, and the HANDOFF pricing was optimistic

Bare `super` forwards *the current parameter values* (`zsuperArgs` reads them out of the frame's
locals), so its argument **types** are the enclosing method's parameter types. `FrameCtx` does not
carry those, and neither does the nominal judgement `bodyVerdictWith` factors into — `Γ` has the
locals but nothing says which of them are parameters. So `zsuper` needs `FrameCtx.params : List Ty`
with a `StackCtx` clause about `runParams`/`locals`, which is a *harder* clause than this one: it
relates a list of declared types to the values in a frame's locals, where `meth` was one string
compared to one string.

**Consequence for the ordering**: `super(args)` (4 bodies) is reachable with this channel plus the
table and the two dispatch lemmas; `zsuper` (2 bodies) is behind a second channel and should be
priced separately rather than assumed to come along. `HANDOFF.md` §The next commit now says so.

### Checks

`lake build`, `lake build Metatheory` green; `check-proofs.sh` axiom-clean, **0 `sorryAx`**;
`--check` byte-identical (56/1,169/0); third ratchet **30**, unchanged — nothing reads the field yet.

## L208 — `TypeAgree`'s sixth clause: a chain fact in the transport, and the price was 4 sites, not 25

Out of fragment **30 → 30**, third ratchet byte-identical. `Proof/`-only, so no `--check` diff is
owed (the binary cannot move) — and `lake build` was run anyway, because the working tree had a
half-applied version of this change in it and "not linked" is an argument, not a check.

This is the first step of the `super` rung, landed **alone** because HANDOFF said to: every later
frame-side fact about a *chain* needs it, and it is inert until one exists.

### What the clause is, and why it cannot be a consequence

```lean
-- L208's sixth clause: an old id's ancestor chain is unmoved.
(∀ k, k < h.objs.size → ancestors h' k = ancestors h k)
```

`TypeAgree`'s other five clauses are all functions of `h.get o`, so `typeAgree_of_get` proves them
from `get`-agreement below the old size. `ancestors` is **not** such a function: it is fuel-bounded
by `objs.size + 1` (L73, so that dispatch stays kernel-reducible), so an allocating step changes the
fuel and the congruence needs **saturation** to bridge it (`Proof/AncestorsGrow.lean`).

So the clause enters as a *hypothesis* on `typeAgree_of_get` — `hanc` — and every caller already had
it from a lemma written for another consumer:

| lemma | the sixth clause's witness |
|---|---|
| `typeAgree_of_get` | hypothesis (it cannot prove it) |
| `typeAgree_of_plainGrow` | `PlainGrow.ancestors_eq hsat` — hence the new `Saturated h` argument |
| `typeAgree_defineMethod` | `ancestors_defineMethod` (L156, written for `constLookupFrom`) |
| `typeAgree_of_fields` | `ancestors_congr` at the same fuel (`hsz` is an *equality* here) |
| `typeAgree_alloc` | now a corollary of `typeAgree_of_plainGrow`, and moved below it |

### The measurement, and it corrects HANDOFF

HANDOFF §The next commit item 3 said the `Saturated h` hypothesis "has to be threaded through
`typeAgree_of_plainGrow`'s **25 call sites** — including `constOk_grow`, `ivarOk_grow` and
`KontOk.heap_congr'`". **The real number is 4**, and two of the four already had `Saturated` in
scope:

* `constOk_grow` and `ivarOk_grow` — signatures gained `(hsat : Saturated h)`, one caller each
  (`DeclsOk_grow`, which already had it);
* `scopedConstOk_grow` (L205) and `inv_grow_value` — **free**, both already carry `hsat` because
  `hg.ancestors_eq hsat` was already load-bearing in them for a *different* clause;
* `KontOk.heap_congr'` — **untouched**. It takes a `TypeAgree` and does not build one.

The over-estimate came from counting `typeAgree_of_plainGrow`'s *uses* as places that would need a
new hypothesis, when the interesting question is which of them lack `Saturated` — and the answer is
that a heap clause needing saturation is *already* the norm on the growing path, so the third rung
of `super` is where saturation gets threaded, not this one. **The transferable rule: a hypothesis's
price is the call sites that do not already have it, and the L205 constant work paid most of them.**

The rest of the diff is arithmetic, not argument: three anonymous constructors gained a sixth
component, and the *one* place that projected the fifth clause positionally
(`ValueTy.congr`'s class branch, `ha.2.2.2.2`) became `ha.2.2.2.2.1`. That single site is the
evidence for the design norm this file has stated twice: clauses go on the **end**, so an append
renumbers exactly the accessors of the clause that used to be last.

### Checks

`lake build` and `lake build Metatheory` green; `check-proofs.sh` axiom-clean, **0 `sorryAx`**,
`heapOkB`/`saturatedB` still hold at the booted heap; third ratchet **30**, unchanged and
byte-identical — nothing reads the clause yet.

## L209 — the chain fact reaches the frame: `ResolvesUser`'s eleventh clause and `StackCtx`'s fifth, extended

Out of fragment **30 → 30**, third ratchet byte-identical, `Proof/`-only. `super`'s second
prerequisite, and — like L207 and L208 before it — inert: nothing reads either clause yet.

### What was owed

`doSuper` (`Interp/Send.lean:260`) walks

```lean
(ancestors m.heap (classOf m.heap f.self)).dropWhile (· != f.defmod) |>.drop 1
```

so if the frame's definee is **not on** the receiver's dispatch chain, `dropWhile` consumes the whole
list and `doSuper` raises `NoMethodError` — type-stuck, which is what the checker exists to rule out.
The fact is therefore owed at the frame, and it has to *cross the call* the way L189's `cref` clause
does.

### Two clauses, and the design decision is where to put the second

1. **`ResolvesUser` gains `md.owner ∈ ancestors h k`** (clause 11). *Not* derivable from clause 1 —
   and the gap is one the existential hides: `lookupIn h k mname = some (owner, md)` gives
   `owner ∈ ancestors h k` (a `lookup.go` induction), but the frame is built with **`md.owner`**, and
   nothing in the fragment pins the two together. Stating it costs one line at the *only* production
   site (the `def` consecution), where `md.owner = defmod` by construction and `ClassOk`'s reopen
   clause already gives `hrest : ancestors … defmod = defmod :: rest`. All three transports
   (`_grow`, `_defineMethod`, `IvarOnly.resolvesUser`) discharge it with the `ancestors` rewrite they
   already perform for the shadow clause.

2. **`StackCtx`'s `selfCls` clause gains the chain fact as a second conjunct** — rather than a new
   clause of its own, and the guard is the whole reason:

   > The transport needs `classOf h' self = classOf h self`, which for a `.ref o` needs
   > `o < h.objs.size` — and `ValueTy h self (.cls sc)`, the clause's *first* conjunct, is exactly
   > that fact (`valueTy_ref_lt`). Free-standing, the chain clause would have had to carry a bound of
   > its own. Attached, it carries none.

   And the guard is right on its merits: a class body says `selfCls = none` and owes neither half,
   which is correct — there `self` is the class object, `defmod` is the class, and a class is not on
   its own eigenclass's chain. **This is the second time the *pairing* of a new clause with an
   existing one was cheaper than a new conjunct** (L193's subsumptive `ValueTy` absorbing four of
   `ClassOk`'s was the first).

### The bound came out of the membership, which is the finding worth keeping

The chain congruence also needs `classOf h self < h.objs.size`, and *nothing* was going to supply it
— until the definition of `ancestors` did:

```lean
theorem classOf_lt_of_mem_ancestors (hd : (h.classPayload? d).isSome) (hm : d ∈ ancestors h k) :
    k < h.objs.size
```

`ancestors.go`'s `classPayload? = none` arm returns `[k]`, so a **non-class** id's chain is the
singleton `[k]` (`ancestors_of_not_class`, new in `Proof/HeapFacts.lean`). So either `k` is a class —
bound by `classPayload?_isSome_lt` — or the member *is* `k`, and the member is a class by hypothesis,
which contradicts `k` not being one. **Membership in a chain bounds the chain's root**, and the
second case is vacuous rather than proved. `StackCtx`'s own first clause supplies `hd`.

### What it cost, itemized

| site | change |
|---|---|
| `ResolvesUser` | one clause; three transports gained one rewrite each |
| the `def` consecution | one line (`rw [hown, hrest]`) |
| `StackCtx` | one conjunct inside clause 5 |
| `StackCtx_congr` | the clause now spends **two** frame agreements (`self` and `defmod`) where it spent one |
| `StackCtx.heap_congr` | the new work: a `cases` on the self value (immediates are `rfl` — a `Boot` dispatch class is heap-independent), then the two rewrites |
| the two user pushes | `⟨hv, hch⟩` where they had `hv`, `hch` from `ResolvesUser`'s new clause |
| five `hself` derivations | `exact this.1` |

Nothing else moved, and in particular **`TypeAgree` did not have to grow again**: L208's sixth clause
is exactly what `heap_congr` spends here, one commit after it landed inert. That is the check on
L208's framing — a transport clause landed for a named future consumer, and the consumer used it
unchanged.

### Checks

`lake build` and `lake build Metatheory` green; `check-proofs.sh` axiom-clean, **0 `sorryAx`**; third
ratchet **30**, byte-identical. No `--check` diff owed (`Proof/`-only, not linked into the binary).

## L210 — `meth` populated end to end: the context names the method, and it stays inert

Out of fragment **30 → 30**, `--check` **56 / 1,169 / 0 — byte-identical**, `--assn` 1,225 clean /
2 decode gates. `super`'s third prerequisite and the first one that touches the **checker**, which is
why this commit owes the `--check` diff where L208 and L209 did not.

L207 landed `FrameCtx.meth` with `none` everywhere. This commit makes it *carry a name*, at all three
places a name exists, and the point of doing it alone is that the three have to agree and nothing
reads the field yet — so a disagreement shows up as a failed proof rather than as a wrong verdict.

| layer | before | after |
|---|---|---|
| `infer`'s `def` arm | `meth := none` explicitly | `meth := some name` |
| `UserConforms` | `(D) (c) (md) (d)` | `(D) (c mname) (md) (d)`, ctx `meth := some mname` |
| the machine's activation | `userFrame` sets `meth := md.superName.getD mname` | unchanged — a `ResolvesUser` clause makes it agree |
| the open front end | `OCtx = {cls, self}` | `OCtx.meth`, and `inferBody`/`bodyVerdict`/`inferBodyWith`/`bodyVerdictWith` take `mname` |

### The one real obligation, and it was already priced

`userFrame` builds the activation with `meth := md.superName.getD mname`, so a context saying
`meth := some mname` owes *`md.superName.getD mname = mname`*. **`ResolvesUser` gains
`md.superName = none`** (clause 12), and L207's finding is what makes it free: `superName` is set
**only** by the alias rule (`Interp.lean:277`), a plain `def` leaves it at its default, and `alias`
has no `infer` arm — so the one production site discharges it with `rfl`, and a prelude method that
*is* an alias simply cannot witness a row, which is sound. That is the same shape as clause 11 (L209)
and clause 10 (L189): **a fact about the callee that only the definition site can know travels on the
resolution predicate.** Three clauses, three commits, one pattern.

### `OCtx.meth`, and why the open side had to move in the same commit

`UserConforms` is discharged two ways — by the `def` consecution (nominal) and by
`userConforms_of_inferBody` (open) — and the second goes through `inferOpen_factors`, whose conclusion
*builds* the nominal context out of the open one. So fixing `UserConforms`' `meth` forces `OCtx` to
carry it: the four `Factors`/`FactorsIf`/`FactorsSeq`/`FactorsArgs` conclusions now say
`meth := ctx.meth`, and the induction is unchanged — **the field is threaded, never read**, so all
twenty-odd arms still close by the same uniform `simp_all`.

`inferOpen` itself does *not* read `ctx.meth` yet. `super` is the arm that will, and when it does the
name is already there — which is the entire value of this commit.

### What "inert" was checked by

Three checks, and only the first is the interesting one:

* **`--check` over the 1,227 cached bootstraptest ASTs: 56 accept / 1,169 unknown / 0 reject**, the
  L207 baseline unchanged. `infer` gained no arm, so the only way this could have moved is if the
  new context leaked into a *verdict*, and it did not.
* `--assn` over the same corpus: 0 non-zero exits outside the two decode gates.
* third ratchet **30**, byte-identical, `--self-test` all agree.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`**; tier 0 and
tier slice green (nothing on the execution path moved — no `Interp/` file changed).

## L211 — the fifth table, and `SuperOk`: the builtin arm alone, deliberately

Out of fragment **30 → 30**, `--check` byte-identical, tier 0 **992 agree / 0 disagree**, tier slice
**351 / 0**. `super`'s fourth prerequisite: the declaration it will read and the heap clause a row
obliges. Nothing reads either yet — `infer` has no `.super'` arm — which is the last inert commit
before the rule.

**Landed in the same commit as L210** rather than after it. The two were developed back to back and
`Types/Decls.lean`/`Proof/Static/Decls.lean` carry hunks of both interleaved; splitting the working
tree after the fact would have meant a commit whose build was never actually run. Both notes are
here; the checks below cover the pair.

### `Decls.supers`, keyed on the pair

```lean
supers : List ((String × String) × MethodDecl) := []
def superDecl? (D : Decls) (cls name : String) : Option MethodDecl
```

Keyed `(class, method)` — `scopedConsts`' shape (L205) — because a `super` inside `C#m`
re-dispatches `m` starting *after* `C`, so the answer depends on both. The alternative HANDOFF
priced (a `parent : String → String` table plus `declOf?` on the parent's rows) needs a heap clause
tying a *name* to a chain position, and `ClassOk`'s uniqueness covers only `readableClasses` — which
is exactly the population the slice's `super` bodies are **not** in.

`SubDecls` becomes a quintuple, with the same equality (not containment) the other three tables get,
and for the third time the same reason: the rule reads its answer *out of* the table, so a `F'`
disagreeing at the same key would make `infer_mono` **false**, not merely unprovable.

### `SuperOk`, and `superFound` as the shared vocabulary

```lean
def superFound (h : Heap) (k dm : ObjId) (mname : String) : Option (ObjId × MethodDef) :=
  (((ancestors h k).dropWhile (· != dm)).drop 1).firstM fun c => …

def SuperOk (h : Heap) (c mname : String) (d : MethodDecl) : Prop :=
  ∀ k dm, (h.classPayload? dm).isSome → className h dm = c → dm ∈ ancestors h k →
    ∃ owner md bid, superFound h k dm mname = some (owner, md) ∧
      md.builtin = some bid ∧ ConformsAt (.cls c) mname bid d
```

`superFound` is written to match `Interp/Send.lean:266-270` symbol for symbol, and it exists so that
the invariant and the (not yet written) dispatch lemma name the *same* function rather than two
copies. The quantification is over a class **name** and any chain such a class is on, because
`StackCtx` knows the frame's definee only by its name — `IvarOk`'s shape, at a chain instead of at an
object. L209's `StackCtx` clause is what supplies `dm ∈ ancestors h k`.

**Only the builtin arm.** A user arm is `ResolvesUser` plus `UserConforms` at a frame push, and
leaving it out is a choice, not an omission: with the builtin arm alone no *program* method can
witness a row, so `preludeDecls` declares none, and the four `super(arg)` bodies will report a
**needed declaration** rather than an accept. That is §5's reading of an unsatisfiable requirement
(`Regexp`, L106) verbatim, and what it buys is the rule and its consecution case landing *before* the
harder witness instead of after.

### The one thing that was not free: `declaresName`

A `def` writes a live method table, and `SuperOk` is a claim about what `doSuper`'s walk **finds** —
so a `def` of a name some `supers` row is keyed on can *displace* that row's target. That is exactly
the side condition `superOk_defineMethod` needs, and the `def` rule's existing freshness test did not
see it, because `declaresName` scanned `rows` only. It now scans both:

```lean
(D.rows.any fun cd => cd.2.any fun md => md.1 == name) ||
(D.supers.any fun sd => sd.1.2 == name)
```

**This is the pattern L194 and L196 both hit**: a new table is not just rows, it is a new way for an
existing rule's guard to be *insufficient*. Free today (the table is empty) and `--check` confirms
it, but it is the kind of thing that is a soundness bug if it is noticed a commit later.

### Three transports, all one-liners over `superFound_congr`

`superFound_congr` takes *per-id method-table agreement* plus *one chain equality* — deliberately
stated over the list rather than over the chain, so each caller supplies its own. Then:

| transport | the two facts |
|---|---|
| `superOk_grow` | `PlainGrow.payload` at every id, `ancestors_eq hsat` |
| `superOk_defineMethod` | `methods_find_defineMethod` (needs `n ≠ name`), `ancestors_defineMethod` |
| `IvarOnly.superOk` | `hi.classPayload`, `hi.ancestors_eq` |

`ConformsAt` mentions no heap (L146), so the conformance half passes through all three untouched —
the fourth commit in a row where L146's decision pays.

`InvA` (`Proof/Static/Assn.lean`) gained the conjunct too, and `invA_iff_inv` one component in each
direction.

### Checks (covering L210 and L211)

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`**;
`--check` over the 1,227 cached ASTs **56 accept / 1,169 unknown / 0 reject**, byte-identical to
L207's; `--assn` 1,225 clean / 2 decode gates; third ratchet **30**, `--self-test` all agree;
`difftest --tier 0` 992 agree / 0 disagree, `--tier slice` 351 / 0.

## L212 — the `super` rule, and it is the first new *dispatch* since L157

Out of fragment **30 → 30** (the open front end is L213), `--check` byte-identical at
**56 / 1,169 / 0**. The rule, its two consecution cases, a new `KontOk` constructor and a new
dispatch lemma — and it accepts nothing yet, because the `supers` table is empty and only its builtin
arm exists (L211). What it buys is that the *next* commit can report a **needed declaration** for a
rule that is actually there.

### The rule

```lean
| .super' [] none | .super' (arg :: args) none =>
  -- ctx.meth = some mn, mn ≠ "", superDecl? D ctx.cls mn = some d, arity/types match
```

Two arms for the reason `.send`'s two are two: **different numbers of machine steps.**
`startSuperArgs m [] [] blk` *is* `doSuper` (dispatch happens in this step, no continuation), while
`startSuperArgs m [] (arg :: rest) blk` pushes a `superArgK`.

Three guards, each paying for a `doSuper` answer that is not a value:

* `ctx.meth = some mn` — L210's channel, and without it there is no name to re-dispatch;
* **`mn ≠ ""`** — `doSuper`'s own *"super outside a method"* test, which answers `.unsupported`, and
  `StepOk .unsupported = False`. So the rule has to *rule it out* rather than assume no row is keyed
  at the empty name. Cheap, and the kind of thing that is only visible from the interpreter's source;
* `subTys τs d.params` — the send's own check.

### Placement, measured

The arms are **last** in `infer`'s match, for `.flt`'s reason (L202) — and this time the cost of
getting it wrong was measured rather than predicted. Written beside `.send`, they shifted
`infer.induct`'s case numbering by **11** and `Proof/Static/Mono.lean` broke at nine places; moved to
the end, only the `inferIf`/`inferSeq`/`inferArgs` alternatives moved (they are numbered *after* every
`infer` arm, so any new arm shifts them). Recovery was the trick the file's own note describes, made
cheap: `| caseN a1 … a20 => sorry` for a whole *range* of N in one build reports every alternative's
arity at once, and the arities identify the alternatives (17 = `inferIf`'s else arm, 4 = a `nil`).
**That is a better recovery than the note's "read the list off a trace".**

`defFree` gained a `.super'` arm — the fifth time (`.array` L174, `.vasgn .ivar` L191, `.ret` L200,
`.cpath` L205) — and this time it was written *with* the rule instead of after `infer_mono_all`
complained.

### `superFound` moved into the interpreter, and that is the finding

`SuperOk` (L211) named `doSuper`'s walk as a copy of it in `Proof/Static/Decls.lean`. The copy was
character-for-character the same and **`rw` still would not fire**: `unfold doSuper` eta-reduces
`fun (_, md) => (c, md)` to `fun x => (c, x.snd)`, and after chasing that, the two terms printed
identically and still did not unify.

So `superFound` now lives in `Interp/Send.lean` and `doSuper` *calls* it. The proof references the
same constant the interpreter does, and `rw [hf]` is one rewrite.

> **A definition the proof needs to name belongs in the code, not in a copy beside the proof.** The
> refactor is behaviour-preserving by construction (`doSuper`'s body is unchanged modulo the `let`),
> and it is the second time a proof-side duplicate of an interpreter expression has cost more than
> naming it would have.

### `KontOk.superArgsK`, and what it does *not* carry

`argsK` with the receiver removed: no stored receiver, no `sigOf`. The signature comes out of the
`supers` table at `(c.cls, mname)`, so the *context's* `meth` is a premise of the constructor rather
than a field of the kont — which is what ties the kont's signature to the activation `doSuper` will
read. `blk` is stored by the machine and mentioned nowhere in the constructor, for `arrK`'s reason at
a different field: the builtin arm ignores it, and the user arm is not in the fragment.

`RetTransparent` gained `.superArgK` (a pending `super` argument has no opinion about a `.retJ`), and
`KontOk.retOk`/`heap_congr'` each gained a one-line case.

### `super_dispatch` is *cheaper* than `entry_dispatch`, and the reason is worth knowing

**`doSuper` has no gates.** It goes straight from `found` to `md.builtin`, where `invoke` first walks
receiver shapes, `invokeMaybeNew`, visibility and the CRuby shadow table. So there is no
`valueTy_shapes` case split at all and the receiver stays abstract — the lemma is fifteen lines where
`entry_dispatch` is a hundred.

Everything about the frame is a hypothesis, because everything about the frame is a `StackCtx` clause
at the call site: the running name (L207/L210), the definee's name and class-ness (L154), that the
activation is not a block (L212, added to the `meth` clause for `returnTarget`'s reason at
`methodFrameOf`), that `self` is an instance of the class the body is written in (L212, the third
conjunct of the same clause), and **that the definee is on the receiver's chain (L209)** — the one
without which `dropWhile` empties the list and `doSuper` raises `NoMethodError`, which is precisely
the type-stuck outcome the checker exists to exclude.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`**; `--check`
byte-identical (56 / 1,169 / 0); third ratchet **30**; tier 0 and tier slice green, and the
regressions corpus re-run because `Interp/Send.lean` was touched.

## L213 — the open front end for `super`: 30 → 26, and the fifth ratchet reprices `zsuper` from 2 to 9

Out of fragment **30 → 26**, `--check` byte-identical (56 / 1,169 / 0), `--assn` 1,225 clean / 2
decode gates. The four bodies L212's rule was built for have crossed, and all four report a **needed
declaration**:

```
NullToken#initialize      needed: NullToken ~ super:initialize : (NilClass) → _
StringToken#initialize     needed: StringToken ~ super:initialize : (α2) → _
NumericToken#initialize    needed: NumericToken ~ super:initialize : (α2) → _
RegexParser#initialize     needed: RegexParser ~ super:initialize : () → _
```

Four for four — this file had `RegexParser#initialize` down as possibly behind a second blocker and it
was not.

### The arm, and why it is *split by arity*

`inferOpen`'s `.super'` arm is the **nominal-receiver send arm's shape at a different table**: the
class is known (it is `ctx.cls`, the class the body is written in), so unlike a send there is no row
to *record* in the store — a `super` cannot constrain a type variable, because its receiver is `self`
and its target is fixed by the chain. An undeclared pair is therefore a needed declaration outright.

The first draft had **one** arm over `args`. It built and the census moved, and then
`inferOpen_factors` failed at `case64` with *"`split` failed: could not split an `if` or `match`"* —
because nominal `infer` has **two** `super` arms and a single open arm has to case-split on the list
*inside* the proof to reach them. Splitting the open arm by arity to mirror the nominal rule made
both new cases close under the existing uniform `simp_all` block with **no new alternative**.

> **A front-end arm should be indexed the way the nominal rule is indexed.** That is the same
> discipline as "no `infer` arm the preservation proof is not indexed by" (constraint 4), stated for
> the factoring theorem — and here it was the difference between zero proof work and a new
> alternative in the hardest tactic block in the project.

`== dd.params.map ATy.nom` rather than `subATy`, for the nominal-receiver send arm's reason (L175):
the open side has no substitution yet, so a *witness* that the argument types are below the declared
ones is not available; equality is, and `ATy.subst_nom_comp` is what lets the factoring see it.

### `fragment-gap.py`: two mirrors, and the fifth ratchet's answer changed

`shape_super` (the per-construct census) and `_body_blockers`' `super` case (the blocker-set ratchet)
both admit `super` now, refusing only a literal block on the `super` itself and a splat/kwargs/fwd
argument. Three `--self-test` rows were added, and they pin **two different reasons** for `unknown`:
at toplevel `--check` passes `meth = none` so the rule cannot fire at all, and inside a `def` the
`supers` table is empty so the body needs a declaration. Both rows staying `unknown` is what makes
the PARTIAL classification honest.

### And the fifth ratchet says something the fifth ratchet's own docstring does not

```
bodies whose blocker set is a SINGLETON — each is a body one rung frees:
    9  {zsuper}     1  {next}     1  {hash}     1  {begin}
```

`zsuper` is **2** in the third ratchet and **9** here, and the first reading of that — *"L207 priced
the value wrong by a factor of four, do `zsuper` next, it frees nine"* — **was written into this file
and is wrong.** Checking the nine bodies against `--assn-dump` is what caught it:

```
AlphaToken#<=> … PostToken#<=>   (6)   needed: T.class_of(Object) ~ ::Token : () → _
Version#respond_to?              (1)   needed: Array ~ include? : (α1) → _
Version#==, Version#freeze       (2)   out of fragment: zsuper
```

**Seven of the nine are already in the `needed:` column, not in `oof`.** `inferOpen` short-circuits at
the first `.missing`, so a body with an early needed atom and a later out-of-fragment construct is
reported as `needed` — while its blocker *set* still contains the construct. So landing `zsuper` moves
**oof 26 → 24**, and moves nothing out of `needed`.

> **The fifth ratchet measures freedom from the *rule set*, not freedom from `oof`, and the two
> diverge once the `needed:` column is large.** At 64 needed against 26 oof that divergence is now the
> common case, and the ratchet's own header — *"each is a body one rung frees"* — reads as a promise
> about `oof` that it cannot keep. Header corrected in `fragment-gap.py`.

What the 9 *does* measure is worth having, and it is the better number for a **whole-file** verdict:
after `zsuper`, nine bodies are entirely inside `infer`'s domain and blocked only on **declarations**.
`{zsuper}` is still the right next rung on that reading — the next-largest singleton is one — but the
census will move by 2, and a claim of 9 would have been a false prediction the next session would have
had to eat.

> **`zsuper` is next.** `FrameCtx.params : List Ty` plus a `StackCtx` clause relating declared types
> to a frame's `runParams`/locals — a list against a store, which is harder than `meth`'s string
> against a string. **Expected: oof 26 → 24, and nine bodies whose only remaining obstacle is the
> declaration table.** Write both numbers down before starting so the outcome is checkable.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`**; `--check`
byte-identical; `--assn` 0 failures outside the two decode gates; third ratchet **26**, `--self-test`
all agree; tier 0 and tier slice green.

## L214 — `zsuper`, and the prediction held: 26 → 24, with the nine bodies moving to declarations-only

Out of fragment **26 → 24**, `--check` byte-identical (56 / 1,169 / 0), `--assn` 1,225 clean / 2 decode
gates. Both numbers L213 wrote down in advance came out:

```
before                                    after
oof 26   {zsuper} singleton = 9           oof 24   singletons: {next} 1, {hash} 1, {begin} 1
marginal table headed by zsuper-sets      marginal table headed by ['block','preq','send-block'] = 10
```

The singleton table is now empty of anything worth a rung, and the marginal table's head is **Wall 1**.
That is the board changing shape rather than shrinking: what is left is the wall, three ones, and the
sets.

### One rung, one commit, because `super` had already paid for it

`FrameCtx.params` / `OCtx.params`, one `infer` arm, one `inferOpen` arm, one `StackCtx` conjunct, one
consecution case — and **no new dispatch lemma and no new `KontOk` constructor**. `evalExpr`
reconstructs the arguments from the frame and calls `doSuper` in the same step, so `super_dispatch`
(L212) is reused verbatim at `args = []`. This is the cheapest of the three `super`-family cases and
L207's finding two — *"price `zsuper` separately, it does not come along with `super`"* — was right
about the **channel** and wrong about everything downstream of it.

### The `StackCtx` clause: the general form was written first and is *false*

The clause `zsuper` wants is *the enclosing method's parameter values are reconstructible and have the
declared types*:

```lean
∃ vs, zsuperArgsOf h (frames.getD fid default) = some (vs, []) ∧ ValuesTy h vs c.params
```

It was written, and `StackCtx_congr` refused it — correctly. **`zsuperArgsOf` reads the frame's
`locals`, and `setLocal` writes them.** `x = x + 1; super` really does change what a bare `super`
forwards (there is a `[V]` note on `zsuperArgs` saying exactly that), so the clause is not congruent
under the one rewrite `StackCtx_congr` exists for. Typing it needs the parameters to be *in `Γ`* with
`FrameConforms` tying them to the locals — which is the `def`-with-a-row rung, not this one.

So the locals-independent form, which is what is actually true today:

```lean
(frames.getD fid default).runParams = [] ∧
(frames.getD fid default).runFromDM  = false ∧
c.params = some []
```

`ResolvesUser` requires `md.params = []`, `userFrame` therefore sets both frame fields, and no context
the invariant builds declares a parameter. The consecution case then gets `zsuperArgs m = some ([], [])`
**by computation** — which is how the interpreter's own two `none` branches (a `define_method` body,
destructuring parameters) are *refuted* rather than handled.

> **A clause that reads `locals` cannot ride on `StackCtx`.** Six of `StackCtx`'s clauses read frame
> fields `setLocal` does not touch, and that is not a coincidence — it is the predicate's design
> constraint, and it is worth stating before the next frame-side clause is drafted.

`StackCtx_congr` gained its seventh and eighth agreements (`runParams`, `runFromDM`) and the `setLocal`
case two more copies of the same one-liner. `zsuperArgsOf` was factored out of `zsuperArgs` for
`superFound`'s reason (L212) — `StackCtx` is indexed by `(heap, frames, stack)` and has no `Machine`,
so the clause has to be statable about **one frame**.

### `params` is an `Option`, and it mirrors `zsuperArgs`'

`zsuperArgs` answers `none` when the shape is not reconstructible. So does the channel:
`FrameCtx.params : Option (List Ty)`, `OCtx.params : Option (List ATy)`, and the rule **refuses `none`
rather than guessing**. `openParamTys` decides it on the open side, and it is all-`.req` only — for an
all-required list `openParams` allocates `1, 2, …, n` in order, so the list is exactly the variables
the body's parameters were opened at; any other kind either allocates differently or is re-bundled by
`zsuperArgs` into keywords, and the two would disagree.

`openParamTys` is a **mirror** of `openParams`' allocation order, which is the kind of copy this
project has been burned by twice (`SUPPORTED`). It is not a soundness risk *today* and the reason is
worth writing down rather than assuming:

> A context with a non-empty `params` cannot be **spent**. `StackCtx` pins every activation the
> invariant describes to `some []`, so a wrong list in `openParamTys` can only ever fail to certify,
> never certify wrongly. That is the same standing `accept (params open)` has had since L168 — and
> `egParam_nominal` now shows it *in a type* (`params := some [.int]`, a context `infer` accepts and no
> machine context matches) rather than in prose.

### Case renumbering, third time, and the recovery is now routine

The `.zsuper` arm shifted `infer.induct` by 5 (the `inferIf`/`inferSeq`/`inferArgs` alternatives are
numbered after every `infer` arm, so *any* new arm moves them). Arity-probing a range in one build
located them; a second probe with `trace_state` over 68–87 identified the new accepting case as
`case82`. Two builds, no guessing — and `defFree` got a `.zsuper` arm even though the rule reads the
context rather than a subexpression, because the catch-all's `true` being *right by accident* has cost
this project five commits already.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`**; `--check`
byte-identical; `--assn` 0 failures outside the two decode gates; third ratchet **24**, `--self-test`
all agree (three new rows, one of them pinning the parameter-shape refusal); tier 0, tier slice and the
regressions corpus re-run because `Interp/Send.lean` was touched again.

## L215 — `ConformsAt` may allocate: Wall 2's first half, and the measurement that says it is the gate

Out of fragment **24 → 24** by design; `--check` byte-identical (56 / 1,169 / 0), `Proof/`-only. This
commit moves no body. It removes the reason the two remaining populations *cannot* be moved.

### The measurement first, because it is what picked this commit

After L214 the census is 24, and the question is which rung is next. Reading the remaining bodies
against the code says: **there is no longer a rung that is not behind a wall or a one-body session.**

| construct | bodies | measured price |
|---|---|---|
| `send-with-block` | 15 (10 freed by the rung alone) | Wall 1's three-channel judgement **and** Wall 2 — `finishSend` reifies a literal block into a `Proc` *before it dispatches*, so a block send allocates |
| `splat` | 3, and they are **three different rungs** | a splat *argument* (destroys the arity a signature is matched against); a splat on a **masgn RHS** (`_, v, r = *path.match(…)` — destructuring); a splat *array element* (needs a new `Inv` conjunct — *class `Array` ⇒ `.arr` payload* — with a boot certificate and transports, for **one** body) |
| `begin` | 2 | the rescue machinery (`CtlOk`'s `.jump` at `.raiseJ`, six kont arms, `retry` as a loop) **and** Wall 2 — both bodies `rescue Uncomparable`, and `class Uncomparable < StandardError` is a *program* class with an explicit superclass, i.e. the allocating `class'` branch |
| `gvar` / `if` / `next` / `hash` | 1 each | four separate rungs. `hash` is the one worth naming: `plainRecv` **excludes** a `.hsh` payload, so a hash literal's value has no type *at all* — it is L185's class-arm work over again, not a `Ty` arm |

**Two of those rows are new information.** `splat` being three rungs is the fourth instance of L192's
rule (*a blocker **name** ranks what it costs*); and `begin`'s dependence on Wall 2 was not written
down anywhere — `slice-verdict.md` §4 had the two walls as *a* pair, not as *the* gate on the whole
remaining census.

### What changed

```lean
-- before
∃ w, ValueTy m.heap w d.ret ∧ Builtins.run bid recv args m = .ok w m
-- after
∃ w m', Builtins.run bid recv args m = .ok w m' ∧ ValueTy m'.heap w d.ret ∧
  PlainGrow m.heap m'.heap ∧ m'.frames = m.frames ∧ m'.stack = m.stack ∧ m'.kont = m.kont
```

*The machine unchanged* → *the machine grown*. The four facts are **`inv_grow_value`'s hypotheses
verbatim** (L149 wrote that lemma for the literal producers and it has been sitting there since), which
is why the generalization is the weakest one that works rather than a design: `entry_dispatch` and
`super_dispatch` carry the new machine in their conclusions, and their six call sites end in
`inv_grow_value` where they ended in `inv_value`.

**It cost four proof edits and two witnesses**, and the reason it was cheap is worth recording against
the docs' own pricing: `baseDecls` has **four rows** (`Integer` `+`, `-`, `*`, `zero?`), witnessed by
two lemmas, and both leave the machine alone — so each supplies `PlainGrow.rfl'` (new, in
`Proof/HeapGrow.lean`) and three `rfl`s. `slice-verdict.md` §3.3's "~128 rows" is the *future* table;
the wall was never 128 witnesses wide, it was one definition and six call sites.

> **A wall priced as structural can turn out to be one clause deep.** This is the second time
> (L195/`Decls.consts` was the first): what made it look large was that its *consumers* are large, not
> that it is.

### What the clause now excludes, and the exclusion is the point

A builtin that **mutates** an existing object — `Array#push`, `String#<<` — is not a `PlainGrow`,
because `get`-agreement below the old size is exactly what in-place mutation breaks. Such a row is
still untabulatable, but now for a reason the clause *states* rather than one it happened to imply. A
mutating row needs its own transport (`IvarOnly`'s shape at a payload), which is a rung and not a
relaxation of this one.

### What is still owed on Wall 2

The **other** half: the allocating `class'` branch (`ClassGrow`, a `consts`-only write, the frame
push — priced in `HANDOFF.md` §After that). This commit makes the *builtin* side able to allocate; the
class-object side is untouched. `Class#new`, the regex literals, and the ~8 program class names are all
still behind it.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`**; `--check`
byte-identical (run anyway, though `Proof/`-only owes no diff); third ratchet **24**, unchanged.

## L216 — `StepOk` admits a non-type-error `.uncaught`, and the strengthening it had was not load-bearing

Out of fragment **24 → 24**, `Proof/`-only, and the headline theorem is *unchanged*. One clause, one
one-line proof edit, and the whole metatheory went through with nothing else touched — which is the
finding.

### What was in the way of `raise`

`typeStuck` has always been

```lean
def typeStuck : StepResult → Prop
  | .uncaught exc m => isTypeError m.heap exc
  | _ => False
```

— an uncaught **user** exception is not type-stuck, and `invariant_sound` never claimed otherwise. But
`StepOk` was refusing `.uncaught` outright (`| _ => False`), which is *stronger than the theorem needs*
and is exactly what makes `raise` unstateable: no rule can produce a jump the bundle forbids, so
`CtlOk`'s `.jump _ => False` could never be relaxed and `begin`/`rescue` had nowhere to start.

```lean
  | .uncaught exc m => ¬ isTypeError m.heap exc
```

### Why it costs nothing

`StepOk` is not the theorem; it is the bundle `step_ok` proves so that the 48-way `Kont` split happens
once instead of twice. The two consumers are in `Proof/StaticSoundness.lean`:

* `consecution` reads only the `.next` case — **unchanged**;
* `safety` proves `¬ aboutToTypeStick`, i.e. `¬ typeStuck (stepFn m)`, and its `.uncaught` branch went
  from `exact hok` (with `hok : False`) to `exact hok hbad`. The new clause **is** that branch's
  obligation rather than a vacuous refutation of it.

`Inv` did not move, so `invariant_sound`/`check_sound`/`assn_sound_from` are the same statements.

And the existing raising branches did not need touching: they are closed by showing the step
unreachable (the rule's guards), not by `StepOk` being `False` there — so weakening the goal from
`False` to `¬ isTypeError` left every one of them proved. **That is the evidence the strengthening was
carrying nothing**: if any branch had been relying on it, the build would have said so.

> **Check what the theorem needs before assuming the bundle should match it.** `StepOk` had been
> strictly stronger than `safety`'s obligation since F1a, and the cost of that surplus was not a proof
> — it was a *rule that could not be written*.

### What is still owed for `begin`/`rescue`

This is the first of three. Next: `CtlOk` gains a `.jump (.raiseJ exc)` case (`¬ isTypeError` plus a
`RaiseOk`-style relation tracking that each `frameK` the jump passes pops one environment — `RetOk`'s
shape at L200, minus the type, since a propagating raise carries no value type the continuation reads).
Then the `raise`/`begin` rules, which is where the census moves (24 → 22).

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`**; third ratchet
**24**, unchanged. No `--check` diff owed (`Proof/`-only).

## L217 — `CtlOk` admits a propagating raise, and the first draft of the arm was wrong

Out of fragment **24 → 24**, `Proof/`-only. The second of three for `begin`, and still inert — no rule
produces a `.raiseJ` yet, so the arm is proved and unreachable.

```lean
| .jump (.raiseJ exc) => ¬ isTypeError m.heap exc ∧ RaiseOk Γs m.kont
```

### The first draft had only the first conjunct, and the argument for it was seductive

*A propagating raise owes nothing about the continuation — it carries no value the receiving kont has
to accept — so `frameKLabels` and `StackCtx`, which `Inv` already has, should carry the pops on their
own.* Every clause of that is true and the conclusion is false. **`CtlOk`'s jump arm has no `KontOk`**,
so nothing bounds which konts are on the stack — and `unwind` does not propagate a raise through all
of them. `definedGuardK` turns it into `.next (withCtl m (.value .nil))` (an exception while evaluating
a `defined?` operand makes it `nil`), at which point `CtlOk` wants a `KontOk` for the continuation and
there is none to be had.

So the stack has to be *known* to be raise-propagating. Found by writing the case and reading the
goal, not by reasoning about it.

> **"This jump carries no type" does not imply "this jump needs no continuation invariant."** The two
> obligations are independent: `RetOk` exists for the *type* agreement at a `frameK`, and `RaiseOk`
> exists for the *shape* of the stack. Dropping the type does not drop the shape.

### `RaiseOk`, and it is cheaper than `RetOk` in every dimension but existence

```lean
inductive RaiseOk : List (FrameCtx × Env) → List Kont → Prop where
  | nil  {Γs}       : RaiseOk Γs []
  | skip {Γs κ k}   : RetTransparent κ → RaiseOk Γs k → RaiseOk Γs (κ :: k)
  | pop  {cΓ Γs k fid} : RaiseOk Γs k → RaiseOk (cΓ :: Γs) (.frameK fid :: k)
```

No `Decls`, no `Heap`, no type — it is a statement about the *shape* of `(Γs, kont)` and nothing else.
`KontOk.raiseOk` derives it, one line per `KontOk` constructor, with none of `KontOk.retOk`'s
machinery (no `top = false`, no `c.ret`, no `infer_table_ret` composition) because there is no type to
line up.

**`RetTransparent` is reused rather than duplicated, and the reuse is a fact about the interpreter**:
the konts it lists are exactly the ones that reach `unwind`'s **catch-all** (or the `while` arm's `_`),
and that catch-all does not look at the jump. So a kont transparent to a `.retJ` is transparent to a
`.raiseJ` *for the same one line of `unwind`*. `unwind_raise_transparent` is `unwind_ret_transparent`'s
twin for that reason — stated as a twin rather than generalized over the jump, because the `while` arms
*do* inspect it (`.brkJ`/`.nxtJ`/`.redoJ` are special there) and the side condition excluding exactly
those is longer than the twin.

### The consecution case is the shortest jump case in the file

Three constructors, and `RaiseOk`'s shape picks the kont:

* `nil` — `unwind` answers `.uncaught exc m`, and **L216's `StepOk` clause is the hypothesis**. That
  commit's whole content, cashed in one line.
* `skip` — pop the kont, keep the jump; heap, frames and stack all unmoved, so only `frameKLabels`
  moves and `frameKLabels_transparent` moves it.
* `pop` — `RetOk.here`'s bookkeeping minus the type agreement and minus the `firstFrameK` target
  match: the stack has two entries (because the continuation has a `frameK`, so `m.stack.dropLast` is
  a cons), and `RaiseOk.pop` has already handed over the caller's environment.

### What is still owed

A raise being **caught**. A handler resumes with `.value v` and needs a `KontOk` below it, which this
arm does not carry — so `RaiseOk` grows a fourth constructor (*a handler typed at τ*) when the rescue
konts enter `KontOk`. That is where the census moves (24 → 22).

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`**; third ratchet
**24**. `Proof/`-only, so no `--check` diff is owed.

## L218 — `begin`'s three prerequisites, and the measured reason the rung is not the kont arms

Out of fragment **24 → 24**. Three pieces landed, all inert, all needed by `begin`/`rescue`; the rule
itself is **not** here and the last section says exactly what stopped it. `--check` byte-identical.

### 1. Environment narrowing, and the restriction it forces is the interesting part

```lean
def SubEnv (Γ Γ' : Env) : Prop := ∀ x τ, envGet? Γ x = some τ → envGet? Γ' x = some τ
theorem FrameConforms.narrow  -- one composition: the third clause is a ∀ over Γ's lookups
theorem FramesOk.narrowHead   -- the only position a region needs
```

A `begin`'s two exits leave **different environments** — the body may have assigned locals the handler
never sees — so the region can only be typed at an environment both paths guarantee.

And the entry environment is **not** it. Writing the `KontOk` arm is what showed why:

```ruby
x = 1
begin;  x = "s";  raise;  rescue;  x;  end     # handler typed at the entry env reads x : Integer
```

The body may *reassign* a binding before raising, so a handler typed at the region's entry environment
reads a stale type off a live frame. **The sound environment for a handler is a lower bound of every
intermediate environment the body passes through**, and the only such bound the fragment can name
without a dataflow analysis is `[]`. Both slice bodies are `… rescue Uncomparable; nil`, so `[]` costs
them nothing — but it is a restriction to write down, not an approximation to fix later.

### 2. `TypeAgree`'s chain clause loses its bound, and gains a size clause

L208 added `∀ k, k < h.objs.size → ancestors h' k = ancestors h k`. The bound was never needed: every
instance proves the unrestricted form already (`PlainGrow.ancestors_eq`, `ancestors_defineMethod`,
`IvarOnly.ancestors_eq`, `ancestors_congr` are all `∀ k`). Dropping it, plus a seventh clause
`h.objs.size ≤ h'.objs.size` — also free everywhere — is what makes this provable:

```lean
theorem isTypeError_congr (ha : TypeAgree h h') (hb : ∀ o, exc = .ref o → o < h.objs.size)
    (hne : ¬ isTypeError h exc) : ¬ isTypeError h' exc
```

`isA h exc k` is `k ∈ ancestors h (classOf h exc)`, so it is two rewrites — the value's dispatch class
and that class's chain. **The bound on `exc` is the one thing no clause supplies**: a `.ref` above the
old size reads back as the *default* object, which is not an exception, so a growing heap can turn
`¬ isTypeError` into `isTypeError` at such an id. Immediates need nothing — a `Boot` dispatch class is
heap-independent.

> **A relativized clause is worth re-reading when a new consumer arrives.** L208 wrote the bound in by
> analogy with the five clauses above it, which *do* need it (they are about `h.get o`). The chain
> clause never did.

### 3. What stopped the rule, and it is not what the pricing said

`slice-verdict.md` priced `begin` as "the rescue machinery, six kont arms". The kont arms were the
*easy* part — three `KontOk` constructors (`beginBodyK`, `rescMatchK`, `rescueK`), their
`heap_congr'`/`retOk`/`raiseOk` cases, `RetTransparent`/`RaiseTransparent` gaining the region konts
guarded on `node.ens`, and two of the three value-delivery consecution cases all went in and built.
Three findings came out of it, and the third is the blocker:

* **`RetTransparent` and `RaiseTransparent` had to split.** L217 reused one for both and the note gave
  a reason — both are the konts reaching `unwind`'s catch-all, which does not look at the jump. That
  reason expires here: `beginBodyK` is transparent to a `.retJ` and **not** to a `.raiseJ`. The two
  lists now differ in exactly that constructor.
* **`unwind`'s transparency lemmas needed an `∃ ec`.** `rescueK`'s exit restores the outer `$!`, so the
  machine it produces is not `{ m with kont := k }`. `Inv` reads no such field, so the honest statement
  is *the kont pops and nothing the invariant looks at moves* — one existential, one `obtain` at each
  of the two `skip` cases.
* **The blocker: `RaiseOk` needs a *table*, and `KontOk` threads tables.** A caught raise resumes with
  a value, so `CtlOk`'s raise arm has to carry a typed continuation — which means `RaiseOk`'s `caught`
  constructor carries `infer` premises, which means `RaiseOk` is indexed by `Decls`. But
  `KontOk.raiseOk` derives `RaiseOk` by induction over `KontOk`, and several `KontOk` constructors
  hand the continuation a **different** table (`seqCons`, `ifK`, `recvK`, `argsK` all thread `D → D'`).
  So the derived relation is at the *continuation's* table and the consumer needs it at the
  invariant's, with no lemma saying the two agree.

> **That is L200's problem, and L200 solved it** — `KontOk.retOk` composes with `infer_table_ret`,
> *the table is constant along a continuation chain*, available because `ctx.ret.isSome` forces
> `def`'s row-adding guard off. A raise has no analogous guard, so `begin` needs its own
> table-stability lemma (the natural guard is the region body's `defFree`, giving
> `infer_decls_stable`). **That is the next commit, and it is a lemma about `infer`, not about
> exceptions** — which is why no amount of work on the rescue machinery was going to reach it.

The rescue machinery is reverted rather than left half-built; this commit keeps only the three pieces
that stand on their own and that the rung needs regardless.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`**; third ratchet
**24**. `Types/Ty.lean` is touched, so the `--check` diff was run: byte-identical.

## L219 — every remaining body priced to a named theorem, and the `if` refusal diagnosed

Out of fragment **24 → 24**. No code; a measurement, and it is the one this initiative has been
missing: until now the remaining census was priced by *construct*, which is what L192's rule warns
against. Priced by **the theorem each one needs**, the board reads differently.

### The `if` refusal is an environment mismatch, and it is caused by desugaring temporaries

`Token.self.from` was the last `if` in the census and this file had it down as *"needs unification"*
(from L175's reading of `in_interval?`). It does not. Reproduced and bisected:

```ruby
return NULL_TOKEN if val.nil? || (val.respond_to?(:null?) && val.null?)   # -> out of fragment: if
return NULL_TOKEN if val.nil? || val.null?                                 # -> accept
val.respond_to?(:null?) && val.null?                                       # -> accept
```

`a || (b && c)` desugars to nested `if`s over three temporaries (`__dt_t1/2/3`), and the outer `if`'s
**else** arm assigns one the then arm does not. Minimal witness, and it is nothing to do with
unification or with `case`:

```ruby
if c then 1 else z = 2; z end     # -> out of fragment: if
if c then z = 1; z else z = 2; z end   # -> accept
```

`inferOpenIf` refuses when `Γt ≠ Γe` (`Types/OpenSelf.lean`), and that is the whole refusal.

**And relaxing it is not local.** The obvious fix — answer the two arms' *meet* and narrow with L218's
`FramesOk.narrowHead` — does not close: `applyKont`'s `ifK` evaluates the chosen branch against the
continuation `k` **directly**, so `CtlOk` needs `KontOk … ((c, Γbranch) :: Γs) … k` while `KontOk.ifK`
registered `k` at the meet. Weakening a `KontOk`'s environment index needs `infer` to be
*environment*-monotone with a **related** answer environment:

```lean
SubEnv Γ Γ' → infer D Γ e … = some (τ, Γ₁, D₁) →
  ∃ Γ₁', infer D Γ' e … = some (τ, Γ₁', D₁) ∧ SubEnv Γ₁ Γ₁'
```

which is `infer_mono`'s shape at `Env` instead of `Decls` — a 40-case induction with the template
already in `Proof/Static/Mono.lean`. Storing *two* continuations in `KontOk.ifK` (one per branch
environment) was tried on paper and pushes the same problem up: the `if`'s own continuation was
registered at one environment.

> **Two of the four one-body rungs were mispriced in the same direction**, and both by inheriting a
> reading from an earlier session instead of running the body. `if` is not unification; `hash` is not a
> `Ty` arm.

### The board, priced by theorem

| construct | bodies | the theorem it needs |
|---|---|---|
| `send-with-block` | 15 | the block subsystem. Typing one `xs.map { }` types the **prelude's** `Enumerable#map`, which is Ruby containing `yield`, `block_given?`, a nested block send and `Array#push`. Not decomposable into a cheap first rung |
| `splat` | 3 | **three** theorems: a signature match that survives unknown arity; multiple assignment; and a new `Inv` conjunct *class `Array` ⇒ `.arr` payload* (with a boot certificate and transports) for **one** body |
| `begin` | 2 | table stability along a `KontOk` chain — L200's `infer_table_ret` **without its guard** (`ctx.ret.isSome` is what made that one available). L218 has the measurement |
| `if` | 1 | `infer` environment-monotonicity (above) |
| `gvar` | 1 | a globals clause on `Inv`, ~50 call sites of threading |
| `next` | 1 | a loop-control channel in `CtlOk`, `.nxtJ`'s analogue of L200's `.retJ` |
| `hash` | 1 | `plainRecv` **excludes** a `.hsh` payload, so a hash literal's value has no type at all — L185's class-arm work again, not a `Ty` arm |

**Seven theorems, and no two of them share machinery.** That is the honest shape of `oof → 0`: it is
not a long tail of small rungs, it is seven independent pieces of which the largest is a subsystem.
Three of the seven (`begin`, `if`, and the array-element `splat`) now have their statement written
down, which is the difference between this entry and a status report.

### What is *not* the obstacle

Worth recording because two sessions have now looked for it: there is no construct here the approach
cannot decide. Every one of the seven has a stateable rule and a stateable consecution case; what they
cost is proof, not design. The nearest thing to a design problem is `hash`, where the *value* has no
type — and that is L185's problem, already solved once for class objects.

### Checks

No code changed. Third ratchet **24**; `--check` untouched.

## L220 — `next` attempted, and the finding is that `inferOpen.induct`'s fixed `ctx` is load-bearing

Out of fragment **24 → 24**. Reverted, and the reason is a constraint worth knowing before the next
four rules are designed.

### The design, which is right and which I still believe

`Version#<=>` is the census's only `next`, and its `next` is inside a **`while`**, not a block — so it
is L200's shape, not Wall 1's. The design fell out cleanly:

* `FrameCtx.inLoop : Bool`, set by `infer`'s `.while'` arm on the condition *and* body (`evalExpr`
  pushes a `whileCondK` for the condition too, so a `next` there has the same target);
* `KontOk`'s two loop constructors **switch the flag off** on the way down — above them the context is
  the flagged one, below them the enclosing one;
* `KontOk.frameK` requires the callee's `inLoop = false` (free: `user_dispatch` builds the callee's
  context from a literal whose field takes the default);
* those two together make *"the flag is on ⇒ a loop kont sits above the `frameK`"* a property of the
  **derivation**, which is exactly what `KontOk.nxtOk` needs to refute the `frameK` position — and
  refuting it is the whole obligation, because `unwind` answers `.unsupported` for a `.nxtJ` crossing a
  method boundary.

All of that built. `StackCtx` is invariant under the flag *by `rfl`* (`stackCtx_inLoop`) — its six
clauses read `cls`, `selfCls`, `ret`, `meth`, `params` and nothing else — and the eleven `Preservation`
sites it touched were mechanical.

### What stopped it

```lean
induction Γ, e, s using inferOpen.induct (D := D) (ctx := ctx)     -- ctx *fixed*
```

`inferOpen_mono`, `inferOpen_rets` and `inferOpen_factors` all take `ctx` as a **fixed** parameter of
the functional induction. That is sound only because **every recursive call in `inferOpen` passes `ctx`
unchanged** — and a loop flag is the first thing that does not.

> **`inferOpen.induct`'s fixed-`ctx` form is load-bearing, and it silently constrains the rule set: no
> rule may use a `FrameCtx`/`OCtx` field that varies *within* an activation until the three open-self
> inductions are generalized over `ctx`.** That is not a fact about `next`. It applies to `break`,
> `redo`, and to Wall 1's block frames — every one of which wants a context that changes partway
> through a body.

`inferOpen_mono` and `inferOpen_rets` generalize in four lines each (nothing in them knows anything
about `ctx`). **`inferOpen_factors` does not**: `hself : θ ctx.self = .cls ctx.cls` is the one thing it
knows, so generalizing `ctx` moves `hself` into the motive, and `revert hself` + `intro hself` in the
uniform block leaves twelve cases with no binder to introduce — the uniform block's `simp_all` list
*names* `hself`, so those twelve fail on an unknown identifier rather than on the mathematics.

That is a solvable problem and it is **not** solvable by trial and error, which is what I was doing:
the right move is to work out which twelve cases they are and why their motive is not the implication,
and that is a session's work on the most delicate proof in the project, for **one** body.

### The order this changes

`next`, `break` and `redo` should be done **together, after** a commit that generalizes `ctx` in the
three open-self inductions — not one at a time. The generalization is the rung; the three rules are
cheap once it lands. And Wall 1 needs it too, which moves it from "after the walls" to "before them".

### Checks

Reverted; `lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`**;
third ratchet **24**.

## L221 — `next`, second attempt: the flag belongs on `OState`, not `OCtx`, and L220's blocker dissolves

Out of fragment **24 → 24**. Reverted again, and this entry supersedes L220's conclusion: the
`ctx`-generalization L220 said was the prerequisite is **not needed**. What is left is smaller and
localized, and it is written down precisely.

### L220's blocker was self-inflicted

L220 put `inLoop` on `FrameCtx`/`OCtx`, which made it vary within an activation, which broke
`inferOpen.induct`'s fixed-`ctx` form, which forced `hself` into the motive. All true — and avoidable.

**`OState` is already an induction target.** Put the flag there and `ctx` stays fixed:

```lean
structure OState where
  st : Store := {}
  inLoop : Bool := false   -- L221
  …
-- and the motives become
(motive2 := fun Γ t els s => FactorsIf D θ stF retF ctx s.inLoop Γ t els (inferOpenIf … ctx s))
```

`Factors`/`FactorsIf`/`FactorsSeq`/`FactorsArgs` take the flag as a parameter and feed it to the
nominal context; `motive1` is *inferred* from the goal, so no `revert`, no implication in any motive,
and **`inferOpen_mono` and `inferOpen_rets` are untouched**. The nominal side keeps
`FrameCtx.inLoop` — `Mono.lean` already has `ctx` as an induction target, so a varying context is free
there.

> **When a rule needs a flag that varies within a body, put it where the induction already
> generalizes.** For `inferOpen` that is the *state*, not the context. L220 spent a session's worth of
> analysis concluding the opposite.

All of this built: the two structures, both `.while'` arms, `KontOk`'s loop constructors clearing the
flag, `KontOk.frameK`'s `cΓ.1.inLoop = false` premise, `stackCtx_inLoop`/`'` (both `rfl` — `StackCtx`
reads none of the five fields), the eleven `Preservation` sites, and a new
`inferOpen_inLoop` (*the flag is preserved*, `inferOpen_rets`' shape).

### What is left, and it is one thing

`inferOpen_factors`' uniform block does not close the `.while'` case. Both IHs are now at
`inLoop := true` **syntactically** (the body's sub-call re-states the flag rather than inheriting it,
precisely so that they are), and the goal is `infer`'s while arm at the same flag — so the mathematics
lines up. What does not is the *store bound*: the generic two-subexpression alternatives are keyed to
helpers (`storeLe_subSeq`, `rets_subSeq`) whose shapes assume the sub-call's state is the plain
threaded one, and it is now `{ s with inLoop := true }`. The fix is a `storeLe_subWhile`/`rets_subWhile`
pair and one alternative in the block — the same thing L175 and L193b each added once.

**And `inferOpen_inLoop` cannot be a `simp` lemma**, which is worth knowing before reaching for it: its
left-hand side is `s'.inLoop` with `s'` universally quantified, i.e. a bare variable, so `simp` will not
use it as a rewrite. Every place it is needed wants it applied by hand — which is why the body's
sub-call restates the flag instead.

### Two attempts, two designs, and the honest score

L220 (flag on the context) hit a motive problem and was reverted. L221 (flag on the state) dissolves
that problem and gets to a single missing helper pair in one tactic block. **The rung is not done and I
am not going to finish it by iterating blind on that block** — it is the most delicate proof in the
project and I have now perturbed it twice. What the next session needs is written above and is roughly
an afternoon: two store-bound helpers and one alternative.

### Checks

Reverted; `lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`**;
third ratchet **24**.

## L222 — `next`, third attempt: the flag must be an explicit parameter, and that is now measured

Out of fragment **24 → 24**. Reverted. Three designs across L220–L222; this names the fourth and says
why the first three fail, so the next session starts on the right one.

| design | where the flag lives | why it fails |
|---|---|---|
| L220 | `FrameCtx` / `OCtx` | varies within an activation, which breaks `inferOpen.induct`'s **fixed-`ctx`** form; generalizing `ctx` moves `hself` into the motive and twelve cases lose their binder |
| L221/L222 | `OState` | `s` *is* an induction target, so `ctx` stays fixed and the motives are clean — **but `Factors` then reads the flag off a state, and every multi-subexpression arm has its IHs at *different* states** |
| **the right one** | an explicit parameter of `inferOpen`/`inferOpenIf`/`inferOpenSeq`/`inferOpenArgs` | — |

### What the third attempt proved

Everything except one tactic block built: both structures, both `.while'` arms, `KontOk`'s loop
constructors clearing the flag, `KontOk.frameK`'s `cΓ.1.inLoop = false` premise, `stackCtx_inLoop`/`'`
(both `rfl`), the eleven `Preservation` sites, `inferOpen_inLoop`, and `Factors`' new parameter.

Then `inferOpen_factors` failed — and **not only at `.while'`**. Reading the trace the block already
emits (rather than guessing at `rename_i` arity, which is what the earlier attempts did) shows a
**send** case:

```
ih2 : … infer D (substEnv θ Γ) recv false { …, inLoop := s✝.inLoop } = some (t, …)
ih1 : (match … inferOpenArgs D Γ₁ (arg :: args) ctx s₁ … )      -- at s₁, not s
```

The receiver's IH is at the *input* state's flag and the arguments' at the *intermediate* state's.
`inferOpen_inLoop` says those are equal but **not syntactically** — and it cannot be a `simp` lemma
(its LHS is `s'.inLoop` with `s'` universally quantified, a bare variable). Restating the flag at each
sub-call, which is what fixed `.while'`, would mean doing it in forty places.

> **A derived index is not an index.** Reading the flag off a threaded state makes `Factors` mention a
> *different expression* at every nesting depth, and a uniform tactic block cannot absorb that. An
> induction needs its varying data as a **parameter**, not as a projection of another parameter.

### The fourth design

```lean
def inferOpen (D : Decls) (Γ : AEnv) (e : Expr) (ctx : OCtx) (il : Bool) (s : OState) : OResult
induction Γ, e, il, s using inferOpen.induct (D := D) (ctx := ctx)
  (motive2 := fun Γ t els il s => FactorsIf D θ stF retF ctx il Γ t els (inferOpenIf … il s))
```

Every IH then mentions the flag *as a variable*, `.while'` passes `true`, every other arm passes `il`
unchanged, and the uniform block sees the shape it sees today. `hself` stays a hypothesis (`ctx` is
still fixed), `inferOpen_mono`/`inferOpen_rets` need only their motive signatures, and
`inferOpen_inLoop` is not needed at all. ~40 mechanical edits in `Types/OpenSelf.lean` plus targets and
motives in three proofs, and no new mathematics.

### Method note, since it cost two of the three attempts

I iterated against build errors instead of reading the goal the block already prints.
`| (trace_state; fail)` has been in that `first` block since L175. Reading it first identified the real
defect in one build instead of five.

### Checks

Reverted; `lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`**;
third ratchet **24**.

## L223 — the `inLoop` channel, and the design L222 named is the one that works

Out of fragment **24 → 24**, `--check` byte-identical, `check-proofs.sh` axiom-clean. **This is the
commit L220, L221 and L222 were each trying to reach**, and it went in without a single failed goal
once the flag was put in the right place.

### The channel

| side | where the flag lives | why |
|---|---|---|
| nominal | `FrameCtx.inLoop : Bool` | `Mono.lean` already has `ctx` as an induction target, so a context field that varies within an activation is free there |
| open | an **explicit parameter** `il : Bool` of `inferOpen`/`inferOpenIf`/`inferOpenSeq`/`inferOpenArgs` | the three open-self inductions keep `ctx` **fixed** (so `hself` stays a hypothesis), and `il` joins the *targets* — so every IH mentions the flag as a **variable** |

`infer`'s `.while'` arm types the condition and body at `inLoop := true`; `inferOpen`'s passes `true`
to both sub-calls; every other arm passes `il` through unchanged; `openParams`' default expressions and
both `inferBody` entry points pass `false`. `KontOk`'s two loop constructors map the flagged context to
the enclosing one on the way down, and `KontOk.frameK` requires the **callee's** flag clear — together
making *"the flag is on ⇒ a loop kont sits above the `frameK`"* a property of the derivation, which is
what a `next` rule will need in order to *refute* the frameK position (`unwind` answers `.unsupported`
for a `.nxtJ` crossing a method boundary).

### What the three failed attempts bought

Nothing about the mathematics changed between them; what changed is where one `Bool` lives.

* **L220 — on `FrameCtx`/`OCtx`.** Varies within an activation ⇒ breaks `inferOpen.induct`'s fixed-`ctx`
  form ⇒ generalizing `ctx` moves `hself` into the motive ⇒ twelve cases lose their binder.
* **L221/L222 — on `OState`.** `s` *is* a target, so `ctx` stays fixed and the motives are clean — but
  `Factors` then reads the flag off a state, and **every** multi-subexpression arm has its IHs at
  different states. `inferOpen_inLoop` says they agree and cannot be a `simp` lemma (bare-variable LHS),
  so the equation would have to be applied by hand in forty places.
* **L223 — an explicit parameter.** Every IH mentions it as a variable. The uniform tactic block in
  `inferOpen_factors` needed **no new alternative at all**.

> **A derived index is not an index.** An induction needs its varying data as a parameter, not as a
> field of a fixed parameter and not as a projection of another target. Three sessions' worth of
> analysis reduces to that sentence.

### What it cost, itemized

Signatures of four functions and ~27 call sites in `Types/OpenSelf.lean`; `il` added to the targets and
motives of `inferOpen_mono`, `inferOpen_rets` and `inferOpen_factors`; an `il` binder on twelve helper
lemmas (`inferOpenIf_mono`, `storeLe_sub`, `rets_subArgs`, …) and their applications; `Factors` and its
three siblings gained the parameter; `stackCtx_inLoop`/`'` (both `rfl` — `StackCtx` reads none of the
five context fields); `KontOk`'s two loop constructors and `frameK`; eleven `Preservation` sites.
**No new mathematics, and no new tactic alternatives.**

### What is next

The channel is inert — nothing reads the flag. `next` is now: `RaiseOk`'s shape for `.nxtJ`
(`NxtTransparent`, an `NxtOk` relation whose `loop` constructor carries the loop's `LoopOk`), `CtlOk`'s
`.jump (.nxtJ v)` case, `KontOk.nxtOk` refuting the `frameK` position from `ctx.inLoop = true`, then
the two rules. `break` and `redo` follow from the same channel — `unwind`'s `whileCondK` arm answers all
three from one `match`.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`**; `--check`
byte-identical (56 / 1,169 / 0); third ratchet **24**.

## L224 — the channel carries the loop's *environment*, and that is the one way `next` costs more than `return`

Out of fragment **24 → 24**, `--check` byte-identical, axiom-clean. A one-type change to L223's
channel: `Bool` → `Option Env` (nominal) and `Option AEnv` (open).

### Why a flag is not enough

`return` and `next` look like the same rung and are not, and the difference is the *frame*:

* a `return` **pops** the activation, so `RetOk` owes nothing about the environment — whatever the
  body had assigned goes with the frame;
* a `next` **restarts the loop in the same frame**. `unwind`'s `whileCondK` arm re-enters the
  *condition*, which `infer`'s `.while'` arm typed at the loop's **entry** environment — while the
  `next` may fire part-way through the body, at a richer one.

So the rule owes `SubEnv Γloop Γcur` (L218's relation, now with its first consumer), and it can only
check that if it knows `Γloop`. Hence the channel carries the environment, not a flag:

```lean
inLoop : Option Env := none        -- FrameCtx
(il : Option AEnv)                 -- inferOpen & friends
```

`infer`'s and `inferOpen`'s `.while'` arms pass `some Γ`; `KontOk`'s loop constructors are indexed at
`{ ctx with inLoop := some Γ }` and hand the enclosing context down; `KontOk.frameK` requires the
callee's `inLoop = none`.

> **Two jumps with the same shape can have different obligations, and the discriminator is whether the
> jump crosses a frame.** `RetOk` and `RaiseOk` both cross one and neither mentions an environment;
> `NxtOk` will not cross one, and that is exactly why it must.

### One incidental improvement

The `while` push site in `step_ok` no longer names the context at all. `inv_push`'s `c` is determined
by unification from `hcnd`'s own type — `infer`'s `.while'` arm *names the loop's environment* in the
context it types the condition at — so `(c := …)` came out and with it a dependence on which of
`Γ`/`Γ₁`/`Γ₂` survived the case's `obtain ⟨rfl, rfl⟩`. That had been the previous build failure.

### What is left for `next`

Unchanged in shape from L223, plus the environment premise:

* `NxtTransparent` — the `KontOk`-admitted konts minus `frameK` and minus the two loop konts (which
  are the *terminators*, not transparent);
* `NxtOk`, two constructors: `loop` carrying the loop's `LoopOk`, `subTy .nilT τw`, the enclosing
  `KontOk`, **and `SubEnv Γloop Γcur`**; `skip` for the transparent konts. No `nil` and no `pop` — a
  `.nxtJ` at `[]` is `.stuck` and at a `frameK` is `.unsupported`, and both are refuted rather than
  handled (`ctx.inLoop = some _` against `frameK`'s `= none`);
* `CtlOk`'s `.jump (.nxtJ v)` case, `KontOk.nxtOk`, then the nominal and open rules.

`break` and `redo` come from the same channel — `unwind`'s `whileCondK` arm answers all three from one
`match` — and `break` additionally needs the loop's *result* type, which is `.nilT` by
`KontOk.whileCond`'s second premise.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`**; `--check`
byte-identical (56 / 1,169 / 0); third ratchet **24**.

## L225 — `next`'s transparency layer, and the finding: it hits `begin`'s wall, so the two share a fix

Out of fragment **24 → 24**. `NxtTransparent` and its three `unwind` lemmas are in and proved; `NxtOk`
is designed, written, and **withdrawn**, because it runs into the wall L218 measured for `begin`. That
those two blockers are the *same* blocker is the news.

### What landed

```lean
def NxtTransparent : Kont → Prop       -- RetTransparent minus the two loop konts
theorem unwind_nxt_transparent         -- pop the kont, keep the jump
theorem unwind_nxt_loopCond            -- pop the loop kont, push a fresh whileCondK, eval c
theorem unwind_nxt_loopBody            -- the same, from the body side
theorem frameKLabels_nxt_transparent
```

Three transparency lists now exist and the differences are all facts about `unwind`: `RetTransparent`
is the konts reaching the catch-all **plus** the loop konts (a `.retJ` passes through a loop);
`RaiseTransparent` is that minus `beginBodyK`; `NxtTransparent` is that minus the two **loop** konts,
which are a `next`'s *terminators*. `frameK` is in none of them.

### `NxtOk` is right and unprovable-from-`KontOk` today

The relation is `RetOk`'s third sibling with no `pop` and no `nil` — a `.nxtJ` at `[]` is `.stuck` and
at a `frameK` is `.unsupported`, and L224's `frameK` premise (`callee's inLoop = none`) is exactly what
**refutes** the second. Its two `loop` constructors carry `KontOk.whileCond`'s premises.

`KontOk.nxtOk` then breaks in two places, and the second is the wall:

1. **`KontOk.nil` needs an `inLoop = none` premise** — it has `ret = none` (L198) and nothing about
   loops, so the empty-continuation case cannot be refuted. Free to add, true at every construction
   site (the outermost continuation is not inside a loop).
2. **`NxtOk` is indexed by `Decls` and `KontOk` threads tables.** `LoopOk` needs a table, so `NxtOk`
   carries one; but `KontOk.seqCons`/`ifK`/`recvK`/`argsK` hand the continuation a *different* table,
   so the derived relation is at the chain's deepest table and `CtlOk` needs it at the invariant's.

> **That is exactly L218's blocker for `begin`, and the fix is one lemma for both**: the analogue of
> L200's `infer_table_ret` — *the table is constant along a continuation chain* — under a guard that
> makes it available. L200's guard was `ctx.ret.isSome`, available because `def`'s row branch requires
> `ctx.ret.isNone`. For loops the guard is `ctx.inLoop.isSome`, and making it available means adding
> `ctx.inLoop.isNone` to `def`'s row branch — free, because a `def` that adds a row inside a loop body
> makes the body table-unstable and `LoopOk` refuses it anyway.

So the two blocked rungs — `begin` (2 bodies) and `next` (1, with `break`/`redo` behind the same
channel) — are **one commit apart**, not two independent problems. That is worth more than either body.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`**; third ratchet
**24**. `Proof/`-only.

## L226 — `infer_table_loop`, and it is the shared unlock L225 named

Out of fragment **24 → 24**, `--check` byte-identical, axiom-clean. Two changes, and the second is a
copy of an existing proof with one word changed.

### The guard

```lean
if top = false ∧ name ≠ "initialize" ∧ reopenableClasses.contains ctx.cls ∧
    groundClassNames.contains ctx.cls = false ∧ defFree body = true ∧
    ctx.ret.isNone ∧ ctx.inLoop.isNone then          -- ← L226
```

L200 added `ctx.ret.isNone` so that *no arm grows the table at `top = false` inside a body that
declares a return type*. This is the same move at the other jump channel. **Free**, and for a reason
worth stating rather than assuming: a `def` that added a row inside a loop body would make the body
table-unstable, and `LoopOk` already refuses such a body — so the guard refuses no *loop* that used to
type. `--check` byte-identical confirms it, and the conjunct sits inside an existing `if`, so
`infer.induct`'s case numbering did not move (contrast L212, where a new *arm* shifted it by eleven).

### The lemma

`infer_table_loop` and its three siblings are `infer_table_ret`'s **verbatim** proof with
`ctx.ret.isSome` replaced by `ctx.inLoop.isSome`. Not paraphrased — literally the same uniform block,
the same `case88` for the `if`-with-else arm, the same eight alternatives.

> **That the proof transfers unchanged is the result, not a convenience.** It says the two jump
> channels are the same shape, and it is why one lemma unblocks both rungs: `begin` (L218) and `next`
> (L225) were each stuck on *"the relation is indexed by `Decls` and `KontOk` threads tables"*, and
> this is the answer for both.

### What each rung still needs on top of it

**`next`** (1 body, plus `break`/`redo` behind the same channel):
* `KontOk.nil` gains an `inLoop = none` premise — it has `ret = none` (L198) and nothing about loops,
  so the empty-continuation position cannot otherwise be refuted. Free at its construction sites;
* `NxtOk` (designed at L225 — two `loop` constructors carrying `KontOk.whileCond`'s premises, a `skip`,
  no `nil` and no `pop`) and `KontOk.nxtOk`, which now has its table-stability;
* `CtlOk`'s `.jump (.nxtJ _)` case — `∃ Γl, c.inLoop = some Γl ∧ SubEnv Γl Γ ∧ NxtOk …`, the `SubEnv`
  being L224's environment obligation and L218's relation;
* the rules. The nominal one must require **`top = false`**, which is how the consecution case gets
  `Γs ≠ []` and hence `infer_table_loop`'s second hypothesis — exactly how L200's `return` rule works.

**`begin`** (2 bodies): the L218 kont arms, now with `RaiseOk.caught` able to carry a table.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`**; `--check`
byte-identical (56 / 1,169 / 0); third ratchet **24**.

## L227 — `next`, the third jump channel, and a mispriced ratchet

Out of fragment **24 → 24**, `--check` byte-identical (56 / 1,169 / 0), axiom-clean. The rung landed
exactly as L226 designed it, in one pass and with no design attempts spent — and it moved the census
by **zero**, which is the more useful half of the entry.

### The rule, and its three guards

```lean
| .nxt none =>
  if top = false then
    match ctx.inLoop with
    | some Γl => if subEnvB Γl Γ then some (.nilT, Γ, D) else none
    | none => none
  else none
```

* **`ctx.inLoop`** is L220's channel. `none` means no enclosing loop, where `unwind` answers
  `.stuck "jump escaped the program"` — so the guard is the soundness argument, as `ctx.ret` is for
  `return`.
* **`subEnvB Γl Γ`** is the obligation **no other jump has**. A `next` restarts the loop *in the same
  activation*, so the locals the body assigned are still live when the condition re-runs, and the
  environment the condition was typed at has to admit the one the `next` fires in. `return` and
  `raise` both pop a frame and owe nothing here. First consumer of L218's `SubEnv`.
* **`top = false`** for L200's reason at the other channel: it is what makes `infer_table_loop` apply.
  Concretely it refuses a `next` in a **toplevel** `while`, where `class'` can still grow the table
  mid-loop.

The answer is `.nilT` for `.ret`'s reason: the machine jumps, so this continuation never sees a value.

### The proof side, in the order L226 predicted

`KontOk.nil` gained `inLoop = none` (`by simp` at both construction sites) — `NxtOk` with its two
`loop` constructors and a `skip`, no `nil` and no `pop`; `KontOk.nxtOk`, whose every threading case is
one `infer_table_loop` `subst` and then `.skip`; `CtlOk`'s `.jump (.nxtJ _)` arm with the four
components; the two consecution cases. The `frameK` position is **refuted**, by L224's premise, and
the `nil` one by the new premise — which is what makes a relation with no `pop` well-formed.

The open front end is `subAEnvB` — `subEnvB` at `ATy`, compared *syntactically* — plus
`subAEnvB_subst`, six lines: a syntactic match survives every `θ`, so the open check is strictly
stronger than the nominal one, which is all `Factors` needs.

> **The `inLoop` channel cost four design attempts (L220–L224) and the rule that uses it cost one
> pass.** Both halves are the lesson: the channel was the hard part, and it was hard because a derived
> index is not an index.

### And the ratchet did not move — the pricing was read off a stale table

`--sets`' singleton `{next}` is gone (35 blocked bodies → 34) and `Version#<=>` type-checks its
`next`. The **census is unchanged at 24**, verified by rebuilding the binary from `HEAD` and diffing
the label histogram rather than by argument:

```
before:  15 send-with-block   3 splat   2 begin   1 return-join   1 nilable-receiver   1 if   1 gvar
after :  15 send-with-block   3 splat   2 begin   1 return-join   1 nilable-receiver   1 if   1 gvar
```

`next` was never in the 24. `Version#<=>` is reported for an earlier missing **declaration**
(`::NULL_TOKEN`), so `inferOpen` never reached its `next` — which is exactly the `--sets`-vs-`--assn`
gap L213 wrote the warning about, and the warning was right there when I priced this rung at 1.

> **`slice-verdict.md`'s "Where the 24 are" block was L214's, and I read it as current.** Two labels
> in it (`next`, `hash`) had already been replaced by `return-join` and `nilable-receiver` in the
> sessions since. **A breakdown in a document is a measurement with a date on it; re-run it before
> pricing anything against it.** The one-line command is
> `--assn-dump | grep -o "out of fragment: [a-z-]*" | sort | uniq -c`, and it is now in `HANDOFF.md`.

So the remaining 24 are: **`send-with-block` 15** (Wall 1), **`splat` 3**, **`begin` 2**, and four
singletons — `return-join`, `nilable-receiver` (`&.` on a nilable receiver), `if`, `gvar`.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`** (29
theorems); `--check` byte-identical to L226; `--self-test` all agree, with four new `next` rows; third
ratchet **24**; fifth ratchet 34 blocked (was 35).

## L228 — `$x`, the sixth table, and the first `Inv` conjunct that is not about the heap

Out of fragment **24 → 23**, `--check` byte-identical (56 / 1,169 / 0), axiom-clean. The rung is
`ivars`' shape at a different storage, and that difference is the whole content: five tables have been
read against `DeclsOk` — a fact about objects, classes or chains — and this one is read against
`m.globals`, an association list on the *machine*. So `Inv` grew a conjunct.

### `GlobalsOk`, and why it is indexed the way it is

```lean
def GlobalsOk (D : Decls) (h : Heap) (gs : List (String × Value)) : Prop :=
  ∀ x p σ, plainGlobal x = true → gs.find? (·.1 == x) = some p →
    globalTy? D x = some σ → ValueTy h p.2 σ
```

Indexed by the **heap and the list**, not by the machine — `FramesOk`'s shape, for `FramesOk`'s
reason: every step that moves only the control or the continuation leaves both projections
`rfl`-equal, so the conjunct transports by handing the hypothesis over. Three lemmas carry the rest:
`GlobalsOk.read` (the rule's whole obligation), `.set` (the write's, and `HeapFacts`' existing
`find?_filter_ne` turned out to be exactly the list fact — it was written for the *method*-table
filter at L142), and `.congr` (one `ValueTy.congr`, which is what an allocating case owes).

**`plainGlobal` is a hypothesis of the conjunct, not a convenience.** `$!` is `currentExc`, `$~` is
the frame's `lastMatch`, and `$1`…`$9` are *computed* by `matchGlobal` from the match data — none of
them is in `m.globals`, so a declaration about them would be a claim about the wrong storage.
`Interp.getGlobal`'s three-way split *is* this predicate, which is why `isMatchView` moved down to
`Syntax.lean`: `Types/` cannot import `Interp/`, and a second copy of the test is exactly the drift
that function's own docstring was written to prevent.

### The threading, and the price of a new conjunct

`ConformsAt` gained `m'.globals = m.globals` — the sentence "nothing else in `Inv` reads the machine"
(L215) coming due. Free at both witnesses, and a real restriction on the next tabulated builtin,
which is the honest place for it. Then: five `inv_*` helpers, 20-odd construction sites, two
`initiation`s (vacuous at `Machine.init`, and *not* vacuous at `initiation_on`, where the list is
quantified — what discharges it there is that `declsOf` declares no global), and `InvA`'s fifth
carried half.

> **The `inv_*` helpers take the conjunct as a *defaulted* argument** — `(hgl : … := by assumption)`,
> elaborated in the caller's context. That is what kept a nine-site positional insertion out of five
> lemmas, and it fails loudly at a caller that lacks the fact rather than papering over it.

### Two lessons from the rules

**`match` on the guard, never `if`.** `simp only [infer]` unfolds an `ite` all the way to a
`Decidable.rec`, after which neither `simp` nor `rw` can use the guard's hypothesis. `infer_mono`'s
write case sat on that for three builds. A `match` on a `Bool` leaves a shape both `split` and the
functional induction handle.

**A named case beats an alternative when the guards are hypotheses.** `infer.induct` splits the
guards, so the goal has no `if` to `split` — and an alternative that half-matches leaves *unsolved
goals* rather than failing, which aborts `first` instead of falling through. The two gvar rules are
explicit `case87`/`case89`/`case90`/`case91` in `Mono.lean` for that reason.

**The table is read *after* the right-hand side** (`globalTy? D₁`), which is `.vasgn .ivar`'s shape
and not a style choice: the continuation `KontOk` types is at the table the rhs leaves, so the
declared type has to be the one *that* continuation can name.

### What moved, and what it did not buy

`Token#self.create` — `case val when /\A#{…}\z/o` — crosses from out-of-fragment to a **needed
declaration**, because the `/o` regex desugars to `$__dt_rxN ||= Regexp.new(…)` and the read is now a
rule. It reports `::Regexp`, not the global: `inferOpen` short-circuits at the first `.missing` and
the constant is read inside the same expression.

> **So the body still does not *type*, and would not even with the table populated** — the `||=`
> desugars to `if $g then $g else $g = …`, whose join is nilable, and the `===` send on a nilable
> receiver is `nilable-receiver`. That is the **flow-narrowing** rung (`&.` and `if x.nil?`), now the
> shared blocker of two of the remaining singletons. Measured before starting, per L227's correction.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`**; `--check`
byte-identical; `--self-test` all agree, with three new gvar rows and a third witness for the
`def-params-dflt` example (ivar → gvar → `retry`, one per widening); third ratchet **23**.

## L229 — `return-join`: a method's type is the join of its exits

Out of fragment **23 → 22**, and this one *type-checks* rather than crossing to a needed atom:
`certified-modulo-precondition (params open)` goes **5 → 6**. `--check` byte-identical, axiom-clean.

### The rule L201 got wrong, and the sentence that admitted it

```lean
-- L201, in inferBody:
if s.rets.all (fun a => subATy a τ) then .ok τ Γ' s else .outOfFragment "return-join"
```

with the comment *"joining them would need the union this fragment does not have."* It does not:
`joinTy` has answered `nil`-shaped joins since **L193**, and a bare `return` records exactly `nilT`.
So the check was refusing the one shape the machinery already handles, for a reason that stopped being
true eight commits later. The replacement is `joinRets`, a right fold of `joinATy` over the recorded
returns, and it is **strictly more permissive**: `subATy a τ` makes `joinATy a τ = some τ`.

`PkgVersion#<=>` is the body: `return if version_comparison.nil?` records `nilT`, the tail
`nonzero? || (revision <=> other.revision)` is `T.nilable(Integer)`, and the method's type is the
join. Sorbet's answer, arrived at from the machine's side.

### `UserConforms` widens, and nothing downstream had to

```lean
∃ Γ' r τb, infer D [] md.body false { … } = some (τb, Γ', D) ∧ subTy τb d.ret = true ∧ …
```

The equality was right while the reported type *was* the body's last expression. Once it is the join
of the exits, there is no reading of the pair as an equality — a body ending in `Integer` with a bare
`return` has type `Integer` and declares `T.nilable(Integer)`.

> **The `subTy` costs one `subTy_trans` at each of the two frame pushes, and nothing else** — because
> `CtlOk`'s eval clause has allowed the continuation to sit at a *wider* type than the expression's
> since L193. A widening that lands exactly where an existing subsumption was already waiting is the
> sign the earlier rung put it in the right place.

`def`'s own row is unaffected: it carries the body's own type, so its new conjunct is `subTy_refl`. A
*declared* signature (W8's `sig`) is the one that can be wider, which is what the clause is for.

### Two soundness lemmas, both three lines of composition

`joinRets_sub` — the join is above the body's answer and above every recorded return — is
`joinATy_subst` (the open join commutes with `θ`) composed with `joinTy_sub` (both sides are below a
nominal join), once per element. `inferBody_sound` and `inferBodyWith_sound` now answer
`∃ τ0, infer … = some (τ0, …) ∧ subTy τ0 (τ.subst θ)`, which is the same widening one layer down, and
the two `eg*_nominal` witnesses recover the old equality with `subTy_atomic`.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`**; `--check`
byte-identical (56 / 1,169 / 0); `--self-test` all agree; third ratchet **22**, `pacc` 6.

## L230 — the splat, and a design that had to be reverted twice to be right

Out of fragment **22 → 21**, `--check` byte-identical, axiom-clean. The rung is small; the *shape* of
it took three attempts, and the two failures are the transferable part.

### `plainRecv`'s sixth clause — an object of class `Array` holds an array

```lean
(if className h (h.get o).klass == "Array" then
   (match (h.get o).payload with | .arr _ => true | _ => false) else true)
```

The splat's step is `spreadA`, which answers `.ok` for an `.arr` payload and `.error` — hence
`.unsupported`, which `StepOk` **refuses** — for a `.str` or an `.int`. `valueTy?` reads the *class*,
and nothing in the invariant tied a class to a payload, so the rule needed a new fact.

> **It went into `plainRecv` rather than into `Inv`**, which is `plainRecv`'s own pattern for the
> **sixth** time (its docstring names the first five): *a side condition a later rung has to derive at
> the use site is cheaper in the judgement.* A sixth `Inv` conjunct would have cost a `heapOkB`
> clause, a `ConformsAt` clause and a transport at every allocating step — L228 paid exactly that bill
> for `GlobalsOk` and it is ~25 edits. A clause of `plainRecv` costs **two producers and two
> congruences**, because that is where `plainRecv` is already established and transported. It will be
> needed again by the first *mutating* `Array` row (`Array#push`, Wall 1's chain).

### `inferElems` — the fifth mutual function, after two rejected designs

**Attempt 1: an `infer` arm for `.splat`.** Unsound, and the reason is worth keeping: `CtlOk`'s eval
clause quantifies over expressions `infer` accepts, so the *invariant* could then sit at
`.eval (.splat e)` — where `evalExpr` answers `.unsupported "splat outside call/array position"`.
Every other position that stores a subexpression and `.eval`s it later (`.seq`'s tail, `if`'s
branches, a `while`'s body, an argument list, a `cpath` base) would have needed its own guard, and
`inferArgs` would have needed one for a second reason: **a splat spreads into many arguments, so
typing it as one argument of type `Array` makes every arity check downstream a lie.**

**Attempt 2: an `allowSplat` flag on `inferSeq`.** Sound, and it renumbered `infer.induct` twice —
`inferSeq`'s arms double, and every case after them moves. Reverted.

**Attempt 3, the one that landed: a fifth mutual function**, declared after `inferArgs`, so its cases
are *appended* and **no existing case number moves**. It answers `(Ty × Env × Decls)` with the type
always `.nilT` — the shape `inferSeq` has, which is what lets the three inductions' uniform blocks
treat its cases with the alternatives they already have.

> **`motive4` is `inferElems` and `motive5` is `inferArgs`** — the *mutual block's* order, not the
> file's. The two have the same signature, so a swapped assignment **type-checks** and only the IHs'
> shapes reveal it (`trace_state` on the `.array` case: its IH was about `inferArgs`). The same trap
> is in `inferOpen.induct`, and it cost a build each side.

### Two more things the proof found

**`defFree` needed a `.splat` arm** — the eighth walk into the trap `.array`/`.vasgn .ivar`/`.ret`/
`.cpath`/`.super'`/`.zsuper`/`.nxt` all have a comment about, and the **first one found by a proof
rather than by the writer**: `inferElems` threads the table through the operand, so the element
traversal's IH arrived with no `defFree` for it at all.

**`inv_continueArray`** — the array loop, stated once. `continueArray` now has three entry points
(the `.array` step, the `arrK` delivery, the `arrSplatK` delivery after the spread) and they are the
same two shapes, so the case that used to be inline became a lemma and the new one costs three lines.

### What moved, and the limit that is now visible

`PkgVersion#self.parse` — `_, v, r = *path.match(REGEX)`, which desugars to `[*…]` — crosses to a
needed declaration (`::Regexp`). `Vulnerability#identifiers` — `[id, *aliases].uniq` — does **not**:
`aliases` types to a type *variable*, and the open rule refuses a variable operand rather than
constraining it, for `cpath-base`'s reason (L205): the store's requirements are rows, and "is an
`Array`" is not a row. The census says so in its own vocabulary — the label is `splat-operand` — and
**that is the assertion language's next rung**, not the splat's.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`**; `--check`
byte-identical (56 / 1,169 / 0); `--self-test` all agree with three new splat rows; third ratchet
**21**; fifth ratchet 31 blocked (was 33), singletons `{hash}` and `{begin}`.

## L231 — the `if` environment join, attempted and reverted: what the wall actually is

**Out of fragment 21 → 21**, and this entry is the *negative* result. It was built, it type-checked
as far as `Preservation`, and then it hit the obligation L219 named — from a direction I had
convinced myself avoided it. Recording the attempt because the next session will otherwise repeat it.

### The design

`inferIf` refuses `Γt ≠ Γe`, which is what refuses every desugared `||`, `&&` and `&.`: each expands
to an `if` whose branches assign *different* temporaries. The proposed rule kept the old branch and
added a second:

```lean
if Γt = Γe ∧ Dt = De then (joinTy τt τe).map (fun τj => (τj, Γt, Dt))
else if subEnvB Γ Γt ∧ subEnvB Γ Γe ∧ Dt = De then (joinTy τt τe).map (fun τj => (τj, Γ, Dt))
else none
```

— both branches extend the incoming environment, so `Γ` itself is sound for the continuation. The
machine side was to be `CtlOk`'s eval clause carrying an **environment subsumption** beside its type
one:

```lean
∃ τ τ' Γ' Γ'' D', infer D Γ e Γs.isEmpty c = some (τ, Γ'', D') ∧ SubEnv Γ' Γ'' ∧ …
```

with `FramesOk.narrowHead` (L218) discharging conformance at each consumer. That much *worked*: the
rule, `infer_mono`, both table lemmas, the five `inv_*` helpers (defaulted `SubEnv` arguments, so no
call site moved), the frame-push case (narrow, *then* `FramesOk.push`).

### Where it dies

`KontOk`'s constructors compute their **tail's** environment from their conclusion's — `asgn`'s tail
is at `envSet Γ x τ`, `seqCons`' at the sequence's threaded env, `ifK`'s at the join's. Once the eval
clause admits `Γ' ⊊ Γ''`, every consecution case holds its incoming tail at `Γ'` and needs it at
`F Γ''` — so **every constructor would need its premise widened**, and widening a stored `infer`
equation from a narrower environment to a wider one *is* `infer` environment-monotonicity.

> **L219 priced this as "relaxing it needs `infer` environment-monotonicity" and was exactly right.**
> The eval-clause subsumption looks like it routes around that — it does not; it *relocates* the
> obligation from `inferIf` into all seventeen `KontOk` constructors. **A subsumption added to a
> judgement that other judgements *store* is not a weakening, it is a distribution.**

### What the monotonicity lemma has to say, for whoever writes it

```lean
infer D Γ e top ctx = some (τ, Γ', D') → Γ₂ ⊇ Γ (disjointly) → e assigns no name of Γ₂ \ Γ →
  infer D Γ₂ e top ctx = some (τ, Γ' ∪ (Γ₂ \ Γ), D')
```

The side condition is real and syntactic: `.vasgn` writes with `envSet`, whose *order* the `while`
and `if` equality checks can see. That is the shape of the rung — a `defFree`-style predicate over
the assigned names, and an induction with the same twelve-case block every other `infer` induction
has.

### Checks

Reverted to L230's tree: `lake build`, `lake build Metatheory` green, `check-proofs.sh` axiom-clean,
third ratchet **21**.

## L232 — `ValueTy _ _ .any` is now *true*, which is what `Ty.lean` already claimed

Out of fragment **21 → 21** — `Proof/`-only, so `--check` cannot move — and it is the prerequisite
two different rungs turned out to share.

### The claim that was not true

`Ty.lean`'s note on `joinTy` says, as the reason `.any` must never be *inferred*:

> `ValueTy h v .any` holds for *every* value, so `.any` in an inferred position would let the checker
> forget what it knows.

It did not hold for every value. `ValueTy` was `∃ σ, valueTy? h v = some σ ∧ subTy σ τ`, and
`valueTy?` answers `none` for a `Proc`, a `Hash`, and any `.ref` that is neither `plainRecv` nor
`classRecv` — so `ValueTy h ⟨hash⟩ .any` was **false**, and a *declared* `.any` parameter was
un-inhabitable rather than unconstrained. The definition now reads

```lean
subTy .any τ = true ∨ ∃ σ, valueTy? h v = some σ ∧ subTy σ τ = true
```

— phrased as `subTy .any τ` rather than `τ = .any` so that `ValueTy.weaken` stays one `subTy_trans`:
the new disjunct has to be closed upwards, and that is exactly what `subTy` *from* `.any` means.

### What it costs, and the shape of the cost

Four inversions are stated at an arbitrary `τ` and are **false at `.any`** — `valueTy_ref_inv`,
`valueTy_ref_lt`, `valueTy_shapes`, `valueTy_ref_not_ground`. Each gains one hypothesis,
`subTy .any τ = false`, and every caller discharges it by `simp [subTy]` (at a concrete `τ`) or by
`subTy_any_false ha hn` (where `subTy_atomic`'s two side conditions are already in scope). Sixteen
call sites, no proof restructured.

> **An inversion principle is only as strong as the definition it inverts** — `Locals.lean`'s own
> L142 lesson, applied to itself for the second time (L185's class arm was the first). Widening a
> judgement weakens every inversion of it by exactly the width added, and the hypothesis that
> restores each one is the *negation of the new case*.

### What needs it

* **Wall 1's block-send rung**: a block's parameter type has to be `.any` — an `Array`'s element
  type is not in `Ty` — and the block frame's `FrameConforms` then has to hold for an element that
  may be a `Hash`.
* **`begin`'s `rescue => e`**: the binding's type has to be `.any`, because `subTy` has no nominal
  subtyping and the raised value's exact class is a *descendant* of `StandardError`. With this, the
  binding costs the invariant nothing (`ValueTy.any`), and any *use* of `e` is a needed row on
  `.any` — which is the honest report.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`**;
`Proof/`-only, so no `--check` diff is owed (L148's borderline rule: the binary cannot move).

## L233 — `begin`'s rescue is gated on the *same* env fact as `if`, and that is the finding

Out of fragment **21 → 21**. The `begin`/`rescue` rung was designed to the point where the
`RaiseOk` refactor was half-written, and then it produced the same obligation L231 hit from the other
side. Two rungs, one gate — worth one entry rather than two false starts.

### What was designed, and what is right about it

The shape is the first cut §10 asks for: **one clause, no class list, no `else`, no `ensure`**, the
binding a local. `RaiseOk` gains the table, the heap, the context and the environment as indices
(a *propagating* raise needed none of them; a *handler's typing* needs all four) and a `caught`
constructor carrying the handler's `infer` equation at `envSet Γ x .any` — which is what L232 was
for, since `subTy` has no nominal subtyping and the raised value's class is a descendant.

**And one part is genuinely free.** The handler's *output* environment is wider than the begin's
answer (the desugarer's string interpolation binds `__dt_t1`/`__dt_t2` — measured on the target
body), and that costs nothing: a new kont constructor may relate its conclusion's environment to its
premise's however it likes, so `KontOk.rescueK`'s conclusion sits at the handler's output and its
tail at the begin's, with `FramesOk.narrowHead` at the delivery. **Narrowing across a kont you are
introducing is free; it is *widening* that is not.**

### Where it dies, and it is L231's wall from the other side

The raise's consecution case has `FramesOk` at the machine's *current* environment `Γcur` and needs
it at the handler's `envSet Γbegin x .any` — so it needs `SubEnv Γbegin Γcur`, i.e. **the begin's
environment is below the one in force where the raise happened**. That is *true* — environments only
grow within a frame — but **the invariant does not record it**, and it cannot be recovered from the
`KontOk` chain: each constructor relates its own conclusion's environment to its premise's, and the
composition runs the wrong way (`asgn`'s premise is *wider* than its conclusion, so walking down the
chain to the `beginBodyK` gives `Γbegin ⊆ Γdeep`, not `Γbegin ⊆ Γcur`).

> **So `if` (L231) and `begin` (L233) are one rung, not two** — and the cheap-looking form of it
> does not work, which is worth writing down before someone tries it.
>
> A `KontOk` clause saying *every constructor's premise environment extends its conclusion's* is
> true (a deeper kont receives its value later, so its environment has more bindings) and composes
> — **in the wrong direction**. Walking down to the `beginBodyK` it gives `Γcur ⊆ Γdeep` and the
> constructor gives `Γbegin ⊆ Γdeep`; neither orders `Γbegin` against `Γcur`, which is what the
> handler's conformance needs. Requiring the *body* to be environment-stable (`Γ₁ = Γ`, which the
> target body satisfies) makes the two equal **semantically**, and the derivation still cannot see
> it: `KontOk` records no connection between "this body assigns nothing" and "every kont in its
> chain is at `Γ`".
>
> What is left is **L231's lemma**: `infer` environment-monotonicity, and with it a `KontOk`
> *widening* — the direction that is not free. Its assign-free special case is much smaller than the
> general one (`asgnFree e → infer D Γ e … = some (τ, Γ, D') → SubEnv Γ Γ₂ → infer D Γ₂ e … = some
> (τ, Γ₂, D')`, no `envSet` reordering to reason about) and covers both rungs' pending programs,
> because what a continuation stores above a frame boundary is the *rest of a method body*.

### Checks

Reverted to L232's tree: `lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean; third
ratchet **21**.

## L234 — `infer_env_mono`, the gate L231 and L233 both stopped at

Out of fragment **21 → 21** — `Proof/`-only plus one predicate — and it is the lemma the two reverted
rungs turned out to share. Axiom-clean, `sorry`-free.

```lean
theorem infer_env_mono : ∀ D Γ e top ctx, asgnFree e = true → ∀ τ Γ' D₀,
    infer D Γ e top ctx = some (τ, Γ', D₀) →
      Γ' = Γ ∧ ∀ Γ₂, SubEnv Γ Γ₂ → infer D Γ₂ e top ctx = some (τ, Γ₂, D₀)
```

### `asgnFree` refuses **two** constructors, and the second one is the finding

`.vasgn .lvar` is the obvious one — it is the only arm that extends the environment, so without it
the answer *is* the argument. `.while'` is the one the first draft did not have and could not do
without: the loop's rule types its body at `{ctx with inLoop := some Γ}`, so widening the environment
widens the **context** too, and the induction hypothesis is fixed at the narrow one. There is no way
to patch that inside the induction; the arm has to leave the fragment of the lemma.

> **A `next` stays in**, and the contrast is the useful part: it *reads* `ctx.inLoop` but never sets
> it, and its guard `subEnvB Γl Γ` survives widening by one transitivity (`case94` — the only case
> in the proof that does anything with `SubEnv` beyond passing it along). **Reading the environment
> is free; putting it into the context is not.**

### The proof is four named cases and one uniform block

The block closes everything that does not read the environment — which is every arm but the local
read — in one `refine ⟨?_, fun Γ₂ hs => ?_⟩ <;> simp_all … <;> done`. The named ones are `if`
(condition then join), the local read, `next`, and the `if`-with-else join; `def` gets its own
alternative because its guards are five deep and its body is typed at `[]`.

Two mechanical lessons, both already in this file and both re-paid here:
* **`split at h`, not `rw [if_pos …]`** — `simp only [infer]` unfolds an `ite` to a `Decidable.rec`
  past the point a hypothesis can be used (L228).
* **An alternative that leaves goals *succeeds*** and aborts `first`. The generic alternative had to
  end in `done` before the four specific ones could ever run — three builds lost to that, and it is
  the same trap as L230's.

And one new one, worth its own line:

> **An inline `match` in an induction *motive* is elaborated with the local context generalized
> into it.** `motive2`'s `match elsa with | some x => asgnFree x | none => true` came out as
> `match elsa, ih1, hasg, h with …`, which does not match the term the arm computes. The fix is a
> named function (`asgnFreeOpt`) — a motive should mention no anonymous `match`.

### What it unblocks, and what is still owed

With this, a `KontOk` **widening** is stateable: a continuation whose stored expressions are
`asgnFree` types at any wider environment, which is what `if`'s branches (L231) and `begin`'s handler
(L233) both need. That lemma plus the two rules is the next rung, and it is now a *proof* rather than
a design question.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean; `#print axioms
infer_env_mono` = `propext + Classical.choice + Quot.sound`. `--check` unowed (`Proof/` plus a
predicate no rule reads).

## L235 — the four mutual forms of `infer_env_mono`, and what they do *not* reach

Out of fragment **21 → 21**, `Proof/`-only, axiom-clean. `inferSeq_env_mono`,
`inferArgs_env_mono`, `inferElems_env_mono` (list inductions on top of L234) and
`inferIf_env_mono` (two cases). Together they are what a `KontOk` widening would consume, since every
constructor stores an equation in one of those five functions.

### And here is the part to read before writing that widening

**`begin` does not need it, and `if` needs more than it.**

* **`begin`** needs one fact and it is not a widening: `SubEnv Γbegin Γcur`, *the environment the
  begin was entered at is below the one in force where the raise happened*. Composing the `KontOk`
  chain gives the wrong pair (L233). Restricting the *body* to be assign-free would make every kont
  between the raise and the `beginBodyK` sit at the same environment — and then `Γcur = Γbegin`
  outright — but that restriction has to be *a hypothesis of `KontOk.raiseOk`*, and the
  raise-producing consecution cases have no way to supply it.
* **`if`** needs the widening at continuations that **do** assign: `t1 = a; if c … end; t2 = b` stores
  `t2 = b` in the `seqK` above the `ifK`, so the assign-free special case does not apply. The general
  form needs `Γ'' = Γ' ++ δ` (a *structural* conclusion, not `SubEnv`), because `inferIf`'s guard is
  an **equality** of environments and only a structural description makes it survive widening — and
  that in turn needs `δ`'s names disjoint from the expression's assigned ones, which is exactly the
  side condition L231 wrote down and this special case was chosen to avoid.

> **So the rung is: `Inv` has to record how environments evolve within an activation.** Not a lemma
> about `infer` — a clause. Two candidate shapes, and the next session should price both before
> writing either: (a) `KontOk` carries, per constructor, that its premise environment is its
> conclusion's *extended by a disjoint δ*, which makes the chain composable in both directions; or
> (b) `Inv` carries a single per-frame "environment so far" and the `KontOk` envs are all suffixes of
> it. (b) is the one that would also give `begin` its fact for free.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean; third ratchet **21**.

## L236 — the environment slack, and the `if` rung it buys (oof 21 → 20)

Out of fragment **21 → 20**; the `if` singleton is gone. `--check` byte-identical
(56 / 1,169 / 0 over the 1,304 cached ASTs, `diff` empty), axiom-clean, `--self-test` all agree with
**three new rows** — two gains and, pinned in the same place, one loss.

### The rung, and why L235's plan was the wrong one

L235 said the `if` environment join needed `Inv` to record how environments evolve. It does not. What
it needs is **slack at the continuation**, and the reason L231–L235 kept failing to find it is that
every attempt tried to *derive* the slack where it is used:

> **There is no `KontOk` monotonicity lemma.** `KontOk.seqCons` stores `inferSeq D Γ (e :: es) = …`,
> so re-indexing a stored continuation at a *different* environment would need `infer_env_mono`
> (L234) on statements that are not `asgnFree` — and `x = 1; x` is exactly such a statement. The
> slack has to be recorded where the continuation is **built**, not derived where it is delivered.

So all 18 `KontOk` constructors (and `NxtOk`'s two loop arms) grew one premise:

```lean
  | seqCons {… Γk} :
      inferSeq D Γ (e :: es) Γs.isEmpty c = some (τ', Γ', D') → subTy τ' τw = true →
      KontOk D' h ((c, Γk) :: Γs) τw k →                       -- the tail, at its own env
      (hsu : SubEnv Γk Γ' := by first | exact SubEnv.refl _ | assumption) →
      KontOk D h ((c, Γ) :: Γs) τ (.seqK (e :: es) :: k)
```

and both halves of `CtlOk` gained the matching existential. Three decisions made the edit cheap
rather than a 43-site rewrite, and they are the reusable part:

1. **The premise is last in the telescope and an `optParam`.** Inductive constructors *do* accept
   default values in Lean 4 (measured, not assumed), so every existing construction site elaborates
   unchanged: `refl` where the tail sits at the computed environment, `assumption` where the
   enclosing case has already destructured a slack of its own.
2. **`Γk` is the last implicit binder**, so `@ctor` case patterns needed one `_` appended rather
   than a reordering — 16 patterns, mechanically.
3. **On the value side the slack is consumed once**, at the top of the delivery block:
   `have hfs := FramesOk.narrowHead hsuE hfs` (L218's lemma, now with a second consumer) moves the
   *runtime* conformance down to the environment the kont was registered at, and all 16 arms then
   run at their own environment with no per-arm reconciliation. Three arms that build their `Inv`
   by hand rather than through an `inv_*` helper needed their env spelled as `Γk`; that is the whole
   diff on that side.

### The rule, and the shape constraint the *open* pass imposes on it

```lean
if subEnvB Γ Γt ∧ subEnvB Γ Γe ∧ Dt = De then (joinTy τt τe).map (fun τj => (τj, Γ, Dt)) else none
```

Two containments where this was `Γt = Γe`, and the answer is the **entry** environment. The `ifK`
delivery then reconciles by `SubEnv.trans hsu (subEnvB_sound hsub1)` — one line, and it is the only
construction site in `Preservation.lean` that passes anything but `SubEnv.refl`.

> **The answer had to be a function of `(Γ, Γt, Γe)` that commutes with `substEnv θ`, and that is
> what killed the first two designs.** A rule that *chose* between answers by a shape test
> (`if Γt = Γe then Γt else Γ`) is unimplementable across the two front ends: two `ATy`
> environments can differ and still substitute equal, so the open pass would answer one environment
> and the nominal pass a different one, and `inferOpen_factors` states an *equality* of answers.
> Same argument kills a key-and-type environment meet. `Γ` commutes trivially, so `Γ` it is.

**And `subEnvB` had to change** (`Γ.all fun e => envGet? Γ' e.1 == envGet? Γ e.1`, each entry's
*lookup* rather than its payload). An `Env` is an association list, so `[(x, Int), (x, String)]` is
a legal value whose second entry is dead — and payload comparison makes such an environment fail
`subEnvB Γ Γ`, which `infer_env_mono` cannot afford: its conclusion instantiates the guard at an
arbitrary wider environment. The lookup form is reflexive by construction (`subEnvB_refl`) and
proves the same `SubEnv`. `subAEnvB` moved with it, and `subAEnvB_subst` got shorter.

### The price, pinned rather than described

`if c then x = 1 else x = 2 end; x` **was** accepted (both branches answered the same environment,
which the old rule then answered) and now is not: the answer environment is the entry one, so a
local bound in *both* branches is invisible after the `if`. It is `--self-test` row 3 of the new
three. `--check` did not move — no bootstraptest program exercises it — and the census gained a
body, so the trade is net positive, but the fix is a real rung: a **typed environment meet** (at
each shared key, the *join* of the two types), which commutes with substitution because keys do and
because `joinATy_subst` already exists. The store threading at each join is why it is a rung and not
a line.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean, tier 0 / slice difftest,
`--check` diff empty against L230's baseline, third ratchet **20**, `--self-test` all agree.

## L237 — the splat operand's *requirement*, and the store field that was already there (oof 20 → 19)

Out of fragment **20 → 19**; `splat-operand` is gone and `Vulnerability#identifiers`
(`[id, *aliases].uniq`) now reports a **needed declaration** — `Array ~ uniq : () → _` — which is the
clean side of the line. `--check` byte-identical, axiom-clean, `--self-test` all agree.

### The rung is four lines of rule and no new machinery

`[id, *aliases]` where `aliases` is still the type variable `α` was refused (`"splat-operand"`)
because the nominal `inferElems` matches the operand's type against `Ty.cls "Array"`. The open pass
already has the atom for saying *make it so*: `Store.eqs`, added at L206 for the join —
"`θ α` must be this type", a requirement rather than an inference, checked by `satStoreB` and chosen
by the untrusted solver.

```lean
      | .ok (.var α) Γ₁ s₁ =>
        inferOpenElems D Γ₁ rest ctx il { s₁ with st := s₁.st.addEq α (.nom (.cls "Array")) }
```

An *equality* rather than a bound (`α ⊒ Array`) is both what the assertion language can say and
enough: the nominal rule wants the operand to **be** `Array`.

The proof cost is three lemmas and two tactic-block options:

* `storeLe_subElemsEq` / `eq_of_addEq_subElems` — the store bridge across the new `addEq`, and the
  requirement's discharge (`mem_addEq` → `StoreLe.eqs` → `SatStore`);
* `inferOpen_mono` and `inferOpen_rets` each gain the `var` arm explicitly (the store *grows* here,
  which outside a join was previously only true of `requireRow`);
* the factoring theorem's elems alternative splits into two options — the `addEq` shape and the plain
  one.

### Two tactic-engineering facts, because they cost the session more than the rung did

1. **A `rw` whose argument fails to elaborate is a *logged* error, not a backtrackable failure.** So
   `first | rw [f h] | rw [g h]` does **not** try `g` when `f h` is ill-typed — it aborts the whole
   block. The fix is to name the term first (`have hb := by first | exact f h | exact g h`), because
   an `exact` inside a `have` *does* backtrack. The same applies to an unsolvable placeholder in a
   `have … : T := by …` type, which is why `eq_of_addEq_subElems` is a lemma: the tactic block cannot
   name `α`, and `have hEq : θ _ = Ty.cls "Array"` leaves a placeholder that aborts rather than fails.
2. **An alternative of an outer `first` has to succeed on *all* of an `all_goals`' goals.** The
   variable-operand shape therefore had to become an *inner* option of the existing elems
   alternative, not a new alternative of the outer chain — as a new alternative it failed on the
   sibling shapes and never got tried on its own.

### What this does not pin

The change is on the **open** side only, so `--self-test` (which runs `--check`, the nominal pass)
cannot cover it. The census is the evidence, and the `Array ~ uniq` atom is the readable half of it.

### Checks

`lake build Metatheory`, `check-proofs.sh` axiom-clean, `--check` diff empty against L236, third
ratchet **19**, `--self-test` all agree.

## L239 — `TypeAgree`'s eighth clause and `ValueTy`'s array arm (oof 19 → 19, inert by construction)

Two commits, both inert (`--check` byte-identical, census **19**, axiom-clean), and together they
are the *relation* `Ty.arrayOf` exists for.

### The clause first, because it is the one that could have been false

Every clause of `TypeAgree` before this one is about a value's **class** — all of them functions of
`classOf`/`className`/`classPayload?` — and an `arrayOf` claim is about the object's **contents**.
So `ValueTy.congr` at the new arm is not merely unproved without a new clause, it is **false**: a
heap-writing step could replace an array's elements and the claim would not survive it. Correctly.

Stated as *unchanged* rather than *still conforms*, which is stronger than the transport needs and
is what every producer proves outright — nothing in the fragment writes an array payload
(`Array#<<` has no row, so `entry_dispatch` never reaches one). The producers cost one line each,
and the interesting one is `defineMethod`: it rewrites the payload of the **class** object, and a
`.arr` payload is not a `.cls` one, so either the ids differ (`get_defineMethod_ne`) or
`defineMethod` is the identity — the same case split `plainRecv_defineMethod` makes.

### The arm, and its four decisions

```lean
  ∨ (∃ σ o xs, subTy (.arrayOf σ) τ = true ∧ v = .ref o ∧ o < h.objs.size ∧
      (h.get o).payload = .arr xs ∧
      ∀ v' ∈ xs, ∃ σ', valueTy? h v' = some σ' ∧ subTy σ' σ = true)
```

* **relational, not computed** — `valueTy?` would have to recurse through the heap, and a Ruby
  array can contain itself (`a = []; a << a`);
* **up-closed** (`subTy (.arrayOf σ) τ`, not `τ = .arrayOf σ`) so `ValueTy.weaken` stays one
  `subTy_trans`: an array does satisfy `nilable (arrayOf σ)`;
* **one level of `valueTy?` inlined** rather than a recursive `ValueTy` call, which keeps the
  definition non-recursive and every `rcases` in the file computing. The cost is nesting —
  `arrayOf (arrayOf String)` is uninhabited, and so is `Array[Hash]`, the latter because
  `plainRecv` excludes a `.hsh` payload (a gap already on the board);
* **the bound is a conjunct**, because `h.get` is total: an out-of-bounds id reads back as the
  default object, so the payload equation alone would not place `o` in the heap — and clause 8 is
  relativized to the old bounds.

`ValueTy.congr` split its exact-type half out as `valueTy?_congr`, because the array arm needs it
once per element as well as once for the array.

### The ripple, and why it is not a tax

Six lemmas grew a *"and not an array type"* side condition (`valueTy_ref_inv`, `ValueTy.atomic`,
`valueTy_shapes`, `valueTy_ref_lt`, `valueTy_ref_not_ground`, `valueTy_tyClass`, and through them
`EntryOk.resolves`/`entry_dispatch`). **`sigOf_atomic` supplies it for free** — the same fact that
supplies `.any` and nilable: `tyClassNames` is `[]` at the arm, so a *row's existence* refutes it.
Every dispatch caller therefore passes `(by simp)` or reads the third conjunct.

> **The day `arrayOf` starts dispatching, `sigOf_atomic`'s third conjunct is where the bill lands.**
> That is the honest place for it, and it is the first item of the chain in `HANDOFF.md`.

### Checks

`lake build Metatheory`, `check-proofs.sh` axiom-clean, `--check` diff empty across both commits,
census **19**, `--self-test` all agree. No machine file changed, so the difftest is unowed.

## L240 — the exact-`Array` conjunct, and why dispatch is not the next commit (oof 19 → 19)

One line of definition landed; a whole sub-rung was attempted and **reverted**. Both are worth
recording, and the reverted one is the useful half.

### What landed

`ValueTy`'s array clause gained `valueTy? h v = some (.cls "Array")`. It is not redundant: the
payload equation alone admits an instance of a **subclass** of `Array` — payload-core subclassing is
in the model — and such a value's `valueTy?` names the subclass. An `arrayOf` is an *exact* `Array`,
which is the honest reading of an invariant element type. `--check` byte-identical, axiom-clean.

### What was attempted: `tyClassNames (.arrayOf _) = ["Array"]`

Everything on the *receiver* side worked, and cheaply:

* `DeclsOk_addRow`'s new `c ≠ "Array"` is discharged at its only caller by
  `"Array" ∉ reopenableClasses` — a `def` in the fragment cannot target `Array`;
* `tableOk_declsOk` gets a real arm (one `simp`: `baseDecls` has rows on `Integer` only);
* `sigOf_atomic` gives up the third conjunct L239 added to it, exactly as L239 predicted;
* **`valueTy_tyClass` is provable at the arm** — `TyClass` at `.arrayOf` asks for
  `className (classOf v) = "Array"`, and the exact-`Array` conjunct above is what supplies it;
* **`valueTy_shapes` is provable without a side condition**, by casing on the *disjunct* rather
  than on the value: every disjunct pins the value's shape, and the array clause's conjunct makes it
  a plain receiver. (`valueTy_ref_inv` still needs the condition — *its* conclusion is about the
  nominal type and is false at an `arrayOf`.)

### What stopped it, and it is the report rather than the machine

`mem_declAtoms_iff` says `declAtoms D` is exactly the graph of `declFor D`, and its **backward**
direction is what makes `⟦declAssn D⟧ → DeclsOk D` — the direction a certificate is read in.
`declTys` is a **finite** list; element types are not. So with dispatch on,
`declFor D (.arrayOf e) n = some d` is an atom the enumeration cannot contain and the biconditional
is **false**.

Weakening it to `τ ∈ declTys D → …` moves the obligation to the consumer, which then has to derive
`DeclsOk` at an `arrayOf` receiver from the `.cls "Array"` atom. That transfer is free for a
*builtin* entry — `TyClass h (.arrayOf e) k` and `TyClass h (.cls "Array") k` are the same
proposition, definitionally — and **false for a user entry**, because `UserEntryOk` pins
`τr = .cls c`.

> **So the first bill of dispatch is widening `UserEntryOk` to admit the parameterised type**, not
> `DeclsOk_addRow`. Its shape, `user_dispatch`, the `def` case's construction, and `DeclsOk_addRow`'s
> `hτ` step. That is the next commit of this rung, and it is a *witness-language* change rather than
> a type-language one — which is why it is worth its own entry rather than being folded into a
> "turn dispatch on" commit.

### Checks

`lake build Metatheory`, `check-proofs.sh` axiom-clean, `--check` diff empty, census **19**.

## L241 — `UserKey`: the user witness stops pinning `τr = .cls c` (oof 19 → 19, inert)

*Entry written at L242 from the commit message; the commit itself (`ca3b4e4`) shipped without one,
which is a §4 norm miss worth naming rather than quietly fixing.*

`UserEntryOk`'s first conjunct was the equation `τr = .cls c`, and that equation is what breaks
`mem_declAtoms_iff`'s certificate reading the moment `arrayOf` dispatches: `declTys` is finite and
element types are not, so `DeclsOk` at an `arrayOf` receiver has to be **derivable** from the
`.cls "Array"` atom — free for a builtin entry (`TyClass` at the two types is the same proposition,
definitionally) and refused by the equation for a user one.

```lean
def UserKey (τr : Ty) (c : String) : Prop :=
  τr = .cls c ∨ (∃ e, τr = .arrayOf e) ∧ c = "Array"
```

Two shapes and no more. Deliberately **not** `tyClassNames τr = [c]`, which would also admit the
ground arms — a user row on `Integer` is what `hground` exists to forbid.

## L242 — the block signature enters the declaration table, and it is unreadable on purpose

Out of fragment **19 → 19**. `--check` byte-identical (56 / 1,169 / 0), `check-proofs.sh`
axiom-clean, `--self-test` all agree. The first rung of Wall 1, and it is an **inert prerequisite**
in L238's sense: it adds the vocabulary a block-send rule needs and arranges that *nothing* can read
it until that rule exists.

### What landed

```lean
structure BlockSig where
  params : List Ty := []
  ret : Ty

structure MethodDecl where
  params : List Ty
  ret : Ty
  blk : Option BlockSig := none          -- L242
```

A **defaulted** field, so all ~130 existing row literals elaborate unchanged and `Sig := MethodDecl`
carries it into the assertion language for free.

`BlockSig` is a separate structure rather than a recursive `MethodDecl`, and the reason is what the
two describe. A `MethodDecl` is a claim about a **method-table entry** — something `ResolvesAt` finds
and `ConformsAt`/`UserConforms` discharge. A `BlockSig` is a claim about a call the **callee** makes,
so the obligation runs the other way: the caller owes a body that answers `ret` when handed values of
`params`, and the callee owes to call it that way. Nesting would suggest a block may take a block,
which no rule will admit and `reifyBlock` gives no shape to.

### The three places that make it inert, and each one names its own bill

1. **`sigOf` refuses a block-taking row.** This is the load-bearing one. Every blockless rule in the
   fragment reads its receiver's declaration through `sigOf`, so without the filter a row
   `Array#each { |x| … } → Array` would let a *blockless* `xs.each` type — a claim about a different
   step entirely (`tryIterator` answers `none` without a block, and the call is an Enumerator the
   model gates). Refusing once, here, is what makes the field unreadable by anything that has not
   been taught about it; a block-send rule will read `declFor` directly.
2. **`ConformsAt` pins `d.blk = none`.** `Builtins.run bid recv args m` is a *blockless* call — the
   signature has no `Proc` slot — so a row declaring a block would be a claim about a step that
   conjunction does not describe. **The bill:** a block-taking row is witnessed by a **third arm of
   `EntryOk`** — the native iterator (`tryIterator` → `startIter`, which pushes an activation frame,
   a `frameK`, an `iterK` and a block frame) — not by widening this one.
3. **`UserConforms` pins `d.blk = none`.** The body below it is checked by `infer` at a context with
   no block channel at all (`FrameCtx` has no `blk` field), so a row declaring a block would oblige
   a `yield` rule that does not exist.

### The price, measured

`sigOf_declFor` now concludes `declFor … = some { params, ret, blk := none }` — the filter means a
rule that has read a signature has *shown* the row is blockless, and this is where that fact reaches
`DeclsOk`. Five destructuring sites gained a `-` or an `rfl` (`entry_dispatch`, `super_dispatch`,
`entryOk_int`, `entryOk_int_nullary`, `DeclsOk_defineMethod`), plus `userConforms_of_inferBody`,
which takes the new pin as a hypothesis. That is the whole diff on the proof side.

### Why the *arrayOf* dispatch rung is not on Wall 1's critical path after all

HANDOFF's chain put `Ty.arrayOf` + dispatch + element-polymorphic rows *before* the block rule,
because L237 measured that a block parameter typed `.any` makes essentially no slice body **accept**
(`tyClassNames .any = []`, so no send can use the parameter as a receiver). That is right about
*accept* and wrong about *oof*: `declFor D .any m = none` is a **missing declaration**, which the
census counts in the `needed:` column, not in `oof`. So for the metric this initiative ratchets, the
type-language rung is optional and the *rule* is the whole cost. L238–L240 are still paid and still
what an accepting `select` will need; they are no longer the gate.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`**, `--check`
diff empty against L241's capture, `--self-test` all agree, third ratchet **19**. No machine file
touched, so no difftest is owed.

## L243 — a block frame becomes expressible: `FrameConforms` follows one hop of the chain

Out of fragment **19 → 19**, `Proof/`-only, `--check` byte-identical, axiom-clean. Wall 1's
**frame-side** prerequisite, and it is one clause moving from one predicate to another.

### The clause that made a block frame inexpressible

```lean
def FrameConforms (h : Heap) (Γ : Env) (f : Frame) : Prop :=
  f.captured = none ∧ …                          -- before
```

`callClosure` builds a block activation with `captured := some cl.captured`, precisely so that
free variables in the block body reach the defining method's locals. So the old first clause did
not merely under-describe a block frame — it **refused to admit one exists**, and no amount of
work on `KontOk` or `EntryOk` was going to get past it.

### What replaced it, and the measurement that fixed the depth

```lean
def localOfIn (frames : Array Frame) (f : Frame) (x : String) : Value :=
  match f.locals.find? (·.1 == x) with
  | some (_, v) => v
  | none => match f.captured with
    | some p => localOf (frames.getD p default) x
    | none => .nil

def ShallowChain (frames : Array Frame) (fid : FrameId) : Prop :=
  ∀ p, (frames.getD fid default).captured = some p →
    p < fid ∧ (frames.getD p default).captured = none

def FrameConforms (h : Heap) (frames : Array Frame) (Γ : Env) (fid : FrameId) : Prop :=
  ShallowChain frames fid ∧ (h.classPayload? _).isSome ∧
  ∀ x τ, envGet? Γ x = some τ → ValueTy h (localOfIn frames _ x) τ
```

**One hop, not a walk, and it is a measurement rather than a simplification.** The only frame the
fragment will give a chain is a block frame; a block nested inside a block is two hops and
`infer`'s block rule will refuse one, because a block body is checked at a context whose block
channel is already open. `Machine.getLocal.go`'s fuel is `m.frames.size + 1`, so `getLocal_curIn`
unfolds it exactly **twice** and the third unfolding never has to happen — a `Nat`-fuelled walk
would have put a fuel argument in every lemma below for nothing.

**`FrameConforms` is now indexed by the frame *id*, not the frame.** That is not cosmetic:
`ShallowChain` has to say `p < fid`, and a bare `Frame` cannot name its own id. The ordering is
what `frames_congr` needs (below), and it is true of the machine for a reason worth stating — a
closure captures a frame that existed when the closure was *created*, and the block frame is
pushed when it is *called*.

### Where the empty chain went, and that is the bill

Into `StackCtx`, as a ninth clause: *the activation has no captured chain*. **A move, not a new
fact** — it is still true of every frame the fragment builds, and something has to supply
`FrameOk` to the `setLocal` lemmas.

> **A *read* through the chain is one lookup; a *write* is not.** `Machine.setLocal` walks the
> chain and mutates the frame that already binds the name — which for a block frame may be the
> **enclosing** activation, invalidating *that* frame's entry in `FramesOk` at a type its own
> environment still claims. `x = 1` inside a block is therefore the one construct a block frame
> cannot host, and this is where the block rung pays: the `StackCtx` clause becomes conditional on
> a `FrameCtx` block channel, and `infer`'s `.vasgn .lvar` arm grows the guard that reads it.
>
> An earlier draft of this commit added that channel (`FrameCtx.inBlock`) up front and pinned it
> `false`. Withdrawn: with no rule setting it, the field is a `DecidableEq`/`Repr` cost and a
> `StackCtx` implication whose hypothesis is never anything but `rfl`. The **unconditional** clause
> says exactly as much and the block rung will weaken it in the same commit that needs it.

### `frames_congr` had to be restated over a *bound*, and that is the other measurement

```lean
theorem FramesOk.frames_congr (hbs : bound ≤ b.size)
    (heq : ∀ g, g < bound → b.getD g default = a.getD g default) :
  FramesOk hp a fids Γs → (∀ g ∈ fids, g < bound) → FramesOk hp b fids Γs
```

It used to quantify the agreement over `fids`. A block frame's `localOfIn` reads a frame that is
**not on the segment being walked**, so agreement over the stack list is no longer enough — and
`ShallowChain`'s `p < fid` is exactly what makes a bound above every stacked id also above every id
any of them reads. Its one caller (`FramesOk.setLocal`) supplies `bound := fid`, which is what
`set!`-at-the-head misses anyway.

### The rest of the diff

`FramesOk.frameOk` now takes `(curFrame m).captured = none`, supplied by `StackCtx.curCaptured`;
`FramesOk.frameShallow` is the version that survives a block frame and is what `FramesOk.localsOk`
uses. `StackCtx_congr` gained a ninth agreement (`captured`, a field `setLocal` does not write) and
`StackCtx.heap_congr` one projection. Three frame pushes in `Preservation.lean` and both
`initiation`s supply the new clause by `rfl` on a frame literal.

**What is *not* blocked by the predicates any more**: a block frame's conformance, its shallow
chain, and the read through it. What is still owed for Wall 1: `KontOk` arms for `blkFrameK`/
`iterK`, `StackCtx` for the iterator activation, the third `EntryOk` arm (the native iterator), and
the rule.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`**, `--check`
diff empty against L242's capture, third ratchet **19**. No machine file touched.

## L244 — Wall 1's machine step, in five reductions, and a measured correction to the plan

Out of fragment **19 → 19**, `Proof/`-only (a new off-import file plus the axiom audit), so
no `--check` diff is owed and none was needed. Axiom-clean.

### The measurement first, because it reprices the wall

`HANDOFF.md` split Wall 1 into *the native-iterator rung (20 of the 30-odd sends) and the
prelude-Enumerable rung behind it*, as **two populations** — `each`/`map`/`inject`/`max_by`
native, `select`/`any?`/`find`/`filter_map`/… written in Ruby in the prelude.

Traced, one program per method (`[1,2].m { |x| x }`, `rubycore --trace`, frame kinds and kont
labels collected):

| method | frames / konts seen |
|---|---|
| `each`, `map`, `each_with_index`, `inject`, `max_by` | one `method` frame, `iterate` konts, block frames |
| `select`, `any?`, `find`, `filter_map`, `flat_map`, `partition`, `sort_by`, `reject`, `all?`, `to_h`, `zip` | **two** `method` frames, `iterate` konts, block frames |
| `tap` | one `method` frame, one block frame, **no** `iterate` |

> **They are not two populations.** A prelude `Enumerable#select` is a Ruby body that calls
> `each`, so its trace has its own activation *on top of* a `startIter` activation. The native
> iterator is the **floor** of fifteen of the sixteen block methods the slice uses, and the
> prelude rung sits on it. So this is not one of two alternatives to pick between — it is the
> shared prerequisite, and nothing about a block send can be proved before it.

### The five reductions, all proved

`RubyCore/Proof/Static/Iter.lean`. A block send is one `stepFn` step that ends with the
**block body in `ctl`**, two frames pushed and three konts pushed; these are the pieces it
factors into.

| lemma | what it says |
|---|---|
| `reifyBlock_eq` | the `Proc` allocation, with the closure named (`blockClosure`) |
| `finishSend_lit` | a literal block reaches `invoke` as that `Proc` — **at any name that is not `lambda`/`proc`/`new`**, so the sixteen iterator rows share one lemma |
| `invoke_iter_each` | …and dispatch is `startIter`, given three side conditions |
| `startIter_eq` | a frame push and a `frameK` — the activation a `break` returns from |
| `iterStep_cons` / `iterStep_nil` | one turn (an `iterK`, then the block call) / the empty loop |
| `callClosure_req1` | the block call for a `\|x\|` block: the block frame, `captured := some cl.captured` |

They compose: the file's `example` runs the whole chain by five rewrites and concludes
*the step lands in `.eval body`*, with no case split and no `Builtins.run`.

**`invoke_iter_each`'s three hypotheses are the specification of a block row**, and each is a
real obligation rather than bookkeeping:

1. **`lookup m.heap (.ref o) "each" = none`** — `tryIterator` is reached only from
   `dispatchMiss`. A program that reopens `Array` and defines `each` takes a different step
   entirely, so this is the clause a block row's `EntryOk` arm carries and the one a
   `defineMethod` has to preserve. It is the *opposite* polarity from both existing arms,
   which say the name **resolves**.
2. **the receiver's payload is an `Array`** — `plainRecv`'s sixth clause (L230) is the bridge
   from `.cls "Array"`, so a typed receiver supplies it.
3. **the block value is a `Proc` over `cl`** — `reifyBlock_eq` supplies it at the allocation.

**`callClosure_req1`'s three are all syntactic**, which is what lets `infer`'s rule check them:
a single required positional, no block-local names, not a lambda. Each turns off one branch —
`classifySimple` succeeds, the auto-splat test needs `required ≥ 2`, `arityOk` is vacuous off a
lambda.

`invoke_iter_each` is stated at `each` and not at an abstract iterator name on purpose:
`tryIterator`'s `match` is a sixteen-way split with a different `IterKind`, element list and
seed per arm, so there is no shared statement. Each declared row pays for its own copy, and the
copy's shape is this one.

### What is still owed for a block send to type

* `KontOk` arms for `blkFrameK` and `iterK`, and `StackCtx`/`FramesOk` entries for the
  iterator activation and the block frame — the predicates are ready as of L243;
* the third `EntryOk` arm, whose content is `invoke_iter_each`'s hypotheses plus the loop's
  own conformance (every element is yielded at the block's parameter type);
* the `infer`/`inferOpen` rule and `inferOpen_factors`' case.

### Checks

`lake build`, `lake build Metatheory` (60 jobs), `check-proofs.sh` axiom-clean with **0
`sorryAx`** — the five lemmas are added to its audit list, because an off-target file with no
consumer is exactly how `Proof/` rotted for 24 commits (L119). Third ratchet **19**.

## L245 — the frame/kont correspondence admits a block frame, and `KontOk` gains its pop

Out of fragment **19 → 19**. `--check` byte-identical, axiom-clean, `Proof/`-only. Wall 1's
**invariant** side, first half.

### The clause that breaks the moment a block frame exists

`Inv`'s L199 conjunct is `frameKLabels m.kont = m.stack.dropLast`, and `frameKLabels` counts only
`.frameK`. `callClosure` pushes a block activation under a **`blkFrameK`** — `applyKont`'s two
arms are the *same* `stack.tail` + `.value v` and only the label's constructor differs — so the
stack gains an entry the labels do not, and the equation is false.

> **The obvious fix is wrong, and that is the finding.** Teaching `frameKLabels` to count
> `blkFrameK` makes `firstFrameK` answer a block frame's id — and `frameKLabels`/`firstFrameK`
> are the **return-target** correspondence: `doReturn` targets `returnTarget m`, which walks
> *past* a block frame to the closure's `home`, and `unwind`'s `frameK fid` case compares the two.
> A `firstFrameK` that answered the block would make that comparison wrong.
>
> The previous HANDOFF entry said "a second function, leaving `frameKLabels` alone", and stopped
> there — which is half the answer: with the `Inv` clause moved, the *bridge* from it to
> `firstFrameK` is gone, and both of `firstFrameK_of_labels`' callers depended on it.

### What replaced the bridge, and it is free

`framePopLabels` (both popping konts) carries the `Inv` clause. The bridge runs through **`RetOk`**
instead of through the labels:

```lean
theorem firstFrameK_of_retOk : RetOk D h Γs σ k → framePopLabels k = fid :: rest →
  firstFrameK k = some fid
```

`RetOk` is built from `skip` at **transparent** konts and `here` at a `frameK`, and no transparent
kont pops. So along a chain that carries a `.retJ` at all, the first popping kont *is* the `frameK`
the jump lands at — which is exactly the fact the two callers needed and could previously only get
by conflating the two notions. `firstFrameK_of_labels` is kept, struck in place: still true, no
longer supplied by the invariant.

### `KontOk.blkFrameK`, and the two premises that make the case analyses close

```lean
  | blkFrameK {…} : cΓ.1.ret = none → cΓ.1.inLoop = none → subTy τ τ' = true →
      KontOk D h (cΓ' :: Γs) τ' k → KontOk D h (cΓ :: cΓ' :: Γs) τ (.blkFrameK … :: k)
```

`frameK`'s shape at a different constructor. The two context premises are not tidiness — they are
what `KontOk.retOk` and `KontOk.nxtOk` discharge their new cases with (`absurd`), and each is the
honest reading of the machine: a `return` inside a block targets the **home method** and a `next`
ends the **block invocation** (`blkFrameK`'s own `.nxtJ` arm), so neither channel is the enclosing
one. §10's "first cut" restated on the invariant side — a block body containing `return` or `next`
is out of the fragment, and it shows up here as a derivation that does not exist rather than as a
rule that refuses.

`RaiseOk` gains **`popBlk`**, `pop`'s twin: `unwind`'s `blkFrameK` arm sends a `.raiseJ` on with
`stack := m.stack.tail`, which is `frameK`'s arm at a different label. One new `unwind` lemma
(`unwind_raise_blkFrameK`, two tactics) and one new consecution arm, a copy of `pop`'s.

The value-delivery case in `Preservation.lean` is `frameK`'s with the type agreement read off the
constructor's own `subTy` instead of off the caller's context. Nothing about the block is used:
the block frame is described by `FramesOk` (L243) and popping it is `hfs.tail`.

### What is still owed for a block send

`KontOk.iterK` — the substantial one, because at its delivery `iterStep` either calls the block
again (a new block frame **and** a new `iterK`) or finishes, so the constructor carries everything
the next call needs; `StackCtx`/`FramesOk` at the two pushes; the third `EntryOk` arm; the rule.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`**,
`--check` diff empty, third ratchet **19**.

## L246 — `KontOk.iterK`'s missing fact, priced before writing it (no code)

Out of fragment **19 → 19**. No code: the next constructor was designed to the point where its
one unprovable premise became clear, and that premise redesigns an `Inv` clause rather than adding
one. Written down before the attempt, following L219/L235's precedent — *a rung priced to the fact
it needs is cheaper than a rung reverted*.

### What `KontOk.iterK` has to say

At its delivery the in-flight value is the block's result for the current element, the block frame
has already popped, and the current activation is the **iterator's**. `iterStep` then either calls
the block again — a *new* block frame and a *new* `iterK` — or delivers `retVal` to the `frameK`
below. So the constructor has to carry everything the next call needs:

1. the block body's typing, `infer D Γb cl.body false <block ctx> = some (τb, _, D)` with
   `subTy τb bs.ret`;
2. every remaining element's type, `∀ a ∈ rest, ValuesTy h a bs.params` — heap-indexed, so it
   rides through `heap_congr'` like every other `ValueTy` premise;
3. `Γb = bs-parameters ++ Γcap`, where `Γcap` is the environment the block's **captured** frame
   conforms at.

(1) and (2) are ordinary `KontOk` premises. (3) is the one that does not fit.

### Why (3) does not fit, stated exactly

`FrameConforms` at the *new* block frame (L243) reads `localOfIn`, which is the frame's own locals
and then **one hop to `frames[cl.captured]`**. So the delivery has to know that
`frames[cl.captured]` conforms at `Γcap` — and `FramesOk` supplies exactly that **for frames on
the stack, positionally**. At the `iterK` delivery the stack is `ifid :: capfid :: …`, and `Γcap`
is the second entry of `KontOk`'s own `Γs` index. So the *only* missing fact is

> `cl.captured = m.stack.tail.headD 0`

— a frame **id**, and `KontOk` is indexed by environments and contexts, not by ids. It cannot say
this, and no amount of premise-adding will let it.

### The three candidate homes, priced

1. **Index `KontOk` by the stack** (`Γs : List (FrameCtx × Env × FrameId)`). Correct and
   mechanical, and it is ~200 sites across five files — every constructor pattern, every
   `@ctor` case in `Preservation.lean`, `CtlOk`, `Inv`. Rejected on cost, not on shape.
2. **A new `Inv` conjunct about the head of the kont.** Cheap to state and **wrong**: while the
   block body runs the head is a `blkFrameK` and the `iterK` is second, so a head-only clause is
   not preserved by the step that needs it.
3. **Redesign L199's clause as a relation over the two lists.** This is the one.

```lean
-- sketch
def KontFramesOk (frames : Array Frame) : List Kont → List FrameId → Prop
  -- walks kont and stack together; at a `frameK fid` the stack's head is `fid`;
  -- at a `blkFrameK fid _ _ cl _` the head is `fid` **and** `cl.captured` is the
  -- next id below; at an `iterK cl brk …` the head is `brk` and `cl.captured` is
  -- the next id below; a non-popping kont advances the kont list only.
```

It **subsumes** `framePopLabels m.kont = m.stack.dropLast` — that equation is its projection — so
it is a replacement rather than an addition, and the ~20 sites that carry `hks` today are the same
~20 sites that would carry this. What it buys beyond the equation is exactly the missing fact, and
it buys it for `blkFrameK` too, which the block frame's own `FrameConforms` needs at the *push*.

> **The reason it is a relation and not another projection**: the closure's captured id is not a
> function of the kont alone (two `iterK`s in a chain may capture different frames), and it is not
> a function of the stack alone. It is a *pairing*, which is what L199's clause already is — the
> equation was the pairing's degenerate case, back when the only popping kont was `frameK` and the
> only thing to say about it was its label.

### What this does *not* change

The five machine reductions (L244) and `KontOk.blkFrameK` (L245) are unaffected — neither mentions
a captured frame. The rung after it is unchanged too: the third `EntryOk` arm, then the rule.

## L247 — L246's premise (3) dissolves: the captured environment does not have to be *precise*

Out of fragment **19 → 19**. No code. L246 concluded that `KontOk.iterK`'s third premise forces a
redesign of L199's clause into a kont/stack relation. **That conclusion is withdrawn**, and the
thing that dissolves it is a fact this file already recorded for exactly this purpose.

### The move

L246 wanted `Γb = bs-parameters ++ Γcap`, where `Γcap` is the environment the captured frame
conforms at — and getting `Γcap` is what needs the frame *id*, which `KontOk` cannot name. But
`Γcap` does not have to be precise:

> **L232 made `ValueTy h v .any` *true for every value*, and said so in as many words: "what needs
> it: the block-send rung (Wall 1)."** So type the enclosing locals at **`.any`**:
>
> ```
> Γb = params(bs.params) ++ blockLocals(nilT) ++ Γcap.map (fun (x, _) => (x, Ty.any))
> ```
>
> The block frame's `FrameConforms` at that environment needs **nothing about the captured
> frame's environment** — every outer name's obligation is `ValueTy h _ .any`, which holds. What
> is still needed of `cl.captured` is only `ShallowChain`: `cl.captured < bfid` and
> `(frames[cl.captured]).captured = none`. Two facts, no environment, no positional pairing.

**And it costs nothing on the census**, which is the measurement that decides it: a send on an
`.any` receiver is `declFor D .any m = none`, a **missing declaration**, so a block body that calls
a method on an outer local reports `needed:` exactly as one that calls a method on its parameter
does. Precision would change the `accept` column, which is the `arrayOf` chain's business
(correction 1 in `homebrew/HANDOFF.md`), not this rung's.

### So L246's redesign is not needed, and what is needed instead is small

```lean
/-- Every closure the continuation mentions captures a frame that exists and is not
    itself a block frame. -/
def ClosuresOk (m : Machine) : Prop   -- a ∀ over `m.kont`'s `iterK`/`blkFrameK` arms
```

A list-wide predicate over the kont, not a positional pairing: state it, and preserving it is
three observations — frames only grow, `setLocal` writes `locals` and not `captured`, and the one
step that pushes such a kont pushes it with `cl.captured = m.stack.headD 0`, whose non-blockness is
`StackCtx`'s L243 clause.

### The other half of the correction, and it is the one that costs bodies

L243 concluded that `x = 1` inside a block cannot be admitted, because `setLocal` walks the chain
and may mutate the **enclosing** activation. True — **for a name the enclosing frame binds.** Ruby
scoping says a name *first assigned inside the block* is block-local, and the model implements
exactly that: the exporter puts such names in the `.block` node's second component, `callClosure`
pre-binds them in the block frame's own `locals`, and `setLocal.owner` therefore stops at the block
frame. Measured on the slice — `Vulnerability#fix_available?`'s block declares
`["version_matched", "ranges", "semver_ranges", …]`, `Identify#self.tag`'s declares `["match"]`.

So the admissible guard is not `asgnFree body`; it is **every assigned name is a parameter or a
block-local**, which is syntactic and checkable from the `.block` node the rule already has. What
it costs on the proof side is one lemma: `setLocal_owner_start`'s twin under
`(curFrame m).locals.any (·.1 == x)` instead of `captured = none`, and `FramesOk.setLocal` taking
that hypothesis. **That matters for the census**: `Identify#self.tag`'s block opens with
`match = url.match(pattern)`, so an `asgnFree` guard would have left it out of fragment and this
one does not.

### Revised order for the rung

1. `ClosuresOk` (above), inert;
2. `KontOk.iterK`, with `Γb` built as above — premises (1) and (2) of L246 unchanged, (3) gone;
3. `StackCtx`/`FramesOk` at the two pushes, and `setLocal` at a block-local;
4. the third `EntryOk` arm;
5. the rule, its `inferOpen` mirror, and `inferOpen_factors`' case.

## L248 — `ClosuresOk`: the whole frame-side price of a block call, and it is one conjunct

Out of fragment **19 → 19**. `--check` byte-identical, axiom-clean, `Proof/`-only. L247's item 1,
built.

```lean
def KontClosure : Kont → Option Closure
  | .iterK cl _ _ _ _ _ _ => some cl
  | .blkFrameK _ _ _ cl _ => some cl
  | _ => none

def ClosuresOk (m : Machine) : Prop :=
  ∀ κ ∈ m.kont, ∀ cl, KontClosure κ = some cl →
    cl.captured < m.frames.size ∧ (m.frames.getD cl.captured default).captured = none
```

`Inv`'s seventh conjunct, beside `BottomObj` and the frame/kont correspondence — a **machine**
fact, mentioning no table and no type, so it sits outside the existential as those two do. `InvA`
mirrors it.

### Why it is this small

Because the captured frame's **environment** is not among the things a block call needs. L232 made
`ValueTy h v .any` true of every value *for this rung*, so the block body is typed with the
enclosing locals at `.any` and the block frame's `FrameConforms` obligation at an outer name is
`ValueTy h _ .any`. What is left is `ShallowChain`'s two conjuncts, and this is them. See L247 for
the pricing that got here from L246's kont/stack relation.

### Four transport lemmas, and every consecution case is one of them

`ClosuresOk.transport` is the general shape — the frames may have grown or had a `locals`
rewritten, and the continuation may have gained konts that carry no closure or lost some from the
front. `konts` (frames unmoved), `pushFrame` (a `frameK` and a frame) and `ctl` are its instances.
`setLocal_captured`/`setLocal_frames_size` are the two facts the assignment case needs: `setLocal`
writes `locals`, so every frame's `captured` is where it was.

### Two placement findings, and the second is the one that cost builds

1. **`hcloTail`, once for the whole proof.** Almost every consecution case steps at
   `{ m with kont := k }` for the tail the kont's head was peeled off, so a defaulted
   `by assumption` cannot find `ClosuresOk m`. One `have` above the `rcases` on `m.ctl` bridges all
   ~30 of them, and the equation naming the head is what each case already has under `hK`.
2. **A defaulted parameter still consumes a positional argument.** L228's note says `hgl` is
   *last* for exactly this reason; inserting `hclo` before it silently rebound every caller's
   `hglob`. Second time this has been load-bearing, so it is now stated twice: the five `inv_*`
   helpers take `hclo` **after** `hsuE`, and `inv_push`'s `hkc` (the pushed kont carries no
   closure) after that.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`**,
`--check` diff empty against L245's capture, third ratchet **19**.

## L249 — L247's dissolution was **partial**: `StackCtx` still wants the pairing, and here is what buys it out

Out of fragment **19 → 19**. No code. `KontOk.iterK` was designed a second time, and the premise
L247 removed from `FrameConforms` turned out to reappear one predicate over. Written down rather
than discovered mid-refactor, for L246's reason.

### The correction

L247 said the block frame's conformance needs nothing about the captured frame because the
enclosing locals are typed `.any`. That is **true of `FrameConforms` and false of `StackCtx`.**
Both are positional over `m.stack`, so the block frame gets an entry in *each*, and `StackCtx`'s
per-entry clauses read fields `callClosure` copies from the captured frame:

| `StackCtx` clause | reads | supplied by |
|---|---|---|
| 1. `(classPayload? defmod).isSome` | `capF.defmod` | name-free |
| 2. `className h defmod = c.cls` | `capF.defmod` **and the context's name** | **needs the pairing** |
| 3. `defVisOfDef = .pub` | `capF.defVis` | name-free |
| 4. `selfCls` (self's type, chain) | `capF.self` **and the context's name** | vacuous at `selfCls = none` |
| 5. `Object ∈ cref` | `capF.cref` | name-free |
| 6. `meth` | the context | vacuous at `meth = none` |
| 7. `captured = none` (L243) | — | **false at a block frame; already the block rung's** |

So four of the seven are free at `.any`-typed enclosing locals; **clause 2 is not**, because it
compares a heap-derived *name* against a name the static context carries, and only the pairing
(`cl.captured` is stack position *k*) connects them.

### What buys it out, and it is cheaper than indexing `KontOk` by the stack

1. **`ClosuresOk` grows the three name-free clauses** about `frames[cl.captured]` —
   `(classPayload? defmod).isSome`, `Object ∈ cref`, `defVisOfDef = .pub`. All true of the caller
   (its own `StackCtx` entry says so at the push), all preserved by the same three observations
   L248's version is.
2. **`StackCtx`'s clause 2 is guarded on `kind ≠ .block`.** Sound because nothing reads it at a
   block frame: its consumers are the `def` row's key and the `class'` rule, and a block body may
   contain neither (`defFree`). Every construction site already proves the equation, so the guard
   is one `intro _` there; the *consumers* are what pay, and they pay one `kind` fact each — which
   `StackCtx`'s own clause 6 or the frame literal already gives at each of them.
3. **The block's context sets `selfCls := none` and `meth := none`** (as well as `ret := none` and
   `inLoop := none`, which L245 already requires), which makes clauses 4 and 6 vacuous.

### What (3) costs on the census, measured rather than assumed

`selfCls = none` refuses an implicit-self send inside a block — so a block that calls an enclosing
method is out. Checked against the fifteen bodies: **it costs one of them**, because in almost
every block the *first* thing evaluated is a send on the parameter, and a send on `.any` is a
`needed:` that short-circuits the whole body before the vcall is reached.

| block | first evaluated | verdict under this cut |
|---|---|---|
| `identifiers.select { \|i\| i.start_with?("CVE-") }` | `i.start_with?` on `.any` | `needed:` |
| `references.find { \|r\| r["type"] == "ADVISORY" }` | `r["type"]` on `.any` | `needed:` |
| `versions.any? { \|v\| normalize_version(v.to_s) == target }` | `v.to_s` on `.any` | `needed:` |
| `list.map { \|data\| new(data) }` | `new(data)`, an implicit-self send | **stays `oof`** |

So the cut is worth taking: `selfCls` inside a block is a *later* widening, and the one body it
costs is `Vulnerability#self.from_osv_list`.

### The option this replaces, and why

Indexing `KontOk` by the frame stack (a parallel `fids` index, or `Γs : List (FrameCtx × Env ×
FrameId)`) is the general answer and would make clause 2 provable directly. It is ~200 mechanical
edits across five files and it makes every constructor carry an index nothing but this one clause
reads. The two changes above are ~15 edits and leave the general answer available for the day a
second consumer appears.

### Revised order for the rung (superseding L247's)

1. `ClosuresOk` — **built** (L248); grow it by the three name-free clauses;
2. `StackCtx` clause 2 guarded on `kind ≠ .block`;
3. `KontOk.iterK`, with the block environment `params ++ blockLocals(nilT) ++ outer-as-`.any``;
4. the two pushes' `StackCtx`/`FramesOk`, and `setLocal` at a block-local;
5. the third `EntryOk` arm;
6. the rule, its `inferOpen` mirror, and `inferOpen_factors`' case.

## L250 — `FrameCtx.inBlock` after all, and `StackCtx`'s name clause is guarded on it

Out of fragment **19 → 19**. `--check` byte-identical, `--self-test` all agree, axiom-clean.
L249's items 2 and 3, built — and it is L243's withdrawn field, reinstated with the reason it is
actually needed.

### The reinstatement, and why L243's withdrawal was right at the time

L243 added `FrameCtx.inBlock`, pinned it `false`, and withdrew it in the same commit: *a field no
rule sets is a `DecidableEq` cost and an implication with one instance*. That was right about
`FrameConforms` — L247 then showed its obligation at an enclosing local is `ValueTy _ _ .any`,
which needs nothing about the captured frame — and **wrong about `StackCtx`**, which is positional
over the same stack and whose second clause compares a *heap-derived name* (`className h defmod`,
read off the frame the closure captured) against the name the context carries. Only the pairing
connects them, and `KontOk` cannot express a pairing (L249).

```lean
  (c.inBlock = false → className h (frames.getD fid default).defmod = c.cls) ∧
```

### What pays for the guard, and where

* **`infer`'s `def` arm** grows `ctx.inBlock = false` as an eighth conjunct of the row guard —
  `ctx.ret.isNone`'s shape at the block channel, and free for the same reason (no rule sets the
  flag). The row's key *is* `ctx.cls`, so it is unwitnessable inside a block; the rule refusing the
  row is what makes the guarded clause enough.
* **The `def` case's `hctx` becomes a function of the flag**, applied where the row is built —
  three sites, one `hdf.2.2` each.
* **`StackCtx`'s `meth` clause gains `c.inBlock = false`.** That is what the two `super` cases read
  the name clause through: they already have `c.meth = some mn`, and a block body's context names
  no method. Without it each would have needed its own guard.
* **`infer`'s `def` body context sets `inBlock := false` explicitly.** L207/L214's point a third
  time: `{ ctx with … }` would inherit the *enclosing* activation's flag, and a `def` body is never
  a block whatever encloses it (`enterUserMethod` pushes a `.method` frame).

### The alternative that was tried first and is worse

Guarding on the **frame's** kind (`(frames.getD fid default).kind ≠ .block`) rather than on the
context's flag. It type-checks at the construction sites just as cheaply, and it fails at the
*consumers*: the `def` case would have to prove the current frame is not a block, and nothing in
`Inv` says so — the fact lives in the static context, which is exactly what a channel is for.
Reverted after one build.

### What is left of the rung

`KontOk.iterK` (L249's item 3) is now unblocked on the `StackCtx` side: a block activation's entry
owes clause 1 (`classPayload?`, name-free), clause 3 (`defVis`, name-free), clause 5 (`cref`,
name-free) and nothing else, and the three name-free ones are `ClosuresOk`'s next growth (L249
item 1). Then the two pushes, the third `EntryOk` arm, and the rule.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`**,
`--check` diff empty against L248's capture, `--self-test` all agree (the `def` guard is the first
change to `infer` in this chain, so the self-test is owed and was run), third ratchet **19**.

## L251 — `ClosuresOk` grows the three name-free clauses, and `FrameShape` is what makes it cheap

Out of fragment **19 → 19**. `--check` byte-identical, axiom-clean, `Proof/`-only. L249's item 1,
built — the last of the block frame's frame-side prerequisites.

```lean
def ClosuresOk (m : Machine) : Prop :=
  ∀ κ ∈ m.kont, ∀ cl, KontClosure κ = some cl →
    cl.captured < m.frames.size ∧ (m.frames.getD cl.captured default).captured = none ∧
    (m.heap.classPayload? (m.frames.getD cl.captured default).defmod).isSome ∧
    Boot.objectId ∈ (m.frames.getD cl.captured default).cref ∧
    defVisOfDef (m.frames.getD cl.captured default) = .pub
```

The three new conjuncts are exactly the `StackCtx` clauses a **block activation's own entry** will
owe that do not mention a name — `callClosure` copies `defmod`, `cref` and `defVis` from the
captured frame, so proving them there is proving them here. The name-dependent clause is the one
L250 guarded on `c.inBlock`.

### `FrameShape`, and why the transport needed it

`ClosuresOk.transport`'s frame hypothesis was *the frame is unchanged*, which is **false at
`setLocal`** — that writes `locals`. Strengthening it broke the assignment case and weakening it
to `captured` alone stopped covering the three new conjuncts. What works is the predicate naming
the four fields the invariant reads:

```lean
def FrameShape (f g : Frame) : Prop :=
  f.captured = g.captured ∧ f.defmod = g.defmod ∧ f.cref = g.cref ∧
  defVisOfDef f = defVisOfDef g
```

One hypothesis instead of four, and `setLocal_shape` discharges it in one lemma — the same
`by_cases` on the owner that `setLocal_captured` was, generalized. `getD_push_lt` and the
frames-unchanged steps give it by `FrameShape.rfl'`.

### And a *heap* hypothesis, which the old version did not need

`(classPayload? defmod).isSome` reads the heap, so the transport now also takes
*classes stay classes*. Three instances: `PlainGrow` (through `TypeAgree`'s third component),
`defineMethod` (the same), and `IvarOnly` (`hi.classPayload`). Every other step leaves the heap
alone and supplies `fun o ho => ho`.

### What is left of the rung

`KontOk.iterK` and the two pushes, then the third `EntryOk` arm, then the rule. Every predicate a
block frame needs is now in place: `FrameConforms` follows the chain (L243), `Inv`'s frame/kont
correspondence counts the block pop (L245), `StackCtx`'s name clause is guarded (L250), and the
captured frame's facts ride on the kont (this).

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`**,
`--check` diff empty, third ratchet **19**.

## L252 — the deferred bill: `x = 1` inside a block, refused by the rule and guarded in the invariant

Out of fragment **19 → 19**. `--check` byte-identical, `--self-test` all agree, axiom-clean. L243's
bill, paid — and with it the **last** of the block frame's frame-side prerequisites.

### What L243 deferred, restated

`StackCtx`'s L243 clause is `(frames.getD fid default).captured = none`, and it is **false at a
block frame**. What it was load-bearing for is `setLocal`, not `getLocal`:

> `Machine.setLocal` walks the `captured` chain and mutates the frame that already binds the name —
> which for a block frame may be the **enclosing** activation, invalidating that frame's own entry
> in `FramesOk` at a type its own environment still claims.

So the clause is guarded on `c.inBlock = false` and `infer`'s `.vasgn .lvar` arm grows the matching
guard. Free today; the block rule is what will make it bite. (The widening it does *not* refuse is
an assignment to a **block-local** — a name first assigned inside the block, which `callClosure`
pre-binds in the block frame's own `locals` so `setLocal.owner` stops there. That needs the name,
not the flag; L247.)

### `KontOk.asgn` carries the flag, and that is where the delivery reads it

The guard is checked at the **eval** step and spent at the **delivery**, two steps apart, so it has
to ride on the kont — `c.inBlock = false` as `KontOk.asgn`'s first premise, free at its one
construction site because the eval case's split hands it over. Same shape as `asgnIvar`'s
`selfCls.isSome` premise (L191), and for the same reason.

### `infer.induct` renumbered, and the recovery cost is worth recording

This is the **first guard in the chain that sits inside an arm** rather than inside an existing
`if`, so the arm's alternatives went from two (`some`/`none`) to three (`true`, `false`+`some`,
`false`+`none`) and every case number after it moved by **one**. Recovery, in the order it worked:

1. `sed` every `| caseN` with `N ≥ 13` to `N+1` — **32 of the 33 numbered alternatives in
   `Mono.lean` were then correct on the first build.** The threshold is one above the last
   pre-`vasgn` alternative, which `Mono.lean`'s own comments name (`case10` is `vcall`).
2. The one that was not is the arm itself: it gained a binder for the guard's branch, and the
   equation it stores is now under that branch — so the case takes `hib` and every `simp only
   [infer, …]` in it needs `hib` in the list.
3. `Preservation.lean`'s eval case gained one `split`: inside a block the rule answers `none`, so
   that branch is the contradiction and the old proof is the `false` branch.

> **`FrameOk` stops being free**, and that is the change with the widest reach. What the proof can
> have unconditionally is now **`FrameShallow`** — `m.stack ≠ []`, `curFid < size`, and a shallow
> chain — which is enough for every *read* and for the twenty `hf.1` uses. Only the `asgnK`
> delivery needs the write, and it has the flag.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`**,
`--check` diff empty, `--self-test` all agree (owed: `infer` changed), third ratchet **19**.

## L253 — `KontOk.iterK`, and the loop's turn is **proved**

Out of fragment **19 → 19**. `--check` byte-identical, axiom-clean, `Proof/`-only. L249's item 3
and half of item 4: the constructor, and the consecution case that consumes it.

### The constructor

```lean
  | iterK … :
      cl.params = [.req x] → cl.locals = [] → cl.lam = false →
      bs.params = [σp] → Γb = (x, σp) :: outer → (∀ e ∈ outer, e.2 = Ty.any) →
      cb.ret = none → cb.inLoop = none → cb.selfCls = none → cb.meth = none →
      cb.inBlock = true →
      infer D Γb cl.body false cb = some (τbody, Γb', D) → SubEnv Γb Γb' →
      subTy τbody bs.ret = true →
      (∀ a ∈ rest, ValuesTy h a bs.params) →
      subTy τ bs.ret = true → ValueTy h retVal τr → subTy τr τ' = true →
      cΓ.1.ret = none → cΓ.1.inLoop = none →
      KontOk D h (cΓ :: Γs) τ' k →
      KontOk D h (cΓ :: Γs) τ (.iterK cl brk rest .ignore acc retVal cur :: k)
```

The conclusion sits at the **iterator activation's** entry — the block frame has already popped —
and the constructor carries *everything the next call needs*, because `iterStep` either calls the
block again (a fresh block frame **and** a fresh `iterK`) or delivers `retVal` to the `frameK`
below.

`kind = .ignore` restricts it to the `each`-shaped iterators. `.collect` accumulates the block's
answers into a fresh array and needs the element claim `Ty` cannot yet write (`arrayOf`);
`.fold`/`.maxBy` change the block's *argument* types between iterations.

### What the consecution case actually needed, in the order it came out

* **`ValuesTy h a [σp]` pins the per-iteration argument list to one value.** `ValuesTy`'s
  `_, _ => False` arm does it; the block's arity check is not a separate premise.
* **`ClosuresOk` is spent in one `obtain`** and supplies all five facts about the captured frame:
  the bound, the empty chain (for `ShallowChain`), and the three name-free `StackCtx` clauses. The
  captured frame's *environment* is never mentioned, which is L247's move cashed.
* **`FrameConforms` at the fresh block frame splits on the name.** The parameter is in the frame's
  **own** locals, so its read is one lookup and `ValueTy.weaken` on the element's type closes it;
  every other name is `.any` and `ValueTy.any` closes it with no lookup at all.
* **`StackCtx` at the block frame is four vacuous clauses and three `ClosuresOk` ones.** `inBlock`
  makes the name clause vacuous (L250), `selfCls = none` and `meth = none` the other two, and
  `defVisOfDef` is a computation on the frame literal (`kind = .block`, `defVis` at its default).
* **`ClosuresOk.transport`'s hypothesis had to be weakened**, and this is the transferable part:

  > It said *every kont of the new continuation was already in the old one*. The block call pushes
  > **two konts that are new** and carry the closure the `iterK` they replace already carried. The
  > right hypothesis is *every closure the new continuation mentions, the old one mentioned* —
  > weaker, still one line at all four existing call sites, and it is what a loop that rebuilds its
  > own continuation needs.

* **`SubEnv Γb Γb'` is a premise, not a lemma.** `CtlOk`'s eval clause relates the continuation's
  environment to the body's *output* one, and `infer` only ever extends — but nothing states that,
  so the constructor carries it and the rule will check `subEnvB`.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`** (and no
`sorry` in the tree), `--check` diff empty, third ratchet **19**.

## L254 — the third `EntryOk` arm, and the "opposite polarity" bill turns out to be already paid

Out of fragment **19 → 19**. `--check` byte-identical, axiom-clean, `Proof/`-only. L249's item 4.

```lean
def MissesAt (h : Heap) (k : ObjId) (mname : String) : Prop := lookupIn h k mname = none

def IterEntryOk (h : Heap) (τr : Ty) (mname : String) (d : MethodDecl) : Prop :=
  τr = .cls "Array" ∧ mname = "each" ∧ d.params = [] ∧ d.ret = .cls "Array" ∧
  (∃ br, d.blk = some { params := [.any], ret := br }) ∧
  ∀ k, TyClass h τr k → MissesAt h k mname

def EntryOk … := BuiltinEntryOk … ∨ UserEntryOk … ∨ IterEntryOk …
```

### The bill L244 named, and why it costs nothing

> `tryIterator` is reached only from `dispatchMiss`, so a block row's witness says the name is
> **not** there — the opposite polarity from both existing arms, and a clause
> `DeclsOk_defineMethod` has to preserve.

It preserves it for free, and the reason is a guard that has been in `infer`'s `def` rule since
F1a: **`declaresName D name = false`**. So the *declared* name and the *installed* one are disjoint
at every `def` the fragment admits, and a miss at one name survives an installation at another —
the same `hne` the two resolving arms already use, read in the other direction. `PlainGrow` needs
no side condition at all (an allocation cannot install a method) and `IvarOnly` is one
`lookupIn_eq`.

### `bs.params = [.any]`, and it is what keeps `Ty.arrayOf` off the critical path

`KontOk.iterK`'s *every remaining element has the block's parameter types* premise becomes
`ValuesTy h a [.any]`, which holds of **every** value — so the arm needs no claim about the
array's contents. A precise element type would need `ValueTy h recv (.arrayOf σ)`, which is L239's
arm and the dispatch rung behind it. This is HANDOFF correction 1, cashed at the place it was
about.

### `EntryOk.blockless`, and why it is one lemma rather than three `rcases` arms

Every *blockless* rule reads its row through `sigOf`, which refuses a block-taking row (L242), so
`sigOf_declFor` concludes at `blk := none` and the iterator arm is refuted by one projection.
Stated once:

```lean
theorem EntryOk.blockless (he : EntryOk D h τr mname { params := ps, ret := τret, blk := none }) :
    BuiltinEntryOk … ∨ UserEntryOk …
```

The three send cases then keep the two-way `rcases` they had, and the diff at each is one `.blockless`.

### What is left

The block-send step's consecution case (L244's five reductions plus `Inv` at the far end, which is
L253's cons case with a heap allocation in front of it) and the rule. **The census moves at the end
of the rule.**

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`**,
`--check` diff empty, third ratchet **19**.

## L255 — the block-send rule, written and **reverted**, and the frame it stumbles on has no `cref`

Out of fragment **19 → 19**. `--check` byte-identical, axiom-clean. The rule was written, the
checker built and stayed byte-identical, and four of the five proof obligations closed. The fifth
is a clause nothing had needed before, and its price is an L236-shaped edit — so the rule is
**reverted** and its *vocabulary* kept, which is what the next session starts from.

### What landed (inert, and all of it the rule's own vocabulary)

`blockSend?` (the four-way read off the row and the block node), `anyEnv`, `blockCtx`, their two
inversions (`blockSend?_shape`, `blockSend?_declFor`), `SubDecls.blockSend_eq`, `anyEnv_get` /
`anyEnv_subEnv` / `SubEnv.cons`, `EntryOk.iter` (a block-taking row is witnessed by the iterator
arm and nothing else, because both resolving arms pin `blk = none`) and `arrayPayload_of_valueTy`
(`plainRecv`'s sixth clause read back out, factored from `spreadA_of_array`).

### What the rule looks like, and that it is small

```lean
  | .send (some recv) mname [] (some (.block ps ls body)) =>
    match infer D Γ recv top ctx with
    | some (τr, Γ₁, D₁) =>
      match blockSend? D₁ τr mname ps ls with
      | some (x, σp, βret, τret) =>
        match infer D₁ ((x, σp) :: anyEnv Γ₁) body false (blockCtx ctx) with
        | some (τb, Γb', D₂) =>
          if subTy τb βret = true ∧ D₂ = D₁ ∧
              subEnvB ((x, σp) :: anyEnv Γ₁) Γb' = true then some (τret, Γ₁, D₁) else none
        | none => none
      | none => none
    | none => none
```

Twelve lines, placed **last** before the catch-all, and `--check` was byte-identical with it in —
no shipped table has a block row, so it accepts nothing until one is declared.

### Four of the five obligations, and what each cost

1. **`infer.induct` renumbers by +5 for `N ≥ 96`** — measured, and the L252 recipe worked again:
   `sed` the numbers, then read the new arm's arities off Lean's own "expected *k*" messages
   (99 and 100 are the `if`'s two branches at 25 binders, 101/102/103 the three refusals).
2. **`defFree` and `asgnFree` must recurse into the block slot.** The **ninth** walk into L174's
   trap, and the first a *block* causes: the rule threads the table and the environment through the
   block **body**, so the `.send` arm's `blk`-ignoring conjunction stops being vacuous.
3. **`infer_env_mono`'s block case is the only arm whose subexpression's environment is built from
   the send's own**, which is what `anyEnv_subEnv` is for. Closed.
4. **`infer_mono_all`'s** is the receiver's IH, `SubDecls.blockSend_eq`, and the body's IH. Closed.
5. **The `recvKBlk` delivery case** — and this is where it stops.

### The fifth: `startIter`'s activation has an empty `cref`

`Proof/Static/Iter.lean`'s five reductions (L244) took the step all the way to the block body with
no trouble, and `KontOk.iterK`'s premises (L253) are exactly what the far end needs. What refuses
is `StackCtx` at the **iterator activation** — the frame `startIter` pushes as the `break` target:

```lean
let frame : Frame := { self := recv, defmod := classOf m.heap recv, kind := .method, meth := mname }
```

`cref` is left at `[]`, and `StackCtx`'s fifth clause is *`Object` is on the frame's lexical
constant scope* (L189, the whole frame-side cost of the `.const` read rule). Nothing needs it
there — **no code runs in that activation**; the loop is driven by the `iterK` continuation and
every expression is evaluated in a block frame above it — but the predicate is positional and
demands the clause of every entry.

> **And guarding it on the *block* flag is wrong**, measured: a block body **does** read constants
> (`CVSS_TYPE_PRIORITY.key?(…)` is in the slice), so a block frame owes clause 5 and gets it from
> the frame it captured (`ClosuresOk`, L251). The two activations a block send pushes want
> *different* clauses relaxed — clause 2 for the block, clause 5 for the iterator — which is why
> `FrameCtx` needs a **second** flag (`noCode`) and not a wider first one.

### The price of that flag, and it is why this is reverted rather than finished

`noCode` on `FrameCtx` and the guard on clause 5 are three lines. The **consumers** are what cost:
`.const`, `def` and `class'` all read clause 5, so each needs `ctx.noCode = false`, and the only
place that fact can come from is **`CtlOk`'s eval clause** — *the context a body is evaluated at
hosts code*. `CtlOk`'s value clause cannot carry it, because at the `iterK` delivery the head
context **is** the iterator's. So the fact has to reach the delivery cases through `KontOk`, which
means a defaulted premise on the constructors that hand a continuation an `.eval` — L236's edit
shape, and L236 is the measurement of what it costs (18 constructors, 43 construction sites
unchanged because the premise is a trailing `optParam`).

That is one clean commit, and it belongs at the top of the next session rather than at the bottom
of this one.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with **0 `sorryAx`** and no
`sorry` in the tree, `--check` diff empty against L254's capture, third ratchet **19**.

## L256 — the iterator activation gets the caller's `cref`, and that is L255's blocker gone

Out of fragment **19 → 19**. **The first change to the interpreter in this chain**, so the full
difftest is owed and was run — every tier matches its recorded baseline exactly.

### One line

```lean
  let frame : Frame :=
    { self := recv, defmod := classOf m.heap recv, kind := .method, meth := mname,
      cref := m.currentFrame.cref }          -- ← was: cref left at its `[]` default
```

`startIter` pushes this activation as the **`break` target**, and **no code evaluates in it**: the
loop is driven by the `iterK` continuation and every expression runs in a block frame above. So the
field was never read — every `cref` read in the interpreter is `m.currentFrame.cref` (during eval
*in* that frame), `md.cref`, or `capF.cref` (the frame a closure captured, which is the caller and
not this one). CRuby's iterator activation inherits the caller's cref, so this is also the more
faithful frame.

### Why it is worth a semantics change, and what it replaces

`StackCtx`'s fifth clause is *`Object` is on the frame's lexical constant scope* (L189, the whole
frame-side cost of the `.const` read rule). It is **positional**, so the iterator activation owes it
and an empty `cref` refuses it — L255's blocker.

L255 priced the alternative: a second `FrameCtx` channel (`noCode`), a guard on clause 5, and — the
real cost — its **consumers**. `.const`, `def` and `class'` all read clause 5, the only source for
the flag is `CtlOk`'s **eval** clause (the value clause cannot carry it, because at the `iterK`
delivery the head context *is* the iterator's), and reaching the delivery cases from there means a
trailing `optParam` on 18 `KontOk` constructors — L236's edit at L236's cost.

> **A one-line change to a frame nothing reads, validated by the difftest, is cheaper than an
> invariant channel with three consumers.** And it is the honest direction: the field was `[]`
> because nothing needed it, not because `[]` was right.

`Proof/Static/Iter.lean`'s `startIter_eq` is the only proof that mentions the literal; it gained the
field and stayed `rfl`.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean, `--check` byte-identical,
third ratchet **19**, and the difftest in full:

| tier | result | recorded baseline |
|---|---|---|
| 0 | **992 agree, 0 disagree** (1,304 ran) | 992 / 0 |
| slice | **351 agree, 0 disagree** | 351 / 0 |
| 4 | **25 agree, 0 disagree** | 25 / 0 |
| advisory | **106 agree, 0 disagree** | 106 / 0 |
| 1 / 1.5 | 146 / 163 agree, **0 disagree** | 0 disagree (generative, re-drawn) |
| regressions | **35 held, 2 still_open, 3 gated** | 35 / 2 / 3 |

## L257 — the block-send rule lands in `infer`, and the delivery case is **proved**

L255 wrote the rule and reverted it; L256 removed its blocker. This puts it back and pays the
consecution case in full, so `Metatheory` builds axiom-clean with the rule in `infer`.

### The rule

`Types/Core.lean`, last arm before the catch-all:

```lean
| .send (some recv) mname [] (some (.block ps ls body)) =>
  match infer D Γ recv top ctx with
  | some (τr, Γ₁, D₁) =>
    match blockSend? D₁ τr mname ps ls with
    | some (x, σp, βret, τret) =>
      match infer D₁ ((x, σp) :: anyEnv Γ₁) body false (blockCtx ctx) with
      | some (τb, Γb', D₂) =>
        if subTy τb βret = true ∧ D₂ = D₁ ∧
            subEnvB ((x, σp) :: anyEnv Γ₁) Γb' = true ∧ ctx.inBlock = false then
          some (τret, Γ₁, D₁)
        else none
      | none => none
    | none => none
  | none => none
```

`ctx.inBlock = false` in the guard is not decoration: without it a *nested* block send would build a
two-hop capture chain and `ShallowChain` — the `FrameConforms` clause that says a frame's captured
parent is itself uncaptured — is a one-hop predicate. One flag refuses the nesting instead.

### The delivery case, and what actually cost

`KontOk.recvKBlk` delivers the receiver; the step is `finishSend_lit ⟶ reifyBlock ⟶
invoke_iter_each ⟶ startIter ⟶ iterStep`, all five already reduced in `Proof/Static/Iter.lean`
(L244). The `nil` branch is the receiver going to a `frameK`. The `cons` branch builds `Inv` at a
machine with **two pushed frames** (the iterator activation, then the block frame), and that is where
the session's time went — not in the semantics, in the arithmetic:

> **`omega` does not fire under a context this large.** With `this : g < m.frames.size` in scope and
> the goal `g < m.frames.size + 1` — verbatim, after `simp only [Array.size_push]` — `omega` reports
> *"No usable constraints found"*, while `exact Nat.lt_succ_of_lt this` closes it. Every index fact
> in the branch is therefore explicit.

Five `have`s at the head of the branch carry all of them (`hpop`, `hlt2`, `hltI`, `hltB`, `hgetI`),
each quantified over the two pushed frames so the giant frame literals never have to be written.
A sixth, `hbc`, is the `rfl` that says the fresh closure's `captured` **is** the send site's frame —
the goal spells it `(blockClosure … ).captured`, and `rw` will not see through that.

Two named constructors, in `Proof/Static/Locals.lean`:

- `FramesOk.cons` — the predicate is a `match`, and a four-deep anonymous constructor at a two-frame
  push re-associates unpredictably. Naming the arm makes each obligation a *typed* hole.
- `StackCtx.cons`, `FrameConforms.mk'` — likewise, eight and three holes.

That is the whole lesson of the case: at this context size, `⟨_, _, _, _⟩` and `omega` both stop
being labour-saving and start being labour.

### Census

The rule is in `infer`. The **census reads `inferOpen`**, which does not have it yet, so the third
ratchet is unchanged at **19** — the `send-with-block` bodies are still counted as a missing *rule*
rather than as the missing *declarations* (`Array ▷ each` with a `blk`) they will become. That is the
next commit, and it is a front-end arm plus one case of `inferOpen_factors`.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean, `--self-test` all agree,
third ratchet **19** (unchanged, and expected — see above). No interpreter change, so no difftest.

## L258 — the open front end gets the block arm, and the census moves **19 → 7**

L257 put the block-send rule in `infer`. The census reads `inferOpen`, so the ratchet did not
move. This is the front-end arm, and it is far cheaper than the nominal one was.

### The body is checked *nominally*

```lean
| .send (some recv) mname [] (some (.block ps ls body)) =>
  match inferOpen D Γ recv ctx il s with
  | .ok τr Γ₁ s₁ =>
    match τr with
    | .nom t =>
      match blockSend? D t mname ps ls with
      | some (x, σp, βret, τret) =>
        match infer D ((x, σp) :: anyOf Γ₁) body false (blockCtx { cls := ctx.cls }) with
        …
      | none => .missing (.nom t) mname []
    | .var α => .missing (.var α) mname []
    | .nilOf _ => .outOfFragment "nilable-receiver"
  | r => r
```

The recursive call is `infer`, not `inferOpen`, and that is the whole economy of the arm:

> **The rule erases the captured environment to `.any` at every name, so by the time the body
> is reached there is nothing open left in it.** The parameter's type, the block's return type
> and the send's answer all come from the *declaration*, which is nominal.

The alternative — recursing with `inferOpen` — would have needed an `inBlock` channel on `OCtx`
and a guard on every arm the nominal `blockCtx` closes off (`self`, `x = …`, `return`, `super`,
`zsuper`, `next`), each of which is a case of `inferOpen_factors`. This needs none of them.

The factoring theorem's cost is **one lemma and two simp arguments**:

```lean
theorem anyOf_subst (θ : TyVar → Ty) (Γ : AEnv) : anyEnv (substEnv θ Γ) = anyOf Γ
```

plus `blockCtx` in the unfolding set, because `blockCtx` keeps only `cls` and the open and
nominal contexts agree there. The case then closes in the existing `simp_all`.

### A missing declaration is not a missing rule

`blockSend?` *is* the question "is there a declaration for this send-with-block", so a receiver
with none answers `.missing`, and the census counts it in the `needed:` column beside `Array ~
hash` and `Hash ~ fetch`. That is the whole of the 19 → 7 move: twelve of the fifteen
`send-with-block` bodies now name the declaration they want (`α1 ~ select`, `α3 ~ select`, …)
rather than naming a hole in the checker.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean, `--self-test` all agree.
No interpreter change, so no difftest.

| ratchet | before | after |
|---|---|---|
| `oof` | 19 | **7** |
| `needed:` | 70 | 82 |

Remaining `oof`: `send-with-block` 3, `begin` 2, `splat` 1, `nilable-receiver` 1.

## L259 — the arity-`n` block send, and the *table* is what refuses it — **7 → 5**

`xs.gsub(re) { |c| … }` — a send with arguments *and* a block. Two of the slice's three
remaining `send-with-block` bodies are this shape; the rule for it is the L257 arm plus the
argument traversal, and its consecution case is a **refutation**.

### The rule

`blockSendA?` is `blockSend?` without the `d.params = []` restriction, handing back the
declaration's parameter list so `subTys` can match the argument types against it. The arm sits
after L257's and before the catch-all.

Its guard carries one conjunct L257's does not: **`D₁ = D`**.

> `Inv`'s eval clause carries `DeclsOk` at the **entry** table only, so a row read at a table
> the subexpressions grew is a row nothing in the invariant knows. Pinning the receiver's
> output table to the entry one is what lets the consecution case reach `DeclsOk` at all.

Nothing in the slice declares a method inside a block send's receiver or arguments, so the
restriction is free on the census.

### The consecution case is a refutation, and that is the honest shape

```lean
obtain ⟨τr, d, σp, βret, hd, hdps, hdb⟩ := infer_sendBlkN_decl hinf
exact hdps ((htab.1 τr mname d hd).iter hdb).2.2.1
```

An arity-`n` block send names a declaration that is **block-taking** *and* has **parameters**.
`EntryOk` cannot grant both: the two resolving arms pin `blk = none` (`EntryOk.iter`), and the
one arm that admits a block — `IterEntryOk` — pins the parameter list to `[]`. So the rule is
real and the **table** refuses it, which is where the refusal belongs. When a future `EntryOk`
arm supplies a block-taking row *with* parameters, that one line becomes work.

`infer_sendBlkN_decl` is the inversion that extracts the pair; `inferArgs_cons_ne` is the
half-line that says a non-empty argument list has a non-empty type list, which is what turns
`subTys τs dps` into `dps ≠ []`.

### The costs that were not the semantics

- **`infer.induct` renumbering, third time.** The arm has six leaves, so **`+6` for `N ≥ 104`**
  in `Proof/Static/Mono.lean` — the arity-zero arm occupies 99–103, not 96–100 as a first
  reading of L255's note suggests. The recipe (renumber, then read arities off Lean's
  "expected *k*" messages) worked unchanged: 33, 33, 29, 22, 18, 13.
- **`simp` and the table equalities.** In `infer_mono_all`, `⟨…, rfl, rfl, …⟩` on the guard
  cannot fire (the receiver's IH has already moved `D₁`), and leaving them as plain facts lets
  `simp` rewrite `D₂ → D₁` in the goal *before* `hbs` — which is stated at `D₂` — can match. So
  they are rewritten **into** the row read and the body first, then used.
- **`inferOpen_factors`' new case is a residual, not an alternative.** The arity-`n`
  alternative reduces the receiver and the argument list and stops; the goal that survives
  names the body's `infer` at `anyEnv (substEnv θ Γ₂)` where the open arm ran it at
  `anyOf Γ₂`. One rewrite closes it — but it has to run *after* the alternative block, because
  **at the moment `first` runs, that term does not exist yet**. An hour went into treating it
  as an alternative that "mysteriously would not fire"; it was firing on a goal that did not
  yet contain the pattern. The file already names this shape twice (L175's `StoreLe`, L193b's
  join); this is the third.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean, `--self-test` all agree.
No interpreter change, so no difftest.

| ratchet | before | after |
|---|---|---|
| `oof` | 7 | **5** |
| `needed:` | 82 | 84 |

Remaining `oof`, one body each except `begin`: `begin` **2** (`in_interval_strict?`,
`in_interval_permissive?`), `splat` **1** (`Version#to_json`), `nilable-receiver` **1**
(`severity_display`, a `&.` chain), `send-with-block` **1** (`comparator_for`, a `->(a, b) { … }`
lambda — proc types, not the block rule).

## L260 — union dispatch at a nilable receiver, and it costs **one** lemma at each send — **5 → 4**

`severity&.to_s&.upcase || "UNKNOWN"`. Measured first, before any code:

```
$ harness/desugar-dt/bin/export-json  # def f(x) = x&.to_s
["seq",["vasgn","local","__dt_t1",["var","local","x"]],
       ["if",["send",["var","local","__dt_t1"],"nil?",[],null],["nil"],
             ["send",["var","local","__dt_t1"],"to_s",[],null]]]
```

So `&.` is **not** a construct the checker is missing. It is a plain send whose receiver
type is a `.nilable σ` — a type `declFor` answers `none` at, because `tyClassNames` is `[]`
there (L193). The rung is a *rule for that send*, and the standard sound one is union
dispatch.

### The rule is one arm of `sigOf`, and that is why it is cheap

```lean
def sigOf (D : Decls) (τ : Ty) (mname : String) : Option (List Ty × Ty) :=
  match τ with
  | .nilable σ =>
    match declFor D .nilT mname, declFor D σ mname with
    | some d₁, some d₂ => if d₁ == d₂ then … else none
    | _, _ => none
  | _ => …
```

> **Every send rule already reads its receiver's row through `sigOf`.** So the rung needs no
> new `infer` arm, no new `KontOk` constructor, and — the part that mattered — **no
> `infer.induct` renumbering**. `NilClass` is a class like any other, so the union is two
> ordinary `declFor` reads at two ordinary keys, and neither owes a new `EntryOk` arm.

`d₁ == d₂` rather than a join of the two signatures: a join would be a second, weaker notion
of conformance to keep sound at dispatch, and the slice needs none of it.

### The whole bill lands at the *dispatch* sites, and there are three

`sigOf_atomic` used to **derive** `∀ τ', τr ≠ .nilable τ'` from a row's existence. It cannot
any more, so it and `sigOf_declFor` take it as a hypothesis. Two of the three callers are at
an abstract receiver type; both are re-bound by one `obtain`:

```lean
obtain ⟨τ, hsg, hv, hnilτ⟩ := sigOf_value_atomic hsg hv
```

`sigOf_value_atomic` **reduces** a nilable receiver to the atomic arm the receiver *value*
actually is — `valueTy_nilable_inv` splits `ValueTy h v (.nilable σ)` into `v = nil` and
`ValueTy h v σ`, and each arm dispatches by the machinery that was already there. The case
bodies below the `obtain` are unchanged, which is the point: nilable dispatch is not a new
dispatch, it is a *choice between two old ones*.

Three small facts it rests on, all new: `declFor_atomic` (a declaration's key is atomic —
`sigOf_atomic`'s old proof, moved one level down), `valueTy_nilT`, `valueTy_not_nilable`.

### The front end names the atom a union-typed checker names

The open arms check the **nil** side first, because it is the one that is almost always
missing and it is the honest atom to report: `severity&.to_s&.upcase` now asks for
`NilClass ~ upcase : () → _`, which is exactly what Sorbet says about the same line.

A receiver whose *under* type is still a type variable stays out of the fragment, and the
reason is worth recording: the requirement would have to pin `θ α` to a **non-nilable**
(otherwise the nominal `sigOf` sees `.nilable (.nilable τ)`, where `declFor` answers `none`),
and `SatStore`'s row clause is stated over `sigOf`, which by construction cannot say that.
The slice does not reach it — the nil side is missing first — and the census's rule has
always been *report the first atom the body needs*.

The factoring case is again a **residual**, for L259's reason and closed the same way:
`ATy.subst θ (.nilOf (.nom t))` *is* `mkNilable t` by definition, so the open arm's `sigOf`
read and the nominal one are the same read — but the term only exists after the alternative
that reduces the receiver has run.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean, `--self-test` all agree.
No interpreter change, so no difftest.

| ratchet | before | after |
|---|---|---|
| `oof` | 5 | **4** |
| `needed:` | 84 | 85 |

Remaining: `begin` **2**, `splat` **1**, `send-with-block` **1** (the `->(a, b) { … }` lambda).

## L261 — the lambda literal, at the only type the language has for it — **4 → 3**

`Vulnerability#comparator_for` returns `->(a, b) { … }`. The census called it
`send-with-block`; it is not the block rule. Desugared:

```
["send", null, "lambda", [], ["block", [["preq","a"],["preq","b"]], [], [], body]]
```

### The rule, and the one thing it says

```lean
| .send none mname [] (some (.block _ _ _)) =>
  match mname == "lambda" with
  | true => some (Ty.any, Γ, D)
  | false => none
```

`.any` is inferred here, and `Ty.lean` says `.any` must never be inferred. The exception is
not a lapse — it is the honest content of the type language at a value it cannot name:

> There is no `Ty.proc`. `plainRecv` excludes a `.proc` payload (dispatch on a proc has
> receiver-shape special cases in `invoke`), so a `Proc` value's `valueTy?` is `none` and
> **`.any` is the only type it satisfies at all**. A rule that answered anything else would
> be false.

**The body is deliberately not checked, and that is sound at this fragment** because the
fragment cannot *call* what the rule produces: a send on `.any` reads `sigOf D .any m`, which
is `none` (`tyClassNames .any = []`); `&e` block-pass is out of fragment; a user method call
in the fragment passes no block; and `ConformsAt` excludes `new`. The closure is allocated
and no step in the fragment reaches `callClosure` with it. When Wall 2's `Ty.proc` lands, the
body is checked against the proc's declared parameter and return types and this rule is
replaced; the note in `Types/Core.lean` says so at the arm.

### The consecution case is L257's allocation with nothing after it

`finishSend`'s `mkLam` branch is `reifyBlock` and then `.value` — no dispatch, no frame, no
continuation. `Proof/Static/Iter.lean` gains a sixth reduction, `startArgs_lambda` (`rfl`),
and the case is:

```lean
rw [startArgs_lambda, reifyBlock_eq]
exact inv_grow_value hfs htab hsc hhook hsat hstr hcls hbot hks
  (plainGrow_alloc m.heap _ (by simp) rfl) rfl rfl rfl
  (ValueTy.weaken ValueTy.any hsubw) hk
```

Every `_grow` transport it spends was paid at L257 for the *same* allocation. And the value
obligation is `ValueTy.any` — there is nothing to prove about what was allocated, which is
exactly what answering `.any` costs and buys.

### Costs

`infer.induct`: the arm has two leaves and sits last before the catch-all, so **`+2` for
`N ≥ 110`**. `infer_env_mono` gets one new alternative — the arm is *one* guard where the
`def` arm is two, so `split <;> simp_all` rather than `split <;> split <;> simp_all`.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean (with
`startArgs_lambda` added to the audit list), `--self-test` all agree. No interpreter change,
so no difftest.

| ratchet | before | after |
|---|---|---|
| `oof` | 4 | **3** |
| `pacc` | 6 | **7** — `comparator_for` now *accepts*, it did not merely move column |

Remaining: `begin` **2**, `splat` **1**.

## L262 — `provs`, `discharge`, and the theorem that replaces factoring for a *program*

The whole-program pass (L263) needs one thing the per-body pass never did: a place for a
class's own `def`s to **meet** its own bodies' requirements. `inferOpen` types
`def get; value; end` into `α ~ value : () → β` and stops; the other half —
`α ▷ value : () → Integer`, which `def value; 1; end` supplies — has never been recorded
anywhere, because `bodyReports` gives every body a *fresh* store at `{}` and two bodies of
one class therefore share nothing.

Three pieces, and the third is the only one with a soundness story.

### 1. `Store.provs`, the fourth field

Same type as `rows` — `List (TyVar × Row)` — because a provision *is* a row entry with
possibly-variable types, so `Row`/`ASig` carry it unchanged and `discharge` compares like
with like. What distinguishes the fields is **polarity, not shape**: `SatStore` obliges
`rows` and assumes `provs`.

`Store.rowIn` is factored out of `rowOf` in the same change (`rowOf_eq`/`provOf_eq` are
`rfl`, so nothing that already unfolds `rowOf` notices). The reason is the proof: the
lookup has to be stated about the *association list*, because `dischargeRows` rewrites one
entry-by-entry and the lemma it needs is *a key-preserving map commutes with the lookup*.

**It is not an `Assn` atom, and that is deliberate.** `toAssn` does not print it and `Assn`
gains no arm, so `entail`/`dischargeAll`/`denote` — all proof-coupled — are untouched. A
provision is an internal ledger that `discharge` *spends* before anything is rendered.

### 2. `discharge`, and the three places it refuses to cancel

`Types/Discharge.lean`. Requirements a provision answers are replaced by the equalities
that answering them owes:

```
Σ = { α ~ value : () → β }  ∪  { α ▷ value : () → Integer }
discharge Σ  =  { β = Integer }
```

The refusals are the design, not gaps, and every one of them **keeps** the requirement —
a weaker output, never a wrong one:

* **two non-variable types** — `pinPair` equates `α` with anything either way round
  (`θ α = τ.subst θ` is exactly an `eqv` atom), but two differing nominal types are
  equatable by no `θ` at all;
* **an arity disagreement** — `pinPairs` is length-indexed. L263 records no provision for a
  `def` with optional or keyword parameters (those accept a *range* of arities and `ASig`
  records one), so this fires only on a genuine caller/callee disagreement;
* **two `def`s of one name at different signatures** — `addProv`'s ★★, upstream of here.

One implementation note worth keeping: every traversal is written `let r := …` + `r.1`/`r.2`
rather than `let (es, keep) := …`. A destructuring `let` elaborates to a `match`, and every
lemma in the proof file would have had to push a motive through it.

### 3. `discharge_sound` — and why `inferOpen_factors` is no longer the theorem to want

```lean
theorem discharge_sound (h : SatStore D θ (discharge st)) (hp : SatProvs D θ st) :
    SatStore D θ st
```

`discharge` **drops** requirements, so that is its entire soundness content: a dropped one
was really met. A solver may then be handed the small cancelled store and its answer still
discharges every requirement `inferOpen` recorded.

**`inferOpen_factors` cannot be the program-level theorem, and this is the argument.** It
says open-self typing factors through nominal typing *at a fixed table*, which is what
makes an open accept re-derivable as an `infer` accept. A program's `def`s are precisely
what changes the table, and generalizing `Factors` to thread `D` would oblige the open
`def` arm to satisfy `infer`'s `def` rule — including `params.isEmpty`, which excludes
**67 of the slice's 112 method bodies**. So the division of labour is:

| theorem | scope | status |
|---|---|---|
| `inferOpen_factors` | one *body*'s typing is a nominal typing | unchanged, untouched — `inferOpen` gains no arm |
| `discharge_sound` | the *cancellation between* bodies preserves what was required | proved here, axiom-clean |

**The second premise is real and is not discharged here.** `SatProvs D θ st` says
`sigOf D (θ α) n` really is the signature the `def` supplied — a fact about the **table**,
not about `θ`, true when the class really does define the method. L263's `def` arm is what
has to record it faithfully. Stating it as a premise is the honest split; pretending it
were free would make the theorem vacuous in exactly the direction that matters. `SatProvs`
is literally `SatStore`'s first clause read at the other field, which is what makes the
last step of the proof one `rw`.

Two corollaries are in the file as sanity checks on which way each premise leans:
`discharge_nil_provs` (no provisions ⇒ `discharge` is the identity on `rows`, so the
cancellation and not the statement is doing the work) and `satProvs_nil` (`SatProvs` at
empty provisions is vacuous, so nothing is smuggled in through it).

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean with
`discharge_sound` added to the audit list, `fragment-gap.py --self-test` all agree. **No
consumer yet** — `--assn` is untouched and the third ratchet cannot move — and no
interpreter change, so no difftest. The three `example`s in `Types/Discharge.lean` are the
capability, by `decide` rather than `native_decide` (§4 norm 5).

## L263 — `inferProgram`: the open front end over a whole program, and one variable per class

`inferOpen` refuses `def` and `class`, and the reason it gives is about the *body* it was
built for: `infer`'s `def` arm requires `defFree body`, so a body that declares a method is
outside the nominal fragment anyway, and a fixed table is what makes `inferOpen_factors`'
conclusion carry `D` in both positions. That is sound, and it is not a reason to refuse a
**program** — a program *is* a sequence of `class`es and `def`s, and typing one asks a
different question with a different answer: *what would the types have to be for this
program's constraints to be satisfiable?*

### A driver, not an arm

`Types/Program.lean`'s `inferProgram` walks the declaration-shaped constructors — `seq`,
`class'`, `module'`, `scopedClass`/`scopedModule`, `def'`, `defs`, `begin'` — and hands
every *expression* to `inferOpen` **unchanged**. So `inferOpen` gains no arm,
`inferOpen_factors`/`inferOpen_mono` and their four companions are untouched, and each
body's typing is still a nominal typing. The price is stated rather than hidden: a `def`
nested inside a *method body* is still refused, by `inferOpen`. Nothing in the slice has one.

### The mechanism is one variable per class — two, actually

`bodyReports` gives every body a **fresh** store at `{}` and `self := 0`, which is why no
requirement it reports has ever been answerable: two bodies of one class share nothing.
Here each class name gets

* `α_C` — an *instance*, which is `self` inside every `def` of `C`;
* `β_C` — the *class object*, which is `self` inside `class C … end`'s own body,

allocated once from one counter into one store. The `vcall` requirement in one body and the
`def` provision beside it land at the same variable, and L262's `discharge` cancels them:

```
class String; def value; 1; end; def get; value; end; end
  ⇒ accept, Symbol, under  α₄ = Integer          -- the obligation on String closes EMPTY
```

**Two variables and not one**, because `self` in a class body is the class and in a method
body an instance — the conflation `infer` avoids by refusing `self` when `selfCls` is
`none`. Merged, an `attr_accessor :x` in a class body would discharge an `x` requirement
from a method body, which is false. The bug this caught in the first draft is worth keeping:
the `defs` arm prefixed the provision name with `self.` (mirroring `bodyReports`' *display*
convention), so `def self.make` provisioned `self.make` while the class body's call required
`make`, and the two silently failed to cancel. The variable is what marks a singleton; the
name is the name.

### Two things read off the output rather than mirrored

* **`ctx.params` and the provision's parameter list come from `Γ_b`**, not from
  `openParamTys`. That function hard-codes `1, 2, …, n`, which is right under
  `inferBodyWith`'s convention (`fresh` starts at 1) and wrong under a shared counter. Here
  a mirror would be a *soundness* bug rather than a stale report — a provision at the wrong
  variables cancels a requirement it does not answer.
* **`PState` wraps `OState`** rather than adding fields to it. `OState` appears in every
  lemma statement in `Proof/Static/OpenSelf.lean` — `inferOpen_mono`, `inferOpen_rets`, the
  five `Factors` motives — and none of them would read the new fields.

### Three refusals, each with its reason

* **A `def` under an `if`/`while` provides nothing** — it may not run, so its row is not a
  fact about the program. `outOfFragment "def-in-if"`, named rather than approximated (the
  label is `"def-in-" ++ headName e`, so the census can say which construct it was under).
* **A `def` whose parameters are not all required positionals provides nothing** — it
  accepts a *range* of arities and `ASig` records one. Its body still types and its
  callers' requirements simply survive.
* **No provision is seeded from a superclass**, and this is the one that would have been a
  real unsoundness. `class Foo < Formula` is typed exactly as `class Foo`. Seeding
  `Formula`'s rows onto `α_Foo` looks attractive and is *false*: `SatProvs` obliges
  `sigOf D (θ α) n` to answer, and `sigOf` does not walk ancestors, so the premise
  `discharge_sound` needs would not hold. The obligation is the honest output —

  ```
  class Foo < Formula; def install; system "make"; end; end
    ⇒ accept, Symbol, under  Foo ⊒ ⟨ system : (String) → α₃ ⟩
  ```

  — and inheritance is what *discharges* an obligation, not what fakes a provision.

### What an accept means, and it is weaker than anything else the tool prints

*Types under these class obligations.* Weaker than `--assn`'s per-body accept (already only
*types under this precondition*, never *is safe* — `slice-verdict.md` §1), and much weaker
than `check`'s `accept`, the only verdict `check_sound` licenses. Nothing here feeds `check`.

### Costs and checks

The pass is a `mutual` block, so it is well-founded-compiled and does **not** reduce in the
kernel: the seven `example`s are `simp` over the equation lemmas, as `Types/OpenSelf.lean`'s
are, not `decide`. `native_decide` is banned (§4 norm 5).

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean,
`fragment-gap.py --self-test` all agree. No consumer yet — `Types/Program.lean` is off the
default target until L265 imports it in `Main.lean` — so `--assn` and the third ratchet
cannot move, and no interpreter change means no difftest.

## L264 — promotion, and the class object: what is reachable and what is deliberately not

L263 records a `def`'s signature as a provision on a type *variable*, which is what lets a
sibling body's requirement cancel. It does not make the method callable on a **nominal**
receiver: `"x".value` reads `sigOf D (.cls "String") "value"` and nothing has put it there.
This is the second half — and it is also where the honest limits of the class-object half
get pinned rather than papered over.

### Promotion: the program's own ground rows, into the table

A provision whose signature is **ground** is a row `Decls` can hold. `promoteOnce` runs the
pass and adds them; `promote` iterates to a fixed point with `defCount prog` as the bound —
counted, not capped, because every non-final round adds at least one row and a row comes
from a `def`.

**Every promoted row is one `infer`'s own `def` arm would add**, and the five guards are
copied from `Types/Core.lean` one for one rather than chosen: `cls ≠ "Object"` (a toplevel
`def` is private, L162), `name ≠ "initialize"` (same rule), `reopenableClasses.contains cls`
(F1b.9's uniqueness clause), `groundClassNames` excluded (L189), and
`declaresName D name = false` (a redefinition is F1c, unbuilt).

The promoted rows are **conjoined into the verdict's assertion as `Assn.decl` atoms**, so an
accept reads *types, **given** these declarations* — `denote_declAssn` is what gives that
clause its meaning — rather than hiding the table extension.

### The measurement that corrected the plan for this rung

The plan for L264 said the delta over `infer`'s `def` rule is "exactly the parameterized
rows", since `infer` additionally requires `params.isEmpty` and this does not. **Running it
shows that is wrong, and the reason is worth keeping:** a parameterized `def`'s provision is
`(α₃) → α₃`, which is *not ground*, so it is not promotable either. An unconstrained
parameter has no ground type. So promotion in practice fires on zero-parameter ground
bodies — the same population `infer`'s rule admits — and what L264 actually buys is
narrower than planned:

* program-defined class **constants** (below), so a class object is a value;
* the fixpoint, so a promoted row can unblock a body that grounds another provision;
* the `decl`-atom machinery that makes any table extension visible in the output.

The parameterized case is not lost — it lives in the *assertion*, where an unresolved type
belongs (`.eqv 3 Integer ∧ .eqv 4 α₃` for `add(a)` called at `Integer`, which is the solved
instantiation). It is only not a nominal row.

### The class object: a value, and still not a receiver

`programConsts` adds each program-defined class name to `D.consts` at `.clsOf name`, so
`Foo` stops being `missing ::Foo`. Syntactic, deliberately *not* read off a pass run: a
program containing `Foo.new` fails the pass and the constant it needs must not depend on the
pass succeeding.

**`Foo.new` is out of reach, and the blocker is a deliberate decision rather than an
oversight.** `tyClassNames (.clsOf _) = []` (`Types/Decls.lean`), so `declFor`/`sigOf`
answer `none` at the class-object arm *whatever* rows the table holds — the arm is a
declaration-and-parameter type with no dispatch, exactly as `.any` is. Undoing that is not a
promotion guard: it needs a key for singleton rows (the note there rejects `"%class:" ++ n`
for a stated reason) and it widens `DeclsOk_addRow`'s `hτ` step — *the only type a freshly
added row is read at is `.cls c`* — into a disjunction, along with every consumer.

What L263 *does* reach is the class object as a **variable**: `def self.x` provisions on
`β_C`, a call in the class body requires on the same `β_C`, and those cancel. Only the
nominal route is missing, and it is missing by design.

### The next rung, with a witness pinned in the file

`"x".twice(1)` against `class String; def twice(a); a; end; end` is **`blocked`**, and the
last `example` in `Types/Program.lean` records it. `twice`'s provision is not promotable
(not ground) and `inferOpen`'s nominal send arm answers `.missing` rather than recording the
requirement `String ~ twice : (Integer) → α` — an atom that already exists (`Store.nom`,
`Assn.req` at a `.nom` receiver). The rung is **one arm of `inferOpen`**, and it is its own
commit because that arm changes the *per-body* verdicts too: `blocked` becomes `accept` and
`fragment-gap.py`'s third ratchet moves, which wants its own measurement.

### Costs and checks

The eight `example`s are `simp +decide` over the equation lemmas. `+decide` is what makes
them robust rather than a war with `List.contains` normalization — the pass is a `mutual`
block, so it is WF-compiled and does not reduce in the kernel, but the *decidable side
conditions* inside it do. `native_decide` remains banned (§4 norm 5).

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean,
`fragment-gap.py --self-test` all agree. Still off the default target until L265, so
`--assn` and the third ratchet cannot move; no interpreter change, so no difftest.

## L265 — `--assn-program`, the playground's third static query, and the number it actually reports

The flag, the pane, and the measurement. `Types/Program.lean` joins the default build here
(`Main.lean` imports it), which is also what makes the ratchet question live.

### `--assn` is byte-identical, verified rather than argued

`--assn`'s per-body census is a *consumed* number (`fragment-gap.py`'s third ratchet), and
L262 touched `Store` — a new field — and `Store.closeAt`, which `closeBody` calls on the
`--assn` path. The provisions are empty there, so the output cannot change; **that was
checked** by building the pre-L262 binary in a worktree at `85bdc4b` and comparing
`--assn` output over all eight slice files:

```
version.rb IDENTICAL   version/parser.rb IDENTICAL   pkg_version.rb IDENTICAL
vulns/semver.rb IDENTICAL   vulns/cvss.rb IDENTICAL   vulns/purl.rb IDENTICAL
vulns/vulnerability.rb IDENTICAL   vulns/identify.rb IDENTICAL
```

`--check` too, on three of them. Third ratchet on `/tmp/hb/brew3`: **112 defs, 17 accept,
7 pacc, 8 uncond, 85 needed, 3 oof** — unmoved. (`HANDOFF.md` records `needed: 84`; the
difference is the brew checkout, not this batch. The byte-comparison is what settles it.)

### The headline, and it is a one-liner

```
class Version; def value; 1; end; def get; value; end; end
  --check          reject / uncertified
  --assn-program   accept  ·  type Symbol  ·  under  α3 = Integer
```

The obligation on `Version` closes **empty** — the class answers its own body — so the whole
assertion is the equality the cancellation owed. This is the thing `--assn` structurally
cannot say: it hands every body a fresh store at `{}`, so the two halves never meet.

### The measurement that matters more than the headline

On the eight **real** slice files, `--assn-program` reports:

| file | verdict |
|---|---|
| `version.rb`, `pkg_version.rb` | `needed: T.class_of(Object) ~ ::Comparable` |
| `version/parser.rb` | `needed: T.class_of(T) ~ ::Helpers` |
| `vulns/vulnerability.rb` | `needed: T.class_of(Object) ~ ::Utils` |
| `vulns/semver.rb`, `vulns/cvss.rb`, `vulns/identify.rb` | `oof: casgn` |
| `vulns/purl.rb` | `oof: receiverless-send-with-block` |

**So the whole-program verdict is all-or-nothing where `--assn`'s is a gradient**, and it
stops *earlier* than the per-body census does — on the class body's own statements, which
`bodyReports` walks straight past. That is the honest shape of the query and it decides how
the two are used: `--assn`'s per-body count stays the ratchet, `--assn-program` is the
verdict beside it. Recording it here rather than letting the next session rediscover it.

It also names the next three rungs for whole-program coverage, in the order the slice wants
them: `include Comparable`'s **constant** (`Comparable` is genuinely absent from
`readableClasses` — modules fail its `noShadow` clause, checked, not assumed), **`casgn`**
(a constant *assignment*, which no rule has), and the receiverless block send.

### The JSON, and one field that is not data

`status` / `type` / `assn` / `classes` / `consts_added`, plus **`means`**: the literal string
*types under these class obligations*. It is in the payload rather than in this file because
the reading is the part a consumer gets wrong, and a verdict whose strength lives only in a
note is a verdict that will be quoted without it. `consts_added` is there for the same
reason: L264 extends the constant table, and an extension a reader cannot see is one they
cannot check.

### Checks

`lake build` (now including `Types/Program.lean`), `lake build Metatheory`,
`check-proofs.sh` axiom-clean, `fragment-gap.py --self-test` all agree, `--assn`/`--check`
byte-identical against a pre-L262 binary, playground `/assn-program` exercised end to end
against CRuby's desugarer. No interpreter change, so no difftest.

## L266 — a row added to the table at a **fixed** heap, and the guard that turns out to be unnecessary

`DeclsOk_addRow` (F1b.10) is the `def` step's form of *the table grew by one row*: the
row and the method arrive together, so its conclusion is stated at
`defineMethod h cls name md` and the new row's own obligation is discharged by the
installation. The certificate language
(`docs/semantics/certificate-language.md`, `RubyCore/Cert/`) needs the same fact with
**nothing about the heap moving** — a claimed row is not installed by anything, its
witness is supplied — and this is that lemma. It is a fact about `addRow`/`declFor`/
`DeclsOk`, so it lives in `Proof/Static/Decls.lean` and `Types/Assn.lean` rather than
in the new tree (that document's §7 norm 7: *never fork a private copy*).

### The measurement: `groundClassNames` was guarding the wrong thing

`DeclsOk_addRow` assumes `groundClassNames.contains c = false` and its central step
concludes `τr = .cls c` — *the only type a freshly added row is read at is the class
arm*. Read against a certificate that wants to declare `Integer#even?` from an RBI,
that assumption refuses the row, and the refusal is **wrong for a stated reason**:
`declFor` reads a row keyed `"Integer"` at `Ty.int`, because `tyClassNames .int =
["Integer"]`. It is the `.cls "Integer"` arm that L189's subtraction empties, and
`nomTy "Integer"` is not that arm.

So the guard is replaced by the true statement rather than kept and worked around:

```
declFor_addRow_self_inv :
  declaresName D name = false → declFor (addRow D c name σ) τr name = some decl →
    tyClassNames τr = [c] ∧ decl = σ
```

*Whatever type the new row is read at, its class list is the singleton `[c]`.* That
covers the ground arms, the class arm, and — vacuously — `.bool`, whose two names
cannot both be `c`, and the four arms whose list is empty. `DeclsOk_addRow_here` then
takes its new-row obligation quantified over exactly those types, and there is at
most one of them: `Types/Assn.lean`'s `tyClassNames_singleton_inv` says it is
`nomTy c`. So a certificate discharges the obligation with **one** `decl` atom.

Four small table lemmas fall out and are worth their names, because all four are
about `addRow`'s prepend-shadowing and each was inlined inside `DeclsOk_addRow`'s
proof: `declOf?_addRow_self`, `declOf?_addRow_ne` (freshness makes every *other*
class answer `none` at the written name), `declOf?_addRow_other` and
`declFor_addRow_other` (a *different* name does not see the row at all).

### What is cheaper at a fixed heap, and it is most of the proof

`DeclsOk_addRow` spends its second half transporting the old rows across
`defineMethod`. At a fixed heap there is nothing to transport: both resolving arms of
`EntryOk` and `IterEntryOk`'s `MissesAt` clause pass through by `rfl`, and the only
surviving obligation is the one that was never about the heap — `UserConforms`'
`infer_mono` step, which needs `SubDecls D (addRow …)`, i.e. `subDecls_addRow` at the
same freshness hypothesis. So the new lemma is a third the length of the old one and
the two do not share a proof; the *statement* `DeclsOk_addRow` proves is not an
instance of this one (its heap moves), which is why it stays where it is untouched.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean. No interpreter
change and no rule change, so `--assn`/`--check` cannot move and there is no
difftest; `DeclsOk_addRow` and every consumer of it are untouched, which the
metatheory build is what checks.

## L267 — `EntryOk` is monotone in the table, and `initiation` is parametric in it

Two generalizations of existing facts, both needed by the certificate language
(`docs/semantics/certificate-language.md`, `RubyCore/Cert/`) and both of them facts
about the standing machinery rather than about certificates — so they land in
`Proof/Static/Decls.lean` and `Proof/StaticSoundness.lean` rather than in the new
tree (that document's §7 norm 7: *never fork a private copy*).

### 1. Why L266 was not enough, and the induction that replaced it

L266 gives *a row added at a fixed heap*, one row at a time. A certificate adds
several — `Cert.table` folds `addRow` over its claims — and doing that one row at a
time is **the wrong induction**, for a reason worth recording because it is not
visible from the statement:

> the new row's obligation has to be discharged at the table the certificate *ends*
> at, because that is the table its `decl` atom in `assumes` is denoted against, and
> `EntryOk` is not antitone.

`EntryOk`'s only table-dependent arm is `UserEntryOk`, whose `UserConforms` says the
body infers at `D` and *leaves* `D`; `infer_mono` transports that from a smaller
table to a bigger one and there is no lemma the other way (nor should there be —
`declaresName` is name-global, so a bigger table refuses `def`s a smaller one
admits). So a one-row-at-a-time induction would need `EntryOk` at each intermediate
table and the hypothesis only supplies it at the last.

The induction is therefore over `declFor` at the final table: each row is *either*
one of the claims (obligation supplied) *or* one of `declsOf p`'s (obligation
transported up). Two lemmas make that work, and the second is the general form of
the second half of every `DeclsOk_*` lemma in the file:

```
EntryOk_mono       : SubDecls D D' → EntryOk D h τ n d → EntryOk D' h τ n d
DeclsOk_of_subDecls: DeclsOk D h → SubDecls D D' →
                       (∀ τ n d, declFor D τ n = none → declFor D' τ n = some d →
                          EntryOk D' h τ n d) →
                     DeclsOk D' h
```

*The old rows survive because `infer` is monotone; only the new ones owe anything.*
The four non-row clauses are free: `SubDecls` pins `consts`/`ivars`/`scopedConsts`/
`supers`/`globals` by **equality** (L195's decision, and this is the first consumer
that spends all five).

The split into old/new is clean rather than approximate, and `SubDecls` is what makes
it so: `declFor D' τ n = some d` with `declFor D τ n = some d₀` forces `d = d₀`, so
there is no third case where a row is *displaced*.

### 2. `initiation`, parametric in the table — and nothing moved

`initiation` had `declsOf p` written in at both places the table appears: the
`DeclsOk` witness and `CtlOk`'s `infer` equation. `initiation_at` takes those two as
hypotheses and `initiation` is the three-line instance.

**Nothing else in that proof was ever specific to `declsOf p`**, which is the
measurement worth keeping: `Inv` ∃-quantifies the table (F1b.8) precisely because it
changes along a run, so the initial machine's invariant is parametric in it by
construction. Every remaining line is a computation on a literal heap. `check_sound`
is unchanged and `#print axioms` still reports the same three.

That is also the answer to a question the certificate design left open: whether
carrying a *larger* table into `Inv` costs a re-proof. It does not; it costs
`DeclsOk` at that table, which is §1's obligation and nothing else.

### Checks

`lake build`, `lake build Metatheory`, `check-proofs.sh` axiom-clean. No rule change
and no interpreter change, so `--assn`/`--check` cannot move — verified
byte-identical on all eight slice files against a worktree binary at `d8b8c7c` — and
tier 0 is `992 agree, 0 disagree`, unmoved.
