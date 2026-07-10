# Lean Model Sketch — mechanizing RubyCore, informed by Essence-of-Ruby and RIL

> **Status:** design sketch (2026-07-07), the bridge from the quasi-formal artifacts
> (00–06) to Lean 4 code. Written after a close read of the two anchor papers
> (`../../ruby_papers/essence_of_ruby.pdf`, `../../ruby_papers/ruby_intermediate_language.pdf`);
> this file records exactly what we adopt, what we reject, and the resulting Lean
> skeleton. Companion to PROJECT_PLAN §5 (architecture) and §3 (the prior-art survey
> whose claims this file operationalizes).
>
> **Execution started (2026-07-07, same day):** the L0 slice of §3–§4 is implemented in
> [`../../lean/`](../../lean/README.md) — `Machine`/`stepFn`/`run` + SUT executable,
> wired into the difftest engine (`--sut lean`). Deviations from this sketch so far:
> the fuel interpreter landed *before* `inductive Step` (to meet the engine on day
> one, §4's own argument); the heap uses a dense `Array Object` rather than AssocList;
> and an unforeseen component proved load-bearing — oracle-generated CRuby method/
> constant name tables (`CRubyNames.lean`) so partial modeling gates as `Unsupported`
> instead of mis-dispatching (a lookup that misses an *unmodeled* builtin must not
> fall through to a user method or a guessed NoMethodError).

---

## 1. What we take from *The Essence of Ruby* (Ueno et al., APLAS'14)

Their semantics is big-step, ours is small-step, so nothing transfers verbatim — but
four of their ideas are load-bearing for the mechanization:

### 1.1 Generative jump targets (their deepest insight)

Their centerpiece: `return`/`break`/`next` destinations **cannot be statically
labeled** — the same `break` in a recursive method-with-block targets a *different*
activation each time (their `foo(1)` example printing `E1..E5 B4 B3 B2 L2 L1`). They
model this with ML-style *generative exceptions*: a fresh tag per method call (for
`return`), per block creation (for `break`), per yield (for `next`); a jump raises the
tag, the matching handler catches it, and a *dead* tag (its dynamic extent already
exited) is `LocalJumpError`.

**Adoption, translated to small-step:** in a frame-stack machine, generativity is
*frame identity*. We give every activation frame a unique `FrameId`; a `Proc` value
captures the `FrameId`s it returns/breaks to; a jump **unwinds the stack searching for
its target id**, running `ensure` handlers as it pops (artifact 04's rules); a target
id no longer on the stack *is* `LocalJumpError`. Tag liveness = frame presence — one
mechanism, no meta-level exception machinery. (Their SML interpreter *failed* the
detached-`Proc`-`break` test precisely because they didn't track effective tag sets —
§5 "Error Handling". The frame-stack formulation gets that case right by
construction.)

### 1.2 The variable store: locals are references, not values

In their control calculus, locals live in a **variable store** `S : Ref ⇀ Value` and
environments map names to *references* (`E : Var ⇀ Ref`) — because Ruby blocks share
their defining scope's locals **mutably** (`x=1; [1].each{ x=99 }; x == 99`, artifact
03 §2 [V]). Artifact 04 encodes this as "the block captures the defining frame *by
reference*", which is fine on paper but not directly expressible in inductive data.

**Adoption:** frames live in a **frame store** (`FrameId ⇀ Frame`) inside the
configuration; the *stack* is a list of `FrameId`s; a block frame holds its captured
frame's id and free-variable lookup walks that chain, mutating locals *in the store*.
This one mechanism (frame store + `FrameId`) delivers **both** of Essence's stores at
once — their variable store `S` (shared mutable locals) *and* their exception-tag
context `T` (generative jump targets). That unification is the sketch's central data
decision.

### 1.3 Orthogonal-calculi modularity as an interface discipline

Their object/control split with "oracle relation" composition is elegant but we won't
mirror it as two literal relations — a single small-step relation over one
configuration is simpler to mechanize and to run. What we keep is the **interface
discipline** it proves possible: all object-model operations (`classOf`, `ancestors`,
`methods`, `lookup`, ivar/const access) are *pure functions on the heap*, defined in
their own module with their own lemmas, and the step relation touches the heap only
through them. That is where their "oracle" boundary lands in Lean: a module boundary,
not a relation boundary. It also keeps artifact 01–02 (object model) provable
independently of artifact 04 (control).

### 1.4 Their corner-case checklist and reflection observation

- §5 lists exactly what a full account needs: Symbols as values, `undef` state,
  globals as one more store, `self` as an implicit parameter, multiple assignment via
  Array primitives. Our desugar already discharges several (massign, symbols); the
  rest are on the fragment roadmap. We inherit the list as a completeness check.
- Their reflection observation — meta-level state kept *in the heap* makes reflection
  primitives trivial — is our artifact-01 stance ("classes are ordinary heap
  objects"), independently confirmed. `def`-destination subtleties (their
  class-module list `C`) correspond to our frame's `defmod`/`cref` pair.

### What we reject from Essence, and why

- **Big-step.** It hides effect order and interleaving, makes `ensure`-during-unwind
  awkward (they thread `handle` premises through every rule), cannot express
  divergence except by omission, and gives no purchase for the bounded/concolic
  checking the workspace user-stories need. Artifact 00 §1 already fixed small-step;
  the papers do not move that.
- **Generative exceptions as the mechanism.** Right *concept*, wrong *substrate* for
  Lean: we get generativity from `FrameId`s (§1.1) without a meta-exception layer.
- **Their scope gap.** No `method_missing`, no mechanization, no metatheory, 26/28 on
  28 hand-picked tests. Full dispatch is our artifact 02 center; validation is the
  standing difftest engine.

## 2. What we take from *RIL* (Furr et al., DLS'09)

RIL is front-end infrastructure, and its catalog is already absorbed into our desugar
harness (PROJECT_PLAN §3 does the detailed accounting). For the *Lean model
specifically*, three things matter:

1. **The pipeline split is validated.** RIL demonstrates a maintainable
   parse→normalize→small-IR pipeline whose output round-trips through the reference
   interpreter. Our Lean core therefore consumes **RubyCore produced by the existing
   Ruby+Prism harness** — Lean does not parse Ruby, and the desugar stays a separately
   difftested component (artifact 06). The harness↔Lean interface is a serialized
   RubyCore AST (JSON), versioned so either side can reject a mismatch.
2. **Eval-order obligations are semantics, not just desugaring.** RIL §3.2's examples
   (`a().f = b().g` evaluates a,b,f=; `a().f, x = b().g` evaluates b,g,f= — order
   *differs*; `ensure` value discarded; fall-through `if` yields `nil`) must hold in
   the *step relation's* argument-evaluation rules, not only in the front end. These
   become early adversarial seeds for the Lean SUT.
3. **The linearization dial stays where artifact `linearization.md` §7 set it:**
   RubyCore keeps expressions compact (small relation, proof-friendly) and linearizes
   only where jumps-in-operand-position force it — RIL's maximal flattening is the
   analysis-side extreme we deliberately don't need. And RIL's profile-guided `eval`
   rewriting stays rejected: `eval` is out of fragment (`Unsupported`), not
   approximated.

## 3. The Lean skeleton

Two co-existing definitions (PROJECT_PLAN §5.1): `inductive Step : Config → Config →
Prop` is the definition of record; a fuel interpreter `stepFn : Config → StepResult`
is what runs. The adequacy theorems (`stepFn` sound & complete w.r.t. `Step`,
determinism of `Step`) are the first metatheory milestones.

```lean
-- RubyCore/Syntax.lean — artifact 00 §4, verbatim as an inductive
inductive Expr
  | lit (l : Lit) | self'
  | lvar (x : Name) | lasgn (x : Name) (e : Expr)
  | ivar (x : Name) | iasgn (x : Name) (e : Expr)      -- cvar/gvar/const later
  | send (recv : Expr) (m : Name) (args : List Expr) (blk : Option BlockArg)
  | yield' (args : List Expr)
  | def' (m : Name) (ps : Params) (body : Expr)
  | seq (a b : Expr) | if' (c t e : Expr) | while' (c body : Expr)
  | begin' (body : Expr) (rescues : List Rescue) (ens : Option Expr)
  | ret (e : Option Expr) | brk (e : Option Expr) | nxt (e : Option Expr)
  -- class/module/sclass/defs/lambda … added with the fragment

-- RubyCore/Heap.lean — artifact 01; pure ops, own lemmas (§1.3)
abbrev ObjId := Nat
abbrev FrameId := Nat
inductive Value | ref (o : ObjId) | int (n : Int) | sym (s : Name) | bool (b : Bool) | nil

structure Object where
  klass : ObjId; ivars : AssocList Name Value
  eigen : Option ObjId; payload : Payload            -- builtin state (String/Array/…)

structure Heap where objs : AssocList ObjId Object; nextObj : ObjId
-- classOf, ancestors (MRO), methodsOf, lookup : pure functions here (artifact 02)

-- RubyCore/Machine.lean — artifact 00 §2 + §1.1/§1.2 above
structure Frame where
  self    : Value
  locals  : AssocList Name Value
  defmod  : ObjId
  cref    : List ObjId
  blk     : Option Value            -- block passed to this activation
  captured : Option FrameId         -- block frames: defining frame (lvar chain walks this)
  retTo   : FrameId                 -- generative `return` target (method frame = itself)
  kind    : FrameKind               -- method | block | toplevel

structure Config where
  ctl    : Control                  -- focus expr / value being returned / unwinding(jump, target)
  kont   : List Kont                -- continuation frames (arg positions, seq-rest, handlers…)
  stack  : List FrameId             -- activation stack, innermost first
  store  : AssocList FrameId Frame  -- THE frame store (Essence's S and T at once, §1.2)
  heap   : Heap
  raised : Option Value             -- in-flight exception (drives rescue/ensure, artifact 04)

-- RubyCore/Step.lean : inductive Step : Config → Config → Prop   (definition of record)
-- RubyCore/Interp.lean : def stepFn (c : Config) : StepResult
--                        def run (fuel : Nat) (c : Config) : RunResult
-- RubyCore/Obs.lean    : obs — stdout trace, result inspect, (excClass, msg); artifact 00 §2
-- Main.lean            : stdin RubyCore-JSON → run → obs-JSON on stdout (the SUT executable)
```

Notes pinned by the papers:

- **Dispatch** (artifact 02) is one rule: `lookup` walks eigenclass-then-MRO; miss
  re-sends `method_missing` with the symbol prepended — *inside the same rule set*,
  not a stuck state. This is the headline divergence from Essence (they omit it).
- **Jumps**: `ret/brk/nxt` put the machine into an unwinding control state carrying
  the target `FrameId`; unwinding pops `kont`/`stack` entries, *running `ensure`
  konts* as it passes them; reaching the target resumes with the carried value;
  exhausting the stack without finding it raises `LocalJumpError` (§1.1).
- **AssocList over HashMap** initially: extensional reasoning is simpler and the
  fragment's programs are small; swap for `Std.HashMap` behind the Heap interface if
  `#eval` throughput ever matters.
- **Determinism target:** `Step` should be deterministic by construction (no rule
  overlap); `theorem step_deterministic` is milestone metatheory, and `stepFn`'s
  existence is the constructive proof.

## 4. Fragment strategy and difftest integration

The Lean model meets the differential engine **on day one**, not after coverage grows:

- `Main.lean` implements the difftest **SUT contract** (`Observation | Unsupported`):
  an out-of-fragment RubyCore node → exit 3 with the node name as the `Unsupported`
  reason, exactly like the desugar SUT adapter. The engine's fragment gate was built
  for this.
- **L0 fragment = difftest tier-1 vocabulary** (literals, locals, send-desugared
  operators, `if`/`seq`, bounded `while`, `def`/call with required params, `puts`,
  arrays/hashes/interp as sends, `begin/rescue`) — because the tier-1 generator plus
  752 in-fragment bootstraptest cases give an instant, large, shrinking-enabled
  corpus against CRuby. `puts`/`inspect` for the observation are the only builtin
  method entities L0 needs.
- **L1 = blocks + jumps + `ensure`** (artifact 04; the Essence test battery §7 —
  their 28 block/jump cases become seeds) — this exercises §1.1/§1.2 and is where the
  model earns its keep. **L2 = object-model core** (class/module/sclass/defs, ivars,
  `super`, visibility; matches the desugar M3 fragment). **L3 = `method_missing` +
  `define_method` + `class_eval`** — the thesis milestone: metaprogramming lands as
  heap mutation with *zero new step rules*; tier-3 `metaprogramming`/`dispatch`
  corpus becomes runnable.
- The ratchet discipline carries over: track in-fragment agreement per corpus
  (bootstraptest / tier-1 / tier-3) exactly as `bin/coverage` does for the desugar,
  and let `Unsupported` reasons drive fragment growth, as they already do there.

## 5. Open questions carried into mechanization **[?]**

- **Frame-store GC.** The store grows monotonically (dead frames are unreachable but
  retained). Fine for difftest-sized programs; decide later whether to prove a
  reachability-based collection sound or just not care (fuel bounds everything).
- **`String`/`Array`/`Hash` payloads.** How much of the builtin behavior is `Payload`
  primitive vs. RubyCore-defined methods? Start primitive (Essence did; their §7 shows
  it suffices for conformity runs), migrate to in-language definitions only when a
  proof needs them.
- **Serialized-AST fidelity.** The harness renders RubyCore for CRuby round-trips; the
  Lean JSON export is a second consumer of the same structure — guard with a
  cross-check (render → parse → desugar → export ≟ export) in the harness test suite.
- **Where `redo`/`retry` land** in the unwinding control state (artifact 04 defines
  them; L1 scope decision).
- **Fuel vs. co-divergence.** `run fuel` conflates "diverges" with "fuel exhausted";
  the difftest timeout side conflates similarly. Artifact 05 §7's co-divergence check
  is deferred but the `RunResult` type should distinguish `outOfFuel` from `stuck`
  from day one so it stays possible.
