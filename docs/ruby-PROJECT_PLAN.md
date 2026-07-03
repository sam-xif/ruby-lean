# Modeling the Semantics of Ruby (and Rails) in Lean

A project plan for building a mechanized, executable semantics of Ruby in Lean 4,
with Ruby on Rails as the flagship framework case study, validated by differential
testing against the reference implementation (CRuby/MRI).

---

## 1. Why this is worth doing

The goal is a **machine-checked, executable specification** of Ruby that is:

- **Accurate** — it agrees with the real interpreter on a large corpus of programs.
- **Explainable** — each observed behavior traces back to a small, readable rule.
- **Useful** — it can power tools: a semantics-aware linter, a soundness oracle for
optimizers/JITs, a foundation for verified refactorings, or a teaching artifact.

Ruby is a hard and interesting target precisely because it is *defined by its
implementation*, not by a standard anyone reads. There is an ISO standard (ISO/IEC
30170:2012) but it is thin and years behind the language people actually use, and the
prior academic semantics (§3) are on-paper, partial, and unmechanized. That gap is the
opportunity: a *mechanized, executable, and reasonably complete* model becomes the
working specification that neither the standard nor the earlier efforts delivered.

Choosing **Rails** as the framework layer is deliberate. It exercises nearly every
"hard" corner of Ruby semantics at industrial scale — metaprogramming, open classes,
`method_missing`, dynamic dispatch, DSLs, thread-local state, and heavy reflection. If
the model can explain Rails, it can explain almost anything.

---

## 2. Surface-area statistics: is the target big enough to matter?

Short answer: yes — large enough to be a serious research/engineering effort, and
still-widely-used enough that the results have real-world value, but not so sprawling
that a phased core-first approach is hopeless.

### Language & ecosystem reach

- **Ruby popularity is real but past its peak.** Ruby sits around **30th in the TIOBE
index (rating ~0.55%) as of early 2026**, down from the low-20s in early 2025 — a
mature language sliding gently, not a dead one. In the RedMonk rankings (which blend
Stack Overflow + GitHub signal) Ruby has historically placed **~9th**, reflecting a
large installed base even as new-project mindshare shifts to JS/Python.
- **Rails still runs a meaningful slice of the web.** Estimates vary widely by
methodology: SimilarTech tracks **~439k live sites**, other trackers report
**~50k–104k active domains**, and framework-market-share estimates land around
**4–5% of the web-framework category** (6th place). The spread itself is a useful fact
— Rails is embedded in long-lived, high-value production systems (GitHub, Shopify,
Stripe-adjacent tooling, Basecamp, GitLab), not throwaway sites.

### Code-surface complexity (the part that matters for a semantics)

- A study of **10 large Rails apps + their 861 gem dependencies** found **6.08M lines
across 50,865 files**, defining **625,761 methods, 32,897 classes, and 11,057
modules**. That is the *real* semantic surface a Rails-aware model must eventually
cope with.
- The Rails framework itself is a multi-hundred-thousand-LOC codebase where a single
conceptual operation (e.g. `ActiveRecord#save`) is deliberately spread across many
modules and stitched together with `super`, `included` hooks, and
`method_missing` — i.e. exactly the dynamic features that make a naive semantics
fall over.

### What the numbers tell us for scoping

1. The **core language surface is bounded**: a few dozen syntactic forms, one object
  model, one method-resolution algorithm, a fixed set of core classes. This is
   *formalizable*.
2. The **library/framework surface is effectively unbounded** (hundreds of thousands
  of methods). So the model must be **core-complete and library-extensible**, never
   "model everything."
3. Because Rails leans so hard on metaprogramming, **getting the object model and
  dispatch exactly right is the whole game** — 80% of the value is in 20% of the
   semantics, but it's a *specific* 20%.

*Sources are listed at the bottom.*

---

## 3. Prior art we should stand on

**Formal semantics of Ruby is not virgin territory — and we should say so plainly.**
There *is* prior work; what is missing is specifically a *mechanized* (proof-assistant)
semantics with metatheory, full dynamic dispatch (incl. `method_missing`), and a
framework case study. That gap is our contribution, and it is narrower and more honest
than "no formal semantics exists."

- **The Essence of Ruby** (Ueno, Fukasawa, Morihata & Ohori, APLAS 2014) is the closest
  and most important prior art. It gives a **big-step (natural) operational semantics**
  of Ruby, structured as *two orthogonal sub-calculi* — an **object calculus** and a
  **control calculus** — composed at method invocation via "oracle relations," with a
  syntactic elaboration phase from surface Ruby. It covers objects, dynamic class/method
  definition, `super`, visibility, modules/mix-ins, constants, `eval`/`class_eval`, and
  — its centerpiece — **blocks and non-local control** (`yield`/`break`/`next`/`return`)
  modeled with ML-style *generative exceptions*. It is **executable** via a Standard-ML
  reference interpreter and was **differentially tested against CRuby 1.9.3** (a narrow
  slice: 26/28 hand-selected block-and-jump cases). It even surfaced ambiguities in the
  ISO/JIS standard. Crucially for us, it is **on-paper + SML — not mechanized in any
  proof assistant, has no metatheory (no determinism/soundness proofs), does not model
  `method_missing`, and is explicitly incomplete** (Symbols, globals, multiple
  assignment, first-class Array/Hash deferred). Methodologically it descends from Guha
  et al.'s *The Essence of JavaScript* (ECOOP 2010); a related line is James & Sabry's
  continuation encoding of `yield`, which Ueno et al. deliberately reject as not matching
  Ruby's primitives. **Our object-model/control split (artifacts 01–04) is convergent
  with theirs; our additions are mechanization + adequacy proofs + `method_missing`/full
  dispatch + the Rails slice + large-scale differential testing.**
- **The Ruby Intermediate Language / RIL** (Furr, An, Foster & Hicks, DLS 2009) is
  *infrastructure, not semantics*: a hand-written GLR parser (dypgen, Ruby 1.8) +
  normalized OCaml IR that makes evaluation order and implicit constructs explicit. It is
  the reference design for our **desugaring/normalization layer** (artifact 00 §5), and
  our desugaring *catalog* is substantially RIL's, independently re-derived and cited —
  operators→method calls, `unless`→`if`, `#{}` interpolation → `to_s`+`concat`, bare
  `rescue` → `rescue StandardError`, implicit `super` args made explicit, linearization
  via temporaries. Even our desugar round-trip oracle (§6, claim C2) is a *formalized,
  strengthened* version of RIL's "unparse the IR and re-run the interpreter's test suite."

  But the goals diverge sharply, and nearly every design difference follows from it —
  **RIL is built to make Ruby tractable for *static analysis*; we build to *faithfully
  model the runtime semantics* and prove things about it.** Consequences:
  - *Core shape.* RIL **linearizes maximally** (one side-effecting action per statement,
    temporaries everywhere) — the CFG-friendly form a **dataflow analysis** wants. We keep
    a **minimal, dispatch-centric core** ("everything is a message send", node-addition a
    red flag) and **linearize only where rendering forces it** — the shape a small-step
    **interpreter + proofs** wants. Same technique (linearization), opposite dial: flatten
    for analysis vs. compress for a compact operational relation
    (see `docs/semantics/linearization.md` §7).
  - *Dynamic features.* RIL handles `eval`/`require` by **profile-guided rewriting**
    (record observed strings, rewrite to `case` dispatch) — clever but **unsound in
    general** — and does **not** model `method_missing`/mixins at the IR level (deferred to
    its type layer). We treat arbitrary `eval` as **explicitly out of scope** rather than
    approximate it, and make dynamic **dispatch/`method_missing`/mixins the center** of the
    model (artifact 02) — faithfully modeling the dynamic parts *is* our contribution.
  - *Validation.* RIL argues correctness **empirically** (corpus parse, unit tests,
    unparse-and-re-run). We use **differential testing** (observation function + eval-order
    trace + coverage ratchet) and target **mechanized proofs** (adequacy/metatheory).
  - *Substrate.* RIL is a deployed OCaml analysis front-end with its own GLR parser; ours
    is a Ruby+Prism prototype (reusing CRuby's own parse decisions) feeding an eventual
    **Lean** model, against which this prototype becomes a differential oracle.

  Where RIL is ahead: it is a *complete, deployed* front-end covering far more surface
  syntax than our current fragment, and its profile-guided `eval` handling is a genuine
  pragmatic idea we deliberately forgo (unsoundness-for-analyzability is a real tradeoff,
  not an oversight). Its clients — **DRuby/Diamondback Ruby** and **DRails** (static typing
  for Rails) — also prefigure our Rails ambition.
- **Ruby type-system work** — **RDL** (Foster et al., Tufts/UMD) and **Sorbet** (Stripe)
  — gives (a) a battle-tested inventory of core-library signatures and (b) evidence that
  the dynamic parts resist static reasoning, informing where our *dynamic* semantics adds
  value beyond types.
- **Mechanized-semantics templates from other languages** are what we actually
  transplant to Lean: **KJS** (K-framework JavaScript, PLDI'15) and **KCC** (C11),
  **KRust**, the K-framework Python semantics, and **JSCert/JSRef** (a Coq relation with
  an extracted interpreter *proven correct* and validated on test262). These supply the
  "executable operational semantics + proof + differential testing against the reference
  implementation" playbook — the piece the Ruby-specific work above never had.
- **Ruby's own tooling** gives us free infrastructure: the `ruby/spec` executable
  specification suite, `prism`/`ripper` for parsing, and MRI's own test suite as
  differential-testing corpora.

---

## 4. Scope: what we model, and in what order

We define a **core calculus, `RubyCore`**, and treat everything else as either
*desugaring into it* or *a modeled library on top of it*.

**In-core (Phase 1–2):**

- Object model: everything-is-an-object, classes as objects, singleton (eigen)classes,
the metaclass chain.
- Method resolution / MRO: ancestor chain with modules, `prepend`, `include`, `extend`,
and `super`.
- Message send as the single primitive; `method_missing` fallback.
- Variables & scope: local, instance (`@x`), class (`@@x`), global (`$x`), constants
and constant lookup (lexical + ancestor).
- Blocks, procs, lambdas, `yield`; the closure/binding distinction.
- Control flow: conditionals, loops, `return`/`break`/`next`/`redo`/`retry`,
exceptions (`raise`/`rescue`/`ensure`), non-local exit semantics.
- Mutable heap, object identity, `freeze`, truthiness.

**Modeled-as-library (Phase 3):** core classes with subtle semantics —
`Integer`/`Float` (incl. bignum promotion), `String` (encoding-aware),
`Array`, `Hash` (insertion order, default procs), `Symbol`, `Range`, `nil`/`true`/`false`.

**Metaprogramming (Phase 3–4):** `define_method`, `send`/`public_send`, `instance_eval`/
`class_eval`, `respond_to?`, `included`/`inherited`/`method_added` hooks,
`const_missing`, `Module#prepend`. This is the Rails-enabling layer.

**Explicitly out of scope (documented as "trusted/unmodeled"):**

- C extensions and FFI (modeled as opaque/axiomatized where Rails needs them).
- True concurrency/`Ractor` memory model, GC timing, `ObjectSpace`, `Fiber` scheduling
fine-grain — model a deterministic single-thread execution first.
- `eval` of arbitrary strings — support only where it desugars to modeled constructs.

**Rails as case study (Phase 5):** we do *not* model all of Rails. We pick a
**vertical slice** that stresses the semantics: ActiveSupport core extensions (open
classes on `String`/`Hash`), a minimal ActiveRecord (`method_missing`-driven attribute
accessors, dynamic finders, `belongs_to`/`has_many` class-macro DSL), and the
ActionController `before_action` callback DSL. The claim we want to defend:
*"the model explains why this Rails code does what it does, rule by rule."*

---

## 5. What the Lean model looks like

### 5.1 Architecture

```
  Ruby source
      │  (parse: prism/ripper → JSON, ingested into Lean)
      ▼
  Surface AST  ──desugar──▶  RubyCore AST
                                  │
                                  ▼
        ┌─────────────────────────────────────────┐
        │  Small-step operational semantics         │
        │  step : Config → Option Config            │  (Lean, decidable, #eval-able)
        │  Config = (Expr/Continuation, Heap, Env,  │
        │            CallStack, Exception state)    │
        └─────────────────────────────────────────┘
                                  │
             ┌────────────────────┴───────────────────┐
             ▼                                          ▼
   Executable interpreter                   Inductive relation  step_rel
   (run : Fuel → Config → Result)           (for proofs & theorems)
             │                                          │
             ▼                                          ▼
   Differential testing vs CRuby         Metatheory (determinism, progress,
                                          soundness lemmas, refactoring proofs)
```

Two co-existing definitions are the key design choice:

1. **An executable, fuel-bounded interpreter** (`def eval`) that Lean can `#eval` — this
  is what differential testing runs against. Fast to iterate, gives us the "executable
   spec."
2. **An inductive step relation** (`inductive Step : Config → Config → Prop`) — the
  *definition of record* for proofs.

We then prove the interpreter **sound and complete w.r.t. the relation**
(`eval` returns `v` ↔ `Step`* reaches `v`). This gives us both machine-runnable and
machine-provable semantics without divergence between them.

### 5.2 Core data types (illustrative Lean sketch)

```lean
-- Values live in a heap; almost everything is a reference to an object.
abbrev ObjId := Nat

inductive Value
  | ref  (id : ObjId)          -- ordinary objects (incl. String, Array, ...)
  | int  (n : Int)             -- immediate-ish; Integer incl. bignum
  | flt  (x : Float)
  | sym  (s : String)
  | bool (b : Bool)
  | nil

structure Object where
  klass    : ObjId                       -- class is itself an object
  ivars    : Std.HashMap String Value
  eigen    : Option ObjId                -- singleton class, lazily created
  payload  : Payload                     -- builtin state: string bytes, array elems…

structure MethodDef where
  params : Params                        -- required/optional/splat/kw/block
  body   : Expr
  owner  : ObjId                         -- defining module (for `super`)
  visibility : Visibility

structure ClassObj where
  superclass : Option ObjId
  ancestors  : List ObjId                -- precomputed MRO incl. prepend/include
  methods    : Std.HashMap String MethodDef
  consts     : Std.HashMap String Value

structure Heap where
  objs   : Std.HashMap ObjId Object
  next   : ObjId

-- A running configuration.
structure Config where
  focus  : Frame                         -- expr under evaluation + continuation
  heap   : Heap
  frames : List Frame                    -- call stack (self, locals, block, lexical scope)
  raised : Option Value                  -- in-flight exception, drives rescue/ensure
```

### 5.3 The one rule that matters most: method dispatch

Every interesting Ruby behavior funnels through message send. The dispatch algorithm —
walk the receiver's ancestor list (which already encodes `prepend`/`include`), find the
first matching method, else retry with `method_missing` — *is* the semantics of Rails'
metaprogramming. Sketch:

```lean
def lookup (h : Heap) (recv : Value) (name : String) : Option (ObjId × MethodDef) := do
  let klass ← classOf h recv          -- singleton class first, then real class
  (ancestorsOf h klass).findSome? fun m =>
    (methodsOf h m)[name]?.map (m, ·)

def send (h : Heap) (recv : Value) (name : String) (args : List Value) : StepResult :=
  match lookup h recv name with
  | some (owner, m) => invoke h owner m recv args
  | none            => send h recv "method_missing" (Value.sym name :: args)
```

`super` is just `lookup` restricted to ancestors *after* `owner`. `define_method`,
`class_eval`, dynamic finders, and Rails' `belongs_to` all reduce to *mutating the
`methods`/`ancestors` maps in the heap* — no new evaluation rules required. That is the
payoff of getting the object model right: metaprogramming becomes ordinary heap
mutation, not special magic.

### 5.4 Desugaring keeps the core small

Surface Ruby has enormous syntactic redundancy. We shrink `RubyCore` by desugaring:
`attr_accessor` → pair of `define_method`s; string interpolation → `to_s` sends + concat;
operators (`a + b`, `a[i]`, `a[i]=`) → sends (`+`, `[]`, `[]=`); `&&`/`||` → conditionals;
keyword args → a normalized `Params` shape; `for` → `each` + block. Each desugaring is a
Lean function we can also test in isolation.

---

## 6. Differential testing: proving the model is *accurate* and *explainable*

The model is only credible if it agrees with real Ruby. Differential testing is the
core validation loop. Formal proofs (§7) come *after* we trust the model empirically.

### 6.1 The oracle harness

```
  test program (Ruby source)
        │
        ├──────────────▶  CRuby / MRI  ──▶  observable behavior_ruby
        │                                    (stdout, return value repr,
        │                                     exception class+msg, final
        │                                     ivar/heap projection)
        │
        └──────────────▶  Lean interpreter ──▶ observable behavior_lean
                                                    │
                                    compare(behavior_ruby, behavior_lean)
                                                    │
                              ┌─────────────────────┴──────────────────┐
                           AGREE                                     DISAGREE
                     (record as passing            (minimize → triage: model bug?
                      corpus, add to CI)             desugar bug? out-of-scope feature?
                                                     → file rule-level defect)
```

**Observation model.** We can't compare internal states directly (different reps), so we
define a canonical **observation function** on both sides: serialize a chosen projection
— program output, the `inspect`/`to_s` of the result, exception class + message, and a
normalized dump of reachable objects' ivars. Ruby side produces it via a small harness
script; Lean side produces it from the final `Config`. Equality is on these
observations, making "same behavior" precise and pinning down what "explainable" means:
*for every observation, there is a derivation in the step relation that produces it.*

### 6.2 Where the test programs come from (four sources, increasing realism)

1. **Handwritten unit oracles** — one per rule, targeting a single semantic feature
  (e.g. "does `ensure` run when `rescue` re-raises?"). These double as regression tests
   and as living documentation of each rule.
2. `**ruby/spec` and MRI's own test suite** — thousands of executable examples that
  already encode intended behavior; run the subset that lands in our modeled fragment.
   Coverage of this suite is our headline "how much of Ruby do we explain" metric.
3. **Grammar-based fuzzing** — a generator that emits *well-typed-ish* RubyCore programs
  (respecting our modeled fragment) to find disagreements we didn't think to write.
   Use **delta-debugging / test-case minimization** to shrink any failure to a minimal
   reproducer before triage.
4. **Rails vertical-slice scenarios** — the Phase-5 payoff: real (if trimmed) Rails
  idioms (`has_many`, `before_action`, an ActiveRecord-style model) run end-to-end
   through both, proving the framework-level claim.

### 6.3 Metrics that make "accurate and useful" measurable

- **Agreement rate** on each corpus (target: 100% on modeled fragment; disagreements are
either bugs to fix or features to explicitly mark out-of-scope).
- **Fragment coverage**: % of `ruby/spec` examples that fall in-scope *and* pass.
- **Explainability**: every passing behavior has a concrete step-relation derivation;
we can emit a **proof/trace** ("here is why `x` happened, rule by rule").
- **Fuzzer disagreement rate over time** — should trend to zero as the model matures;
a rising rate flags newly-modeled features with bugs.

### 6.4 Version pinning & determinism

Pin a specific CRuby version (semantics drift between minor versions — Hash ordering,
keyword-arg rules, `Integer#/` etc.). Run the reference in a container for
reproducibility. Force deterministic execution (single-thread, disable GC-observable
behavior, fixed hash seed) so observations are stable.

---

## 7. From "tested" to "proven": metatheory & tooling payoff

Once the interpreter is trusted empirically, the inductive semantics unlocks proofs that
a test suite can never give:

- **Determinism** of the (single-threaded) step relation.
- **Interpreter ↔ relation adequacy** (the soundness/completeness theorem in §5.1).
- **Verified refactorings**: prove that a source-to-source transformation (e.g.
`attr_accessor` expansion, or a specific Rails-safe refactor) preserves observable
behavior — a genuinely useful tool for a refactoring engine.
- **Optimizer/JIT soundness oracle**: use the model as the ground truth a YJIT-style
optimization must refine.
- **Explainability tooling**: a "semantic debugger" that shows the derivation tree for
why a program produced its result — the concrete deliverable behind the
"explainable description" goal.

---

## 8. Phased roadmap


| Phase                                 | Goal                                                       | Key deliverable                                                                               | Exit criterion                                                |
| ------------------------------------- | ---------------------------------------------------------- | --------------------------------------------------------------------------------------------- | ------------------------------------------------------------- |
| **0. Foundations**                    | Repo, parser bridge, harness skeleton                      | prism/ripper → JSON → Lean AST; CRuby-in-container oracle; observation function on both sides | round-trip a trivial program through both engines             |
| **1. Pure core**                      | Expressions, control flow, exceptions, locals              | `Step` relation + fuel interpreter for `RubyCore` minus objects                               | 100% agreement on handwritten arithmetic/control-flow oracles |
| **2. Object model**                   | Classes, MRO, dispatch, `super`, blocks/procs              | The dispatch engine of §5.3; adequacy theorem (interp ↔ relation)                             | passes `ruby/spec` method-resolution + closures subset        |
| **3. Core library + metaprogramming** | Modeled builtins; `define_method`, `send`, `*_eval`, hooks | library layer + reflection ops as heap mutation                                               | fuzzer disagreement rate near zero on modeled fragment        |
| **4. Differential-testing at scale**  | Fuzzing + minimization + coverage dashboard                | CI that runs `ruby/spec`/MRI subset + generated corpus nightly                                | published fragment-coverage number                            |
| **5. Rails vertical slice**           | ActiveSupport ext + mini-ActiveRecord + callback DSL       | end-to-end Rails idioms explained rule-by-rule                                                | the "explains Rails" scenarios pass with derivation traces    |
| **6. Payoff tooling**                 | Verified refactoring + semantic-debugger demo              | one proven behavior-preserving transform; trace visualizer                                    | demo artifact + writeup                                       |


---

## 9. Key risks and mitigations

- **Metaprogramming explosion.** *Mitigation:* the object-model-as-heap-mutation design
(§5.3) keeps new features from adding evaluation rules; invest heavily in Phase 2.
- **"Model everything" trap.** *Mitigation:* explicit trusted/unmodeled boundary (§4);
library methods are opt-in, driven by what the Rails slice actually calls.
- **Version drift in the oracle.** *Mitigation:* pin CRuby, containerize, force
determinism (§6.4).
- **Executable vs. relational semantics diverging.** *Mitigation:* the adequacy theorem
is a Phase-2 gate, not an afterthought.
- **Parser fidelity.** *Mitigation:* reuse Ruby's own parser (prism) rather than writing
one; desugaring is the only bespoke front-end code, and it's independently tested.
- **Concurrency/GC nondeterminism** leaking into observations. *Mitigation:* single-
threaded deterministic execution first; concurrency is a separate future project.

---

## 10. One-paragraph summary

Build `RubyCore`, a small desugaring target, and give it a dual Lean semantics — a
fuel-bounded executable interpreter for testing and an inductive step relation for
proofs — proven adequate to each other. Get the object model and method dispatch
*exactly* right so that Ruby's metaprogramming (and therefore Rails) reduces to ordinary
heap mutation rather than special rules. Validate accuracy and explainability by
differential testing against a pinned CRuby via a canonical observation function, fed by
handwritten oracles, the `ruby/spec` suite, and a grammar fuzzer with delta-debugging.
Prove the payoff with a Rails vertical slice that the model can explain rule-by-rule,
plus a verified refactoring and a derivation-trace "semantic debugger" as the useful,
explainable artifacts.

---

## Sources

Ruby / Rails usage & market share:

- [Ruby on Rails Usage Statistics — BuiltWith Trends](https://trends.builtwith.com/framework/Ruby-on-Rails)
- [Ruby on Rails Market Share — SimilarTech](https://www.similartech.com/technologies/ruby-on-rails)
- [Ruby on Rails market share — Enlyft](https://enlyft.com/tech/products/ruby-on-rails)
- [Usage Statistics and Market Share of Ruby for Websites — W3Techs](https://w3techs.com/technologies/details/pl-ruby)
- [Ruby on Rails Statistics and Facts: 2025 — Bacancy](https://www.bacancytechnology.com/blog/ruby-on-rails-statistics-and-facts)

Language popularity:

- [Ruby sinking in popularity, buried by Python — TIOBE (InfoWorld)](https://www.infoworld.com/article/4142618/ruby-sinking-in-popularity-buried-by-python-tiobe.html)
- [TIOBE Index April 2025 — TechRepublic](https://www.techrepublic.com/article/news-tiobe-index-april-2025-programming-languages/)
- [2025 Stack Overflow Developer Survey — Technology](https://survey.stackoverflow.co/2025/technology)

Codebase size / complexity:

- [The Shape of 6M Lines of Ruby — Stefan Marr](https://stefan-marr.de/2020/12/shape-of-large-source-code-ruby/)
- [How We Estimate the Size of a Rails Application — FastRuby.io](https://www.fastruby.io/blog/rails/code-quality/how-we-estimate-rails-application-size.html)
- [Perusing the Rails Source Code — Alex Kitchens](https://alexkitchens.net/rails-source-code)

Prior art (semantics & Ruby types):

- [An Executable Structural Operational Formal Semantics for Python — arXiv:2109.03139](https://arxiv.org/pdf/2109.03139)
- [KRust: A Formal Executable Semantics of Rust — arXiv:1804.10806](https://arxiv.org/pdf/1804.10806)
- [Executable formal semantics for the POSIX shell — arXiv:1907.05308](https://arxiv.org/pdf/1907.05308)
- [State of Sorbet — sorbet.org](https://sorbet.org/blog/2019/05/16/state-of-sorbet-spring-2019)

