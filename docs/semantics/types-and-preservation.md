# RubyCore Semantics — Sorbet's Type System and a Type-Preservation Roadmap

> **Status:** research artifact, expected to grow. It has two jobs: (A) collect what a
> *formalizer* needs to know about **Sorbet**, the type system we intend to model, and (B)
> survey how **type preservation / soundness** is proved in the literature, so a
> Ruby+Sorbet preservation theorem over our small-step semantics can borrow the right
> machinery. §C connects both to the existing `Step` relation and metatheory PoC
> (`../../lean/RubyCore/Proof/`).
>
> Evidence tags follow the house convention (`README.md`): **[V]** verified against CRuby,
> **[D]** from documentation / the literature (Sorbet docs or a cited paper), **[?]** open
> question to settle during mechanization. Everything in Parts A and B is **[D]** unless
> noted; each claim traces to a source in §D. Claims marked **[✗→]** are corrections of a
> plausible-but-false statement that the research pass actively refuted — recorded so we
> don't reintroduce the error.

---

## A. Sorbet's type system, for a formalizer

Sorbet is Stripe's gradual type checker for Ruby. Two framing facts set the whole shape:

- **It is gradual by construction.** Types are adopted incrementally, file-by-file or
  team-by-team [D: sorbet.org/docs/gradual]. Absence of a signature is *not* an error — a
  method with no `sig` is assumed to take and return `T.untyped` [D: /docs/untyped].
- **It is unsound by design, and bridges the gap at runtime.** A program that typechecks
  can still fail at runtime; Sorbet's answer is not static soundness but **runtime `sig`
  enforcement** (§A.5) plus escape hatches (§A.3) [D: /docs/gradual, /docs/runtime]. For a
  formalizer this is the single most important design fact: the "soundness" object of
  interest is a *runtime* invariant maintained by inserted checks, not a static
  subject-reduction property of the surface language.

### A.1 The type grammar (what to mechanize)

A first-cut abstract syntax of Sorbet types, assembled from the docs:

```
τ ::= C                       -- a class/module constant (nominal), e.g. Integer, String
    | T.untyped               -- the dynamic/unknown type (the gradual boundary, §A.5)
    | T.nilable(τ)            -- ≡ T.any(NilClass, τ)                    [D: /docs/union-types]
    | T.any(τ, …)             -- union
    | T.all(τ, …)             -- intersection
    | T.proc.params(…).returns(τ)   -- function/block type
    | [τ, …]                  -- tuple type
    | {k: τ, …}               -- shape/record type
    | T.class_of(C)           -- the singleton (class object) type, vs. instance type C
    | T.self_type             -- the receiver's own class
    | T.attached_class        -- in singleton-method context, the instance type produced
    | T.type_parameter(:U)    -- a method-generic type variable
    | G[τ, …]                 -- application of a generic class G to type args
```

Notable definitional facts, all useful because they *reduce the grammar*:

- `T.nilable(x)` is **literally** `T.any(NilClass, x)`, and `T::Boolean` is
  `T.any(TrueClass, FalseClass)` (Ruby has no single Boolean class) — so nilable and
  boolean are not primitive constructors, just unions [D: /docs/union-types].
- On a union, Sorbet permits **only methods common to all members** until flow-sensitivity
  (§A.2) narrows it in a branch [D: /docs/union-types].
- **`T::Struct`** — typed records via a `prop` DSL (mutable, typed `attr_accessor`) and
  `const` DSL (immutable, typed `attr_reader`); constructors are keyword-only and every
  prop is required unless given `default:`/`factory:` or made nilable (nilable ⇒ implied
  `default: nil`) [D: /docs/tstruct]. **Runtime-check asymmetry worth modeling:**
  constructors and setters are checked at runtime, but **getters are not** (plain
  `attr_reader`, for speed) — a deliberate soundness/performance trade [D: /docs/tstruct].
- **`T::Enum`** — each enum value is a **singleton instance of the enum class**
  (`Suit::Spades.is_a?(Suit)`), so an enum is an ordinary class type; Sorbet does
  **exhaustiveness checking** over enum cases, with `T.absurd` giving compile-time proof
  that all cases are handled [D: /docs/tenum]. (These singletons carry mutable state
  observed program-globally — a heap fact for our object model, artifact 01.)

### A.2 Flow-sensitive (occurrence) typing

Sorbet "models control flow through a program and uses it to track types more accurately"
[D: /docs/flow-sensitive]. A `T.nilable(String)` is `String` in the truthy branch and
`NilClass` in the else; narrowing is driven by `is_a?`, `kind_of?`, `instance_of?`,
`nil?`, `Module#===`, and boolean/negation structure, and understands `case`/`when`, not
just `if` [D: /docs/flow-sensitive]. Three constraints matter for a model:

1. **Locals only.** Narrowing applies to local variables, *not* to method-call results —
   Sorbet can't assume a method returns the same value on two calls. Workaround: bind to a
   temporary local first [D: /docs/flow-sensitive]. (This is exactly occurrence typing's
   "object" restriction — narrow a path, not an arbitrary expression.)
2. **`respond_to?` does not narrow** — knowing a method exists says nothing about its
   signature [D: /docs/flow-sensitive].
3. **Soundness hinges on the guards not being overridden** — if user code redefines
   `is_a?` etc., the analysis is unsound [D: /docs/flow-sensitive]. A model that takes
   these predicates as primitive is implicitly assuming this.

`T.reveal_type(e)` prints Sorbet's inferred (narrowed) type at a point — the tool we'd use
to build an oracle for a flow-sensitive typing judgment [D: /docs/flow-sensitive]. This is
the same discipline formalized (and proved sound) as **occurrence typing** in Typed
Racket (§B.4) — the closest existing mechanization to what Sorbet does here.

### A.3 The soundness stance and the escape hatches

Sorbet is explicit that a passing typecheck does not warrant full confidence, and offers
opt-outs [D: /docs/gradual]. The type-assertion / escape-hatch family, stated *correctly*
(the static-vs-runtime split is the crux):

| Form | Static | Runtime | Note |
|------|--------|---------|------|
| `T.let(e, τ)` | checked | checked | fully dual-checked assertion [D: /docs/type-assertions] |
| `T.cast(e, τ)` | **trusted, not proved** | **checked** (raises `TypeError`) | **[✗→]** *not* "converts without runtime validation" — Sorbet "cannot statically guarantee … but will check the invariant dynamically on every invocation" [D: /docs/type-assertions] |
| `T.must(e)` | narrows away `nil` | checked (raises if `nil`) | for nils Sorbet can't see statically [D: /docs/type-assertions] |
| `T.unsafe(e)` | disables checks | none | defined as `T.let(e, T.untyped)` — pure static opt-out [D: /docs/type-assertions] |
| `T.bind(self, τ)` | trusted | checked | like `T.cast`, unchecked statically, checked at runtime [D: /docs/type-assertions] |
| `T.assert_type!`, `T.absurd` | checked | checked | also dual-checked [D: /docs/type-assertions] |

**[✗→]** Correction to a tempting simplification: `T.let` is **not** the *only* fully-sound
(static+runtime) assertion — `T.assert_type!` and `T.absurd` are dual-checked too
[D: /docs/type-assertions]. The clean invariant to model is: **`T.unsafe` is the one form
with no runtime check; everything else that is static-unsound is at least runtime-checked.**
That is the whole soundness architecture in one line — and it is what makes a *runtime*
preservation statement (§C) the right target rather than a static one.

### A.4 Strictness levels

A per-file `# typed:` sigil, five levels; sigils affect **static analysis only**, never
runtime behavior [D: /docs/static]:

- `ignore` — file not read at all.
- `false` — **(default)** only syntax, constant-resolution, and `sig`-correctness errors.
- `true` — full type errors (nonexistent methods, arity, arg types).
- `strict` — every method/constant/instance-var needs an explicit signature/type
  (Sorbet stops implicitly inserting `T.untyped`).
- `strong` — **no `T.untyped` values at all** (the strongest guarantee; beta) [D: /docs/static].

For a formalizer this is a **staged fragment ladder**: `strong` is (approximately) the
fully-static sublanguage where a classical soundness theorem could hold; `false`/`true`
are the genuinely gradual regime. Note signatures in a `# typed: false` file are still
parsed and enforced when called from a stricter file — the boundary is per-*call*, not
per-file [D: /docs/static].

### A.5 The gradual boundary and runtime enforcement

`T.untyped` is the dynamic type: Sorbet has no knowledge of it and permits any call with
any args [D: /docs/untyped]. It coerces **bidirectionally** — any value ⇒ `T.untyped`, and
any `T.untyped` ⇒ any type — which is precisely the "`?`/`dyn`" boundary type of gradual
typing (§B.5) [D: /docs/untyped]. Absence of a `sig` makes every param and the return
`T.untyped`, so **the untyped boundary is "no signature"** [D: /docs/untyped].

The bridge is **runtime `sig` enforcement**: adding a `sig` *wraps* the method beneath it
in a new method that validates argument types against the sig, calls the original, and
validates the return value [D: /docs/runtime, blog.jez.io/runtime-type-checking]. Checks
are **on by default**, configurable per-sig via `.checked(:always | :tests | :never)` and
globally via `T::Configuration` [D: /docs/runtime]. The stated rationale is telling: static
predictions can be wrong, so runtime checks make violations "fail loudly and immediately,
rather than silently" and let existing tests + production monitoring build confidence in
the annotations [D: /docs/runtime, blog.jez.io]. **This wrapping is exactly a
method-boundary contract** — the same mechanism the gradual-typing literature analyzes as
"guarded" enforcement (§B.5), and it maps directly onto our object model (a `sig` is heap
mutation that replaces a method-table entry with a checking wrapper — artifact 02 §6).

**Caveat for modeling:** generic type parameters are **erased at runtime** (both class and
method generics), so generics are validated *only* statically and get *no* runtime backstop
[D: /docs/generics]. Any runtime-preservation argument therefore cannot lean on generics.

### A.6 Generics, variance, inference

- **Generic classes:** `type_member` (scoped to instance methods) and `type_template`
  (singleton methods), both requiring `extend T::Generic` [D: /docs/generics].
- **Generic methods:** `type_parameters(:U)` in the sig, referenced as
  `T.type_parameter(:U)` [D: /docs/generics].
- **Variance:** invariant (default — subtyping ignored), covariant (`:out`, output
  positions), contravariant (`:in`, reversed) [D: /docs/generics].
- **Bounds:** `upper` (subtypes of bound), `lower` (supertypes), `fixed` (both, forbidding
  explicit type args) [D: /docs/generics].
- **Inference** is local + flow-sensitive (§A.2); it does *not* do whole-program inference
  in the DRuby sense (§B.4) — signatures are the interface. `T.reveal_type` is the inference
  oracle.

### A.7 What this buys the mechanization

The formalizable core of Sorbet is: a **nominal** subtype lattice over Ruby's class graph,
closed under **union/intersection/nilable**, with a **top-ish dynamic type `T.untyped`** at
the gradual boundary, **flow-sensitive narrowing** on locals via a fixed predicate set, and
**runtime method-boundary contracts** as the enforcement mechanism. That last item is why
the literature to imitate is *gradual/contract* soundness (§B.5), not classical static
soundness — although the fully-static (`# typed: strong`, generics-erased) sublanguage is a
legitimate first target for a classical theorem (§C).

---

## B. How type preservation / soundness is proved — a survey

Preservation ("subject reduction") is almost always half of a two-part **syntactic**
argument; the other half is progress. Below, each entry notes **the exact theorem shape**
and **what transfers** to a gradual, everything-is-a-send, classes-as-heap-objects setting.

### B.1 The classic syntactic method — Wright & Felleisen (1994)

The founding recipe: give the semantics as a **rewriting/reduction system with evaluation
contexts**, then prove soundness from a **subject-reduction** result [D: inco.1994.1093].

- **Preservation (subject reduction):** `if Γ ⊢ e₁ : τ and e₁ → e₂ then Γ ⊢ e₂ : τ`
  [D: inco.1994.1093].
- Interestingly, Wright–Felleisen complete soundness **not** with a progress lemma but by
  defining **"faulty" expressions** (those with a type-erroneous redex) and proving *faulty
  ⇒ untypable*, combined with a **Uniform Evaluation** lemma [D: inco.1994.1093]. (The
  now-standard "progress + preservation" packaging is the common modern presentation
  [D: sigplan blog].)
- Two soundness strengths to name precisely: **Weak** — `⊢ e : τ ⇒ eval(e) ≠ wrong`;
  **Strong** — `⊢ e : τ ∧ eval(e) = v ⇒ v ∈ V_τ` (the value lands in the type's value set)
  [D: inco.1994.1093].
- **Modular/extensible:** proved for Functional ML, then *reused* for references,
  exceptions, and first-class continuations [D: inco.1994.1093] — the property we want,
  since we extend RubyCore head-by-head.

**Transfers:** our semantics is *already* small-step with an explicit machine — this is the
native setting for subject reduction. The "extend the language, reuse the proof" modularity
is exactly the L0→L1→L2 ladder discipline.

**A caution the literature raises about *syntactic* soundness** [D: sigplan blog]: it says
nothing about programs using unsafe features (it just *excludes* them from the well-typed
fragment — cf. `Obj.magic`, Rust `unsafe`), and gives no guarantee that data abstraction
actually holds (Java reflection can smash private invariants while staying syntactically
sound). Both caveats bite us directly — Ruby's `send`/`eval`/`method_missing`/reflection
*are* the language. This is the argument for eventually wanting **semantic** soundness
(`Γ ⊨ e : τ`, "behaves safely when executed", via a logical-relation/adequacy + fundamental
theorem) as the stronger target [D: sigplan blog]. Keep syntactic as the near-term goal,
semantic as the aspiration.

### B.2 Object-oriented: Featherweight Java (Igarashi, Pierce, Wadler, 2001)

The canonical compact OO soundness proof — "FJ bears the same relation to Java as
λ-calculus to ML" [D: fj-toplas]. Nondeterministic small-step reduction, **three** compute
rules (field access, method invocation, cast) + congruence rules [D: fj-toplas]. Soundness
is Wright–Felleisen style:

- **Subject Reduction (2.4.1):** `if Γ ⊢ e : C and e → e' then Γ ⊢ e' : C'` for some
  `C' <: C` — i.e. **type preserved up to subtyping** (the type may *shrink*)
  [D: fj-toplas]. This "up to subtyping" is essential for any language with subsumption —
  and Ruby is all subtyping.
- **Type Soundness (2.4.3):** a well-typed `e` reducing to a normal form yields either a
  value of a subtype, or an expression **stuck at a failed downcast** — so *the only stuck
  states are cast failures* [D: fj-toplas].
- **The "stupid cast" lesson** [D: fj-toplas]: a small-step reduction of a well-typed
  cast-free term can produce an *ill-typed* cast, so FJ must **admit "stupid casts"**
  (rule `T-SCast`) purely so subject reduction holds. Omitting this is precisely the bug
  that made ClassicJava's published proof wrong. **General principle: closure of the type
  system under the step relation may force auxiliary/runtime-only typing rules** — a trap
  to expect for our `Step`.

**Transfers:** "preservation up to subtyping"; "the only stuck states are `X`" as the shape
of the soundness statement (for us `X` = a dynamic `TypeError` from a failed runtime sig
check, or a genuine `NoMethodError`); and the store-typing generalization (§B.3) needed
once we add mutation — FJ itself is functional (implicitly-final fields) and so *doesn't*
need a heap, which is exactly the gap our object model creates.

### B.3 OO + heap + gradual: the TypeScript formalizations

Two complementary papers, both directly relevant because they add a **heap** and a
**gradual/unsound reality** — our exact situation.

**"Understanding TypeScript" (Bierman, Abadi, Torgersen, ECOOP 2014)** [D: springer 978-3-662-44202-9_11]:
- Isolates a safe fragment **safeFTS** and proves **subject reduction over a big-step
  semantics with heap types** `Σ` (locations → types): `if Σ ⊨ ⟨H,L,e⟩ : T and
  ⟨H,L,e⟩ ⇓ ⟨H',r⟩ then ∃ Σ' ⊇ Σ, T' with Σ' ⊨ ⟨H',r⟩ : T' and T' <: T`.
- The **store-typing technique** is the transferable core: extend typing to runtime
  configurations via `Σ`, with heap well-formedness `H ⊨`, scope/heap compatibility
  `H,L ⊨`, and `Σ`-compatibility `Σ ⊨ H`; the heap type only *grows* (`Σ ⊆ Σ'`)
  [D: springer]. **This is the recipe for a classes-as-heap-objects preservation proof** —
  and note our metatheory PoC *already* proved the monotone-heap fact `Σ` needs (§C).
- TS is gradual in the Siek–Taha sense with `any` as boundary, but — unlike most gradual
  systems — **erases types with no runtime checks**, which is *why* it's unsound; assignment
  compatibility through `any` is even non-transitive (`string ~ any ~ boolean` but not
  `string ~ boolean`) [D: springer]. Contrast Sorbet, which *does* insert runtime checks
  (§A.5) — so Sorbet is closer to the *sound* gradual systems below than to TS.

**"Safe & Efficient Gradual Typing for TypeScript" (Rastogi, Swamy, Fournet, Bierman,
Vekris, POPL 2015)** [D: safets.pdf]:
- Makes TS **sound** via a "Safe" compile mode: stricter static checks + **residual runtime
  checks** compiled into plain JS, using per-object **RTTI** added only as needed, with
  "differential subtyping" (minimal RTTI to add) and an "erasure modality" (erased-type
  code needs no RTTI, runs full speed) [D: safets].
- **Core theorem is a forward simulation (Thm 1):** inserted checks (1) catch any dynamic
  type error and (2) don't alter the semantics of type-safe code; this yields a
  progress-shaped **Type Safety** corollary and implies subject reduction for well-typed
  programs [D: safets]. ~15% overhead on ~120kLOC, and the checks *found real bugs*
  [D: safets].

**Transfers (this is the closest analogue to Sorbet+our project):** the simulation framing
— *the checked (runtime-enforced) execution simulates the type-safe one* — is very close to
how we should state Sorbet's runtime-sig guarantee, and it dovetails with the
forward-simulation machinery already chosen for the Rails/POSIX vertical relations
(`co-semantics.md` §5, `../../relating-language-and-substrate.md`). RTTI-as-needed ≈
Sorbet's runtime checks attached at `sig` boundaries.

### B.4 Dynamic-language & Ruby-specific work

**DRuby / PRuby (Furr, An, Foster, Hicks — OOPSLA 2009)** [D: druby-oopsla09]:
- Static type **inference** for Ruby (union & intersection types, optional/vararg args,
  self types, object/field types, parametric polymorphism, mixins, tuples, first-class
  method types), working by translating Ruby → **RIL**, an analyzable subset (our
  `desugar`/RubyCore is the same move — RIL is cited in `PROJECT_PLAN`).
- **Core soundness (TinyRuby):** small-step semantics, and `Type Soundness (Thm 3)`:
  `if ⊢ e and ⟨∅,∅,e⟩ → ⟨M,P,r⟩ then r is a value or blame ℓ` — never `error` [D: druby].
  Note the **three-outcome** shape (value / blame / diverge), the gradual signature.
- **The Ruby lesson we cannot dodge:** to be sound, DRuby **forbids `eval`, `send`,
  `method_missing`** in well-typed programs — they can't be checked statically [D: druby].
  PRuby's fix is **runtime profiling + source-to-source transformation** replacing dynamic
  constructs with analyzable ones plus dynamic checks (`safe_eval`) that assign blame
  [D: druby]. It also infers locals flow-sensitively but deliberately avoids a
  "must-be-defined" analysis for methods, assuming any syntactically-present method is
  available everywhere and using dynamic checks otherwise [D: druby]. **This is the central
  tension for us:** the very features that make Ruby Ruby (and make Rails possible —
  `method_missing`, `*_eval`) are the ones static typing must either forbid or push to
  runtime. Sorbet's answer (runtime sigs; `T.untyped` for the dynamic parts) is PRuby's
  answer in production form.

**Typed Scheme / Typed Racket (Tobin-Hochstadt & Felleisen)** [D: arxiv 1106.2575]:
- Introduced **occurrence typing** (§A.2's ancestor) and **mechanically proved it sound**.
- **Preservation with a twist:** typing judgments carry a **propositional "visible
  predicate"** component: `⊢ e : τ ; ψ`, and `Preservation (Lemma 1)`: reduction preserves
  type *up to subtyping* **and** the predicate *up to a sub-predicate relation*
  (`τ' <: τ and ψ' <:? ψ`), paired with a standard Progress lemma [D: arxiv]. This is the
  template for making flow-sensitivity survive subject reduction.
- **A proof-engineering trick to steal:** to make *every intermediate term* typeable (which
  Wright–Felleisen requires), they add auxiliary "proof-theoretic" rules (e.g.
  `T-IfFalse`) used **only** in the proof, then show they're unnecessary for the final
  ground-type result [D: arxiv]. (Same species as FJ's stupid casts.)
- **Gradual/incremental basis:** a typed sister-language with *identical semantics* to the
  untyped one, so values flow freely and scripts convert module-by-module [D: arxiv] — the
  conceptual model under Sorbet's file-by-file adoption.
- **Mechanization:** soundness done in **Isabelle/HOL (nominal package, ~5000 lines)**,
  with **PLT Redex (~500 lines)** used *alongside* for executable exploration and for
  *visualizing subject-reduction counterexamples* [D: arxiv]. This is a **prove-and-
  differentially-test workflow** — the same philosophy as our harness (build the executable
  check next to the proof).

### B.5 Gradual-typing soundness specifically (the most relevant bucket)

Because Sorbet is gradual with runtime enforcement, this is the literature whose theorem
statements we should imitate.

**Gradually Typed Lambda Calculus type safety (Siek & Taha)** [D: dagstuhl SNAPL 2015]:
`if ⊢ e : T then e ⇓ v (⊢ v : T), or e ⇓ blame ℓ, or e ⇑` — the **three-outcome** safety
statement: a well-typed program never hits an *untrapped* error, though *trapped* (blame)
errors may be pervasive. A gradual language must also be a **conservative extension** of
both the fully-static and fully-dynamic languages (Thms 1–2) [D: dagstuhl].

**Refined Criteria / the Gradual Guarantee (Siek, Vitousek, Cimini, Boyland, SNAPL 2015)**
[D: dagstuhl]:
- The key new criterion: **changing only the *precision* of annotations must not change
  behavior** (except a less-precise program may trap fewer errors). `Gradual Guarantee
  (Thm 5)`: if `e ⊑ e'` (e' less precise) and `⊢ e:T`, then `⊢ e':T'` with `T ⊑ T'`; if
  `e ⇓ v` then `e' ⇓ v'` with `v ⊑ v'`, and divergence is preserved; conversely `e'`
  either matches `e` or blames [D: dagstuhl].
- The order is the **precision relation `⊑`** (a.k.a. naive subtyping), with the unknown
  type `?` least precise (`T ⊑ ?`), extended structurally/congruently [D: dagstuhl]. The
  GTLC satisfying the gradual guarantee was **mechanized** [D: dagstuhl].
- **Transfers:** `T.untyped` is Sorbet's `?`; the gradual guarantee is the *right property
  to state about adding/removing Sorbet annotations* (does putting a `sig` on a method
  change behavior? — only by trapping more errors). This is testable in our harness *today*
  via `obs⁺` (run with and without sigs, compare) before any Lean.

**"Well-Typed Programs Can't Be Blamed" (Wadler & Findler, ESOP 2009)** [D: blame.pdf]:
- The **blame calculus**: an explicitly-typed core with casts `⟨T ⇐ S⟩^p s` carrying source
  type `S`, target `T`, and blame label `p`; runtime reduction does dynamic checks and
  assigns blame to `p` (positive) or `p̄` (context, negative) on failure. Unifies
  Siek–Taha gradual, Flanagan hybrid, and dependent dynamic types [D: blame].
- **Soundness is textbook Wright–Felleisen:** `Preservation (Prop 6)`: `Γ ⊢ s : T ∧ s → t
  ⇒ Γ ⊢ t : T`; `Progress (Prop 7)`: a well-typed `s` is a value, steps, or steps to
  `⇑p` (blame) [D: blame]. Note it drops subsumption from term typing to get **unicity of
  type (Prop 1)** and **decidability (Prop 2)** [D: blame].
- **The Blame Theorem (Cor 11):** blame never lands on the more-typed side of a cast —
  upcasts (`S <: T`) can't be blamed; only downcasts/cross-casts can. Enabled by
  **factoring subtyping** into positive & negative (`S <: T iff S <:⁺ T and S <:⁻ T`)
  [D: blame]. **Transfers:** this is the precise sense in which Sorbet's *typed* code is
  protected from *untyped* code — when a runtime sig check fails at a boundary, blame is on
  the untyped caller. If we model runtime sigs as casts, this is the theorem to aim for.

**Enforcement strategies — guarded vs transient** [D: arxiv 1902.07808]:
- **Guarded/proxy** (Typed Racket): wrap higher-order values in contracts/chaperones at the
  boundary — matches Sorbet's method-wrapping `sig`s (§A.5).
- **Transient** (Vitousek et al.): insert pervasive **first-order** checks at every call
  site and function entry, checking only a value's *top-level* constructor, no proxies
  [D: arxiv 1902.07808]. Supports **open-world soundness** (sound even under unmoderated
  interaction with untranslated code) — **mechanized in Coq for "Anthill Python"** (models
  Reticulated Python) [D: arxiv, dl.acm 3009837.3009849]. Transient solves blame *without*
  proxies [D: dl.acm]. Costs up to ~6× on CPython, motivating a **provably-sound
  redundant-check-removal** inference (subtyping + "check" constraints) [D: arxiv].
- **Why this matters for us:** Sorbet erases generics (→ no runtime check there, §A.6) but
  wraps methods (guarded), so it is a *hybrid*. Modeling it precisely means being explicit
  about which checks are first-order (arg/return class checks) and which are absent
  (generics, struct getters, `T.unsafe`).

**The performance/soundness debate** — context, not a proof technique:
- "Is sound gradual typing dead?" (Takikawa et al., POPL 2016) introduced the
  fully-untyped→fully-typed **2ⁿ configuration lattice** measured over 20 Typed Racket
  benchmarks [D: cambridge JFP]. **[✗→] authorship note:** the follow-up "Sound gradual
  typing: only mostly dead" (OOPSLA 2017) is by **Bauman, Bolz-Tereick, Siek,
  Tobin-Hochstadt** (not Greenman & Migeed as one metadata record stated); it shows the
  overhead is *not fundamental* — a Pycket tracing JIT removes >90% of it by JIT-optimizing
  the chaperone/impersonator machinery [D: dl.acm 3133878]. Bottom line: soundness's cost
  is an implementation matter, and Sorbet's default-on runtime checks are a pragmatic point
  on that curve, not a theoretical obstacle.

### B.6 Mechanization techniques (Lean/Coq/Isabelle)

- **Store typing `Σ`** (locations → types), heap well-formedness, and monotone `Σ ⊆ Σ'` —
  the standard way to do preservation with a mutable heap (TS §B.3, and every
  imperative-language soundness proof). **This is the technique our proof will be built on.**
- **Auxiliary runtime-only typing rules** to keep intermediate terms typeable (FJ stupid
  casts §B.2; Typed Racket proof-theoretic rules §B.4) — expect to need these.
- **Nominal representation of binders** (Isabelle nominal package, §B.4) — Lean 4 analogue:
  either de Bruijn or a locally-nameless encoding; our current model sidesteps this by
  using string-keyed frames (`../../lean/RubyCore/`), which is fine for an executable
  interpreter but will need care in the relation.
- **Executable model beside the proof** (PLT Redex + Isabelle §B.4; and Safe TS's
  simulation §B.3) — *this is precisely our architecture already*: the fuel interpreter and
  difftest SUT are the "Redex" half, the `inductive Step` + adequacy is the "Isabelle" half
  (`../../lean/RubyCore/Proof/`). We are unusually well-positioned to run this workflow.
- **Semantic soundness / logical relations** (`Γ ⊨ e : τ`, §B.1) — the heavier hammer that
  can reason about encapsulated unsafe code; the right long-term tool for Ruby's reflective
  features, but not the place to start.

---

## C. Implications for this project

### C.1 What "preservation" even means here — pick the runtime statement

The current metatheory PoC (`../../lean/RubyCore/Proof/`) has an `inductive Step` over an
untyped control-core fragment, and its only "preservation" so far is **heap monotonicity**
(`Step.heap_monotone` — the heap only grows; ObjIds never reused). **There is no typing
judgment yet.** Adding one is the whole task. The literature says the target should *not* be
naive static preservation, because Sorbet is deliberately unsound statically (§A.3). The
three honest options, in order of increasing ambition:

1. **Static preservation on the fully-typed sublanguage** (`# typed: strong`, no
   `T.untyped`, generics erased-but-monomorphic). Classical Wright–Felleisen subject
   reduction, *up to subtyping* (FJ §B.2): `⊢ m : τ ∧ Step m m' ⇒ ⊢ m' : τ'` with
   `τ' <: τ`, over a **store typing `Σ`** (TS §B.3) that extends our already-proven monotone
   heap. **Recommended first target** — smallest, and the machinery (`Σ`, subsumption,
   auxiliary runtime rules) is exactly the transferable core of §B.
2. **Gradual type safety with `T.untyped` and runtime sigs** (the real Sorbet). State it as
   the **three-outcome** theorem (§B.5): a well-typed config runs to a value of its type,
   or **raises a `TypeError` at a runtime sig check** (the "blame" outcome), or diverges —
   *never* silently reaches a genuinely stuck / wrong state. Model a `sig` as a
   boundary **cast** (blame calculus §B.5) inserted by heap mutation (§A.5), and aim for the
   **blame theorem** (typed code is never blamed) as the confinement-flavored payoff.
3. **The gradual guarantee** (§B.5): adding/removing `sig`s changes behavior only by
   trapping more errors. **Testable in the harness *now*** via `obs⁺` (run a program with
   and without its sigs; compare observations) — a cheap de-risking experiment before any
   Lean, in the exact spirit of the desugar round-trip and `co-semantics.md` §6.2.

### C.2 The everything-is-a-send / classes-as-heap-objects angle

Our central bet reshapes the proof:

- **One dispatch rule** (artifact 02 §3) means preservation has essentially **one
  interesting case** — `send` — plus congruence. The typing rule for `send` must look up the
  receiver's method type in the heap (the method table *is* the class object), so the
  **typing judgment is heap-relative from the start**: `Σ; Γ ⊢ e : τ`, and well-typed heaps
  `Σ ⊨ H` must say "each method-table entry has a body matching its `sig`." This is the
  store-typing recipe (§B.3) specialized to method tables.
- **Metaprogramming = heap mutation** (artifact 02 §6) is the DRuby wall (§B.4) in our
  favor *and* against us: against, because `define_method`/`*_eval` mutate the very `Σ` the
  proof quantifies over — a well-typed-heap invariant can be *broken* mid-execution; in our
  favor, because we already have the vocabulary for this — it is the **same `escape` /
  invariant-breaking-step device** as `co-semantics.md` §5.3 and
  `../../bounded-effect-checking.md` ("a metaprogramming backdoor is a heap delta"). A
  mutation that installs a method violating an existing `sig` is a *type* `escape`, and the
  runtime sig check is what catches it — the reason the *runtime* statement (§C.1 option 2)
  is the sound one to prove.
- **Runtime sig wrapping is our `obs`-visible enforcement**: because a failed check raises a
  Ruby `TypeError` that the observation function already records (artifact 05 §3), the
  "blame" outcome of the safety theorem is a *directly differential-testable* event —
  the Safe-TypeScript simulation shape (§B.3) fits our harness natively.

### C.3 Concrete next steps (cheapest first, no Lean needed for 1–2)

1. **Gradual-guarantee `obs⁺` probe** — take existing bootstraptest programs, generate a
   sig-stripped variant, and check observations agree (modulo fewer trapped errors). Wires
   into the difftest engine as a metamorphic relation; validates that Sorbet's runtime
   checks behave as the theory predicts *on real Ruby* before we formalize anything.
2. **Executable typing oracle** — use `srb`/`T.reveal_type` as an oracle for a draft typing
   judgment (mirrors how `desugar` was validated against a CRuby round-trip, artifact 06):
   generate the type Sorbet infers, compare to a hand-written `⊢ e : τ` checker. Measures
   the true size of the type grammar (§A.1) we must model.
3. **`Σ`-typing + static preservation on L0** (§C.1 option 1) — add `Ty`, `TyEnv`,
   `StoreTy`, a `HasType` relation, and `⊢ m : τ` over the *current* control-core fragment,
   proving `Step` preserves it up to subtyping. Reuse `Step.heap_monotone` as the `Σ ⊆ Σ'`
   lemma. This is the first real theorem and slots directly into `../../lean/RubyCore/Proof/`.
4. **Introduce `send` typing + method-table well-formedness**, then extend to `T.untyped`
   and the runtime-sig cast (§C.1 option 2), stealing FJ's stupid-cast / Typed-Racket
   proof-theoretic-rule trick (§B.2, §B.4) for intermediate typeability.

### C.4 Open questions [?]

- **[?]** Which Sorbet subtype rules to take as primitive vs. derived (esp. the `T.untyped`
  bidirectional/non-transitive compatibility, §A.5, cf. TS §B.3) — settle against `srb`.
- **[?]** Do we model generics at all in the first pass, given runtime erasure (§A.6) means
  they contribute nothing to a *runtime* preservation statement? (Lean toward: no — defer.)
- **[?]** Exact blame/`TypeError` normalization in `obs` so the "blame" outcome is
  distinguishable from a genuine `NoMethodError` in differential testing.
- **[?]** Whether to pursue semantic soundness (§B.1) for the reflective core long-term, or
  stay syntactic and quarantine reflection behind `T.untyped` (the DRuby/PRuby move, §B.4).

### C.5 Which typing discipline — extrinsic, with store typing over the machine

> The full catalog of judgments and rules to implement is a separate artifact,
> [`type-judgments.md`](type-judgments.md). This subsection records the *decision* and the
> *shape*; that artifact is the *reference spec*.

**The fork.** There are two ways to introduce types (see the survey for who does which):

1. **Extrinsic (Curry-style):** terms/values stay untyped; a *separate* relation
   `Δ; Γ ⊢ e : τ` assigns types over the existing syntax, and preservation is a **theorem**.
2. **Intrinsic (Church-style):** only well-typed terms exist as objects (`Expr τ` indexed by
   type); preservation is true *by construction*. This is the "encode values with type info
   and evolve types over execution" reading.

A third axis — **runtime type information (RTTI) / cast-carrying values** (Safe TypeScript
§B.3, blame calculus §B.5, transient §B.5) — threads type info through *execution*, but only
as an *enforcement* mechanism, with the metatheory still extrinsic.

**Decision: extrinsic, layered over the existing untyped `Step`.** Every real-language work
surveyed in Part B is extrinsic; intrinsic type-indexed syntax appears only in mechanization
*tutorials*, never for a language with subtyping + mutation + gradual boundaries. It is
essentially forced here:

- **The interpreter must stay untyped — it is the difftest SUT.** The fuel interpreter is
  validated against CRuby, which runs untyped Ruby (`T.untyped`, no-sig methods, reflection).
  An `Expr τ` interpreter can't run gradual code and would fork the model from the SUT,
  destroying the trust architecture. The type layer must be *purely additive* — it changes
  nothing that runs.
- **Sorbet is gradual + unsound-by-design + runtime-enforced (§A.3, §A.5).** The interesting
  theorem is the *runtime* three-outcome statement (§C.1 option 2), which inherently relates
  two separate things (the type discipline and the untyped execution) — i.e. extrinsic.
- **Classes are heap objects that mutate (central bet).** A method table's type changes as
  the program runs (`define_method`, open classes) — there is no stable index to hang an
  intrinsic type on. Extrinsic **store typing `Δ` (≙ `Σ`)** handles this: `Δ` grows
  monotonically and re-typing after a mutation is a proof obligation, not a type error.

The Option-2 instinct is not wrong — it just belongs to the **runtime sig-enforcement
layer**: a `sig` is heap mutation installing a boundary check whose failure is the observable
`TypeError`. That is the RTTI axis (transient/guarded), and it is tied back to the static
discipline by a **forward simulation** — the same machinery already chosen for the
Rails/POSIX vertical relations (`co-semantics.md` §5).

**The shape.** Because `Step` is an *abstract machine* (`Ctl` + kont stack + heap), not a
reduction relation, preservation is over **configurations**, so we type the whole machine
state, and store typing `Δ` extends the monotone-heap fact we already proved
(`Step.heap_monotone`):

```lean
inductive Ty | cls (c : ObjId) | untyped | uni (ts : List Ty) | inter (ts : List Ty)
             | proc (params : List Ty) (ret : Ty) | selfTy   -- §A.1 grammar

Sub        (Δ : StoreTy) : Ty → Ty → Prop      -- static subtyping (transitive)
Consistent (Δ : StoreTy) : Ty → Ty → Prop      -- gradual boundary (`~`, NOT transitive)
StoreTy    -- Δ ≙ Σ: typeOf : ObjId → Option Ty ; classOf : ObjId → Option ClassTy (sigs)
StoreTy.mtype  (Δ) (recv : Ty) (m : String) : Option MethSig   -- mirror of Heap.lookup

HasType  (Δ : StoreTy) : TyEnv → Expr → Ty → Prop    -- the engine, one rule per Expr head
KontOk   (Δ : StoreTy) : List Kont → Ty → Ty → Prop  -- kont stack : hole ⇒ answer
ConfigTy (Δ) (m : Machine) (ans : Ty) : Prop         -- CtlOk ∧ KontOk over m.ctl / m.kont
StoreOk  (Δ) (h : Heap) : Prop                        -- Δ ⊨ H (heap realizes Δ)

theorem preservation :                               -- FJ §B.2 + Understanding-TS §B.3 shape
  StoreOk Δ m.heap → ConfigTy Δ m ans → Step m m' →
  ∃ Δ', Δ.extends Δ' ∧ StoreOk Δ' m'.heap ∧ ConfigTy Δ' m' ans
```

**Two load-bearing design commitments** (the reason this is smaller than a from-scratch OO
calculus):

- **Nominal subtyping *is* the existing ancestors walk.** `Sub Δ (.cls a) (.cls b)` iff `b`
  is an ancestor of `a` — subtyping is a *view of the class heap* (`Heap.ancestors`), not new
  machinery.
- **`send` typing needs `mtype` = a store-typing mirror of `Heap.lookup`.** Static and
  dynamic method resolution walk the same ancestry; that parallel is exactly what makes the
  `send` case of preservation go through. Since everything is a send, `send` is the one
  interesting typing rule and the one interesting preservation case.

And the running theme of §B–§C made concrete: **it is not just subtyping.** `Sub` (transitive,
static) and `Consistent` (non-transitive, the `T.untyped` boundary) are *separate* relations;
`join`/`⊔` (typing an `if`) and `narrow` (flow-sensitivity, §A.2) are *separate*
lattice/dataflow ingredients the typing rules call. See [`type-judgments.md`](type-judgments.md)
for the complete rule set and the implementation staging.

---

## D. Sources

Sorbet (primary — official docs at sorbet.org, plus a Sorbet-team blog):
`/docs/gradual`, `/docs/untyped`, `/docs/runtime`, `/docs/type-assertions`, `/docs/static`,
`/docs/flow-sensitive`, `/docs/union-types`, `/docs/generics`, `/docs/tstruct`,
`/docs/tenum`, `/docs/quickref`; `blog.jez.io/runtime-type-checking/` (Jake Zimmerman).

Literature (primary papers):
- Wright & Felleisen, *A Syntactic Approach to Type Soundness*, Inf. & Comp. 1994 — `doi:10.1006/inco.1994.1093`.
- Igarashi, Pierce & Wadler, *Featherweight Java*, TOPLAS 23(3):396–450, 2001 — `cis.upenn.edu/~bcpierce/papers/fj-toplas.pdf`.
- Bierman, Abadi & Torgersen, *Understanding TypeScript*, ECOOP 2014 — `doi:10.1007/978-3-662-44202-9_11`.
- Rastogi, Swamy, Fournet, Bierman & Vekris, *Safe & Efficient Gradual Typing for TypeScript*, POPL 2015 — `goto.ucsd.edu/~pvekris/docs/safets.pdf`.
- Furr, An, Foster & Hicks, *Profile-Guided Static Typing for Dynamic Scripting Languages* (DRuby/PRuby), OOPSLA 2009 — `cs.umd.edu/projects/PL/druby/papers/druby-oopsla09.pdf`.
- Tobin-Hochstadt & Felleisen, *The Design and Implementation of Typed Scheme* — `arxiv.org/pdf/1106.2575`.
- Siek & Taha; Siek, Vitousek, Cimini & Boyland, *Refined Criteria for Gradual Typing* (incl. GTLC safety + gradual guarantee), SNAPL 2015 — `drops.dagstuhl.de/.../LIPIcs.SNAPL.2015.274.pdf`.
- Wadler & Findler, *Well-Typed Programs Can't Be Blamed*, ESOP 2009 — `homepages.inf.ed.ac.uk/wadler/papers/blame/blame.pdf`.
- Vitousek, Siek & Baker, *Optimizing and Evaluating Transient Gradual Typing* — `arxiv.org/pdf/1902.07808`; Vitousek et al., *Big types in little runtime* (open-world soundness, Anthill Python/Coq), POPL 2017 — `doi:10.1145/3009837.3009849`.
- Takikawa et al., *Is Sound Gradual Typing Dead?* / Greenman et al., *How to Evaluate the Performance of Gradual Type Systems*, JFP — `cambridge.org/.../DC765724C52A3A462F16C7FB3AD18697`; Bauman, Bolz-Tereick, Siek & Tobin-Hochstadt, *Sound Gradual Typing: Only Mostly Dead*, OOPSLA 2017 — `doi:10.1145/3133878`.
- Harper, *PFPL* (2nd ed.), Type Safety chapter — `cs.cmu.edu/~rwh/pfpl/`; *What Type Soundness Theorem Do You Really Want to Prove?*, SIGPLAN Blog 2019 — `blog.sigplan.org/2019/10/17/...`.

> Method note: sources were gathered by a fan-out web-research harness with 3-vote
> adversarial verification per claim. The two **[✗→]** corrections above are claims the
> verification pass *refuted* (the `T.cast` "no runtime check" error and the `T.let` "only
> dual-checked" overreach); they are recorded as corrections rather than dropped so the
> mistakes aren't reintroduced.
