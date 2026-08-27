# The judgment layer — semantic Ruby types, and making the relation the definition of record

> **Status (2026-08-26, second update the same day): BUILT through J2, plus the
> narrowing rung.** J0 landed as `lean/RubyCore/Judgment/` (J1–J17 in its
> implementation-notes); the machine-typing spine, preservation, the composed
> theorem, and the derivation-checker pipeline landed the same day as J18–J27
> (`lean/RubyCore/Proof/Judgment/`). The headline theorems, all axiom-clean and in
> `check-proofs.sh`'s audit:
>
> * `judge_sound` / `judge_sound_cert` — a `Judge` derivation at a table sound for
>   the boot heap certifies `∀ r, ReachableResult (Machine.init p) r → ¬ typeStuck r`;
>   **no checker function in the statement** (§3's `MachineTyped → invariant_sound`
>   spine, delivered as `InvJ`/`CtlOkJ`/`KontOkJ` + `step_okJ`).
> * `validateJ_certifies` — §4(3) built: a **data** certificate (claimed rows + a
>   `Deriv` tree, JSON format in `Judgment/Json.lean`), checked by one
>   kernel-reduced `Bool` (`Judgment/Check.lean`), concludes the same property; the
>   claimed rows' residue is the one honest hypothesis, exactly as in
>   `validate_sound_of_ctl`.
> * Worked ends from literal certificate data under `decide`: `egIf`/`egZero`
>   (control core + builtin dispatch), `egEven` (**the claimed-row corollary C-1
>   was parked on, delivered unconditionally**), `egUserCall`/`egVcall` (the T5
>   `class_hierarchy` shape: reopen, promoted row, user dispatch), and `egNarrow`
>   (**the DRuby guard-discrimination shape, through the narrowing rules** — §1.4's
>   flagship, machine-typed by the J27 stored-atom construction).
> * **The Rails pilot (J32–J35, 2026-08-27)** — semantic claims grown into
>   **records** (`SemClaim`: claimed type `τ`, claimed **rows**, a `reqCls`
>   class-body gate), `define_method` made typing-visible by two ratchet-verified
>   semantics changes (capture erasure for closed bodies; one-step composition of
>   reify+dispatch), the invariant taught what a class body *is*
>   (`FrameCtx.inClassBody` + the `StackCtx` self-identity clause; `NoHook` over
>   `define_method`), and the goal program
>   `class String; define_method(:shout) { 1 }; end; "a".shout` **type-checked at
>   `.int`** (`Proof/Judgment/Rails.lean`): the claim's obligation
>   (`semAxiomsOk_dm`) discharged **by executing the semantics** — one machine
>   step, `defPromote`'s preservation argument scavenged at the grown table — and
>   composed through both the hand derivation (`railsE_safe`,
>   `railsE_result_int`) and a data certificate replayed by one `decide`
>   (`railsE_data_certified`). The type system never saw a rule for
>   `define_method`; the machine certified it once, and the syntactic pipeline
>   consumed the certificate.
> * **Semantic axioms (J31, 2026-08-27)** — user-specified semantic judgments as
>   **`Judge` leaves, invoked from the `Deriv` language**: `SemAxioms` (claims =
>   expressions at the canonical judgment `.any`/env-/table-preserving, gated to
>   out-of-fragment heads by `fragHead`), `Judge.semantic`, the field-free
>   `Deriv.semantic` node, `JCert.semAssumes`, and `validateJ_certifies` now
>   conditional on `SemAxiomsOk` (one `EvalOkAt` obligation per claim — exactly
>   the statement `step_okJ`'s eval branch consumes, so the preservation case is
>   an application). v1 embeds claims in **statement position** (`seq`), with the
>   `JudgeSeq` coupling premises + the checker's `fragHead`-guarded `.sub` node
>   closing the perverse-pairing hazard. Pilot delivered end to end
>   (`Proof/Judgment/SemAxiom.lean`): `lambda { 1 }` — a block-bearing send, the
>   arrow bill, no syntactic route — claimed, its obligation **discharged by
>   executing the semantics**, and the program certified both by hand derivation
>   and from a data certificate replayed by one `decide`.
> * **The semantic judgment (J29/J30, 2026-08-27)** — `SemJudge D Γ e c τ`
>   (`Proof/Judgment/Sem.lean`), defined by **reachability alone** (no `Judge`, no
>   `MFrag`, no checker in the definiens), with `judge_semJudge` as the
>   **fundamental lemma** (adequacy of the syntactic `Judge`), `semJudge_sound`
>   composing type safety through it, and `judge_result_vty` — terminating values
>   inhabit the judged type — bought by J29's answer-typed `KontOkJ`/`InvJ` for
>   the price of one `VTy.weaken`. §1.5's "reachability is already the semantic
>   ground truth" is now a definition rather than a remark, and `SemJudge` is the
>   layer's **extension point**: out-of-fragment constructs (the Rails direction)
>   are admitted by proving their `SemJudge` statement directly.
>
> The machine-typed fragment (`MFrag`, the eval arm's syntactic gate playing the
> role `infer`'s partiality played): T1 control core, block-less sends at any
> arity (explicit/implicit/`vcall`/`self`), `def` (install and promote), toplevel
> class reopens, `const`/ivar/gvar reads and writes, plain array literals, and
> bare-local `if`-narrowing. Not yet in it (each a recorded rung, none blocked):
> `return`/`next` jumps (unreachable until a running context opens those channels —
> W8 sigs), splat elements, block iterators/`lambda` (J16/J19's arrow bill),
> `begin`/`rescue` (**gated on resolving J8 first** — the entry-env handler rule is
> the piece preservation would refute), `cpath`, `super`/`zsuper`. The binary
> replay path IS wired (`rubycore --certify-j`, J28; worked files in
> `certify/certs/j/`, replayed against real `export-json` output). Deliberately
> not built, per the initiative's own exclusion: **emitters** — the hand-authored
> example certificates are what a future emitter targets.
>
> Origin: a first-principles design conversation prompted by the observation that
> the type-checking strand feels like wheel-spinning. The conclusion was a
> **re-scoping of C-1** ([`certificate-language.md`](certificate-language.md)
> §10.5–10.6, `lean/HANDOFF.md` C-1 entry): state the invariant over an inductive
> judgment rather than over `chk`. §0's diagnosis is now *measured*: the
> preservation mountain was climbed in one day of rungs because inversion is
> `cases`, the `sub` rule costs one slack-composition for every head at a stroke
> (`judge_eval_ok`), and the `infer_mono` port tax collapsed into one gated
> induction (`judge_mono`). The §8 risk-1 sentence ("if J1 hits an 8k-line-port-
> shaped wall anyway, the diagnosis was wrong") is answered: it did not.

Companions: [`type-judgments.md`](type-judgments.md) (the declarative judgments this
document promotes to definition of record — §6–§9 there are the content, already
written), [`certificate-language.md`](certificate-language.md) (the certificate
architecture, which survives with one section re-specified),
[`../../../type-safety-by-reachability.md`](../../../type-safety-by-reachability.md)
(the safety property and `invariant_sound`, both unchanged and load-bearing here).

---

## 0. The diagnosis — why this keeps feeling like wheel-spinning

The checker layer has been formulated twice (`infer`, L225–L265; then `chk`, V9–V20),
and both times the **metatheory was stated over the function**: Mono's twenty laws,
Konts' twelve constructors, Locals, Preservation — each proved by that function's
induction principle. The costs that followed are all consequences of that one choice:

* the V19 restructuring of `chk` into a mutual fuel block *solely* so that
  `chk.induct` becomes derivable;
* the motive-map ambiguities (motives 3/5/7 and 1/10 type-identical, a swapped
  assignment type-checks and fails only at IH-shape depth — measured twice);
* the ~8,200-line port priced in §10.5a, re-priced to "tractable" only after V19;
* the 600-line `chk_infer` bridge, built and deleted because it tied the headline
  theorem to the function being retired.

C-1 as currently scoped repeats the pattern a third time: it bakes
`CtlOk`/`KontOk`/`FramesOk`/Preservation to the *second implementation*, so the third
implementation change re-incurs the whole port. The §10.5a bridge lesson — "do not
make the theorem depend on the thing being retired" — applies one level up:
**an implementation is always eventually the thing being retired.** The layer that is
stable under implementation churn is the declarative judgment, which changes only when
the type system's *meaning* changes. `type-judgments.md` already specifies that layer
in full (expression typing §6, continuation/configuration typing §7, heap WF §8,
metatheorem statements §9); the build drifted into making functions the definition of
record instead. This document is the pivot back, with the semantic-type question
settled first because the judgment's indices depend on it.

## 1. Semantic Ruby types

**The intuition under test:** a Ruby type is (a) the slot types (ivars; cvars for a
class type), (b) the set of names it responds to, and (c) the signatures of those
entries — a recursive definition, since signatures mention types.

The shape is right. Four corrections, each with a design consequence:

### 1.1 Tie the recursive knot with names, not structure

Taken literally, "signatures mention types which contain signatures…" is not an
inductive definition — it is **coinductive**. `Integer#+ : Integer → Integer` is
already a cycle; any linked-list class is one. Anonymous recursive structural types
need equirecursive infinite trees or step-indexing to be well-defined, and equality
becomes bisimilarity. Ruby hands us the standard escape for free: **the class name is
the μ-binder.** A type mentions other types *by name into a table `D`* (class name →
structural content: slots, responds-to entries, sigs), and `D` ties every knot.

This is what nominal typing *is*, semantically — not a stance against duck typing but
the observation that in a heap-based semantics the structural content already lives in
one place (the booted method tables; `classOf` is total, `Sub` is the `ancestors`
walk) and names are references into it. Duck types, if later wanted, are a **derived**
notion: a structural/interface type is a *predicate over `D`* ("the set of classes
whose row includes these entries at compatible sigs"), never the base representation.

### 1.2 Slots are an invariant component, not intrinsic structure

Ivars are per-object: they spring into existence on first write, read as `nil` when
unset, and two instances of one class can carry different slot sets. Reading a missing
slot is *not* a type error — it is the `nil` flowing into a later dispatch that is.
So "the ivar types of class C" is not a semantic fact about C; it is a **claimed
heap-conformance invariant**: every reachable instance of C has its set ivars within
the claimed types, and an ivar read is typed at `claimed ∪ nil` unless initialization
is proven. Slot claims belong in `D`'s rows, but their proof-theoretic home is the
heap-typing half of preservation (`type-judgments.md` §8's `Δ ⊨ H`), not the type
grammar. Nilability discipline on ivars is where most real Ruby type bugs live (T2
`nil_dispatch` is the canonical toy), so this component earns its keep.

### 1.3 The responds-to set is a heap fact indexed by time

`define_method` / `prepend` / reopening mutate method tables, so "the type of C" is
only meaningful relative to a **table snapshot**. A semantic type is `(name, D)` where
`D` is a *phase*; the existing answer is boot-phase schedules
(`certificate-language.md` D3/C9): replay boot concretely, claim `D` = the settled
tables, `NoHook` thereafter. And `method_missing` must live in the definition, not as
an afterthought — a class defining it responds to everything, which collapses the
responds-to abstraction (`type-safety-by-reachability.md` §7.4); model its signature
explicitly or push such classes to the frontier.

### 1.4 The load-bearing structure is unions and nil, not recursion

The first-principles test for any candidate type grammar in this project: *the type
language's only job is to be a sound abstraction strong enough to refute
`aboutToTypeStick` at each site.* Per bad-state family:

| family | what the invariant must supply |
|---|---|
| `NoMethodError` | bound `classOf recv` within a set of classes whose rows all contain `m` |
| `ArgumentError` | arity compatibility of the resolved sig |
| `TypeError` | primitive coercion facts at the modeled coercion sites |

What that demands is **finite unions of class names, with `nil` as the ubiquitous
member, plus flow-sensitive narrowing** (`is_a?`/`respond_to?` guards — the mechanism
that kills DRuby's sixteen false positives). It does *not* demand deep recursive
structure: recursion is fully absorbed by names-into-`D`. Ranked grammar budget:
unions/nilability and narrowing first-class; slot maps as heap invariants (§1.2);
structural interfaces derived (§1.1); anonymous recursion never.

### 1.5 The fully semantic grounding, noted and deliberately not bought

The truly semantic type of an expression is "the set of (heap, value) pairs it can
evaluate to," and the honest metatheoretic framing of §2's judgment would be a
step-indexed unary logical relation over the machine, with soundness as the
fundamental lemma. We do not need it: **the reachability property is already the
semantic ground truth** (`type-safety-by-reachability.md` §1), and `invariant_sound`
already plays the fundamental lemma's role at the machine level, more cheaply. Do not
buy step-indexing to answer a question reachability already answers. Recorded so a
future session doesn't re-derive the option and mistake it for missing.

**Update (J29/J30, 2026-08-27): the first-order rendition of this section is now
built.** `SemJudge D Γ e c τ` (`Proof/Judgment/Sem.lean`) *is* the unary relation,
with the step index replaced by reachability — no `▷`, no worlds, first-order and
`Judge`-free in its definiens — and `judge_semJudge` is its fundamental lemma. What
stays deliberately unbought is exactly the *step-indexed, behavioral* version:
`SemJudge`'s value clause is `VTy` (a class tag below `SubJ`), never a behavior set,
so the flip conditions below are unchanged. The division of roles is now: `Judge` is
the proof theory, `SemJudge` the meaning, machine typing (`InvJ`) the mechanism —
and rule-free extension (prove `SemJudge` directly for a construct the fragment
cannot check) is a stated capability rather than a plan.

**The RustBelt/Iris comparison, pressure-tested (2026-08-26).** The obvious prior art
for "a semantic type system" is RustBelt (⟦τ⟧ as an Iris predicate; fundamental
theorem; unsafe libraries proven semantically typed). We decline it — but for specific
reasons, because the *casual* reasons don't survive scrutiny:

* **Not because Ruby's heap is abstract.** λRust's heap is abstract too; Iris was
  never about pointer arithmetic. Separation logic earns its keep on **aliased mutable
  state and framing**, which Ruby has in spades (shared ivar graphs, mutable method
  tables, closures over shared scopes). Our `heap_monotone`/`HeapGrow` lemmas *are*
  hand-rolled frame conditions — we already pay manually what SL automates. If
  preservation's mutation cases ever blow up on framing, that is a proof-engineering
  signal, and the minimal response is a footprint discipline, not Iris.
* **The real threat Iris answers is higher-order store circularity** — Ruby's heap
  stores procs/methods, so *behavioral* semantic types ("well-typed heap" mentions
  types of stored closures, which quantify over heaps) hit the classic circularity
  that step-indexing cuts. We are exempt only because §1–§2 cut it **syntactically**:
  a value's type is its class tag (first-order, decidable), and method bodies are
  checked by `Judge` on their *source*, never as behavior sets. Wright–Felleisen,
  viable exactly because the fragment is closed (whole-program, boot-phase `D`,
  everything else gates to the frontier).
* **RustBelt's raison d'être has no consumer here.** Its point is proving code the
  syntactic system cannot check (unsafe blocks) semantically inhabits its type, for
  open-world linking. Our analogue — builtins/prelude — is inside the trusted
  *semantics*, with first-order conformance lemmas (`BuiltinConformance.lean`)
  discharged by execution; untyped user code is not linked against, it is UNKNOWN.
* **Architecture incompatibility is decisive alone.** The certificate design requires
  first-order, kernel-decidable invariants (`Deriv.check`, `decide` at the boot heap,
  non-Lean emitters); Iris predicates are the opposite, iris-lean is immature, and the
  safety target (three exception families unreachable) is far weaker than RustBelt's.

**Flip conditions**, so a future session knows when this verdict expires: (a) duck
types made *behavioral* ("acts like an IO") rather than predicates over `D`; (b) D6
linking wanting semantic guarantees against arbitrary untyped neighbors rather than
syntactic `assumes ⊆ provides`; (c) builtins with proved behavioral specs instead of
axiomatized conformance; (d) concurrency. Even then, plain step-indexed logical
relations (Appel–McAllester/Ahmed) precede Iris — Iris is the ergonomics layer for
when ghost-state bookkeeping gets bad, not the entry ticket.

### 1.6 What nominality costs on untyped code (2026-08-26)

Question pressure-tested: does the nominal choice restrict certifying *untyped* code
(where the emitter invents all types)? **In expressiveness, essentially no; in
certificate lifecycle, yes, in two specific ways.**

* **The closed-world collapse.** Certification is whole-program against a boot-phase
  `D`, so every reachable value's class is drawn from `D`'s finite class set — and any
  structural type ("responds to `:to_s`/0") *denotes* a finite, enumerable subset of
  those classes. A nominal union naming that subset makes every judgment the
  structural type could. Duck-typed idioms that are actually safe are therefore
  certifiable with unions, for a fixed program. Nominality is also the machine's
  *native* vocabulary — `stepFn` dispatches by `classOf` → ancestors → table walk, so
  any abstraction adequate to refute `aboutToTypeStick` factors through the class tag
  regardless.
* **Real cost 1 — brittleness.** A duck-typed site's union enumerates the classes
  that flow there; adding a class to the program stales every certificate naming that
  union. Structural interface claims would be growth-stable. Tolerable while
  re-emission is cheap (emitters are untrusted); a difference in kind nonetheless.
* **Real cost 2 — no per-library certificates for polymorphic untyped code.**
  `def log(x); x.to_s; end` certifies per *program* (C6 per-call-site
  instantiation), never once for all clients. This is the same trade §1.5 records
  against RustBelt: whole-program + frontier instead of open-world linking. **Flip
  condition:** if D6 ever needs reusable certificates for duck-typed library
  interfaces, promote §1.1's derived structural layer (interface types as predicates
  over `D`) into the certificate vocabulary — it discharges to the nominal subset it
  denotes, so the base representation does not change.
* **Misattributed limitation — lost branch correlations.**
  `x = cond ? 1 : "a"; y = cond ? 2 : "b"; x + y` is safe but per-variable unions
  lose the correlation. That is a *path-sensitivity* limit shared identically by
  structural types; the fix vocabulary (per-path or correlation claims) should wait
  for corpus evidence — DRuby's false positives were guard-discrimination cases,
  which narrowing (§1.4) already covers.
* **Non-costs.** Input-controlled `Class.new`, post-boot eigenclass `def obj.foo`,
  and `method_missing`-style dynamic responders all *look* like nominal restrictions
  but are phase/frontier restrictions (§1.3): structural types rescue none of them,
  and the frontier discipline handles all of them.

**Why nominal is the scaling choice for real code** (added same day; the brittleness
cost above is accepted *because* re-emission is cheap, and these two properties are
what the cheapness buys):

* **Type terms stay short — `D` is maximal sharing.** A structural term for `Integer`
  must carry `+`'s signature, which mentions `Integer`, … — structural terms either
  loop or inline the transitive closure of the interface graph. Names make every type
  term O(union width) independent of behavioral depth, with the table paid once per
  certificate rather than once per occurrence. And union width has an *empirical*
  bound, which is the actual scaling bet: real Ruby call sites are overwhelmingly
  mono/bimorphic — the fact inline caches (PICs, YJIT/JRuby) exploit is the same fact
  that keeps emitted unions short. Measure it: emit the union-width distribution over
  the slice at **J4**; a fat tail there is the early warning that the bet is wrong.
* **Emitted types are human-legible, and this architecture consumes legibility.**
  Certificates are reviewable/diffable CI artifacts (§2 constraint 5) and the residue
  is ranked human-facing output — reviewers *read* type terms when accepting a
  conditional certificate. Nominal names are the vocabulary Rubyists and RBI/Sorbet
  already use (so C4 ingestion is translation, not re-abstraction) and the vocabulary
  the LLM emitter arm has priors over. Edge case: legibility degrades at wide-union
  duck sites; the fix is **untrusted sugar** — a certificate-carried alias table
  (`Stringish := String ∪ Symbol ∪ nil`) used only for rendering and diffing, with
  the checked form staying the expanded union. Aliases never reach the checker, so
  the trust cost is zero.

### 1.7 The first-order dividend, cashed as solvers (2026-08-27)

The nominal/first-order choice (§1.1–§1.5) has an operational payoff beyond proof
economics, and it is the sharpest way to *sell* the choice: every object in the layer
— `Ty` (seven constructors), `subTy` (an ancestors walk over a finite table, hence a
finite ground relation per program), `Judge` (first-order inductive over finite
syntax), the invariant — is finitely representable in solver-decidable theories. An
Iris-style model forecloses this — not "makes it harder," forecloses: step-indexed,
resource-quantified predicates have no decision procedure, so automation there means
tactics-per-proof by an expert. Here it means running cvc5, **untrusted**, because
`validateJ` is the sole arbiter. Three slots, in increasing ambition:

1. **SMT as the J4 emitter arm** (untrusted `Deriv` synthesis). Encode `Ty` as an
   SMT algebraic datatype, `D` as ground facts, `subTy` unrolled, each `Judge` rule
   as a constraint template with unknowns for env entries / claimed rows / joins —
   quantifier-free over datatypes + UF for a fixed program. The solver's *model* is
   a type assignment; a pretty-printer turns model + program into the existing JSON
   `Deriv`; a hallucinated model dies at the kernel `Bool`, zero new trusted code.
   Prior art: [InferType (ECOOP 2024)](https://drops.dagstuhl.de/storage/00lipics/lipics-vol313-ecoop2024/LIPIcs.ECOOP.2024.23/LIPIcs.ECOOP.2024.23.pdf)
   (type constraints as Z3 datatype equalities) and Ruby's own
   [InferDL/RDL](https://www.cs.tufts.edu/~jfoster/papers/dls20.pdf) (constraint
   solving + heuristics) — neither with a proof-grade checker behind it, which is
   the differentiated sentence. [Dminor](https://catalin-hritcu.github.io/publications/dminor-icfp2010.pdf)
   (Bierman–Gordon, ICFP 2010) is the closest historical arrangement — semantic
   subtyping *as* first-order validity discharged by Z3 — except they trust the
   solver; we would not have to. The design point itself is validated by
   [decidable tag-based semantic subtyping](https://arxiv.org/pdf/1912.08255)
   (the Julia lineage): nominal-tag interpretation is what keeps semantic subtyping
   decidable where behavioral interpretations aren't.
2. **The untrusted invariant-inference engine** (`type-safety-by-reachability.md`
   §4) **as CHC solving.** Inductive-invariant synthesis over `stepFn` is literally
   the Constrained Horn Clause problem (Spacer, Eldarica). The unknown predicates
   are first-order and small *because* the abstract domain is class names; had "type
   of v" meant a predicate over heaplets, the CHC unknowns would be higher-order and
   no encoding would exist. This is the crispest instance of "first-order rendered X
   tractable": the still-open engineering on the roadmap is solver-shaped only
   because of §1's choice. Blocks do not break this slot — the reduction from
   higher-order CHCs to first-order CHCs is
   [sound and complete via defunctionalization](https://arxiv.org/pdf/1810.03598)
   (see §1.9).
3. **Solver proofs replayed into Lean** —
   [lean-smt](https://arxiv.org/pdf/2505.15796) reconstructs cvc5's CPC proofs
   kernel-checked, but covers ~30% of the rule set (2025); real but young. Our own
   certificate format + `validateJ` is strictly better for this use case anyway
   (total, ours, built). Recorded so it isn't mistaken for the load-bearing slot.

The decidability *argument* can be borrowed verbatim from the refinement-types
community, which restricts to QF-UFLIA on purpose: quantified/higher-order VCs make
typability hostage to "the solver's unpredictable quantifier instantiation
heuristics," while the QF fragment gives "a precise, solver-agnostic, language-based
characterization of when a program is well-typed"
([Refinement Types: A Tutorial](https://arxiv.org/pdf/2010.07763)). Ours is the same
claim one level up: not just the side conditions but the entire semantic soundness
story stays first-order, because reachability replaced step-indexing as the ground
truth (§1.5).

### 1.8 The admission boundary for discharge-by-execution (2026-08-27)

J31/J35 discharge a claim's obligation **by executing the semantics**, and both
pilots (`lambda { 1 }`, the `define_method` row) sat in a sweet spot: closed,
deterministic, terminating, state-insensitive. Each adjective names a failure mode,
and the umbrella over all of them: **`SemJudge` is a Π-statement (all conformant
states, all runs) and execution discharges Σ-statements (this one run).** The
translation-validation literature supplies the right frame
([Tristan–Leroy](https://jtristan.github.io/papers/popl08.pdf)): the discharge is
*sound* for any claim (replay cannot lie) but *complete only relative to a named
fragment* — and the honest deliverable is the fragment's boundary. This section is
that boundary, i.e. **the admission policy for semantic claims**, because the
project-level risk is not any single gap below: it is an axiom quietly admitted
outside the fragment, "discharged" by an execution that does not cover its
quantifier — poisoning the axiom-clean claim while still typechecking.

Discharge-by-execution is complete for claims that are **closed** (the conformant
start-state set is a singleton or enumerated), **terminating within the certificate's
fuel**, **deterministic**, **first-order-argumented** (no quantified block/proc
parameters), and **table-stable** (footprint slice of `D` untouched between discharge
and use). Outside it, three named escalations — never a fourth, improvised one:

* **State-polymorphism → footprint lemma.** A claim at nonempty `Γ` with an abstract
  `cls C` quantifies over infinitely many conformant heaps; one run instantiates one.
  The reduction to finitely many representative runs is a lemma "running `e` reads
  only these locations" — which is **the frame rule, re-entering as pay-as-you-go
  first-order obligations**. Named honestly: §1's choice did not eliminate framing,
  it deferred it to exactly these discharge obligations (this is §1.5's "if
  preservation's mutation cases blow up on framing" signal, relocated to the
  claim layer).
* **Unboundedness → the invariant route.** A fuel-bounded run proves "no type-stuck
  outcome within n steps" — the bounded-model-checking verdict, with BMC's known
  repair (k-induction/IC3 ≙ our inductive invariant) and BMC's known discipline: the
  bound is a **first-class output**. A fuel-discharged claim is a `SemJudgeUpTo n`
  grade carrying its fuel in the certificate, never silently promoted to the
  unbounded judgment.
* **Higher-order arguments → per-instantiation discharge** (§1.9).

Two further conditions on any discharged claim:

* **Table evolution.** The claim is conditioned on `D`, and `define_method`/`prepend`
  move `D`. The direct ancestor is
  [Hummingbird](https://www.cs.tufts.edu/~jfoster/papers/pldi16.pdf) (Ren–Foster,
  PLDI 2016 — just-in-time static checking *is* discharge-by-execution at the moment
  metaprogramming settles), and its documented lesson is that **cache invalidation
  was the hard half of its preservation theorem**, not an engineering afterthought.
  A discharged claim must carry the slice of `D` it depends on, and the checker must
  refuse composition across a delta touching that slice — the semantic heap-diff of
  `bounded-effect-checking.md` §6 as part of the *proved* story.
* **The effect seam.** `stepFn` is deterministic today, so one run per state
  suffices; the moment the POSIX mediator lands, a run fixes one oracle sequence.
  Prior art's verdict is unanimous — Netsem retreated from verification to
  *membership of the observed trace*; CakeML keeps theorems oracle-quantified and
  never discharges them by running. Effectful constructs get **trace-grade
  monitoring claims, syntactically distinct** from state-quantified ones, so one
  grade cannot masquerade as the other.

Trust grades, recorded per certificate: kernel `decide` vs `native_decide` (which
adds `Lean.ofReduceBool` to the audit — a distinct trust level, per two decades of
proof-by-reflection practice from the four-color proof onward, not a dent to hide).

### 1.9 Blocks do not breach the boundary (2026-08-27)

Pressure-tested worry: blocks are ubiquitous, `SemJudge` claims about block-taking
methods quantify over all blocks, so does the first-order commitment cap the layer
where Ruby actually lives — and doesn't HOL "directly represent" blocks? Two
conflations to undo, then three instruments.

**First-order is a property of the *model*, not the ambient logic.** Lean quantifies
over `Prop`s every day; what §1.5 declines is the step-indexed Kripke *construction*.
And step-indexing is forced by exactly one thing: **behavioral types over
higher-order store** ("cell holds a σ→τ function" constraining behavior on heaps
satisfying the world being defined). Nominal `VTy` severs that knot at the root: the
type of a stored proc is `tag = Proc`, a heap fact with no behavioral content, no
recursion, no worlds. §1.5 records this cut for the `Judge` route (bodies checked on
*source*); it holds unchanged for the claim route. Storing blocks in ivars costs the
invariant nothing; the only question is recovering *behavioral* facts at use sites.

* **Rank-1 conditional claims.** A block's behavioral spec doesn't need a new logic —
  **it is a `SemJudge` statement** ("invoked with σ-typed arguments in a conformant
  heap, reaches no type-stuck outcome, returns a τ"). A claim about a block-taking
  method becomes an implication: `(∀ b, SemJudgeBlock D Γ b σ τ) → SemJudge …` —
  one quantifier over a first-order-defined predicate, rank-1, no self-reference,
  stated and consumed in plain Lean. This covers the ubiquitous pattern: blocks
  passed *downward* and called (`each`/`map`/`times`), which never round-trip
  through the store in a way that recreates the knot.
* **Closed-world defunctionalization.** In the whole-program setting certification
  already assumes (§1.6's closed-world collapse), "all blocks of type σ→τ" is the
  program's **finite set of block literals**, and the sub-set flowing to a given
  yield site is computable by CFA. The ∀ in the rank-1 premise collapses to a finite
  conjunction: discharge `SemJudgeBlock` once per literal (by execution, by `Judge`,
  or by claim — the existing tri-modal admission), with the CFA untrusted and its
  flow set certified element-wise like everything else. Captured environments do
  *not* reopen the higher-order problem — a capture is just more `Γ`, reducing to
  §1.8's footprint escalation. The industrial precedent to cite:
  [ACL2's `apply$`](https://www.cs.utexas.edu/~kaufmann/papers/apply/report.pdf)
  (Kaufmann–Moore, JAR 2020) — a strictly first-order prover where "functions" are
  data, a syntactic **tameness** predicate gates interpretability (≙ `fragHead`),
  and **warrants** are explicit per-function hypotheses (≙ per-block claims);
  twenty years of hardware verification then used mapped functionals routinely.
  First-order prover + ubiquitous higher-order idioms is a solved coexistence, not
  a research bet. (The encodings also keep §1.7's solver slots alive under blocks:
  Sledgehammer's apply/λ-lifting translation, and the sound-and-complete
  [defunctionalization of higher-order CHCs](https://arxiv.org/pdf/1810.03598).)
* **The havoc block**, for the bounded checker only: replace an unanalyzed block by
  a most-general one (arbitrary τ-result, arbitrary mutation within a declared
  footprint), Boogie-style. A run surviving the havoc covers every real block with
  that footprint; used only when *choosing* not to enumerate, with the CFA saying
  what the real footprint is.

**Residual watchlist**, stated precisely: procs stored in the heap and invoked far
from creation, *when a behavioral fact is needed at the invocation*. The invariant
stays sound there (nominal `VTy`), but recovering the return type at such a site
binds on **CFA precision, not on the logic** — which cell can hold which literals is
an analysis question the certificate architecture already knows how to consume
untrusted answers to.

**Flip-condition refinement** (extends §1.5's list): step-indexed semantic typing
earns its keep when behavioral types must be assigned to heap-stored code while
remaining **open-world** — linking against unknown, never-executed, syntactically
unavailable code (a gem as a black box, certified once for all clients). That is
RustBelt's problem statement and §1.6 already records it as the trade taken. If the
roadmap ever grows it, the increment is one logical-relation module *over the same
machine* (reachability stays the ground truth —
[the Iris school's own framing](https://iris-project.org/pdfs/2024-jacm-logical-type-soundness-final.pdf)
builds its models over an operational semantics like ours), not a rewrite.

## 2. The judgment — `Judge D Γ self e t Γ'`

Flow-sensitive expression typing as an **inductive `Prop`**, exactly as `Step m m'` is
mechanized today, transcribing `type-judgments.md` §6. The out-environment `Γ'` is
right for Ruby (assignment retypes locals; narrowing is flow). Refinements over the
bare `Judge G e t G'` shape:

* **Indices.** `D` (the table/phase, fixed per boot phase — §1.3), `self`'s class
  (implicit-self dispatch, visibility), and the block/return context that `chk`'s
  `ctx` already threads. Heap typing is *not* an index of the expression judgment; it
  is a conjunct of machine typing (§3).
* **Blocks close over and mutate enclosing locals.** `[1,2].each { x = 1 }` — a
  block's `Γ'` leaks into its caller's environment, because captured scopes are
  shared (`captured` chains in the frame store). The block rule must either join the
  block's effect into the continuation environment or the fragment must exclude
  capture-mutation. Decide at J0 (§6); do not let it be discovered at preservation
  time.
* **Subsumption is a rule, and joins become derivation content.** Add
  `Γ ≤ Γ'`, `t ≤ t'` weakening. Join points (`if`, loop heads, `rescue`) are then
  *nondeterministic choices recorded in the derivation* — D1's stackmaps falling out
  of the proof theory instead of being a bolted-on section. The L231–L236 join walls
  existed because a *function* must compute joins; a *relation* accepts the claimed
  one and only checks it.
* **Why a relation, mechanically.** Inversion on an inductive is `cases` — no motive
  maps, no `.induct` derivability crises, no macro-hygiene traps. The twenty Mono laws
  about a function collapse to one or two weakening lemmas about a relation (standard,
  one clean induction). New heads are new constructors, which do not perturb existing
  proofs the way new fuel-function arms perturb every `.induct` motive.

## 3. Machine typing is the invariant — and the real theorem

`Judge` alone is **not** an inductive invariant: reachable states are mid-reduction
configurations `(ctl, konts, frames, heap)`, not surface programs. The "extract a
judgment into an invariant" step is standard CK-machine typing, and it is where the
work lives:

```
KJudge     D k t_in t_out        -- each kont frame typed as hole-type → result-type
MachineTyped D m :=              -- the Inv instance, schema-level
  ctl judges at the type the kont stack expects
  ∧ frames conform to their Γs
  ∧ heap conforms to D            -- §1.2's slot invariant lands here
```

with the two theorems:

* **subject reduction** — `MachineTyped D m → stepFn m = .next m' → MachineTyped D m'`
* **progress/safety** — `MachineTyped D m → ¬ aboutToTypeStick m`

Then `I := MachineTyped D` plugs into the **already-proved** `invariant_sound`, and the
certificate's role is to instantiate `D`/`Γ`/the derivation — which is precisely
`certificate-language.md` §2 constraint 3 ("the cert determines an `Inv` instance").
Nothing in this spine is new: `CtlOk`/`KontOk`/`FramesOk` *are* machine typing. The
proposal is to author them **over the inductive relation instead of over `chk`**.

**Honest cost.** Subject reduction is the mountain regardless of formulation:
`Proof/Static/Preservation.lean`'s 2,711 lines and 73 inversion sites are real content
(every `stepFn` arm preserves typing) and do not evaporate. What changes is the
*marginal* cost structure — `cases` instead of motive maps now, and the next checker
rewrite costs one adequacy lemma instead of a four-file port. The existing
`Proof/Static/` and in-flight `Proof/Cert/` proofs are **scavenged, not ported**:
their case analyses and heap lemmas transliterate, their induction scaffolding does
not.

## 4. The certificate is a derivation — sharpening "parse a term into an inhabitant"

"Checking a certificate = exhibiting an inhabitant of `Judge`" has three distinct
mechanizations; choose consciously:

1. **Lean proof term as certificate.** Emitter produces a Lean term of type
   `Judge …`; the kernel checks it. Rightly excluded by `certificate-language.md` §5:
   emitters must speak Lean, elaboration cost is unpredictable.
2. **Boolean checker + `decide`.** `chk`'s world. Small certificates (choices only,
   deterministic propagation between), but you own a checker *with metatheory* — the
   C-1 tax — plus the L73 kernel-reducibility discipline on the whole checked path.
3. **Derivation-as-data + a trivial local checker.** A first-order `Deriv` datatype
   mirroring `Judge`'s constructors one-to-one, JSON-serializable, emitted by any
   untrusted tool. The trusted `Deriv.check : Deriv → Bool` verifies each node
   *locally* — side conditions hold, children's conclusions match the premises — no
   propagation, no fixpoints, no joins computed. The soundness lemma
   `Deriv.check d = true → Judge …` is a one-induction near-triviality **because the
   checker mirrors the constructors**.

**Recommendation: (3).** It is the maximal reading of §2 constraint 1 ("validation is
search-free"): `chk`'s metatheory is expensive exactly because `chk` still
*re-derives* (propagates environments between claims); a derivation-carrying
certificate makes the trusted checker nearly content-free — the Java-stackmap/PCC
endgame that D1 was pointing at. Certificates grow to linear in program size × rule
size, which at slice scale (2,159 linked lines) is nothing; emitters stay non-Lean;
and the kernel work per program is reducing a structurally recursive local checker,
the friendliest possible shape for norm 5. Option (2) can return later purely as a
cert-size optimization, and its obligation is then one lemma against `Judge`, not
four metatheory files.

## 5. Relation to what is built — kept, superseded, scavenged

* **Kept unchanged:** `invariant_sound` and the whole reachability framing; the
  bad-state predicate; `validate`'s table half — `declsOk_of_validate`, `rowsGuarded`,
  the residue discipline (`assumes`), the JSON format's row/provenance sections; the
  Direction-A witness machinery; the difftest/ratchet foundation.
* **Superseded:** C-1 *as scoped* ("restate `CtlOk`/`KontOk` over `chk`"). The open
  premise `hctl` of `validate_sound_of_ctl` remains the target; its supplier changes
  from `chk`-acceptance to a checked `Deriv`. The §10.6 ladder's head item is replaced
  by §6 below. The in-progress `chk_table_ret` rung (HANDOFF C-1 "immediate next
  task") is **abandoned deliberately** — recorded here so it reads as a decision, not
  a loose end. Sunk-cost note: it was "one uniform tactic away," but finishing it
  buys a rung of a port this document argues against completing.
* **Demoted, not deleted:** `chk`. Its 47-arm totality is valuable as the **coverage
  tier** (fast pre-filter, frontier report — §10.3's two-dimensional verdict
  survives). `chk → Judge` adequacy becomes *optional* future work, no longer
  load-bearing.
* **Promoted:** `type-judgments.md` from "implementation catalog" to the source the
  Lean definition of record transcribes. Divergences discovered during J0 are edits to
  *that* file, each its own commit.

## 6. Milestones — the J-ladder

Sized like the C-ladder: each rung is a commit series with a measurable exit.
**Scorecard (2026-08-26): J0 ✓, J1 ✓ (`judge_sound_cert`, audited), J2 ✓
(`validateJ_certifies` + JSON format + the `--certify-j` replay path, J28), J3 ✓ in substance (sends/`def` landed with J22/J23; the
T2-shape is `egNarrow`, the T5-shape `egUserCall`), J4 open (needs the emitter
arm — §1.7 slot 1 records the SMT-as-untrusted-emitter candidate for it).** The J-numbers continue in `lean/RubyCore/Judgment/implementation-notes.md`
(J18–J35; J29 the answer-typed invariant, J30 `SemJudge` + adequacy + result
typing, J31 semantic axioms — user-supplied semantic judgments as `Judge` leaves,
Deriv-invocable, pilot delivered).

* **J0 — author the judgment.** `Judge`/`KJudge`/`MachineTyped` in Lean, transcribing
  `type-judgments.md` §6–§8 for the T1 control core, **with subsumption and narrowing
  from day one** (§2) and the block-capture decision made explicitly. Exit: the
  definitions elaborate; hand-built derivations for two toy programs exist as terms.
* **J1 — subject reduction + progress on the fragment.** The §3 theorems over
  `stepFn`, scavenging `Proof/Static/{Konts,Locals,Preservation}.lean`. Exit:
  `validate_sound_of_judge` — the composed theorem with `hctl` discharged from
  `MachineTyped`, axiom-clean, in `check-proofs.sh`'s audit list.
* **J2 — `Deriv` + local checker + adequacy.** The §4(3) pipeline end-to-end: JSON
  derivation → `Deriv.check` → `Judge` → theorem, demonstrated on `egEven` and T5.
  Exit: `rubycore --certify` accepts a derivation certificate; the fourth ratchet
  counts it.
* **J3 — `send`/`def` (T2 of `type-judgments.md` §6.2).** The dispatch rule against
  `D`, the first rung where §1's type-notion decisions (unions, nil, phase-indexed
  `D`) are exercised for real. Exit: T2/T5 toys certified via derivations.
* **J4 — re-run the slice.** The Homebrew slice census under the new pipeline;
  compare against the fourth ratchet's 11. Exit: the coverage-vs-sound gap of §10.3
  re-measured, and a decision on whether `chk → Judge` adequacy is worth its lemma.

R2, `Assn.const`, and T2(`Sub`) from §9.7/§9.9 keep their positions *after* the
equivalent of C-1 — i.e., after **J1** — unchanged in content.

## 7. Working norms

`certificate-language.md` §7 (= `homebrew/PLAN.md` §4) applies unchanged, including
the ratchet byte-stability expectation (this initiative adds no interpreter behavior)
and norm 5's reducibility discipline — which §4(3) makes *cheaper* to honor, since the
only kernel-reduced trusted code is the local checker. Layout, per norm 7:

| directory | contents | trust | decisions file |
|---|---|---|---|
| `lean/RubyCore/Judgment/` | `Judge.lean`, `Kont.lean`, `Machine.lean` (the relations), `Deriv.lean` (+ JSON codec), `Check.lean` (the local checker) | **trusted** (spec + checker) | `lean/RubyCore/Judgment/implementation-notes.md` (**J-numbers**) |
| `lean/RubyCore/Proof/Judgment/` | `Preservation.lean`, `Progress.lean`, `Adequacy.lean` (`Deriv.check → Judge`), `Sound.lean` (the composed theorem) | **trusted** (the theorems) | same J-file |
| `certify/` | gains a derivation-emitting mode; everything stays untrusted | untrusted | E-numbers, as today |

Same interaction rule: depend on `Types/`/`Proof/Static/` by import only; missing
lemmas about existing machinery land *there* with L-numbers, never forked.

## 8. Risks, stated

1. **Third-formulation churn.** This is the third rebuild of the checker layer, and
   the pattern to fear is that J-work stalls the way C-1 did. The structural
   mitigation is the argument of §0 itself: the judgment is the *spec* layer — both
   `infer` and `chk` (and any future checker) bridge to it by one-directional lemmas,
   so this is the last formulation the metatheory should ever be stated over. If J1
   hits an 8k-line-port-shaped wall anyway, the diagnosis of §0 was wrong; record
   that here.
2. **The preservation mountain is unchanged** (§3). The relation buys maintainability
   and marginal cost, not a smaller theorem. Price J1 by scavenge-rate against
   `Proof/Static/Preservation.lean`, measured at the first three `stepFn` arms, before
   committing to the rest.
3. **Derivation size** — linear, but with a constant factor (environments at every
   node vs. at choice points). Measured at J2 on the slice; the §4(2) fallback exists
   and costs one adequacy lemma, not a redesign.
4. **The vocabulary wall does not move** (inherited from §8 risk 2 verbatim):
   judgments change *who checks*, not *what is provable*. Growing the rule set is
   still hand-proof work in preservation — now priced per constructor instead of per
   motive.
5. **Quantifier under-coverage in discharged claims.** The failure mode §1.8 exists
   to prevent: a semantic claim admitted outside the five-adjective fragment, its
   obligation "discharged" by an execution that instantiates only part of its
   quantifier (one conformant state of many, one fuel of unboundedly many, one
   block of a quantified set). It typechecks, stays axiom-clean by `#print axioms`,
   and is wrong. Mitigation is structural, not vigilance: the admission policy's
   grades (`SemJudgeUpTo n`, trace-grade, per-instantiation) must be distinct
   *types of claim* the checker refuses to compose as the unbounded judgment, so
   the gap is unrepresentable rather than merely discouraged.
