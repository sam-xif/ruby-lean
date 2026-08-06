# Typed-portion safety — a plan of attack

> **Status:** plan, second draft (2026-08-06). Nothing here is built. It supersedes nothing
> proved: the whole-program runtime statement of
> [`types-and-preservation.md`](types-and-preservation.md) §C.1 option 2 *is* proved
> (`lean/RubyCore/Proof/SorbetSafety.lean`, L81); this is a **different, weaker, more
> useful** property reusing most of the same machinery.
>
> **This draft corrects the first one in two places**, both marked **[✗→]** below: the
> closure condition is not a call-graph property (§3), and "deepen the boundary checks"
> does not fix it (§4.3). Both corrections came from experiments, not from re-reading.
>
> Evidence tags per [`README.md`](README.md): **[V]** verified against CRuby/`srb` in this
> workspace, **[D]** documentation or literature, **[?]** open, **[✗→]** a correction of a
> plausible-but-false claim, recorded so it is not reintroduced.

---

## 1. The property, and why this one

**Informally:** *a type error never occurs inside typed code.* Untyped code may fail
however it likes; when it hands bad data to a sig'd method the wrapper catches it and
blame lands on the caller. This is the **blame theorem** shape — "well-typed programs
can't be blamed" [D: Wadler & Findler, ESOP 2009; §B.5].

| Target | Status | Problem |
|---|---|---|
| Static soundness on `# typed: strong` | not started | `strong` is beta and rare; true but about almost no code |
| Whole-program runtime three-outcome safety | **proved** (L81) | needs the whole program in the fragment — 3 of 22 corpus programs, and essentially no real codebase |
| **Typed-portion safety** | this document | the hypothesis is a heap property that cannot be discharged locally (§3–§4) |

The decisive advantage is scope. Sorbet codebases are **partially typed by design** — that
is the point of gradual typing — so any whole-program hypothesis is unsatisfiable on real
code, while a per-method claim applies to every sig'd method in a mostly-untyped codebase.
It is also what a Sorbet user believes they are buying.

Secondary advantage (§5): the property is **local**, so the proof is per-method rather than
whole-program.

---

## 2. Four channels by which untyped data reaches typed code

All four are corpus programs, all verified: `srb tc` reports **no errors**, and a
`TypeError` is raised **inside a sig'd body**, with no escape hatch used [V].

| # | Channel | Corpus | On the call graph? |
|---|---|---|---|
| 1 | **call return** — unsigned callee's return value | `untyped-boundary/002` | yes |
| 2 | **block return** — a proc from untyped code, `yield`ed to | `untyped-boundary/003` | no — higher-order |
| 3 | **ivar write** — unsigned method writes `@n`, typed method reads it | `untyped-boundary/004` | not a call at all |
| 4 | **alias + mutate** — argument conforms at entry, mutated later through an alias | `untyped-boundary/005` | no, and see §4.3 |

Channel 1 is the diagnosis: sorbet-runtime is *guarded* at sig'd boundaries — it wraps the
sig'd method and checks its own parameters and return — but an **unsigned** method has no
wrapper at all, so nothing is checked in either direction, and statically, assigning
`T.untyped` to anything is permitted [D: /docs/untyped].

Channel 4 is the one that constrains the design, and it is worth reading closely:

```ruby
a = untyped_array   # [1, 2] — conforms; even a DEEP check at the boundary would pass
h.store(a)          # sig { params(xs: T::Array[Integer]).void }
a << "boom"         # mutated AFTERWARDS, through the alias untyped code still holds
h.total             # TypeError inside typed code
```

> **Method note.** A first version of this experiment put the hostile values as literals in
> typed context, and `srb` caught two of the three statically — correctly, since it could
> see the whole flow. That version would have overstated the case. Redone with every
> hostile value originating in an unsigned method (the case that matters), `srb` is silent
> on all of them [V].

---

## 3. Closure is a heap property, not a call-graph property

**[✗→]** The first draft framed the required hypothesis as *call-graph closure*: every
callee of a typed method must itself be typed. §2 refutes that as a sufficient condition —
only one of four channels is a call. Blocks are higher-order so the call graph cannot name
the callee; ivars are not calls; and channel 4 is not about control flow at all.

The property is about the **heap over time**:

> no untyped data enters typed execution ⟺ the region of the heap reachable from typed
> code is disjoint from, or protected against, writes by untyped code

That is an **ownership / separation** condition. Call-graph closure survives as the
*syntactically visible fragment* of it — necessary, not sufficient — and is still worth
computing (§6), but it must not be mistaken for the whole condition.

### 3.1 Why it cannot be discharged locally

Stated per entry point, the condition quantifies over two things:

1. the heap at entry — *values reachable from the arguments conform to their declared
   types*; and
2. the interference untyped code may cause **during** the call — *no write into the typed
   region while typed code is running*.

(1) is local and checkable (at a cost — see §4.3). **(2) is a rely condition and cannot be
discharged locally at all**, because it quantifies over code we are deliberately not
looking at. That single sentence is the whole difficulty, and it is why "specify closure on
a partial program" felt slippery: local *specification* is possible, local *verification* is
not.

### 3.2 The three sound routes, and the fourth pragmatic one

There are exactly three ways to make (2) true rather than assumed:

- **(a) Whole-program.** See all the code. Sound; defeats the purpose of gradual typing.
- **(b) Ownership discipline.** Restrict typed code so it cannot share mutable state with
  untyped code — typed methods mutate only what they allocate; crossing values are frozen
  or copied. Sound and locally checkable, but it changes how Ruby is written, and it is a
  *proposal*, not a description of Sorbet.
- **(c) Use-site runtime checks** (transient enforcement [D: Vitousek et al.; §B.5]). Give
  up boundary checking; check where values are used. Sound, costly, also a change to
  Sorbet.

And the route this plan takes:

- **(d) Assume-guarantee.** Do not prove (2). State it *precisely, in the semantics*, prove
  the theorem conditional on it, and **measure** how often it holds (§7). The theorem
  becomes conditional — but the condition is written down and instrumented rather than
  hidden in prose, and (a)/(b)/(c) remain available later as ways to discharge it.

---

## 4. The assume-guarantee statement

### 4.1 Shape

```
  Rely  (assumed, measured — §7):
    R1  at entry, every value reachable from the arguments conforms to its declared type
    R2  while typed code runs, untyped code performs no write into the typed region

  Guarantee (proved):
    G   no type-family error is raised in a frame belonging to the typed portion
```

R1 is what a deep entry check would buy; R2 is what no check can buy (§4.3). Splitting them
is deliberate: R1 may later be *discharged* by a deep check or by induction over the typed
portion, while R2 needs (a), (b) or (c).

### 4.2 In Lean

The bad state moves from a property of the terminal `StepResult` — which is what
`SorbetSafety.lean` uses —

```lean
def sorbetStuck : StepResult → Prop
  | .uncaught exc m => isTypeError m.heap exc ∧ ¬ isBlame m.heap exc
  | _ => False
```

— to a property of the **configuration at the raise**:

```lean
def currentMethod (m : Machine) : ObjId × String :=
  (m.currentFrame.defmod, m.currentFrame.meth)

def blamesTypedCode (P : TypedPortion) (m : Machine) : Prop :=
  raisesTypeFamily (stepFn m) ∧ P.contains (currentMethod m)

def TypedPortionSafeFrom (P : TypedPortion) (R : Rely) (m₀ : Machine) : Prop :=
  R.holds m₀ → ∀ m, Reaches m₀ m → ¬ blamesTypedCode P m
```

**Frames already carry what attribution needs** [V]: `Frame.meth` and `Frame.defmod`
(`lean/RubyCore/Machine.lean`). No model change is required to *state* the property.

Two definitional decisions:

- **Attribution is by *raising* frame, not by unwinding path.** An error raised in an
  untyped callee that propagates *through* typed frames is attributed to the untyped
  frame. This matches blame-calculus attribution; the alternative reading makes the
  theorem false for trivial reasons.
- **[?] Rescued errors.** `typeStuck` counts only *uncaught* outcomes ("raised ≠ stuck",
  `type-safety-by-reachability.md` §2). Here the natural reading is stricter: a type error
  raised inside typed code is a defect even if typed code catches it. Recommendation:
  strict, with the uncaught variant derivable.

The metatheorem is unchanged in shape from L81 — the **third** swap of the bad-state
predicate, after `typeStuck` and `sorbetStuck`, which is the running thesis of
[`../../type-safety-by-reachability.md`](../../type-safety-by-reachability.md). It is a
five-line proof reusing `invariant_reaches` and is not the interesting part.

### 4.3 [✗→] Deep boundary checks do not fix this

The first draft listed "deepen the checks" (RTTI at the boundary, à la Safe TypeScript
[D: §B.3]) as one of three responses to shallow checking. **That is wrong as a general
fix.** Channel 4 shows why: the array *conformed* at the boundary, so a deep check would
have passed, and the violation was introduced afterwards through an alias. Deep checking is
not merely expensive, it is **insufficient in the presence of aliasing and mutation** —
which is exactly why transient typing checks at use sites rather than boundaries.

What remains true, and is the reason shallow checks still matter: the wrapper's `is_a?`
gives a weaker precondition than the sig declares.

```
   sig says:      xs : T::Array[Integer]
   wrapper gives: xs.is_a?(Array)            (element type erased, §A.6)
   body relies on: xs.first + 1
```

So R1 is genuinely needed as a hypothesis; it is not implied by the runtime checks.
Two ways to eventually discharge it — **restrict** (exclude parameterized types from
crossing positions; sound but probably too restrictive for real code) or **induct** (carry
depth statically through the typed portion, so deep conformance is needed only at entry
points) — with induct the more promising. **[?]** Settle before M5.

---

## 5. Why runtime checks still make the *proof* local

Given R1/R2, the obligation per typed method is:

```
   assume:  arguments conform to the sig's parameter types  (the wrapper, plus R1 for depth)
            callees are typed or RBI-declared               (§6)
            no interference                                 (R2)
   prove:   the body raises no type-family error, and returns a value of the return type
```

This is **local, per-method**, with the sig as pre/postcondition. It does *not* need the
global well-typed-heap invariant `Δ ⊨ H` that whole-program subject reduction demands
(`type-judgments.md` §8): the boundary is where the precondition is discharged by an actual
runtime check instead of by an inductive hypothesis. That is the guarded/contract shape of
§B.5, and it is dramatically cheaper than whole-program preservation. It is also the
concrete reason the `T` shim had to go into the model (L80) rather than being mocked.

---

## 6. Three kinds of callee (what makes the checkable part affordable)

Call-graph closure is only *part* of the condition (§3), but it is the part we can compute,
and it is affordable because there are three kinds of callee, not two:

| Kind | Statically typed? | Runtime-checked? | Verdict |
|---|---|---|---|
| **(i)** sig'd user method | yes | **yes** — the wrapper | safe boundary |
| **(ii)** builtin / stdlib declared by an RBI | yes (Sorbet ships RBIs) | **no** — sorbet-runtime does not wrap the stdlib | safe *in our setting*, see below |
| **(iii)** unsigned user method | no (`T.untyped`) | no | **the hole** — must be excluded |

Kind (ii) is where our setting is *better off than Sorbet's*. Sorbet trusts its RBIs with
no runtime backstop; we do not have to, because **the model defines the builtin**. Trust
becomes a proof obligation:

> **RBI-conformance obligation.** For every builtin the typed portion calls, the model's
> implementation conforms to Sorbet's RBI declaration for it.

— separately and differentially checkable (§8, M3), not assumed. Admitting kind (ii) is
what lets ordinary code call the stdlib and still be in scope.

### 6.1 Computing the call graph

Ruby dispatch is heap-dependent, so the callee set is not syntactic. Three options:

- **(a) Whole-program closure** — every method typed. Trivial to check, collapses to
  today's fragment, gives up the scope advantage. Useful as a first milestone only.
- **(b) Type-directed closure** — use the receiver's static type to determine the callee.
  The right answer, and **benignly circular**: it needs `HasType` (M4), and the
  circularity resolves as a greatest fixpoint (start from the sig'd methods, drop those
  with a kind-(iii) callee, iterate).
- **(c) Dynamic closure** — check at each call from typed code whether the callee is typed.
  This is transient enforcement again; a proposal for changing Sorbet, worth evaluating
  with our semantics but not a description of it.

---

## 7. Measuring the rely condition: taint tracking in the model

The assume-guarantee route only works if the assumption is *measured* rather than hoped
for, and here the executable semantics is an instrument nobody else has:

> Mark values originating in untyped frames, propagate the mark through `stepFn`, and flag
> when a marked value reaches a type-relevant operation inside a typed frame.

This is a dynamic reading of R1/R2, and it gives:

- **M0 answered empirically** — how often untyped data actually reaches typed code in real
  programs, rather than a static over-approximation of how often it *could*;
- **witnesses generated rather than hand-written** — the four in §2 took a conversation to
  find; a tainting run over a corpus finds them mechanically;
- **a validator for whatever static condition we eventually write** — static closure should
  imply zero taint violations across the corpus, which is a falsifiable link between the
  syntactic condition and the semantic one.

Mechanism has precedent: the concolic engine already carries shadow values alongside
concrete ones (`lean/RubyCore/Concolic/Shadow.lean`), so this is a second shadow field, not
new machinery. It is the project's standing move — run the property before proving it.

---

## 8. Validating the checker: one-directional difftest against `srb`

**[Supersedes the first draft's plan.]** That draft proposed comparing inferred types at
`T.reveal_type` sites. That is a development aid, not a trust argument, and it tests
neither direction that matters. What matters:

**Soundness is proved, not tested.** `C accepts P ⇒ P safe` (under R1/R2) is a Lean
theorem, independent of Sorbet's existence. What difftesting buys is **relevance** —
evidence that `C` formalizes *Sorbet* rather than a type system we invented. So the
relation to test is one-directional:

> `C` accepts ⇒ `srb` accepts

Failures in the other direction (`srb` accepts, `C` does not) are **incompleteness**, which
is the expected state of a growing checker and must not be a failure.

### 8.1 The verdict taxonomy

`C` is four-valued, and each verdict carries its own relation:

| `C` says | semantic content | relation to `srb` | a violation means |
|---|---|---|---|
| `accept` | safe — *proved*, under R1/R2 | must ⇒ `srb` accepts | `C` over-claims: fix `C`, or we found an `srb` bug |
| `reject-witnessed` | here is a replayable trace to a type error | **may disagree** | nothing — the disagreement *is* the finding |
| `reject-syntactic` | our rules cannot type it | should ⇒ `srb` rejects | `C` over-claims: downgrade to `unknown` |
| `unknown` | no claim | none | — |

Three things this gets right:

- **`reject` cannot mean "unsafe".** A call to a missing method may sit on a dead branch,
  so a rejectable program can be perfectly safe — the classic asymmetry. Syntactic reject
  is a claim about *our rules*, and the `srb` comparison is what keeps it honest.
- **Reject rules need the same care as accept rules.** "Method does not exist on the
  receiver" is safe only when the receiver's type is known: `x.no_such_method` on
  `T.untyped` is *accepted* by srb [V: `untyped-boundary/000`]. Where a real type is in
  hand, srb agrees and rejects with 7003.
- **`reject-witnessed` is the one verdict allowed to disagree**, and it is exactly the
  unsoundness catalogue already in `difftest/corpus/sorbet/` — so the checker and the
  catalogue become one output vocabulary instead of two projects.

### 8.2 Ratchet

`unknown` absorbs all growing pains, so the metric is: **unknown ↓, accept-disagreements =
0, reject-syntactic-disagreements = 0**, witnessed disagreements a number you *want* to
grow. Two pinned zeros instead of one; still monotone.

The discipline this imposes: moving a program `unknown → reject` is exactly as risky as
`unknown → accept`, and needs the same guard. `unknown` stays the default; `reject` is a
deliberate, tested assertion. The failure mode to avoid is treating reject as the safe
default for anything `C` dislikes.

### 8.3 Architecture and attribution

Certifying-checker pattern: `check : Expr → Verdict` (total, executable, difftested), plus
`theorem check_sound : check P = .accept → HasType P`, plus the safety theorem. The
executable function is what runs; the `Prop` and theorems are what make its "yes" mean
something.

`C` is per-method, `srb` reports by line, so the relation is *"`C` accepts `M` ⇒ `srb`
reports no error within `M`'s line range"*. We cannot produce line numbers (the AST has
none) but we can consume srb's.

The engine already accommodates all of this: the per-SUT comparator hook takes the case
(difftest N31), and `AGREE_WEAKENED` is precedent for a verdict counted separately without
failing the run.

Note this largely **dissolves `Types/Fragment.lean`**: `C`'s `unknown` already encodes the
scope, since it refuses on `T.unsafe`, missing sigs and the rest. The fragment predicate
becomes an early, cheap approximation of `C` rather than a separate artifact.

---

## 9. What exists and transfers

| Asset | Where | Role here |
|---|---|---|
| `isBlame`, blame vs genuine error | `Proof/SorbetSafety.lean` | the property is about blame; proved |
| `invariant_reaches` / `*_invariant_sound` | `Proof/TypeSafety.lean` | bad-state-agnostic; third swap |
| Direction-A certificates | `SorbetSafety.lean`, `SorbetConcrete.lean` | `reject-witnessed` is exactly this |
| **The `T` prelude shim** | `prelude/prelude.rb` (L80) | **load-bearing**: without enforcement in the model, "at the boundary" vs "inside typed code" is not a distinguishable event, and §5's local proof has nothing to discharge its precondition |
| `Frame.meth` / `Frame.defmod` | `Machine.lean` | attribution, no model change [V] |
| Shadow values | `Concolic/Shadow.lean` | precedent for §7 tainting |
| tier-4 corpus, `sorbet check` | `difftest/` | shim fidelity; the witness catalogue |
| `Types/Fragment.lean` | Lean | early approximation of `C` (§8.3) |

---

## 10. Milestones

| # | Work | Exit criterion |
|---|---|---|
| **M0** | **Taint tracking (§7)** over the corpus and a real Sorbet codebase: how often does untyped data reach typed frames? | A number, plus auto-found witnesses. **If untyped data reaches typed code everywhere, R2 is not a plausible assumption and the direction needs (b) or (c) — stop and re-plan.** |
| **M1** | Per-method typed portion + call-graph closure(a) in Lean; `rubycore --typed-portion`; `sorbet check` gains the column. | Corpus report lists the typed portion per program; existing fragment numbers derived, unchanged. |
| **M2** | Bad state on configurations; the R1/R2 statement; `typed_portion_invariant_sound`; Direction-A certificates. | Axiom-clean; `untyped-boundary/002–005` certified as violations by execution; `sig-basic/000` safe. |
| **M3** | `C` as a decision procedure with the §8.1 taxonomy, difftested one-directionally; plus the **RBI-conformance** probe for builtins the corpus calls. | Both pinned zeros hold on the corpus; unknown-count ratchet established. |
| **M4** | `HasType` T1+T2 over method bodies. | Unknown count declining, zeros held. |
| **M5** | The per-method obligation (§5) proved for the T1 fragment, R1 depth question settled. | One real corpus method proved, assumptions explicit. |
| **M6** | Compose: closure + per-method obligations + R1/R2 ⇒ `TypedPortionSafe`. | The theorem, over a named set of corpus programs. |

M0 is first and is deliberately an **off-ramp**: it is the cheapest milestone and the only
one that can say the direction is not worth pursuing.

---

## 11. Open questions [?]

- **[?] R1 depth** (§4.3): restrict or induct.
- **[?] Rescued-vs-uncaught** attribution (§4.2): strict or uncaught-only.
- **[?] Are there channels beyond the four?** Class variables, globals, constants, and
  `self` set up by untyped code are all candidates and none is tested yet. Tainting (§7)
  would find them mechanically rather than by enumeration — a further argument for doing
  M0 first.
- **[?] `T.cast` inside typed code.** Statically trusted but runtime-checked, so it is an
  admissible *checked* boundary for this property even though it must be excluded from a
  *static* soundness fragment. Confirms the fragment predicate is theorem-relative;
  parameterize it rather than hard-coding one theorem's criteria.
- **[?] Shim limitation to remove before M3:** a sig declaring a block parameter cannot be
  matched positionally against the argument list, so the shim gates
  (`untyped-boundary/003` is currently `unsupported` against `--sut lean`). Honest, but it
  blocks that witness from being certified in-model.

---

## 12. Relation to the rest of the workspace

- The bad-state swap is the third instance of the pattern in
  [`../../type-safety-by-reachability.md`](../../type-safety-by-reachability.md): one
  engine, one metatheorem, a swappable bad state (effect violation → type-stuck →
  non-blame type-stuck → **typed-frame type error**).
- §5's local obligation with a runtime-checked precondition is the *guarded* enforcement
  strategy of [`types-and-preservation.md`](types-and-preservation.md) §B.5; §3.2(c) is
  the same literature's *transient* branch.
- R2 is a rely condition in the rely-guarantee sense; the ownership route §3.2(b) is where
  separation-logic machinery would enter if this direction is pushed hard.
- Fidelity of all of it rests on the `T` shim agreeing with the real gem — the tier-4
  ratchet (`difftest/README.md`) — the same trust architecture as the model itself: prove
  over the semantics, difftest the semantics against reality.
