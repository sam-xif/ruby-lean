# Typed-portion safety — a plan of attack

> **Status:** plan, drafted 2026-08-06. Nothing here is built. It supersedes nothing:
> the whole-program runtime statement of
> [`types-and-preservation.md`](types-and-preservation.md) §C.1 option 2 is *proved*
> (`lean/RubyCore/Proof/SorbetSafety.lean`, L81) and this is a **different, weaker, more
> useful** property that reuses most of the same machinery.
>
> Evidence tags per the house convention ([`README.md`](README.md)): **[V]** verified
> against CRuby/`srb` in this workspace, **[D]** documentation or literature, **[?]** open,
> to settle before or during mechanization.

---

## 1. The property, and why this one

**Informally:** *a type error never occurs inside typed code.* Untyped code may fail
however it likes; when it hands bad data to a sig'd method, the sig wrapper catches it and
blame lands on the caller. This is the **blame theorem** shape — "well-typed programs
can't be blamed" [D: Wadler & Findler, ESOP 2009; §B.5 of `types-and-preservation.md`].

Three candidate theorems, and why this is the one to chase:

| Target | Status | Problem |
|---|---|---|
| Static soundness on `# typed: strong` | not started | `strong` is beta and rare; the theorem would be true and about almost no code |
| Whole-program runtime three-outcome safety | **proved** (L81) | needs the *whole program* in the fragment — 3 of 19 corpus programs, and essentially no real codebase |
| **Typed-portion safety** | this document | needs a closure hypothesis (§2), and the boundary checks are shallower than the sigs (§7.2) |

The decisive advantage is scope. Sorbet codebases are **partially typed by design** — that
is the entire point of gradual typing — so any whole-program hypothesis is unsatisfiable
on real code. A per-method claim applies to every sig'd method in a mostly-untyped
codebase, which is what people actually have. It also matches what a Sorbet user believes
they are buying, which makes it the theorem worth being able to state.

Secondary advantage, developed in §7: the property is **local**, so the proof is
per-method rather than whole-program.

---

## 2. The counterexample that shapes the statement

The naive property is **false for Sorbet**. `difftest/corpus/sorbet/untyped-boundary/002.rb`
[V]:

```ruby
# typed: true
def untyped_source          # no sig ⇒ return type is T.untyped
  "not an integer"
end

sig { returns(Integer) }
def typed_consumer
  v = untyped_source        # crosses INTO typed code, unchecked
  v + 1                     # TypeError raised HERE, inside the typed body
end
```

`srb tc` says **"No errors! Great job."** [V]; CRuby raises
`TypeError: no implicit conversion of Integer into String` inside `typed_consumer` [V]. No
escape hatch is used — just a missing sig.

**Diagnosis.** sorbet-runtime is *guarded* at sig'd method boundaries: it wraps the sig'd
method and checks its own parameters and return. An **unsigned** method has no wrapper at
all, so nothing is checked in either direction; and statically, assigning `T.untyped` to
anything is permitted [D: /docs/untyped]. The value therefore crosses with no check on
either side of the call.

**Consequence.** The theorem needs a hypothesis that untyped values can only enter typed
code *through a checked boundary*. That is a **call-graph closure** condition, and it is
the single most important structural addition this direction requires.

---

## 3. Three kinds of callee (the refinement that makes closure affordable)

Naively "closed under calls" would mean typed code may only call typed user methods, which
would exclude essentially everything (all real code calls the stdlib). But there are three
kinds of callee, not two:

| Kind | Statically typed? | Runtime-checked? | Verdict |
|---|---|---|---|
| **(i)** sig'd user method | yes | **yes** — the wrapper | safe boundary |
| **(ii)** builtin / stdlib declared by an RBI | yes (Sorbet ships RBIs) | **no** — sorbet-runtime does not wrap the stdlib | safe *in our setting*, see below |
| **(iii)** unsigned user method | no (`T.untyped`) | no | **the hole** — must be excluded |

Kind (ii) is the interesting one and it is where our setting is *better off than Sorbet's*.
Sorbet trusts its RBI declarations with no runtime backstop. We do not have to trust them:
**the model defines the builtin**, so instead of a runtime check we get a proof obligation
—

> **RBI-conformance obligation.** For every builtin the typed portion calls, the model's
> implementation conforms to Sorbet's RBI declaration for it.

— which is *separately and differentially checkable* (§8, M3), not assumed. Where Sorbet
has an unchecked trust boundary, we have a testable lemma.

So **closure means: every callee of a typed method is of kind (i) or (ii), never (iii)**.
That admits ordinary code that calls the stdlib freely, which is what makes the hypothesis
plausibly inhabited. Measuring whether it actually is, on real code, is milestone M0.

---

## 4. The formal statement

### 4.1 What must change about the bad state

`SorbetSafety.lean` defines the bad state as a property of a **terminal `StepResult`**:

```lean
def sorbetStuck : StepResult → Prop
  | .uncaught exc m => isTypeError m.heap exc ∧ ¬ isBlame m.heap exc
  | _ => False
```

Typed-portion safety is not an outcome property — it is about *where* the error is raised.
So the bad state moves to the **machine configuration at the raise**:

```lean
/-- The activation currently executing, as (owning module, method name). -/
def currentMethod (m : Machine) : ObjId × String :=
  (m.currentFrame.defmod, m.currentFrame.meth)

/-- About to raise a type-family exception from inside a typed method's frame. -/
def blamesTypedCode (P : TypedPortion) (m : Machine) : Prop :=
  raisesTypeFamily (stepFn m) ∧ P.contains (currentMethod m)

def TypedPortionSafeFrom (P : TypedPortion) (m₀ : Machine) : Prop :=
  ∀ m, Reaches m₀ m → ¬ blamesTypedCode P m
```

**Frames already carry what this needs** [V]: `Frame.meth` ("name of the method this
activation is running") and `Frame.defmod`, both in `lean/RubyCore/Machine.lean`. No model
change is required to *state* the property — a pleasant surprise, and worth checking
before designing around it.

Two definitional decisions to make explicit:

- **Attribution is by *raising* frame, not by unwinding path.** An error raised in an
  untyped callee that propagates *through* typed frames on its way out is attributed to
  the untyped frame. This is the right choice (it matches blame-calculus attribution) and
  it must be stated, because the alternative reading makes the theorem false for trivial
  reasons.
- **Rescued errors.** `typeStuck` deliberately counts only *uncaught* outcomes
  ("raised ≠ stuck", `type-safety-by-reachability.md` §2). Here the natural reading is
  stricter: a type error raised inside typed code is a defect even if typed code catches
  it. **[?]** Decide: strict (any raise in a typed frame) or uncaught-only. Strict is more
  informative and is what a Sorbet user expects; uncaught-only composes better with the
  existing development. Recommendation: strict, with the uncaught variant derivable.

### 4.2 The metatheorem

Unchanged in shape from L81 — this is the **third** swap of the bad-state predicate, after
`typeStuck` and `sorbetStuck`, which is the running thesis of
[`../../type-safety-by-reachability.md`](../../type-safety-by-reachability.md):

```lean
theorem typed_portion_invariant_sound (P : TypedPortion) (I : Machine → Prop)
    (init : I m₀)
    (cons : ∀ m m', I m → SmallStep m m' → I m')
    (safe : ∀ m, I m → ¬ blamesTypedCode P m) :
    TypedPortionSafeFrom P m₀
```

This is a five-line proof reusing `invariant_reaches`, and it is not the interesting part.
The interesting part is §7.

---

## 5. What already exists and transfers

| Asset | Where | Role here |
|---|---|---|
| `isBlame` + the blame/genuine-error distinction | `Proof/SorbetSafety.lean` | the property *is* about blame; already proved |
| `invariant_reaches` / `*_invariant_sound` | `Proof/TypeSafety.lean` | bad-state-agnostic; third swap |
| Direction-A execution certificates | `Proof/SorbetSafety.lean`, `SorbetConcrete.lean` | transfer with the new predicate |
| **The `T` prelude shim** | `prelude/prelude.rb` (L80) | **load-bearing**: without enforcement in the model, "at the boundary" vs "inside typed code" is not a distinguishable event and the property cannot be *stated*, let alone proved |
| `Frame.meth` / `Frame.defmod` | `Machine.lean` | attribution, with no model change [V] |
| tier-4 corpus + `sorbet check` | `difftest/` | fidelity of the shim; the witness catalogue |
| `Types/Fragment.lean` | Lean | the whole-program *degenerate case* of the per-method predicate — generalizes, not wasted |

---

## 6. What must change

1. **`Fragment.lean` becomes per-method plus closure.** Today: `Expr → Bool` over a whole
   program. Needed: (a) `typedMethods : Expr → List (Owner × Name)` — the sig'd methods
   whose bodies use no escape hatch; (b) a closure check that every callee is kind (i) or
   (ii). The current predicate is exactly "every method is typed", so it survives as a
   corollary.
2. **The bad state moves from outcome to configuration** (§4.1).
3. **A call graph is needed**, and this is the genuinely hard new ingredient — see below.

### 6.1 The call-graph problem, and three ways out

Ruby dispatch is heap-dependent, so "the set of methods this typed method can call" is not
syntactically determined. Three options, in increasing order of both fidelity and cost:

- **(a) Whole-program closure.** Require *every* method in the program to be typed. Sound,
  trivial to check, and collapses back to today's fragment — i.e. it gives up the scope
  advantage that motivated the whole direction. Useful only as a first milestone.
- **(b) Type-directed closure.** Use the receiver's *static* type to determine the callee
  set: if `x : Foo` and `Foo#bar` is sig'd, the call is kind (i). This is the right answer
  and it is **circular in a benign way** — it needs `HasType`, which is exactly what M4
  builds, and the circularity resolves because the closure check is a *fixpoint* over the
  typed portion (start with the sig'd methods, keep only those whose callees are in the
  set, iterate to a greatest fixpoint).
- **(c) Dynamic closure.** Check at each call *from* typed code whether the resolved callee
  is typed, and treat "not typed" as a boundary requiring a check. This is the **transient**
  enforcement strategy [D: Vitousek et al.; §B.5] and it is a *proposal for changing
  Sorbet*, not a description of it. Worth naming because it is the principled fix for the
  §2 hole, and because our semantics could evaluate it experimentally — but it is a
  different project from proving something about Sorbet as it is.

Recommendation: (a) as M1 to get the machinery end-to-end, (b) as the real target once M4
lands, (c) documented as an evaluated alternative, not built.

---

## 7. The proof architecture

### 7.1 Why runtime checks make this local — the payoff

To prove "no type error inside typed method `M`", the preconditions come **free from the
wrapper**: sorbet-runtime already checked `M`'s arguments against its sig at entry. So the
obligation per typed method is

```
   assume:  arguments satisfy the sig's parameter types  (discharged by the wrapper)
            every callee is kind (i) or (ii)             (closure, §3)
   prove:   the body raises no type-family error, and returns a value of the return type
```

This is a **local, per-method** obligation with the sig as pre/postcondition. Crucially it
does **not** need the global well-typed-heap invariant `Δ ⊨ H` that whole-program subject
reduction demands (`type-judgments.md` §8) — the boundary is where the assumption is
discharged by an actual runtime check instead of by an inductive hypothesis. That is the
guarded/contract shape of §B.5, and it is dramatically cheaper than whole-program
preservation.

### 7.2 …and the reason it is not free: checks are shallow

The wrapper checks `is_a?`. For `sig { params(xs: T::Array[Integer]) }` it verifies only
that `xs` is an `Array` — the element type is **erased** [D: §A.6, and reproduced in the
model, L80]. So the precondition the wrapper actually gives us is *weaker than the sig*:

```
   sig says:      xs : T::Array[Integer]
   wrapper gives: xs.is_a?(Array)
   the body may rely on:  xs.first + 1     ← not justified by the wrapper alone
```

This is the same erasure fact from §A.6 biting in a new place, and it is the central
technical risk of this direction. Three responses:

- **Restrict:** exclude parameterized types from boundary-crossing positions in the typed
  portion. Sound, and probably too restrictive to be useful — real typed Ruby is full of
  `T::Array[String]`.
- **Induct:** carry the depth statically. If the *caller* is also in the typed portion and
  its sig was satisfied deeply, the element types hold by induction over the typed portion
  — the shallow runtime check is then only needed at the *entry points* where untyped code
  calls in. This is the right answer and it makes the theorem's shape:
  *deep types hold throughout the typed portion, given they hold at its entry points* —
  with entry points the one place needing a deep check.
- **Deepen the checks:** RTTI at the boundary, à la Safe TypeScript [D: §B.3]. Again a
  change to Sorbet, not a description.

**[?]** This choice determines whether the theorem is about Sorbet-as-is (restrict) or
Sorbet-plus-an-assumption (induct, with deep entry checks as the assumption). Settle it
before M5.

### 7.3 What `HasType` is still needed for

All of it. "No type error inside `M`'s body" is a claim about the body, so the T1–T2
staging of [`type-judgments.md`](type-judgments.md) is still required. What changes is the
*scope*: T1 (control core) plus T2 (`send`) over **method bodies**, with sigs as the
interface, rather than a whole-program judgment. That is a smaller and much more
incrementally useful target — every method typed is a method the theorem covers.

---

## 8. Milestones, each with a checkable exit criterion

| # | Work | Exit criterion |
|---|---|---|
| **M0** | **Measure inhabitance.** Run a per-method typedness + closure(a) count over a real Sorbet codebase, not just our corpus. | A number: what fraction of sig'd methods are in a closed typed portion. **If it is near zero, stop and reconsider** — this milestone exists to be able to abandon the direction cheaply. |
| **M1** | Per-method `TypedPortion` + closure(a) in `Types/Fragment.lean`; `rubycore --typed-portion` reports it; `sorbet check` gains the column. | Corpus report lists the typed portion per program; the whole-program fragment is derived from it and the existing numbers are unchanged. |
| **M2** | Bad state on configurations; `typed_portion_invariant_sound`; Direction-A certificates. | Axiom-clean; `untyped-boundary/002` certified as a *violation* by execution, and `sig-basic/000` as safe. |
| **M3** | `T.reveal_type` oracle harness, comparing by `srb_type <: our_type` (§ the conversation of 2026-08-06); plus the **RBI-conformance** probe for builtins the corpus calls. | Site-by-site agreement report with a three-valued gate; unknown-count ratchet established. |
| **M4** | `HasType` T1+T2 over method bodies, driven by M3. | Reveal-type agreement above a threshold on the corpus, 0 disagreements, unknowns declining. |
| **M5** | The per-method obligation (§7.1) proved for the T1 fragment, with the §7.2 depth question settled. | One real corpus method proved, with its assumptions explicit. |
| **M6** | Compose: closure + per-method obligations ⇒ `TypedPortionSafe`. | The theorem, over a named set of corpus programs. |

M0 before M1 is deliberate. It is the only milestone that can tell you the direction is not
worth pursuing, and it is the cheapest.

---

## 9. Open questions [?]

- **[?] Blocks and procs.** A typed method that `yield`s to a block supplied by untyped
  code: sorbet-runtime validates that the block *parameter* is a `Proc` (the
  `Block parameter` message family, L80) but nothing about what the block returns. This
  looks like a second instance of the §2 hole, on a different channel. Verify against the
  gem and, if confirmed, add a corpus witness — it would further constrain the closure
  condition.
- **[?] Instance variables.** A typed method reads `@x` declared via `T.let`; an untyped
  method in the same class writes `@x` directly with no check. A third crossing channel,
  and unlike §2 it is not a call at all, so closure over the call graph does not cover it.
  Likely needs the typed portion to own its ivars, or a per-class condition.
- **[?] Rescued-vs-uncaught** (§4.1): strict or uncaught-only.
- **[?] Depth** (§7.2): restrict, induct, or deepen.
- **[?] `T.cast` inside typed code.** Statically trusted, runtime-checked — so it is a
  *checked* boundary and admissible for this property, even though it must be excluded from
  a *static* soundness fragment. Confirms that the fragment predicate is theorem-relative
  (see the 2026-08-06 discussion); make sure the per-method predicate is parameterized
  accordingly rather than hard-coding one theorem's criteria.

---

## 10. Relation to the rest of the workspace

- The bad-state swap is the third instance of the pattern in
  [`../../type-safety-by-reachability.md`](../../type-safety-by-reachability.md): one
  engine, one metatheorem, a swappable bad state (effect violation → type-stuck →
  non-blame type-stuck → **typed-frame type error**).
- The per-method obligation with a runtime-checked precondition is the *guarded* enforcement
  strategy analyzed in [`types-and-preservation.md`](types-and-preservation.md) §B.5; the
  transient alternative of §6.1(c) is the same literature's other branch, and Safe
  TypeScript's forward simulation (§B.3) is the closest existing theorem to §7.2's
  "deepen the checks" option.
- Fidelity of everything here rests on the `T` shim agreeing with the real gem, which is
  the tier-4 ratchet (`difftest/README.md`) — the same trust architecture as the model
  itself: prove over the semantics, difftest the semantics against reality.
