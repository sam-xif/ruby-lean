# Design decisions

How the rules on the previous pages became the Lean definitions in
`ruby-lean/RubyCore/`, and why they have the shape they do.

## `require`

Core boot evaluates `prelude/prelude.rb`; optional
feature bodies remain decoded programs until `require`. A modeled require enters
a fresh top-level frame with `self = main`, `defmod = Object`, empty lexical
nesting and Object as its constant fallback. The caller's locals and namespace do
not become the feature's.
The heap, globals and effects remain shared. **[V]**

The machine distinguishes loading, completed and attempted features. A completed
or recursively loading feature returns false; successful execution records the
feature and returns true. An escaping exception clears only its loading state:
effects survive, and a later require retries. Attempted-feature API inventories
remain available after a failure so missing dependency APIs cannot become false
negative constant or method answers. These lists stay shared across Enumerator
suspension. **[V]** (cache, scope and unwind are compared to CRuby with identical
small feature bodies; the modeled optional libraries remain partial.)

`json`, `uri`, `forwardable`, `sorbet-runtime` and the `pathname.rb` wrapper have
registered bodies; `.rb` aliases share a cache key. CRuby 4.0.5 already loads
`pathname.so` at startup, so Pathname belongs to core boot. JSON installs its real
generator mixin hierarchy. Standalone execution begins without JSON; the
differential adapter passes `--preload-json` because its control wrapper requires
JSON before the program. **[V]**

Filesystem resolution, `require_relative`, feature path conversion, loader-global
paths/mutation and unknown libraries remain explicit gates. Partial library
bodies gate user definition hooks and frozen target namespaces when omitted
upstream declarations would change the callback order or first failing write.
Forwardable's body matches the 1.4.0 method declarations and order, so its
method hooks and frozen writes execute normally, including failed-load retry.
Its source generator emits real RubyCore definitions with argument, keyword and
block forwarding for simple method, ivar and constant accessors. General accessor
expressions, source-position warning paths and source-generator overrides remain
explicit gates. This compiler is specific to Forwardable, not general string eval.
Existing class/module conflicts gate when their diagnostic requires
the original source position. This does not claim full standard-library or
Sorbet-runtime conformance.

## Two definitions of a step

Two definitions coexist: `inductive Step` (`books/Books/Metatheory/Machine/Step.lean`) is the definition of
record, and `stepFn` + `run fuel` (`Interp.lean`) is what executes. The adequacy
theorems in `books/Books/Metatheory/Machine/Adequacy.lean` are the bridge — differential testing earns
trust for the *interpreter*, proofs live on the *relation*, and adequacy transfers
the empirical trust across. Deliberately, the interpreter landed **first**, so the
model could meet the differential engine on day one rather than after coverage
grew.

## Three decisions taken from prior work

Three decisions carried over from earlier formalizations of Ruby:

**Generativity is frame identity.** *The Essence of Ruby* (Ueno et al., APLAS'14)
observed that `return`/`break`/`next` destinations cannot be statically labeled —
the same `break` in a recursive method-with-block targets a *different* activation
each time — and modeled it with ML-style generative exceptions: a fresh tag per
call, per block creation, per yield, with a dead tag meaning `LocalJumpError`.
Right concept, wrong substrate for Lean. Here every activation has a unique
`FrameId`; a `Proc` captures the ids it returns and breaks to; a jump unwinds
searching for its target id; **a target id no longer on the stack *is*
`LocalJumpError`.** Tag liveness is frame presence — one mechanism, no meta-level
exception layer. (Their SML interpreter failed the detached-`Proc`-`break` test for
exactly the reason this formulation gets right by construction.)

**Frames live in a store, not on the stack.** Their control calculus keeps locals
in a variable store with environments mapping names to *references*, because
blocks share their defining scope's locals mutably. Here the configuration holds a
frame store `FrameId ⇀ Frame` and the activation stack is a list of ids. That one
mechanism delivers **both** of their stores at once — shared mutable locals *and*
generative jump targets. It is the central data decision.

**Heap operations are a module boundary.** Their object/control split composed two
relations through an "oracle"; a single relation over one configuration is simpler
to mechanize and to run, so what is kept is the interface discipline it proves
possible: `classOf`/`ancestors`/`lookup`/ivar and const access are *pure functions
on the heap*, in their own module with their own lemmas, and the step relation
touches the heap only through them. Sections 01–02 stay provable independently of
[section 04](control-flow.md).

## What was rejected

Rejected: **big-step** (hides effect order, makes
`ensure`-during-unwind awkward, cannot express divergence); **generative
exceptions as the mechanism** (see above); and **maximal linearization** — RIL
(Furr et al., DLS'09) flattens every side-effecting subexpression to a temporary
because its consumer is static dataflow analysis, whereas a nested-evaluation
semantics already handles compound subexpressions correctly, so RubyCore
linearizes *minimally* and stays small, which is what keeps the metatheory
tractable.

What RIL does contribute: the **pipeline split is validated** — Lean does not parse
Ruby, it consumes RubyCore JSON from the separately-difftested Ruby front end, over
a versioned wire format either side can reject. And RIL §3.2's **evaluation-order
obligations are semantics, not just desugaring**: `a().f = b().g` and
`a().f, x = b().g` evaluate their parts in *different* orders, and that has to hold
in the step relation's own argument-evaluation rules. Those became early
adversarial seeds.

One component was not foreseen by any of this and proved load-bearing:
`CRubyNames.lean`, the oracle-generated method and constant name tables (00 §6).

## Open

Still open **[?]**: the frame store grows monotonically
(dead frames are retained — fine while fuel bounds everything); how much builtin
behavior stays a `Payload` primitive versus migrating into the Ruby prelude; and
`run fuel` conflating "diverges" with "fuel exhausted", which is why `RunResult`
distinguishes `outOfFuel` from `stuck` from day one even though the co-divergence
check itself is deferred.
