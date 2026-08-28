# The slot frame — local heap stability as a first-order resource algebra

**Design artifact (2026-08-28). Designed, not built.** Origin: a design conversation
against the machinery as it stands after J56, starting from the observation that the
judgment layer's blockers (the four-row table, the mixin arithmetic, unchecked bodies,
`HTy`'s undecidability at the certificate boundary) are symptoms of one structural
absence: **no way to say a heap fact is *locally* stable**, so stability is bought
globally (`declaresName`, name-global) or not at all. Decisions are **SF-numbers**.

Companion: [`../../homebrew/slice-inventory.md`](../../homebrew/slice-inventory.md) —
the semantic-judgment inventory this machinery is priced against.

**License to demolish, stated up front:** this design is not required to preserve the
existing machinery. Where a mechanism below subsumes an existing guard, the guard is
listed in §7 for removal, not accommodation. The things that *are* fixed points are in
§7.2 — chiefly the data-certificate posture (facts checkable by one kernel `Bool`, no
proof terms in the loop) and the soundness formula (`SemJudge` at a conformant start
state).

---

## §1 — The problem, with its three current stand-ins

Every typing fact in the system is a claim about a mutable method table.
`EntryOkJ A D h τ name sig` says: at heap `h`, everything of type `τ` resolves `name`
to a conforming body. Ruby's openness means any later step can falsify it, so every
fact needs an answer to *"why is this still true after the program runs?"* — and the
system has exactly one answer: **nobody, anywhere, ever installs that name.**

Three places pay for that answer today, and each one's own documentation admits it is
standing in for a locality argument nobody had a mechanism for:

1. **`declaresName` is name-global** (`Types/Decls.lean:329` — `D.rows.any … md.1 == name`,
   any class, any row). Its docstring: *"installing one they do mention is a
   redefinition, which F1c is where the conformance check lands. Until then a `def` of
   a declared name is `unknown`."* F1c is unbuilt; the placeholder is the sledgehammer.
   Consequences measured on the slice: the table holds `String#to_s` **or**
   `Version#to_s`, never both; three `include Comparable` need `<` claimed at three
   classes and can have it at one; `baseDecls` is four rows because each row's
   stability is priced against the whole future.
2. **`core-rows.txt` is "a choice of receiver per name"** (its own header) — not the
   core library, but the one-slot-per-name contortion the guard forces.
3. **`NoHook`'s `T::Sig` case is a prose frame argument** (`Proof/Static/Decls.lean:2011`):
   *"the prelude's `T::Sig` legitimately carries `method_added` … reachable only from a
   class that `extend`s it — which the fragment never does."* A locality claim, argued
   by hand inside a global invariant.

The fix is the frame rule — `{P} e {Q} ⟹ {P ∗ R} e {Q ∗ R}` — specialized to the one
resource this system cares about (the method table) with a **decidable** disjointness
check, so it rides the certificate as data. Iris is deliberately *not* the vehicle
(§8), but the algebra is written as a PCM so the Iris lift stays mechanical if a
construct ever needs the general rule.

## §2 — The model: a class is a slot map with a default

**SF1.** A class object `K` is modeled, for stability purposes, as

```
slots(K)  =  finite map (name ↦ body)  ⊎  default(K)
```

infinitely many slots, co-finitely empty. Three primitive facts about `(K, m)`:

| fact | meaning | machine reading |
|---|---|---|
| `defined K m md` | the slot is filled with `md` | `(methods of K).find m = some md` |
| `empty K m` | the slot is known empty | `… = none` **and** `default(K)` is inert |
| `dflt K` | the default component's state | `method_missing` absent from `K`'s table |

`empty` is the ownable form of the negative fact `ResolvesAt`'s shadow clause needs
(`crubyShadow … = none` is an absence quantified over a chain — unownable cell-wise,
ownable as slot resources along the segment).

**SF2 — `method_missing` is a write to `default`, not to any named slot.** It
populates all unfilled slots at once *because* they are all derived from one resource.
Consequences: `defined` readers are untouched by a `method_missing` install (positive
resolution wins); **every `empty` reader on a chain through `K` is invalidated at
once**. This is a *new* obligation: today `hookFreeNames = ["method_added",
"define_method"]` (`Types/Decls.lean:694`) omits `method_missing`, soundly, because
nothing in the system owns emptiness yet. The moment `empty` is a resource,
`method_missing` becomes load-bearing. Priced in §5's conflict check; measured cost on
the slice: zero (no slice file defines it).

**SF3 — resolution is a projection over the chain.** `ancestors` (`Heap.lean:527`)
lays out `prepends.reverse ++ [k] ++ includes.reverse ++ super-chain`; resolution of
`(C, m)` is the fold over that list, front slot winning. So a `Row` claim owns a
*prefix* of the projection: `empty` on every slot before the owner, `defined` at the
owner. Note what this makes `prepend`: a write **into the head** of every projection
through `C` — which is why the chain's shape is itself a resource:

**SF4 — `spine C seg`**: the segment of `ancestors` from `C` to the owner, as a value.
A reader of `spine` is invalidated by `include`/`prepend`/`extend` landing anywhere on
the segment (they change *which slots the projection consults*, the linked-list-spliced-
from-outside case). `alias` under this model is a slot **copy** — reader on `(K, old)`,
writer on `(K, new)` — and `zsuper` is a **read of the superclass's slot**, which is
why the Token hierarchy (13 `class-sup` + 9 `zsuper` sites) is native to this model
rather than an extension of it.

## §3 — The resources as a partial commutative monoid

**SF5.** Claims compose by disjoint union with agreement:

```lean
/-- One claim's footprint: what it reads. All three read-only — see SF6. -/
structure SlotClaim where
  defined : List (ObjId × String × MethodDef)   -- agreement required on overlap
  empty   : List (ObjId × String)                -- freely duplicable
  spines  : List (ObjId × List ObjId)            -- segment of ancestors, as data
  noMM    : List ObjId                            -- default(K) inert, per chain class

/-- Composition: defined-overlap must agree; everything else unions.
    `none` is conflict. This is the gmap-RA shape — the Iris lift is mechanical. -/
def SlotClaim.compose : SlotClaim → SlotClaim → Option SlotClaim
```

**SF6 — reads are duplicable; writes are not resources at all.** This is the decision
that keeps the logic first-order, and it is worth stating as the theorem it replaces:
in a general separation logic, a writer *acquires* exclusive ownership and the logic
tracks the transfer. Here there is **one linked program and one enumerable claim
set** — a closed world — so the writer's obligation is discharged by *enumeration*:
the checker lists every table-mutating action the program performs and verifies none
lands on a slot or spine any claim reads. No fractions, no ghost state, no transfer.
Where the closed world fails (a `define_method` over a computed list, `Class.new` in a
loop, runtime `prepend`), the claim simply cannot be made and the case exits to
`HJudge.wp` (§8) — the same fast-path/slow-path split `Judge`/`SemJudge` already has,
one level down.

**SF6a — what "closed world" means, exactly.** *Closed write-site inventory with
literal name keys* — **not** closed input space. A program over serialized input
(argv, a JSON feed) is fully inside the frame: the conflict check enumerates
table-mutating *sites*, which a static text fixes regardless of input, and it already
assumes every site may execute, so input selecting a path subset only adds slack.
Input varying over a typed domain is the system's normal quantification
(`SemJudge` at every conformant start state) and the same posture as the concolic
design (`bounded-effect-checking.md`: concrete boot heap, symbolic inputs). The
boundary is **data laundered into the name coordinate of a write site** —
`define_method(argv[0])` keeps the site enumerable but forces its key set to ⊤ at
the name coordinate, conflicting with every `empty` reader through that class;
`eval` makes the site inventory itself dynamic and is already desugar-gated.
Soundness is never at stake; completeness is lost exactly at laundering sites, and
that loss is **accepted as a feature**: a rejection there flags code whose
metaprogramming is driven by unvalidated input — a defensiveness signal to the
programmer, not a checker deficiency to engineer away. (A computed *dispatch*,
`obj.send(name)`, is not a write and is invisible to the frame — it is untypable
for the ordinary no-`Row`-for-an-unknown-name reason.) The `wp` door remains for
the site a hand proof can bound, e.g. a name drawn from a validated whitelist.

**SF7 — `Row` is derived, not primitive.** The assertion the type system consumes:

```
Row C m σ  ≜  spine C seg
            ∗ empty K m           for each K ∈ seg before owner
            ∗ noMM K              for each such K
            ∗ defined owner m md,  md conforming to σ
```

The footprint of a certificate is the composition of its Rows' claims — computed by
the emitter, carried as JSON, recomputed and checked by the validator. A reader can
audit it the way `carries:` is audited today.

**The two measured blockers, cleared by construction:** `Row Version "<" σ` and
`Row PkgVersion "<" σ'` share `defined Comparable "<" …` (agreement — same slot, same
body) and own disjoint `empty` segments: both coexist. `defined Version "to_s"`
touches no slot `Row String "to_s" …` reads (`Version` ∉ `String`'s chain): additive
monkey-patching of unrelated classes is free. Both are impossible today, and both are
one `compose` away here.

**SF8 — the write rule, corrected from the naive reading.** Writing `(K, m)` requires
*no outstanding reader on `(K, m)`* — not ownership of the slots in front of it. The
"front slots" intuition (to change a projection you must own everything ahead)
double-counts: the readers of `(K, m)` are already indexed by every chain through `K`,
so absence-of-readers on the one slot is exactly the projection-safety condition, and
it is enumerable where "own all subclass slots" quantifies over classes that do not
exist yet. Concretely:

| program action | conflicts with |
|---|---|
| `def m` / `defs m` / `alias new old` (the write half) at `K` | any `defined (K, m)` reader (overwrite) **or** any `empty (K, m)` reader (a new shadow) |
| `include`/`prepend`/`extend` M at `K` | any `spine` reader whose segment contains `K` |
| `def method_missing` at `K` | any `noMM K` reader |

Note the first row prices *additions*, not just redefinitions: adding a fresh `to_s`
at `Version` breaks `Row Version "to_s" …`-resolving-at-`Object` because `Version` is
on that Row's own `empty` segment. `declaresName`'s docstring's "additions are free"
was true only of the four-row table it guarded.

## §4 — The boot prefix is outside the frame

**SF9.** Claims are taken at the **conformant start state**, which `SemJudge` already
quantifies over — not at `Boot.initHeap`. Everything the boot stubs and the module/
class-definition prefix do (`class Module; include T::Sig`, the 8 slice-file ancestry
mutations, all of them class-body-position) happens *before* any claim exists and is
simply not framed. Measured (2026-08-28, the 8 slice files + boot stubs): **8 ancestry
mutations, every one in definition-position, zero runtime sends of
`include`/`prepend`/`extend`**. The chain graph is static after boot. This is the fact
that makes enumeration (SF6) sufficient for this target, and it should be re-measured
per target — a program that mutates ancestry mid-run pushes those claims to the `wp`
door, not to a redesign.

## §5 — The conflict check (what `validateJ` gains)

Decidable, over data, in this order:

1. **Collect** the certificate's composed footprint (SF7). Reject on `compose = none`.
2. **Enumerate installs**: walk the linked program (post-strip, the same AST the
   derivation is over) for `def`/`defs`/`alias`/`include`/`prepend`/`extend`/
   `method_missing`-defining heads, splitting boot-prefix from post-claim (SF9).
3. **Check disjointness** per SF8's table.
4. **Check `defined` witnesses** at the conformant heap — the existing
   `constOkB`-style boot-heap decision, per slot instead of per name-global row.

Step 2 is the honest cost of the closed world: an install the walk cannot see
syntactically (a computed `define_method`) makes the *program* rejectable, not the
check unsound — same polarity as every other gate in the pipeline.

**Adequacy (the "typed ⇒ stable" half):** every `Judge` admission route already
*performs* its installs in its conclusion (`defPromote` returns `addRow D cls name`;
the `defs` schema carries `freshNames`). SF10: promote that ad-hoc channel to a
uniform **install-set** on the judgment — each rule declares what it writes — and the
adequacy theorem is: *a derivation's declared install-set misses a claim's footprint ⟹
running the derived expression preserves that claim*. Then step 2's walk shrinks to
the **untyped remainder** of the program, and the check gets cheaper as the fragment
grows instead of staying whole-program forever.

## §6 — Theorem ladder

| rung | statement | anchor |
|---|---|---|
| **SF-T1** | `resolvesAt_defineMethod` generalized: hypothesis `¬(mname = name)` → *slot-disjointness* (`(cls, name)` not in the claim's `defined ∪ empty`, `cls` not on its spine) | `Proof/Static/Decls.lean:1298` — the existing lemma is the `name`-only special case |
| **SF-T2** | the `defineMethod` case of `step_okJ` re-proved with SF-T1; `DeclsOkJ A F m.heap` becomes `DeclsOkJ` *per framed claim*. `InvJ` already existentially quantifies `F` and threads it (`Proof/Judgment/Konts.lean:530`) — this rung changes how one premise is discharged, not the invariant's shape | `step_okJ` |
| **SF-T3** | install-sets on `Judge` (SF10) + adequacy: typed code frames every disjoint claim | new; subsumes `freshNames` |
| **SF-T4** | wire format: footprint in `JCert`, conflict check in `validateJ`, `validateJ_certifies` restated with the frame hypothesis | `Judgment/Json.lean`, `Check.lean` |

SF-T1 is deliberately first and small: **it is the frame rule for one step**, and it is
where the design meets the shadow clause (`crubyShadow` quantifies builtin-name
shadowing over the same segment `empty` owns — the two must decompose together). If
SF-T1 fights, we find out in one lemma, not after a layer.

## §7 — Demolition and fixed points

### §7.1 Removed or subsumed (licensed, not incidental)

* **`declaresName`'s name-globality** — replaced by the SF8 conflict check. The guard
  itself survives only as the degenerate footprint "every slot at this name."
* **`core-rows.txt`'s ONE-ROW-PER-METHOD-NAME rule** and the "choice of receiver per
  name" posture — rows become per-`(class, name)` slots; the String-vs-Integer `to_s`
  choice dissolves.
* **`SemClaim.freshNames`** — subsumed by SF10's install-sets (it is the `defs`
  schema's hand-rolled install-set).
* **`NoHook`'s `T::Sig` prose case** — becomes a `noMM`/hook-slot fact about a chain
  segment, checked, not argued.
* Candidate, not committed: `Types/Assn.lean`'s store-cancellation machinery overlaps
  SF7's `Row` (both are "requirements a sibling `def` discharges"); if SF-T3 lands,
  reconcile rather than maintain both.

### §7.2 Fixed points

* **The certificate is data; validation is one kernel `Bool`.** Every SF check is
  `decide`-able by construction; the moment a design variant needs a proof term in the
  certificate, it is the wrong variant (that door is `wp`).
* **`SemJudge`'s formula** (reachability at a conformant start state) — SF9 leans on
  it as-is.
* **`HJudge.wp` as the slow path** — the general frame rule for what enumeration
  cannot see. First-order slots foreclose nothing: SF5's PCM is the gmap RA, and the
  lift target is `HJudge/StateInterp.lean`.

## §8 — Why not Iris (recorded so it can be reversed on evidence)

Decidability is the binding constraint and has killed three designs already
(per-method generated lemmas; `HTy.sem : Heap → Value → Prop` at the certificate
boundary; any `wp` obligation as certificate content). The assertion language here is
four predicates; the closed world does the work the logic would otherwise do; the
J-layer metatheory is axiom-clean today and iris-lean sits in the H-layer only.
**Flip condition:** a target whose footprint needs existential quantification over
unboundedly many runtime-created classes — then enumeration fails, ghost state earns
its keep, and SF5's PCM discipline is what makes that migration a lift instead of a
rewrite.

## §9 — What this does not fix (so it is not oversold)

* **Signature expressiveness** — `MethodDecl` is one pinned signature; `Integer#/` at
  Integer *and* Float needs two. A frame doesn't help; that is the Tier-1
  call-shape-facts axis of the inventory.
* **Prelude witnessing** — `ResolvesUser` takes nullary prelude methods only
  (`md.params = []`); Comparable's `<` stays an *assumed* `defined` witness until that
  arity gap closes. The frame makes the assumption local and printable; it does not
  discharge it.
* **Behavioral block content** ("responds to `each` with a block yielding τ") — the
  recorded step-indexing flip condition (`HJudge/HTy.lean`), untouched here.
