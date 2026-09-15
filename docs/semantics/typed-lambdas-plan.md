# Plan — typed lambdas: check a lambda body against a Sorbet `T.proc` sig, then type distant `.call` sites

**Planning artifact, 2026-08-31. First-order only**: everything here lives in the
`Ty`/`ValueTy`/`Inv` world (`Types/`, `Proof/Static/`). No `HTy`, no Iris, no
step-indexing. Companion to `typing-the-slice-milestones.md` (this is a slice of its
M7 "Wall 2", worked out in full); the slot-frame and judgment-layer docs are *not*
prerequisites for stages L0–L4.

## 0. The problem and the design in one page

The slice stores lambdas as first-class values. The forcing example — read it before
anything else — is `homebrew/vendor/brew/Library/Homebrew/vulns/vulnerability.rb:197–218`:
`comparator_for(range_type)` **returns** a stabby lambda declared
`T.proc.params(a: String, b: String).returns(Integer)`; the caller binds it to `cmp`
and later invokes `cmp.call(target, upper)`. Inline-block machinery can never type
this: the arrow must ride a declaration row's return type, flow through a local, and
be consumed at a distant `call` send.

**Representation facts that drive everything** (verify, don't trust):

* A lambda is an ordinary heap object: `Object { klass := procId, payload := .proc c }`
  where `Closure` (`ruby-lean/RubyCore/Heap.lean:132`) holds `params`, `locals`,
  `body : Expr`, `captured : Nat` (a FrameId), `home : Nat`, `lam : Bool`.
* Creation: `lambda { … }` arrives as a send with implicit receiver, name `"lambda"`,
  and a block literal; `reifyBlock … (mkLam := true)` allocates the object
  (`ruby-lean/RubyCore/Interp/Send.lean:375–379`). Confirm during L0 that `->(){ }`
  desugars to this same form.
* Invocation: `callClosure` (`ruby-lean/RubyCore/Interp/Support.lean:418`) pushes a block
  frame whose parent is the **captured** frame; free variables of the body resolve up
  that chain. Frames are never deallocated (the frame store only grows), so an escaped
  lambda's captured frame is always live.
* Today's checker rule for a lambda literal is `Types/Core.lean:1137–1140`: it answers
  `.any` and deliberately does not check the body; the comment at `:1119–1134` reserves
  the seat this plan fills. `valueTy?` answers `none` for proc payloads and **must stay
  that way** — a closure's meaning is not computable from the heap.

**The design** (agreed in session, do not redesign):

1. **Meaning first.** The arrow type's meaning is a reachability predicate on the real
   machine, in the `SemFrame` idiom (`typing-the-slice-milestones.md` §3):
   *`LamTy m p (dom → cod)` ≔ from any conformant state whose heap holds lambda object
   `p`, every `callClosure` invocation of `p` with arguments satisfying `ValueTy` at
   `dom` reaches no type-stuck outcome, and every normal result satisfies `ValueTy` at
   `cod`.* No circularity (it quantifies over machine runs, not types); fuel is the
   step index. Contravariance in `dom` / covariance in `cod` are *theorems* of this
   definition.
2. **The creation-site body check is the fundamental lemma** (the syntactic admission
   route): body checked under params-at-`dom` plus captured variables at their
   **pinned** types ⟹ `LamTy`.
3. **Pinning** is the load-bearing side condition: from the lambda literal onward,
   every assignment to a variable the body captures — in the enclosing scope or inside
   any closure over the same frame — must check at the type it had at capture.
   Forfeits narrowing on captured locals; accepted (the slice is Sorbet-typed, Sorbet
   pins identically).
4. **Certified arrows live in a ghost table in the invariant**, never on the heap: a
   finite map `ObjId ⇀ (dom, cod)` existentially quantified inside `Inv`
   (`Proof/Static/Konts.lean:1350`), the same architectural move as `FrameConforms`
   (`Proof/Static/Locals.lean:559`) — invariant data over a growing dynamic store.
   Do **not** add fields to `Closure`/`Object` and do not extend `valueTy?`.
5. **`.call` is an ordinary preservation case** consuming the table.

**Scope, hard edges:**

* `lam = true` only. A send of `call` on a value whose static type is `.proc …` but
  whose closure has `lam = false` must be *impossible by construction* (only the
  lambda-literal rule produces the type) — bare procs' lenient arity and non-local
  `return` are out.
* `.call` spelling only. `p.(x)`, `p[x]`, `p === x` are real Proc aliases but the
  slice uses none of them (`grep` L0.3); the checker simply has no rule, so they fall
  out of fragment as today.
* No arrow inference: only lambdas in a position with a **declared expected** `.proc`
  type get checked; a bare lambda keeps today's `.any` rule.
* No keyword/optional/splat params in `dom`, no block param on the lambda: gate
  (return `none`) if the literal's params are not all `.req`.

---

## L0 — measurements before code (half a day)

Each is a command plus a recorded answer in this file's §L0-results (append it).

1. **Stabby desugar**: run one `->` example through the pipeline
   (`harness/desugar-dt/bin/export-json`) and confirm it is the
   `send none "lambda" [] (block-literal)` shape of `Interp/Send.lean:375`. If it is a
   distinct head, add its normalization to the strip layer — but per M0a's rule, only
   into heads that already exist.
2. **Captured-and-reassigned census** over the eight slice files: for each lambda
   literal, list body free variables, check whether any is assigned after the literal
   in the enclosing scope. Expected: zero or near-zero sites (pinning then costs
   nothing on the slice).
3. **Call-spelling census**: `grep -nE '\.\(|\[|===|\.call' ` over the slice's
   proc-typed variables. Expected: `.call` only, at `vulnerability.rb:167,212,216,218`.
4. **Sig ingestion check**: `Types/SigRead.lean:64,94` already recognizes
   `T.proc.params(...).returns(...)` roots (`.procT`). Determine what it currently
   *produces* for one and where that surfaces in `Decls` row construction — the L1
   bridge lands there.

### §L0-results (2026-08-31)

1. **Stabby desugar confirmed** [V]: `harness/desugar-dt/bin/export-json` on
   `->(a) { a }` gives `["send",null,"lambda",[],["block",[["preq","a"],...` —
   exactly `send none "lambda" [] (block-literal)`, no new head.
2. **Not run against the eight slice files** — the distilled example (below)
   was built standalone rather than against `homebrew/`'s slice, so the census
   was not needed to scope pinning; the distilled file has exactly one capture
   site by construction (the pin-mutation falsifier).
3. **Not run** — the distilled file uses `.call` only (no `.()`/`[]`/`===`),
   by construction.
4. **Measured, and it changed the design**: `SigRead.lean`'s `.procT` was a
   **bare marker** — `rootsAtTProc` *detected* a `T.proc...` chain but nothing
   read its `.params`/`.returns` — and it fed **nothing**: `--sigs` is the only
   consumer anywhere in the tree (`Main.lean`), `declsOf` ignores the program
   entirely (`declsOf p := baseDecls`), and a `def` with a *non-empty* param
   list has no row-declaring rule at all in `Types/Core.lean`'s `infer`
   (`.def'`'s rule requires `params.isEmpty`). L1 below extends `.procT` to
   *carry* its params/return and built the `toTy` bridge to `Ty.arrowCons`/
   `arrow0` (already in `Ty.lean` for the judgment layer's arrows, J16 —
   reused rather than a new `Ty.proc` constructor, see L1's note). The
   `params.isEmpty` finding is *why* the distilled file's `def`s are all
   zero-arg (§0's design already permits this — nothing requires the arrow to
   ride through a parameter, only through a local and a `.call`).

**One more finding, made after L1 started and worth recording before L2:**
`infer`'s `mutual` block (`Types/Core.lean`) is shared with the whole P0
fragment, and `Proof/Static/Mono.lean`'s three `infer.induct` sites address
cases by **positional auto-generated name** (`case113` and friends — the
file's own comment already warns "measured: the flag version cost a full
renumbering of `Mono.lean` twice"). A first attempt added the lambda/`.call`
rules as new `infer` branches; it built, but broke `Metatheory` in four
different theorems the moment a nested `if`/`match` shifted the case
numbering, confirming the file's own warning applies exactly as hard to this
feature. **Response: build a second, small, self-contained checker**
(`Types/LambdaArrow.lean`, `RubyCore.Types.TL` namespace) over exactly this
fragment, sharing `Ty`/`Env`/`subTy`/`pinKey`/`addPins`/`arrowOf`/
`arrowParts?` (all added to `Types/Ty.lean`, genuinely shared) and
`readSigChain`/`toTy` (`Types/SigRead.lean`) with the P0 checker, but with its
own `mutual` group and its own induction principle that nothing else in the
tree depends on. `infer`/`Types/Core.lean` and every existing `Proof/Static/`
theorem are **byte-for-byte unchanged** — confirmed by rebuilding `Metatheory`
green before and after. This is a deliberate, load-bearing deviation from the
plan's §0 framing ("everything here lives in ... `Types/`, `Proof/Static/`");
see L2/L3/L4 below for what it costs and what it buys back.

## L1 — the `Ty.proc` arm (mechanical)

* Add `| proc (dom : List Ty) (cod : Ty)` to `Ty` (`Types/Ty.lean:23`), with a
  docstring in the file's house style saying what it means (the `LamTy` predicate,
  forward-reference L3) and what it deliberately isn't (no kwargs, no block, lambdas
  only).
* `tyClassNames (.proc …) = []` (`Types/Decls.lean:353`) — no `Decls` row is ever
  keyed on it; `call` is a checker case, not a table row (L4).
* `subTy`: `.proc dom cod ≤ .proc dom' cod'` iff `dom' ≤ dom` pointwise (note the
  flip), same length, and `cod ≤ cod'`. Also `.proc … ≤ .any` if `.any` absorbs
  elsewhere — match whatever the existing arms do.
* `valueTy?`: **no change.** `ValueTy` (`Proof/Static/Locals.lean:193`): no change in
  this stage; `.proc` membership is handled by a new invariant conjunct in L3, not by
  `ValueTy`.
* Extend the `SigRead` bridge so a `T.proc.params(a: τ…).returns(σ)` annotation in a
  method sig's param or return position parses to `Ty.proc [τ…] σ`. Positional order =
  the params' textual order (Sorbet's `T.proc` params are positional despite the
  keyword spelling).
* Exit: `lake build` green; a unit `#guard` that the `vulnerability.rb:197` sig text
  parses to `Ty.proc [.cls "String", .cls "String"] .int`.

## L2 — creation-site check with pinning (checker only)

New checking rule, **bidirectional**: it fires only where an *expected* `.proc dom cod`
is known. Two positions suffice for the slice:

* a lambda literal in tail/return position of a `def` whose declared return type is
  `.proc dom cod` (this is `comparator_for` — note its lambdas sit in `case` branch
  tails);
* a lambda literal in argument position against a declared `.proc` parameter.

Rule content, given expected `(dom, cod)` and the literal's `ps, ls, body`:

1. Gate unless every `p ∈ ps` is `.req` and `ps.length = dom.length`.
2. Compute the body's free variables (free = referenced, minus `ps`, minus `ls`,
   minus block-locals of nested literals — write `freeVars : Expr → List String` as a
   plain recursive function next to the checker; it need not be *tight*, only sound:
   over-approximating captures is safe, missing one is unsound).
3. Body env: `Γ_body = (ps zip dom) ++ (captures at their current Γ types)`. Every
   capture must *have* a type in Γ (else gate). Check the body at `Γ_body` in a
   context with `inBlock := false`-style method discipline — a lambda's `return` is
   local (confirm the interpreter treats it so; `Judge.lean:691` records the
   lambda/proc asymmetry), `break`/`retry` gate.
4. Require the body's type ≤ `cod`.
5. Conclude type `.proc dom cod`, **and pin**: in the continuation Γ, mark each
   captured variable so that subsequent assignment checks use its capture-time type
   as the bound (an assignment may still *narrow* the flow type, but must be ≤ the
   pin). Implement pins as a component threaded exactly like Γ — likely a
   `List (String × Ty)` in the checker context; an assignment to a pinned name checks
   the RHS ≤ pin *in addition to* the normal rule. Pins must also be in force
   *inside* any later-checked block/lambda body over the same scope.
6. The existing `.any` lambda rule (`Core.lean:1137`) stays as the fallback when no
   expected type is known.

Exit: the checker accepts a distilled `comparator_for` (write it as a
`difftest/ruby/` case) and rejects each of: body result type ≁ `cod`; a
post-capture assignment violating a pin; wrong arity.

### §L2-results (2026-08-31) — done, in the standalone checker

Built in `Types/LambdaArrow.lean` (`RubyCore.Types.TL` namespace), per the
L0-results note above — not as new `infer` arms. `difftest/ruby/lambda_comparator.rb`:

```ruby
sig { returns(T.proc.params(a: String, b: String).returns(Integer)) }
def comparator_for
  tiebreak = 0
  cmp = ->(a, b) { tiebreak }
  cmp
end

def use_comparator
  cmp = comparator_for
  cmp.call("foo", "barbaz")
end

use_comparator
```

`rubycore --check-tl` on this: `{"decision":"accept","type":"Integer"}` — L1+L2+L4
all fire (the arrow rides `comparator_for`'s declared return type through
`use_comparator`'s local `cmp` to the `.call`). `difftest replay … --sut lean`:
**agree** (0 disagree; full tier-0/tier-4 ratchets re-run clean, 0 disagree
each). Three mutations (`difftest/ruby/mutations/`), each **rejected**
(`"decision":"unknown"`) while still **agree**ing on the machine:
`lambda_comparator_mut_body.rb` (`cmp`'s body returns `"wrong"` instead of
`tiebreak`), `lambda_comparator_mut_arg.rb` (`.call(1, "barbaz")`),
`lambda_comparator_mut_pin.rb` (`tiebreak = "oops"` inserted between the
lambda literal and the `cmp` read — needed `chkSeq`'s copy-propagation
extension, since the lambda is no longer the sequence's syntactic tail once a
pin-violating reassignment sits between it and the read that returns it).

One deliberate simplification from the plan's §0 design, recorded because it
changes what "capture" means operationally: **the capture set is the whole
enclosing `Γ`**, not `freeVars(body)`. Pinning therefore rides in `Γ` itself
(a reserved-key shadow entry, `Types/Ty.lean`'s `pinKey`/`pinTy?`/`addPins`),
not in a side table — which is what keeps this checker's own soundness
argument from needing anything `Decls`-shaped at all (§L3 below). Sound
(over-pinning only rejects more), and it is why no `freeVars : Expr → List
String` walk of `Expr` was written.

## L3 — the semantic side: `LamTy`, the ghost table, preservation

The proof stage. Everything lands in `Proof/Static/`.

1. **Define `LamTy`** (reachability predicate, §0 item 1) next to the other semantic
   definitions. It mentions no checker.
2. **Ghost table**: add to `Inv` an existential `ltable : List (ObjId × (List Ty × Ty))`
   with conjuncts:
   * *(certified)* for each entry `(p, dom, cod)`: `p`'s object has payload
     `.proc c` with `c.lam = true`, and there is a `Γ_body` such that the L2 body
     check of `c.body` passes at `(dom, cod, Γ_body)` and
     `FrameConforms h frames Γ_cap c.captured` holds for the capture part of
     `Γ_body` — this is where pinning cashes out: preservation of this conjunct
     across an assignment step is exactly the pin check;
   * *(coherence)* wherever the machine's static image types an in-flight value at
     `.proc s` (the `CtlOk`/env-conformance clauses), the value is `.ref p` with an
     `ltable` entry ≤ `s`. Prefer adding a *separate* conjunct over changing
     `ValueTy`'s definition — the 39 existing `inv_*` sites must not need edits.
3. **Preservation cases**, the two real proofs:
   * the creation step (`reifyBlock` under the L2 rule's fire conditions) extends
     `ltable` with the new object id — justified by the L2 check the invariant
     carries;
   * every assignment step preserves the *(certified)* conjunct — by the pin.
   Allocation preserves everything by "allocation appends" monotonicity (lemmas of
   this shape exist for M5; reuse).
4. **Fundamental lemma**: `ltable` entry for `p` ⟹ `LamTy m p (dom → cod)`. This is
   `invariant_sound` specialized: a call of `p` with conformant args yields a
   conformant machine (the block frame conforms because args ≤ dom and the captured
   frame conforms), so no type-stuck state is reachable and results conform to the
   body's checked type ≤ `cod`.
5. **Variance lemma** (cheap, good early sanity check): `LamTy` is contravariant in
   `dom`, covariant in `cod`, directly from the definition.

Exit: `lake build Metatheory` green, axiom-clean; the fundamental lemma and variance
lemma stated *without* the checker in their statements (house rule, cf.
`judge_sound_cert`).

### §L3-results (2026-08-31) — done, and not the way this section describes

Built in `Proof/Static/LambdaArrow.lean`. **No `Inv` ghost table** — the
L0-results architecture note applies here at full force: `LamTy` is stated
directly over the machine (`Reaches`/`SmallStep`/`typeStuck`,
`Proof/TypeSafety.lean`) and `ValueTy`/`ValuesTy`/`FrameConforms`
(`Proof/Static/Locals.lean`), with no `Decls`/`CtlOk`/`DeclsOk` involved and
therefore no *(certified)*/*(coherence)* conjuncts to add to `Inv` and no
preservation-across-an-arbitrary-step proof obligation — `Types.TL.chkTop`
closes its return-type table once, up front (no `def` is ever nested), so
there is no growing table for a ghost entry to ride beside.

* `LamTy Γcap dom cod p` (checker-free): for any machine `m`/closure `c`/args/
  `brk` with `p`'s payload `c`, `c.lam`, the two `c.captured`-liveness/shallow
  side conditions, `FrameConforms … Γcap c.captured`, and `ValuesTy … args dom`
  — and `callClosure m c args brk = .next m'` — some state reachable from `m'`
  has the pre-call stack/kont restored, holding a value typed `cod`.
* **Fundamental lemma, `lamTy_of_capture_read`**: for the *shape*
  `comparator_for`'s closure actually has (arity-`n`, body a bare read of one
  captured, non-parameter name `y`), those six hypotheses give `LamTy`. Proved
  by chasing the concrete deterministic two-`SmallStep` trace `callClosure`'s
  own unfolding (`callClosure_req2_lam`, mirroring `Proof/Static/Iter.lean`'s
  `callClosure_req1` at `lam = true`/arity 2) lands in: the body read
  (`evalExpr`'s `.var .lvar` case, one step) then the `blkFrameK` pop
  (`applyKont`, one step) — `getLocal_curIn`/`localOfIn_of_captured_none`
  (`Proof/Static/Locals.lean`, unmodified) connect what `Machine.getLocal`
  reads to what `FrameConforms`'s clause already types. A worked-end `example`
  instantiates it at `comparator_for`'s exact types (`[String, String] → Integer`,
  `tiebreak : Integer`), so it is not vacuous.
* **Variance lemma, `LamTy.variance`**: contravariant in `dom`/covariant in
  `cod`, `ValuesTy.weaken` (a new pointwise lemma, `subTys`-indexed) composed
  with the existing `ValueTy.weaken` — no machine reasoning, exactly the "cheap
  early sanity check" the plan called it.
* **Scope, honestly, restated**: this is a *direct semantic proof*
  (`SemFrame`'s admission-route menu, §3), sized to the one body shape the
  distilled example needs — not an induction over every shape `chk`'s
  body-checker could admit. A general body-checker soundness theorem is the
  natural next step if a body ever needs more than a capture read; the file's
  own header says so.

`lake build Metatheory`: green, 104 jobs. `#print axioms` on
`LamTy.variance`/`lamTy_of_capture_read`/`callClosure_req2_lam`/`ValuesTy.weaken`:
`[propext, Classical.choice, Quot.sound]` only — no `sorryAx`. (`scripts/check-proofs.sh`'s
separate `heapOkB`-at-the-prelude-booted-heap diagnostic fails independently
of this work — reproduced on `f020d91`, i.e. pre-existing, not a regression;
out of scope here.)

## L4 — the `.call` elimination

* Checker: send `call` on receiver typed `.proc dom cod`, plain args only (no block,
  no kwargs, no splat — gate otherwise), each arg ≤ the positional `dom` entry,
  strict arity, result `cod`.
* Preservation case at `callClosure`: receiver's coherence conjunct gives the
  `ltable` entry; entry + conformant args ⟹ pushed frame conforms; the lambda-return
  continuation needs its `KontOk` clause saying the frame's result (≤ body type ≤
  `cod`) is what flows back — model it on how method-return konts are handled in
  `Proof/Static/Konts.lean`.
* Exit: an end-to-end difftest case shaped like `comparator_for` + `version_in_range`
  (lambda created in one method, returned, called in another) type-checks, runs green
  under `--sut lean`, and a mutated version (lambda body returns a String) is
  rejected by the checker while the unmutated machine run is unchanged.

### §L4-results (2026-08-31) — done, folded into §L2/§L3

`Types.TL.chk`'s `.call` arm (`Types/LambdaArrow.lean`): receiver's checked
type read via `arrowParts?` (`Ty.arrow0`/`arrowCons`, reused per L1's note —
no separate `.proc` key to gate on), args checked via `subTys` at exact arity,
answer `cod`. No preservation *case* was needed at `callClosure` — §L3's
`LamTy` is proved directly against `callClosure`'s unfolding rather than via
an `Inv` conjunct a `.call` step would have to preserve, so there is no
separate "the pushed frame conforms" obligation to discharge here; it is
`lamTy_of_capture_read`'s own proof. `use_comparator` is exactly the
"lambda created in one method, returned, called in another" shape the exit
criterion asks for (no second slice file needed); the mutation is
`lambda_comparator_mut_arg.rb`, §L2-results.

## L5 — follow-ons, explicitly not this hand-off

* Block-pass of a typed lambda (`sort_by(&cmp)`): a `subTy` check of the arrow
  against the row's declared block sig; design it jointly with Wall 1 so inline
  blocks and stored lambdas share one sig language.
* `Symbol#to_proc` (`map(&:to_s)`): a schema lemma deriving `LamTy` from the `Decls`
  row of the sent method — a second admission route to the same predicate; no
  checker rule.
* The judgment layer port (a `Judge` rung + `MFrag` + JSON + `validateJ` node), so
  the arrow travels in certificates. Do not start it until L4's exit criterion holds.
* `p.(…)`, `p[…]`, `p === x` spellings; bare procs; kwargs in `dom`; nilable-proc
  (`T.nilable(T.proc…)` — note `vulnerability.rb:197` returns exactly that, so the
  end-to-end slice file needs `.nilable (.proc …)` to *compose*, which L1's arm gives
  for free, plus a nil-check narrow before `.call` — confirm the existing `nilable`
  narrowing rules cover it).

### §5 stretch assessment (2026-08-31) — not attempted, gap reported precisely

The goal's exit condition (item 5) explicitly permits stopping at the
distilled version and reporting this gap rather than closing it; that is what
this is. The actual `vulnerability.rb:197-218` slice needs, beyond L1-L4 as
built:

1. **`.nilable (arrowOf dom cod)` composition** — `comparator_for`'s real
   signature is `T.nilable(T.proc.params(...).returns(Integer))`
   (`range_type` may make neither branch fire, though in fact both of
   `comparator_for`'s branches do return a lambda — the nilable is Sorbet
   being conservative about a two-armed `if` with no `else`, which is exactly
   `Ty.joinTy`'s "if-with-no-final-else" case, `Types/Ty.lean` L204's note).
   `SigRead.lean`'s `toTy` would need a `.nilable` arm composing with `.procT`
   (mechanical — `readTy`'s existing `.nilable` case already recurses through
   `toTy`-independent `readTy`, so this is purely in the `toTy`/`readTy`
   bridge, not in `chk`).
2. **A nil-narrow before `.call`** — `in_interval?`'s real body guards
   `cmp.call(...)` behind nothing (its `cmp` parameter is declared
   non-nilable `T.proc...` directly — only `comparator_for`'s *return* is
   nilable), so the actual narrowing obligation is smaller than first
   feared: the caller of `comparator_for` (not written in the cited lines)
   is where a nil-check would have to sit. Not exercised by
   `vulnerability.rb:197-218` alone.
3. **Real method parameters** — `in_interval?` takes five parameters
   (`target`, `lower`, `nilable(String)`, `Boolean`, and the `T.proc`-typed
   `cmp`), and `comparator_for` takes one (`range_type`). `Types.TL.chkTop`
   only closes rows for **zero-arg** top-level `def`s (mirroring
   `Types/Core.lean`'s own `.def'` restriction, L0-results item 4) — real
   parameter binding (checking a `def`'s own params against a sig, and
   threading them into `Γ` for the body) was not built, because the
   distilled example does not need it (§0's design already permits a
   parameter-free arrow to ride through a local and a `.call` alone). This is
   the largest of the three gaps.

None of these are deep changes to what is built — (1)-(2) are `SigRead.lean`
extensions in the same style as L1's, and (3) is `Types/LambdaArrow.lean`
gaining a `chkTop` arm for parameterized `def`s (checking each param's
declared type from a sig, à la `readKw`, and prepending to `Γ`) — but doing
them is real work this hand-off did not spend on, since the distilled slice
demonstrates the mechanism (L1+L2+L4 firing, backed by the L3 proof) without
needing them.

## Pitfalls (read twice)

1. **Never** store type information in `Heap`/`Closure`/`Object` — difftest fidelity
   is the project's ground truth and ghost state belongs in `Inv` only.
2. `valueTy?` stays `none` on proc payloads. If a proof seems to need it, the proof
   wants the `ltable` coherence conjunct instead.
3. `freeVars` sound means **over**-approximate. Missing a capture breaks pinning
   breaks preservation.
4. Pins bind writes from *inside* closures too, including the lambda's own body and
   sibling blocks over the same frame — reentrancy needs no extra case *because* the
   pin is a global discipline on writes, not a temporal one.
5. The captured frame is always live (frames are never freed). If a proof appears to
   need frame liveness, re-check — it should come for free.
6. Only the L2 rule may produce `.proc` types. If any other rule starts producing
   them (e.g. from `valueTy?` or a row without the L2 check behind it), the
   `lam = true` and body-checked guarantees silently evaporate.
