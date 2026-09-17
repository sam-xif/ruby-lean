# desugar-dt — the front end, and the harness that earns trust in it

`desugar : Surface → RubyCore` is stage 2 of the typed pipeline and the front end
for everything in this repository: the Lean model never parses Ruby, it consumes
RubyCore JSON from here. This directory is both that front end and the
differential-testing harness that validates it — **using CRuby as the sole
oracle, before RubyCore has any semantics at all.**

Design decisions are recorded in
[`implementation-choices.md`](implementation-choices.md) (C-numbers, cited from
the code). The method is [below](#the-method); code comments cite it as
*"artifact 06 §N"*.

## The idea in one line

For a surface program `P`, check that `P` and `render_core(desugar(parse(P)))`
produce the **same observation under CRuby** — where the observation includes an
**evaluation-order trace**, not just the final value.

```
  P ──parse──▶ Prism AST ──desugar──▶ RubyCore ──render_core──▶ Ruby′
  obs⁺_CRuby(P)   ≟   obs⁺_CRuby(Ruby′)      (+ pure checks: is_core, normal-form)
```

## Layout

| Path | Role |
|------|------|
| `lib/rubycore.rb` | the RubyCore node set (`HEADS`, tagged S-expressions) + `is_core?`/`explain` — the authoritative list, mirrored by `RubyCore/Syntax.lean` |
| `lib/desugar.rb`  | `Prism AST → RubyCore`, with per-rule coverage tracking |
| `lib/linearize.rb`| hoist unconditional control-flow jumps out of operand position ([why](#linearization)) |
| `lib/render.rb`   | `RubyCore → Ruby` (over-parenthesized, re-parseable) |
| `lib/export.rb`   | the versioned JSON wire format the Lean side decodes (`Export::VERSION`) |
| `lib/observe.rb`  | `obs⁺`: run under a CRuby subprocess, capture (stdout, value, exc), normalize |
| `lib/roundtrip.rb`| the round-trip + `is_core` + normal-form checks + disagreement triage |
| `bin/run`         | driver over a corpus; agreement + coverage report |
| `bin/export-json` | Ruby source on stdin → RubyCore JSON on stdout (**the pipeline entry point**) |
| `bin/desugar`     | inspect one program: source, rules fired, rendered RubyCore, AST |
| `bin/coverage`    | fragment-coverage % + blocker histogram + ratchet |
| `bin/harvest_bootstraptest` | corpus harvester from MRI `bootstraptest/` |
| `corpus/seeds/`   | hand-written self-contained seeds (incl. eval-order adversarial) |

## Usage

```sh
RUBY=$(brew --prefix ruby)/bin/ruby      # a modern CRuby with +PRISM

$RUBY bin/run                 # run all corpus programs
$RUBY bin/run --verbose       # also print the rendered RubyCore for each
$RUBY bin/run corpus/seeds    # run a specific dir or file
$RUBY bin/run --bug           # inject the naive &&/|| desugaring (demo, below)

echo 'puts 1 + 2' | $RUBY bin/export-json          # what the Lean model is fed
```

Exit status is non-zero if any program disagrees or errors.

## Why the evaluation-order trace matters (built-in demo)

`&&`/`||` must evaluate their left operand **exactly once**. The naive desugaring
`a && b ⇒ if a then b else a` re-evaluates `a`. A value-only oracle misses this —
the *result* is unchanged — but the trace does not. `--bug` injects the naive
form:

```
$ $RUBY bin/run --bug
[XX ] seeds/03_and_falsy_order.rb  [trace]
      stdout: "a=nil" vs "aa=nil"
[XX ] seeds/04_or_truthy_order.rb  [trace]
      stdout: "a=5" vs "aa=5"
```

The value is identical on both sides; only the trace exposes the double
evaluation. That is the concrete payoff of augmenting `obs` with the trace (§06
§2), and the same injected bug is the difftest engine's end-to-end detection
self-test (`--sut desugar --inject-bug`).

## The fragment

The node set is `RubyCore::HEADS` in `lib/rubycore.rb` — that list, not this
file, is authoritative, and `RubyCore/Syntax.lean` mirrors it one-for-one.
Anything outside it makes `desugar` raise `Unsupported`, and the driver marks the
program **out-of-fragment** (skipped with a reason) rather than failing.

Measured coverage of the bootstraptest corpus is **1227 of 1299 parseable
programs in fragment** (`coverage-baseline.json`; `bin/coverage` recomputes it and
ratchets against that baseline). The remaining 72 are the unsupportable and
deliberately-deferred set.

### Growing it

Expansion is a **measure → expand → re-measure** loop, which is why `bin/coverage`
exists and is first-class. It reports fragment coverage, a **blocker histogram**
(per unsupported Prism node type, how many programs it blocks — the *full* profile
per program, not just the first blocker `desugar` trips on, because the
first-blocker view undercounts), and a **ratchet** against a committed baseline
that may only go up.

Two framing rules:

- **"In fragment" is not the goal — "in fragment *and* agrees" is.** Expect some
  newly-admitted programs to disagree on admission: that is the payoff, a real
  `desugar`/`render` bug the growth exposed.
- **The out-of-scope list is a deliverable**, in `implementation-choices.md`, one
  line of justification per entry. Literal 100% of bootstraptest is neither
  achievable nor desirable — the suite deliberately exercises VM internals that
  are out of scope by design — so the honest headline is *"100% of in-scope
  bootstraptest, N programs explicitly excluded (listed)"*, never a bare 100%.

Every feature is first **classified**, because where the work goes differs by kind:

| Kind | What it costs | Owes the model |
|---|---|---|
| **desugaring** | a rewrite in `lib/desugar.rb` + a rule in `Desugar::RULES`; **no new node** | nothing |
| **new core node** | `RubyCore::HEADS` + `explain`, a `render_core` case, the `desugar` mapping | a `Step` rule later — it is part of the model, not sugar |
| **out of scope** | raise `Unsupported` with a reason, add the justified entry | nothing, ever |

Then: implement, **seed it** (and if it carries an evaluation-order or once-only
obligation — op-assign receiver-once, multi-assign order, `case` subject-once,
`for`'s leaking index, splat evaluation — add a *trace-augmented* seed, because
value-only checks miss exactly these), keep `bin/run` green, re-measure, ratchet,
commit with an `implementation-choices.md` entry for any scope decision.

Guardrails: coverage is monotone; no silent caps — every uncovered program is a
tracked bug, a pending batch item, or an enumerated exclusion; one adversarial
seed per ordering obligation; and **batch, then re-measure** — never plan more
than one batch ahead on stale numbers, because the blocker distribution shifts as
programs unlock to their *next* blocker. Don't try to handle all of Ruby at once
(`implementation-choices.md` C3), and prefer desugaring over adding a node (C12).

The measured order the histogram produced, for the record: values and statements
first (self-contained, no class/def machinery), then method and block shapes, then
**classes and exceptions — the single biggest unlock**, because bootstraptest is
class-heavy; then control-flow sugar, then long-tail triage moving each remainder
to either a rule or the exclusion list.

---

# The method

Why a front end can be validated before the language it targets has any
semantics, and what that validation has to observe. Numbering is stable and is
what code comments mean by *"artifact 06 §N"*.

## 06 §1 — Why `desugar` can be tested with no RubyCore semantics

`desugar` is a **source-to-source, behavior-preserving** transform, so its
correctness is checkable entirely inside Ruby. With a RubyCore pretty-printer
`render_core` and the trivial surface printer `render_surf`, the defining
property is a **metamorphic round-trip**:

```
  ∀ surface program s in the fragment:
     obs_ruby( render_surf(s) )  ≡  obs_ruby( render_core(desugar(s)) )
```

Both sides run through **CRuby only.** That is the whole reason desugar testing
could be front-loaded: a solid front end is a prerequisite for the model, and
waiting for the model to validate it would have inverted the dependency.

Two structural checks are *pure* — no oracle, run on every output:

- **well-formedness** — `is_core(desugar(s))`: the output uses only RubyCore
  forms, no residual sugar. Catches "forgot to handle this node."
- **normal form** — `desugar(reparse(render_core(desugar(s))))` is structurally
  equal to `desugar(s)`. Catches unstable or non-terminating rewrites.

**Trusted-base caveat, stated rather than hidden.** The round-trip validates
`render_core ∘ desugar` *as a pair*; a compensating bug (desugar breaks X, render
un-breaks it) would hide. Mitigations: keep `render_core` near-identity — RubyCore
is deliberately Ruby-shaped — test it independently via the structural round-trip,
and lean on the two pure checks above, which do not involve `render_core` on the
surface side.

## 06 §2 — Observe the value **and the evaluation order**

Value-only comparison misses the most important class of desugaring bugs: the
ordering and once-only obligations that desugaring exists to make explicit.
`a.b ||= c` must evaluate the receiver `a` **exactly once**; a desugaring that
evaluates it twice can still return the same value.

So the observation is extended with a side-effect trace:

```
  obs⁺(program) = ( obs(program) , trace )
  trace = the ordered log of observable markers evaluated, with multiplicity
```

Two programs agree **iff they evaluate the same markers in the same order the
same number of times.** This is the cheap mechanism that catches
receiver-evaluated-twice, operand reordering, and short-circuit bugs that a
value-only oracle waves through — see the `--bug` demo above.

## 06 §3 — "Nonsensical" is fine; "shallow" is the enemy

A program that deterministically raises `NoMethodError` is a **perfectly good
oracle case** — desugar must preserve that exact observation. The bar is only:
**parseable**, and **deterministic** under CRuby.

Parseability is nearly free because generation happens at the AST level and
renders to source — surface syntactic variety has already collapsed at parse
time, so it is the *parser's* concern, not desugar's.

The residual risk is not nonsense but **shallowness**: a generator that mostly
emits "undefined method"/"undefined local variable" programs produces
valid-but-trivial cases that bail at line 1 and never exercise desugar on rich,
*nested* constructs. Defeating shallowness is the job of the corpus below.

## 06 §4 — The three-pronged corpus

Complementary along distinct axes; no single prong suffices.

| Prong | Nature | Strength | Weakness |
|---|---|---|---|
| **1. `bootstraptest`** | curated, real, human-written | high signal, core-focused, self-contained, *ships an oracle value* | small volume |
| **2. grammar-aware fuzzing** | broad, random, structure-aware | volume; unexpected rule *combinations* | shallow without care |
| **3. adversarial targeted examples** | intentional | reaches corners requiring *understanding* | doesn't scale to volume |

**Prong 1 — MRI `bootstraptest`.** CRuby's pre-build smoke suite: each test is
`assert_equal '<expected>', '<program>'` where the program string is complete and
self-contained. The harness is not run; the test files are parsed and the program
strings lifted out (`bin/harvest_bootstraptest`). The `expected` argument is a
**free cross-check on the `obs` normalizer** — if `obs_ruby(program)` disagrees
with it, the observation function is the suspect, not desugar. Tests probing
GC/`ObjectSpace`, threads, deliberate `SyntaxError` or VM internals are filtered
out.

Why not `ruby/spec` or MRI `test/`? Those run on **mspec** and **minitest** — a
bespoke harness and a bundled library. Neither is part of the language, and their
example bodies are coupled to `describe`/`before`/`let` setup, so they are not
self-contained. Deferred, and the frameworks stay out of the model.

**Prong 2 — grammar-aware fuzzing.** Built, as the difftest engine's
[tier 1](../difftest/README.md). Two findings from designing it are worth keeping.
First, the approach chosen was *generate a surface AST and render it to Ruby text*
rather than Superion's splice-a-parsed-tree, because **Prism has no unparser** and
`render_core` handles only RubyCore, i.e. post-desugar — so mutation of scraped
Ruby stayed deferred while generation did not. Second, generation is
**scope-aware**: an environment threads through so only bound names are
referenced, which is the single highest-leverage feature, because a naive
generator produces valid-but-shallow programs that die at line 1 with `NameError`
and never reach nested sugar.

Its honest ceiling, stated when it was designed and still true: prong 2 excels at
breadth and at rule *combinations*, and shakes out crashes on valid-but-weird
trees — but because `desugar` is mostly structural, the subtle semantic
obligations (once-only evaluation, ordering) are better hit by prong 3. It
complements prong 3 rather than replacing it.

**Prong 3 — adversarial targeted examples.** Programs written deliberately to
stress each rule's semantic obligation, each using the evaluation-order trace.
The standing obligation list: `x ||= e` / `a.b ||= c` / `h[k] ||= v` (receiver and
key evaluated **once**); `&.` (receiver once, nil short-circuit skips the call
*and* its arguments); interpolation (`to_s` dispatch, strict left-to-right);
multiple assignment and splat; `case/when` (subject once, `===` dispatch order);
precedence and associativity with side-effecting operands; `for … in` (the index
leaks to the enclosing scope, unlike block params); and `&&`/`||`/`and`/`or`
value-preservation — they return an *operand*, not a boolean. Realized as tier 3.

## 06 §5 — Metric: desugaring-rule coverage

`desugar` emits the set of rewrite rules fired per input, aggregated over the
corpus (`bin/run` reports it). The analogue of semantic-rule coverage
(artifact 05 §6).

An uncovered rule is either dead (front-end bug) or untested (→ point prong 3 at
it). **Rule-*pair* coverage is the real target**: desugaring bugs cluster at
interactions — an `||=` whose RHS is a `case`, a splat inside a multiple
assignment inside a block. Coverage feeds back into prong 2 (bias generation) and
prong 3 (choose targets).

## 06 §6 — Triage

Because RubyCore had no semantics when this was built, the only components under
test are `desugar`, `render_core` and the `obs` normalizer, so the full
disagreement pipeline collapses to four buckets:

| Symptom | Bucket |
|---|---|
| differs only in a normalized field, or against bootstraptest's `expected` | **obs_normalizer** |
| the *trace* differs (order or multiplicity) | **desugar** — broke evaluation order / once-only |
| the value or exception differs | **desugar** — changed meaning |
| `render_core(x)` misparses, or the structural round-trip fails | **render** — printer bug |
| the program uses an out-of-fragment feature | **out of scope** — filtered, with a reason |

There is deliberately **no "model bug" bucket.** That is the point of doing this
round first.

## 06 §7 — The exit criterion

Trust `desugar` enough to build RubyCore semantics against it when: round-trip
agreement on the filtered bootstraptest corpus is total and the `expected`
cross-check passes; rule coverage is saturated, every rule and every reachable
rule-pair exercised; prong-2 fuzzing sits at a stable disagreement rate trending
to zero with everything triaged; the prong-3 obligation list passes under `obs⁺`;
and the pure checks hold across the whole corpus.

At that point a future C1 disagreement is known *not* to be a front-end artifact —
which is the property the whole ordering was for.

## 06 §8 — Open

- **[?]** How faithful must `render_core` be to keep the trusted base small? Could
  it be skipped by emitting an AST that Prism itself can unparse, reusing a
  maintained unparser?
- **[?]** Which AST reductions preserve parseability *and* trace-observability
  well enough to hand to a general structure-aware reducer?
- **[?]** Does scope-aware generation bias away from the very
  `NameError`/`NoMethodError` paths that exercise `method_missing`-relevant
  desugarings? May need a deliberate undefined-reference mode.

---

# Linearization

The worked case proving `desugar` is not a trivial map. Implemented in
`lib/linearize.rb`; decision recorded as `implementation-choices.md` C15/C16.
Prior art: the Ruby Intermediate Language (RIL), whose contribution was exactly
this — making evaluation order explicit.

## The problem

Ruby allows a control-flow jump inside string interpolation:

```ruby
while true
  counter -= 1
  break if counter == 0
  "#{next}"          # legal; the `next` fires when the interpolation is reached
end
```

`"#{next}"` behaves exactly like a bare `next`. (Not idiomatic — it comes from
CRuby's own parser regression tests.) But the obvious structural desugaring of
interpolation — concatenate `to_s` of each embedded expression — produces
`[:send, [:next], "to_s", …]`, which renders as `(next).to_s`: a **SyntaxError.**
A jump cannot appear as an operand.

## The precise rule **[V]**

Ruby's parser accepts a jump in **statement or branch** position and rejects it in
**operand** position:

| Position | Example | Legal? |
|---|---|---|
| statement | `next` | ✅ |
| if/while body, seq element | `while c; next; end` | ✅ |
| if/ternary **branch**, even when the `if` is itself an operand | `(if c then next else 5 end).to_s`, `foo(x ? next : 5)` | ✅ |
| **operand** — send receiver/arg, array/hash element, assignment RHS, condition | `(next).to_s`, `foo(next)`, `[next]`, `x = next` | ❌ |
| operand where **all** `if` branches jump | `(if c then next else break end).to_s` | ❌ |

The distinction is *whether the operand can ever yield a value*. A conditional
jump is fine; an **unconditional** one is not.

Notably, interpolation is essentially the only valid-Ruby construct that puts a
jump in operand position — `foo(next)`, `[break]`, `x = next` are already
SyntaxErrors in source and never reach the desugarer. That is why this surfaced
via interpolation specifically.

CRuby handles it at the bytecode level: it emits the interpolation normally, emits
the control transfer where the embedded expression sits, leaves the
string-completion instructions as **dead code**, and inserts `adjuststack` to keep
the operand stack consistent. That is not available at source level, so we do the
source-level analogue.

## The transformation

`definitely_jumps?(node)` — does evaluating this always transfer control?

```
  return | break | next   → true
  seq                     → any element definitely jumps
  if(c, t, e)             → c jumps, or (t jumps AND e jumps)
  otherwise               → false
```

**Linearize:** for a compound (`send`, `array`, `hash`, and the concats
interpolation produces), evaluate operands left to right; if operand *i*
definitely jumps, replace the whole compound with the sequence of operands up to
and including *i*, dropping the unreachable remainder.

```
  [:send, recv, m, [a₀, …, aᵢ(jumps), …]]   ⟿   [:seq, recv, a₀, …, aᵢ]
```

**No temporaries are needed** — we only ever hoist an operand that never yields a
value, so there is nothing to bind. That is what keeps the pass small. A
*conditional* jump is left in place, because Ruby accepts it in branch position.

| Source (in a loop) | Linearized render | Note |
|---|---|---|
| `"#{next}"` | `next` | pure hoist |
| `"a#{next}b"` | `("a"; next)` | prefix evaluated for effect; `"b"` dropped |
| `"x#{(p 1); next}y"` | `("x"; (p(1); next))` | embedded effects preserved in order |
| `"v=#{c ? next : 5}"` | `("v=").+((if c then next else 5 end).to_s)` | **conditional** → not hoisted |

## The lesson, and the dial setting

**Desugaring is not a homomorphism.** A context-free structural rewrite
(`e ↦ e.to_s`) is *unsound* here — it produces ill-formed output. Faithful
desugaring has to reason about control flow. And **the core stayed small**: the
fix added no RubyCore node, using only `seq` and existing forms (C12).

RIL pioneered Ruby linearization but for the opposite consumer, and the difference
shows up precisely here:

| | RIL | here |
|---|---|---|
| Consumer | static dataflow analysis | operational interpreter + proofs |
| Linearization | **maximal** — every side-effecting subexpr → a temporary | **minimal** — only unconditional jumps in operand position |
| Temporaries | pervasive | none for this case |
| Goal shape | flat, one action per statement (CFG-friendly) | small nested AST (proof-friendly) |

A nested-evaluation semantics already handles compound subexpressions and their
order correctly, so there is no reason to flatten them — and keeping the AST small
is what makes the metatheory tractable.

**The harness found it.** This pass was not designed up front. It surfaced as a
round-trip *harness error* — the original observed fine, the rendered version
didn't parse — the first time `return`/`break`/`next` were admitted. The
differential loop doing its job (§06 §6).

**[?]** Are there other valid-source operand-position jump sites (pattern-matching
value positions)? None known; the round-trip will flag any as a harness error.
When temp-requiring desugarings land (indexed op-assign), the general ANF
machinery grows to *bind* intermediates; the jump case here is its degenerate,
temp-free corner.
