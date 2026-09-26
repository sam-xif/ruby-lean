# Growing the fragment

How the set of Ruby programs `desugar` accepts is measured and extended. Commands
run from `desugar/`, with `RUBY` set to a CRuby that has Prism
(`RUBY=$(brew --prefix ruby)/bin/ruby`).

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
evaluation. That is the concrete payoff of augmenting `obs` with the trace ([06 §2](method.md#06-2-observe-the-value-and-the-evaluation-order)), and the same injected bug is the difftest engine's end-to-end detection
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

## Growing it

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
