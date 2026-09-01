# Issues found while building tiers 13–19 (the Homebrew slice)

**Written 2026-09-01**, from the pass described in [`AGENTS.md`](AGENTS.md) §2026-09-01.
A tracking list, not a work plan: each entry is something that is *wrong or missing
outside this package* — in the Lean model, in the difftest harness, or in the shared boot
stubs — that a ratchet rung ran into. Checker-side gaps are not here; they are the ladder
(§The ladder) and the `Ty` grammar gaps (§Ty language gaps).

Every entry has a **minimal reproducer** that was actually run, and states which side is
wrong. Where a fix was already applied, the entry says so and stays, because the fix is
local to `ratchet/` and the underlying problem is not.

Reproduce any `MODEL`/`DISAGREE` line with:

```sh
ruby X.rb                                                    # the oracle
harness/desugar-dt/bin/export-json X.rb | lean/.lake/build/bin/rubycore   # the model
```

---

## A. Silent divergences — both executors run, and disagree

The dangerous class: nothing gates, nothing raises, and the difftest engine is the only
thing that can catch them.

### A1. The model does not enforce `sig`s, so a sorbet-runtime `TypeError` is missed

**Status:** open. **Severity:** high — it is a *type* error the model does not produce,
in a target that is `# typed: strict` essentially everywhere (947 of 962 files).

```ruby
require "sorbet-runtime"
class Module
  include T::Sig
end

class Box
  sig { params(v: String).returns(String) }
  def self.take(v)
    v
  end
end

begin
  Box.take(5)
rescue StandardError => e
  puts("#{e.class}")
end
```

CRuby prints `TypeError`; the model prints **nothing** — the call succeeds. So on any
sig-annotated program the model's reachable-outcome set is *smaller* than CRuby's, which
is the wrong direction for a type-safety-by-reachability argument: a program the model
says never goes type-stuck may go type-stuck under CRuby, at a `sig` boundary.

Found via `Version::Token.create(1)` in the tier-18 `version.rb` driver (CRuby: `TypeError`
from `T.let`; model: the file's own `RuntimeError`). That probe was removed from the driver
rather than left as a recorded disagreement, so **nothing in the corpus covers this today**.

Two sub-cases worth separating when this is picked up: a `sig` violation that CRuby turns
into a raise the program then *rescues* (a control-flow difference), versus one that
escapes (an outcome difference).

### A2. sorbet-runtime failure messages carry the caller's file path

**Status:** open (works as designed, but it makes those programs undiffable).
**Severity:** low, but it constrains what a corpus rung may do.

A `T.let`/`sig` failure message is multi-line and includes `Caller: <path>:<line>`. That is
process- and location-dependent, so it violates the output discipline every difftest corpus
depends on (`difftest/implementation-notes.md` N38) *even if* A1 were fixed. Observed on
`V.new({ "id" => 5 })` in `homebrew/slice-driver/probes/adversarial-inputs.rb`; the ratchet's
copy of that probe drops the row for this reason (`ratchet/slice/drivers/slice-adversarial.rb`).

### A3. The model does not enforce `Module#include`'s argument check

**Status:** open. **Severity:** medium — it is the one thing `Judge.classStmt`'s `allModules`
premise exists to prevent, and the model cannot corroborate it.
**Found:** 2026-09-01, ratchet clink 31 (tier 13e), while writing a nested-class control.

```ruby
class NotAModule; end
module M
  class Box
    include NotAModule
  end
end
```

CRuby: `TypeError: wrong argument type Class (expected Module)` at the `include` line —
squarely inside the type-stuck family. The Lean model runs the program to a value.

Nesting is irrelevant; the flat form diverges too, and it has been visible in the ratchet's own
output since tier 10 without being read: `checkrungs`' control
`class K; def m; 1; end; end; class P; include K; end; P.new.m` prints **"conservative: safe,
no rule yet"**, which is the harness reporting the *model's* verdict, not Ruby's. So the
`allModules` premise is justified against CRuby (verified directly) and is *unsupported* by the
model — the same shape as A1, and in the same unhelpful direction for a reachability argument.

What it does **not** affect: the premise itself, or any rung. No corpus rung includes a
non-module (which is also why `run_agreement.sh` never caught it), and the controls that
depend on `allModules` still reject. What it affects is what a control's printed label means:
"conservative: safe" reads as a claim about Ruby and is only ever a claim about the model.

---

## B. Model gates — the model refuses the program (exit 3)

Not disagreements. Each is a real Ruby construct that the slice, or a natural driver for
it, wants; each blocked a rung and was routed around.

| # | gate message | minimal reproducer | wanted by |
|---|---|---|---|
| B1 | `unmodeled method Array#hash` | `[1, "a"].hash` | `Purl#hash`, `PkgVersion#hash`, `Version#hash` — all three slice classes that define `hash` delegate to `Array#hash` |
| B2 | `sort needs <=> dispatch` | `[N.new(2), N.new(1)].sort` for a user `N` with `<=>` | sorting `Version`s, which is the slice's most natural use of its own ordering |
| B3 | `min/max needs <=> dispatch` | `[N.new(2), N.new(1)].max` | same; and `range_status` ends with `past_fixes.max_by { \|v\| Version.new(v) }` |
| B4 | `Enumerator: Enumerable#each_cons without a block` | `[1, 2, 3].each_cons(2).to_a` | any blockless enumerator; hit writing a monotonicity check in the `cvss.rb` driver |

B2 and B3 are one thing: **`<=>` dispatch to a user-defined method from a builtin
collection operation.** `sort_by` works (it compares the *block's* results, which are
builtins), which is why the tier-18 `version.rb` driver reaches the ordering that way — but
that is a workaround, and `Version` exists to be sorted.

B1 is separable and small. B4 is the enumerator protocol and is probably the largest of the
four.

### B5. Two previously-recorded gates appear to be **closed** — worth confirming

`homebrew/slice-driver/probes/README.md` records `Integer#[]` and `Array#[] non-int index`
as model gates (the reason `malformed-shapes.rb` exits 3 and is a CRuby-only probe). Both
minimal shapes now **agree** through the real difftest engine:

```ruby
["a", "b"]["type"]   # TypeError, both sides
5["type"]            # TypeError, both sides
```

Either the gates were closed since that README was written, or `malformed-shapes.rb` reaches
them by a shape these two do not. Someone should re-run that probe and update the README
either way; it is currently the only reason a whole probe is excluded from difftesting.

### B6. Pre-existing, already recorded: `super` with an explicit block

`AGENTS.md` §Frontier item 15. `class Child < Base; def run; super { |x| x * 3 }; end; end`
answers `sut_unsupported`. Listed here only so the model-demand list is in one place.

---

## C. Boot-stub bugs — both executors run the same wrong code

These are the worst kind to find, because **difftest cannot see them**: the harness gives
the same stub to both sides, so they are wrong together and agree.

### C1. `BLANK_STUB` is missing every per-class `blank?` row except `Object`'s

**Status:** fixed for `ratchet/`'s rungs only; **open for the shared harness.**
**Severity:** high — it silently changes what the slice computes.

`difftest/tiers/tier0/rspec_harvest.py`'s `BLANK_STUB` is upstream's `Object#blank?` alone:

```ruby
def blank? = respond_to?(:empty?) ? !!empty? : false
```

Upstream `extend/blank.rb` then requires ten more files, each overriding `blank?` for one
class. The stub therefore answers correctly for `Array`/`Hash`/`Symbol` (whose upstream rule
*is* `empty?`) and **wrongly** for at least three:

```
nil.blank?    => false   (upstream extend/blank/nil_class.rb:   true)
false.blank?  => false   (upstream extend/blank/false_class.rb: true)
'   '.blank?  => false   (upstream extend/blank/string.rb:      true — whitespace-only)
```

The `nil` row is fatal in one slice file. `version/parser.rb` guards with
`return if match.blank?` and `return @block.call(version) if @block.present?`, so under the
stub a non-matching regex reaches `nil.captures` and an absent block reaches `nil.call`:
`RegexParser#parse` raises `NoMethodError` on every path that should return `nil`. It went
unnoticed because the harvested spec corpus difftests *agreement*, and both executors were
wrong together.

**Fixed in `ratchet/scripts/build_slice_rungs.py`'s `BLANK_NIL_STUB`** (the `nil_class` and
`false_class` rows, verbatim from upstream), added there rather than in the shared harness so
the harvested corpus's programs do not change underneath it. Two consequences to track:

1. The two stub sets now **differ**, which is exactly the drift `slice-driver/README.md`
   argues against. Whoever fixes the shared harness should delete `BLANK_NIL_STUB`.
2. The `String` whitespace-only row is **still wrong on both sides**. It is not fixed here
   because upstream's version needs `Regexp::FIXEDENCODING` and an encoding-keyed cache, and
   nothing in the slice was observed to depend on it — but that is an absence of evidence,
   not evidence of absence.

### C2. `PATHNAME_STEM_STUB` strips one extension where Homebrew strips an archive suffix

**Status:** open. **Severity:** medium — it changes `Version.detect`'s answers.

The stub is `File.basename(self, extname)`; Homebrew's `extend/pathname.rb` strips the whole
archive suffix. So:

```
Pathname.new("https://example.test/libexample-1.4.2.tar.gz").stem
  => "libexample-1.4.2.tar"      # Homebrew: "libexample-1.4.2"
Pathname.new("https://example.test/dash_0.5.5.1.orig.tar.gz").stem
  => "dash_0.5.5.1.orig.tar"     # Homebrew: "dash_0.5.5.1.orig"
```

which is why the tier-18 `version.rb` rung records `Version.detect(".../libexample-1.4.2.tar.gz")`
as `"1.4.2.tar"`. Both executors agree, so the rung is honest about the *stub*; it is not
honest about Homebrew. Recorded in the driver's own comment as well.

Note this interacts with C1: `StemParser` is the parser class most of `VERSION_PARSERS` is
built from, so a wrong `stem` and a wrong `blank?` compound.

---

## D. Performance

### D1. The whole linked slice does not fit the difftest engine's default 10 s budget at 64 inputs

**Status:** worked around in the corpus; the cost itself is the finding.

`difftest replay`'s default `--timeout` is 10.0 s (`difftest/cli.py:425`). Measured on the
linked slice (2,176 lines) with `probes/input-sweep.rb`'s 64 versions: **CRuby 0.128 s, model
10.054 s → timeout**, reported as `sut_unsupported` ("sut timeout"), i.e. it is *not*
distinguishable from a fragment gap in the summary. Boot of the linked program is ~2.5 s and
each further `range_status` is ~0.15 s.

The corpus rung was narrowed to 16 inputs to fit. Two things worth tracking: an ~80× gap
against CRuby on a real program, and the fact that a **timeout and a fragment gap report as
the same verdict**, which will mislead someone the first time a slice-sized rung gets slower.

---

## E. Not bugs — decisions this pass made that someone may want to revisit

- **The tier-19 `slice-adversarial` rung's driver is a modified copy**, not a reference, of
  `probes/adversarial-inputs.rb` (one row dropped, per A2). If the probe changes, the copy
  does not. The other two tier-19 drivers *are* references to the originals.
- **`vulns/vulnerability.rb`'s tier-18 rung links `version.rb` alongside it**, though the
  file does not `require` it. It names `Version` in its `ECOSYSTEM` comparator and its
  `:fixed` tiebreak, i.e. it depends on Homebrew's boot path rather than on its own require
  closure — the "undefined constants" coupling `homebrew/closure.py` measures. Without it,
  half the file's branches die on a `NameError`.
