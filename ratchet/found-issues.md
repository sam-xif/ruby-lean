# Issues found while building tiers 13–19 (the Homebrew slice)

**Written 2026-09-01**, from the pass described in [`AGENTS.md`](AGENTS.md) §2026-09-01.
A tracking list, not a work plan: each entry is something that is *wrong or missing
outside this package* — in the Lean model, in the difftest harness, or in the shared boot
stubs — that a ratchet rung ran into. Checker-side *gaps* are not here; they are the ladder
(§The ladder) and the `Ty` grammar gaps (§Ty language gaps).

**§F is the exception, added 2026-09-01 by the semantic ratchet** (clink 45): a checker
**soundness bug** — `validate` returning `true` on a program the semantics takes to a
`TypeError` — is a wrong answer rather than a gap, and belongs with the other wrong answers
rather than in a ladder that reads "not yet climbed".

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

### A4. Two `String` type errors the model gates instead of raising

**Status:** open. **Severity:** low — it weakens two controls, no rung. **Found:** 2026-09-01,
ratchet clink 36 (tier 15a).

| program | CRuby | the model |
|---|---|---|
| `"abc".delete_prefix(1)` | `TypeError: no implicit conversion of Integer into String` | `unsupported(start_with?)` |
| `"abc".sub(1, "-")` | `TypeError: wrong argument type Integer (expected Regexp)` | `unsupported(String#sub/gsub with a non-String, non-Regexp pattern)` |

Both CRuby messages verified directly. These are the controls for
`PrimSig.strDeletePrefix`/`strSub` requiring their argument types rather than leaving them
unconstrained, so the rows are justified against Ruby and *uncorroborated* by the model — the
same shape as A3, and much narrower. The second gate is explicit and arguably the right
behaviour for an unmodelled signature; the first is incidental (`delete_prefix` is implemented
in terms of `start_with?`, so the gate fires one method down).

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

### A5. A user `def lambda` does not shadow `Kernel#lambda` in the model — and the checker trusts the model

**Status:** open (model side). **Severity:** high — it is the reason §F2 below is a *wrong
answer about Ruby* rather than only about the model. **Found by:** asking what
`Judge.lambdaLit`'s semantic obligation needs of a conformant machine (clink 48): the rule has
no premise excluding a user definition of `lambda`, so the rung has to know how the machine
dispatches the name.

```ruby
def lambda
  5
end
f = lambda { 1 }
f.call + 1
```

| | |
|---|---|
| CRuby | `NoMethodError: undefined method 'call' for an instance of Integer` |
| the Lean model | `{"result_repr":"2"}` — the builtin won, `f` is a Proc |

A toplevel `def` installs a **private instance method on `Object`**, and `Kernel` is a module
included *in* `Object`, so `Object`'s own entry comes first in the ancestor walk: in CRuby the
user's `lambda` shadows `Kernel#lambda`, and `lambda { 1 }` returns `5`. The model cannot do
that, and not by accident of lookup order — `Interp/Send.lean`'s `finishSend` special-cases
the name **before any lookup at all**:

```
| .lit ps ls body =>
  let mkLam := implicit == .implicit && mname == "lambda"
  let (v, m) := reifyBlock m ps ls body mkLam
  if implicit == .implicit && (mname == "lambda" || mname == "proc") then
    .next (withCtl m (.value v))
```

So `lambda`/`proc` at an implicit-self send with a literal block are **unshadowable** in the
model. `Proc.new` is in the same arm but keyed on the receiver, which is the right shape; these
two are keyed on the name.

Same class as A1–A4 (both executors run, they disagree) but note the direction: here the model
is the *more* permissive one, and it hides an error CRuby raises. Nothing in the corpus covers
it, because no rung defines a method named after a Kernel builtin.

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

---

## F. Checker soundness — `validate` accepts a type-stuck program

**Out of this file's stated scope, on purpose.** The header says checker-side gaps belong to
the ladder rather than here. A *gap* does; this is not a gap, it is a **wrong answer**: a
program `validate` certifies and the real semantics takes to a `TypeError`. There is nowhere
else for that to live, and it should not live in a ladder that reads "not yet climbed".

### F1. Assigning to a captured local does not invalidate the `Ty.clos` that captured it

**Status:** **fixed, clink 46** (see §The fix, below). **Severity:** high — `validate`
returned `true` on a program whose real outcome is **type-stuck**, which is the one thing the
ladder's permanent negatives exist to make impossible. **Found by:** attempting
`Judge.vasgn`'s semantic obligation (`Denote/Sem/`, clink 45); see below for why that pins the
rule exactly.

```ruby
x = 1
f = lambda { x }
x = "a"
f.call + 1
```

| | |
|---|---|
| CRuby | `TypeError: no implicit conversion of Integer into String` |
| the Lean model | `uncaught`, and `Semantics.typeStuck = true` |
| `lake exe ratchet --stdin`, before clink 46 | `{"type":"Integer","validate":true}`, with `f : <closure#0>{x: Integer}` |
| `lake exe ratchet --stdin`, after | `{"validate":false}` |

Also reproduces with `proc` for `lambda`, and inside a method body. It does **not** reproduce
when the reassignment keeps the type (`x = 2` — sound, and correctly accepted), nor through an
instance variable (`@f = lambda { x }` is rejected for an unrelated reason).

**What is wrong.** `Judge.lambdaLit` records the creation-site environment into the type:
`.clos idx (envToSpine Γ) …`. A Ruby block captures **by reference**, so that spine is a claim
about a *binding*, not about a value — exactly like `Ty.sameAs`. `Judge.vasgn` already knows
this about `sameAs`: it applies `killAliasesTo Γ' x`, and its docstring enumerates the three
ways an alias can go stale. It does the same job for **no** `Ty.clos`. So after `x = "a"` the
environment holds `f : clos idx {x: Integer}` while `x` holds a `String`, and
`Judge.closCall` — which judges the body in `spineToEnv cap` — types `f.call` as `Integer`.

`capIntact` is not this. It stops a *block body* from retyping a captured local
(`Ratchet/Judge.lean` L2067 and its docstring); nothing stops ordinary code **after the
literal** from doing it, and that is the case here.

**Why the semantic ladder names the rule and the corpus did not.** 232 corpus programs agree
and 140 negative controls are rejected, because no rung writes this shape. The obligation
does not need a witness: `Obl.Judge.vasgn` concludes `StateOk κ (envSet (killAliasesTo Γ' x) x τ) I' m'`,
whose `EnvOk` component asks for `denM (clos idx cap σ) m' f` — i.e.
`denSpine cap m' (closLocal m' cl)`, the captured *frame's* locals read at the post-machine.
`m.setLocal x` writes through the captured chain, so `closLocal m' cl` answers the new value
and the spine no longer denotes. **`Judge.vasgn`'s obligation is false as written**, and that
is the whole content of this entry: the rung did not fail to close for want of a lemma, it
failed because the rule is not true of `stepFn`.

### The fix (clink 46)

Two functions and one premise, all in `Ratchet/Ty.lean` §Stale closure captures and the two
rules that use them.

* **`killClosOver` / `killClosOverSpine`** widen to `.any` every binding — and every ivar-spine
  entry — whose type records a capture of the assigned name **at a different type**.
  `Judge.vasgn` and `Judge.vasgnAlias` apply them beside `killAliasesTo`, and
  `Ratchet/Validate.lean` matches. Both are the *identity on a closure-free environment*, which
  is why the 177 derivation terms in `Ratchet/Rungs.lean` needed no edit — the same property
  the alias operations were built with.
* **`capStale x τ τ = false`, an `autoParam` premise on both rules**, is the half
  `killClosOver` cannot do. A second reproducer, found while checking the first fix:

  ```ruby
  x = 1
  x = lambda { x }
  x.call + 1        -- CRuby: NoMethodError (Proc + Integer)
  ```

  Here the stale record is in the type being **bound**, and in the assignment expression's own
  type index, so there is nothing left to widen. `:= by rfl` is what let the premise be added
  without touching a derivation either (`Judge.varAlias`'s docstring recommends exactly this
  for a `Bool` side condition); `Ratchet/Proof/ChkSound.lean` threads it from the checker's
  guard.

**Precision is kept where it is sound.** `x = 1; f = lambda { x }; x = 2` still types — the
recorded capture is `x : Integer` and still true — which is the same boundary `capIntact`
draws for a block body. That case is `corpus/235-lambda-capture-reassigned-same-type`, a
*positive* rung, so a blanket erasure would fail the ladder.

**Regressions on file**: `corpus/233-lambda-capture-reassigned-unsafe` and
`corpus/234-lambda-captures-own-target-unsafe` (both `expect_validate: false`,
`unsafe_program` — a `true` on either is this bug returning),
`corpus/235-lambda-capture-reassigned-same-type` (the precision control), and two
`CheckRungs.lean` controls, which is where the rejection is labelled *sound* by running the
program: both report `rejected (sound: really type-stuck)`. Numbers after: **235/235 agree,
178 climbed, 177/177 + 142/142**.

**Closed in clink 47: the `Ctx` fields.** `selfTy`, `blockTy` and `consts` can each carry a
frame-sensitive type, and `Ctx` is an *input* to every rule — no rule rewrites it, so no rule
can widen them. They became a fourth guard, `capStaleCtx` (`Ratchet/Judge.lean`), premised on
`vasgn`/`vasgnAlias` the same `autoParam` way. It is sound rather than precise: a method frame
captures nothing, so an assignment inside a method body cannot reach the frame `blockTy`'s
closure captured, but the premise refuses the case where the two merely share a *name*. A
`StateOk` component stating frame-chain disjointness would recover that precision; no rung has
asked for it.

**Two more things the semantic rung turned up** (clink 47), both fixed, both about the
denotation rather than the checker:

* **Nested aliases.** `killAliasesTo` peeled one `sameAs` layer, so `sameAs x (sameAs z ρ)`
  survived an assignment to `x` as an alias to `z` that nothing justifies (`EnvOk` constrains
  only a binding's *outermost* alias). `killAliasTy` now collapses an alias to `x` with
  `deAlias`, which peels all of them. No derivation on file builds a nested alias, so this is
  invisible to the ladder — but the obligation quantifies over every `Γ`.
* **`Value.identEq` is not the right probe for object identity, and is a model bug in its own
  right.** `identEq (.flt a) (.flt b)` is `a == b`, so the model's `equal?` says `0.0` and
  `-0.0` are the same object (they are two different values) and that `NaN` is **not** the same
  object as itself (`Float`'s `==` is false at `NaN`, so `identEq v v` is not reflexive). CRuby
  answers `true` for `x = Float::NAN; y = x; y.equal?(x)`. `Denote`'s `EnvOk` now states object
  identity as `Value` equality and no longer inherits the quirk; the model side is **open** and
  belongs with the §A entries.

### F2. `validate` accepts a program CRuby takes to `NoMethodError` — because the model hides it

**Status:** open. **Severity:** high, with a caveat that is the entry's whole point.
**Found by:** the same question as A5 (clink 48).

The program is A5's:

```ruby
def lambda
  5
end
f = lambda { 1 }
f.call + 1
```

| | |
|---|---|
| CRuby | `NoMethodError` — type-stuck |
| the Lean model | returns `2` |
| `lake exe ratchet --stdin` | `{"type":"Integer","validate":true}`, with `f : <closure#0>` |

**The caveat, and why it is not §F1 again.** This ladder's soundness claim is against the
*model* — that is what a rung of the semantic ratchet discharges — and against the model
`Judge.lambdaLit` is **right**: the model's `finishSend` cannot dispatch an implicit-self
`lambda` with a literal block to anything but the builtin (A5), so the rule's conclusion really
does hold of `stepFn`. The wrong answer is about **Ruby**, and it arrives through the model
divergence. So this is the first entry where the two soundness statements come apart, and it is
worth stating what each one is worth: `run_agreement.sh` (CRuby vs the model, 235/235) is
exactly the gate that would have caught it, and it never saw this program.

**What each side needs.**

* **The model** should let a user definition shadow `Kernel#lambda` (A5). That is the fix that
  makes the two executors agree.
* **The checker needs a premise either way**, and this is the part not to lose: the day the
  model shadows, `Judge.lambdaLit` becomes unsound *against the model* too — its obligation
  turns false at any conformant machine whose `Object` carries a user `lambda`. The premise is
  the same shape as `Judge.bareName`'s: `defGet? κ.defs m = none`, plus the corresponding
  absence from `κ.classes` for a `lambda` defined in a class body. `Judge.closCall`'s `call`
  has the same exposure through `κ.classes` and is worth checking in the same pass.

Not fixed here, on purpose: clink 48 was under an explicit "do not modify `Ratchet/`"
constraint, and a premise added to `lambdaLit` moves the `Rungs.lean` derivations (14 uses of
`Judge.lambdaLit` on file) and the ladder's two committed numbers. It wants its own clink, with
a negative-control rung for the program above — which is what makes the fix pinned rather than
believed.
