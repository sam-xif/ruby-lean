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

**Status:** **fixed, clink 49** (see §The fix, below). **Severity:** high — it was the reason
§F2 below was a *wrong answer about Ruby* rather than only about the model. **Found by:** asking what
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
is the *more* permissive one, and it hides an error CRuby raises. Nothing in the corpus covered
it, because no rung defined a method named after a Kernel builtin.

**The fix (clink 49).** `finishSend` now looks the name up before taking the shortcut, and only
takes it when nothing user-defined shadows it:

```
let shadowed :=
  match methodOn m.heap (classOf m.heap recv) mname with
  | some (_, md) => md.builtin.isNone && !md.undefined
  | none => false
let mkLam := implicit == .implicit && mname == "lambda" && !shadowed
```

Same `builtin.isNone` test the `X.new { … }` arm three lines below already used for the same
reason, so the model now makes the distinction in one style rather than two. `mkLam` is
computed from `shadowed` as well, so a shadowed call passes an ordinary (non-lambda) Proc as
the block, which is what CRuby does. Measured after: tier-0 difftest **992 agree, 0
disagreements** (1304 cases, 306 gated) and the ratchet corpus **237/237 agree**;
`corpus/237-shadowed-lambda-unsafe` is the rung that now covers it.

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

**Status:** **fixed, clink 49** — both halves. **Severity:** high, with a caveat that is the
entry's whole point.
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

**The fix (clink 49).** Both, as argued above:

* **`Judge.lambdaLit` gained `nameFree κ m = true`** — no top-level `def` of the name, and no
  class or module in the table declaring it as an instance or singleton method. An
  `autoParam` (`:= by rfl`), so none of the 14 `Judge.lambdaLit` uses in `Rungs.lean` moved;
  `chk`'s guard gained the same conjunct and `chk_sound`'s `lambdaLit` case destructures one
  more `&&`. Deliberately coarse — it asks whether *any* class declares the name, not whether
  `self`'s does — because sharpening it means walking the ancestor chain and no rung wants the
  precision.
* **The model shadows properly** (§A5 above), so the two executors now agree on the program.

**Regression on file**: `corpus/237-shadowed-lambda-unsafe` (`expect_validate: false`,
`unsafe_program`) plus a `CheckRungs.lean` control, which is where the rejection is labelled
*sound* by running the program: it reports `rejected (sound: really type-stuck)`.

### F3. A method body's `def` escapes the checker's context, so every call rule carries a stale `defs` table

**Status:** **fixed, clink 49** (the conservative half — see §The fix below). **Severity:**
high — `validate` returned `true` on a program **both** executors take to `TypeError`, which is
the §F1 shape exactly. **Found by:** the semantic ladder again
(clink 48), and this time by the *sixth stall point* rather than by a rung:
`Denote/Sem/notes.md` recorded that a rule cannot re-assert conformance with the incoming `κ`
after a statement that declares something. The consequence nobody had drawn is that a **call**
declares things too — the body runs, and `def` is an ordinary statement inside it.

```ruby
def bar
  1
end
def foo
  def bar
    "s"
  end
  1
end
foo
bar + 1
```

| | |
|---|---|
| CRuby | `TypeError: no implicit conversion of Integer into String` |
| the Lean model | `TypeError`, same message — the two **agree** |
| `lake exe ratchet --stdin` | `{"type":"Integer","validate":true}` |

**What is wrong.** `Ctx.afterStmt` grows `κ.defs` at *statement* boundaries of the sequence it
is typing, and `Judge.vcallDef` — like every other call rule — concludes
`Judge κ Γ I (.vcall m) ρ Γ I` with the **same `κ`** it started from. So the nested `def bar`
is recorded in the context used to type `foo`'s *body* and nowhere else, while at runtime it
installs on `Object` and **replaces** the earlier `bar` (`Heap.defineMethod` filters the old
entry out). After `foo` returns, `κ.defs` says `bar` returns `Integer` and the heap says
`String`, and `Judge.vcallDef` at the next statement types `bar` off the stale table.

It is specifically a **redefinition** that is unsound. A body that defines a *new* name only
makes the checker miss a method it could have typed — conservative, and that is what
`DefTable`'s "already" docstring is about.

**Why the ladder names the family and the corpus did not.** 235 corpus programs agree and 142
negative controls are rejected, because no rung defines a method inside a method body. The
obligation says it without a witness: `Obl.Judge.vcallDef` concludes `StateOk κ Γ I m'`, whose
`DefsOk` component asks that every entry of `κ.defs` be installed at the post-machine — and the
body just replaced one. Same for `callDef`, `callDefKw`, `callMethod`, `selfCall`, `closCall`,
`iterBlock` and the rest: **every rule whose run can execute a statement** is exposed, which is
why this entry is about a family rather than a rule.

**The fix, and the choice in it.** Two shapes:

* **A premise, per call rule:** the body declares nothing that `κ` records — a syntactic
  `bodyDeclares?`-style check, conservative and cheap, and the same move `Judge.bareName` makes
  with `defGet? κ.defs m = none`. Rejects `def foo; def bar; …; end; …; end` outright.
* **Threading the context through the judgment** (`Judge κ Γ I e τ Γ' I' κ'`), which is what
  the semantic obligation actually wants — see `Denote/Sem/notes.md` §The sixth stall point,
  where the same fix is what `Judge.defStmt`'s own (false) obligation needs. It is a change to
  `Judge`'s signature and therefore to every derivation on file.

Not fixed in clink 48, which ran under an explicit "do not modify `Ratchet/`" constraint. The
regression to add with the fix is the program above, as an `unsafe_program` rung — a `true` on
it is this bug returning.

### F4. A user `method_missing` turns the miss `Judge.bareName` reasons from into a return

**Status:** **fixed, clink 52.** **Severity:** high — `validate` returned `true`, with a
*type*, on a program **both** executors take to `TypeError`; the §F1/§F3 shape exactly.
**Found by:** the semantic ladder, while attempting `Obl.Judge.bareName` — see below, because
*how* is the point.

```ruby
@a = "s"
def method_missing(*n)
  @a = 1
  2
end
x
@a + "b"
```

| | |
|---|---|
| CRuby | `TypeError: coerce must return [x, y]` |
| the Lean model | `TypeError: coerce must return [x, y]` — the two **agree**, message included |
| `lake exe ratchet --stdin` | `{"ivars":"{@a: String}","type":"String","validate":true}` |

And the minimal form, where the wrong answer is the *type* rather than a missed raise:

```ruby
def method_missing(name)
  @a = 1
  2
end
x
@a
```

`validate` answers `NilClass`; CRuby and the model both answer `1`.

**What is wrong.** `Judge.bareName` reads a bare `x` as raising `NameError` — which is outside
the `NoMethodError`/`ArgumentError`/`TypeError` family this ladder defines type-safety over —
and concludes `.any` with `Γ` and the ivar spine `I` threaded out **unchanged**. Both halves
of that rest on the call never returning. A user `Object#method_missing` falsifies both:

* the miss **returns** (`x` is `2`), so `.any` is now a claim about a real value rather than a
  vacuous one; and
* the body **runs**, and an assignment in it rebinds an ivar. The spine threaded out unchanged
  still said `@a : String` after `@a` had become `1`, and `Judge.ivarRead`'s completeness
  reading of the spine is what then turns that into a wrong type.

The second is the one that bites, and it generalises: *any* rule that concludes a run has no
effect on `I` is wrong about a run that can execute an assignment. `bareName` is the only rule
that claims it for a **send**.

The `TypeError` in the reproducer is reached by a second miss, and it is worth spelling out
because it is why the program is type-*stuck* rather than merely mistyped: `Integer#+` with a
`String` argument tries the coerce protocol, `"b".coerce` misses, and *that* miss goes to the
same `method_missing`, which answers `2` — not the `[x, y]` pair the protocol requires. With a
user `method_missing` installed, a `NoMethodError` is unreachable, so a witness has to be a
`TypeError` or an `ArgumentError`.

**Why no corpus rung caught it.** Two rungs define `method_missing`
(`corpus/113`/`114-metaprog-method-missing-*`) and both call the missing method on an
**explicit** receiver (`Ghost.new.anything_at_all`), which is `Judge.callMissing` — a rule
that types the handler's body and threads its effects. No rung had a `method_missing` *and* a
bare name, and nothing about either rung suggests looking for one.

**Why the ladder did.** `Obl.Judge.bareName` asks for `StateOk κ Γ I m'` at the post-machine
of a run of `.vcall m`, and the ninth stall point (`Denote/Sem/notes.md`) had already recorded
what that needs: an **upper** bound on the machine — "`x` resolves to nothing" is not
implied by any lower-bound component. Clink 51 supplied one for the *name being called*
(`NameFreeOk`). Attempting the rung with that in hand forces the next question — which other
name has to be absent for the walk to reach the `NameError`? — and `dispatchMiss`'s answer is
`method_missing`, in one line of the interpreter. The counterexample is two lines after that.
Nothing was searched for and no witness generator ran.

**The fix (clink 52).** A premise, `nameFree κ "method_missing" = true`, on `Judge.bareName` —
the same predicate and the same shape as §F2's fix to `Judge.lambdaLit`, for the same reason: a
rule that reasons from the *absence* of a method needs the program not to have supplied one.
An `autoParam`, so no derivation term moved (the corpus's one `bareName` rung is at a `κ` that
declares nothing, and the premise is `rfl`); `Ratchet/Validate.lean` gains the matching
conjunct, and `Ratchet/Proof/ChkSound.lean`'s `bareName` branch splits the guard into the two
premises, so the checker is still *proved* to only accept what `Judge` derives.

Pinned by two regressions, both required: `corpus/239-method-missing-bare-name-unsafe`
(`expect_validate = false`, `unsafe_program`) and a `CheckRungs.lean` negative control, which
reports it as a **sound** rejection because the model really does go type-stuck on it.

**What is still open.** `nameFree` reads `κ.defs` and `κ.classes` and not `κ.closures`, so a
`method_missing` installed by `define_method` is not covered — the same coarseness §F2's fix
has. Not reachable today: `Object#define_method` is `unsupported` in the model, so no such
program executes here at all. The day it is modeled, the premise wants `κ.closures` too.

## §F5 — `Judge.vasgn` records the right-hand side's type verbatim, and an *alias* type must not be recorded that way

**The rule.** `Judge.vasgn` types `x = e` with `e`'s type `τ` and records that type for `x`:
`envSet (killClosOver (killAliasesTo Γ' x) x τ) x τ`. Nothing in the rule constrains `τ`.

**Why that is unsound.** `Ty.sameAs y σ` means *this binding holds the same value as `y`* — a
fact about a binding, which is why `denM` ignores it (`Denote/Den.lean`: `denM (.sameAs _ τ) =
denM τ`) and `EnvOk` is where it acquires meaning (`Denote/Sem/State.lean`: an entry
`x : sameAs y ρ` requires `m.getLocal x = m.getLocal y`). So if `τ` is an alias type, the
premise `SemJudge κ Γ I e τ Γ' I'` carries **no information about `y`** — it is exactly the
premise for `stripAlias τ` — while the conclusion claims `x` and `y` now hold the same value.

The counterexample is immediate: `e := 1`, `τ := sameAs "b" .int`, in a state where `b` holds
`2`. The premise holds (`denM (sameAs "b" .int) m' (.int 1)` *is* `denM .int m' (.int 1)`), the
two `capStale` guards hold (`capStale` recurses through `sameAs` into `.int`, where it is
`false`), and the conclusion's `EnvOk` requires `1 = 2`.

**Why the ladder found it.** `Obl.Judge.vasgn` is the first compound obligation whose
conclusion writes the environment through `envSet` with a type it did not itself construct.
Discharging it means producing `StateOk κ (envSet … x τ) …`, and `StateOk_setLocal` — the
transport already on file — asks for `stripAlias ρ = τ` and, when `ρ` is an alias, for the
alias to hold of the written value. Neither is available. Nothing was searched for: the
transport's own hypotheses name the missing premise.

**Not reachable through `chk`, and the source already said so.** `Validate.lean`'s `var` arm
reads `some (stripAlias τ, …)` with the comment *"Tier 12: `stripAlias`, so no expression ever
has type `sameAs`"*, and `Judge.varAlias`'s conclusion type is the stripped `τ` rather than the
alias. The invariant was real; it just was not a premise of the rule that depends on it. So
there is **no corpus counterexample to add** — an accepted program cannot exhibit this — and
that is the honest report: a rule unsound in isolation, whose soundness in the checker rested
on an invariant stated only in a comment.

**The fix.** `(halias : isAliasTy τ = false := by rfl)` on `Judge.vasgn`, with the matching
conjunct in both of `Validate.lean`'s `vasgn .lvar` arms (the general one and the
`vasgn t (var x)` arm that shadows it) and the three-way split in
`Ratchet/Proof/ChkSound.lean`. The second arm's guard is `isAliasTy (stripAlias τ) = false`,
which is *not* vacuous by definition — `stripAlias` removes one layer, so a nested
`sameAs y (sameAs z σ)` in `Γ` would survive it. Nothing builds one, and now nothing has to
assume that: it is rejected rather than assumed away.

Gate numbers unchanged: `run_ratchet.sh` 35 mismatches before and after, `run_check_rungs.sh`
177/177 + 145/145.

## §F6 — `Judge.isAQuery` assumed the boot `is_a?` was intact, and only checked the user table for `.inst` types

**The rule.** `Judge.isAQuery` types `recv.is_a?(C)` as `.bool` behind one guard,
`isADispatchOk κ.classes σ = true`. That guard reads

```
| .inst n _ => (mroGet? C n "is_a?").isNone      -- the user chain does not override it
| .union σ τ => … | .nilable ρ => …
| .any | .clos _ _ _ | .never | .sameAs _ _ => false
| _ => true                                       -- ← every immediate, unconditionally
```

so at an `Integer`, a `String`, a `Symbol` — anything whose type is not an `.inst` — it answers
`true` **without looking at anything**. That is an assumption that the boot `Integer#is_a?` is
still the builtin, and Ruby lets a program falsify it:

```ruby
class Integer
  def is_a?(c)
    "s"
  end
end
5.is_a?(Integer) & true    # certified `bool & bool`; runs `String#&`, which does not exist
```

`& true` is what turns the wrong *type* into a real `NoMethodError`: `bool` has `&` and
`String` does not, so this is inside the type-stuck family rather than merely imprecise.

**Why the ladder found it.** `Obl.Judge.isAQuery` has to be discharged from the machine's own
dispatch, and the component that describes it (`QueryOk`, clink 54) can only be stated for a
name the *context* does not declare — `MethodsExact` allows any method the context declares, so
a reopening is a conformant machine. Writing the component down is what asks the rule for the
premise. Nothing was searched for.

**The second premise is §F4's, for §F4's reason.** A receiver whose class does not resolve
`is_a?` **at all** — a `BasicObject` subclass — reaches `dispatchMiss`, whose last question
before raising `NoMethodError` is whether the receiver has a `method_missing`. If it does, the
call *returns*, with a value of any type. So `nameFree κ "method_missing"` is needed here
exactly as it is on `Judge.bareName`.

**The fix.** Two `autoParam` premises on `Judge.isAQuery` — `nameFree κ "is_a?" = true` and
`nameFree κ "method_missing" = true` — with the matching conjuncts in `Validate.lean`'s `is_a?`
arm and the three-way split in `Ratchet/Proof/ChkSound.lean`. No derivation term moved (the
corpus's `is_a?` rungs are at contexts that declare neither name, and both premises are `rfl`).

Pinned by `corpus/241-reopen-integer-is-a-unsafe` (`expect_validate = false`,
`unsafe_program`), which the checker already rejected — for the *arity* of the `&` that follows
rather than for this — and now rejects for this reason too.

Gate numbers unchanged: `run_ratchet.sh` 35 mismatches, `run_check_rungs.sh` 177/177 + 145/145,
corpus agreement 242/242.

**What is still open.** `nameFree` reads `κ.defs` and `κ.classes` and not `κ.closures`, so an
`is_a?` installed by `define_method` is not covered — the same coarseness §F2 and §F4 have, and
unreachable for the same reason (`Object#define_method` is `unsupported` in the model).

## §F7 — `Judge.caseEqQuery`'s guard looked at the wrong table: `===` dispatches through the eigenclass chain

**The rule.** `Judge.caseEqQuery` types `C === v` as `.bool` — the form `case v when C`
desugars to — behind one guard, `smroGet? κ.classes cn "===" = none`. The docstring justified
dropping §F6's `isADispatchOk` on the grounds that `Module#===` is implemented directly as the
ancestor test and does *not* go through `obj.is_a?`, so a user-written `is_a?` cannot affect
it. That much is true, and it is not the hole.

The hole is that `smroGet?` asks about singleton methods **on `cn` itself**, while the dispatch
of `C === v` starts at `classOf(C)` — `C`'s eigenclass — and walks its whole ancestor chain.
Two shapes get past the guard:

```ruby
class A
  def self.===(o)      # inherited by B's eigenclass; `smroGet? … "B" "===" ` is none
    "s"
  end
end
class B < A
end
(B === 5) & true       # certified `bool & bool`; runs `String#&`, which does not exist
```

```ruby
class Module           # `Module#===` is what *every* class object resolves `===` to
  def ===(o)
    "s"
  end
end
(Integer === 5) & true
```

As in §F6, `& true` is what turns the wrong type into a real `NoMethodError` rather than mere
imprecision, so this is inside the type-stuck family.

**Why the ladder found it.** `Obl.Judge.caseEqQuery` has to be discharged from the machine's
own dispatch, and the component that describes it (`ClsQueryOk`, clink 55) says what `===`
resolves to at a *class object* receiver — measured at the booted machine, all 87 class objects
answer `Module#===`, public and unshadowed. Writing that component down forces the question the
guard was ducking: the claim can only hold for a name the context does not declare, because
`MethodsExact` allows the context's own methods to be anywhere in the heap. The rung is
unprovable without the premise, and the two programs above are what the premise excludes.

**The fix.** `Judge.caseEqQuery` gained `nameFree κ "===" = true` and, for the eigenclass that
resolves `===` nowhere at all, §F4's `nameFree κ "method_missing" = true`; `Validate.lean`'s
`===` arm gained the matching conjunction and `ChkSound.lean` the split. `nameFree` is blunter
than the two shapes above — *any* `def ===` anywhere in the program turns the rule off,
including a perfectly harmless one on an unrelated class — and that bluntness costs rungs, not
soundness. The precise premise ("no `===` on `Module`/`Class`/`Object`/`BasicObject`, and no
singleton `===` on `cn` or any of its ancestors") is expressible and is the natural refinement
if a rung ever wants it.

Corpus: `243-inherited-singleton-case-eq-unsafe`, which validate now rejects. The
`class Module` shape is **not** a corpus element: reopening `Module#===` breaks the difftest
harness's own JSON wrapper (`case` in `json/common.rb`), so the program produces no observation
to compare. It is recorded here instead, and it is the shape that shows why the premise has to
be a statement about the whole context rather than about `cn`.

**What is still open.** The same `κ.closures` coarseness §F6 records, for the same reason.

## §F8 (unconfirmed) — `Judge.classOf`'s conclusion is exact where its receiver premise is not

Not fixed, and possibly not a bug: recorded because it was found while sizing the rung and the
argument is short. `Judge.classOf` types `x.class` as `.clsOf n` from a receiver premise of
`.inst n I`. But `denM (.inst n I) m v` is `isAName m.heap v n = true ∧ …` — an *is-a* test,
which a `D < C` instance passes at `n = "C"` — while `denM (.clsOf "C")` is
`isClassRefNamed`, the **exact** class object. So `x : .inst C` where `x` is really a `D`
makes `x.class` a counterexample to the rule as stated over the denotation.

Whether it is **reachable** is a different question, and the answer looks like no. Probed, in
the direction the goal asks for: `244-self-class-subclass-unsafe` is the natural attempt — an
inherited `C#whoami` returning `self.class`, called on a `D` — and CRuby really does raise
`TypeError` on it, so it is a genuine unsafe program. `validate` **rejects** it, and the reason
is not luck: the checker types a callee's body per *call site*, with the self type taken from
the receiver's type at that site (`Validate.lean`'s `.inst n Iself` arm), so `self.class` in
`whoami` is `.clsOf "D"` and the program never gets an `.inst C` for a `D` at all.

The same argument runs over `Judge` itself, which is the level the obligation is at. Every
`.inst n` in a derivation traces back either to an allocation of exactly `n` (`newInst`/
`newInstNoInit`) or to a `self` whose class is `κ.frame`'s **`recvClass`** — and `recvClass` is
threaded *exactly*: `superCall`/`zsuperCall` change `defClass` and deliberately keep
`recvClass`, which is the one place a subclass could have leaked in. Joins widen (`joinT` of two
`.inst`s is not an `.inst`) rather than upcast, so there is no subsumption by the back door
either. So the rule is true of every derivable judgment and false of the denotation read on its
own — the §F5 family — and discharging it needs either an exactness conjunct threaded through
the judgment or a `Ty` that can say "a class object for *some* subclass of `n`", which is a
language gap rather than a bug. Filed, with the probe kept as a negative control.

## §F9 — `isAAnswer`'s *negative* answer read a static table, and `include` into a core class falsifies it

**Confirmed reachable, and the first finding on this ladder that `validate` accepted before it
was fixed.** Corpus `245-include-into-core-narrow-unsafe`:

```ruby
module M
end
class Integer
  include M          # `5.is_a?(M)` is now true
end
x = 5
if x.is_a?(M)
  x + "s"            # certified, because the branch is typed `x : never`
else
  1
end
```

CRuby raises `TypeError` (`String can't be coerced into Integer`). `validate` answered **true**.

**The mechanism.** `isATy` refines the then-branch of `if x.is_a?(C)` by asking `isAAnswer`,
and turns a `some false` — "no value of this type is a `C`" — into `Ty.never`, i.e. *this
branch cannot run*. `never` makes everything downstream vacuous, so a wrong `some false` does
not merely mistype the branch: it certifies **anything** in it. And `isAAnswer`'s builtin arm
was

```
| τ => (builtinAncestors τ).map (fun ch => ch.contains cn)
```

— a **static table**. `builtinAncestors .int` is `["Integer", "Numeric", "Comparable"] ++
rootAncestors`, so `is_a?(M)` at an `Integer` answered `some false` for every `M` outside it,
which is an assumption that nothing has been mixed into `Integer`'s chain. Ruby lets a program
falsify that in three lines.

The `.inst` arm was careful about exactly this — `ancestors?`/`mixinAncestors?` refuse a chain
whose mixins they cannot see, and `Judge.lean`'s own comment at `ancestorsUp` says omitting
them "would make `isAAnswer` answer `is_a?(SomeIncludedModule)` with a *wrong* `some false`".
The hole is that the *declared* chain was checked while `rootAncestors` was appended blindly,
and the **builtin** chain was not checked at all: tier 10 gave `include` a rule, and the
comment above `rootAncestors` ("whichever tier gives `include` a rule must revisit
`isAAnswer`") was the prediction that this half of the revisit did not happen.

**The fix.** `mixinFreeChain C ch` asks whether the context reopens any class *named in the
chain* with an `include` or a `prepend`, and both arms of `isAAnswer` now answer

* `some true` when the chain contains `cn` — unchanged, and still sound: a mixin only **adds**
  ancestors, so a name already in the chain stays an ancestor;
* `some false` only when the chain is mixin-free;
* `none` — "this judgment cannot tell" — otherwise, which `isATy`/`notATy` already handle by
  keeping the type unrefined in both branches.

`isANilPart` needed the same treatment (`class NilClass; include M; end` makes `nil.is_a?(M)`
true) and now takes the table; `notANilPart` did not, because its `.never` is on the side where
`cn` *is* in the chain.

**Precision cost, measured.** The refinement is retained wherever it was justified: the same
program without the `include` still types (its then-branch really is unreachable), and all 177
hand derivations plus the 145 negative controls are unaffected. `expect_validate` mismatches
stayed at 35.

**How it was found.** Not by search. `denM_isATy` — the fifth of the six type-level lemmas the
twelfth stall point lists — is exactly the statement "the refined type still denotes the
value", and it cannot be proved without `isAAnswer` conformance. Writing down what that
conformance would have to say ("the static chain is the machine's chain") is what exposed the
missing side condition; the program above was then written to fit the hole rather than the
other way round. That is the same route §F6 and §F7 took, and the third time the *obligation's*
statement — not a test — is what named the assumption.

**What is still open.** `mixinFreeChain` reads the context, so a mixin installed by
`Object#include` through `send`/`*_eval` is outside it — the `κ.closures` coarseness §F2, §F4,
§F6 and §F7 all share, and unreachable for the same reason (those forms are `unsupported` in
the model or have no rule).
