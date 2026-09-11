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

### A6. `Symbol#to_proc` — the model's proc carries a **binding CRuby's does not have**, and is not identity-stable

**Status:** A6a **FIXED** (2026-09-08, L266 — `Closure.captured` is now `Option Nat` and the
two `:sym.to_proc` sites take `none`; `Sealed.clos`/`FramesWF.clos` are quantified over the
captured id so a capture-free closure discharges them vacuously, and `Denote/Sem/StepLocal.lean`'s
`not_BuiltinsSeal` is retired. See `ratchet/Denote/Sem/notes.md`, the eighteenth stall point,
for what was implemented and how it differed from the plan). A6b/A6c open.
**Severity:** medium for identity, **high for the capture edge** — see below, it is what stalled
the semantic ratchet's locals layer.

Measured 2026-09-08 with a 20-program probe corpus replayed under `--sut lean` (17 agree,
2 disagree, 1 gate) plus CRuby-only probes for what the model cannot express. CRuby 4.0.5.

**A6a — the capture edge is a fiction.** Both `Symbol#to_proc`
(`RubyCore/Builtins/Strings.lean:449`) and the `&:sym` block-pass path
(`coerceToProc`, `RubyCore/Interp/Support.lean:448`) build

```lean
{ params := [.req "__recv", .rest (some "__rest")], locals := [],
  body := .send (some (.var .lvar "__recv")) s [.splat (some (.var .lvar "__rest"))] none,
  captured := 0, home := 0, lam := true }
```

`captured := 0` names the **toplevel frame**. CRuby's object has no binding at all:

```
:upcase.to_proc.binding          # => ArgumentError (C-level Proc)
:upcase.to_proc.source_location  # => nil
```

So the model's capture graph has an **edge the reference semantics does not have**. It is not
a free choice: `Closure.captured : Nat` (`RubyCore/Heap.lean:136`) while `Frame.captured :
Option FrameId` (`RubyCore/Machine.lean:57`) — the closure record has no way to spell "captures
nothing", and `0` is the least-wrong filler.

**Unobservable through the body, and that is why it has gone unnoticed.** The body's only free
names are its own parameters, so nothing reads or writes the captured frame — probed both ways
and agreeing: a `to_proc` proc invoked from inside a callee cannot read (`b5`) or write (`c2`)
an enclosing local, in CRuby *or* in the model, while a real `lambda { x = 2 }` writes its
captor in both (`c1` → `2` on both sides). Shadowing probes (`__recv`/`__rest` bound at
toplevel) agree too.

**But it is observable to a proof about the capture graph**, which is exactly what
`ratchet/Denote/Sem/Locals.lean`'s `Sealed` is. `Sealed.clos` reads `cl.captured`, so this
fiction breaks the seal at `b = 0` — the toplevel frame, the one every toplevel narrowing rung
is about. `ratchet/Denote/Sem/StepLocal.lean`'s `not_BuiltinsSeal` is the refutation, and
`Denote/Sem/notes.md`'s eighteenth stall point is the write-up. **The honest fix is here, not
there**: give `Closure.captured` the `Option` its `Frame` counterpart already has, so a C-level
proc captures nothing. Blast radius measured: 2 construction sites, ~4 readers under
`RubyCore/Interp/`, 14 files under `RubyCore/Proof/`, 12 under `ratchet/Denote/`.

**Scope of that fix, stated so it is not over-read.** It is right for exactly the two sites
where the model *invents* a Proc for a Symbol. When `&obj` learns to dispatch a **user-defined
`to_proc`** — today `coerceToProc` gates it ("block-pass of a non-Proc (to_proc dispatch is
L2)") — the Proc that comes back is an ordinary `reifyBlock` closure over a real frame, and it
will capture like any other. The `none` shortcut neither breaks nor helps there; the seal will
have to carry it through `Sealed.clos` as usual. **Deliberately not addressed now**; re-read
this paragraph when L2 lands.

**A6b — not identity-stable.** CRuby interns the proc per symbol; the model allocates a fresh
object on every call.

```ruby
a = :upcase.to_proc
b = :upcase.to_proc
a.equal?(b)        # CRuby: true    model: false
```

`:a.to_proc.equal?(:b.to_proc)` is `false` on both, so the interning is per-symbol.
`frozen?` is `false` on both. Independent of A6a and not fixed by it.

**A6c — the zero-argument message.** `:upcase.to_proc.call` raises `ArgumentError` on both
sides, with different messages: CRuby `"no receiver given"`, the model `"wrong number of
arguments (given 0, expected 1+)"`. The model implements the coercion as a genuine two-parameter
lambda where CRuby has a bespoke C-level receiver check.

**What the probes confirm is faithful**, so the arm is close and these three are the whole gap:
`call` (`"AB"`), `&:sym` block-pass (`["1","2","3"]`), extra arguments through the rest
parameter (`:+.to_proc.call(1,2)` → `3`), `lambda?` → `true` on both, `class` → `Proc`,
`NoMethodError` propagation, reuse across calls, and nesting (`map(&:first).map(&:to_s)`).
CRuby's `parameters` is `[[:req],[:rest]]`, which is exactly the model's
`[.req "__recv", .rest (some "__rest")]`. `Proc#arity` is unmodeled (a gate, not a
disagreement).

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

## §F8 (**resolved by §F12** — the fix was in the denotation, not the rule) — `Judge.classOf`'s conclusion is exact where its receiver premise is not

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

## §F10 — narrowing trusted the constant's *name*, and a constant is not its name

**Confirmed reachable, `validate` accepted it.** Corpus `246-const-alias-narrow-unsafe`:

```ruby
Foo = Integer
x = 5
if x.is_a?(Foo)
  x + "s"          # certified: the branch is typed `x : never`
else
  1
end
```

CRuby raises `TypeError`. `validate` answered **true**.

**The mechanism**, and it is one layer above §F9. `narrowCond?` reads the tested class out of
the condition's **syntax**:

```
| .send (some (.var k x)) "is_a?" [.const cn] none => some (k, x, .isA cn, .both)
```

so the refinement is computed for the *name* `cn`, and `isAAnswer` then answers off that name's
static ancestor chain. `"Foo"` is in no chain, so `isATy` produced `.never` — the branch cannot
run — while at runtime `Foo` **is** `Integer` and the branch runs. §F9's `mixinFreeChain` does
not help: nothing was mixed into anything. The two findings are the same shape at different
distances from the name: §F9 is "this name's class has more ancestors than the table says",
§F10 is "this name is not that class at all".

Note the rule's own premises do not catch it either, and that is worth saying, because it looks
as though they should: `Judge.isAQuery`'s argument premise is `JudgeAll … [.clsOf cn']`, and
`cn'` there is the *resolved* name (`Foo = Integer` types `Foo` at `.clsOf "Integer"`). So the
judgment already knows the right answer — it is the **narrowing functions** that re-derive it
from syntax and get a different one. Making them read the argument's type instead is the
principled fix and a much larger change (`narrowEnvs` would have to take a typing, not an
expression); the guard below is the small one.

**The fix.** `narrowNameOk κ` gates the `.isA` shapes on `constGet? κ cn = none` — the same
condition `Judge.constCls`/`constBuiltin` already carry for *reads* of a constant, for the same
reason. A name the context does not bind either resolves to the boot class of that name (which
is what the static tables describe) or does not resolve at all, and then the condition itself
raises `NameError` and the branch never runs. `.truthy`/`.isNil` are ungated: neither mentions a
class.

`narrowEnvs`/`narrowSpine` now take the whole `Ctx` rather than `κ.classes`, because the
constant table is not in the class table. That is visible in `Judge.if'`/`ifNoElse`'s premises
and in `Validate.lean`'s eight call sites; all 177 hand derivations and 145 negative controls
are unaffected, and `expect_validate` mismatches stayed at 35.

**How it was found.** Sizing `denM_isATy` — the same route as §F9, one question further along.
Writing down what "the static chain is the machine's chain" would have to assume turns up the
name→class step first (`classNamed? m.heap cn`), and asking what pins *that* is what produces
the alias.

## §F11 — `rescue` binds a *subclass* instance, and `PrimSig` cannot see the class table

**Confirmed reachable, `validate` accepted it.** Corpus `247-rescue-subclass-message-unsafe`:

```ruby
class E < StandardError
  def message
    5
  end
end
begin
  raise E
rescue StandardError => e
  e.message + "s"     # certified `String + String`; runs `Integer#+` on a String
end
```

CRuby raises `TypeError`. `validate` answered **true**.

**The mechanism, and why it is the deepest of the four.** `Ty.cls n`'s denotation is `isAName`
— *is-a*, not equality — and that is deliberate: `Ty.cls`'s own docstring says "inhabited by
instances of subclasses of `Foo` too, matching `is_a?`". `rescueBind?` is the one place in the
judgment that *uses* the slack, because `rescue C => e` really does bind an instance of a
subclass of `C`. But every rule that **dispatches** on a nominal receiver type looks the method
up in `n`'s own table, and a subclass can have redefined it. `PrimSig`'s `excMessage` row is
where the target's own code makes the call.

So this is not a missing side condition on one row; it is the general gap between "is-a" and
"dispatches like". The other rules in the family are sound only by the exactness-by-
construction argument §F8 records — a value's nominal type is its exact class *everywhere
except* a rescue binding — and this finding is that argument's one real exception.

**The fix.** `Judge.prim` gained a fourth premise, `primDispatchOk κ.classes σ m = true`, which
at a `.cls n` receiver asks whether any **declared** class descends from `n` and redefines `m`.
Precise, not structural: rung `194-ctl-raise-custom` (`rescue Uncomparable`) is unaffected
because nothing descends from `Uncomparable`.

`valueClsNames` — `String`, `Hash`, `Regexp`, `MatchData`, the only four `.cls` names the
judgment mentions — is exempt, and the exemption is the §F8 argument stated where it is used: a
value of one of those types comes from a literal or a builtin and is an instance of exactly
that class, because `rescueBind?` is the only subsumption source and it binds exception
classes. Without the exemption `constLitTy?_sound` would have to be conditional, and *that*
would be a real problem: it types `"s".freeze` in **any** context, so the premise would have to
be pushed onto callers (`Ctx.afterStmt`'s class-body constants, `paramEnv`'s optional defaults)
that have no class table to check. `constLitTy?_primDispatchOk` is the companion lemma — every
type `constLitTy?` produces is exempt — and it is the same shape as `constLitTy?_nilQSafe`.

**What is still open, and it is the interesting part.** The guard is on `Judge.prim`. The same
argument applies to any *other* rule that dispatches on a `.cls n` receiver, and the reason
none is affected today is that the dispatch rules key on `.inst`/`.clsOf`, where exactness
holds. If a later rule dispatches user methods on a `.cls n`, it needs this premise too — and
the principled alternative, which is what a fifth finding of this shape should trigger, is to
split `Ty.cls` into an is-a reading and an exact one, with `rescueBind?` producing the former
and everything else the latter.

## §F12 — the denotation's `Ty.inst` was *is-a* where the whole dispatch family needs **exact**

Not a program that `validate` accepted, and not a rule that is wrong: a **definitional**
finding, and the one that unblocks the largest part of the remaining ladder. It is what §F8 was
a symptom of.

**The gap.** `denM (.inst n I) m v` was `isAName m.heap v n` — is-a — so an instance of a
declared subclass `D < C` satisfied `.inst "C"`. But every rule whose receiver premise is
`.inst n` **dispatches** by typing the callee's body out of `n`'s own table
(`Judge.callMethod`, `callDef`, `selfCall`, the block-carrying variants, `superCall`,
`newInst`…), and `Judge.classOf` concludes the *exact* class object. Under an is-a reading all
of those obligations are false, with the same one-line counterexample: a `D < C` that redefines
the method.

Sizing that is what produced §F8's entry, and the follow-up question is the finding: **is-a is
not what the judgment means by `.inst`.** `Judge` produces an `.inst n` in exactly two ways —
allocating an `n` (`newInst`/`newInstNoInit`) or a `self` whose class is `κ.frame.recvClass`,
which `superCall`/`zsuperCall` thread *exactly* — and `joinT` of two `.inst`s is a union, not
an upcast, so there is no subsumption anywhere. The denotation was strictly weaker than the
judgment, and every dispatch rule was quietly relying on the difference.

**The change.** `Denote/Val.lean` gained `isExactInst`, and `denM`'s `.inst` arm uses it:

```
isExactInst h v n = match classNamed? h name, v with
  | some k, .ref o => o < h.objs.size && realClassOf h (.ref o) == k
  | _, _ => false
```

Two details in it are load-bearing:

* **`realClassOf`, not `classOf`.** They differ at an object with a singleton class: `classOf`
  answers the eigenclass, because that is where dispatch starts, while `realClassOf` answers
  the `klass` field — which is what `Object#class` reports and what "an instance of `n`" means.
  `classOf` would make the reading false for any object that has ever had a `def obj.foo`.
* **The range test.** `Heap.get` is total, so a dangling reference reads as `default`, whose
  class is `0`. The is-a reading survives that (`0` is `BasicObject`, an ancestor of
  everything, so `isAName` only grows); the exact reading does not, and `denM_ext`/`StateOk_ext`
  would break for any machine holding an `.inst`-typed local. `Ext.isExactInst_mono` is the
  transport, and it needs the test.

**`Ty.cls` keeps the is-a reading**, and that asymmetry is the point rather than an oversight:
`rescueBind?` needs it (§F11), and §F11's `primDispatchOk` is what guards the one family that
dispatches on it. So the two nominal arms now say different things, deliberately — `.cls` is
"responds like an `n`, possibly a subclass", `.inst` is "is an `n`".

**What it cost and what it bought.** Cost: four sites (`denM`, `denB`'s mirror, `Grow.lean`'s
monotonicity, one `Ext` lemma). All 41 rungs already on file, the 33 `Examples.lean` `#guard`s,
the 177 hand derivations and the 145 negative controls were unaffected — the guards check real
programs, where instances *are* exact, which is itself evidence for the reading. Bought:
`Judge.classOf` (§F8) is now a rung — `Object#class` answers `realClassOf` and `isExactInst`
*is* `realClassOf`, so the two ends meet definitionally — and the dispatch family's central
obstacle is gone.

**What is still open.** The narrowing rules (`Judge.if'`/`ifNoElse`) need one more thing this
does not give: `denM_isATy` at a `.cls n` type, where the is-a reading survives and
`isAAnswer`'s negative answer still assumes a subclass has not mixed in the tested module. That
is §F9's guard extended from "the chain's own classes" to "the declared classes below `n`", and
it is the next piece of narrowing soundness rather than a separate finding.

## §F13 — the `&&` narrowing shape needs "evaluating the right-hand side cannot rebind the local", and `noLocalAsgn` does not say that

**Not reachable through `validate` today, and recorded as a control** (corpus
`248-and-narrow-closure-write`) rather than as a bug against the checker. It is the reason
`Judge.if'`/`ifNoElse` are **still** not on the ladder after all six narrowing lemmas were
proved, so it is worth stating precisely.

`narrowCond?`'s first arm recognises Ruby's `&&`, which the desugarer emits as a
`seq`/`vasgn`/`if` sandwich, and licenses a **then-branch** refinement of the tested local when
the right-hand side passes `noLocalAsgn` — a syntactic check for "assigns no local". The
refinement is a claim about the local's value *at the point the branch begins*, so what it
needs is that evaluating the right-hand side cannot rebind it. Those are not the same thing:

```ruby
x = 1
f = lambda { x = nil; true }
if x && f.call        # `f.call` assigns no local *syntactically*
  x + 1               # x : Integer recorded; nil in the local; NoMethodError
else
  2
end
```

`noLocalAsgn` admits `.send` (it has to — `x && x > 1` is the shape the feature exists for),
and a send can invoke a closure that assigns. It excludes block-carrying sends, so the
right-hand side cannot *create* a Proc; it cannot exclude *calling* one that already exists,
and no syntactic condition can, because the Proc may arrive from anywhere (a local, an ivar, a
method's return value).

**Why the rung is blocked rather than the rule wrong-and-fixable.** Even the strongest sound
guard available — "the context records no closures at all" (`κ.closures = []`), which is
checkable and true of every corpus rung — does not *discharge* the obligation. It makes the
claim true; proving it needs **"a run of a `noLocalAsgn` expression at a closure-free machine
leaves the current frame's locals alone"**, which is a property of the *run* derived from a
property of the *syntax*. Nothing on file relates the two.

**And removal is not available**, which is the sharpest thing measured about it. The obvious
conservative fix — stop recognising the shape — was tried: `validate`'s *verdicts* do not move
(all 248 rungs answer as before), but `narrow-and-guard`'s **hand derivation stops
type-checking**, because the program genuinely needs the refinement (`x` is `nilable Integer`
there and `x + 1` needs the narrowed `Integer`), and its recorded output environment changes.
So `checkrungs` would read 176/177. The feature is load-bearing, the fix therefore has to be
the guard *plus* the invariant, and this entry is the record of why the cheap way out is not
one.

That is the same shape as the fourteenth stall point ("a `Judge`-derivable expression contains
no `.ret`, therefore its run emits no return jump"), and the two together are what
`Denote/Sem/notes.md` now records as the **syntax-directed run invariants** layer: one
induction over `stepFn` carrying a syntactic predicate through the machine, which unblocks
`if'`/`ifNoElse` and the whole call family. It is the largest remaining piece of the ladder and
it is well-defined, which is progress of a kind — the six lemmas that were the *stated* next
step are done, and what they uncovered is a single named wall rather than a list.

**Update (clink 59): the fix is not a grammar tightening.** `Denote/Sem/notes.md`'s
sixteenth stall point records the measurement: `Machine.setLocal` walks the **capture chain**,
not the frame stack, so `x = 1; f = lambda { x = 2 }; def g(p); p.call; end; g(f)` leaves `x`
as `2` — a callee writing its caller's local, confirmed under CRuby. No tightening of
`noLocalAsgn`'s grammar excludes that, because every tightening still has to admit `.send`
(rung 132 `x && x > 1` is the program the feature exists for, and dropping the send arm stops
three rung derivations compiling), and pinning the dispatch to a builtin is *false at the
booted heap* for every operator but `nil?` and `length`. The honest premise bounds the
program's **closures** — a `ClosuresOk` exactness component in `MethodsExact`'s mould plus "no
closure assigns a local it captures" over `κ.closures`.

## §F14 — `x.nil?` is a dispatch, and the narrowing read the *shape* where it needed the *name*

**Confirmed reachable, `validate` accepted it.** Corpus `249-nilq-narrow-redefined-unsafe`:

```ruby
class NilClass
  def nil?
    false            # `nil` now answers `false`
  end
end
x = nil
if x.nil?
  1
else
  x + 1              # certified: the branch is typed `x : never`
end
```

CRuby raises `NoMethodError` (`undefined method '+' for nil`). `validate` answered **true**.

**The mechanism.** `narrowCond?` recognises `x.nil?` and licenses `isNilTy`/`nonNilTy` on both
branches. `nonNilTy .nilT` is `Ty.never` — "a `nil` cannot reach the else branch" — which is
true of Ruby's `nil?` and false of a redefined one. As in §F9 and §F10, `never` does not merely
mistype the branch: it certifies everything in it.

**Why the existing guard does not cover it, and this is the point.** `Judge.nilQuery` — the
rule that types `x.nil?` itself — carries `NilQSafe σ`, which asks about the **receiver's
shape** (it refuses `.inst` outright, precisely because a user class could override `nil?`).
The *narrowing* is a different consumer of the same expression and needs a different fact: not
"this receiver's `nil?` is safe to type" but "the name `nil?` means what it usually means".
`NilQSafe` at a `.nilT` receiver answers yes — correctly, for typing the query — and says
nothing about `NilClass` having been reopened.

**The fix.** `narrowNameOk κ .isNil` = `nameFree κ "nil?" && nameFree κ "method_missing"`, the
same premise §F6 added for `is_a?`. Corpus-neutral: mismatches stayed at 35, 177/177 hand
derivations and 145/145 controls unaffected.

**How it was found.** Sizing the *else*-side run inversions for `JudgeSeq.nextGuard` — the one
narrowing consumer that reads only `narrowEnvs`'s second component. The fifth finding in a row
where the obligation's own statement, not a test, named the assumption; and the third where the
missing premise is `nameFree`, which is now worth stating as a pattern: **a narrowing that
recognises a *send* needs the sent name to be unclaimed, and the rule that types the send
guards something else.**

## §F15 — a refinement could *create* an alias claim the environment never made

Found by a lemma that turned out to be false, which is the cheapest way to find one.

`refineOne`'s ordinary arm replaced a binding `x : τ` with `x : refine τ`, and the transport
that proves `EnvOk` survives that needed "a refined type is an alias only if the type was".
It is not:

```
falsyTy (union (sameAs y ρ) int) = joinT (sameAs y (falsyTy ρ)) (falsyTy int)
                                 = joinT (sameAs y (falsyTy ρ)) never
                                 = sameAs y (falsyTy ρ)
```

`joinT` returns its non-`never` argument, so refining a **union** that happens to contain an
alias yields the alias. `EnvOk`'s second conjunct reads a `Ty.sameAs` as "these two locals hold
the same object" — a claim about *object identity*, which is what makes `case v when C` narrow
`v` and not just the temporary — and the union never made it.

**Reachability is thin but not obviously nil.** `Ty.sameAs` is created only by
`Judge.vasgnAlias`, whose premise restricts the name to `desugarTemps`, so a union containing
one needs a desugarer temporary whose binding is joined across branches — nested `case`
statements over the same scrutinee. And exploiting it needs a *second* narrowing to consume the
manufactured alias, because `Judge.var` strips aliases and `narrowEnvs` is the only other
consumer. No probe is filed; the finding is recorded at the level the proof exposed it.

**The fix.** `refineOne`'s ordinary arm declines to refine when the result would be an alias
(`if isAliasTy τ' then τ else τ'`). Conservative, corpus-neutral (mismatches 35, 177/177 hand
derivations), and it leaves the **alias arm** — where the environment *did* make the claim, and
`refineOne` refines under it deliberately — untouched.

Worth keeping as a pattern: `Ty.sameAs` is the one type constructor whose denotation is a claim
about **two** values, so every function that builds a `Ty` has to be checked for whether it can
manufacture one. `joinT` can.

## §F16 — the `C === x` narrowing shape put the tested name in the **receiver**, where a non-class constant means something else

Unconfirmed against `validate` and fixed anyway, for the reason §F13 records: the obligation
cannot be discharged without it, and the fact it needs is one the judgment does not carry.

`narrowCond?` recognises `C === x` — what `case x when C` desugars to — and refines `x` by
`.isA cn`. That reading is only correct if `C` **is a class**: `Module#===` is the ancestor
test, but `String#===` is *equality*, and `Integer#===` likewise. With a non-class constant in
the receiver position the condition still returns a boolean, still looks truthy or falsy, and
says nothing about ancestry — so the refinement answers a question the program never asked.

**`validate` cannot build such a derivation today**, and it is worth recording why, because the
protection is three separate accidents: the `.const` rules type only *class* names
(`constCls`/`constBuiltin`/`constExc`, and `BuiltinCls` is exactly the nine classes
`builtinAncestors` covers), a *user* constant is caught by §F10's `constGet? κ cn = none`
guard, and `case t when "pypi"` puts a **literal** in the receiver, which `narrowCond?` does
not match. None of the three is stated as a premise, and the *semantic* premise for the
condition (`SemJudge κ Γ I c σ Γc Ic`) carries no typing at all — so at the level the
obligation lives, the receiver could be anything.

**The fix.** `narrowNameOk κ (.isA cn)` now also requires that `cn` names a class —
`(clsGet? κ.classes cn).isSome || builtinClsNames.contains cn` — plus `nameFree κ "==="`,
`nameFree κ "is_a?"` and `nameFree κ "method_missing"`, which are what make `ClsQueryOk`/
`QueryOk` say where the dispatch goes. Corpus-neutral: mismatches 35, 177/177 hand derivations,
145/145 controls.

With it, `caseeq_inv` goes through: the constant resolves to its class object (`ClassesOk` for a
declared class, `CoreOk.coreNamed` for a builtin name — the same two routes `Const.lean`'s
rungs take), and `ClsQueryOk` says `===` there is `Module#===`.

**The pattern, third instance.** §F14 was "a narrowing that recognises a *send* needs the sent
name unclaimed". This is the other half: **it also needs the operands to be what the shape
assumes.** The narrowing functions read syntax; every fact they rely on about what that syntax
*means* has to be a premise, because the judgment they are premises of is semantic.

## §F17 — `@x = e` invalidated every spine that mentioned `@x`, and the rule said nothing

**Reachable, and the checker accepted it.** `Judge.ivarAsgn` typed `@x = e` at `e`'s type and
set the `self` spine's `@x` entry with `ivarSet`. What it did *not* do is notice that the same
`@x` may be mentioned somewhere else — and every such mention is a claim about the object the
write just changed. The smallest witness:

```ruby
class C
  def initialize; @x = 1; end
  def set(o); @o = o; end          # @o : C[@x : Integer]
  def go;     @o.x_plus_one; end
end
c = C.new; c.set(c); c.instance_variable_set(:@x, "s")   # or, inside a method, @x = "s"
```

Inside a method of `C`, `κ.selfTy` is `.inst "C" (@x : Integer, @o : C[@x : Integer])`. The
assignment `@x = "s"` moves the `@x` entry of the *outer* spine, and `ivarSet` does exactly
that — but the `@o` entry still claims `C[@x : Integer]` of a value which, when `@o` is `self`,
is now an object whose `@x` is a `String`. Reading `@o.@x` as an `Integer` then goes to a
`String`. `κ.selfTy`, `κ.blockTy`, `κ.consts`, the environment `Γ'` and the inferred spine `I'`
are five separate places a type can hold such a mention, and the rule guarded none of them.

**The fix is agreement, not absence.** `ivarAsgnOk κ x τ Γ' I'` now checks
`ivarAgree x τ σ` at each of those five, where `ivarAgree` walks a type and demands that every
spine entry named `@x` claim exactly `τ`. Two rejected alternatives, each rejected by a program
the corpus has:

* **Absence** — "no reachable type mentions `@x`" — rejects *every* in-method assignment,
  because `κ.selfTy` mentions every ivar the class has. Agreement admits the common case
  (`@x = 1` in a class whose `selfTy` says `@x : Integer`) and rejects only the case that is
  actually wrong.
* **Agreement at the top-level entry of `I'` too** rejects type-changing reassignment —
  `if flag then @v = 1 else @v = "s" end`, the program that put `joinIvars` in `Ratchet/Ty.lean`.
  So `ivarAgreeIvars` exempts `I'`'s own `@x` entry, which is sound because `ivarSet` replaces
  it: its old type is never read after the write.

**Arrows are exempt, and that is `Later`'s doing.** `ivarAgree` waves `.arrow0`/`.arrowCons`
through without looking. An arrow's denotation is a claim about *future* runs, quantified over
`Later`-futures of the machine, and an ivar write is one (`IvarWrite.later`) — so the claim
survives it for free. `Ty.clos` is **not** exempt: its denotation reads the captured scope and
creation `self` at *this* machine, so both of its type components are checked. That split is
the same one `found-issues.md` §F1 turned on, one component over.

Corpus-neutral: mismatches 35, 249/249 corpus agreement with 0 disagreements, 177/177 hand
derivations, 145/145 controls. One negative-control probe (240) is newly rejected, which is
what a tightening should do.

## §F18 — a constant assignment *buried* in an expression rebinds what the tables describe

**Reachable, and the checker accepted it.** `X = 1; y = (X = "s"); X + 1` was certified
`Integer`; CRuby raises `TypeError` (`no implicit conversion of Integer into String`).
Confirmed by the corpus: rung 250 read `validate=true (MISMATCH)` against
`expect_validate=False`.

The mechanism is a mismatch between two functions that are supposed to describe the same
thing. `Ctx.afterStmt` records a constant's type through `extendConsts`, which matches a
**top-level `casgn` statement**:

```
| .casgn n _, τ => envSet S (constKey n) τ
```

An assignment anywhere else — the right-hand side of a `y = …`, an argument, a branch — is not
that shape, so `κ.consts` is not updated. `Judge.casgn` had **no premise at all**, and its own
docstring called the invisibility conservative: "a `casgn` buried inside a larger expression
types but is invisible to later reads — conservative, and in the direction that costs a rung
rather than soundness." That reasoning is backwards. Invisibility is only conservative for a
name the tables say *nothing* about; for a name they already describe, the write makes the
description **wrong**, and every later read is certified against it.

**Two doors, not one.** The witness above goes through `constEnv` (the read finds the stale
`κ.consts` entry). The same hole goes through `constBuiltin`/`constCls`/`constExc`, whose
premise is `constGet? κ n = none` — satisfied, because a buried `casgn` records nothing — so
`y = (String = 5); String.new` types `String` as the class object while the machine has `5`.

**The fix is agreement, not absence**, which is §F17's shape for §F17's reason: the *first*
assignment of a name resolves nowhere yet, so absence is what the common case has, and a
re-assignment at the type already recorded changes nothing anyone read. `constAsgnOk κ n τ`
therefore admits exactly those two and refuses a rebinding the tables would be wrong about:

```
match constGet? κ n with
| some σ => σ == τ
| none => (clsGet? κ.classes n).isNone && !builtinClsNames.contains n && !excName? κ.classes n
```

`Judge.cpathAsgn` carries it too, at `constKeyIn owner n` — the key `extendConsts` uses for
`M::X = 4`, so the guard and the table agree about which name moved.

Corpus-neutral: 250/250 agreement with 0 disagreements, mismatches back to **35**, 177/177 hand
derivations, 145/145 controls.

**The pattern, and it is now three deep.** §F17 was "a write to `@x` invalidates every type
that mentions `@x`". This is the same sentence with the constant table in place of the ivar
spine — and the same wrong first instinct (absence) and the same right answer (agreement).
Worth stating as a rule for the rules: **every table the context carries is a claim about the
machine, so every rule that writes what a table describes owes that table a premise.**

## §F19 — `bodyResult` is right for a lambda and wrong for a proc, and there were four doors

**Reachable, four ways, and the checker accepted all four.** Each of these is certified
`Integer` and raises `TypeError` under CRuby *and* under the Lean model:

```ruby
def f;  p = proc { return "s" };  p.call;              1; end;  f + 1   # closCall
def h;  x = [1].map { |y| return "s" };                1; end;  h + 1   # iterBlock
def m;  yield; end
def h;  m { return "s" };                              1; end;  h + 1   # yieldExpr
def h;  p = proc { |y| return "s" }; x = [1].map(&p);  1; end;  h + 1   # iterClosPass
```

Corpus rungs **251–254** are the four, each `expect_validate=False`,
`false_reason="unsafe_program"`.

**The mechanism is one function used in four places.** `bodyResult` rewrites a body that is
*exactly* `return e` to `e`, so a call to that body is typed as `e`'s type. Its docstring
explains why the rewriting is a function on syntax rather than a `Judge` rule for `.ret`
(a rule would make `def f; return "a"; 2; end` validate at `Int`), and it says the rewriting is
"applied only at `closCall`, because only a lambda rung asks". Both halves of that sentence were
false by the time it was read: `bodyResult` had spread to `iterBlock`, `iterClosPass` and
`yieldExpr`, and `closCall` itself cannot tell a lambda from a proc.

**The distinction it needed is Ruby's, and it is not subtle.** `return` inside a **lambda**
returns from the lambda — so `lambda { return e }.call` really does evaluate to `e`, and
`corpus/105-lambda-explicit-return` is that rung. `return` inside a **proc** or a **block**
returns from the *enclosing method* — so the call never comes back at all, and the method's
value becomes `e`'s. Typing the call as `e`'s type is then wrong twice: the call has no type,
and the method's recorded return type is a lie. Every one of the four witnesses above is that
second lie being spent by a caller.

**The fix is a refusal at the one rule that can see the difference.** `Judge.lambdaLit` is the
only rule that turns a block literal into a callable `Ty.clos`, and it admits `lambda` and
`proc` alike:

```lean
def procRetOk (m : String) (body : Expr) : Bool :=
  match body with
  | .ret (some _) => m == "lambda"
  | _ => true
```

as a premise of `lambdaLit`. A `proc` whose body is exactly `return e` now gets **no type**, so
`closCall` never sees one and `bodyResult` stays sound where it is still used — and
`iterClosPass` needs no change at all, because a `&lambda` with a `return` body is genuinely
sound (there the `return` really is the block's value) and a `&proc` no longer has a `Ty.clos`
to be passed.

The other two doors are blocks, never lambdas, so they lose the rewriting outright:
`Judge.iterBlock` and `Judge.yieldExpr` now judge `body` / `c.body` as written. A whole-body
`return` in a block literal has no rule, which is the right answer.

Note the guard matches `bodyResult`'s pattern rather than merely mentioning `.ret`, and that is
deliberate: a `return` anywhere *other* than as the whole body already had no rule, so this
refuses nothing that was previously derivable.

**Corpus-neutral.** 178/254 certified, expect_validate mismatches **35** (unchanged), 254/254
agreement with 0 disagreements, 177/177 hand derivations, 145/145 negative controls, semantic
ladder unchanged at 47/83.

**The pattern, and it is a different one from §F17/§F18.** Those were "a rule that writes what a
table describes owes that table a premise". This one is: **a syntactic shortcut is scoped to the
rule that justified it, and copying it to a second rule re-opens the justification.**
`bodyResult` was introduced with an argument that was correct *for lambdas at `closCall`*, and
the argument was never re-run at the three sites it was later reused at. Worth a rule for the
rules of its own: a function whose soundness argument names a rule does not travel to another
rule for free.



### A7. `lake build Metatheory` is red at HEAD — three breaks, all pre-existing

**Status:** open. **Severity:** medium — no *model* claim depends on these, but `AGENTS.md`
advertises the Direction-B type-safety result as axiom-clean and the library that carries it
does not currently compile. Found 2026-09-08 while establishing a baseline for L266, on a
clean tree; none of the three is caused by that change.

`RubyCore/Proof/` is not in `defaultTargets` (deliberately — it is slow, and nothing the SUT
does depends on it), which is exactly the rot mode `lakefile.toml`'s own comment predicts.

1. **`Proof/Static/Iter.lean:196`, `startArgs_lambda` — the statement is now false, not just
   unproved.** It claims `startArgs … .implicit "lambda" … (.lit ps ls body)` is `reifyBlock`
   by `rfl`. Commit `0657e1c` (the A5 fix — *"teach the model to shadow `Kernel#lambda`"*)
   put a `shadowed` test in front of that branch: a user `def lambda` makes the send an
   ordinary dispatch. So the theorem needs a `shadowed = false` hypothesis, and its consumer
   (`Preservation.lean`, L261's lambda-literal case) then needs a fragment invariant that
   supplies it — which the fragment does not currently have. That missing clause is the real
   finding; the `rfl` is just where it surfaced.
2. **`Proof/Static/Preservation.lean:1518`** — `simp only [List.any_eq_true] at hcond` makes
   no progress, in the private-method gate's `exfalso` branch.
3. **`Proof/Static/Preservation.lean:2404`** (2415 after L266's added lines) — the `arrSplatK`
   case's `exact inv_continueArray …` no longer typechecks.

Measured extent: with exactly those three transiently `sorry`ed, `Metatheory` + `Judgment` +
`HJudge` build clean and the only remaining failures are the `#guard_msgs` axiom bills
correctly reporting `sorryAx`. So the rot is three spots, not a general decay — and (2) and
(3) are proof-script repairs, while (1) is a soundness-shaped gap in the fragment's invariant.


### F20. A **buried `def`** never enters `κ.defs`, and `nameFree` believes it — `validate` certifies a `NoMethodError`

**Status:** **FIXED** 2026-09-09 (`negSeed`, `context-splitting.md` §2.2 / §8.1 step 1 — see
the fix note at the end of this entry). **Severity:** high — `validate` returns `true` with a type for a
program both executors take to a type-stuck outcome. Found 2026-09-09 while testing whether
`Judge`'s failure to thread `κ` is merely awkward or actually wrong. It is actually wrong.

**The witness** (three shapes, one bug):

```ruby
x = (def lambda; 5; end)          # ...or `if true; def lambda; 5; end; end`
f = lambda { 1 }                  # ...or `[def lambda; 5; end]`
f.call + 1
```

| | answer |
|---|---|
| CRuby 4.0.5 | `NoMethodError: undefined method 'call' for an instance of Integer` |
| the Lean model | `NoMethodError: undefined method 'call' for an instance of Integer` |
| `validate` | **`true`**, `type: Integer`, `f : <closure#0>` |

Both executors agree, so this is purely a **checker** unsoundness. Any expression position
works — `vasgn` right-hand side, `if` branch, array element.

**Why.** It is §F2/§A5 (a user `def lambda` shadows `Kernel#lambda`, so `lambda { 1 }` is `5`
and `5.call` raises) reaching through a hole the fix left open. `Judge.lambdaLit`'s guard is
`nameFree κ "lambda"`, which reads `κ.defs`; `κ.defs` is grown by `Ctx.afterStmt`, which
`JudgeSeq.cons` applies to a **statement** and whose `extendDefs` matches only a top-level
`.def' n ps body`. But `Judge.defStmt` has *no premise* and types a `def` **anywhere an
expression is legal**. So a `def` that is not a top-level statement installs a method no table
records, and every rule that reads a table *negatively* believes the name is unclaimed.

**The class of bug, not just the instance.** The tables have two kinds of use and only one of
them is served by "declared *already*":

* **Positive** — "this method exists, call it" (`defDeclared?` feeding `callDef`). Program
  order is essential here, and it is what `DefTable`'s docstring defends: a whole-program table
  would certify `foo(); def foo; end`.
* **Negative** — "no method of this name exists" (`nameFree` -> `lambdaLit`; `declaresName` ->
  `MethodsExact`, `NameFreeOk`; `defDeclared? ... = none` -> `BareNameFree`; `MissFree`). Here
  "already" is exactly the wrong question and a **whole-program** scan is the conservative and
  correct one.

`MethodsExact` is broken by the same programs for the same reason, which is why this shows up
in the semantic layer too: `Judge.defStmt`'s obligation
`SemJudge κ Γ I (.def' n ps body) .sym Γ I` is **false** — the run installs a method and
`declaresName κ n` need not hold.

**Two independent fixes, and they are worth separating.**

1. **The narrow one, for this bug.** Split the tables' two uses: keep `κ.defs`/`κ.classes` as
   the "already declared" tables the positive rules read, and give `Ctx` a **whole-program**
   declaration set for the negative ones. `Ctx.withBlocks` (`Validate.lean`) is the existing
   precedent — `κ.closures` is already seeded by a whole-program pre-pass for exactly this
   reason. Small, local, and it does not touch `Judge`'s signature.
2. **The architectural one.** `Judge` should thread `κ -> κ'` the way it already threads
   `Γ -> Γ'` and `I -> I'`, so a declaration is reported by the rule that types it rather than
   reconstructed from statement syntax by the sequence rule. See `Denote/Sem/notes.md`
   §The sixth stall point; that change also dissolves `JudgeSeq.cons`'s transport (L268) and
   makes the five declaration rules statable at all. It does **not** subsume fix 1: with κ
   threaded, `if c; def lambda; end; end` still has to decide what the *join* of a declaring
   and a non-declaring branch records, and the conservative answer for the negative uses is
   the union — i.e. fix 1's whole-program set, arrived at from the other side.

**The fix, as built (2026-09-09).** Fix 1, with `context-splitting.md`'s §4.5/§4.6 keying
landed at the same time — §10.1 argues the two have to arrive together or the seed is a
regression.

* `Neg` (`Ratchet/Judge.lean`) is a component of `Ctx` in its own right, seeded once by
  `Ctx.withBlocks` alongside the block table and never changed afterwards.
* `negEmit` walks **every expression position** — the point of the whole thing — carrying the
  lexical *cref* down, so `class C; def a; def b; end; end; end` puts `b` on `C`'s chain and a
  top-level `def` anywhere puts its name on `Object`'s. `negSeed` then closes that over both
  chains of §4.6 (`negInstHit`/`negClsHit`, the latter including the metaclass tail) and
  materialises the port grid.
* Every rule's negative premise now reads `Neg`: `nameFreeN` (declared nowhere in the program)
  where the receiver's type is not to hand, `portFree`/`tyFree` at a receiver port where it is.
  `Judge.bareName`'s `defDeclared? κ.defs m = none` and `clsToS`/`caseEqQuery`'s
  `smroGet? … = none` are gone: each was a **miss in a positive table**, which is a claim about
  that table's completeness, and completeness is exactly what a buried `def` breaks.
* The semantic components that carried the same defect moved with them —
  `MethodsExact`/`NameFreeOk`'s `declaresName κ n = true` escape and `BareNameFree`/`MissFree`'s
  antecedents are the one whole-program fact now, so `Denote/Rules/Lambda.lean`'s
  `nameFree_declaresName` (the lemma that used to relate the rule's premise to the component's
  escape) is a rewrite.

**Measured.** `context-splitting.md` §11's first open question — does the keyed-and-seeded `Neg`
hold the ladder? — answers **yes, exactly**: `run_ratchet.sh` 178/254 unmoved tier for tier,
`checkrungs` 177/177, `semladder` 47/83. The negative controls go **145 → 148**: all three F20
shapes (`x = (def lambda; …)`, `if true; def lambda; …; end`, `[def lambda; …]`) are now
refused, and `checkrungs` confirms the real semantics takes each of them to an uncaught
`NoMethodError`.

**What is not yet keyed.** `Judge.isAQuery`/`caseEqQuery`/`classOf`/`clsToS` ask `nameFreeN`
(whole-program, name-global) rather than `portFree` at the receiver's port, even though the
seed materialises the keyed fact and `tyPorts?` computes the port. The blocker is on the
*semantic* side, not the syntactic one: `QueryOk`/`ClsQueryOk` (`Denote/Sem/State.lean`) are
quantified over **class ids** with a name-global antecedent, so a keyed premise has nothing to
discharge them with. Keying them needs a "this `Port` denotes this class id" relation, which is
a `denM`-level change and belongs with the semantic layer rather than with the seed. Nothing on
the ladder turns on it today (the six programs §10.1 measured are tier 18/19, currently 0/8 and
0/3); it is the remaining half of §4.5.

### F21. `Pos` is not a growing *set* — `consts` overwrites, and `BaseChainsOk` is antitone in both

**Status:** **FIXED** 2026-09-10 — see the closing note. Never a soundness bug: it was a
blocker on a proof, and on a claim `context-splitting.md` §3 makes. **Severity:** medium (it was
what stopped `JudgeSeq.cons`). Found 2026-09-09 while building §8.1 steps 1–4 and then trying
step 5.

**The claim it falsifies.** `context-splitting.md` §3:

> | weaken an outgoing `P'` back to a smaller `P` | `P ⊆ P' → PosOk P' m → PosOk P m` | antitone, one line |

and §10.3's justification for it:

> our facts are keyed and **immutable-per-key**

**Two counterexamples, both inside `Pos`.**

1. **`consts` is keyed and *mutable* per key.** `extendConsts` is `envSet`, which **overwrites**.
   `X = 1; y = (X = "s")` makes `ConstsOk κ` — which still says `X : Integer` — false at the
   machine the statement left behind, so `StateOk (κ.afterStmt e τ) → StateOk κ` fails outright.
   A *qualified* binding is the second shape: adding `::Box::X` shadows `::X` for
   `constGet?` inside a method declared in `Box`, changing the answer without changing any key's
   value. §F18's `constAsgnOk` is exactly the premise that rules the first out — and it lives on
   the *syntactic* `Judge.casgn`, which is nothing a semantic obligation quantified over an
   arbitrary `SemJudge` premise can see.

2. **`BaseChainsOk` is antitone in `Pos`.** Three of its clauses are guarded by facts about the
   context — `coreConstFree κ`, `isANoOk κ.classes ch`, `(constGet? κ cn).isNone` — and every
   one fires on **fewer** inputs as the context grows. §3's table does not list it at all.

The rest of `Pos` really is free, and the reason is worth recording so the next attempt does not
re-derive it: `mergeCls` **prepends** the merged entry rather than replacing it in place, and
`extendDefs`/`addPrivNames` cons — so `classes`/`defs`/`privConsts` grow as *lists*, and
`ClassesOk`/`DefsOk`/`DeclClassOk`/`NestedClassesOk` weaken for nothing.

**What it costs.** `Obl.JudgeSeq.cons` needs the down-transport and cannot have it. The *up*
transport, which L268 recorded as the other half of the problem, is **gone**: step 1 moved
`NameFreeOk`/`BareNameFree`/`MissFree`/`MethodsExact` onto `Neg` (which `afterStmt` does not
touch, so they are invariant), and step 4's second conjunct states the grown-context conformance
instead of transporting to it. So this is the only thing left between the ladder and that rung.

**The fix (2026-09-10), and it is §2's own test applied twice more.** Three of the antitone
components are *negative* facts about the context — "no constant rebinds a core name", "no class
is declared below this base", "this name is not bound" — so by §2 they belong in `Neg`, seeded
whole-program the way `noMethod` is. `Neg` gained `wholeCls` and `boundConsts`; `isANoOk`/
`mixinFreeChain` read the first, `coreConstFreeN` and `BaseChainsOk`'s third clause the second.
`Ctx.afterStmt` does not touch `Neg`, so all three are now **invariant** and transport both ways.

Each is **strictly more conservative** — a bigger class table can only make
`mixinFreeChain`/`noDeclaredBelow` answer `false`, and not-bound-*ever* implies not-bound-*yet* —
so none can admit anything the per-point version refused. The *positive* half of narrowing still
reads `κ.classes`: a chain is broken by a class declared later just as much as by one declared
earlier, while a constant not yet assigned resolves nowhere and raises. **The ladder did not
move.**

What stayed is `Ratchet.ctxKept`, `JudgeSeq.cons`'s third premise: the constants clauses, and
`DeclClassOk`'s four guarded antecedents stated one-directionally. **All 178 hand derivations
discharge it by `rfl`**, `chkSeq` carries the matching guard so `chk_sound` still holds, and
what it refuses is a statement that rebinds a constant, shadows one through the cref, or reopens
a class the context already records in a way that moves its ancestor chain, its `new` or its
`initialize`. `Judge.casgn`'s `constAsgnOk` (§F18) already refused the first.

`Denote/Sem/Down.lean` is the transport; `Sem.JudgeSeq.cons` (`Denote/Rules/SeqCons.lean`) is
what it was for, and the semantic ratchet went **47 → 48 of 83**.

**One thing the earlier measurement got right and is worth keeping.** `noDeclaredBelow` answers
`false` when it cannot compute a chain — which it cannot for a class whose superclass is outside
the table (`class Uncomparable < StandardError`). That was fatal while the guard had to be
*preserved* across a declaration; with the guard invariant it is only a precision question.
Sharpening it would be a loosening of §F9's guard and wants its own measurement.

### F22. `constAsgnOk`'s guard list is not the set of class names a `Ty` can carry — and `Regexp` is outside it

**Status:** **open, and not a soundness bug** — a blocker on `Obl.Judge.casgn`, filed so the
next attempt does not re-derive it. **Severity:** low as a wrong answer (there is none, and
§Why it is not reachable says why), medium as a proof obstruction: it is the *third* independent
reason `Judge.casgn`'s obligation is false, and unlike the other two it is not about where the
machine is standing. Found 2026-09-10 while sizing `casgn` against the seventeenth stall point.

**The measurement.** `constAsgnOk κ n τ` (§F18's guard) refuses a rebinding only when the name
is one the *tables* describe — a recorded constant at a different type, a declared class, a
`builtinClsNames` entry, or an `excName?`. Measured at `ctx0`
(`lake env lean` on `#eval constAsgnOk ctx0 …`):

```
constAsgnOk ctx0 "Regexp" (.cls "String")  =  true    -- permitted
constAsgnOk ctx0 "Comparable" .int         =  true    -- permitted
constAsgnOk ctx0 "Range" .int              =  true    -- permitted
constAsgnOk ctx0 "String" (.cls "String")  =  false   -- refused (builtinClsNames)
constAsgnOk ctx0 "StandardError" .int      =  false   -- refused (excName?)
```

`builtinClsNames` is nine names (`Integer Float String Symbol NilClass TrueClass FalseClass
Array Hash`). **`Regexp` is not one of them, and `Judge.regexpLit` concludes `.cls "Regexp"`.**

**Why the obligation is false.** `denM (.cls n) m v` is `isAName m.heap v n`, which resolves
`n` through `classNamed?` → `constLookup` → the toplevel constant table (`Denote/Val.lean`).
So take

```
Γ = [("r", .cls "Regexp")]      and      Regexp = "s"
```

at any machine where `r` holds a Regexp instance. The machine is conformant with `(κ, Γ, I)`;
the run returns; and at `m'` the name `Regexp` resolves to a **String object**, whose
`classPayload?` is `none`, so `classNamed? m'.heap "Regexp" = none` and `isAName … = false`.
`EnvOk Γ m'` fails, hence `StateOk κ Γ' I' m'` — the conjunct §12.3 of `context-splitting.md`
keeps for the rule's *consumer* — is false. Nothing in the rule's premises can exclude it.

**Why it is not reachable**, which was checked rather than assumed. The other producers of a
nominal `Ty` are all inside the guard: `constCls` requires `clsGet? κ.classes n = some c`
(refused), `constBuiltin` requires `BuiltinCls n` (refused), `constExc` requires `excName?`
(refused), and `rescueBind?`'s `.cls n` is an exception class (refused). That leaves `Regexp`,
and rebinding the *constant* `Regexp` is behaviourally inert: no `PrimSig` row has a `Regexp`
receiver, `/x/` is a literal that consults no constant, and `"a".match?(r)` dispatches on the
**object** `r` still holds. So the type goes stale while the program keeps working — the
opposite polarity from §F10, where the stale name made the checker *wrong*.

**The shape, stated for the next fix.** This is §F10's pattern (*a constant is not its name*)
read from the assignment side rather than the read side: a `casgn` can falsify any type that
mentions the name, and the set of names a `Ty` can mention is not the set of names the
context's tables record. Two candidate repairs, neither a one-liner and neither in this
window's edit surface:

1. **Widen the guard** to "the name currently names no class at all". That is a fact about the
   *machine*, not about `κ`, so as a `Judge` premise it would have to be approximated — the
   honest approximation is a fixed list of every nominal name the `Ty` grammar and the
   `PrimSig` table can produce, which is `builtinClsNames ∪ {Regexp} ∪ excNames`. Cheap, and it
   moves `Ratchet/`.
2. **Make the nominal arms identity-based rather than name-based.** `denM (.cls n)` would carry
   the class *object* the name resolved to when the type was made, which is what `Ty.inst`'s
   `isExactInst` already half-does (§F12). That is a `denM` change with a blast radius through
   `DenB`, `Examples.lean` and every nominal rung.

Recorded here rather than fixed because `Judge.casgn` is blocked by the seventeenth stall point
as well (`ConstScopeOk` is falsified by a class body's first constant), and that one needs `Ctx`
to record the cref. Fixing this alone moves no rung.


## §F23 — **a `next` escapes mid-body, and both loop rules check the environment at the end** *(reachable; FIXED)*

**Found by reading `Judge.while'`'s semantic obligation** rather than by search, which is what
the semantic ratchet is for: the rule's premises are `Γc = Γ` and `Γb = Γ` — claims about the
condition's and the body's **outgoing** environments — and a `next` leaves the iteration *in the
middle*, at an environment neither premise mentions.

```ruby
i = 0
x = 1
while i < 2
  i = i + 1
  x = "s"
  next if i == 2      # leaves with x : String
  x = 2               # ...which is why Γb = Γ holds anyway
end
x + 1                 # CRuby: TypeError. `validate` said Integer.
```

**Reachable**: `validate` certified it (`corpus/…-while-next-escapes-unsafe`, added), and CRuby
raises `TypeError: no implicit conversion of Integer into String`. The Lean model agrees
(corpus agreement 256/256).

**The same hole one rule over**, because `Judge.iterBlock`'s `capIntact` is read at the block
body's outgoing environment too:

```ruby
s = 0
[1, 2].each do |y|
  s = "a"
  next if y == 2
  s = 1
end
s + 1                 # CRuby: TypeError. `validate` said Integer.
```

(`corpus/…-iter-block-next-escapes-unsafe`.)

**The fix** is the conservative one the shape allows: a new premise `nxtPrefixOk body = true` on
both rules — *a `next` may only occur before anything has assigned*. Then the environment at the
escape **is** the body's incoming one, which is exactly what the outgoing premise already pins.
It keeps every climbed rung (`ctl-next`'s `next if x == 2` is its body's first statement) and
rejects both witnesses. Corpus: **178 of 256**, mismatches unchanged at 35, `checkrungs`
177/177 + 148/148.

Three notes on the fix, because each was a decision:

* **`asgnFree`, not `noLocalAsgn`.** The first version used the existing `noLocalAsgn`, which is a
  *whitelist of narrowing-condition shapes* and answers `false` for `next` itself — so it rejected
  `ctl-next`, a climbed rung. `asgnFree` asks the honest question (is there a `vasgn`, a `for`
  target, or a block body that writes a captured local anywhere in here) and keeps it.
* **An `autoParam` (`:= by rfl`)**, so the 27 hand derivations that predate the premise discharge
  it the way they would have written it, without being re-edited — and a derivation whose body
  *does* `next` after an assignment fails to elaborate, which is the point.
* **`Ratchet/Proof/ChkSound.lean` paid two lines**: the `while'` and `iterBlock` arms now destructure
  one more conjunct out of `validate`'s guard. That is the whole ripple of a `Judge` premise, and
  it is worth knowing it is two lines and not a clink.

**Known limitation, inherited not introduced**: `asgnFree` is syntactic, so a `next` after a call
to a closure that assigns a captured local is still accepted — §F13's hole, the fifteenth stall
point's, unchanged here.


## §F24 — the same shape at `break`, **checked and not a bug** *(negative result, pinned)*

> **The control was run, which is what makes this a result rather than an absence.** The two
> witnesses with the `break` *removed* (`[1,2].each { |y| s = "a"; s = 1 }; s + 1` and the `while`
> twin) both validate **true**, so the rejection below is caused by the `break` specifically and
> not by the shape being unsupported. Contrast §F25, where the control fails too.

§F23's reasoning applies verbatim to `break`: it leaves the *loop* (or, in a block, the *call*)
where `next` leaves the iteration, and `Judge.while'`'s `Γb = Γ` / `Judge.iterBlock`'s `capIntact`
are read at the body's end just the same. Both witnesses were written and run —

```ruby
i = 0; x = 1
while i < 2
  i = i + 1; x = "s"
  break if i == 2
  x = 2
end
x + 1                            # CRuby: TypeError

s = 0
[1, 2].each { |y| s = "a"; break if y == 1; s = 1 }
s + 1                            # CRuby: TypeError
```

— and **`validate` rejects both already**, because it has no rule that types a `break` in either
position (`ctl-break` is an unclimbed rung). So this is a *negative* finding, and the two programs
are on file as corpus rungs (`while-break-escapes-unsafe`, `iter-block-break-escapes-unsafe`,
tier 16, `unsafe_program`) for one reason: **they are the regression pin for the day a `break`
rule is written.** The `nxtPrefixOk` premise §F23 added says nothing about `.brk`, so that rule
will need the same treatment, and these two rungs will say so.


## §F25 — and the same question at `raise`, which the checker **cannot answer yet** *(open, pinned)*

`begin`'s body leaves in the middle too: a raise hands control to the handler at the environment
the *raise point* left, not the one the body's last statement would have. So the §F23 pattern has
a third door in principle —

```ruby
x = 1
begin
  x = "s"
  raise "boom"
  x = 2
rescue
  nil
end
x + 1                            # CRuby: TypeError
```

— and `validate` rejects it. **But the negative is vacuous**, and saying so is the finding: the
**raise-free control** (the same program with `raise "boom"` deleted) is rejected too, so what is
being refused is `begin`/`rescue` itself, not the escape. `ctl-begin-rescue-else-ensure` is an
unclimbed rung and `Judge.begin'` is undischarged on the semantic ladder.

On file as `corpus/…-begin-rescue-midway-escapes-unsafe` for the same reason as §F24's pair: it is
the pin for the day `Judge.begin'` is written, and `nxtPrefixOk` says nothing about a raise.
**Method note**: the control is what separates §F24 (a real negative — its controls validate
`true`) from this one (an absence). Running it costs one `#eval` and it is the difference between
"checked" and "assumed".


## §F26 — how strict `Judge.while'` actually is, measured; and one **pure over-strictness** in it *(open, actionable)*

Prompted by the question "are ordinary imperative loop patterns allowed?". Measured rather
than read off the premises: 42 programs through three checkers — `validate` (via a scratch
corpus and `.lake/build/bin/ratchet`), **CRuby 4.0.5** for ground truth, and **`sorbet`
0.6.13405** at `# typed: true` for comparison. Reproduce with

```sh
python3 probes/loop_strictness.py     # 24 loop shapes, three columns
python3 probes/loop_controls.py       # the same bodies with the loop removed
python3 probes/loop_more.py           # other loop heads, assigning/compound conditions
python3 probes/loop_workarounds.py    # the same rejections with the locals hoisted
```

### The rule, in one line

`Judge.while'` requires `Γc = Γ`, `Ic = I`, `Γb = Γ`, `Ib = I` — **the condition and the body
must each leave the local environment exactly as they found it** — plus `nxtPrefixOk body`
(§F23). That is a fixed point by equality, not by joining, and everything below follows from
it.

### What passes **[V]**

Counters in every direction, which was the question asked: `i = i + 1`, `i = i - 1`, `i -= 1`,
`i = i - 2`, `until i <= 0`, accumulation into a second local (`n = n + i`, `s = s + "a"`), a
branching body whose arms both advance the counter, a body that calls a user-defined method,
`while true; end` (diverges, safe by prefix-closure), and a body that *retypes* a local and
restores it before the end.

### What is rejected, and why — three different reasons, only one of them the loop rule **[V]**

The straight-line controls are what separate them.

| rejected | control (loop removed) | cause |
|---|---|---|
| new local in the body (`y = i`) | **passes** | **the loop rule** — `Γb` gained `y` |
| nested loops (inner counter `j`) | **passes** | the loop rule, same fact (`j` is new) |
| a swap through a temp (`t = a; …`) | **passes** | the loop rule, same fact |
| `while (j = i) < 3` | — | the loop rule — `Γc` gained `j` |
| `while i < 3 && x > 0` | **passes** | the loop rule, **and it is a bug — see below** |
| `next` after the increment | (§F23's premise) | `nxtPrefixOk`, deliberately |
| `break if …` in a loop | fails too | **not the loop rule** — `Judge` has no `.brk` rule at all (`ctl-break` unclimbed, §F24) |
| float counter (`x = x + 0.5`) | fails too | not the loop rule — `Float#+`/`Float#<` have no `PrimSig` row |
| `a.push(i)`, `a = a + [i]` | fails too | not the loop rule — those sends are untyped straight-line as well |
| `dowhile`, `for i in 0..2`, `3.times`, `0.upto` | — | separate heads, unclimbed rungs |
| `x = nil` then `x = i` in the body | — | the loop rule; **and `srb` rejects it too** (7001) |

**Hoisting recovers every loop-rule rejection.** The same four programs with the body's new
locals pre-initialised before the loop — `y = 0`, `j = 0`, `t = 0`, `j = 0` — all validate
`true`. So the restriction is *"every local the loop touches must already be bound, at the
type the loop preserves"*, not *"no imperative loops"*.

### The bug: a compound loop condition is rejected by an artefact of desugaring **[V]**

`while i < 3 && x > 0` is rejected, and the cause is neither the loop nor `&&`. `&&` desugars
to a **synthetic temp assignment**:

```
["while", ["seq", ["vasgn","local","__dt_t1", i < 3],
                  ["if", ["var","local","__dt_t1"], x > 0, ["var","local","__dt_t1"]]], …]
```

so the *condition* binds a new local and `Γc = Γ` fails. Two controls pin it: the same `&&`
outside a loop validates `true`, and the same loop with `__dt_t1 = false` hoisted by hand
**validates `true`** (`probes/loop_workarounds.py`, `hoist-dt-temp`). The temp is dead after
the condition, so there is no soundness content here at all — this is pure over-strictness,
and it rules out a very large fraction of real `while` conditions.

Two candidate fixes, not yet decided: weaken `Γc = Γ` to "agrees on every name the loop's
body or continuation can read" (a liveness condition, which is what the premise is trying to
approximate), or let the premise quotient by the desugarer's `__dt_*` namespace (cheaper,
narrower, and leaves the general case standing). The same weakening would admit the body
cases too, at which point the hoisting workaround stops being needed.

### How Sorbet handles `while` **[V]**

**The same restriction, by the same name.** `sorbet` 0.6.13405 answers the widening cases
with error **7001, "Changing the type of a variable is not permitted in loops and blocks"**,
and autocorrects by asking for the loop-invariant type up front:

```
probe.rb:5: Changing the type of a variable is not permitted in loops and blocks https://srb.help/7001
  Existing variable has type: `NilClass`
  Attempting to change type to: `Integer(0)`
  Autocorrect: Replace with `T.let(nil, T.nilable(Integer))`
```

So `Judge.while'`'s `Γb = Γ` is not an eccentricity of this checker; it is Sorbet's rule for
loops, arrived at independently, and Sorbet's `T.let` is the ascription this checker has no
syntax for. Where the two differ:

* **Sorbet is more permissive** on new locals and nested loops (a local introduced in the
  body is fine, because Sorbet joins at the loop header where 7001 only fires on a *changed*
  type), and on compound conditions (it does not desugar `&&` into an assignment).
* **Sorbet is more permissive on the `while (x = …)` idiom**, for the same reason.
* **Sorbet is *less* permissive** on retype-and-restore (`x = "s"; x = 2` inside the body is
  7001; `validate` accepts it, soundly, because `nxtPrefixOk` bans a `next` in between and
  there is no `.brk` rule) and on a body that calls an unannotated method (`i = f(i)` is
  7001 because `f` returns `T.untyped`; `validate` accepts it by typing `f`'s body).
* On `while true; end` both say the program is fine; on `if`-bodies Sorbet adds **7006
  "This code is unreachable"**, which `difftest/checker_relation.py` already excludes as a
  reachability opinion rather than a type one.

**Method note**: the three-column table is the point. `validate=false` on its own cannot
distinguish "the loop rule refused this" from "this rung is not climbed yet", and eleven of
the twenty-four round-one rejections turned out to be the latter.

