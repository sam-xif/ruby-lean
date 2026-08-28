# Ruby-in-Lean stepper playground

Write a Ruby program in the browser and step through its execution **in the
Lean model**, one `stepFn` transition at a time — watching the control state,
the call/block-frame stack with live locals, the continuation stack, and
accumulating stdout. **Run in CRuby ▶** executes the same source in real Ruby
so you can compare the model's stdout against the oracle's.

It's glue over pieces that already exist: the desugar harness and the Lean
`rubycore` binary. The only model addition is a `--trace` mode
(`lean/RubyCore/Trace.lean`) that emits every configuration as JSON instead of
just the final observation.

```
Ruby source ──▶ harness/desugar-dt/bin/export-json ──▶ RubyCore JSON
            ──▶ lean/.lake/build/bin/rubycore --trace ──▶ {steps, status, detail}
            ──▶ browser UI (prev / next / ← → )
```

The same first hop feeds three **static** queries, which execute nothing:

```
RubyCore JSON ──▶ rubycore --check        ──▶ decision / basis / verdict / type   (`infer`)
              ──▶ rubycore --fragment     ──▶ why an `uncertified` is uncertified
              ──▶ rubycore --assn         ──▶ one assertion per method body    (`inferOpen`)
              ──▶ rubycore --assn-program ──▶ one assertion for the whole program
                                                                            (`inferProgram`)
```

## Run

```sh
# 1. build the model once (from ruby/lean)
cd ../lean && lake build && cd -

# 2. start the playground (needs CRuby 4.0.5 on PATH or $RUBY / brew)
python3 server.py            # http://localhost:8077   (or: python3 server.py 9000)
```

No dependencies — Python stdlib `http.server` only. `server.py` finds Ruby via
`$RUBY`, then `brew --prefix ruby`, then `ruby`.

## What runs and what doesn't

**Whatever the model runs.** The stepper is a *printer* over `stepFn`, not a
second implementation, so it has never had a fragment of its own: everything the
model has gained since this page was first written — classes and `super`,
yielding builtins (`each`/`map`), the prelude's core library, regex, the
reflective metaprogramming core — steps here without the playground being
touched. (The list that used to be in this paragraph named `class`/`super` and
`Array#each` as *unsupported*; it was describing the model of July 2026, and it
was wrong by August.) If a program does leave the model's fragment the trace ends
with `status: unsupported` and the reason; `done` ends with the program's result,
`uncaught` with an escaping exception.

The prelude is booted **before** tracing starts, so a trace begins at the first
step of *your* program, not 300,000 steps into the core library.

## Stepping a big program

A whole-program trace is only viable for a toy. The Homebrew slice
(`homebrew/slice-driver/`, 2,151 lines) takes **825,259 steps**, and a snapshot
is about 1 KB — so "from step 0" is 4,000 steps of class-definition boot and
0.5% of the run, and a complete trace would be most of a gigabyte.

Three controls make it usable, all of them new in L126:

| control | in the UI | on the binary |
|---|---|---|
| how long is this program? | **count steps** | `rubycore --steps` |
| start the window at a step | **or step** `500000` | `rubycore --trace 4000 --trace-from 500000` |
| start it at the first interesting step | **start at** `send .compare(` | `rubycore --trace 4000 --trace-at "send .compare("` |

`start at` is the one to reach for: it matches a substring of the *rendered*
control (`send .compare(`, `eval class Version`, `then a = ▢`) and stops at the
first step that contains it, which is how you find a call whose step index you
could not have known. On the slice, `send .compare(` lands at step **50,765** —
inside `range_status`, sixteen frames deep, with `a = "0.9.9"` and `b = "1.0.0"`
in the top frame. The step counter then shows absolute indices, so two windows of
the same program cannot be mistaken for each other.

A breakpoint that never fires is not an error: the trace comes back with zero
steps and a status saying how the program ended instead.

## Typing it instead of running it

Two buttons under **Static types** ask the checker about the same source. Neither
executes anything, so neither boots the prelude and neither answer depends on
model coverage — a program the stepper cannot run can still be typed, and a
program that runs fine can still read `unknown`.

**Type-check (infer)** — `rubycore --check`, the nominal whole-program `infer`.
It prints `decision` (total: `accept` or `reject`), the `basis` underneath it
(`certified` · `refuted` · `uncertified`) and the inferred program type. The
distinction is the whole point of showing both: a `reject` on basis
`uncertified` says *the fragment escaped and this checker did not certify*, which
is not the same claim as `refuted` (*our rules refute this program*) and neither
is *the program fails*. `--fragment`'s list is printed in the same box, and it is
**context, not cause**: neither checker reads a Sorbet `sig` at all. `declsOf`
ignores the program (`declsOf _p := baseDecls`), so adding a full `sig` to a
method changes no verdict — a one-parameter `def` with a `sig` is
`in_fragment: true` and still `reject`/`uncertified`. What `infer` wants is a
*declaration*, and the only rule that makes one is the `def` arm's `addRow`,
which fires only for a **zero-parameter** `def` reopening a class in
`reopenableClasses` at `top = false`. So a call to a user-defined method is
`unknown` today whether or not it is typed.

**Per-body (inferOpen)** — `rubycore --assn`, the open front end, one verdict per
method body in the assertion language of `homebrew/assertion-language.md` §11.
This is the per-body gradient a whole-program verdict cannot show: a file reads
`unknown` under `--check` until the fragment covers all of it and then flips,
whereas here each body reports separately and an `unknown` **carries the atom it
wanted**.

```
Box#get  accept : α1
  requires: Box ⊒ ⟨ value : () → α1 ⟩
  and:      Box ⊒ ⟨ value : () → α1 ⟩

Box#twice  accept : α2
  params:   (n : α1)
  and:      α1 ~ + : (α1) → α2

Box#oops  unknown
  needed:   Integer ~ frobnicate : () → _

Box#h  unknown
  out of fragment: hash
```

**top level too** adds `--assn-top`'s `Object#<main>` row. `bodyReports` walks
into structure and reports `def`/`defs` only, so a program's straight-line code
has no open verdict without it — and that code is usually the part whose type a
reader thinks is obvious. It is off by default because `--assn`'s census is a
consumed number (`homebrew/fragment-gap.py`'s third ratchet) and a row that is
not a method body would move it.

**Whole program (inferProgram)** — `rubycore --assn-program`, L263/L264. The third
static query, and the difference from the other two is the point:

* against **`--check`**, it accepts programs whose `def`s and `class`es have *no
  declarations yet*, and answers what the types would have to be rather than
  whether they are already known;
* against **`--assn`**, the bodies share **one store**, so the requirement a
  `vcall` in one body records is cancelled by the `def` beside it. A per-body pass
  structurally cannot do that — it hands every body a fresh store at `{}`.

```ruby
class Version
  def value; 1; end
  def get; value; end
end
```

```
accept  types under these class obligations
  type    Symbol
  under   α3 = Integer
  class   Version — instance α2, class object α1
  consts  Version
```

`--check` says `reject / uncertified` on that same program. The obligation on
`Version` closed **empty** — the class answers its own body — so the assertion is
only the equality the cancellation owed.

Two things it is honest about. An `accept` is the **weakest** verdict the tool
prints (*types under these class obligations*, printed in `means`); only
`--check`'s `accept` is licensed by `check_sound`. And it is **all-or-nothing**
where `--assn` is a gradient: on a real slice file this reports the *first*
construct that stopped the program, which is why `--assn`'s per-body census stays
the ratchet and this stays the verdict.

Where it stops is worth knowing, because it is one gap and not a list. `inferOpen`
defers an unknown **receiver** — that is what open-self means — and cannot defer an
unknown **argument**:

```ruby
def f(n)  n + 1  end   # accept : α2  and: α1 ~ + : (Integer) → α2
def g(n)  1 + n  end   # unknown      needed: Integer ~ + : (α1) → _
```

`g` needs `α1 ≤ Integer`, an *upper bound on a variable*, which the assertion
language deliberately does not have (`Types/Assn.lean`'s header, §6.5's deferred
family). Everything else this program trips over is smaller: `Integer#to_s` and
`String.===` are missing table rows, and `Object#<main>` reads
`out of fragment: def` because `inferOpen` has no `def` arm.

The census line beside the buttons counts `accept` and `accept/open-params`
**apart**, and that is not cosmetic: an `accept` factors through a nominal
judgement at the empty environment, one substitution from the judgement `--check`
uses, while an open-params accept factors through a body-only judgement no `def`
rule exists for (`infer`'s `def` arm still requires `params.isEmpty`). Merging
them would report an accept rate the checker does not have.

## Tab 2 — the Homebrew slice explorer

The second tab drives the **slice** — `homebrew/PLAN.md` §2's eight files, from
the vendored `homebrew/vendor/brew` checkout — through the pipeline the ratchets
already run, one stage at a time and with the artifact between each pair of
stages visible:

```
load a file  ─┐
              ├─▶ [buffer] ─▶ strip ─▶ desugar ─┬─▶ rubycore          (Lean model)
link whole   ─┘                                 ├─▶ ruby              (CRuby oracle)
slice                                           ├─▶ rubycore --trace  (the step view)
                                                └─▶ jcert.rb ─▶ rubycore --certify-j
```

Nothing here is a second implementation; every button is the tool named on it.

| button | what runs |
|---|---|
| **Load file** | the file as vendored, unstripped |
| **Link whole slice** | `homebrew/slice-driver/build.py` — boot stubs + `linker` over the three entries (all eight files, 8 spliced, 0 cycles) + `driver.rb`. 2,159 lines |
| **Strip ▸** | `certify-file.sh`'s chain: `sig` · `visibility` · `freeze` · `require` · `const_inline` · `class_sugar` |
| **Desugar** | `harness/desugar-dt/bin/export-json`, printed as the s-expression |
| **Lean model ▶** | `rubycore` with no flags — the `Obs.lean` observation record (stdout, `result_repr`, uncaught), *not* the stepper's lossy rendering |
| **CRuby ▶** | the oracle. The **agree** pill compares stdout, which is what `slice-driver/run.sh` diffs |
| **Step it ▶** | the same `/trace` as tab 1, over this buffer, into the same step pane |
| **Derive (jcert)** | `certify/jcert.rb`, the untrusted emitter |
| **Validate ✓** | `rubycore --certify-j`, the trusted kernel `Bool` (`validateJ_certifies`) |

**The buffer is the input.** Loading or linking fills it, stripping rewrites it,
and every stage downstream reads whatever it currently holds — so an edit you
type is a first-class input rather than something the pipeline can ignore.

**Derive and validate are two buttons, not `certify-file.sh`'s one pipe.** That
script pipes the emitter into the kernel, so a failure is one word. Here the
certificate is an editable artifact between them: you can read it, change it,
and re-validate, and a `reject` is then a fact about *that JSON* — with the
`why` (`certificate-undecodable`, `certificate-unreadable`, a failed claim)
printed beside it. An accept says whether it was **unconditional**, because a
certificate that carries rows is an accept *relative to* those assumptions.

A `derive` failure names the blocking head (`jcert.rb` raises `JCert::Blocked`),
which is a coverage fact about `MFrag` and not a verdict on the program. The
linked whole-slice program blocks today on *implicit send outside a method
body*; the individual stripped files certify.

The **semantic steps** checkbox in the header hides the step pane and gives the
editor the whole window. It is a layout change only — the trace is kept, and
**Step it ▶** switches it back on.

## Notes

- The `--trace N` step cap defaults to 4000 (server) / 3000 (binary) — a tight
  loop, or a long program without a window, stops at the cap with
  `status: step-cap`.
- Renderings (`Trace.lean`) are a *tooling* view, deliberately lossy and
  non-gating — not the Ruby-faithful `Obs.lean` observation the difftest uses.
  `--trace-at` matching the rendering rather than the machine is the same
  choice: a breakpoint that reads what you read cannot disagree with it.
- `POST /trace` still takes a bare source body; it also takes
  `{"source": …, "at": …, "from": …}`. `POST /steps`, `POST /check`,
  `POST /assn` and `POST /assn-program` take a bare source body.
- The static panes are **printers over the checker's output, not second
  checkers** — the same rule `Trace.lean`'s renderings follow. The verdict text
  mirrors `Assn.explain`; nothing here decides anything, and a rendering that
  drifted would be a display bug rather than a soundness one.
- `--assn` and `--assn-program` report against the **prelude-aware** declaration
  table and `--check`
  against `declsOf prog`. That asymmetry is `Main.lean`'s and deliberate (two
  tables, each sound at the heap it describes), so the two panes can disagree
  about a name like `T` without either being wrong.
