# Type soundness

The book `books/Books/TypeSoundness/` is a type checker and the proof that its
answer means something. The checker, in the book's `Checker/` directory,
decides whether a Sorbet-annotated Ruby program is well typed. The rest of the
book proves what that guarantees when the model runs the program.

## The theorem

In `books/Books/TypeSoundness/Soundness.lean`:

```lean
theorem validateD_safe_run {p : Checker.Expr} {d : Deriv}
    (h : validateD p d = true) (hb : bootOkB = true) (fuel : Nat) :
    Semantics.typeStuck (Semantics.run fuel (toRuby p)) = false
```

If the executable checker `validateD` accepts program `p`, with any derivation
`d`, then running `p` on the model from the booted core library, for any number
of steps, never ends *type-stuck*: in an uncaught `NoMethodError`,
`ArgumentError` or `TypeError`, or a subclass of one.

* `validateD p d` is the function `bin/ruby-lean-check` calls. The hypothesis is
  the verdict of the code that runs, not a relation the code is separately
  claimed to implement.
* `d` is a typing derivation, an untrusted hint. The theorem holds for every
  `d`.
* `toRuby p` translates the checker's copy of the syntax to the model's.
* `bootOkB = true` says the booted machine satisfies the proof's invariant. It
  is a closed boolean that the build evaluates.

`validateD_safe` is the same statement from any machine that satisfies the
invariant, and `validateD_safe_boot` is the step between the two.

The theorem does not say that an accepted program terminates, and it does not
rule out other exceptions.

## Why the checker and the model are separate

The checker lives inside the book, in `Checker/`, but it imports nothing from
the model and nothing from the rest of the book. It has its own copy of the
syntax (`Checker/Lang/`). So the checker can be read, audited and re-implemented
without the model or the proof in scope, and the proof around it is the only
place that sees both. `books/scripts/check-isolation.sh` enforces the separation, and
`make soundness` runs it first.

| Directory in `Checker/` | Contents |
|---|---|
| `Lang/` | The copied language: `Expr`, `Ty`, JSON decoding |
| `Static/` | The tables, contexts and predicates the typing rules are stated over |
| `Judgment/` | The typing rules, as inductive judgments (`DJudge` and its companions) |
| `Guards/` | The decidable side conditions the rules use |
| `Check/` | The executable checker: `Deriv` and `validateD` |
| `Controls/` | Derivations the checker must refuse |

## How the proof is put together

The book's directories follow the argument.

1. **What a type means.** `Denotation/` defines, for each type of the checker,
   the set of runtime values it describes on a real heap.
2. **What it means for a machine to agree with the checker.** `Conformance/`
   defines `StateOk`: every local, instance variable, class and method table on
   the machine has the type the checker's context says. Most of the book shows
   that each kind of machine step preserves it.
3. **What a typing rule owes.** `Judgment/` states the semantic contract of a
   typing judgment, and `Rules/` proves, rule by rule, that each rule meets it.
4. **No rule without its proof.** `Registry/` pairs each rule with its proof.
   The checker refuses any derivation that uses a rule with no registered proof,
   and `Registry/AuditBridge.lean` turns an accepted derivation into a certified
   one.
5. **The theorem.** `Soundness.lean` composes these in about forty lines.

`Semantics/Interp.lean` is where the model's `stepFn` is imported and
`typeStuck` is defined. `Controls/` and `Examples/` test the above.

## The registry

A typing rule is written once, with the judgment abstracted. Instantiating it
one way gives the syntactic rule the checker uses; instantiating it the other
way gives a proof obligation over the real machine. The pairing is a structure
with the proof as a field, so a rule cannot be registered without it.

`books/Books/TypeSoundness/Checker/ClinkPolicy.lean` lists the rules that are enabled. A rule
that is not listed is refused by `validateD`, so the theorem never speaks about
it. All 131 rules are currently enabled and proved; `make soundness` prints the
count.

In the source, a rule together with its proof is called a *clink*.

## The corpus

`books/corpus/` holds 268 small Sorbet-annotated programs, each with a
`.meta.json` saying what Sorbet and the checker are expected to answer.
`make soundness` runs each through the whole pipeline and reports:

```text
model vs CRuby on the corpus: 259 agree, 0 disagree
typing rules with a soundness proof: 131/131
corpus programs accepted by validateD: 140/268
  must be rejected, and are: 46/46
  not accepted yet: 82
    096-block-pass-symbol-to-proc: emitter: map requires one positional block parameter and no arguments
    …
SOUNDNESS CHECK PASSED
```

| Line | Meaning |
|---|---|
| model vs CRuby | The model and CRuby agree on every corpus program the model runs |
| typing rules | How many of the checker's rules are registered with a proof |
| accepted | Programs for which the real `validateD` returned `true`. The theorem covers each |
| must be rejected | Ill-typed programs, such as `1 + true`. Accepting one is a failure |
| not accepted yet | Well-typed programs outside the fragment, each with the reason |

The set of accepted programs is recorded in `books/corpus/accepted.txt`, and the
run fails if it changes in either direction. When a change makes the checker
accept more, `books/scripts/check-soundness.sh --record` updates the file, and
the diff shows exactly which programs moved.

## Running it

```sh
make soundness                                  # everything
cd books
./scripts/check-soundness.sh --proofs-only      # no Ruby, Sorbet or CRuby needed
./scripts/check-soundness.sh --only 061,070     # only these corpus programs
./scripts/check-soundness.sh --verbose          # every stage's output, every program
```
