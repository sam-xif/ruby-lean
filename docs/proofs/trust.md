# What you have to trust

A theorem here is a statement about the model. This page lists what stands
between such a theorem and a statement about a Ruby program running under CRuby.

## Trusted

**Lean's kernel and its three standard axioms.** Every headline theorem depends
on `propext`, `Classical.choice` and `Quot.sound` only. `make comparator`
re-checks the soundness theorem's whole dependency closure in a fresh kernel.

**The statement of the theorem.** A proof is only as useful as what it proves.
The soundness theorems are restated on their own, with no proofs, in
`books/Comparator/Challenge.lean`, and the comparator checks that what was
proved is exactly that. Reviewing the claim means reading that file and the
definitions it mentions: `validateD`, the model's `run`, and `typeStuck`.

**The model is Ruby.** This is the large one, and it is established by testing,
not proof. Every build runs the model and CRuby side by side on about 1300
programs from CRuby's own test suite and on the typed corpus, and fails on any
difference. Randomly generated and adversarial programs are also compared.
[How the model is tested](../testing.md) describes this. It gives strong
evidence that the model agrees with CRuby 4.0.5 on the Ruby it supports. It does
not prove it.

**The desugarer.** The model runs a core language, and `desugar/` translates
Ruby into it. The desugarer is tested on its own, by translating each program
back to Ruby and checking that CRuby behaves the same on both. A theorem about a
program is about its desugared form.

## Not trusted

For the type-soundness result, these can be wrong without making the result
wrong. A mistake in any of them can make the checker decline a program. It
cannot make the checker accept one, because `validateD` checks the derivation it
is handed and the theorem is about `validateD`'s answer.

* **Sorbet.** It is used to read the signatures. The checker does not rely on
  Sorbet's verdict about the program.
* **The annotation stripper** (`difftest/ruby/*_strip.rb`).
* **The derivation emitter** (`ruby-lean/scripts/emit_deriv.rb`), the script
  that proposes a typing derivation.

One caveat follows from the list above. The checker reads types from the
signatures Sorbet reports, and the program it checks is the stripped and
desugared one. The theorem is about that program.

## What the results do not say

* **Termination.** Type soundness holds for any number of steps and says nothing
  about whether the run ends.
* **Other exceptions.** An accepted program can still raise `ZeroDivisionError`,
  or any exception other than the three classes named.
* **Programs outside the model.** When the model declines a program, no theorem
  applies to it.
* **Other Ruby versions and implementations.** The reference is CRuby 4.0.5.
* **Resource limits.** The model has unbounded integers and no stack limit, so
  it never raises `SystemStackError` or `NoMemoryError`.
