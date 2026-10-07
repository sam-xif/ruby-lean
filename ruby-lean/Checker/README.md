# Checker/ — the type checker

A type checker for a fragment of Sorbet-annotated Ruby. Its entry point is

```lean
def validateD (p : Expr) (d : Deriv) : Bool
```

`p` is a program and `d` is a proposed typing derivation, an untrusted hint.
[`bin/ruby-lean-check`](../../docs/guides/prove-type-safety.md) runs it on a
Ruby file.

The theorem that gives `true` its meaning, `validateD_safe_run`, is in
[`books/Books/TypeSoundness/`](../../books/Books/TypeSoundness/README.md):
a program `validateD` accepts never ends in an uncaught `NoMethodError`,
`ArgumentError` or `TypeError` when the model runs it.

## Isolated from the model

Nothing under `Checker/` imports `RubyCore/`. The checker has its own copy of
the syntax and the types, so it can be read, audited and re-implemented without
the model in scope. The two libraries share a Lake package, so the compiler
does not enforce this; [`../scripts/check-isolation.sh`](../scripts/check-isolation.sh)
does, and `make soundness` runs it first.

## Layout

| Directory | Contents |
|---|---|
| `Lang/` | The copied language: `Expr`, `Ty`, JSON decoding |
| `Static/` | The tables, contexts and predicates that the typing rules are stated over |
| `Judgment/` | The typing rules, as inductive judgments: `DJudge` and its companions |
| `Guards/` | The decidable side conditions the rules use |
| `Check/` | The executable checker: `Deriv` and `validateD` |
| `Audit/` | Generated from `Check/` by `../scripts/generate_audited_checker.py`: the same checker, also returning which rules a derivation used. Do not edit |
| `Controls/` | Derivations the checker must refuse. Built with everything else, so a control that stops holding fails the build |
| `ClinkPolicy.lean` | The list of enabled typing rules. `validateD` refuses a derivation that uses any other |

A typing rule says nothing here about why it is sound. That is a proof about the
model's `stepFn`, and it lives with the other proofs in `books/`.
[Adding a typing rule](../../docs/contributing.md#adding-a-typing-rule) describes
the steps.
