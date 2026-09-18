# `Ratchet/` — the syntactic side

The certificate checker, and it is **isolated from the model on purpose**: nothing under
`Ratchet/` imports `RubyCore/`, `Semantics/` or `Denote/`, so it can be read, audited and
re-implemented without the 24k-line model in scope. That used to be a Lake package boundary;
since the merge it is [`scripts/check-isolation.sh`](../scripts/check-isolation.sh), which
[`scripts/run_typed_ratchet.sh`](../scripts/run_typed_ratchet.sh) runs first.

Six subdirectories, and the split is by *what kind of thing a file says*:

| directory | what a file here is | files |
|---|---|---|
| `Lang/` | the copied language — `Expr`, `Ty`, and the JSON plumbing. Copied *text*, not an import of `RubyCore/Syntax.lean`, which is the whole point of the isolation | 3 |
| `Static/` | the **static vocabulary**: the tables, contexts and predicates that both sides are stated over. Not a judgment; see [`Static/README.md`](Static/README.md) | 17 |
| `Judgment/` | the **syntactic judgments** — `DJudge` and its companions, `InitJudge`. Eight families, and nothing else lives here | 2 |
| `Guards/` | the decidable side conditions a rule's premises are written in: the native/class/subclass guards, the header publication guards, `WriteTypes`, the frame and route guards, the definition-site contexts | 16 |
| `Check/` | the **executable checker**: `Deriv` (untrusted hints), `validateD` and the checked-body/receiver caches, `Rung` | 7 |
| `Controls/` | negative controls — what the checker must *refuse*. Built by the gate as `Ratchet.Controls.DerivControls` | 9 |

## What is deliberately not here

**The semantic reading of any rule.** A `DJudge` constructor states a rule syntactically; what
it *owes* is a proof over the real machine, and that lives in [`../Denote/`](../Denote) — under
`Rules/`, registered as a `Clink`, which is the only way a rule enters the certified judgment.
The dependency runs one way and cannot be inverted: `Denote/` imports `Ratchet/`.

**Any claim about `stepFn`.** `Ratchet/` has never seen it. `Semantics/Interp.lean` is the one
file that imports it, and `Denote/` is the one library allowed to see both.
