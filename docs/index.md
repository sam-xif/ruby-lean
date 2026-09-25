# ruby-lean documentation

The component READMEs explain what each directory is and how to run it. These pages
hold the longer material: design decisions, testing methodology, and the details of
what the model supports.

Source comments cite some of these pages by number. *"artifact 05 §N"* is
[Testing methodology](testing/methodology.md) and *"artifact 06 §N"* is
[The round-trip method](front-end/method.md). *"artifacts 00–04"* and
*"RubyCore/README.md §…"* refer to the written semantics in
`ruby-lean/RubyCore/README.md`, which lives next to the code it describes.

## Pages

| Page | What it covers |
|---|---|
| [Reproducing the results](reproducing.md) | every command behind the numbers in the root README, and how to read the gate's output |
| **The model** | |
| [Layout and fragment](model/fragment.md) | the files in `RubyCore/`, what Ruby the model supports and what it declines, fidelity policies, regenerating generated files |
| [Metatheory](model/metatheory.md) | the inductive `Step` relation, adequacy, type safety as reachability, and the type checkers that were removed |
| **The front end (`desugar/`)** | |
| [The round-trip method](front-end/method.md) | artifact 06: how the desugarer is tested against CRuby before the model exists |
| [Growing the fragment](front-end/growing-the-fragment.md) | the measure, expand, re-measure loop and its rules |
| [Linearization](front-end/linearization.md) | why a jump in operand position needs a rewrite, and the rewrite |
| **Differential testing (`difftest/`)** | |
| [Testing methodology](testing/methodology.md) | artifact 05: the claims, prior art, observation, triage and metrics |
| [The difftest engine](testing/engine.md) | tiers, the comparison, the SUT interface, the Sorbet tier, invariants |
| **Tools** | |
| [The playground](playground.md) | how the browser UI works, running it with and without a server, its limits |

## Building this site

```sh
uvx --from 'mkdocs<2' --with mkdocs-material mkdocs serve    # http://127.0.0.1:8000, from the repo root
uvx --from 'mkdocs<2' --with mkdocs-material mkdocs build    # static site in site/
```
