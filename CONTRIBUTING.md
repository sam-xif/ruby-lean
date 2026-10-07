# Contributing

**`make check` must pass before a change is merged.** It builds everything,
checks every proof and runs the model against CRuby; continuous integration runs
the same targets and each one blocks.

[`docs/contributing.md`](docs/contributing.md) explains what to run while
working, the two boundaries the design depends on, how recorded results are
updated, and how to add Ruby to the model, a typing rule to the checker, or a
proof about a program.
