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

The stepper is the current model fragment (L0 + L1): literals, variables,
`def`/method calls, `if`/`while`, `begin/rescue/ensure`, arrays/hashes/strings,
and **blocks/procs/lambdas** — `yield`, `&blk`, `proc`/`lambda`/`->`,
`.call`, `next`/`break`/`return`. If a program leaves the fragment the trace
ends with `status: unsupported` and a reason (e.g. `Array#each` and other
yielding *builtins*, `class`/`super` (L2), optional/keyword params). A `done`
trace ends with the program's result; `uncaught` shows an escaping exception.

## Notes

- The `--trace N` step cap defaults to 4000 (server) / 3000 (binary) — a tight
  loop will stop at the cap with `status: step-cap`.
- Renderings (`Trace.lean`) are a *tooling* view, deliberately lossy and
  non-gating — not the Ruby-faithful `Obs.lean` observation the difftest uses.
