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

## Notes

- The `--trace N` step cap defaults to 4000 (server) / 3000 (binary) — a tight
  loop, or a long program without a window, stops at the cap with
  `status: step-cap`.
- Renderings (`Trace.lean`) are a *tooling* view, deliberately lossy and
  non-gating — not the Ruby-faithful `Obs.lean` observation the difftest uses.
  `--trace-at` matching the rendering rather than the machine is the same
  choice: a breakpoint that reads what you read cannot disagree with it.
- `POST /trace` still takes a bare source body; it also takes
  `{"source": …, "at": …, "from": …}`. `POST /steps` takes a bare source body.
