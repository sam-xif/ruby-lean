# Lean model — export-v4 migration hand-off (get `--sut lean` green again)

> Fresh-context hand-off written 2026-07-15. Read `README.md` (layout/build),
> `HANDOFF.md` (model state before this — L0+L1+L2, **468/1304 agree, 0 disagree** on
> export **v3**), and `implementation-notes.md` (L1–L19) first. This doc is the single
> task: **migrate the Lean decoder + stepper from export v3 to v4** so the difftest SUT
> runs again. The desugar side is done — it now emits v4 (852→**1227/1299** bootstraptest
> in-fragment, 0 disagree; see `../harness/desugar-dt/implementation-choices.md` C25–C29).

## Why it's red

`../harness/desugar-dt/lib/export.rb` bumped `VERSION` 3→4. The Lean decoder
(`RubyCore/Syntax.lean`) hard-gates on v3, so **every** program now fails to decode:

```
RubyCore/Syntax.lean:205   unless v == some (.num 3) do   -- rejects v4 outright
```

Nothing about the *semantics* of the already-modeled fragment changed — the desugarer
produces byte-identical RubyCore for `send`/`block`/`yield`/`super`, classes/modules,
control flow, `begin`/`rescue`, and multi-RHS massign. This is purely an **interface +
new-forms** migration. Two things changed in the wire format:

### Change 1 — the parameter slot: flat `[String]` → structured param nodes (load-bearing)

v3 carried `def`/`defs`/`block`/lambda params as a flat list of sigil-prefixed strings:
required = `"a"`, rest = `"*a"` (or `"*"`), block-capture = `"&blk"` (or `"&"`). v4 carries
a list of **param nodes** (see `RubyCore::PARAM_HEADS` in `../harness/desugar-dt/lib/rubycore.rb`):

| v4 param node | surface | was in v3 |
|---|---|---|
| `["preq", "a"]` | `a` (incl. post-rest) | `"a"` |
| `["prest", "a"]` / `["prest", null]` | `*a` / `*` | `"*a"` / `"*"` |
| `["pblock", "b"]` / `["pblock", null]` | `&b` / `&` | `"&blk"` / `"&"` |
| `["popt", "a", <default-expr>]` | `a = E` | *(gated in v3)* |
| `["pkey", "k", <default-or-null>]` | `k: E` / `k:` | *(gated)* |
| `["pkwrest", "o"]` / `["pkwrest", null]` | `**o` / `**` | *(gated)* |
| `["pfwd"]` | `...` | *(gated)* |
| `["pdestr", [<sub-params>]]` | `(a, b)` | *(gated)* |

The three v3 kinds (`preq`/`prest`/`pblock`) are a pure **re-encoding** — same binding
semantics. The other five are genuinely **new binding semantics** the stepper does not have.

### Change 2 — new heads (decoder `fail`s on them today)

`RubyCore/Syntax.lean:197` errors on any unknown head. v4 adds:
`kwargs`, `cpath`, `cpath_asgn`, `defined`, `redo`, `undef`, `alias`, `for`, `dowhile`,
and the `fwd` arg marker. (`case`/`when`, regex, and interpolated symbols **desugar away**
— no new head — but their output uses sends like `Regexp.new`, `Array.try_convert`, `to_sym`,
and `Array#any?`-with-block; the model will gate those as `Unsupported` via `CRubyNames`
until modeled, which is fine — 0 disagree is preserved, coverage just doesn't grow there.)

## The plan (ordered; keep the ratchet: `--sut lean` tier0, 0 disagree, agreement only up)

### Phase 0 — decoder unblock via legacy lowering (fastest path to green; ~restores 468)

**Goal:** `--sut lean` runs again and re-attains roughly the old agreement, without any new
stepper semantics. Do this first as its own commit + `implementation-notes.md` entry (L20).

1. `RubyCore/Syntax.lean:205` — accept `v == some (.num 4)`.
2. Rewrite `params` (line 115) to decode the **param-node array**, then **lower the three
   already-modeled kinds back to the legacy `List String`** the stepper already consumes:
   `preq name → name`, `prest name → "*"++name` (null → `"*"`), `pblock name → "&"++name`
   (null → `"&"`). If a param list contains any of `popt`/`pkey`/`pkwrest`/`pfwd`/`pdestr`,
   **return a decode error** (→ the SUT reports `Unsupported`, out of fragment — same as v3
   gated them). This keeps `Expr.def'/block/defs` (Syntax.lean:42/50/62), `MethodDef.params`
   / `Closure.params` (Heap.lean:52/78), `parseParams` (Interp.lean:136), and the synthetic
   `["__recv", "*__rest"]` string-params (Interp.lean:225, Builtins.lean:571) **untouched**.
3. Add graceful gating for the **new heads not yet modeled**: either a catch-all that maps
   unknown-but-known-v4 heads to a decode error (→ Unsupported), or explicit no-op decode
   arms that produce an `Unsupported` sentinel. Verify a decode error surfaces as engine
   `Unsupported` (exit 3), **not** `MODEL-BUG` (exit 1) — check how `RubyCore/Obs.lean` /
   the binary maps `Decode.program`'s `Except String`.
4. Re-run `uv run python -m difftest run --tier 0 --sut lean`. Expect ~468 agree, **0
   disagree**. Re-baseline the ratchet. **Commit.** `--sut lean` is green again.

> Why lowering, not a full `Param` type, first: it is the minimal diff that restores the
> SUT, it can't regress semantics (identical binding for the three modeled kinds), and it
> gives a clean 0-disagree checkpoint before the real modeling work.

### Phase 1 — cheap new heads (decode + light semantics, each its own ratchet)

Order by effort. Each is heap-mutation or a small stepper rule (the project bet: prefer
heap mutation over new evaluation rules):

- **`dowhile`** — run `body` once, then `while cond`. Smallest; mirror the `while'` rule.
- **`undef` / `alias`** — method-table heap mutation on the current `defmod`
  (remove / copy a `MethodDef`). Reuse the class-payload method-list machinery in `Heap.lean`.
- **`cpath` / `cpath_asgn`** — relative/absolute constant lookup + assign on a base module
  (`A::B`); `base = null` is top-level. Reuses the const-resolution already used for `const`
  (artifact 03 §5); assign mutates the base class payload `consts`.
- **`for`** — the index **leaks** to the enclosing scope (not a block-local). Simplest
  faithful move: model as `coll.each` with the index assigned in the *enclosing* frame, or
  add a direct `for` rule. Verify the leak `[V]`.
- **`redo`** — restart the current loop iteration; needs a loop-frame re-entry target. Model
  alongside the existing `while`/`for` loop handling.

Gate (Unsupported) for now: **`defined`** (must inspect the syntactic arg *without*
evaluating — a real evaluator, do it deliberately), **`kwargs`** and **`fwd`** (pair with
keyword/forwarding params — do them in Phase 2).

### Phase 2 — native param-binding semantics (replaces the Phase-0 lowering; extends coverage)

This is the real modeling work and the only way past the desugar's biggest levers
(optional/keyword params dominate the histogram). Introduce a proper `Param` inductive
(mirror `PARAM_HEADS`) and thread `List Param` through `Expr.def'/block/defs`,
`MethodDef.params`, `Closure.params`, and the two synthetic builtin methods. Then extend the
method-entry (`Interp.lean` ~301) and closure-invoke (~233) binding, per kind, each its own
ratchet + adversarial seed:

- **`popt` optional defaults** — evaluate **lazily, left-to-right, in the callee frame, only
  for omitted args, at call time**; a later default may read an earlier param. This is the
  eval-order obligation `../harness/desugar-dt/corpus/seeds/31_param_defaults_eval_order.rb`
  pins on the desugar side — mirror it as a Lean check.
- **`pkey` / `pkwrest` keywords** — match keyword args by name, `ArgumentError` on a missing
  required keyword, collect leftovers into `**kwrest`; requires the call site to pass the
  `kwargs` marker through as a keyword mapping (Ruby-3 separation — a positional hash is
  **not** keywords). Pairs with decoding `kwargs` at the call site.
- **`pfwd` / `fwd`** — `...` forwards all positional + keyword + block args; needs a hidden
  forwarding bundle on the frame that `g(...)` re-expands.
- **`pdestr` destructuring** — `|(a, b)|` binds by array-destructuring the single arg
  (to_ary-or-wrap coercion, like a nested massign); can nest and hold a rest.

Adversarial parity seeds already exist on the desugar side (`30_params`, `31_*`, `32_kwargs`,
`40_destructuring`) — the model should agree with CRuby on all of them once each kind lands.

## Where to touch (file map)

| File | What |
|---|---|
| `RubyCore/Syntax.lean` | version gate (205), `params` decoder (115), `expr` head match (147–197), `Expr` def (30–68); Phase 2: new `Param` type + `def'`/`block`/`defs` fields |
| `RubyCore/Interp.lean` | `parseParams` (136) — the sigil-string splitter to replace; method entry (~301), closure invoke (~233), `reifyBlock` (~199); synthetic params (225) |
| `RubyCore/Heap.lean` | `MethodDef.params` (52), `Closure.params` (78) — `List String` → `List Param` in Phase 2 |
| `RubyCore/Builtins.lean` | synthetic `["__recv", "*__rest"]` params (571); Phase 1 will want `Array.try_convert`, `Regexp.new`, `Symbol#to_proc`/`to_sym`, `Array#any?`-with-block, `Kernel#String` if extending coverage past the desugar's new sends |
| `RubyCore/CRubyNames.lean` | the oracle name tables gate unmodeled builtins as Unsupported — regenerate (`scripts/gen_cruby_names.rb`) only if adding builtins |
| `RubyCore/Obs.lean` / binary | confirm `Decode.program` errors map to `Unsupported` (exit 3), not `MODEL-BUG` (exit 1) |

## Validation each step

```
cd ../harness/desugar-dt && $RUBY bin/export-json <FILE>   # inspect the v4 JSON the model sees
cd lean && lake build && python3 playground/server.py       # step through in the model
cd ../difftest && uv run python -m difftest run --tier 0 --sut lean   # ratchet: 0 disagree, agreement up
```

Invariant (unchanged from HANDOFF.md): **0 disagreements** at every commit; exit 3 =
Unsupported (out of fragment, fine), exit 1 = `MODEL-BUG:` (never silently absorbed).
Re-baseline the ratchet after Phase 0, then it only goes up.

## Definition of done

`--sut lean` green at ≥ the pre-v4 468 (Phase 0), then climbing through Phases 1–2 with 0
disagree. The desugar in-fragment set is 1227/1299; the model will trail it (builtins +
param kinds gate), but every non-gated program must agree.
