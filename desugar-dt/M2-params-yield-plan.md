# M2 (params + yield) — next-batch plan & hand-off note

> Written so a fresh-context session can pick up M2 without re-deriving anything. M1 + the
> splat batch + M3 (object-model core) are done; this is the next fragment-expansion batch,
> and the `bin/coverage --full` histogram now points squarely at it. Read
> `fragment-expansion-strategy.md` for the overall plan and `implementation-choices.md`
> (C12–C20) for the decisions so far. The M3 plan (`M3-classes-plan.md`) is the template
> this note imitates and is now largely realized.

## Where things stand (resume point)

- **Branch:** `sam-xif-investigation`. **Oracle:** CRuby 4.0.5 via `$(brew --prefix ruby)/bin/ruby`.
- **Harness:** `sam-xif/ruby/desugar-dt/`. Run: `RUBY=$(brew --prefix ruby)/bin/ruby`,
  then `$RUBY bin/run` (round-trip over `corpus/`), `$RUBY bin/coverage` (fragment % +
  first-blocker histogram + ratchet; `--full` = per-program next-blocker profile),
  `$RUBY bin/desugar FILE` (inspect one program).
- **Ratchet baseline:** **752/1299** bootstraptest in-fragment, **0 disagree, 0 harness-error**,
  rule coverage 46/46.
- **Discipline (C12):** a new RubyCore head is a red flag *unless* the construct is an
  irreducible primitive. Parameter binding and `yield` are part of the object-model/control
  core (category d) — so the heads/representation below are **justified**, not a red flag.

## What M2 covers & why it's next

Fresh `bin/coverage --full` per-program blocker profile (top, after M3):

```
106  optional_parameter_node
 95  block_parameter_node
 73  yield_node
 62  keyword_hash_node          (keyword args at a call site: foo(a: 1))
 41  constant_path_node         (A::B — deferred to its own batch)
 38  defined_node
 31  forwarding_parameter_node  (def f(...) — defer)
 30  when_node / case_node
 24  optional_keyword_parameter_node
 15  required_keyword_parameter_node
  …  keyword_rest_parameter_node, block_argument_node
```

Admitting M3's classes exposed the *method bodies* inside them, so parameters and `yield`
now dominate. These interlock (a block param `&blk` is what `yield`/`block.call` consume;
keyword *call args* bind to keyword *params*), so treat them as one batch — but land it in
two commits (see Process) to keep the ratchet attributable.

## The central design decision: params must become a structured list

**Today** `def`/`defs`/`block` store parameters as a **flat list of Strings** (C17): required
params are plain names; a rest param is the verbatim string `"*b"` (or `"*"`); everything
else (`optionals`, `keywords`, `keyword_rest`, `block`) is **rejected** in `param_names`
(`lib/desugar.rb`) with a clean `Unsupported`. That flat-string trick cannot carry M2:

- An **optional default** (`b = 1 + 2`) is an arbitrary **expression** with real semantics —
  evaluated *in the callee's scope, at call time, only when the arg is omitted, left-to-right,
  and it may reference earlier params* (`def f(a, b = a + 1)`). A string can't hold that.
- **Keyword params** and **block params** are likewise not expressible as bare names.

**So change the parameter slot of `def`/`defs`/`block` from `[String]` to a list of param
nodes.** This is *not* a new top-level head — it extends the parameter structure of the
existing object-model primitives (C12 category d), so it is justified. Proposed param nodes
(pick final spellings during implementation, record as C21):

| Param node | Surface | Renders to |
|------------|---------|-----------|
| `[:preq, name]` | `a` | `a` |
| `[:popt, name, default_expr]` | `a = E` | `a = (E)` |
| `[:prest, name_or_nil]` | `*a` / `*` | `*a` / `*` |
| `[:pkey, name, default_or_nil]` | `a:` (required) / `a: E` | `a:` / `a: (E)` |
| `[:pkwrest, name_or_nil]` | `**o` / `**` | `**o` / `**` |
| `[:pblock, name]` | `&blk` | `&blk` |

Post-rest requireds (`a, *b, c`) are just more `:preq` after `:prest`. **Migration note:** the
existing rest-as-`"*b"`-string and plain-name conventions must be replaced everywhere they
are consumed — `param_names` (build), `render.rb` `def`/`block`/`defs`/`super` param join,
`rubycore.rb` `is_core?` (the `params.all? { String }` checks), and `linearize.rb` (which
currently passes `node[2]`/param lists through untouched — a `:popt` default is an **operand
position** and can contain a jump, so linearize must recurse into defaults). Keep a single
`render_params` helper so all four sites agree.

## yield — a new head (irreducible)

`yield` invokes the block passed to the enclosing method; there is no send it reduces to
faithfully (it is not `block.call` — there may be no reified block object, and `yield`
raises `LocalJumpError` with different semantics). Add head **`[:yield, [args]]`**; Prism
`yield_node` has `arguments` (nil ⇒ `[]`). Renders `yield(args...)`. Splat in yield args
reuses `arg_node` → `[:splat, …]`.

## Keyword args at a call site — the Ruby-3 separation trap (like "don't rewrite class to Class.new")

`foo(a: 1, b: 2)` parses as a trailing `keyword_hash_node` in the call's arguments. **Do NOT
desugar it to a positional hash `foo({a: 1})`.** Since Ruby 3.0 keyword and positional-hash
arguments are *separated*: `foo({a: 1})` binds to a positional param, `foo(a: 1)` binds to
keyword params — they are not interchangeable and dispatch differently. So keywords at a
call site need a faithful marker in the arg list (e.g. `[:kwargs, [[k, v], …]]`, rendered
back as `k: v, …`) that pairs with `:pkey`/`:pkwrest`. **`block_argument_node`** (`foo(&blk)`)
likewise needs an arg marker (e.g. `[:blockpass, expr]`, render `&(expr)`), pairing with
`:pblock`. Both are irreducible-ish and belong with this batch.

## Semantics to verify against the oracle (write [V] snippets / adversarial seeds)

The eval-order corners most likely to produce round-trip disagreements — cover each with a
seed, and an **eval-order (`print`-trace) adversarial seed** where there is an ordering /
once-only obligation:

- **Optional defaults evaluate lazily, left-to-right, only for omitted args, at call time.**
  `def f(a, b = (print("b;"); a + 1), c = (print("c;"); 0)); …; end` — calling `f(1, 9)` must
  print only `c;` (b supplied, c defaulted); `f(1)` prints `b;c;`. A naive desugaring that
  evaluates all defaults, or evaluates them once at def time, or in the wrong scope, diverges.
- **A later default may reference an earlier param** (`b = a + 1`) — scope must be the callee.
- **Keyword vs positional-hash separation** (Ruby 3): `def f(h); h; end` vs `def g(a:); a; end`
  — `f(x: 1)` must be an ArgumentError (or bind the hash) exactly as CRuby does; `g(x: 1)`
  binds. Verify both directions so the `:kwargs` marker is faithful.
- **`yield`** with/without args, and `yield` when no block is passed (`LocalJumpError`) —
  `obs` compares `[class, message]`.
- **Block param `&blk`** reifies the block into a Proc; `f { … }` vs `f(&p)` should bind the
  same. Verify `blk.call` / re-`yield` see the same block.
- **`**kwrest`** collects leftover keywords; **`*rest` + kw** interaction.

## Deferred within / alongside M2 (enumerate, don't silently skip)

- **Argument forwarding `...`** (`forwarding_parameter_node` / `forwarding_arguments_node`,
  31/27) and `numbered_parameters_node` (`_1`), `implicit_rest_node` (`a, = x`) — their own
  step.
- **`case`/`when`** (30) and **`defined?`** (38) — the next batch after this (call it M4);
  `defined?` also unblocks the deferred `const ||=` / `@@x ||=` from C14.
- **Constant paths `A::B`** (41) — deferred since M3 (distinct lexical-nesting primitive).
- **do-while** (`begin…end while`), single-RHS massign (`to_ary`), indexed/attr **op**-assign
  — still deferred (see C14/C19).

## Prism shapes (verified 2026-07-03 against CRuby 4.0.5)

- `ParametersNode`: `.requireds` `.optionals` `.rest` `.posts` `.keywords` `.keyword_rest`
  `.block`. An `OptionalParameterNode` has `.name` (Symbol) + `.value` (the default, a node).
  Keywords are `RequiredKeywordParameterNode` (name, **no** value) or
  `OptionalKeywordParameterNode` (name + `.value`). `KeywordRestParameterNode` `.name`
  (may be nil for bare `**`). `BlockParameterNode` `.name`.
- `yield_node`: `.arguments` (an `ArgumentsNode` or nil).
- Call site: `foo(1, a: 2)` → arguments `[integer_node, keyword_hash_node]`; the
  `keyword_hash_node` has `.elements` of `assoc_node` (reuse hash handling). `foo(&blk)` →
  `.block` is a `block_argument_node` (its `.expression` is the passed proc), NOT `.arguments`.

## Process (per `PROCEDURE-authoring-semantics.md` + `fragment-expansion-strategy.md` §6)

Land in **two commits** so the ratchet is attributable:

1. **Structured params + `yield`.** Do the representation migration (all four consumer sites
   + linearize recursion into `:popt` defaults) first with the fragment still restricted to
   *required + rest* params (behaviour-identical to today — round-trip stays green at 752),
   *then* admit `:popt`/`:pkey`/`:pkwrest`/`:pblock` and `[:yield]`. Add seeds incl. the
   lazy-default eval-order adversarial seed. Re-measure, ratchet up.
2. **Keyword call args + block-pass** (`[:kwargs]`, `[:blockpass]`), with the Ruby-3
   separation seed. Re-measure, ratchet up.

For each: classify → extend `rubycore.rb` (HEADS/`explain`), `render.rb`, `desugar.rb`
(+`Desugar::RULES`), `linearize.rb` → add a seed (+ eval-order adversarial seed) → keep
`bin/run` green (**0 disagree, 0 harness-error**) → `bin/coverage --save` to ratchet →
commit + an `implementation-choices.md` entry (next is **C21**), and **commit+push
`implementation-choices.md` as a checkpoint** (project request). Expect the harness to catch
bugs — it has every batch (interp `to_s`-vs-`String`, assignment-call value, massign
underflow); that is the point.

**Exit criterion (this batch):** optional/keyword/kwrest/block params, `yield`, keyword call
args, and block-pass admitted; the formerly-param/`yield`-blocked bootstraptest programs are
in-fragment **and agree**; ratchet climbs with 0 disagree/0 harness-error; deferred items
above are documented.
