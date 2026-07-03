# M3 (classes) — next-batch plan & hand-off note

> Written so a fresh-context session can pick up M3 without re-deriving anything. M1 +
> the splat batch are done; this is the next fragment-expansion batch (the projected big
> coverage jump). Read `fragment-expansion-strategy.md` for the overall plan and
> `implementation-choices.md` (C12–C17) for the decisions so far.

## Where things stand (resume point)

- **Branch:** `sam-xif-investigation`. **Oracle:** CRuby 4.0.5 via `$(brew --prefix ruby)/bin/ruby`.
- **Harness:** `sam-xif/ruby/harness/desugar-dt/`. Run: `RUBY=$(brew --prefix ruby)/bin/ruby`,
  then `$RUBY bin/run` (round-trip over `corpus/`), `$RUBY bin/coverage` (fragment % +
  blocker histogram + ratchet), `$RUBY bin/desugar FILE` (inspect one program).
- **Corpus:** `corpus/seeds/` (committed) + `corpus/bootstraptest/` (gitignored; regenerate
  with `bin/harvest_bootstraptest /path/to/ruby/bootstraptest` — sparse-clone recipe in
  that script's header).
- **Ratchet baseline:** **473/1299** bootstraptest in-fragment-and-agree, 0 disagreements.
- **Discipline (C12):** a new RubyCore head is a red flag *unless* the construct is an
  irreducible primitive. Classes/modules/singleton-classes/`begin`-rescue/singleton-defs
  fall in C12 category (d) "object-model/control core" — so heads for them are **justified
  and expected**, not a red flag. Prefer desugaring only for things that truly are sugar
  (see §3).

## What M3 covers & why it's the big unlock

Top remaining blockers (from `bin/coverage --full`): `class_node` (~301 programs),
`begin`/`rescue`/`ensure` (~171/147/49), constants-paths, and — enabling class bodies —
singleton methods (`def self.x`). bootstraptest is class-heavy, so admitting classes +
exceptions is projected to move coverage from the low-30s% toward the ~80s%
(`fragment-expansion-strategy.md` M3 ≈ 84% cumulative, though that estimate assumed M2's
full params too — see §6).

## RubyCore heads to add (all C12-legit object-model/control primitives)

| Head | Surface | Render back to |
|------|---------|----------------|
| `[:class, name, super_or_nil, body]` | `class Foo < Bar; …; end` | keyword form |
| `[:module, name, body]` | `module M; …; end` | keyword form |
| `[:sclass, obj, body]` | `class << obj; …; end` | keyword form |
| `[:defs, recv, name, params, body]` | `def self.m` / `def o.m` | `def (recv).m(params); …; end` |
| `[:begin, body, [rescues], else_or_nil, ensure_or_nil]` | `begin/rescue/ensure` | keyword form; each rescue = `[[exc_class_nodes], var_or_nil, handler]` |

`name` for class/module is the simple constant string (defer `class A::B` constant-path
names — see §5). `super`/`obj`/exception-classes are expression nodes. `params` reuses the
existing `param_names` machinery (rest params supported; optional/keyword/block still
deferred — that's M2).

### The one trap to avoid (important)

**Do NOT desugar `class Foo; …; end` to `Foo = Class.new do … end`.** It looks equivalent
but changes semantics our round-trip will (rightly) reject: the `class` keyword pushes
`Foo` onto the *lexical* constant nesting (`Module.nesting`) and evaluates the body with
that cref and `self = Foo`, whereas a `Class.new do…end` block keeps the outer lexical
scope. Keep `class`/`module` as **core heads rendered back to the keyword form** (near
identity) — that is both faithful and trivially round-trippable. (Note: `Class.new do … end`
is *already* in-fragment today — it's just a `send` + `block` — so anonymous-class
metaprogramming works now; M3 adds the *keyword* form. See `samples/01-most-complex.txt`.)

## What actually desugars (no new head beyond `begin`)

- **`rescue`-modifier** `expr rescue fallback` (`rescue_modifier_node`) → `[:begin, expr,
  [[[], nil, fallback]], nil, nil]` (a begin with one bare `rescue`, default `StandardError`).
- **Implicit method-body rescue** `def f; …; rescue; …; end`: Prism makes the def body a
  `begin_node` already, so it flows through the `begin` handling — no special case, just
  ensure `desugar_def`/`stmts` route a `begin_node` body correctly.

## Semantics to verify against the oracle (write [V] snippets / adversarial seeds)

These are the corners most likely to produce round-trip disagreements — cover them with
seeds (see artifacts 01–04 for the documented behavior):

- **`ensure` always runs**, and an explicit value/`return` in `ensure` overrides a pending
  return/exception (artifact 04 §5). Adversarial seed with an eval-order trace.
- **Bare `rescue` matches `StandardError`, not `Exception`** (artifact 04 §5). A `raise
  Exception` must escape a bare rescue.
- **`retry`** re-runs the begin body; **`redo`** (already a jump head? no — `redo` is not
  yet a head; add it if needed here or note deferred).
- **Exception observation**: `obs` compares `[class_name, message]` (backtrace already
  stripped, C6). Rescue with `=> e` binds the exception; verify message text matches.
- **`def self.x` / `def o.x`** singleton methods dispatch (artifact 02 §5, 01 §5).
- **Constant scoping in class bodies** (artifact 03 §5) — lexical vs ancestor. If constant
  *paths* are deferred, class bodies using `A::B` are out-of-fragment (fine, skipped).
- **`super`** (bare and `super(...)`) — appears in class hierarchies; `super_node` /
  `forwarding_super_node`. Likely a **separate sub-step** (needs method-owner tracking);
  can defer initially and admit method-only classes first.

## Deferred within / alongside M3 (enumerate, don't silently skip)

- Constant **paths** `A::B` (`constant_path_node`, `constant_path_write_node`) — decide
  whether to include (common in class bodies) or defer one iteration.
- `super`/`forwarding_super` — may warrant its own sub-step.
- Optional/keyword/block params (M2), `case`/`for`/`defined?` (M4).
- Pattern-matching rescue, `refinements`.

## Process (per `PROCEDURE-authoring-semantics.md` + `fragment-expansion-strategy.md` §6)

For each feature: classify (here: mostly new core heads) → add head to
`lib/rubycore.rb` (HEADS + `explain`), a `lib/render.rb` case, and the `lib/desugar.rb`
mapping (+ `Desugar::RULES`) → add a seed (and an **eval-order adversarial seed** for
`ensure`/`retry`) → keep `bin/run` green → re-measure `bin/coverage`, **ratchet up** →
commit + an `implementation-choices.md` entry (next is **C18**). Expect the harness to
catch bugs (it has every batch: interpolation-jump SyntaxError, massign underflow) —
that's the point.

**Exit criterion (this batch):** class/module/singleton/begin-rescue admitted; the
formerly-`class`-blocked bootstraptest programs are in-fragment **and agree**; ratchet
climbs with 0 disagreements; deferred items listed above are documented.
