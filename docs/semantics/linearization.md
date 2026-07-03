# Linearization — a worked example of why desugaring is nontrivial

> A cross-cutting desugaring technique, referenced by `00-notation-and-syntax.md` §5 (the
> desugaring table) and `06-desugaring-and-its-testing.md`. Implemented in the harness at
> `../../harness/desugar-dt/lib/linearize.rb`; decision recorded in that harness's
> `implementation-choices.md` (C15/C16). Prior art: the Ruby Intermediate Language (RIL),
> `../../ruby_papers/ruby_intermediate_language.pdf`, whose contribution was exactly this
> kind of "make evaluation order explicit via temporaries / one action per statement."

This artifact documents a small but instructive case where a *faithful* desugaring cannot
be a naïve structural rewrite — it must reorganize control flow. It is the concrete proof
that `desugar : Surface → RubyCore` is not a trivial map.

## 1. The problem

Ruby allows a control-flow jump (`next`/`break`/`return`) inside string interpolation:

```ruby
while true
  counter -= 1
  break if counter == 0
  "#{next}"          # legal; the `next` fires when the interpolation is evaluated
end
```

`"#{next}"` behaves exactly like a bare `next`: the jump fires the instant that part of
the interpolation is reached, and the string is never assembled. (This is not idiomatic —
it comes from CRuby's own parser/compiler regression tests, `bootstraptest/test_syntax.rb`,
"reported by Yusuke ENDOH".)

Our desugaring of interpolation is the obvious structural one — build the string by
concatenating `to_s` of each embedded expression:

```
"a#{e}b"   ⟿   [:send, [:send, [:str,"a"], "+", [[:send, e, "to_s", []]]], "+", [[:str,"b"]]]
```

But if `e` is a jump, this produces `[:send, [:next], "to_s", …]`, which renders to the
Ruby text `(next).to_s` — a **`SyntaxError`**. A jump cannot appear as an operand.

## 2. The precise rule (verified against CRuby 4.0.5)

Ruby's parser accepts a jump in a **statement / branch position** but rejects it in an
**operand position**:

| Position | Example | Legal? |
|----------|---------|--------|
| statement | `next` | ✅ |
| if/while body, seq element | `while c; next; end` | ✅ |
| if/ternary **branch** — even when the `if` is itself an operand | `(if c then next else 5 end).to_s`, `foo(x ? next : 5)`, `[x ? next : 5]` | ✅ |
| **operand** — send recv/arg, array/hash element, assignment RHS, if/while cond | `(next).to_s`, `foo(next)`, `[next]`, `x = next` | ❌ SyntaxError |
| operand where **all** `if` branches jump | `(if c then next else break end).to_s` | ❌ SyntaxError |

The distinction is *whether the operand can ever yield a value*. A conditional jump (one
branch jumps, the other yields) is fine; an **unconditional** jump (never yields) is not.

Notably, string interpolation is essentially the *only* valid-Ruby source construct that
places a jump in operand position — `foo(next)`, `[break]`, `x = next` are already
SyntaxErrors in source, so they never reach the desugarer. That is why this surfaced via
interpolation specifically.

## 3. How CRuby handles it (for contrast)

CRuby does *not* rewrite to a value-expression. Its compiler emits the interpolation's
byte­code normally (push prefix, evaluate embedded, `objtostring`/`anytostring`, push
suffix, concat), but when the embedded expression is a jump it emits the control transfer
right there — a `jump` (to the loop condition) for a `while`-`next`, a `leave` for a block
`next`, a `throw` for `break` — leaving the string-completion instructions as **dead
code**, and inserts `adjuststack` to keep the operand-stack depth consistent. (The
stack-depth bookkeeping for a non-falling-through operand is exactly what the historical
bugs were about — hence the tests are `assert_normal_exit`.)

We can't do that at the bytecode level, so we do the **source-level analogue**.

## 4. The transformation: hoist unconditional jumps

`definitely_jumps?(node)` — does evaluating `node` always transfer control (never yield a
value)?

```
  return | break | next            → true
  seq                              → any element definitely jumps
  if(c, t, e)                      → c jumps, or (t jumps AND e jumps)   -- both branches
  otherwise                        → false
```

**Linearize**: rewrite so no `definitely_jumps?` node sits in operand position. For a
compound (`send`, `array`, `hash`, and the concats interpolation produces), evaluate the
operands left-to-right; if operand *i* definitely jumps, replace the whole compound with
the **sequence of operands up to and including *i***, dropping the unreachable remainder:

```
  [:send, recv, m, [a₀, …, aᵢ(jumps), …]]   ⟿   [:seq, recv, a₀, …, aᵢ]
```

**Key property: no temporaries are needed.** We only ever hoist an operand that never
yields a value, so there is nothing to bind — we just sequence the effects up to the jump
and discard everything after (which is genuinely unreachable, mirroring CRuby's dead
code). This is what makes the pass small. (A *conditional* jump is left in place, because
Ruby accepts it in a branch position — see the table.)

## 5. Worked results (harness, verified to re-parse and round-trip)

| Source (in a loop) | Linearized render | Note |
|--------------------|-------------------|------|
| `"#{next}"` | `next` | pure hoist |
| `"a#{next}b"` | `("a"; next)` | prefix `"a"` evaluated for effect; `"b"` dropped |
| `"x#{(p 1); next}y"` | `("x"; (p(1); next))` | embedded effects preserved in order, then jump |
| `"v=#{c ? next : 5}"` | `("v=").+((if c then next else 5 end).to_s)` | **conditional** → *not* hoisted, stays inline |

All four re-parse as valid Ruby and produce the same observation (incl. the
evaluation-order trace) as the original under CRuby.

## 6. Why this is the lesson

- **Desugaring is not a homomorphism.** A structural, context-free rewrite (`e ↦ e.to_s`)
  is *unsound* here — it produces unparseable/ill-formed output. Faithful desugaring has
  to reason about control flow and evaluation order, exactly as RIL's linearization does.
- **The core stayed small.** The fix added *no* RubyCore node — it uses only `seq` and
  existing forms (consistent with the node-addition policy, harness C12). Complexity lives
  in the desugaring pass, not the core.
- **It generalizes.** The same `definitely_jumps?`-driven hoisting is the mechanism we
  will reuse for other order-sensitive desugarings (indexed/attribute op-assign
  once-only, safe navigation, splat with side effects). Interpolation was just its first
  customer.
- **The harness found it.** The need for this pass was not designed up front; it surfaced
  as a round-trip *harness-error* (original observed fine, rendered didn't parse) when
  `return/break/next` were admitted — the differential loop doing its job (see
  `06-desugaring-and-its-testing.md` §6).

## 7. Contrast with RIL — linearize *minimally*, not maximally

RIL (`../../ruby_papers/ruby_intermediate_language.pdf`) pioneered Ruby linearization, but
for a different purpose, and the difference shows up precisely here. RIL is an intermediate
representation built to enable **static dataflow analysis** (its clients are DRuby type
inference and DRails), so it **linearizes maximally**: every side-effecting subexpression
is hoisted to a temporary, giving "one semantic action per statement" — the normalized,
CFG-friendly shape a dataflow analysis wants.

We linearize for the opposite consumer — a **small-step operational semantics** (an
interpreter, and eventually Lean proofs). A nested-evaluation semantics already handles
compound subexpressions and their order correctly, so we have no reason to flatten them.
We therefore **linearize minimally**: only where the render-to-Ruby step would otherwise
produce ill-formed text — i.e. an *unconditional jump in operand position*. Everything else
stays nested, keeping the RubyCore AST small (which is what makes the eventual metatheory
tractable, and is consistent with the node-addition policy, harness C12).

So the same technique, opposite dial settings:

| | RIL | Ours |
|---|-----|------|
| Consumer | static dataflow analysis | operational interpreter + proofs |
| Linearization | maximal — every side-effecting subexpr → temp | minimal — only unconditional jumps in operand position |
| Temporaries | pervasive | none for this case (a jump yields no value to bind) |
| Goal shape | flat, one-action-per-statement (CFG-friendly) | small nested AST (proof-friendly) |

The general ANF machinery that *does* bind temporaries (for order-sensitive rewrites like
indexed op-assign — §8 below) is where we approach RIL's fuller linearization; the
jump-hoisting here is the degenerate, temp-free corner of it. (Broader RIL comparison:
`../../PROJECT_PLAN.md` §3.)

## 8. Open questions

- **[?]** Are there other valid-source operand-position jump sites beyond interpolation
  (e.g. inside `BEGIN{}`-like forms, or pattern-matching value positions)? None known; the
  round-trip will flag any as a harness-error.
- **[?]** When we add temp-requiring desugarings (indexed op-assign etc.), the general
  ANF/linearization machinery grows to *bind* intermediate values; the unconditional-jump
  case documented here is the degenerate, temp-free corner of that larger pass.
