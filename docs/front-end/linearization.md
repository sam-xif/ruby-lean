# Linearization

The worked case proving `desugar` is not a trivial map. Implemented in
`lib/linearize.rb`; decision recorded as `implementation-choices.md` C15/C16.
Prior art: the Ruby Intermediate Language (RIL), whose contribution was exactly
this — making evaluation order explicit.

## The problem

Ruby allows a control-flow jump inside string interpolation:

```ruby
while true
  counter -= 1
  break if counter == 0
  "#{next}"          # legal; the `next` fires when the interpolation is reached
end
```

`"#{next}"` behaves exactly like a bare `next`. (Not idiomatic — it comes from
CRuby's own parser regression tests.) But the obvious structural desugaring of
interpolation — concatenate `to_s` of each embedded expression — produces
`[:send, [:next], "to_s", …]`, which renders as `(next).to_s`: a **SyntaxError.**
A jump cannot appear as an operand.

## The precise rule **[V]**

Ruby's parser accepts a jump in **statement or branch** position and rejects it in
**operand** position:

| Position | Example | Legal? |
|---|---|---|
| statement | `next` | ✅ |
| if/while body, seq element | `while c; next; end` | ✅ |
| if/ternary **branch**, even when the `if` is itself an operand | `(if c then next else 5 end).to_s`, `foo(x ? next : 5)` | ✅ |
| **operand** — send receiver/arg, array/hash element, assignment RHS, condition | `(next).to_s`, `foo(next)`, `[next]`, `x = next` | ❌ |
| operand where **all** `if` branches jump | `(if c then next else break end).to_s` | ❌ |

The distinction is *whether the operand can ever yield a value*. A conditional
jump is fine; an **unconditional** one is not.

Notably, interpolation is essentially the only valid-Ruby construct that puts a
jump in operand position — `foo(next)`, `[break]`, `x = next` are already
SyntaxErrors in source and never reach the desugarer. That is why this surfaced
via interpolation specifically.

CRuby handles it at the bytecode level: it emits the interpolation normally, emits
the control transfer where the embedded expression sits, leaves the
string-completion instructions as **dead code**, and inserts `adjuststack` to keep
the operand stack consistent. That is not available at source level, so we do the
source-level analogue.

## The transformation

`definitely_jumps?(node)` — does evaluating this always transfer control?

```
  return | break | next   → true
  seq                     → any element definitely jumps
  if(c, t, e)             → c jumps, or (t jumps AND e jumps)
  otherwise               → false
```

**Linearize:** for a compound (`send`, `array`, `hash`, and the concats
interpolation produces), evaluate operands left to right; if operand *i*
definitely jumps, replace the whole compound with the sequence of operands up to
and including *i*, dropping the unreachable remainder.

```
  [:send, recv, m, [a₀, …, aᵢ(jumps), …]]   ⟿   [:seq, recv, a₀, …, aᵢ]
```

**No temporaries are needed** — we only ever hoist an operand that never yields a
value, so there is nothing to bind. That is what keeps the pass small. A
*conditional* jump is left in place, because Ruby accepts it in branch position.

| Source (in a loop) | Linearized render | Note |
|---|---|---|
| `"#{next}"` | `next` | pure hoist |
| `"a#{next}b"` | `("a"; next)` | prefix evaluated for effect; `"b"` dropped |
| `"x#{(p 1); next}y"` | `("x"; (p(1); next))` | embedded effects preserved in order |
| `"v=#{c ? next : 5}"` | `("v=").+((if c then next else 5 end).to_s)` | **conditional** → not hoisted |

## The lesson, and the dial setting

**Desugaring is not a homomorphism.** A context-free structural rewrite
(`e ↦ e.to_s`) is *unsound* here — it produces ill-formed output. Faithful
desugaring has to reason about control flow. And **the core stayed small**: the
fix added no RubyCore node, using only `seq` and existing forms (C12).

RIL pioneered Ruby linearization but for the opposite consumer, and the difference
shows up precisely here:

| | RIL | here |
|---|---|---|
| Consumer | static dataflow analysis | operational interpreter + proofs |
| Linearization | **maximal** — every side-effecting subexpr → a temporary | **minimal** — only unconditional jumps in operand position |
| Temporaries | pervasive | none for this case |
| Goal shape | flat, one action per statement (CFG-friendly) | small nested AST (proof-friendly) |

A nested-evaluation semantics already handles compound subexpressions and their
order correctly, so there is no reason to flatten them — and keeping the AST small
is what makes the metatheory tractable.

**The harness found it.** This pass was not designed up front. It surfaced as a
round-trip *harness error* — the original observed fine, the rendered version
didn't parse — the first time `return`/`break`/`next` were admitted. The
differential loop doing its job ([06 §6](method.md#06-6-triage)).

**[?]** Are there other valid-source operand-position jump sites (pattern-matching
value positions)? None known; the round-trip will flag any as a harness error.
When temp-requiring desugarings land (indexed op-assign), the general ANF
machinery grows to *bind* intermediates; the jump case here is its degenerate,
temp-free corner.
