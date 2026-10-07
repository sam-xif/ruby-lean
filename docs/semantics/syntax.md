# 00 — Notation and abstract syntax

## §1 — Design stance

Small-step SOS over an explicit configuration, not big-step. Ruby's observable
behavior depends on the *order and interleaving of effects* and on non-local
control (`ensure` ordering, `break`/`return` from blocks, exception propagation),
all of which big-step rules hide.

**Everything is a message send.** Wherever Ruby *could* desugar to a method call,
it does (§00 §5). That concentrates the semantics into one dispatch rule
([section 02](dispatch.md)) and makes metaprogramming ordinary heap mutation rather than new
evaluation rules.

## §2 — Machine configuration, and the observation

```
  C  ::=  ⟨ K , H , Ξ ⟩            normal (executing) state
       |  ⟨ K , H , Ξ ⟩^exc(v)     exceptional state carrying raised value v
```

- `K` — the **control**: the expression under focus plus an explicit continuation
  (`kont`) stack rather than evaluation contexts, because Ruby's non-local exits
  need to *inspect and unwind* that stack ([section 04](control-flow.md)).
- `H` — the **heap**: `ObjId ⇀ Object` plus a fresh-id counter ([section 01](objects.md)).
- `Ξ` — the activation stack.

An activation **frame** carries the dynamic *and* lexical context of a running
method or block: `self` and `locals` (dynamic, established at the call site),
`defmod` and `cref` (lexical, captured at the definition site), the block passed
in, and the frame's kind. **That split recurs everywhere** — it is what makes
`super` and constant lookup work.

In Lean this is `Machine` (`Machine.lean`): `ctl`, `kont`, an activation stack of
`FrameId`s, a frame **store** `FrameId ⇀ Frame`, the heap, and the accumulators
the observation needs (stdout, `$!`). See §*Mechanization* below for why the
frames live in a store rather than on the stack.

External Enumerators add a store indexed by object id. Each running or
suspended producer holds an `Execution`: control, continuation and activation
stacks, `$!`, missing-call reason, active Enumerator, live block-call tokens,
Object inspection guards and FrozenError rendering guards. A new producer starts
with empty dynamic scopes; a detached answer run retains its execution's scopes.
Switching execution preserves the shared heap, frame store,
globals, output, literal cache and native Hash iteration locks. Hash locks are a
shared multiset: each active native iteration callback owns one entry, including
callbacks suspended in another execution. A native yield callback suspends at
the actual yield; resumption never replays effects. `Ctl.send` queues an ordinary method dispatch from a native operation.

**Observation.** Differential testing compares `obs(C)`, never raw configs:

```
  obs(C) = ( stdout-trace , inspect(final value) ,
             (exception class, message) if C is ^exc else ⊥ )
```

Two configurations are *observationally equal* iff their `obs` agree. "The model
explains a behavior" means there is a derivation `C₀ →* C` with the matching
`obs(C)`. A heap projection over reachable objects' ivars was specified as a
fourth component and is still deferred (`Obs.lean`).

## §3 — Judgments

The primary judgment is `C → C'`, with `→*` its reflexive-transitive closure.
Auxiliary judgments defined on later pages:

```
  H ⊢ v : k                     v's direct class object is k                   (01 §4)
  H ⊢ ancestors(k) = k̄          the MRO of k                                    (02 §1)
  H; φ ⊢ lookup(v, m) = (k, M)  dispatch of m on v resolves to M, owned by k    (02 §2)
  H; φ ⊢ const C_n ⇓ v          constant resolution                            (03 §5)
```

`H[o ↦ obj]` is heap update, `H(o)` lookup, `H, o:obj` allocation of a fresh id.

## §4 — Abstract syntax

Surface Ruby desugars into this core (`Syntax.lean` mirrors it 1:1, and the
desugarer's `HEADS` set in `desugar/lib/rubycore.rb` mirrors that):

```
Expr e ::= lit ℓ | self | array [e…] | hash [(e ⇒ e)…]
         | lvar x   | lasgn x e          -- one pair per namespace: also
         | ivar @x  | iasgn @x e         --   @@x (cvar/cvasgn), $x (gvar/gasgn),
         | const C  | casgn C e          --   C_n (const/casgn)
         | send e_recv m [e_arg…] blk?   -- THE core primitive
         | blockarg params e_body | yield [e_arg…] | lambda params e_body
         | def m params e_body | defs e_recv m params e_body
         | class C e_super? e_body | sclass e_recv e_body | module C e_body
         | seq e e | if e e e | while e e
         | begin e_body rescues ensure?
         | return e? | break e? | next e? | redo | retry

params ::= [ req x… ; opt (x = e)… ; splat x? ; kwreq k… ; kwopt (k = e)… ;
             kwsplat k? ; block &b? ]
rescue ::= rescue [C_n…] => x? e_handler
```

There is **no operator syntax**: `a + b`, `a[i]`, `a[i] = v`, `-a`, `a == b` are
all `send`. Variable assignment is a distinct form (it binds, it does not
dispatch) but `[]=` and `attr=` are sends. `def`/`class`/`module` are expressions
with effects: they mutate `H` and return a value. A `blockarg` is not
free-standing — it rides on a `send`, and is reified into a `Proc` at the
dispatch boundary.

## §5 — Desugarings

Applied before evaluation, by the Ruby-side front end in
`desugar/`, which is [tested against CRuby on its own](../testing.md#the-desugarer). Representative set:

| Surface | Desugars to |
|---|---|
| `a + b`, `-a`, `a < b` | `send a :+ [b]`, `send a :-@ []`, … |
| `a[i]` / `a[i] = v` | `send a :[] [i]` / `send a :[]= [i, v]` |
| `a && b` / `a \|\| b` | `if a then b else a` / `if a then a else b` — **single-evaluation** |
| `x \|\|= e` / `x &&= e` | `x \|\| (x = e)` / `x && (x = e)` |
| `"…#{e}…"` | `to_s` dispatch + `+` chain, strict left-to-right |
| `attr_accessor :x` | `def x() @x` **and** `def x=(v) @x = v` |
| `unless c` / `until c` | `if (not c)` / `while (not c)` |
| `for v in e` | `send e :each [] (blockarg [req v] …)` — index leaks to the enclosing scope |
| `case x when P` | chain of `if (send P :=== [x])`, subject evaluated once |

Desugaring is **not a homomorphism**, and one case proves it: a control-flow jump
may appear inside string interpolation (`"#{next}"`), and the naive structural
rewrite produces `(next).to_s`, which is a **SyntaxError** — Ruby accepts a jump in
statement or branch position but rejects it in operand position. The fix is to
hoist: if an operand *definitely jumps* (never yields a value), replace the whole
compound with the sequence of operands up to and including it and drop the
unreachable remainder. No temporaries are needed, precisely because a jump has no
value to bind. `desugar/lib/linearize.rb` implements it.

## §6 — Deliberately excluded

C extensions/FFI, `Ractor`/thread memory model, `Fiber` scheduling, GC-observable
behavior and `ObjectSpace`, `eval` of arbitrary strings, `TracePoint`,
`set_trace_func`, and `binding` reification beyond what closures need.
`refinements` are deferred — they perturb dispatch lexically ([section 02](dispatch.md) §7).

Exclusion is not approximation: an excluded construct makes the SUT exit
`Unsupported` with a reason. See `Fragment.lean` and `CRubyNames.lean` — the
latter is oracle-generated per-class method-name tables, so a lookup that misses
an *unmodeled* builtin gates rather than falling through to a user method or a
guessed `NoMethodError`.
