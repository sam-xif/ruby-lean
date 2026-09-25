# RubyCore — the modeled semantics

What the machine in this directory *means*: the configuration it steps, the value
and heap domain, the one dispatch rule, the five variable namespaces, and the
unwinding model behind every non-local exit.

**This file is addressed by the code.** Comments across `*.lean`, the prelude and
the desugarer cite it as *"artifact NN §M"* — the numbering below is that
addressing and is kept stable. It was originally five separate quasi-formal
documents written before the mechanization; they were folded in here when the
code they describe became the thing that runs.

Where this file and the code disagree, **the code is what runs.** `Interp.lean`'s
`stepFn` is the semantics; this is its readable account. Evidence tags: **[V]**
verified against CRuby 4.0.5, **[D]** from documentation / ISO 30170, **[?]** open,
to be pinned by differential testing.

For layout and build, see [`../README.md`](../README.md); for the current fragment, [`../../docs/model/fragment.md`](../../docs/model/fragment.md).

---

## Artifact 00 — notation and abstract syntax

### 00 §1 — Design stance

Small-step SOS over an explicit configuration, not big-step. Ruby's observable
behavior depends on the *order and interleaving of effects* and on non-local
control (`ensure` ordering, `break`/`return` from blocks, exception propagation),
all of which big-step rules hide.

**Everything is a message send.** Wherever Ruby *could* desugar to a method call,
it does (§00 §5). That concentrates the semantics into one dispatch rule
(artifact 02) and makes metaprogramming ordinary heap mutation rather than new
evaluation rules.

### 00 §2 — Machine configuration, and the observation

```
  C  ::=  ⟨ K , H , Ξ ⟩            normal (executing) state
       |  ⟨ K , H , Ξ ⟩^exc(v)     exceptional state carrying raised value v
```

- `K` — the **control**: the expression under focus plus an explicit continuation
  (`kont`) stack rather than evaluation contexts, because Ruby's non-local exits
  need to *inspect and unwind* that stack (artifact 04).
- `H` — the **heap**: `ObjId ⇀ Object` plus a fresh-id counter (artifact 01).
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

**Observation.** Differential testing compares `obs(C)`, never raw configs:

```
  obs(C) = ( stdout-trace , inspect(final value) ,
             (exception class, message) if C is ^exc else ⊥ )
```

Two configurations are *observationally equal* iff their `obs` agree. "The model
explains a behavior" means there is a derivation `C₀ →* C` with the matching
`obs(C)`. A heap projection over reachable objects' ivars was specified as a
fourth component and is still deferred (`Obs.lean`).

### 00 §3 — Judgments

The primary judgment is `C → C'`, with `→*` its reflexive-transitive closure.
Auxiliary judgments defined by later artifacts:

```
  H ⊢ v : k                     v's direct class object is k                   (01 §4)
  H ⊢ ancestors(k) = k̄          the MRO of k                                    (02 §1)
  H; φ ⊢ lookup(v, m) = (k, M)  dispatch of m on v resolves to M, owned by k    (02 §2)
  H; φ ⊢ const C_n ⇓ v          constant resolution                            (03 §5)
```

`H[o ↦ obj]` is heap update, `H(o)` lookup, `H, o:obj` allocation of a fresh id.

### 00 §4 — Abstract syntax

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

### 00 §5 — Desugarings

Applied before evaluation, by the Ruby-side front end in
[`../../desugar/`](../../desugar/README.md), which is separately
differential-tested against CRuby. Representative set:

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
value to bind. Details and the worked cases are in
[`../../docs/front-end/linearization.md`](../../docs/front-end/linearization.md).

### 00 §6 — Deliberately excluded

C extensions/FFI, `Ractor`/thread memory model, `Fiber` scheduling, GC-observable
behavior and `ObjectSpace`, `eval` of arbitrary strings, `TracePoint`,
`set_trace_func`, and `binding` reification beyond what closures need.
`refinements` are deferred — they perturb dispatch lexically (artifact 02 §7).

Exclusion is not approximation: an excluded construct makes the SUT exit
`Unsupported` with a reason. See `Fragment.lean` and `CRubyNames.lean` — the
latter is oracle-generated per-class method-name tables, so a lookup that misses
an *unmodeled* builtin gates rather than falling through to a user method or a
guessed `NoMethodError`.

---

## Artifact 01 — object model, values and heap

Getting this representation right is the whole game: once classes are ordinary
heap objects and dispatch is one rule, metaprogramming becomes heap mutation.

### 01 §1 — Values

```
  Value v ::= ref o | int n | flt x | sym s | true | false | nil
```

Modeling `Integer`/`Float`/`Symbol`/`true`/`false`/`nil` as **immediates** is a
representation choice, not a claim that they aren't objects: every immediate has
a class (§4) and dispatches identically to a `ref`. The consequence to respect is
that their identity is *value* identity — `1.equal?(1)`, `:a.equal?(:a)` and
`nil.equal?(nil)` are all `true`, which falls out for free. `Integer` is
arbitrary-precision.

### 01 §2 — Objects and the heap

```
  Object ::= { class : ObjId, ivars : Var ⇀ Value,
               eigen : Option ObjId, frozen : Bool, payload : Payload }
  Heap   ::= ( store : ObjId ⇀ Object , next : ObjId )
```

Allocation takes `o = H.next` and bumps it; **ids are never reused** (there is no
GC in the model). A class object additionally carries:

```
  ClassPayload ::= { superclass : Option ObjId,   -- none only for BasicObject
                     methods : m ⇀ MethodDef,     -- defined *directly* here
                     consts  : C_n ⇀ Value, cvars : @@x ⇀ Value,
                     is_module, is_singleton : Bool,
                     attached : Option Value }    -- for an eigenclass, its object
```

`MethodDef` records params, body, **`owner`** (needed for `super`), visibility,
and `origin`. `origin = builtin` marks a method whose behavior is a primitive rule
rather than a RubyCore body (`Builtins.lean`, keyed `"Owner#name"` and registered
in H₀'s method tables so that shadowing is uniform). Everything else in the core
library is written *in Ruby* — see `../prelude/prelude.rb`.

### 01 §3 — Builtin payloads

Hidden state that RubyCore expressions cannot express directly: `str` (bytes +
encoding), `arr`, `hsh`, `rng`, `proc` (a `Closure`), `meth`, `exc`. Three carry
semantic teeth:

- **String is mutable** and byte-oriented; `<<`/`gsub!` mutate in place, and two
  equal strings are not `equal?`. **[V]**
- **Hash preserves insertion order** for iteration and `#inspect` — guaranteed
  since 1.9 and observable, so it is part of the spec, not an implementation
  detail. **[V]**
- Frozen string literals change identity and mutation behavior; `frozen` is
  tracked per object.

### 01 §4 — The class-of relation

`H ⊢ v : k` is "the *direct class object* of `v` is `k`". For immediates it is
fixed; for a `ref` it is the object's `class` field — **unless** it has an
eigenclass, which is then its direct class for dispatch purposes.

```
  H(o).eigen = none                      H(o).eigen = some e
 ──────────────────── (CLASS-REF)      ──────────────────── (CLASS-EIGEN)
 H ⊢ ref o : H(o).class                 H ⊢ ref o : e
```

Dispatch (artifact 02) starts from this `k` and walks `ancestors(k)`.

The bootstrap classes are a fixed initial heap **H₀**, including the metaclass
knot — `Class.class == Class`, `Object.class == Class`, and
`Class < Module < Object < BasicObject` **[D]**. The self-reference lives entirely
in H₀ as initial data; no rule has to construct it. `Kernel` and `Numeric` are in
the real ancestor chain so `ancestors` is byte-exact.

### 01 §5 — Eigenclasses

Per-object behavior (`def obj.foo`, `class << obj`) is a **singleton class**
inserted directly above the object in its ancestor chain:

```
  H(o).eigen = none    e ∉ dom(H)
  e_obj = { class = Class, superclass = H(o).class, is_singleton = true,
            attached = ref o, methods = ∅ }
 ───────────────────────────────────────────────────────────── (EIGEN-ALLOC)
  eigenclass(H, ref o) = (e, H[o ↦ … eigen := e][e ↦ e_obj])
```

- `def obj.m` installs into `eigenclass(obj).methods`; `extend M` on an object is
  exactly `include M` into its eigenclass.
- For a **class** `k`, its eigenclass holds `k`'s class methods, and the
  eigenclass chain mirrors the class chain:
  `eigen(k).superclass = eigen(k.superclass)`. That is the rule that makes
  inherited class methods work. **[V]**
- Immediates **cannot** have one: `def 1.foo` raises `TypeError`. The model
  refuses EIGEN-ALLOC for non-`ref` values. **[V]**

### 01 §6 — Identity, equality, truthiness

**Equality is a method, not a primitive.** `==`, `eql?`, `===`, `<=>` are sends
and are user-overridable; the semantics bakes in structural equality nowhere
except as the *default* `BasicObject#==` (identity), supplied as a builtin.
Hash/Set membership therefore *dispatches* `eql?`/`hash` on keys — a place where
the library layer calls back into the core.

**Truthiness is total and simple** **[D][V]**: exactly `false` and `nil` are
falsey; everything else — including `0`, `""`, `[]` — is truthy. This one fact
drives `if`, `while`, `and`/`or` and `!`.

### 01 §7 — Mutation and freezing

The heap is mutable, and ivar assignment plus builtin mutators updating `H` in
place is the *only* reason the semantics is stateful. Mutating a frozen object
raises `FrozenError`. `freeze` is idempotent and in-model irreversible;
`dup`/`clone` allocate copies, and `clone` copies frozen state *and* the
eigenclass while `dup` does not — a genuine observable difference. **[V]**
Immediates are always frozen.

---

## Artifact 02 — dispatch and the ancestor chain

The heart of the semantics. Every operator, attribute access and DSL macro is a
`send`, so **one dispatch rule carries most of the language.**

### 02 §1 — The ancestor chain (MRO)

Ruby's linearization is simpler than C3 — a depth-order insertion, fully
determined by `superclass`, `include`, `prepend` and `extend`:

```
  pre = expand(reverse (prepends k))      -- reverse: last-added is nearest
  inc = expand(reverse (includes k))
  up  = ancestors(superclass k)  (or [] if none)
 ───────────────────────────────────────────────────────── (ANCESTORS)
  H ⊢ ancestors(k) = dedup( pre ++ [k] ++ inc ++ up )
```

where `expand` splices each mix-in's *own* ancestor list, skipping modules
already present. So `prepend`ed modules sit **above** the class, `include`d ones
**below** it and above the superclass, most-recently-added nearest. **[V]**

```
  class B < A; include M; prepend P; end
    B.ancestors == [P, B, M, A, Object, Kernel, BasicObject]
  class D; include M1; include M2; end        # last include wins
    D.ancestors == [D, M2, M1, Object, Kernel, BasicObject]
```

**[?]** Re-`include` and re-`prepend` of a module already in the chain re-insert
under specific conditions in Ruby ≥ 3.0; pinned by differential testing, not by
this sketch.

### 02 §2 — Method lookup

Lookup starts at the receiver's **direct class** (§01 §4 — the eigenclass if one
exists) and returns the first module in `ancestors(k)` defining the name
directly; if none does, `lookup = ⊥`. The resolved pair carries the **owner**
module, which is what `super` (§4) resumes the search after — not the receiver's
class.

### 02 §3 — `send` and `method_missing`

```
  lookup(v, m) = (owner, M)    visible(M, callsite, v)
 ───────────────────────────────────────────────────── (SEND-INVOKE)
  ⟨ send e_recv m [ā] blk ⟩ → invoke(owner, M, v, ā, blk)

  lookup(v, m) = ⊥      m ≠ :method_missing
 ───────────────────────────────────────────────────── (SEND-MM)
  ⟨ send e_recv m [ā] blk ⟩ → ⟨ send e_recv :method_missing [sym m, ā…] blk ⟩
```

`invoke` pushes a frame with `self := v` and `defmod := owner`, binds params,
installs the block and evaluates the body.

**`method_missing` is not magic** — it is an ordinary method whose *default*
(`BasicObject#method_missing`, a builtin) raises `NoMethodError`. Overriding it
just shadows the default in the ancestor chain. `respond_to?` likewise
dispatches, and its default consults defined methods plus
`respond_to_missing?`. **[V]** A miss is a *re-send inside the same rule set*, not
a stuck state — the headline divergence from the prior SML semantics, which omits
dispatch entirely.

### 02 §4 — `super`

`super` re-dispatches the same method name starting strictly **after the current
method's owner**. Bare `super` forwards the current method's actual arguments;
`super(...)` forwards exactly what is given (including `super()` = none). **[V]**

Searching from `owner` rather than from the receiver's class is what makes
`prepend` work:

```
  module P; def greet; "P->" + super; end; end
  class C; prepend P; def greet; "C"; end; end
  C.new.greet == "P->C"
```

Two things the implementation had to get right and this sketch did not say: the
frame records the method name being run, which for an **alias** is the *original*
name (what CRuby's `super` searches for), and `zsuper` reconstructs its arguments
from the running frame's own parameter list rather than re-looking-up the name.

### 02 §5 — Visibility

Checked at the *call site*, against how the method is called:

- **public** — any receiver.
- **private** — implicit receiver only, **or** a literal `self` receiver
  (`self.foo`, including setters `self.x=`), since Ruby 2.7. **[V]**
- **protected** — explicit receiver only if the current `self` `is_a?` the
  method's owner (peer access).

Violations raise `NoMethodError` (`"private method 'm' called"`). Visibility
affects **only** dispatch admissibility, never lookup — a private method is still
*found*; the call is what is rejected. `send`/`__send__` bypass private;
`public_send` does not.

### 02 §6 — Why this design pays off

Every metaprogramming feature reduces to mutating `methods` / `ancestors` /
`eigen` in the heap, after which these same rules apply unchanged:

| Feature | Heap effect |
|---|---|
| `define_method(:m){…}` | insert `m` into the current class's `methods` |
| `attr_accessor :x` | insert `x` and `x=` (desugar, 00 §5) |
| `include M` / `prepend M` | extend `includes`/`prepends`, recompute ancestors |
| `def obj.m` / `extend M` | allocate an eigenclass, insert there |
| `alias` / `alias_method` | copy a `MethodDef` under a new name |
| a dynamic finder | not defined → SEND-MM |

**No new evaluation rules.** That is the concrete cash value of "everything is a
message send" plus "classes are heap objects", and it is why the fragment reached
`define_method`/`class_eval`/`method_missing` without the step relation growing.

### 02 §7 — Open

**[?]** `refinements` genuinely perturb lookup *lexically* — they add modules
consulted before the normal chain, scoped to the activation's `cref`. Deferred;
would need an extra lookup premise keyed on `φ.cref`.
**[?]** `method_added`/`inherited` hooks fire as side effects of the mutations
above, and their sequencing relative to the mutation is observable.

---

## Artifact 03 — variables, scope and constants

Five namespaces. The recurring theme: *dynamic* things key off `self`/`locals`,
*lexical* things key off `cref`/`defmod`, captured at the definition site.

### 03 §1 — The five namespaces

| Form | Stored in | Scope | Undefined read |
|---|---|---|---|
| `x` | `φ.locals` | lexical block/method scope | `NameError` (as a bareword) |
| `@x` | `H(self).ivars` | the current object | `nil` |
| `@@x` | class hierarchy (§4) | the class + subclasses | `NameError` |
| `$x` | a global table | everywhere | `nil` (warns) |
| `C_n` | a module's `consts` (§5) | lexical + ancestor | `NameError` |

The asymmetry — ivar and global reads default to `nil`, locals/constants/cvars
raise — is itself a semantic fact to encode.

### 03 §2 — Locals

Two subtleties dominate.

**(a) Reads and calls are syntactically ambiguous.** `foo` is a local read *if*
`foo` was assigned earlier in the same lexical scope; otherwise it is
`send self :foo []`. That is why an undefined bareword reports *"undefined local
variable or method 'foo'"* — the runtime tried the send. The decision is the
parser's, and the desugarer threads an assigned-locals set to make it. **[V]**

**(b) Blocks close over enclosing locals; methods do not.** A method body starts
with fresh `locals`. A block *shares* the enclosing frame's — it can read and
mutate them: `x=1; [1].each{ x=99 }; x == 99`. **[V]** Block parameters shadow, and
block-locals declared after `;` are fresh: `x=1; [5].each{|y; x| x=99 }; x == 1`.
**[V]**

So a block's environment is *chained*: own params and block-locals, then the
captured frame. In Lean the chain is a `captured : Option FrameId` walked through
the frame store — which is exactly why frames live in a store (see
*Mechanization*).

### 03 §3 — Instance variables

`@x` reads and writes `H(self).ivars`. There is **no declaration**; an unset `@x`
reads as `nil`, no error. Because `self` is dynamic, the same method body touches
different objects' ivars on different calls — ivars are per-object, keyed by the
runtime `self`, never lexical.

### 03 §4 — Class variables

`@@x` is shared across an entire hierarchy: a `@@x` in a superclass is the *same
slot* seen by subclasses and by instance methods. **[V]** Resolution walks from
the current `defmod` up the superclass chain for an existing `@@x`, creating it on
`defmod` if there is none; an undefined read is a `NameError`. This
shared-mutable-across-hierarchy behavior is a notorious footgun and differs from
ivars, so it has to be modeled exactly.

### 03 §5 — Constants: the two-phase lookup

The subtlest scoping rule in Ruby. An unqualified `C_n` resolves in order:

1. **Lexical** — search `Module.nesting` (`φ.cref`), the chain of lexically
   enclosing `module`/`class` bodies, innermost first. **Not** the ancestor chain.
2. **Ancestor** — if lexical fails, search the ancestors of the innermost lexical
   class.
3. Else send `const_missing`, whose default raises `NameError`.

Lexical beats ancestor **[V]**: a method in `Outer::Inner < Base` sees `Outer::C`
even when `Base` defines `C`. Ancestor lookup applies only when lexical fails
**[V]**. And `Module.nesting` is lexical, not dynamic — it reflects the textual
nesting, independent of where the method is called from. **[V]**

A **qualified** `A::B` skips the lexical phase entirely and searches only `A`'s
own consts and ancestors. `casgn` always writes to the innermost lexical module.
Constants are reassignable (with a warning) — not truly immutable. **[V]**

A method carries the cref of where it was *defined*, not its dispatch owner —
which is what makes `def self.m` inside a module resolve constants correctly.

### 03 §6 — Globals

`$x` reads and writes one global table; unset reads yield `nil`. A handful are
special and are modeled as explicit fields rather than table entries: `$!` on the
machine, and `$~` (with `$1`…`$9`, `` $` ``, `$'` as views of it) **per frame** —
CRuby keeps the last match frame-local, so a callee's match is invisible to its
caller. Prelude methods standing in for CRuby C functions (`String#sub`/`#gsub`/
`#index`, `Regexp.last_match`) write the *caller's* slot.

---

## Artifact 04 — blocks, procs and non-local control flow

Where the choice of small-step plus an explicit stack earns its keep: every rule
here is about inspecting and unwinding it.

### 04 §1 — Closures

Blocks, procs and lambdas are the same runtime thing — a `Proc` wrapping a
closure — differing in `lambda?` and how they were created:

```
  Closure ::= { params, body,
                captured : Frame,   -- the DEFINING frame, by reference
                lambda   : Bool }
```

`captured` being by reference is why a block mutating an outer local is visible
after the block runs (03 §2). Creation: `{…}`/`do…end` on a send → a block,
reified to a non-lambda `Proc` only if the callee captures it via `&blk` or asks
`block_given?`; `proc`/`Proc.new` → non-lambda; `->(){}`/`lambda` → lambda.

The lambda flag controls **two** observable behaviors: arity (§2) and the meaning
of `return` (§4).

### 04 §2 — Calling a closure; arity

Invoking a closure pushes a **block frame** whose parent is `captured`, so free
locals resolve into the enclosing scope. Argument binding differs by
`lambda` **[V]**:

- **non-lambda** (blocks, procs): *lenient*. Missing params bind `nil`, extra args
  are dropped, and a single array argument is **auto-splatted** across multiple
  params. `proc{|a,b| [a,b]}.call(1) == [1, nil]`.
- **lambda**: *strict*, exactly like a method. Wrong arity ⇒ `ArgumentError`, no
  auto-splat.

So `bind` is parameterized by the flag, and method invocation uses the strict
variant. `yield` calls the *current method frame's* block without naming it, with
non-lambda binding, and raises `LocalJumpError` when there is none.
`block_given?` is that block being present. **[V]**

### 04 §3 — The unwinding model

`return`, `break`, `next`, `redo`, `retry` and `raise` are **not** ordinary
values: they abort normal evaluation and unwind, looking for a specific target,
running `ensure` blocks encountered on the way. An in-flight transfer is a
distinguished control state:

```
  ^return(v, tgt) | ^break(v, tgt) | ^next(v) | ^redo | ^retry | ^exc(v)
```

In Lean this is the `jump` control state (`Machine.lean`), unwinding the kont
stack and honoring marker konts — frame boundaries, `begin` nodes with live
rescues, while-loop markers.

### 04 §4 — `return`, `break`, `next`, `redo`, `retry`

**`next [v]`** — local to the current block: end this invocation, making
`.call`/`yield` produce `v`. In `map` it sets that element's result.
`[1,2,3].map{|x| next x*10 if x==2; x} == [1, 20, 3]`. **[V]** It is the
block-level analogue of `return`.

**`redo`** — re-run the current block body from the top with the *same*
parameters, without fetching the next element.

**`break [v]`** — terminate the *method call the block was passed to*, making
**that call** return `v` — not the block. The target is the send activation that
installed this block. **[V]**

**`return [v]`** — the crux distinction:

- in a method body or a **lambda**: returns from the immediately enclosing
  method/lambda. **[V]**
- in a **non-lambda proc or block**: returns from the method where the proc was
  *defined* — its captured method frame. If that method has already returned,
  `LocalJumpError`. **[V]**

**`retry`** — inside a `rescue`, restart the enclosing `begin` body from the top.
**[V]**

These lambda-vs-proc control semantics are a top source of real-world Ruby bugs,
so they were a priority target for the oracle.

### 04 §5 — Exceptions

`raise` produces `^exc(v)`; propagation unwinds, and at each frame: transfer to a
matching `rescue` (binding `$!` and the `=> x` variable), and run that frame's
`ensure` as the transfer passes through, matched or not.

**Rescue matching uses `===`**, and the **default rescue class is `StandardError`,
not `Exception`** **[V]** — so `raise Exception` is *not* caught by a bare
`rescue`, and signals/system errors (`SignalException`, `NoMemoryError`,
`SystemExit`) are intentionally missed.

**`ensure` always runs**, on every path out of the protected body. Two facets with
teeth **[V]**:

- an explicit `return` *from* an `ensure` **overrides** the pending return or
  exception, and even swallows an in-flight exception — `def e2; return 1; ensure;
  return 9; end` returns **9**;
- ordering is inner-rescue, then inner-ensure, then the *newly* raised exception
  reaches the outer handler:

```ruby
begin
  begin; raise "a"; rescue; puts "inner-rescue"; raise "b"; ensure; puts "inner-ensure"; end
rescue => e; puts "outer: #{e.message}"; end
# => inner-rescue / inner-ensure / outer: b
```

So `ensure` fires as the `^exc`/`^ctl` state *transits* the frame, and must be
able to **replace** the in-flight transfer if it returns or raises itself.
`raise` with no args inside a `rescue` re-raises `$!`.

### 04 §6 — The unwinding invariant

All of §3–§5 share one mechanism, stated as the metatheorem worth proving:

> **Unwind soundness.** Any control state `^ctl` deterministically either (a)
> reaches its target, running exactly the `ensure` blocks lexically between the
> jump site and the target, innermost-to-outermost, each exactly once; or (b)
> escapes the whole stack, becoming an uncaught-exception or `LocalJumpError`
> observation. No `ensure` is skipped or double-run, and a later `^ctl` raised
> inside an `ensure` supersedes an earlier in-flight one.

This is what makes the control semantics *explainable*: every observed ordering
has a derivation that runs the ensures in a provably correct sequence.

### 04 §7 — Open

**[?]** `Fiber`/`Enumerator` need a first-class captured continuation; deferred.
**[?]** An `ensure` that raises while an exception is already in flight — whose
backtrace wins, and `Exception#cause` chaining.

---

## Mechanization — from these rules to `stepFn`

Two definitions coexist: `inductive Step` (`Proof/Step.lean`) is the definition of
record, and `stepFn` + `run fuel` (`Interp.lean`) is what executes. The adequacy
theorems in `Proof/Adequacy.lean` are the bridge — differential testing earns
trust for the *interpreter*, proofs live on the *relation*, and adequacy transfers
the empirical trust across. Deliberately, the interpreter landed **first**, so the
model could meet the differential engine on day one rather than after coverage
grew.

Three decisions carried over from the prior art, which was read closely before any
Lean was written:

**Generativity is frame identity.** *The Essence of Ruby* (Ueno et al., APLAS'14)
observed that `return`/`break`/`next` destinations cannot be statically labeled —
the same `break` in a recursive method-with-block targets a *different* activation
each time — and modeled it with ML-style generative exceptions: a fresh tag per
call, per block creation, per yield, with a dead tag meaning `LocalJumpError`.
Right concept, wrong substrate for Lean. Here every activation has a unique
`FrameId`; a `Proc` captures the ids it returns and breaks to; a jump unwinds
searching for its target id; **a target id no longer on the stack *is*
`LocalJumpError`.** Tag liveness is frame presence — one mechanism, no meta-level
exception layer. (Their SML interpreter failed the detached-`Proc`-`break` test for
exactly the reason this formulation gets right by construction.)

**Frames live in a store, not on the stack.** Their control calculus keeps locals
in a variable store with environments mapping names to *references*, because
blocks share their defining scope's locals mutably. Here the configuration holds a
frame store `FrameId ⇀ Frame` and the activation stack is a list of ids. That one
mechanism delivers **both** of their stores at once — shared mutable locals *and*
generative jump targets. It is the central data decision.

**Heap operations are a module boundary.** Their object/control split composed two
relations through an "oracle"; a single relation over one configuration is simpler
to mechanize and to run, so what is kept is the interface discipline it proves
possible: `classOf`/`ancestors`/`lookup`/ivar and const access are *pure functions
on the heap*, in their own module with their own lemmas, and the step relation
touches the heap only through them. Artifacts 01–02 stay provable independently of
artifact 04.

Rejected, and the rejections still stand: **big-step** (hides effect order, makes
`ensure`-during-unwind awkward, cannot express divergence); **generative
exceptions as the mechanism** (see above); and **maximal linearization** — RIL
(Furr et al., DLS'09) flattens every side-effecting subexpression to a temporary
because its consumer is static dataflow analysis, whereas a nested-evaluation
semantics already handles compound subexpressions correctly, so RubyCore
linearizes *minimally* and stays small, which is what keeps the metatheory
tractable.

What RIL does contribute: the **pipeline split is validated** — Lean does not parse
Ruby, it consumes RubyCore JSON from the separately-difftested Ruby front end, over
a versioned wire format either side can reject. And RIL §3.2's **evaluation-order
obligations are semantics, not just desugaring**: `a().f = b().g` and
`a().f, x = b().g` evaluate their parts in *different* orders, and that has to hold
in the step relation's own argument-evaluation rules. Those became early
adversarial seeds.

One component was not foreseen by any of this and proved load-bearing:
`CRubyNames.lean`, the oracle-generated method and constant name tables (00 §6).

Still open from the mechanization **[?]**: the frame store grows monotonically
(dead frames are retained — fine while fuel bounds everything); how much builtin
behavior stays a `Payload` primitive versus migrating into the Ruby prelude; and
`run fuel` conflating "diverges" with "fuel exhausted", which is why `RunResult`
distinguishes `outOfFuel` from `stuck` from day one even though the co-divergence
check itself is deferred.

---

## Where the rest of this lives

| Topic | Read |
|---|---|
| Layout and build | [`../README.md`](../README.md) |
| The current fragment, the metatheory | [`../../docs/model/fragment.md`](../../docs/model/fragment.md), [`../../docs/model/metatheory.md`](../../docs/model/metatheory.md) |
| The checker over this model, and the gate | [`../AGENTS.md`](../AGENTS.md) |
| Front end: `desugar : Surface → RubyCore` | [`../../desugar/README.md`](../../desugar/README.md); artifact 06 is [`../../docs/front-end/method.md`](../../docs/front-end/method.md) |
| Differential-testing methodology, and artifact 05 | [`../../docs/testing/methodology.md`](../../docs/testing/methodology.md) |
| The chronological record — what was tried and what it cost | [`../notes/`](../notes/README.md) |
