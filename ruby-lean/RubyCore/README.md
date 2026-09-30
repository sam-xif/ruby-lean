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

External Enumerators (L280) add a store indexed by object id. Each running or
suspended producer holds an `Execution`: control, continuation and activation
stacks, `$!`, missing-call reason, active Enumerator, live block-call tokens and
Object inspection guards. A new producer starts with empty dynamic scopes; a
detached answer run retains its execution's scopes. Switching execution preserves the shared heap, frame store,
globals, output and literal cache. A
native yield callback suspends at the actual yield; resumption never replays
effects. `Ctl.send` queues an ordinary method dispatch from a native operation.

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
  ClassPayload ::= { superclass : Option ObjId,   -- none for modules, BasicObject, allocation
                     methods : m ⇀ MethodDef,     -- defined *directly* here
                     consts  : C_n ⇀ Value, cvars : @@x ⇀ Value,
                     is_module, is_singleton : Bool,
                     initialized, ancestryReady, allocatorUnavailable : Bool,
                     attached : Option Value }    -- for an eigenclass, its object
```

`MethodDef` records params, body, **`owner`** (needed for `super`), visibility,
and `origin`. `origin = builtin` marks a method whose behavior is a primitive rule
rather than a RubyCore body (`Builtins.lean`, keyed `"Owner#name"` and registered
in H₀'s method tables so that shadowing is uniform). Everything else in the core
library is written *in Ruby* — see `../prelude/prelude.rb` and
`../prelude/features/`. Method and closure origin follows model library code
through calls; it is separate from the boot-only flag that suppresses callbacks.
Classes opened by library code retain a canonical namespace tag for the generated
API inventories, independently of their Ruby-visible names (including aliases).
An inherited visibility override stores `visibilityOnly` and resolves the current
ancestor body on each lookup. Aliases instead retain the selected body,
`superName`, and (for class/eigenclass aliases) `superScope`; the latter preserves
the lookup context needed when the same module occurs in different class chains.
L283 adds `definee`, distinct from the dispatch owner. A `def self.make` inside C
can therefore define an instance method on C when its body executes a nested def.
A define_method body also retains its block's definition-context frame even when
its local-variable capture can be erased; the two kinds of capture are independent.

### 01 §3 — Builtin payloads

Hidden state that RubyCore expressions cannot express directly: `str` (bytes +
encoding), `arr`, `hsh`, `rng`, `proc` (a `Closure`), `meth`, `exc`, and
`rational` and `complex`. Some observable consequences:

- **String is mutable** and byte-oriented; `<<`/`gsub!` mutate in place, and two
  equal strings are not `equal?`. **[V]**
- **Hash preserves insertion order** for iteration and `#inspect` — guaranteed
  since 1.9 and observable, so it is part of the spec, not an implementation
  detail. **[V]**
- Frozen string literals change identity and mutation behavior; `frozen` is
  tracked per object.
- **Exception** retains its message as a Ruby Value, including mutable objects;
  nil selects the current class-name default. String messages retain identity.
  Other messages render through checked to_str then to_s calls (L285).
- **Rational** carries a reduced arbitrary-precision numerator and positive
  denominator. It remains a heap object even when the denominator is one.
  Instances are frozen; `dup`, `clone` with nil/true freezing, and `to_r` retain identity.
  A native rational literal bypasses constructor/constant lookup and is cached
  by compilation unit and syntax site; repeated execution of one site shares
  its object, while separate sites and constructor calls remain distinct (L278).
  Mixed numeric operations follow Ruby's coercion protocol. Conversion to Float
  follows the 64-bit CRuby integer-division paths, including their intermediate
  rounding; it is not specified as the exact quotient rounded only once.
- **Complex** carries native real and imaginary components (Integer, Float or
  Rational), preserving their types and identities. Instances are frozen; `dup`,
  `clone` with nil/true freezing, and `to_c` retain identity. Imaginary literals use the
  same compilation-unit/site cache as Rational literals and bypass constructor
  lookup. Float components cross JSON as IEEE bits, preserving negative zero.
  Numeric construction follows CRuby's zero normalization, including its
  distinction between exact zero and Float zero. Division uses the oracle's
  ratio-based scalar operations and intermediate rounding; division through a
  user coerce result sends `quo`. Effectful component operations/representation,
  nonfinite arithmetic, string/custom conversion and unimplemented methods
  remain explicit fragment gates (L279).

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
`dup`/`clone` allocate copies. Native `clone` accepts `freeze: nil`, `true`, or
`false`; nil preserves the source's live frozen state after the copy hooks return,
true freezes the result, and false leaves the hook's final state alone. Immutable
values return themselves and reject `freeze: false`. Positional arity precedes
keyword validation; unknown keys are inspected and invalid option classes use
Ruby `to_s`. **[V]** (L298)

For Object, String, Array, Hash and Exception, clone copies ivars into a mutable
allocation and sends private `initialize_clone`, which normally sends
`initialize_copy`. Hook results are discarded; raise/throw retain effects and
skip final freezing. String/Array/Hash initially have empty native contents;
Exception's message and native metadata are copied before hooks. The native
core `initialize_copy` methods fill contents, preserve destination ivars, and use
checked String/Array/Hash conversion. Frozen checks precede conversion; String
also checks afterward, while Array/Hash can finish after conversion freezes them.
Ordinary copies of other already-modeled payloads retain the default-hook shortcut;
custom hooks require their uninitialized native state. Singleton-class copying,
namespace copying and Random state remain incomplete.
CRuby clone copies singleton classes, but that behavior is still gated here.
**[V]** (L298)

Native `dup` checks zero positional arity (a nonempty keyword bundle counts as
one positional Hash), then returns immutable values unchanged or allocates a
mutable copy. It omits the source's eigenclass, including extension modules,
singleton methods and singleton copy hooks. It dispatches private initialize_dup
on the copy, whose default calls initialize_copy; hook results are discarded and
hook freezing is preserved. Core shell allocation/content copying is shared with
clone, without clone's final freeze policy. Aliases and super use the resolved
native entry. Existing namespace/Random and other native custom-copy boundaries
remain explicit. **[V]** (L299)


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

`invoke` pushes a frame with `self := v`, the body's lexical `defmod`, and a
separate `methodOwner` for super, then binds params,
installs the block and evaluates the body.

**`method_missing` is not magic** — it is an ordinary method whose *default*
(`BasicObject#method_missing`, a builtin) raises `NoMethodError`. Overriding it
just shadows the default in the ancestor chain. `respond_to?` likewise
dispatches, and its default consults defined methods plus
`respond_to_missing?`. **[V]** A miss is a *re-send inside the same rule set*, not
a stuck state — the headline divergence from the prior SML semantics, which omits
dispatch entirely.

Native Class#new is selected after lookup and visibility, including aliases and
super. For plain objects and modeled core payloads, it allocates directly (without
sending an overridable allocate), sends private initialize with the original
arguments/keywords/block, and discards only the normal initializer result.
Undef initialize therefore reaches method_missing. Proc construction retains or
copies the block's closure before initialization. Core initializers return the
receiver; BasicObject#initialize requires zero arguments and returns nil.
Class and Module use the same allocation/initializer protocol, including Module
subclasses and replaced or undefined initializers. `Class.allocate` produces an
uninitialized class. Native Class#initialize validates the superclass, installs
its ancestry and allocator state, replaces the old eigenclass, sends `inherited`
to the parent, then executes the block as module_exec and returns the class.
Native Module#initialize executes that block and returns nil. Normal `new`
discards this result; block exits keep their original targets. Module's public
`allocate` method is undefined, but an alias of native Class#allocate can allocate
it. Random/Regexp still use partial argument-dependent factories and gate
replaced initializers. **[V]** (L284, L291)

New named classes bind their constant before sending `inherited`, and execute
the saved class body only after the callback returns. Reopening does not resend
the callback. Raises retain the binding and earlier effects; a callback replacing
the constant cannot redirect the saved body. Class.new rejects an uninitialized
parent, while named class syntax in CRuby 4.0.5 permits one. Such children retain
an unavailable ancestry index and allocator, even if their parent is initialized
later. CRuby 4.0.5 also permits initializing a frozen allocated class; these rules
are pinned to the executable oracle. Superclass type errors dispatch the selected
class's live to_s, preserving effects, exceptions and non-String fallback. **[V]**
(L291)

Unnamed Module-subclass instances render through their direct class's temporary
path, including an eigenclass if present. This path uses its name/address rather
than recursively rendering its attachment. Singleton-class to_s itself still
renders the attached object from the live heap. Reflective const_set names an
anonymous class/module just as ordinary constant assignment does. **[V]** (L291)

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
Class aliases also retain the chain in which their body was selected. Module
aliases use the eventual host receiver's chain. This fixes alias/super context;
the ancestor representation still deduplicates repeated module identities and
does not claim a complete model of CRuby's distinct inclusion nodes. **[V]**

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

Changing the visibility of an inherited method installs a live forwarding entry,
so a later ancestor redefinition changes the body called through it. An unchanged
visibility is a no-op. Module visibility and alias macros can consult Object;
undef/remove do not use that fallback. Initialization methods are private when
defined as instance methods, including through aliases and attributes. **[V]**
Reflection observes the forwarding entry even after its ancestor body disappears;
calls then fail, and aliases cannot capture a missing body. **[V]**

Ordinary blocks share their defining context's visibility, including changes made
before a saved Proc runs or inside a block. Block forms of class_eval/instance_eval
start a fresh public definition context while retaining lexical constant scope.
Ordinary method bodies start public and ignore bare visibility changes (Ruby's
warning is outside the observation triple). Attribute/define_method macros use
the caller's visibility only when it belongs to the same class/eval target;
top-level define_method is public. Top-level def defaults to private and honors
an explicit public change. **[V]**

Main's native singleton methods have their own entries and visibility. Public,
private, include and define_method are private macros there, and do not appear on
ordinary Object instances. Their missing/unmodeled inventory is separate from
Object's method inventory. **[V]**

### 02 §6 — Why this design pays off

Every metaprogramming feature reduces to mutating `methods` / `ancestors` /
`eigen` in the heap, after which these same rules apply unchanged:

| Feature | Heap effect |
|---|---|
| `define_method(:m){…}` | insert `m` into the current class's `methods` |
| `attr_accessor :x` | insert `x`, run its callback, then insert `x=` |
| `include M` / `prepend M` | extend `includes`/`prepends`, recompute ancestors |
| `def obj.m` / `extend M` | allocate an eigenclass, insert there |
| `alias` / `alias_method` | copy a `MethodDef` under a new name |
| a dynamic finder | not defined → SEND-MM |

L282's `MethodEdit` queue commits one method-table mutation, then dispatches its
Ruby callback before continuing. Definitions, aliases, define_method and attributes
call `method_added`; remove/undef call `method_removed`/`method_undefined`.
Eigenclass writes call the corresponding `singleton_method_*` on the attached
receiver. Ordinary dispatch preserves private hooks, super and method_missing.
A hook may raise, freeze the target or alter the next method: prior writes remain,
and each remaining write checks the current heap and frozen state. The boot-only
prelude suppresses hooks; runtime library loading does not. **[V]**

### 02 §7 — Open

**[?]** `refinements` genuinely perturb lookup *lexically* — they add modules
consulted before the normal chain, scoped to the activation's `cref`. Deferred;
would need an extra lookup premise keyed on `φ.cref`.
**[?]** Ancestry mutation hooks (`append_features`, `prepended`, `extended`)
still need a complete protocol audit. Constant-name conversion, removal and
recursive temporary namespace naming also remain incomplete; const_added dispatch
is modeled below (L292).

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
the innermost ordinary lexical class/module up its ancestor chain for an existing
`@@x`, creating it there if there is none; an undefined read is a `NameError`.
Singleton-class scopes are skipped. With no enclosing class/module, reads and
writes raise RuntimeError even inside a Proc or method; defined? can still inspect
Object's class variables. Block eval retains this lexical scope. **[V]** This
shared-mutable-across-hierarchy behavior is a notorious footgun and differs from
ivars, so it has to be modeled exactly.

### 03 §5 — Constants: the two-phase lookup

The subtlest scoping rule in Ruby. An unqualified `C_n` resolves in order:

1. **Lexical** — search `Module.nesting` (`φ.cref`), the chain of lexically
   enclosing `module`/`class` bodies, innermost first. **Not** the ancestor chain.
2. **Ancestor** — if lexical fails, search the ancestors of the innermost lexical
   class. A module can then fall back to Object.
3. A miss follows `const_missing` in Ruby. The model handles the default error;
   user const_missing hooks remain a boundary that needs a complete audit.

Lexical beats ancestor **[V]**: a method in `Outer::Inner < Base` sees `Outer::C`
even when `Base` defines `C`. Ancestor lookup applies only when lexical fails
**[V]**. And `Module.nesting` is lexical, not dynamic — it reflects the textual
nesting, independent of where the method is called from. **[V]**

A **qualified** `A::B` skips the lexical phase entirely and searches only `A`'s
own consts and ancestors. `casgn` always writes to the innermost lexical module.
Constants are reassignable (with a warning) — not truly immutable. **[V]**

Every modeled constant write binds and names its value before sending private
`const_added` through ordinary dispatch. Reassignment calls the hook again. Its
normal result is discarded; exceptions and nonlocal exits retain the write and
skip the pending continuation. Named class/module definitions keep their original
object for the body even if the hook replaces the binding. Their order is binding,
const_added, inherited (classes), then body; reopening sends neither hook. Only
core prelude boot suppresses const_added. **[V]** (L292)

Namespace paths distinguish temporary names from permanent ones. Binding under
Object or an already permanent namespace promotes the value and its live nested
namespaces before const_added. Existing permanent names survive aliases; naming
does not traverse inherited constants, emit descendant callbacks or reject frozen
descendants. Ancestor cycles stop at the newly named ancestor. Temporary parents
give only a first temporary path and do not rename descendants. Native class paths
are distinct from singleton-class display names; Object-qualified declarations
still acquire bare top-level names. Shared descendants whose chosen path depends
on CRuby's symbol-table iteration order remain gated. **[V]** (L295)

Native `Module#name` returns a frozen base String cached by native path and
encoding tag. Repeated reads and distinct namespaces bearing the same path share
identity; permanent promotion selects a new cached value without mutating saved
temporary-name Strings. Anonymous namespaces return nil. ASCII temporary paths
are binary; non-ASCII paths are UTF-8. Permanent ASCII paths retain the existing
US-ASCII/UTF-8 observation boundary. Ruby String constructors/freezing hooks do
not run, and `Module#to_s`/`inspect` still return fresh mutable display Strings.
This name cache does not implement general String#-@ interning. **[V]** (L297)

Native `Module#const_set` checks arity, then converts its name through checked
`to_str` unless it is already a Symbol or String. Conversion and name validation
precede the frozen check. UTF-8 names require an uppercase/titlecase first scalar;
later characters may be ASCII letters/digits/underscore or any non-ASCII scalar.
The oracle-generated Unicode table pins this classification. Invalid names raise
NameError without writing. Missing/nil conversion diagnoses the original argument
through ordinary inspect, String conversion and native fallback; embedded NUL in
that rendering raises ArgumentError. Saved target/value identity survives callbacks.
Aliases, visibility, super and undef use the native method entry. Non-UTF-8 names
and high-byte binary diagnostic renderings remain explicit gates. **[V]** (L294)

A constant rescue target (`rescue => E`) also writes through this protocol in the
lexical namespace. `$!` already contains the rescued exception during the hook,
and the handler begins only after it returns. A hook failure or frozen target
therefore skips the handler while preserving ordinary ensure/unwinding behavior.
**[V]** (L292)

A method carries the cref of where it was *defined*, not its dispatch owner —
which is what makes `def self.m` inside a module resolve constants correctly.
Top-level nesting is empty; Object is a fallback, not an extra lexical ancestor
that could beat a superclass constant. A qualified class body adds that class to
the actual surrounding lexical nesting, without adding the path's container.
Block eval keeps that nesting for constants and class declarations while rebinding
the target of def/alias/undef. New class declarations check the frozen state of
their constant namespace; reopening an existing nested class does not write a new
constant. **[V]**

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

For `&e`, receiver, arguments and keywords are evaluated before `e`. A Proc passes
through unchanged and `nil` supplies no block. Otherwise the model calls the resolved
`to_proc`, including private methods, and requires a Proc result. A lookup miss follows
checked conversion through response hooks and `method_missing`; a missing conversion
raises TypeError. Continuations preserve the pending call across conversion's side effects,
exceptions and jumps (L275). Native `Symbol#to_proc` supplies a capture-free closure;
overriding or undefining that method changes `&:symbol` accordingly.

### 04 §2 — Calling a closure; arity

`Proc#call`, `Proc#[]`, `Proc#yield` and `Proc#===` use ordinary method lookup, including
singleton/class overrides, aliases, visibility and `undef`. Resolving their native
marker invokes the closure; `super` can resolve the same marker. `f.()` is syntax
for `f.call`, not a separate method named `()` (L272).

Array's `map`/`collect` likewise resolve native entries through ordinary lookup (L274).
They walk the original receiver with a live index, independent of Ruby overrides of
`each`, `length` or `[]`, and collect each block result into a fresh Array. Mutations
before the next yield affect both the next element and exhaustion. Enumerable's separate
Ruby implementation dispatches `each`; removing Array's entry can expose that method.

`for` retains a core node but invokes ordinary explicit `each`, including
visibility, missing-method dispatch, overrides and live iterator mutations. Its
normal value is the return from `each`. A single target takes the first yielded
argument; multiple targets (including `for x,`) expand one argument through checked
`to_ary`, while zero/multiple arguments bind directly. Target writes use ordinary
assignment rules. The hidden callback has a fresh control frame and aliases the
enclosing local environment, preserving new/shared locals, the enclosing block,
match state and definition context without reviving a dead return target. Captured
callbacks can be called, used with block eval, or installed by define_method. **[V]**
(L288)

A block installed by `define_method` keeps that origin even when it has no captured
locals. Its method boundary handles local break/next/return and restarts redo in
the same activation without repeating parameter conversion or defaults. This also
applies to captured for callbacks; strict method arity remains in force. **[V]**
(L288)

Invoking a closure pushes a **block frame** whose parent is `captured`, so free
locals resolve into the enclosing scope. Argument binding differs by
`lambda` **[V]**:

- **non-lambda** (blocks, procs): *lenient*. Missing params bind `nil`, extra args
  are dropped, and a single array argument is **auto-splatted** across multiple
  params. `proc{|a,b| [a,b]}.call(1) == [1, nil]`.
- **lambda**: *strict*, exactly like a method. Wrong arity ⇒ `ArgumentError`, no
  auto-splat.

Nested positional parameters use checked `to_ary`, honoring private methods,
response hooks and missing handlers; actual Arrays bypass conversion. Missing or
nil conversion treats the original as one value, while other non-Array results
raise TypeError. Each expansion snapshots its leading/rest/trailing values before
nested callbacks, pads short inputs with nil, and never reuses consumed leading
values in trailing positions. Each later parameter sees the live heap. Methods
perform positional and keyword defaults before nested conversions; destructured
names are nil during defaults and shadow captured locals in define_method bodies.
Blocks, procs and lambdas share this binding sequence and ordinary unwind rules.
The compiler's synthetic slots cannot collide with Ruby local names. **[V]** (L287)

So `bind` is parameterized by the flag, and method invocation uses the strict
variant. `yield` calls the *current method frame's* block without naming it, with
non-lambda binding, and raises `LocalJumpError` when there is none.
`block_given?` is that block being present. **[V]**

Native Object#inspect first performs a checked `instance_variables_to_inspect`
call, honoring response hooks, private dispatch, missing handlers and nonlocal
exits. Nil/missing selects all fields; an Array selects matching Symbol names;
other results raise TypeError without to_ary conversion. It buffers field names
in insertion order after the hook, then reads each field value and the selection
Array live. Nested values use ordinary inspect followed by String coercion. A
continuation resumes buffered rendering. Execution-local `objectInspections`
guards receiver recursion, including nested String conversion, and releases one
guard on callback return or unwinding; the hook runs before that guard. Native
traversal bypasses Ruby instance_variables/get overrides.
Existing-field assignment preserves its insertion position. Pure rendering is
allowed only when these hooks cannot run, and detects cycles before recursing.
Binary non-UTF-8 nested renderings and native Object#inspect on immediate values
remain explicit gates. **[V]** (L289)

Native UTF-8 String inspection escapes non-printing Unicode scalars with
`\uXXXX` or supplementary-plane `\u{XXXXX}` notation. Printability comes from
the pinned CRuby oracle's generated Unicode table, verified against every scalar.
Existing named control escapes, interpolation escaping and binary byte escapes
retain their separate rules. **[V]** (L293)

Native String#b always returns a fresh mutable base String in ASCII-8BIT, including
for already-binary, frozen and subclass receivers. It copies the bytes without
copying ivars/eigenclasses or calling Ruby conversion, copy or initialization hooks.
Aliases and super retain native dispatch. The old exposed __as_binary wrapper is
removed. **[V]** (L296)

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

The executable model records that target in `Closure.breakScope`, with a
fresh token in execution-local `liveBreakScopes` and a `blockCallK` boundary at
the literal call (L284). Closure entry reads the live tokens, independently of
the continuation; the boundary expires its token on normal return or unwinding.
Forwarding the Proc through
initialize, super or another method preserves the original target; a detached
Proc's break raises LocalJumpError. The boundary consumes the targeted transfer
after intervening ensures have run, independently of method return values and
the constructor's discarded initializer result. Lambda break remains local.

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

For Ruby-level raise/fail, the one-argument form first tries checked String
conversion. Otherwise the checked exception method receives zero or one message
argument, and its result must be an Exception. Visibility does not block this
protocol. Exception's singleton exception method constructs directly, independently
of overridden new. The instance method returns self for no argument or self,
otherwise clones through initialize_clone/initialize_copy and replaces the message
without dispatching initialize. Source frozen state is applied after clone hooks.
Metadata/backtrace/cause and singleton copies remain incomplete. **[V]** (L285)

Native VM errors construct through private initialize(message), preserving the
surrounding `$!` and bypassing overridden new/allocate/exception. Native NameError,
NoMethodError and KeyError use direct native initialization instead. FrozenError
renders the class, initializes with a mutable prefix String, then inspects the
receiver and appends to that same String. A callback can replace the exception's
message, mutate/freeze the prefix, or raise before inspection. **[V]** (L286)

An uncaught throw constructs with `(tag, value, "uncaught throw %p")`; its native
initializer delegates the remaining arguments to super and then stores hidden
tag/value metadata. Message rendering inspects the live tag lazily, including
String conversion of a non-String inspect result. Arbitrary printf formats and
non-String format conversion remain gated. **[V]** (L286)

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

### 04 §7 — External iteration and remaining boundaries

**[V]** An Enumerator stores its receiver, method, positional/keyword arguments
and size policy separately from its external cursor. `each` starts a fresh
ordinary dispatch, independent of `next`. The first external resume dispatches
the Enumerator's own `each`, honoring overrides, with a native yield callback.
`next`/`peek` pack zero, one and multiple yielded arguments; their `_values`
variants always return an Array. Peek caches yielded arguments, while feed is
consumed only when execution resumes past that yield. Completion initializes
StopIteration inside the producer's execution context, stores the method result
after that callback, and caches the exception. Later resumes duplicate its live
raw String message and initialize a fresh StopIteration in the caller's context.
Errors reset the producer; nested Enumerators retain separate dynamic exception/
control contexts. StopIteration cause chains and repeated non-String messages
other than nil remain gated. **[V]** (L280, L286)

`rewind` checks the receiver's rewind protocol, including response/missing
hooks, before discarding suspension. It does not execute abandoned `ensure`
bodies. Native Hash iteration cleanup is abandoned too: its insertion lock
remains, even after CRuby's explicit GC. Live/suspended continuations hold normal
Hash locks; abandoned locks are retained separately. Existing Hash values and
deletions remain visible during iteration, and Array cursors reread their
receiver after every yield. **[V]**

Incremental String#scan writes its native caller's match slot. A native external
fiber first resumed from top level shares that lexical match environment;
first resumption from an ordinary method gets a separate slot. A dedicated
`Frame.matchAlias` expresses this without capturing caller locals. Proc bodies
continue to use their own captured lexical match environments. **[V]**

Reentrant resumes, custom method-name/size conversions, copy initialization
hooks/singleton classes, Chain's blockless wrapping/rewind, remaining blockless
prelude iterators and public Fiber APIs are explicit gates. String#scan gates
receiver mutation during a block and high-byte binary receivers. General
Fiber/Thread scheduling remains open.
**[?]** An `ensure` that raises while an exception is already in flight — whose
backtrace wins, and `Exception#cause` chaining.

---

## Mechanization — from these rules to `stepFn`

**Feature loading (L281).** Core boot evaluates `prelude/prelude.rb`; optional
feature bodies remain decoded programs until `require`. A modeled require enters
a fresh top-level frame with `self = main`, `defmod = Object`, empty lexical
nesting and Object as its constant fallback. The caller's locals and namespace do
not become the feature's.
The heap, globals and effects remain shared. **[V]**

The machine distinguishes loading, completed and attempted features. A completed
or recursively loading feature returns false; successful execution records the
feature and returns true. An escaping exception clears only its loading state:
effects survive, and a later require retries. Attempted-feature API inventories
remain available after a failure so missing dependency APIs cannot become false
negative constant or method answers. These lists stay shared across Enumerator
suspension. **[V]** (cache, scope and unwind are compared to CRuby with identical
small feature bodies; the modeled optional libraries remain partial.)

`json`, `uri`, `forwardable`, `sorbet-runtime` and the `pathname.rb` wrapper have
registered bodies; `.rb` aliases share a cache key. CRuby 4.0.5 already loads
`pathname.so` at startup, so Pathname belongs to core boot. JSON installs its real
generator mixin hierarchy. Standalone execution begins without JSON; the
differential adapter passes `--preload-json` because its control wrapper requires
JSON before the program. **[V]**

Filesystem resolution, `require_relative`, feature path conversion, loader-global
paths/mutation and unknown libraries remain explicit gates. Partial library
bodies gate user definition hooks and frozen target namespaces when omitted
upstream declarations would change the callback order or first failing write.
Forwardable's L282 body matches the 1.4.0 method declarations and order, so its
method hooks and frozen writes execute normally, including failed-load retry.
Its source generator emits real RubyCore definitions with argument, keyword and
block forwarding for simple method, ivar and constant accessors. General accessor
expressions, source-position warning paths and source-generator overrides remain
explicit gates. This compiler is specific to Forwardable, not general string eval.
Existing class/module conflicts gate when their diagnostic requires
the original source position. This does not claim full standard-library or
Sorbet-runtime conformance.

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
