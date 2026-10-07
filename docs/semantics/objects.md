# 01 — Objects, values and the heap

Getting this representation right is the whole game: once classes are ordinary
heap objects and dispatch is one rule, metaprogramming becomes heap mutation.

## §1 — Values

```
  Value v ::= ref o | int n | flt x | sym s | true | false | nil
```

Modeling `Integer`/`Float`/`Symbol`/`true`/`false`/`nil` as **immediates** is a
representation choice, not a claim that they aren't objects: every immediate has
a class (§4) and dispatches identically to a `ref`. The consequence to respect is
that their identity is *value* identity — `1.equal?(1)`, `:a.equal?(:a)` and
`nil.equal?(nil)` are all `true`, which falls out for free. `Integer` is
arbitrary-precision.

## §2 — Objects and the heap

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
library is written *in Ruby* — see `ruby-lean/prelude/prelude.rb` and
`ruby-lean/prelude/features/`. Method and closure origin follows model library code
through calls; it is separate from the boot-only flag that suppresses callbacks.
Classes opened by library code retain a canonical namespace tag for the generated
API inventories, independently of their Ruby-visible names (including aliases).
An inherited visibility override stores `visibilityOnly` and resolves the current
ancestor body on each lookup. Aliases instead retain the selected body,
`superName`, and (for class/eigenclass aliases) `superScope`; the latter preserves
the lookup context needed when the same module occurs in different class chains. adds `definee`, distinct from the dispatch owner. A `def self.make` inside C
can therefore define an instance method on C when its body executes a nested def.
A define_method body also retains its block's definition-context frame even when
its local-variable capture can be erased; the two kinds of capture are independent.

## §3 — Builtin payloads

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
  Other messages render through checked to_str then to_s calls.
- **Rational** carries a reduced arbitrary-precision numerator and positive
  denominator. It remains a heap object even when the denominator is one.
  Instances are frozen; `dup`, `clone` with nil/true freezing, and `to_r` retain identity.
  A native rational literal bypasses constructor/constant lookup and is cached
  by compilation unit and syntax site; repeated execution of one site shares
  its object, while separate sites and constructor calls remain distinct.
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
  remain explicit fragment gates.

## §4 — The class-of relation

`H ⊢ v : k` is "the *direct class object* of `v` is `k`". For immediates it is
fixed; for a `ref` it is the object's `class` field — **unless** it has an
eigenclass, which is then its direct class for dispatch purposes.

```
  H(o).eigen = none                      H(o).eigen = some e
 ──────────────────── (CLASS-REF)      ──────────────────── (CLASS-EIGEN)
 H ⊢ ref o : H(o).class                 H ⊢ ref o : e
```

Dispatch ([section 02](dispatch.md)) starts from this `k` and walks `ancestors(k)`.

The bootstrap classes are a fixed initial heap **H₀**, including the metaclass
knot — `Class.class == Class`, `Object.class == Class`, and
`Class < Module < Object < BasicObject` **[D]**. The self-reference lives entirely
in H₀ as initial data; no rule has to construct it. `Kernel` and `Numeric` are in
the real ancestor chain so `ancestors` is byte-exact.

## §5 — Eigenclasses

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

## §6 — Identity, equality, truthiness

**Equality is a method, not a primitive.** `==`, `eql?`, `===`, `<=>` are sends
and are user-overridable; the semantics bakes in structural equality nowhere
except as the *default* `BasicObject#==` (identity), supplied as a builtin.
Hash/Set membership therefore *dispatches* `eql?`/`hash` on keys — a place where
the library layer calls back into the core.

**Truthiness is total and simple** **[D][V]**: exactly `false` and `nil` are
falsey; everything else — including `0`, `""`, `[]` — is truthy. This one fact
drives `if`, `while`, `and`/`or` and `!`.

## §7 — Mutation and freezing

The heap is mutable, and ivar assignment plus builtin mutators updating `H` in
place is the *only* reason the semantics is stateful. Mutating a frozen object
raises `FrozenError`. `freeze` is idempotent and in-model irreversible;
`dup`/`clone` allocate copies. Native `clone` accepts `freeze: nil`, `true`, or
`false`; nil preserves the source's live frozen state after the copy hooks return,
true freezes the result, and false leaves the hook's final state alone. Immutable
values return themselves and reject `freeze: false`. Positional arity precedes
keyword validation; unknown keys are inspected and invalid option classes use
Ruby `to_s`. **[V]**

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
**[V]**

Native `dup` checks zero positional arity (a nonempty keyword bundle counts as
one positional Hash), then returns immutable values unchanged or allocates a
mutable copy. It omits the source's eigenclass, including extension modules,
singleton methods and singleton copy hooks. It dispatches private initialize_dup
on the copy, whose default calls initialize_copy; hook results are discarded and
hook freezing is preserved. Core shell allocation/content copying is shared with
clone, without clone's final freeze policy. Aliases and super use the resolved
native entry. Existing namespace/Random and other native custom-copy boundaries
remain explicit. **[V]**
