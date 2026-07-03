# RubyCore Semantics — 1: Object Model, Values and Heap

> Notation and conventions: see `00-notation-and-syntax.md`.

Ruby's slogan is *everything is an object* — including classes, modules, and `nil`.
Getting this representation exactly right is the whole game (PROJECT_PLAN §5.3): once
classes are ordinary heap objects and dispatch is one rule, metaprogramming becomes
heap mutation rather than new evaluation rules. This artifact fixes the value domain,
the shape of objects and classes, object identity, truthiness, and mutation.

Primary source: ISO/IEC 30170:2012 §6 (Objects) and §7 (Classes/Modules); Ruby docs for
`Object`, `Class`, `Module`, `BasicObject`.

---

## 1. Values

A `Value` is what an expression evaluates to. Ruby has no unboxed user-visible values
in principle (everything responds to methods), but for a faithful *and* efficient model
we distinguish immediates from heap references — exactly as CRuby does internally.

```
  Value  v ::=  ref o           reference to a heap object (o : ObjId)
             |  int n           n : ℤ  (arbitrary precision — Integer, incl. former Bignum)
             |  flt x           IEEE-754 double
             |  sym s           interned symbol
             |  true | false | nil
```

**Design note [D].** Modeling `Integer`/`Float`/`Symbol`/`true`/`false`/`nil` as
immediates is an *optimization of the representation*, not a semantic claim that they
aren't objects. Every immediate has a well-defined class (§4) and participates in
dispatch identically to a `ref`. The alternative — allocating a heap object per integer
— is observationally equivalent for a single-threaded deterministic model but wasteful.
We must prove the immediate encoding refines the "everything is a ref" model, OR just
adopt it as primitive and check via differential testing. **[?]** decide during
mechanization.

Consequence to respect: integer/symbol/`nil`/`true`/`false` identity is *value
identity* — `1.equal?(1)` is `true`, `:a.equal?(:a)` is `true`, `nil.equal?(nil)` is
`true`. This falls out for free from immediates.

---

## 2. Objects and the heap

```
  Object  obj ::= {
      class    : ObjId,                      -- the object's direct class (an object itself)
      ivars    : Var ⇀ Value,                -- instance variables @x
      eigen    : Option ObjId,               -- singleton class, allocated lazily (§5)
      frozen   : Bool,
      payload  : Payload                     -- built-in internal state (§3)
  }

  Heap  H ::= ( store : ObjId ⇀ Object , next : ObjId )
```

Allocation `alloc(H, obj) = (o, H')` picks `o = H.next`, sets `H'.store = H.store[o ↦ obj]`,
`H'.next = o+1`. Ids are never reused (matches "no GC in the model", PROJECT_PLAN §4).

A **class object** additionally carries class-specific payload:

```
  ClassPayload ::= {
      superclass : Option ObjId,             -- nil only for BasicObject
      methods    : m ⇀ MethodDef,            -- methods defined *directly* on this module
      consts     : C_n ⇀ Value,              -- constants namespaced here
      cvars      : @@x ⇀ Value,              -- class variables (shared down hierarchy; artifact 03)
      is_module  : Bool,                     -- true for Module, false for Class
      is_singleton : Bool,                   -- true for eigenclasses
      attached   : Option Value              -- for a singleton class, the object it belongs to
  }
```

`MethodDef` records the method's parameters, body, defining module (`owner`, needed for
`super`), and visibility:

```
  MethodDef ::= { params : Params, body : Expr, owner : ObjId,
                  visibility : (public | private | protected),
                  origin : (ruby | builtin bid) }
```

`origin = builtin bid` marks a method whose behavior is given by a primitive rule rather
than a RubyCore body (e.g. `Integer#+`, `Object#object_id`). These are the axiomatized
leaves of the semantics; the modeled-library layer (PROJECT_PLAN §4) supplies their rules.

---

## 3. Built-in payloads

Some core classes carry hidden state that RubyCore expressions can't express directly;
we model it as `Payload`:

```
  Payload ::=  none
            |  str  (bytes : List UInt8, enc : Encoding)     -- String is mutable, encoding-aware
            |  arr  (elems : List Value)                     -- Array
            |  hsh  (entries : List (Value × Value),         -- Hash: *insertion-ordered* [V]
                     default : DefaultSpec)
            |  rng  (lo : Value, hi : Value, excl : Bool)    -- Range
            |  proc (Closure)                                -- Proc/lambda (artifact 05)
            |  meth (bound receiver + MethodDef)             -- Method object
            |  exc  (message : Value, backtrace : …)         -- Exception instances
```

Notes with semantic teeth:
- **String is mutable** and byte-oriented with an attached encoding; `String#<<`,
  `#gsub!` mutate in place. Two equal strings are *not* `equal?`. **[V]**
- **Hash preserves insertion order** for iteration and `#inspect` — this is guaranteed
  since Ruby 1.9 and is observable, so it is part of the spec, not an implementation
  detail. **[V]**
- Frozen string literals (`# frozen_string_literal: true`, default-ish in modern Ruby)
  change identity/mutation behavior; the model tracks `frozen` per object.

---

## 4. The class-of relation

Every value has a class. For immediates it is fixed; for refs it is the object's
`class` field — **unless** the object has an eigenclass, in which case that is its
*direct* class for dispatch purposes (§5, artifact 02).

```
        ────────────────────  (CLASS-INT)      ────────────────────  (CLASS-SYM)
        H ⊢ int n : Integer                     H ⊢ sym s : Symbol

   similarly:  flt x : Float,  true : TrueClass,  false : FalseClass,  nil : NilClass

        H(o).eigen = none                       H(o).eigen = some e
      ──────────────────────  (CLASS-REF)     ──────────────────────  (CLASS-EIGEN)
      H ⊢ ref o : H(o).class                  H ⊢ ref o : e
```

`H ⊢ v : k` reads "the *direct class object* of `v` is `k`". Dispatch (artifact 02)
starts from this `k` and walks `ancestors(k)`.

The bootstrap classes form a fixed initial heap `H₀`:

```
  BasicObject  (superclass = none)
     ▲
  Object       (includes Kernel)
     ▲
  Module ▲ Class     Class < Module < Object
  ...   NilClass, TrueClass, FalseClass, Integer, Float, String, Symbol,
        Array, Hash, Range, Proc, Method, Exception hierarchy, …
```

The metaclass twist [D]: `Class.class == Class`, `Object.class == Class`,
`BasicObject.class == Class`, and `Class < Module < Object < BasicObject`. This
self-referential knot lives entirely in `H₀`; no rule needs to construct it.

---

## 5. Eigenclasses (singleton classes)

Per-object behavior (`def obj.foo`, `class << obj`) is modeled by a **singleton class**
inserted directly above the object in its ancestor chain.

```
        H(o).eigen = none        e ∉ dom(H)
        e_obj = { class = Class, superclass = H(o).class, is_singleton = true,
                  attached = ref o, methods = ∅, … }
      ─────────────────────────────────────────────────────────────────────  (EIGEN-ALLOC)
        eigenclass(H, ref o)  =  (e, H[o ↦ H(o) with eigen := e][e ↦ e_obj])
```

- `def obj.m …` installs `m` into `eigenclass(obj).methods`.
- For a **class** `k`, its eigenclass holds `k`'s *class methods*; and the eigenclass
  chain mirrors the class chain: `eigen(k).superclass = eigen(k.superclass)`. This is
  the rule that makes inherited class methods work. **[V]**
- Immediates (`Integer`, `Symbol`, `nil`, …) **cannot** have an eigenclass —
  `def 1.foo` / `1.singleton_class` raises `TypeError`. The model refuses `EIGEN-ALLOC`
  for non-`ref` values. **[V]**

---

## 6. Identity, equality, truthiness

**Identity.** `object_id` is a stable per-object number; `a.equal?(b)` iff same
identity. For immediates, identity is value identity (§1). The model can use `ObjId`
for `ref`s and a fixed injection for immediates.

**Equality is a method, not a primitive.** `==`, `eql?`, `===`, `<=>` are all sends and
are user-overridable; the semantics never bakes in structural equality except as the
*default* `BasicObject#==` (identity) supplied as a builtin. Hash/Set membership uses
`eql?` + `hash`. This means correctly modeling e.g. `Hash` lookup requires *dispatching*
`eql?`/`hash` on keys — a place where the "library" layer calls back into the core.

**Truthiness is total and simple** [D][V]: exactly `false` and `nil` are falsey; every
other value — including `0`, `""`, `[]` — is truthy.

```
      v ∉ { false, nil }
    ─────────────────────  (TRUTHY)        ───────────────────────  (FALSEY)
        truthy(v)                            ¬ truthy(false) , ¬ truthy(nil)
```

This single fact drives `if`, `while`, `and`/`or`, `&&`/`||`, and `!`.

---

## 7. Mutation and freezing

The heap is mutable; instance-variable assignment and builtin mutators update `H` in
place (they are the *only* reason the semantics is stateful — a pure-value subset would
be much smaller).

```
        H ⊢ v : _        H(o) defined       ¬ H(o).frozen        (v = ref o)
      ─────────────────────────────────────────────────────────────────────  (IASGN)
        ⟨ iasgn @x v-expr … ⟩  →  updates H(o).ivars[@x] := (value of v-expr)

        H(o).frozen = true
      ──────────────────────────────────────────  (FROZEN-ERR)
        mutating H(o)  ↦  ^exc(FrozenError)
```

`freeze` sets `frozen := true` (idempotent, irreversible in-model); `frozen?` reads it;
`dup`/`clone` allocate copies (`clone` copies frozen state and the eigenclass; `dup`
does not — a genuine observable difference **[V]**). Immediates are always frozen.

---

## 8. Open questions

- **[?]** Exact `Float` semantics (NaN, `-0.0`, `Float#==` vs `eql?`) — adopt IEEE-754
  and verify via differential testing rather than axiomatize prematurely.
- **[?]** String encoding coercion rules (`Encoding::CompatibilityError`) — likely
  deferred to the library layer; core keeps bytes+encoding but not the full coercion lattice.
- **[?]** `object_id` allocation scheme must be *deterministic* for the observation
  function (PROJECT_PLAN §6.4) yet must not accidentally make distinct-in-CRuby objects
  compare equal. Use allocation order; verify.
