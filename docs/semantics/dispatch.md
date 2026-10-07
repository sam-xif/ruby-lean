# 02 — Method dispatch

The heart of the semantics. Every operator, attribute access and DSL macro is a
`send`, so **one dispatch rule carries most of the language.**

## §1 — The ancestor chain (MRO)

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

## §2 — Method lookup

Lookup starts at the receiver's **direct class** (§01 §4 — the eigenclass if one
exists) and returns the first module in `ancestors(k)` defining the name
directly; if none does, `lookup = ⊥`. The resolved pair carries the **owner**
module, which is what `super` (§4) resumes the search after — not the receiver's
class.

## §3 — `send` and `method_missing`

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
replaced initializers. **[V]**

New named classes bind their constant before sending `inherited`, and execute
the saved class body only after the callback returns. Reopening does not resend
the callback. Raises retain the binding and earlier effects; a callback replacing
the constant cannot redirect the saved body. Class.new rejects an uninitialized
parent, while named class syntax in CRuby 4.0.5 permits one. Such children retain
an unavailable ancestry index and allocator, even if their parent is initialized
later. CRuby 4.0.5 also permits initializing a frozen allocated class; these rules
are pinned to the executable oracle. Superclass type errors dispatch the selected
class's live to_s, preserving effects, exceptions and non-String fallback. **[V]**


Unnamed Module-subclass instances render through their direct class's temporary
path, including an eigenclass if present. This path uses its name/address rather
than recursively rendering its attachment. Singleton-class to_s itself still
renders the attached object from the live heap. Reflective const_set names an
anonymous class/module just as ordinary constant assignment does. **[V]**

## §4 — `super`

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

## §5 — Visibility

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

## §6 — Why this design pays off

Every metaprogramming feature reduces to mutating `methods` / `ancestors` /
`eigen` in the heap, after which these same rules apply unchanged:

| Feature | Heap effect |
|---|---|
| `define_method(:m){…}` | insert `m` into the current class's `methods` |
| `attr_accessor :x` | insert `x`, run its callback, then insert `x=` |
| `include M` / `prepend M` | extend `includes`/`prepends`, recompute ancestors |
| `def obj.m` / `extend M` | allocate an eigenclass, insert there |
| `alias` / `alias_method` | copy a `MethodDef` under a new name |
| a dynamic finder | not defined → SEND-MM |'s `MethodEdit` queue commits one method-table mutation, then dispatches its
Ruby callback before continuing. Definitions, aliases, define_method and attributes
call `method_added`; remove/undef call `method_removed`/`method_undefined`.
Eigenclass writes call the corresponding `singleton_method_*` on the attached
receiver. Ordinary dispatch preserves private hooks, super and method_missing.
A hook may raise, freeze the target or alter the next method: prior writes remain,
and each remaining write checks the current heap and frozen state. The boot-only
prelude suppresses hooks; runtime library loading does not. **[V]**

## §7 — Open

**[?]** `refinements` genuinely perturb lookup *lexically* — they add modules
consulted before the normal chain, scoped to the activation's `cref`. Deferred;
would need an extra lookup premise keyed on `φ.cref`.
**[?]** Ancestry mutation hooks (`append_features`, `prepended`, `extended`)
still need a complete protocol audit. Constant-name conversion, removal and
recursive temporary namespace naming also remain incomplete; const_added dispatch
is modeled below.
