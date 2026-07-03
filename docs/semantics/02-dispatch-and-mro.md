# RubyCore Semantics — 2: Method Dispatch and the Ancestor Chain

> Notation: `00-notation-and-syntax.md`. Object/class representation: `01-object-model.md`.

This is the heart of the semantics. Every operator, attribute access, DSL macro, and
Rails callback is a `send`, so **one dispatch rule carries most of the language**. All
behaviors below verified against CRuby 4.0.5 unless marked otherwise.

---

## 1. The ancestor chain (MRO)

Each class object stores only its *directly* defined methods (artifact 01). Resolution
walks a linearized `ancestors` list. Ruby's linearization is simpler than C3 (it is a
depth-order insertion, not full C3 merge) and is fully determined by four operations:
`superclass`, `include`, `prepend`, and `extend`.

`ancestors(k)` is built by these insertion rules:

```
  ancestors(BasicObject) = [BasicObject]

  ancestors(k) =  prepends(k) ++ [k] ++ includes(k) ++ ancestors(superclass(k))
```

where `prepends(k)` / `includes(k)` are the modules mixed in via `prepend`/`include`,
each *itself* expanded to its own ancestor list, and **later mix-ins take precedence**
(are placed nearer the front of their group). Duplicates already present earlier in the
list are skipped (a module appears once).

Verified shapes **[V]**:

```
  class B < A; include M; prepend P; end
      B.ancestors == [P, B, M, A, Object, Kernel, BasicObject]

  class D; include M1; include M2; end          # last include wins
      D.ancestors == [D, M2, M1, Object, Kernel, BasicObject]
```

So: `prepend`ed modules sit **above** the class, `include`d modules sit **below** it
(above the superclass), and within a group the most-recently-added is closer to the
class. `extend M` on an object is exactly `include M` into that object's eigenclass.

We formalize with an auxiliary that expands a mix-in list, front-to-back, skipping
already-present modules:

```
        expand(H, [])            = []
        expand(H, mod :: rest)   = dedup( ancestors(H, mod) ++ expand(H, rest) )

        pre = expand(H, reverse (prepends k))        -- reverse: last-added first
        inc = expand(H, reverse (includes k))
        up  = ancestors(H, superclass k)   (or [] if none)
      ─────────────────────────────────────────────────────────────────────  (ANCESTORS)
        H ⊢ ancestors(k)  =  dedup( pre ++ [k] ++ inc ++ up )
```

**[?]** Ruby ≥3.0 lets you `include` a module *after* it's already in the chain and it
re-inserts under specific conditions; and re-`prepend` interacts subtly. We pin exact
behavior by differential testing rather than trusting this sketch at the edges.

---

## 2. Method lookup

Lookup starts at the receiver's **direct class** (`H ⊢ v : k`, artifact 01 §4 — the
eigenclass if one exists) and returns the first module in `ancestors(k)` that defines
the name directly:

```
        H ⊢ v : k        H ⊢ ancestors(k) = [k₀, …, kₙ]
        j = least index with  m ∈ dom(methods(k_j))
      ─────────────────────────────────────────────────────────  (LOOKUP-FOUND)
        H; φ ⊢ lookup(v, m) = (k_j, methods(k_j)[m])

        H ⊢ v : k        H ⊢ ancestors(k) = k̄
        ∀ kⱼ ∈ k̄.  m ∉ dom(methods(kⱼ))
      ─────────────────────────────────────────────────────────  (LOOKUP-NONE)
        H; φ ⊢ lookup(v, m) = ⊥
```

The resolved `(owner, M)` pair carries the **owner** module — essential for `super`
(§4), which must resume the search *after* `owner`, not after the receiver's class.

---

## 3. The send rule and `method_missing`

```
        (value of e_recv) = v
        H; φ ⊢ lookup(v, m) = (owner, M)
        visible(M, callsite, v)                        -- §5
      ─────────────────────────────────────────────────────────  (SEND-INVOKE)
        ⟨ send e_recv m [ā] blk ⟩  →  invoke(owner, M, v, ā, blk)

        H; φ ⊢ lookup(v, m) = ⊥        m ≠ :method_missing
      ─────────────────────────────────────────────────────────  (SEND-MM)
        ⟨ send e_recv m [ā] blk ⟩  →  ⟨ send e_recv :method_missing [sym m, ā…] blk ⟩

        H; φ ⊢ lookup(v, :method_missing) = ⊥          -- only BasicObject's default left
      ─────────────────────────────────────────────────────────  (SEND-NME)
        ⟨ send … m … ⟩  →  ^exc(NoMethodError)
```

`invoke` (detailed in artifact 05) pushes a new frame `φ'` with `self := v`,
`defmod := owner`, binds params to args, installs the block, and evaluates the body.
The `owner`/`defmod` distinction is what makes `super` work.

**method_missing is not magic** — it is an ordinary method whose *default*
(`BasicObject#method_missing`, a builtin) raises `NoMethodError`. Overriding it (as
ActiveRecord does for dynamic finders/attributes) just shadows the default in the
ancestor chain. `respond_to?` similarly dispatches, and its default consults defined
methods plus `respond_to_missing?` **[V]**:

```
  class G; def method_missing(n,*a); "mm:#{n}"; end
           def respond_to_missing?(n,inc=false); n==:zzz; end; end
      G.new.anything            == "mm:anything"
      G.new.respond_to?(:zzz)   == true
      G.new.respond_to?(:qqq)   == false
```

This is the single most important interaction to get right for Rails (PROJECT_PLAN §4).

---

## 4. `super`

`super` re-dispatches the *same method name* starting after the current method's owner.
Two surface forms desugar differently:

- **bare `super`** — forwards the *current method's arguments* (the caller's actual
  args, re-read from the current frame's params). **[V]** `Q#m(a,b) = super` on
  `m(1,2)` yields `[1,2]`.
- **`super(...)`** — forwards exactly the given args (including `super()` = none).

```
        φ.kind = method invoking m, with owner = own, self = v, current args = ā
        H ⊢ v : k        H ⊢ ancestors(k) = k̄
        k̄' = tail of k̄ strictly after own
        least j with m ∈ dom(methods(k̄'[j]))  ⇒  (own', M')
      ─────────────────────────────────────────────────────────────────────  (SUPER)
        ⟨ super args? ⟩  →  invoke(own', M', v, (args? ? args : ā), φ.block)

        (no such j)
      ─────────────────────────────────────────────────────────  (SUPER-NONE)
        ⟨ super … ⟩  →  ⟨ send self :method_missing [sym m, …] ⟩   -- then NoMethodError
```

Crucially the search key is `own` (the defining module), *not* `v`'s class — this is why
searching resumes correctly through `prepend`ed modules **[V]**:

```
  module P; def greet; "P->" + super; end; end
  class C; prepend P; def greet; "C"; end; end
      C.new.greet == "P->C"           # P is above C, so P#greet's super finds C#greet
```

---

## 5. Visibility

Each `MethodDef` has visibility `public | private | protected` (artifact 01). Visibility
is checked at the *call site*, against how the method is called:

```
  public     : callable with any receiver.
  private    : callable only with an implicit receiver (no `e_recv`), OR — since Ruby 2.7 —
               with a literal `self` receiver (`self.foo`, incl. setters `self.x=`).  [V]
  protected  : callable with an explicit receiver ONLY IF the current `self` is_a? the
               method's owner (peer access).
```

```
        M.visibility = private        callsite has explicit receiver e_recv ≠ self-literal
      ─────────────────────────────────────────────────────────────────────  (VIS-PRIV-ERR)
        ⟨ send e_recv m … ⟩  →  ^exc(NoMethodError "private method 'm' called")

        M.visibility = protected      ¬ (H ⊢ φ.self : k'  ∧  owner(M) ∈ ancestors(k'))
      ─────────────────────────────────────────────────────────────────────  (VIS-PROT-ERR)
        ⟨ send e_recv m … ⟩  →  ^exc(NoMethodError)
```

Verified **[V]**: `self.val = 5` inside `initialize` works even when `val=` is private;
calling a `private` method with an explicit non-self receiver raises
`"private method 'sekret' called"`.

Note visibility affects **only** dispatch admissibility, never lookup — a private method
is still *found*; it's the call that's rejected. `send`/`__send__` bypass private;
`public_send` does not.

---

## 6. Why this design pays off

Every metaprogramming feature reduces to *mutating `methods`/`ancestors`/`eigen` in the
heap*, after which these same rules apply unchanged:

| Feature | Heap effect | Then dispatch is ordinary |
|--------|-------------|---------------------------|
| `define_method(:m){…}` | insert `m` into current class's `methods` | ✓ |
| `attr_accessor :x` | insert `x` and `x=` (desugar, artifact 00 §5) | ✓ |
| `include M` / `prepend M` | extend `includes`/`prepends`, recompute ancestors | ✓ |
| `def obj.m` / `extend M` | allocate eigenclass, insert there | ✓ |
| Rails `belongs_to :a` | define reader/writer/association methods at class-eval time | ✓ |
| Rails dynamic finder `find_by_x` | not defined → `method_missing` handles it | ✓ (rule SEND-MM) |
| `alias`/`alias_method` | copy a `MethodDef` under a new name | ✓ |

No new evaluation rules. This is the concrete cash value of "everything is a message
send" + "classes are heap objects."

---

## 7. Open questions

- **[?]** `refinements` (`using`/`refine`) genuinely perturb lookup *lexically* — they
  add refinement modules consulted before the normal chain, scoped to the activation's
  `cref`. Deferred; will need an extra lookup premise keyed on `φ.cref`.
- **[?]** `prepend` interaction with already-activated `super` chains during
  re-opening; `Module#include?` transitivity; `Comparable`-style modules relying on a
  single method — all to be pinned by differential tests.
- **[?]** `method_added`/`method_removed`/`inherited` hooks fire as side effects of the
  heap mutations above; sequencing them relative to the mutation is observable.
