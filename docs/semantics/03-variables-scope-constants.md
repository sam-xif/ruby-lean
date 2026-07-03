# RubyCore Semantics — 3: Variables, Scope, and Constant Resolution

> Notation: `00-notation-and-syntax.md`. Frames carry `self`, `locals`, `defmod`, `cref`.

Ruby has **five variable namespaces**, each with its own storage and scoping rule. The
recurring theme (artifact 00 §2): *dynamic* things key off `self`/`locals`, *lexical*
things key off `cref`/`defmod` — captured at definition site, not call site. All
behaviors verified against CRuby 4.0.5 unless marked.

---

## 1. The five namespaces at a glance

| Form | Namespace | Stored in | Scope | Undefined read |
|------|-----------|-----------|-------|----------------|
| `x` | local | `φ.locals` | lexical block/method scope | `NameError` (as bareword) |
| `@x` | instance | `H(self).ivars` | the current object | `nil` (no error) |
| `@@x` | class | class hierarchy (§4) | the class + subclasses | `NameError` |
| `$x` | global | global table `G` | everywhere | `nil` (warns) |
| `C_n` | constant | module's `consts` (§5) | lexical + ancestor | `NameError` |

The asymmetry — instance/global reads default to `nil`, but locals/constants/class-vars
raise — is itself a semantic fact to encode.

---

## 2. Local variables

Locals live in `φ.locals`. Two subtleties dominate:

**(a) Reads and calls are syntactically ambiguous.** `foo` is a local-variable read *if*
`foo` was assigned earlier in the same lexical scope (the parser tracks this); otherwise
it desugars to `send self :foo []`. This is why an undefined bareword gives
`"undefined local variable or method 'foo'"` — the runtime tried the method send and it
`method_missing`'d to `NoMethodError`, reported as `NameError`'s subclass. **[V]**

```
        x ∈ dom(φ.locals)                         x ∉ dom(φ.locals)
      ─────────────────────  (LVAR)             ──────────────────────────  (LVAR-ASSEND)
      ⟨ lvar x ⟩ → φ.locals[x]                  ⟨ lvar x ⟩ ⇝ ⟨ send self x [] ⟩

        (desugaring decision is made by the parser, using lexical assignment info —
         we thread an "assigned-locals" set through desugaring, artifact 00 §5)
```

**(b) Blocks close over enclosing locals; methods do not.** A method body starts with a
fresh `locals` (only its params). A block *shares* the enclosing frame's locals — it can
read and mutate them. **[V]** `x=1; [1].each{ x=99 }; x == 99`.

Block parameters shadow; and block-locals declared after `;` are fresh:

```
  x=1; [5].each{|y; x| x=99 }; x == 1        # the `; x` makes x block-local  [V]
```

So a block's `locals` is a *chained* environment: `[own block-locals+params] → enclosing φ.locals`.
Model as an explicit parent pointer, resolving reads/writes to the nearest binding.

```
  resolve_lvar(φ, x) = φ.locals[x]  if present, else resolve_lvar(φ.parent, x)   (blocks only)
```

Method frames have no `parent` (`self`/locals do not leak across a `def`).

---

## 3. Instance variables

`@x` reads/writes `H(self).ivars`. There is **no declaration**; an unset `@x` reads as
`nil` (no error, though modern Ruby may warn). **[V]** Even `nil`, integers, etc. can
carry ivars conceptually, but immediates are frozen so writes fail.

```
        H ⊢ self : _ , self = ref o , @x ∈ dom(H(o).ivars)
      ──────────────────────────────────────────────────────  (IVAR)
        ⟨ ivar @x ⟩  →  H(o).ivars[@x]

        @x ∉ dom(H(o).ivars)
      ──────────────────────────────────────  (IVAR-UNSET)
        ⟨ ivar @x ⟩  →  nil
```

Because `self` is dynamic, the *same* method body touches different objects' ivars on
different calls — ivars are per-object, keyed by the runtime `self`, never lexical.

---

## 4. Class variables

`@@x` is shared across an entire class hierarchy: a `@@x` defined in a superclass is the
*same slot* seen by subclasses and by instance methods. **[V]**

```
  class P; @@c = 0; def self.inc; @@c += 1; end; end
  class C < P; end
  P.inc; C.inc                 # both bump the SAME @@c
  P.get == 2
```

Resolution walks from the current `defmod` up the superclass chain to find an existing
`@@x`; if none exists, it is created on the current `defmod`. Reading an undefined `@@x`
is a `NameError`. This shared-mutable-across-hierarchy behavior is a notorious footgun
and must be modeled exactly (it differs from ivars, which are per-object).

```
        cvowner = nearest module in (defmod :: superchain(defmod)) with @@x defined
      ──────────────────────────────────────────────────────────────────────  (CVAR)
        ⟨ cvar @@x ⟩  →  cvars(cvowner)[@@x]         (NameError if none)
```

**[?]** Ruby raises `RuntimeError` on ambiguous class-variable access when the variable
is defined in both a class and a descendant that reopens it inconsistently; pin by test.

---

## 5. Constants — the two-phase lookup

Constant resolution is the subtlest scoping rule in Ruby and the one Rails' autoloading
bends hardest. Resolution of an *unqualified* `C_n` proceeds in two phases:

1. **Lexical scope** — search `Module.nesting` (`φ.cref`): the chain of lexically
   enclosing `module`/`class` bodies, innermost first. This is captured at definition
   site and is **not** the ancestor chain.
2. **Ancestor scope** — if not found lexically, search the ancestors of the
   *innermost* lexical class (`cref` head): its superclass chain and included modules.
3. Else `const_missing` is sent (Rails autoloading hooks here), whose default raises
   `NameError`.

Lexical beats ancestor **[V]**:

```
  C = "top"
  module Outer
    C = "outer"
    class Inner < Base          # Base does NOT define C
      def look; C; end          # sees Outer::C == "outer" via lexical scope
    end
  end
  Outer::Inner.new.look == "outer"
```

Ancestor lookup applies only when lexical fails **[V]**:

```
  class Base2; X = "fromBase"; end
  class Sub2 < Base2; def look; X; end; end
  Sub2.new.look == "fromBase"        # X found via Sub2's ancestors
```

`Module.nesting` is lexical, not dynamic **[V]**: nesting reflects the textual
`module A; module B; …` structure (`[A::B, A]`), independent of where methods are called
from.

```
        φ.cref = [n₀, n₁, …]                       -- lexical nesting, innermost first
        lex = first nᵢ with C_n ∈ dom(consts(nᵢ))
      ─────────────────────────────────────────────────────────  (CONST-LEX)
        H; φ ⊢ const C_n ⇓ consts(lex)[C_n]

        no lexical hit
        anc = first a ∈ ancestors(cref-head) with C_n ∈ dom(consts(a))
      ─────────────────────────────────────────────────────────  (CONST-ANC)
        H; φ ⊢ const C_n ⇓ consts(anc)[C_n]

        no lexical or ancestor hit
      ─────────────────────────────────────────────────────────  (CONST-MISS)
        H; φ ⊢ const C_n  ⇝  ⟨ send (cref-head) :const_missing [sym C_n] ⟩
```

A **qualified** constant `A::B` skips the lexical phase: it evaluates `A` to a module and
searches only that module's own consts + ancestors (with a top-level fallback quirk that
warns). Assignment `C_n = e` (`casgn`) always writes to the innermost lexical module
(`cref` head). Constants are reassignable (with a warning) — not truly immutable. **[V]**

**Why this matters for Rails.** ActiveSupport/Zeitwerk autoloading is implemented as
`const_missing`/`Module#autoload` hooks (rule CONST-MISS is the entry point) that
`require` a file and define the constant, then retry. Our model treats autoloading as an
observable effect layered on CONST-MISS — the core rule is unchanged; the library layer
supplies the hook (PROJECT_PLAN §4).

---

## 6. Globals

`$x` reads/writes a single global table `G`, shared everywhere; unset reads yield `nil`
(with a warning). A handful are special (`$~`, `$1`…, `$stdin`, `$!`); several are
read-only or thread/frame-local (`$~` and `$1` are *frame-local* — set by the last regex
match in the current method). Those special globals are modeled explicitly as fields of
the config or frame, not the generic table. **[?]** enumerate the special-globals set
during mechanization.

---

## 7. Open questions

- **[?]** Interaction of `casgn` with re-opened modules and the exact `const_missing`
  retry protocol (does the retry re-run the full two-phase lookup?).
- **[?]** `defined?(x)` returns a *string tag* ("local-variable", "method",
  "constant", "expression", or `nil`) without evaluating side effects — needs its own
  non-evaluating judgment.
- **[?]** Frame-locality of `$~`/`$1` and their propagation into blocks vs methods.
