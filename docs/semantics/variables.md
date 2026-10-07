# 03 — Variables, scope and constants

Five namespaces. The recurring theme: *dynamic* things key off `self`/`locals`,
*lexical* things key off `cref`/`defmod`, captured at the definition site.

## §1 — The five namespaces

| Form | Stored in | Scope | Undefined read |
|---|---|---|---|
| `x` | `φ.locals` | lexical block/method scope | `NameError` (as a bareword) |
| `@x` | `H(self).ivars` | the current object | `nil` |
| `@@x` | class hierarchy (§4) | the class + subclasses | `NameError` |
| `$x` | a global table | everywhere | `nil` (warns) |
| `C_n` | a module's `consts` (§5) | lexical + ancestor | `NameError` |

The asymmetry — ivar and global reads default to `nil`, locals/constants/cvars
raise — is itself a semantic fact to encode.

## §2 — Locals

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

## §3 — Instance variables

`@x` reads and writes `H(self).ivars`. There is **no declaration**; an unset `@x`
reads as `nil`, no error. Because `self` is dynamic, the same method body touches
different objects' ivars on different calls — ivars are per-object, keyed by the
runtime `self`, never lexical.

## §4 — Class variables

`@@x` is shared across an entire hierarchy: a `@@x` in a superclass is the *same
slot* seen by subclasses and by instance methods. **[V]** Resolution walks from
the innermost ordinary lexical class/module up its ancestor chain for an existing
`@@x`, creating it there if there is none; an undefined read is a `NameError`.
Singleton-class scopes are skipped. With no enclosing class/module, reads and
writes raise RuntimeError even inside a Proc or method; defined? can still inspect
Object's class variables. Block eval retains this lexical scope. **[V]** This
shared-mutable-across-hierarchy behavior is a notorious footgun and differs from
ivars, so it has to be modeled exactly.

## §5 — Constants: the two-phase lookup

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
core prelude boot suppresses const_added. **[V]**

Namespace paths distinguish temporary names from permanent ones. Binding under
Object or an already permanent namespace promotes the value and its live nested
namespaces before const_added. Existing permanent names survive aliases; naming
does not traverse inherited constants, emit descendant callbacks or reject frozen
descendants. Ancestor cycles stop at the newly named ancestor. Temporary parents
give only a first temporary path and do not rename descendants. Native class paths
are distinct from singleton-class display names; Object-qualified declarations
still acquire bare top-level names. Shared descendants whose chosen path depends
on CRuby's symbol-table iteration order remain gated. **[V]**

Native `Module#name` returns a frozen base String cached by native path and
encoding tag. Repeated reads and distinct namespaces bearing the same path share
identity; permanent promotion selects a new cached value without mutating saved
temporary-name Strings. Anonymous namespaces return nil. ASCII temporary paths
are binary; non-ASCII paths are UTF-8. Permanent ASCII paths retain the existing
US-ASCII/UTF-8 observation boundary. Ruby String constructors/freezing hooks do
not run, and `Module#to_s`/`inspect` still return fresh mutable display Strings.
This name cache does not implement general String#-@ interning. **[V]**

Native `Module#const_set` checks arity, then converts its name through checked
`to_str` unless it is already a Symbol or String. Conversion and name validation
precede the frozen check. UTF-8 names require an uppercase/titlecase first scalar;
later characters may be ASCII letters/digits/underscore or any non-ASCII scalar.
The oracle-generated Unicode table pins this classification. Invalid names raise
NameError without writing. Missing/nil conversion diagnoses the original argument
through ordinary inspect, String conversion and native fallback; embedded NUL in
that rendering raises ArgumentError. Saved target/value identity survives callbacks.
Aliases, visibility, super and undef use the native method entry. Non-UTF-8 names
and high-byte binary diagnostic renderings remain explicit gates. **[V]**

A constant rescue target (`rescue => E`) also writes through this protocol in the
lexical namespace. `$!` already contains the rescued exception during the hook,
and the handler begins only after it returns. A hook failure or frozen target
therefore skips the handler while preserving ordinary ensure/unwinding behavior.
**[V]**

A method carries the cref of where it was *defined*, not its dispatch owner —
which is what makes `def self.m` inside a module resolve constants correctly.
Top-level nesting is empty; Object is a fallback, not an extra lexical ancestor
that could beat a superclass constant. A qualified class body adds that class to
the actual surrounding lexical nesting, without adding the path's container.
Block eval keeps that nesting for constants and class declarations while rebinding
the target of def/alias/undef. New class declarations check the frozen state of
their constant namespace; reopening an existing nested class does not write a new
constant. **[V]**

## §6 — Globals

`$x` reads and writes one global table; unset reads yield `nil`. A handful are
special and are modeled as explicit fields rather than table entries: `$!` on the
machine, and `$~` (with `$1`…`$9`, `` $` ``, `$'` as views of it) **per frame** —
CRuby keeps the last match frame-local, so a callee's match is invisible to its
caller. Prelude methods standing in for CRuby C functions (`String#sub`/`#gsub`/
`#index`, `Regexp.last_match`) write the *caller's* slot.
