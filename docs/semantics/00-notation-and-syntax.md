# RubyCore Semantics — 0: Notation and Abstract Syntax

> **Status:** quasi-formal design artifact. This is the semantics we intend to
> mechanize in Lean (see `PROJECT_PLAN.md`). It is deliberately precise but not yet
> Lean code. Behaviors marked **[V]** have been checked against CRuby; **[D]** are
> from documentation; **[?]** are open questions to resolve during mechanization.

This document fixes the meta-notation used across all the semantics artifacts and
gives the abstract syntax of `RubyCore` — the small language that surface Ruby
*desugars into*.

References used throughout the series:
- ISO/IEC 30170:2012 *Information technology — Programming languages — Ruby* (the only
  formal-ish standard; thin and dated, but authoritative for the core object model).
- The official Ruby documentation (`docs.ruby-lang.org`) and `ruby/spec` executable suite.
- Plotkin-style structural operational semantics (SOS) conventions; the
  Python (arXiv:2109.03139) and KRust (arXiv:1804.10806) executable-semantics papers as
  structural templates.

---

## 1. Design stance

We give a **small-step structural operational semantics** over an explicit machine
configuration. Small-step (rather than big-step) is chosen because Ruby's observable
behavior depends on the *order and interleaving of effects* and on *non-local control*
(`ensure` ordering, `break`/`return` from blocks, exception propagation), which big-step
rules hide. See `PROJECT_PLAN.md` §7 for why the relation, not the interpreter, is the
definition of record.

**Everything is a message send.** Wherever Ruby *could* be desugared to a method call,
we do so (§4). This concentrates the semantics into one dispatch rule (artifact 02) and
makes metaprogramming ordinary heap mutation rather than new evaluation rules.

---

## 2. Machine configuration

A configuration `C` is a tuple:

```
  C  ::=  ⟨ K , H , Ξ ⟩            normal (executing) state
       |  ⟨ K , H , Ξ ⟩^exc(v)     exceptional state carrying raised value v (an ObjId)
```

- `K` — the **control**: an expression under focus plus its continuation. We use an
  explicit continuation stack (a *frame stack*) rather than evaluation contexts, because
  Ruby's non-local exits need to *inspect and unwind* the stack (artifact 04).
- `H` — the **heap**: a finite map `ObjId ⇀ Object` plus a fresh-id counter (artifact 01).
- `Ξ` — the **frame stack** (call stack): a list of activation frames, innermost first.

An activation **frame** `φ` carries the dynamic + lexical context of a running method
or block:

```
  φ  ::=  {
            self    : Value,             receiver / current self
            locals  : Var ⇀ Value,       local variable bindings (incl. block params)
            defmod  : ObjId,             module lexically enclosing the def (for `super`, consts)
            cref    : List ObjId,        lexical constant/nesting scope (Module.nesting)
            block   : Option Value,      block passed to this activation (a Proc or nil)
            kind    : method | block | toplevel | class-body
            handlers: List Handler       active rescue/ensure for this frame (artifact 04)
          }
```

The split between `defmod`/`cref` (lexical, captured at definition site) and
`self`/`locals` (dynamic, established at call site) is essential and recurs everywhere.

### Observation function

Differential testing (PROJECT_PLAN §6) compares an **observation** `obs(C)`, not raw
configs. We fix:

```
  obs(C) = ( stdout-trace ,
             result-repr  = inspect(final value) ,
             exc-repr     = (class-name, message) if C is ^exc, else ⊥ ,
             heap-proj    = canonical dump of reachable objects' ivars )
```

Two configs are *observationally equal* iff their `obs` agree. "The model explains a
behavior" means: there is a derivation `C₀ →* C` in the step relation with the matching
`obs(C)`.

---

## 3. Metavariables and judgments

| Metavar | Ranges over |
|--------|-------------|
| `x`, `y` | local variable names |
| `@x` | instance variable names; `@@x` class variables; `$x` globals |
| `m` | method names (symbols) |
| `C_n` | constant names (capitalized) |
| `v`, `w` | runtime values (`Value`, artifact 01) |
| `o`, `k` | object ids (`ObjId`); `k` when it's a class object |
| `e` | RubyCore expressions (§4) |
| `H`, `Ξ`, `φ` | heap, frame stack, frame |

The primary judgment is the small-step transition:

```
        C  →  C'
```

read "configuration `C` steps to `C'`". Its reflexive-transitive closure is `→*`.
Auxiliary judgments (defined in later artifacts) use named turnstiles, e.g.:

```
  H ⊢ v : k                     v is a direct instance of class object k        (01)
  H ⊢ ancestors(k) = k̄          MRO of k is the list k̄                           (02)
  H; φ ⊢ lookup(v, m) = (k, M)  dispatch of m on v resolves to method M in k     (02)
  H; φ ⊢ const C_n ⇓ v          constant C_n resolves to v                       (03)
```

Rules are written in the usual inference-rule style:

```
        premise₁      premise₂      …
      ─────────────────────────────────  (RULE-NAME)
                conclusion
```

We write `H[o ↦ obj]` for heap update, `H(o)` for lookup, and `o ∉ dom(H)` /
`H, o:obj` for allocation of a fresh id.

---

## 4. Abstract syntax of RubyCore

Surface Ruby is desugared into the following core. The desugarings themselves are
listed in §5; they are ordinary total functions (independently testable).

```
Expr  e ::=
        -- values / literals
        | lit ℓ                                   integer, float, string, symbol, true, false, nil
        | self                                    current receiver
        | array [e, …]                            (desugars further; see §5)
        | hash  [(e ⇒ e), …]

        -- variables (one form per namespace)
        | lvar x            | lasgn x e            local read / write
        | ivar @x           | iasgn @x e           instance var read / write
        | cvar @@x          | cvasgn @@x e         class var read / write
        | gvar $x           | gasgn $x e           global read / write
        | const C_n         | casgn C_n e          constant read / write (scoped; artifact 03)

        -- THE core primitive: message send
        | send  e_recv m [e_arg, …] blk?          e_recv.m(args) { blk }
        | send  self  m [e_arg, …] blk?  (implicit self when e_recv absent)

        -- blocks / callables
        | blockarg params e_body                   the { |params| body } attached to a send
        | yield [e_arg, …]                          yield to the current frame's block
        | lambda params e_body                      ->(params){ body } (lambda-flavored proc)

        -- definitions (evaluate to a symbol / the class; mutate the heap)
        | def m params e_body                       define instance method on current defmod
        | defs e_recv m params e_body               def obj.m … (singleton method)
        | class C_n e_super? e_body                 class definition / reopening
        | sclass e_recv e_body                      class << obj … (singleton class body)
        | module C_n e_body

        -- control flow
        | seq e e                                   e₁ ; e₂
        | if e_cond e_then e_else
        | while e_cond e_body                        (until desugars to while ¬)
        | begin e_body rescues ensure?              exception handling (artifact 04)
        | return e?    | break e?    | next e?
        | redo         | retry
        | and e e      | or e e      | not e         short-circuit (desugar to if; §5)

  params  p ::= [ req x, … ; opt (x = e), … ; splat x? ; kwreq k, … ; kwopt (k=e), … ; kwsplat k? ; block &b? ]
  rescue    ::= rescue [C_n, …] => x? e_handler
```

Notes:
- There is **no separate operator syntax**: `a + b`, `a[i]`, `a[i] = v`, `-a`, `a == b`
  are all `send`. Assignment to a variable is a distinct form (it binds, it does not
  dispatch), but `[]=` and `attr=` are sends.
- `def`/`class`/`module` are *expressions with effects*: they mutate `H` (installing
  methods/classes) and return a value (a Symbol for `def`, the class body's last value).
- A `blockarg` is not a first-class expression on its own; it rides along on a `send`.
  Reifying it into a `Proc` object happens at the dispatch boundary (artifact 05).

---

## 5. Desugarings (surface → RubyCore)

Each is a syntactic function applied before evaluation. Representative set:

| Surface | Desugars to |
|--------|-------------|
| `a + b`, `a * b`, `-a`, `a < b`, `a == b` | `send a :+ [b]`, … , `send a :-@ []` |
| `a[i]` / `a[i] = v` | `send a :[] [i]` / `send a :[]= [i, v]` |
| `a.b ||= c` | `a.b || (a.b = c)` then each `.b`/`.b=` → sends |
| `x ||= e` / `x &&= e` | `x || (x = e)` / `x && (x = e)` (var form: read may be nil-init) |
| `"...#{e}..."` | `send (send e :to_s []) :+ [...]` chain |
| `attr_accessor :x` | `def x () ivar @x` **and** `def x= (v) iasgn @x (lvar v)` |
| `a && b` / `a || b` | `if a then b else a` / `if a then a else b` (value-preserving) |
| `unless c then …` | `if (not c) then …` |
| `until c do …` | `while (not c) do …` |
| `for v in e do …` | `send e :each [] (blockarg [req v] …)` |
| `case x when P …` | chain of `if (send P :=== [x]) …` |
| keyword/optional args | normalized into the `params` record above |
| string/array/hash literals | `send Array :[] …` style constructors over `lit`s |

Open desugaring questions **[?]**: pattern matching (`case/in`, Ruby 3+), one-line
pattern `=>`, endless methods (`def f = e`), and `&.` safe-navigation (desugars to a
nil-guarded `if`, but the *evaluation-once* semantics of the receiver must be preserved).

---

## 6. What is intentionally excluded

Consistent with PROJECT_PLAN §4, the core omits (models as opaque/axiomatic where a
Rails slice needs them): C extensions/FFI, `Ractor`/threads' true memory model, `Fiber`
scheduling, GC-observable behavior and `ObjectSpace`, `eval` of arbitrary strings,
`TracePoint`, `set_trace_func`, and `binding` reification beyond what closures need.
`refinements` are deferred (they perturb dispatch; artifact 02 notes the hook).
