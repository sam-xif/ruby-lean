# RubyCore Semantics — 4: Blocks, Procs/Lambdas, and Non-Local Control Flow

> Notation: `00-notation-and-syntax.md`. This artifact is where the choice of
> *small-step + explicit frame stack* (artifact 00 §1–2) earns its keep: every rule here
> is about inspecting and unwinding `Ξ`. All behaviors verified against CRuby 4.0.5.

---

## 1. Closures: blocks, procs, lambdas

All three are the same runtime thing — a `Proc` object wrapping a **closure** — differing
in two boolean-ish attributes: `lambda?` and how they were created.

```
  Closure ::= {
      params   : Params,
      body     : Expr,
      captured : Frame,          -- the DEFINING frame: self, locals (by reference!), cref, defmod, block
      lambda   : Bool
  }
```

`captured` is the enclosing frame *by reference* — this is why a block mutating an outer
local is visible after the block runs (artifact 03 §2). A `Proc` is `alloc`'d with
`payload = proc(Closure)`.

Creation forms:
- `{ … }` / `do … end` attached to a `send` → a **block**; reified to a non-lambda Proc
  only if the callee captures it via `&blk` or calls `block_given?`/`yield`.
- `proc { … }` / `Proc.new { … }` → non-lambda Proc.
- `->(x){ … }` / `lambda { … }` → lambda Proc (`lambda = true`).

The lambda flag controls **two** observable behaviors: arity checking (§2) and the
meaning of `return` (§4).

---

## 2. Calling a closure; arity

Invoking a closure pushes a **block frame** whose `parent` is `captured` (so free
locals resolve into the enclosing scope, artifact 03 §2):

```
        cl = closure of the callee proc
        φ_b = { self = cl.captured.self, defmod = cl.captured.defmod,
                cref = cl.captured.cref, parent = cl.captured,
                locals = bind(cl.params, args, lambda := cl.lambda), kind = block }
      ─────────────────────────────────────────────────────────────────────  (PROC-CALL)
        ⟨ send (proc p) :call [ā] ⟩  →  push φ_b ; evaluate cl.body
```

**Arity / argument binding differs by `lambda`** **[V]**:
- **non-lambda** (blocks, procs): *lenient*. Missing params bind `nil`, extra args are
  dropped, and a single array argument is **auto-splatted** to fill multiple params.
  `proc{|a,b| [a,b]}.call(1) == [1, nil]`.
- **lambda**: *strict*, exactly like a method. Wrong arity ⇒ `ArgumentError`; no
  auto-splat. `lambda{|a,b|}.call(1)` raises `ArgumentError`.

So `bind` is parameterized by the lambda flag; method invocation (artifact 02 §3) uses
the strict variant.

`yield` calls the *current method frame's* block without naming it:

```
        φ_m = nearest enclosing method frame        φ_m.block = proc p   (p ≠ nil)
      ─────────────────────────────────────────────────────────  (YIELD)
        ⟨ yield [ā] ⟩  →  same as ⟨ send (proc p) :call [ā] ⟩   (non-lambda binding)

        φ_m.block = nil
      ─────────────────────────────────────────  (YIELD-NONE)
        ⟨ yield … ⟩  →  ^exc(LocalJumpError)
```

`block_given?` is `φ_m.block ≠ nil` **[V]**.

---

## 3. Non-local control: the unwinding model

`return`, `break`, `next`, `redo`, `retry`, and `raise` are **not** ordinary values —
they abort normal evaluation and unwind `Ξ` looking for a specific target frame. We model
each as searching the frame stack for a matching *handler marker*, running `ensure`
blocks encountered along the way (§5), and either resuming or re-raising.

We represent an in-flight non-local transfer as a distinguished control state (a variant
of the `^exc` configuration from artifact 00 §2, generalized):

```
  C^ctl ::= ⟨…⟩^return(v, tgt)    -- unwind to method frame tgt, yield v
         |  ⟨…⟩^break(v, tgt)     -- unwind to the send that took the block, yield v
         |  ⟨…⟩^next(v)           -- unwind to current block frame boundary, yield v
         |  ⟨…⟩^redo              -- restart current block body with same args
         |  ⟨…⟩^retry             -- restart nearest begin body
         |  ⟨…⟩^exc(v)            -- exception (§5)
```

Each propagates through the continuation (skipping normal steps) until it hits its
target, running `ensure`s in between.

---

## 4. `return`, `break`, `next`, `redo`, `retry`

**`next [v]`** — local to the *current block*: end this block invocation, making
`.call`/`yield` produce `v` (default `nil`). In `map`, it sets that element's result.
**[V]** `[1,2,3].map{|x| next x*10 if x==2; x} == [1, 20, 3]`. It is the block-level
analogue of `return`.

```
      ───────────────────────────────────────────────  (NEXT)
      ⟨ next v ⟩ in block frame φ_b  →  pop φ_b, resume its caller with value v
```

**`redo`** — re-run the current block body from the top with the *same* parameters (no
re-fetch of the next element). Rarely used; models as restarting `φ_b.body` without
popping.

**`break [v]`** — terminate the method call that the block was passed to, making *that
method call* return `v`. **[V]** `each_it{|x| break :broke if x==2}` makes `each_it`
return `:broke`, not `:normal`. The target is the `send` frame that installed this block
(recorded in the closure/`φ_b`):

```
        tgt = the send-activation that this block was passed to
      ─────────────────────────────────────────────────────────  (BREAK)
        ⟨ break v ⟩  →  unwind Ξ down to tgt (running ensures), tgt yields v
```

**`return [v]`** — return from a **method**, but *which* method depends on lambda-ness
when inside a closure — the crux distinction:
- In a method body or a **lambda**: returns from the immediately enclosing
  method/lambda. `lambda{return 1}.call` inside `m1` → `m1` continues, returns 2. **[V]**
- In a **non-lambda proc/block**: returns from the method where the proc was *defined*
  (its `captured` method frame). `proc{return 1}.call` inside `m2` → `m2` returns 1. **[V]**
  If that home method has already returned, `return` raises `LocalJumpError`.

```
        φ.kind = block, closure non-lambda        tgt = closure.captured's method frame
      ─────────────────────────────────────────────────────────  (RETURN-PROC)
        ⟨ return v ⟩  →  unwind Ξ to tgt (running ensures); if tgt gone ⇒ ^exc(LocalJumpError)

        φ.kind ∈ {method, lambda-block}
      ─────────────────────────────────────────────────────────  (RETURN-METHOD)
        ⟨ return v ⟩  →  unwind Ξ to nearest method/lambda frame, yielding v
```

**`retry`** — inside a `rescue`, restart the enclosing `begin` body from the top.
**[V]** the classic retry-counter loop runs the body 3 times.

These lambda-vs-proc control semantics are a top source of real-world Ruby bugs, so they
are a priority target for the differential-testing oracle (PROJECT_PLAN §6.2).

---

## 5. Exceptions: `raise` / `rescue` / `ensure`

A `begin e_body rescue* ensure?` frame installs handlers. `raise` produces `^exc(v)`
where `v` is an exception object; propagation unwinds `Ξ`, at each frame:

1. If the frame has a matching `rescue` clause, transfer control there (binding `$!` and
   the `=> x` variable).
2. Whether or not it matched, its `ensure` block runs as the transfer passes through.

**Rescue matching uses `===`** (Module#=== ⇒ `is_a?`), and the **default rescue class is
`StandardError`, not `Exception`** **[V]**: `raise Exception` is *not* caught by a bare
`rescue`. This is a critical, frequently-misunderstood fact — signals/system errors
(`SignalException`, `NoMemoryError`, `SystemExit`) descend from `Exception` but not
`StandardError`, so bare `rescue` intentionally misses them.

```
        ^exc(v) reaches begin-frame with clauses [rescue C̄ᵢ => xᵢ hᵢ]
        i = least index with  ∃ C ∈ C̄ᵢ.  H ⊢ C === v   (default C̄ = [StandardError])
      ─────────────────────────────────────────────────────────────────────  (RESCUE-MATCH)
        →  bind $! := v, xᵢ := v ; evaluate hᵢ   (then run ensure on normal exit)

        no clause matches at this frame
      ─────────────────────────────────────────  (RESCUE-PASS)
        run this frame's ensure (if any), continue propagating ^exc(v) outward
```

**`ensure` always runs**, on every path out of the protected body — normal completion,
exception, `return`, `break`, `throw`. Verified facets **[V]**:
- `def e1; return 1; ensure; puts "ens"; end` prints `ens`, returns `1`.
- `def e2; return 1; ensure; return 9; end` returns **9** — an explicit value/return
  *from* `ensure* overrides the pending return/exception (and even swallows an
  in-flight exception). This is a genuine, surprising override rule.
- Ordering: inner `rescue` runs, then inner `ensure`, then the re-raised exception
  reaches the outer handler:

```
  begin
    begin; raise "a"; rescue; puts "inner-rescue"; raise "b"; ensure; puts "inner-ensure"; end
  rescue => e; puts "outer: #{e.message}"; end
    # => inner-rescue / inner-ensure / outer: b     [V]
```

So `ensure` runs *after* the rescue body decided to re-raise, and the newly raised `"b"`
(not `"a"`) is what escapes. Modeling this requires `ensure` to fire as the `^exc`/`^ctl`
state transits the frame, and to be able to *replace* the in-flight transfer if it
itself returns/raises.

**`throw`/`catch`** are a separate labeled non-local jump (not exceptions); model as a
`^ctl` variant targeting a `catch` frame matched by tag. `raise` with no args inside a
`rescue` re-raises `$!`.

---

## 6. Consolidated unwinding invariant

All of §3–§5 share one mechanism, which we state as the key metatheorem to prove once
mechanized (PROJECT_PLAN §7):

> **Unwind soundness.** Any control state `⟨…⟩^ctl` deterministically either (a) reaches
> its target frame, running exactly the `ensure` blocks lexically between the raise site
> and the target, in innermost-to-outermost order, each exactly once; or (b) escapes the
> whole stack, becoming an uncaught-exception / `LocalJumpError` observation. No `ensure`
> is skipped or double-run; a later `^ctl` produced inside an `ensure` supersedes an
> earlier in-flight one.

This single invariant is what makes the exception/control semantics *explainable* — every
observed ordering has a derivation that runs the ensures in a provably-correct sequence.

---

## 7. Open questions

- **[?]** `Fiber`/`Enumerator` (lazy `next`/`yield` across a resumable boundary) — needs
  a first-class captured continuation; deferred (PROJECT_PLAN §4 excludes fine-grained
  Fiber scheduling).
- **[?]** Exact interaction of `break`/`next` with `Enumerator`-based iteration vs. plain
  `yield`-based iteration.
- **[?]** `ensure` that itself raises while an exception is already in flight — which
  exception's backtrace wins, and `Exception#cause` chaining.
- **[?]** `throw` across a block boundary that has already returned (uncaught-throw
  `ArgumentError`).
