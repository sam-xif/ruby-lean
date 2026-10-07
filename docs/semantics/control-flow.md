# 04 — Blocks, procs and control flow

Where the choice of small-step plus an explicit stack earns its keep: every rule
here is about inspecting and unwinding it.

## §1 — Closures

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
exceptions and jumps. Native `Symbol#to_proc` supplies a capture-free closure;
overriding or undefining that method changes `&:symbol` accordingly.

## §2 — Calling a closure; arity

`Proc#call`, `Proc#[]`, `Proc#yield` and `Proc#===` use ordinary method lookup, including
singleton/class overrides, aliases, visibility and `undef`. Resolving their native
marker invokes the closure; `super` can resolve the same marker. `f.()` is syntax
for `f.call`, not a separate method named `()`.

Array's `map`/`collect` likewise resolve native entries through ordinary lookup.
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


A block installed by `define_method` keeps that origin even when it has no captured
locals. Its method boundary handles local break/next/return and restarts redo in
the same activation without repeating parameter conversion or defaults. This also
applies to captured for callbacks; strict method arity remains in force. **[V]**


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
The compiler's synthetic slots cannot collide with Ruby local names. **[V]**

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
remain explicit gates. **[V]**

Native UTF-8 String inspection escapes non-printing Unicode scalars with
`\uXXXX` or supplementary-plane `\u{XXXXX}` notation. Printability comes from
the pinned CRuby oracle's generated Unicode table, verified against every scalar.
Existing named control escapes, interpolation escaping and binary byte escapes
retain their separate rules. **[V]**

Native String#b always returns a fresh mutable base String in ASCII-8BIT, including
for already-binary, frozen and subclass receivers. It copies the bytes without
copying ivars/eigenclasses or calling Ruby conversion, copy or initialization hooks.
Aliases and super retain native dispatch. The old exposed __as_binary wrapper is
removed. **[V]**

## §3 — The unwinding model

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

## §4 — `return`, `break`, `next`, `redo`, `retry`

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
the literal call. Closure entry reads the live tokens, independently of
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

## §5 — Exceptions

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
Metadata/backtrace/cause and singleton copies remain incomplete. **[V]**

Native VM errors construct through private initialize(message), preserving the
surrounding `$!` and bypassing overridden new/allocate/exception. Native NameError,
NoMethodError and KeyError use direct native initialization instead. FrozenError
renders the class, initializes with a mutable prefix String, then inspects the
receiver and appends to that same String. A callback can replace the exception's
message, mutate/freeze the prefix, or raise before inspection. **[V]**
Execution-local `frozenInspections` tracks receiver recursion only during inspect
and String conversion, after initialization. Returning or unwinding through the
owning rendering continuation releases one guard; continuation cuts retain it.

An uncaught throw constructs with `(tag, value, "uncaught throw %p")`; its native
initializer delegates the remaining arguments to super and then stores hidden
tag/value metadata. Message rendering inspects the live tag lazily, including
String conversion of a non-String inspect result. Arbitrary printf formats and
non-String format conversion remain gated. **[V]**

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

## §6 — The unwinding invariant

All of §3–§5 share one mechanism, stated as the metatheorem worth proving:

> **Unwind soundness.** Any control state `^ctl` deterministically either (a)
> reaches its target, running exactly the `ensure` blocks lexically between the
> jump site and the target, innermost-to-outermost, each exactly once; or (b)
> escapes the whole stack, becoming an uncaught-exception or `LocalJumpError`
> observation. No `ensure` is skipped or double-run, and a later `^ctl` raised
> inside an `ensure` supersedes an earlier in-flight one.

This is what makes the control semantics *explainable*: every observed ordering
has a derivation that runs the ensures in a provably correct sequence.

## §7 — External iteration and remaining boundaries

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
other than nil remain gated. **[V]**

`rewind` checks the receiver's rewind protocol, including response/missing
hooks, before discarding suspension. It does not execute abandoned `ensure`
bodies. Native Hash iteration cleanup is abandoned too: its insertion lock
remains, even after CRuby's explicit GC. Shared `hashIterationLocks` carries one
entry per active callback. Callback return or unwind releases one entry;
suspension and abandonment retain it. Releasing one callback preserves entries
owned by nested iterations, other producers or abandoned executions.
No continuation scan is needed. Existing Hash values and deletions remain
visible during iteration, and Array cursors reread their
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
