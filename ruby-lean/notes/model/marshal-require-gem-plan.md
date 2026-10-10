# Plan: the gem system, `require`/`require_relative`, and `Marshal`

Status: proposal / design note. Nothing here is implemented. This describes a
staged route from the symbolic virtual filesystem (issue #7, PRs #21–#42) to a
model in which a **Marshal deserialization gadget chain is an ordinary program
trace** — one the executable semantics either runs faithfully or declines by
name, never approximates.

## Why this exists, and what it is not

The elttam write-up *"Ruby 4.0 universal RCE deserialization gadget chain"*
demonstrates that `Marshal.load` on attacker-controlled bytes can, through
nothing but ordinary library code, reach code execution. The interesting claim
for this project is structural: the chain uses **only documented language and
standard-library behaviour** — constant autoload, `Hash` rehashing calling
`#hash`, a `Time` deserialization hook, a gem cache-write routine, a spec loader
that `eval`s a file. Each step is a method call the current model would have to
either reproduce byte-for-byte or gate.

So the goal of this work is a **defensive, analysis** capability: give those
mechanisms precise operational semantics so that the *reachability* of a
dangerous sink from `Marshal.load` becomes a property the model can state and a
proof can discharge — the same shape as the type-soundness-by-reachability
argument the project already makes.

Explicit non-goals, and a hard rule for every PR in this plan:

- **No working exploit lives in the repo.** No payload-builder, no serialized
  gadget bytes, no gadget-by-gadget weaponization recipe. Fixtures exercise one
  mechanism at a time (e.g. "`Marshal.load` of a hash calls `#hash` on the
  restored key"), not an assembled chain against a real sink.
- **The dangerous sink is modeled as a decline or as an abstract observation,
  never as a live effect.** `eval` of attacker bytes is not executed (§M6). The
  artifact is a thing that *recognizes* "this trace reaches `eval`/`system`",
  not a thing that performs it.
- This stays inside the project's existing exclusion of `eval`/`Fiber`/threads
  (`docs/semantics/supported-ruby.md`): we are not lifting that exclusion, we
  are making the *approach* to the excluded boundary observable.

Treat this document the way `docs/semantics/design.md` is treated: a readable
account of intended mechanism, with the Lean definitions as the semantics of
record once they land.

## What the chain exercises, as language mechanisms

Stripped to mechanism (not payload), the chain needs the model to have faithful
semantics for five things. Each maps to a milestone below.

| Mechanism (abstract) | Model capability needed | Milestone |
|---|---|---|
| Resolving a library constant pulls in more stdlib | `Module#autoload` + `require` reading real file bodies from the VFS | M1, M2 |
| Rebuilding a `Hash` calls `#hash`/`#eql?` on restored keys | `Marshal.load` dispatches user methods during reconstruction | M4 |
| A library routine writes attacker bytes to a predictable path | faithful `Gem`/`FileUtils` file-write over the VFS, **or** an honest gate | M3, M5 |
| A deserialization hook calls a coercion wrapped in `rescue` | `Marshal` user hooks (`_load`/`marshal_load`) + exact `rb_rescue` unwinding | M4 |
| A spec loader reads a file and `eval`s it | the sink — decline, or abstract "dangerous call reached" observation | M6 |

The payoff is in the last column of the middle: once each of these is an
ordinary dispatch through the one dispatch rule, "does untrusted `Marshal.load`
reach this sink" is a question about reachable configurations, which is the
model's native language.

## Where the model stands today (the floor to build on)

- **VFS (issue #7).** Files, directories and descriptors are heap `Payload`
  variants with a pure, total path walk from a boot fixture; `File`/`IO`/`Dir`
  read/write/open/list/line-read/seek are modeled; everything else gates by
  name. The planned **dynamic mode** keeps `stepFn` pure by emitting `FSReq`
  values answered by an external driver (issue #7 body). This is the substrate
  for reading library source and for the chain's disk-staging step.
- **`require` of modeled features only.** `Interp/Require.lean` runs a body from
  `Machine.featurePrograms` (a fixed table: `sorbet-runtime`, `json`, `uri`,
  `forwardable`), caches it in `loadedFeatures`, and otherwise answers
  `unsupported "require of an unmodeled library"`. It **never reads the VFS**,
  does no `$LOAD_PATH` resolution, and `require_relative` gates outright
  (`Require.lean:15`).
- **No `Marshal`.** `Marshal` exists only as a CRuby constant name so lookups
  gate; `marshal_dump`/`marshal_load` appear only in the generated name tables.
  No format, no `dump`, no `load`.
- **No autoload.** `autoload`/`autoload?` are names in `CRubyNames.lean` only.
- **No gem system.** `Gem` is a bare constant name. No `Specification`, no
  activation, no `$LOAD_PATH` contents.
- **`eval` is excluded** by design, alongside `Fiber`/threads.

So four of the five mechanisms are entirely absent and the fifth (`require`) is
present only in a form that cannot read a file. The plan is mostly additive, and
each milestone is shippable in the project's house style: decline-not-
approximate, a differential-test case against CRuby 4.0.5 before shipping, the
proof books rebuilt (`make books`), and the checker left isolated from the model
(`AGENTS.md` rule 1).

## Milestones

Dependencies: M1 → {M2, M5}; M3 → M4; M4 depends on M1 (restored objects can
trigger `require`) and on M5 (gadget classes live in gem/stdlib); M6 is the
capstone. Each is a stack of small PRs the way VFS steps 1–5 were.

### M1 — `require` and `require_relative` over the VFS

The keystone. Today `require` is a lookup in a fixed table; make it a **file
load through the VFS**, so a required file's bytes come from the heap fixture and
run as a fresh top level. This is what turns "the stdlib" from four hand-written
prelude features into actual source the fixture carries.

Design, keyed to existing machinery:

- **Resolution.** Add `Machine.loadPath : List String` (the `$LOAD_PATH` / `$:`
  globals already exist as names in `Interp/Support.lean:27`; give them
  backing). `require "x"` searches `loadPath` for `x.rb` (and the modeled `.so`
  convention already in `loadedFeatures := ["pathname.so"]`); `require_relative`
  resolves against the **current source file's** directory — which means the
  machine must carry the running file's path. Add `Frame.sourcePath : Option
  String` (frames already carry `libraryOrigin`), set it on the require frame
  (`Require.lean:45`) and on the top-level frame.
- **Loaded-feature identity.** CRuby keys `$LOADED_FEATURES` by *expanded
  realpath*, not the argument. Model the expansion as a pure VFS `realpath`
  (the walk from issue #7 already computes this). The existing
  `loadedFeatures`/`loadingFeatures`/`requireK` cycle-and-cache logic
  (`Kont.lean:24`, `:356`) is reused unchanged; only the key changes from
  feature-string to realpath.
- **Body source.** A required file's `Expr` must come from somewhere pure.
  Options:
  1. **Pre-desugared fixture bodies** (recommended first cut): the fixture
     carries `(realpath × Expr)` pairs, desugared offline by the existing
     `desugar/` pipeline, exactly as `featurePrograms` carries them today. The
     VFS file's *bytes* and the parsed `Expr` are both fixture data; the model
     does not parse. This keeps parsing out of the trusted kernel (the desugarer
     is untrusted per `AGENTS.md` rule 2) and needs no in-model lexer.
  2. In-model parse of VFS bytes — rejected for now: a Ruby parser in Lean is a
     huge trusted surface and duplicates `desugar/`.
- **Honest gates stay.** The existing refusals (`const_added` hook, frozen
  namespace, `String#freeze` override, namespace conflict) carry over. A
  `require` of a path not in the fixture gates `unsupported "require of an
  unmodeled file: …"` rather than raising a guessed `LoadError` — until M-errno
  gives `LoadError` message fidelity.
- **Difftest.** New hermetic `"vfs"`-family programs: `require_relative` a
  sibling file that defines a constant; `require` the same file twice (second
  returns `false`); a circular `require` (returns `false` mid-load); a
  `require` that raises partway (effects kept, retry allowed — the existing
  retry semantics).

Risk: `require` running arbitrary fixture source multiplies the behaviour the
model must already get right. Mitigate by starting with tiny fixtures (a file
that assigns a constant) and growing toward real stdlib files only as M3–M5
need specific classes.

### M2 — `autoload`

`Module#autoload(:Const, "path")` registers a deferred `require` fired the first
time `Const` is resolved and found missing. The chain relies on this to expand
the reachable gadget set during a load.

Design:

- Store autoload registrations on the class object, next to its constant table
  (constants are already heap fields per `docs/semantics/objects.md`). A new
  small `ClassPayload` field `autoloads : List (String × String)` (name →
  path), or a dedicated heap payload — prefer the field, to keep it inside the
  existing constant-lookup path.
- Fire in **constant resolution**, not at a special site: when the two-phase
  constant lookup (`docs/semantics/variables.md`) misses and an autoload entry
  matches, perform the M1 `require` of its path, then re-resolve. This is one
  new arm in the constant-miss continuation; it reuses M1 end to end.
- Reentrancy and the already-loaded/already-loading interaction with
  `loadedFeatures` match `require`'s. `autoload?` reports the pending path.
- Difftest: `autoload :A, "a"` then first reference to `A` triggers the load and
  resolves; a second reference does not re-require; an autoload whose file fails
  to define the constant (CRuby raises `NameError` — model classes first, gate
  message until M-errno).

### M3 — `Marshal` core: format and the hook-free values

Model `Marshal.dump`/`Marshal.load` for the values that carry no user code:
`nil`, booleans, `Integer`, `Float`, `String` (+ ivars/encoding), `Symbol`,
`Array`, `Hash`, `Range`, plain objects (class + ivars), and the back-reference
/ symbol-reference table the format uses for shared and cyclic structure.

Design, keyed to the project's style for serialization:

- **`dump` is a pure fold, like JSON generation.** `prelude/features/json.rb`
  already models generation as a total fold over the value and *declines to
  parse*. `Marshal.dump` is the analogue: a pure `Value → String` (the version
  header `\x04\x08` + typed, length-prefixed encoding) computed from the heap.
  This is honest and fully testable against CRuby byte-for-byte.
- **`load` is the hard direction** and must be a *small step*, not a pure
  decoder, because reconstruction dispatches user methods (M4). Represent the
  Marshal byte string as input consumed by a continuation (`Machine.kont`), so
  that when reconstruction needs to call `#hash` on a key or an object's
  `marshal_load`, it suspends into ordinary dispatch and resumes — the same
  pattern `require` uses to run a body and come back (`requireK`).
- **Back-references.** The format's object/symbol tables are reconstruction
  state carried in the load continuation, not global heap state.
- **Decline, don't approximate.** Any tag the model does not handle
  (`Data`-struct, `bignum` beyond modeled `Integer`, user-marshal classes not
  yet in M4) gates `unsupported "Marshal.load of a <tag> record"`. A malformed
  stream gates rather than guessing CRuby's `ArgumentError "marshal data too
  short"` until M-errno gives that message exactly.
- **Difftest.** Round-trip `Marshal.load(Marshal.dump(x))` for each hook-free
  value, and load of *fixture* byte strings produced by CRuby offline, compared
  to CRuby's own load result. Fixtures are benign values only.

### M4 — `Marshal` user hooks: where chaining becomes expressible

This is the milestone that makes gadget *chaining* a thing the model can run.
The four hooks, each an ordinary dispatch during `load`:

- **`_dump`/`self._load(str)`** (string-based custom marshal). `Time` uses this:
  `Time._load` is called with attacker-controlled bytes and, in the chain,
  coerces a zone value via `#to_str` inside an `rb_rescue`. Model it as: `load`,
  on a user-marshal-string tag, sends `_load` to the named class with the
  embedded string; the method runs as ordinary Ruby, so its `rescue` is the
  model's existing exception unwinding (`docs/semantics/control-flow.md`) with
  no special case.
- **`marshal_dump`/`marshal_load(obj)`** (object-based). `load` reconstructs the
  inner object, then sends `marshal_load` to a freshly allocated instance.
- **Instance-variable restoration.** For a plain object, `load` sets ivars
  directly (no setter dispatch) — matches CRuby and reuses the existing
  `instance_variable_set` heap write path semantics (`Interp/Reflect.lean`).
- **`Hash` rehash dispatch.** Restoring a `Hash` inserts each restored key,
  which **calls `#hash` and `#eql?`** on that key object. This is the chain's
  trigger and the post's core point: it is core-language behaviour, not a
  removable override. Model it as: `load`, having reconstructed a key, performs
  the ordinary hash-insert, which already dispatches `#hash`/`#eql?` in
  `Builtins/Collections.lean`. No new mechanism — the key is that a *user
  object* restored by Marshal flows into the normal insert.

Because every hook is ordinary dispatch, an assembled chain is just a sequence
of sends triggered by one `Marshal.load`. The model does not need to know it is
a "chain"; it runs the sends or gates one.

Fixtures here are strictly **single-mechanism**: e.g. a class whose
`marshal_load` increments a counter, to show the hook fires; a hash whose key is
a user object with an observable `#hash`. No fixture assembles a real gadget
sequence or targets a real sink.

### M5 — the gem system surface

Enough of `Gem` for the stdlib classes a chain traverses to exist and resolve,
not a faithful RubyGems:

- `Gem` module, `Gem::Specification` and the `$LOAD_PATH`-population that gem
  activation performs, as **fixture data** (a small set of stub specs), so that
  requiring a gem's entry file resolves through M1. Gem activation becomes
  "prepend these fixture paths to `loadPath`", a pure heap/machine update.
- The specific library routines the chain repurposes (a cache-write helper, a
  spec loader) are modeled **only to the fidelity needed to observe the step**,
  and the file-*write* goes through the VFS from M-write below. Where faithful
  modeling of a real RubyGems internal would be large, **gate it by name** — an
  honest `unsupported "Gem::… needs the full RubyGems loader"` is a correct
  answer; a guessed one is a bug (`AGENTS.md` rule 3).
- Difftest is limited: RubyGems internals are version-sensitive and partly
  filesystem/network bound (exactly the ambient facts issue #7 refuses). Pin to
  CRuby 4.0.5's shipped RubyGems for the handful of routines modeled, and gate
  the rest.

Supporting pieces M3–M5 lean on:

- **M-write.** VFS write + directory-create through the dynamic-mode `FSReq`
  path (issue #7). The staging step is `File.write`/`FileUtils.mkdir_p` to a VFS
  path — already within the VFS roadmap; no new effect model.
- **M-errno.** `Errno::*`, `LoadError`, `ArgumentError "marshal data too short"`
  message fidelity (VFS step 7 territory). Until it lands, the milestones above
  gate on these rather than emit a guessed message.

### M6 — the sink, and the actual deliverable

The chain ends at `eval` of a staged file. `eval` is **excluded** from the
model and this plan does not lift that. Two ways to make the endpoint useful
without executing attacker code:

1. **Decline at the sink, prove reachability up to it (recommended).** Model
   every step up to the final `eval`/`instance_eval`/`Kernel#system` call, and
   at that call emit a distinguished `Unsupported`/observation —
   `dangerousSinkReached (sink : SinkKind) (argProvenance : …)` — rather than
   running it. The model then faithfully shows *that* a `Marshal.load` of fixture
   bytes drives execution to a sink, which is the whole defensive claim, without
   ever being an exploit. This is the honest-gate discipline turned into a
   feature.
2. **A restricted, effect-free `eval`** of a syntactically-constrained subset —
   larger, riskier, and still would need the sink neutered. Not recommended.

With option 1, the capstone artifact is a **reachability observation**: given a
machine started on a Marshal byte-string fixture, does `run` reach
`dangerousSinkReached`? That is a decidable question over the pure machine, and
it is the thing a defender wants: a checker that, given a hardening (an
allowlist à la `Gem::SafeMarshal`, a removed gadget), re-runs and reports the
sink is **no longer reachable** — the model-side analogue of the two RubyGems
commits that broke the earlier chain.

## How this pays off (and ties to the existing proofs)

The project already argues type-safety **by reachability**: well-typed programs
never reach a stuck/type-error configuration. Deserialization safety is the same
shape with a different bad set:

> For a machine `m₀` whose only untrusted input is a Marshal byte string `s`,
> `run` from `m₀` never reaches `dangerousSinkReached`.

That is a statement the metatheory can host, and a specific hardening is a
hypothesis that makes it provable (or a counterexample fixture that makes it
false). Two concrete uses:

- **Regression oracle for a patch.** Encode a mitigation as a model change
  (type check in a `marshal_load`, a gadget method removed), and show the sink
  becomes unreachable from the same fixture — mirroring how `62b49465f8` /
  `89ad04db86` broke the prior chain.
- **Allowlist adequacy.** Model a `SafeMarshal`-style allowlisted `load` and
  state that it never reaches a user hook outside the allowlist — turning "is
  this allowlist enough" into a proof obligation.

## Invariants every PR here must keep

From `AGENTS.md` and the VFS PRs:

1. `obs` stays a pure function of the configuration; difftest stays byte-exact
   against CRuby 4.0.5. Marshal `dump` and the hook-free `load` are directly
   comparable; the dynamic FS and gem internals ride the issue-#7 conformance
   hypothesis, not a proof assumption.
2. Decline, don't approximate. Every unmodeled tag, routine, path and message is
   a named `Unsupported`, never a guess. This is load-bearing here: a wrongly
   *accepted* Marshal record is exactly the failure mode the work is about.
3. The checker (`books/.../Checker/`) imports nothing from the model; `make
   books` is run, not just `make lean`; no `sorry`/`native_decide`/new axiom.
4. Recorded results only improve; generated files are regenerated (`make gen`),
   not edited.
5. The repo never contains a working chain, a payload builder, or serialized
   gadget bytes; fixtures are single-mechanism and benign; the sink is a
   decline/observation, never a live effect.

## Open questions

- **`cwd` for `require_relative`** overlaps issue #7 open question 2 (the
  machine `cwd`). Settle them together.
- **Body source for required files** — pre-desugared fixture `Expr` (M1 option 1)
  is the safe first cut; whether the model ever parses VFS bytes in-tree is a
  separate, larger decision.
- **Marshal format coverage** — how far down the tag list to go before gating;
  propose: exactly the tags the single-mechanism fixtures need, no more.
- **Where `dangerousSinkReached` lives** — a new `Obs` variant vs an
  `Unsupported` reason. A first-class observation is more useful for the
  reachability theorem but touches `Obs.lean` and its framing lemmas.
- **Gem fidelity ceiling** — which RubyGems routines are worth modeling vs
  gating, given they are version- and filesystem-bound.

## Suggested first PR

`require`/`require_relative` over the VFS reading a **pre-desugared fixture
body** (M1, option 1), with: `loadPath` backing the `$LOAD_PATH` globals,
`Frame.sourcePath`, realpath-keyed `loadedFeatures`, and a hermetic difftest
covering `require_relative` of a sibling, double-require, and a circular
require. It unblocks M2 and M5 and is independently a real feature (it closes
the `require_relative` gate at `Require.lean:15`). Everything Marshal-specific
(M3+) stacks on it.
