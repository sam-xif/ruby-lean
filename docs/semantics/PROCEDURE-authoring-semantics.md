# Procedure: Authoring RubyCore Semantics Artifacts (Agent Playbook)

> A repeatable, agent-followable procedure for producing or extending the quasi-formal
> semantics artifacts in this directory, **assuming access to a working Ruby oracle**.
> It codifies how artifacts 00–05 were actually produced so the next domain (param
> binding, core library, the Rails slice) is authored the same way.

**Audience:** an autonomous coding agent (or a human) with shell access, a Ruby
interpreter, and web access. **Output:** one Markdown artifact of small-step rules with
every claim tagged `[V]` / `[D]` / `[?]` (see §0).

---

## 0. Invariants that must hold for every artifact

- **Evidence tags on every non-trivial claim:**
  - `[V]` — *verified* against the Ruby oracle in this session (a runnable snippet exists).
  - `[D]` — *documented*: sourced from ISO/IEC 30170, ruby-lang docs, or `ruby/spec`.
  - `[?]` — *open question* to pin during mechanization, typically by differential test.
  A rule with a surprising consequence and no `[V]` is not done.
- **Notation is fixed by `00-notation-and-syntax.md`.** Do not invent new config/frame
  structure; extend it there first if genuinely needed, then use it.
- **Design bet is load-bearing:** prefer reducing a feature to *message send + heap
  mutation* over adding a new evaluation rule (artifact 02 §6). If you find yourself
  adding a rule, ask whether it desugars (artifact 00 §5) or is heap mutation instead.
- **Small-step, explicit stack.** Rules step `⟨K,H,Ξ⟩ → ⟨…⟩`; control effects unwind
  `Ξ` (artifact 04). No big-step shortcuts that hide effect ordering.

---

## 1. Establish the oracle (once per environment)

```bash
# Prefer a modern CRuby. On macOS a Homebrew bottle is fastest (RVM source-compiles and
# may fail on deprecated openssl); on Linux use a pinned container image.
brew install ruby              # macOS: gives a current CRuby quickly
RUBY="$(brew --prefix ruby)/bin/ruby"; $RUBY -v     # record the EXACT version in the artifact
# Linux / CI parity:  docker run --rm -i ruby:X.Y.Z-slim ruby -
```

- **Record the exact version** in the artifact header (semantics drift across minors —
  artifact 05 §3.2).
- For behavior that must be deterministic, invoke with `RUBY_HASH_SEED=0`, single thread,
  and stub `Time`/`rand` (artifact 05 §3.2).
- Sanity-check the oracle before trusting it: run a known snippet (e.g. `p [].class`).

---

## 2. Scope the artifact

1. Pick **one coherent domain** (e.g. "parameter binding", "Hash builtins"). One artifact
   = one domain; cross-link rather than duplicate (`[[02-dispatch-and-mro]]` style refs).
2. List the **surface features** in scope and the ones you will explicitly exclude or
   desugar. Write the exclusions down (PROJECT_PLAN §4 "trusted/unmodeled").
3. Enumerate the **judgments** you will define and which existing judgments they depend
   on (e.g. lookup depends on `ancestors`).
4. Create a task per subsection if the domain is large (`TaskCreate`), so progress is
   visible and nothing is dropped.

---

## 3. Gather ground truth (documentation + literature)

- **Primary:** ISO/IEC 30170:2012 for the object model; ruby-lang.org docs for the class
  under study; `ruby/spec` for executable intent.
- **Secondary/literature:** search for prior formal treatments (KJS/JSCert/Redex for
  *method*, RDL/Sorbet for Ruby *signatures*). Cite what you reuse (artifact 05 §2).
- Tag everything sourced here `[D]`. Do **not** yet trust it — §4 converts `[D]`
  suspicions and all surprising claims into `[V]` or `[?]`.

---

## 4. Probe the oracle — the core loop

This is where most of the work is. For each rule you intend to write, **design a minimal
discriminating snippet** that would come out differently under a plausible-but-wrong
model, and run it.

```bash
# Template: isolate ONE behavior, print a canonical observation.
$RUBY -e '<minimal program>; p <observable>'
# Prefer p/inspect over puts; capture exception class + message on the rescue path:
$RUBY -e 'begin; <program>; rescue Exception => e; p [e.class, e.message[0,40]]; end'
```

Probing discipline:
- **One variable per snippet.** Change exactly one thing to attribute the effect.
- **Target the corners**, not the happy path: precedence between two lookup mechanisms
  (lexical vs ancestor constants), last-writer-wins (module include order), non-local
  control targets (`break` vs `next` vs proc-`return`), default-value vs error on unset,
  ordering of effects (rescue → ensure → re-raise).
- **Contrast pairs.** Run the two forms you suspect differ side by side (`proc` vs
  `lambda` `return`; `dup` vs `clone`; bare `rescue` vs `rescue Exception`).
- **Confirm the negative.** If a rule says "X raises," verify the exception *class*, not
  just that it failed.
- Batch related probes into one shell call to move fast; keep each probe labeled with an
  `echo "--- what this checks ---"`.

Record each confirmed behavior as a `[V]` line with the snippet inlined or referenced.
Anything the oracle *can't* settle (version-specific, genuinely ambiguous, or an excluded
feature) becomes `[?]` with a note on how differential testing would resolve it.

---

## 5. Write the rules

- One inference rule per behavior, in the fixed ASCII style:

  ```
          premise₁      premise₂
        ─────────────────────────────  (RULE-NAME)
                 conclusion
  ```

- Name rules in `CATEGORY-CASE` form (`SEND-INVOKE`, `RESCUE-MATCH`, `RETURN-PROC`).
- State the **auxiliary judgment** first (e.g. `ancestors`, `lookup`), then the rules
  that use it.
- Attach the `[V]`/`[D]`/`[?]` tag to the surrounding prose, and where a rule was
  verified, show the discriminating snippet + its observed output.
- Add a short **"why this design pays off"** note when a rule collapses many surface
  features into one mechanism (reinforces the load-bearing bet).
- End the artifact with an **Open questions** section listing every `[?]`.

---

## 6. Self-check before marking done

- [ ] Every surprising claim is `[V]` with a runnable snippet, or `[?]` with a reason.
- [ ] Oracle version recorded; deterministic-sensitive probes used fixed seed/stubs.
- [ ] No new config/frame structure invented outside artifact 00.
- [ ] Each new feature was checked against "can this be desugar + heap mutation instead
      of a new rule?" and the answer is documented.
- [ ] Judgments are defined before use; cross-links resolve to real artifacts.
- [ ] Open-questions section lists all `[?]`.
- [ ] README index (`README.md`) updated with the new artifact row.
- [ ] Rules are stated so they could be transcribed to a Lean `inductive Step` /
      executable `def` with no missing premises (the eventual mechanization target).

---

## 7. Hand-off to mechanization & differential testing

Each `[V]` snippet is a **ready-made differential-testing oracle case** (artifact 05 §4.1):
drop it into the per-rule corpus (`t/<domain>/<RULE_NAME>.rb`) so that when the Lean rule
is implemented, the same snippet checks interpreter-vs-CRuby agreement, and its rule name
feeds the semantic-rule-coverage metric (artifact 05 §6). Each `[?]` becomes a
differential-testing *question*, not a guess baked into the model.

**In short:** scope one domain → read the docs (`[D]`) → interrogate the oracle with
minimal discriminating snippets (`[V]`) → write small-step rules that prefer
send+heap-mutation → tag every claim → leave `[?]` for differential testing → update the
index. Repeat per domain.
