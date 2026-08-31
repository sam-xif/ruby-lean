# Milestone plan — from "certified but untyped" to typing the Homebrew slice

**Planning artifact, 2026-08-30.** The *machinery* path. It does not restate the
design docs it depends on:

* [`slot-frame.md`](slot-frame.md) — the slot resource algebra (**SF-numbers**), and
  §10 for what is built.
* [`slot-frame-experiment.md`](slot-frame-experiment.md) + the measurements in
  [`../../spikes/slot-frame/RESULTS.md`](../../spikes/slot-frame/RESULTS.md) — E2/E3
  pass, E4 fails.
* [`judgment-layer.md`](judgment-layer.md) — `Judge`/`SemJudge`/`HJudge`, J0–J36.
* [`../../homebrew/slice-inventory.md`](../../homebrew/slice-inventory.md) — the
  *bill of judgments* for typing all eight files, in four tiers. **That document
  prices the judgments; this one sequences the machinery they need.** §6 below is
  the interlock.
* [`../../homebrew/slice-verdict.md`](../../homebrew/slice-verdict.md) §4a — the
  class-object rung ladder (1, 2, 2a, 2b, 3, 4), whose rung 3 this plan builds on.

---

## 1. The baseline, measured

**Every whole-file certificate in `certify/certs/` carries zero rows.**

| cert | `delta_rows` | `sem_assumes` | `defs` in the file |
|---|---|---|---|
| `cvss.jcert.json` | 0 | 5 | 5 |
| `semver.jcert.json` | 0 | 4 | 4 |
| `purl.jcert.json` | 0 | 2 | 2 |
| `identify.jcert.json` | 0 | 7 | 7 |
| `output.jcert.json` | 0 | 7 | 7 (`vulns/output.rb`) |
| `osv_export.jcert.json` | 0 | 8 | 8 |

`sem_assumes` equals the file's `def self.x` count in every case. So the accepts are
real but **vacuous in the intended sense**: each `def self.x` is admitted by the J51
`defsShapeB` schema (`validateJ_certifies_defs`), which is a fact about the *defining
step* and never looks inside the body. Nothing is declared; nothing composes. That is
the state this plan exists to end.

Three further measurements from the E2/E3 spike (`../../spikes/slot-frame/`):

1. **The name-global guard is exactly and solely what blocks a multi-row
   certificate.** On `"abc".to_s.length + 1.to_s.length` with three rows, today's
   `validateJ` rejects with `rowsGuarded = false` and every other conjunct `true`.
2. **All 26 `opaque_` install sites in the five certificated files are `def self.x`**
   (`semver` 4/4, `cvss` 5/5, `osv_export` 8/8, `purl` 2/11, `identify` 7/16). No
   `anyName`, no `eval`, no `class << self`.
3. **Two model defects found while measuring**, both in the eigenclass machinery and
   both cheap (§M1).

---

## 2. What already exists — do not rebuild it

* **The producer of class-object types.** `Judge.const` / `Judge.cpathScoped`
  (`Judgment/Judge.lean:589`, `:593`) conclude `.clsOf cname` from
  `constTy?`/`scopedConstTy?`, fed by J38b's claimed constants. `Homebrew::Vulns::CVSS`
  is typable *as a value* today.
* **`valueTy?` treats modules and classes identically** — `classRecv` asks only
  whether the id has a `ClassPayload`, and the type is keyed on the object's own
  qualified name (`Proof/Static/Locals.lean:163`). Module-ness is **not** a blocker;
  see §5's note.
* **The `srows` decision.** `slice-verdict.md` §4a rung 3 already settles *where*
  class-object rows go: a third `Decls` field, **not** a non-empty
  `tyClassNames (.clsOf n)` — one decidable obligation per row instead of a universal
  heap conjunct. Designed and de-risked (L186/L187), **not built**.
* **The frame algebra** works verbatim on an eigenclass id: an eigenclass is an
  ordinary object with a `ClassPayload` and a wired ancestor chain, and `def self.x`
  performs literally `defineMethod h e name md` (`Interp.lean:360`). SF1–SF8 need no
  change.
* **The semantic-judgment pattern**, twice instantiated: `SemJudge`
  (`Proof/Judgment/Sem.lean:87`) and `HJudge`'s four admission routes.

---

## 3. M0 first — the frame has to be *stated* before it can be proved

This is the update that reorders the rest of the plan, so it is stated before the
table.

The layer's discipline is: **a semantic predicate defined by reachability, mentioning
no checker; syntactic routes that manufacture facts of it, each with an adequacy
theorem; consumers stated over the predicate alone.** `SemJudge` is definitionally
free of `Judge` and `MFrag`; `HJudge`'s four routes collapse through one fundamental
lemma; `semJudge_sound` says "whatever supplied the `SemJudge`".

**The frame half-breaks that pattern.** `SlotClaim.Holds` is genuinely semantic and
`holdsB`/`holdsB_iff` is a textbook checker-plus-bridge — but `Holds` is a
**single-state** predicate, and `frameOkB` then conflates two unlike things:
`fp.holdsB Boot.initHeap` (a decided instance of a semantic predicate) with
`framedProgB` (a claim about the *program text*). The second is an **admission route
wearing the property's clothes**, and the property it is trying to establish is
*defined nowhere*.

That is the real reason SF-T3 reads as unbounded. "Every `defineMethod` the machine
performs while running `p` is one of `installsOf p`'s installs" is a statement about
the checker's enumeration, not about the claim's meaning — so it has no natural
induction hypothesis and **no other route can ever discharge it**.

The fix is a definition in `SemJudge`'s idiom:

```lean
/-- The claim survives running `e` from any conformant state. -/
def SemFrame (A : SemAxioms) (D : Decls) (Γ : Env) (e : Expr) (c : JCtx)
    (fp : SlotClaim) : Prop :=
  ∀ m, Conformant A D c Γ m → m.ctl = .eval e → fp.Holds m.heap →
    ∀ m', Reachable m m' → fp.Holds m'.heap
```

Three choices in it are load-bearing:

* **`Holds` at the start is a hypothesis, not a conclusion.** The judgment is about
  *stability*; "holds here" is decidable at a concrete heap and stays `holdsB`'s job.
  Same division of labour as `Conformant` being a hypothesis of `SemJudge`.
* **It quantifies over intermediate states (`Reachable`), not results
  (`ReachableResult`).** The one genuine difference from `SemJudge`: type-stuckness is
  a property of outcomes, but a row is *consumed* at every dispatch mid-run, so the
  claim must hold throughout.
* **No walk, no `InstallN`, no resolver in the definiens** — that is what makes other
  routes possible at all.

Then the routes mirror `HJudge`'s constructors:

| route | content | state |
|---|---|---|
| **syntactic** | `framedProgB fp f p fuel = true → SemFrame … p fp` | **this is SF-T3**, now with a statement to induct toward; the definee lemma in `../../lean/HANDOFF-SF.md` is its core |
| **direct semantic** | prove `SemFrame` by hand or by execution where the walk cannot read the program (`eval`, `def obj.x`) | the J31 pilot pattern verbatim |
| **Iris WP** | `Holds` is a heap predicate, so `stateIs`-based WP per conformant state | seat available (J36), unneeded today |
| **subsumption** | `holds_compose` already says composition *is* conjunction, so a composite's stability yields each conjunct's | free; the `HSub` analogue |

And the consumer discipline: row obligations take `SemFrame` (or a per-row corollary)
as hypothesis, and `validateJ_certifies` composes
`frameOkB → SemFrame → row stability → safety` with **`frameOkB` absent from the
statement**, exactly as `judge_sound_cert` has no checker in its statement.

**Why this is the ordering constraint and not a nicety.** `declaresName` is
*definitional* — a decidable predicate baked into the checker, sound locally. M6
replaces it with the frame. Without M0 that replaces a proof with a check, which is
the one move the C-ladder's whole architecture exists to prevent. M0 is also cheap: a
definition, a restated `frameOkB` docstring, and the honesty caveat promoted from a
comment to a theorem statement.

**One structural note.** This fits the **first-order** `SemJudge` pattern rather than
needing the H-layer, and specifically because all four `SlotClaim` components are
read-only (SF6), so the meaning is a plain heap predicate. If `slot-frame.md` §8's
flip condition ever fires and writes become resources, the meaning stops being a heap
predicate and the Iris route becomes mandatory rather than optional.

---

## 4. Milestones

| # | milestone | prereq | exit criterion |
|---|---|---|---|
| **M0** | **`SemFrame`** — state the frame semantically (§3): the reachability definition, `frameOkB` demoted to one route, consumers restated over the semantic predicate. SF-T3 becomes *a theorem with a statement*; it is not itself in this milestone. | — | `SemFrame` in `Proof/Judgment/`; the four routes' signatures written down (proofs may be `sorry`-free-by-absence, not stubbed); `frameOkB`'s docstring says "route", not "check with a caveat" |
| **M0a** ✅ | **Strip hygiene — a transform may not invent a head.** Reduce `alias` to constructs that already have a rung instead of promoting `fwd` to one (§4.1), and re-baseline `judge-slice.md` §5a's census. Independent of everything else; hours. **Landed 2026-08-30**, session log in `../../lean/HANDOFF-SF.md`. | — | no `fwd`/`pfwd` anywhere in the certified ASTs; `certify/certify-file.sh` output for all five strippable files censuses with heads drawn only from the rung ladder + tiers; §5a's table re-measured with the drift explained per file |
| **M1** ✅ | **Metaclass hygiene.** `eigenclassOf`: `if c.isModule then Boot.moduleId else Boot.classId` (`Interp/Dispatch.lean:199` — the `none` arm currently serves double duty as "top of chain" *and* "module"). And `enterScopedClassBody` must realize the eigenclass eagerly, as `enterClassBody` does. **Landed 2026-08-30** — the second defect was stale (already symmetric); the real cost was `NoHook`'s fresh-chain clause, which the model fix broke and needed a fourth (`Module`-chain) conjunct to repair. Session log in `../../lean/HANDOFF-SF.md`. | — | `spikes/slot-frame/Probe4.lean`-style ancestors match CRuby for module / class / nested module; difftest green; a regression case for `Module#new` raising `NoMethodError` once that builtin is modeled |
| **M2** ✅ | **Qualified names pin ids.** Extend `ClassOk`'s uniqueness clause past `readableClasses` to every class/module the certificate declares (`deltaClasses`/`deltaModules` are already checked at the boot heap by `classNameOkB`/`moduleNameOkB`), keyed on the **qualified** name. **Landed 2026-08-30** — `NamesUnique` was already the general clause; the missing piece was `className_inj_of_namesUnique`, its corollary at `className`. Session log in `../../lean/HANDOFF-SF.md`. | M1 | `className h k = n → className h k' = n → k = k'` for declared `n`; a `#guard` that the static definee spelling equals the heap's name for all five files (`Outer::Inner`, never `Inner`) |
| **M3** | **`srows`** — build rung 3, generalized from the single designed `Module#===` row to per-`(class-object, name)` rows, with its `DeclsOk` clause and one decidable obligation per row. | M2 | a `sigOf`-analogue answers for `.clsOf "Homebrew::Vulns::CVSS"` / `"base_score"`; `lake build Metatheory Judgment` axiom-clean |
| **M4** | **`self` as a class object** — the J11 widening the `Judge.self` docstring records as "refused for now" (`Judgment/Judge.lean:541` concludes `.cls cc`): inside a `defs`/`sclass` body conclude `.clsOf ctx.cls`, plus the implicit-receiver send that dispatches on it. This is what types `def self.severity`'s call to `base_score(vector)`. | M3 | `cvss.rb`'s `severity` typed with no semantic axiom; the toplevel case (`self` is `main`, an Object instance) still pinned apart |
| **M5** | **Eigenclass-aware install walk.** A `Definee` algebra (`cls` / `scoped` / `meta`) with `toName` = `eigenclassOf`'s own naming (`"#<Class:" ++ qualified ++ ">"`); an **injective** heap resolver replacing `bootResolver`; the two lazy-allocation preservation lemmas (allocation appends, and setting `.eigen` touches neither payload nor methods, so `slotOf` is invariant under both). | M1, M2 | E4 rerun: 26/26 `opaque_` sites become `defM`; E2 timings hold; program-declared classes resolvable |
| **M6** | **Drop name-globality.** Re-key `Decls` rows per `(class, name)` (`slot-frame.md` §7.1) and land **SF-T3** so the frame *replaces* `declaresName` instead of riding beside it. M3 makes this urgent rather than optional: class-object rows multiply the collisions E3 measured. | M0, M5 | E3's positive case accepts through the real `validateJ`; `validateJ_certifies` unconditional and axiom-clean; a certificate carries >1 row per method name |
| **M7** | **The bodies.** The remaining fragment walls, already itemized and priced in `slice-verdict.md` §3/§4 and `slice-inventory.md`: `send-with-block` (Wall 1 + Wall 2), the three `splat` rungs, ivars, `===` narrowing. Not re-derived here. | M4, M6 | per file: `sem_assumes = 0`, `delta_rows > 0`, `validateJ` accepts |

### §4.1 — M0a in full: reduce, do not promote

Measured 2026-08-30: the only head in the whole slice with no strategy anywhere is
**`fwd`/`send-fwd-arg`**, and it is *self-inflicted*. No slice source contains `(...)`;
`difftest/ruby/class_sugar_strip.rb:17` produces it, expanding

```ruby
alias eql? ==            # pkg_version.rb:59, version.rb:650, vulns/purl.rb:56
```

into `def eql?(...) = self.==(...)`. The expansion itself is right — `alias`'s miss
branch raises `NameError` and `CtlOkJ.jump _ => False` has no mode for it — but the
*target form* it expands to is a construct nothing can type.

**The rule, and it is the durable content of this milestone: a strip transform may only
emit heads that already have a rung.** Emitting a new one is a plan change, not a
transform detail, and it silently moves work from the pipeline (hours) to the judgment
layer (a rung with `fragHead` + `MFrag` + preservation + checker node + JSON + emitter).
Where a transform cannot honour the rule it should **gate** (`exit 3`), the same
polarity as every other gate in the pipeline, rather than emit and hope.

**The reduction for `alias`,** in preference order:

1. **Explicit arity**, when the target's `def` is visible in the same body:
   `def eql?(other) = self.==(other)`. Adds no head at all. Covers `version.rb` and
   `vulns/purl.rb`, which both define `==` in the aliasing class.
2. **`*args`**, when it is not: `def eql?(*args) = self.==(*args)`. `pkg_version.rb`
   is this case — it `include Comparable` (line 8) and defines no `==`, so no
   in-file lookup can recover the arity. Heads: a splat parameter and
   `send-splat-arg`, both of which have Tier-3 rungs. Add `**kw` only if the target
   may take keywords; that head has a rung too.
3. **Gate** if the target may take a **block**. `&blk` decodes to `blockpass`, which
   has no rung anywhere either — so forwarding a block is the same mistake in a
   different constructor. None of the three `eql?` sites can take one.

Note what this does to `slice-inventory.md`'s Tier 2 `alias` row ("2 sites · a slot
copy: the algebra's demo case"): it is wrong twice over — there are **three** sites, and
the certified artifact contains no `alias` at all, because the pipeline expands them.
The slot-copy demo is still worth having as a *frame* exercise, but it is not on the
path to certifying these files and should not be priced as if it were.

**Target end state**, per file: a certificate with `sem_assumes = 0`, rows claimed at
both instance and class-object receivers, accepted by `validateJ` unconditionally.

---

## 5. Critical path, ordering constraints, first cut

**Critical path: M1 → M2 → M3 → M4.** That is what ends the "certified but untyped"
state — the first real row at a class object and the first `def self.x` typed rather
than assumed. None of it is speculative: the producer, the key decision and the row
machinery are all either built or designed.

**M0 → M5 → M6** runs in parallel after M2, and is what lets one certificate hold the
whole file's rows at once. **M7** is the long tail.

Ordering constraints that are not preferences:

* **M2 before M5.** A heap resolver without name-uniqueness can resolve `CVSS` to the
  wrong id — unsound, not merely imprecise. (`Decls.supers`' docstring already records
  the general version of this: a row is quantified over *every* class object of that
  name, because "a program class's name does not pin an id".)
* **M0 before M6.** Otherwise the frame replaces a proof with a check.
* **M3 before M6.** So the re-keying is designed against the row population it will
  actually carry, not the instance-only one.

**Module-ness is not a blocker, and that is worth stating because it looks like one.**
The whole slice is `module X … def self.y`, but `valueTy?` types module objects and
class objects identically and `Ty.clsOf` is keyed on the object's own name. What bites
is (a) `clsOf` having no table key — M3, equally true of classes — and (b) *nesting*,
i.e. qualified names — M2. The only genuinely module-specific defect is the metaclass
superclass in M1, and it does **not** block this slice's rows: `def self.x` installs on
the front-most slot of the chain, so a row for `CVSS.base_score` owns `defined` there
with an *empty* `empty` segment. It blocks inherited class methods and any spine claim
below the front, and it is currently invisible to difftest (`module M; end; M.new` exits
3 as unsupported rather than answering wrongly).

**Cheapest first cut, if a signal is wanted before committing:** M1 alone (two lines
plus tests), then M5 as a spike to confirm the 26/26 conversion. Both are hours, and
M5's number is what says whether the frame half of this path is worth starting.

---

## 6. Interlock with `slice-inventory.md`

That document's four tiers price the *judgments*; this plan sequences the *machinery*.
They meet at three points, and the meeting corrects one thing in each direction:

* **Its Tier 0** (generated slot resources: ~114 `defined`, ~35 spines) assumes the
  footprints can be *named and resolved*. That is M2 + M5. Its counts are unaffected;
  its emitter is not writable before them.
* **Its Tier 2 `defs` schema** is the J51 pre-discharge route — it makes a `def self.x`
  *definition* admissible. It does **not** type a *call* to one; that needs M3 + M4.
  So "typed bodies for `cvss.rb`/`semver.rb`" in its sequencing step 1 is gated on M3
  and M4, which its ladder does not currently name.
* **Its consumption rule** — each tier row discharged by a named artifact, then re-run
  the §5a census — is the right ratchet for M7, and this plan's exit criteria are
  written to feed it (`sem_assumes` per file is the number to watch, and it is already
  measured in §1).

Conversely, the honest note its closing paragraph makes — that the accepts this path
produces are **conditional** where today's six are unconditional-but-vacuous — is
exactly what M0 makes auditable rather than a matter of trust: the conditions become
named `SemFrame`/`SemAxioms` residues in the certificate instead of a weakened guard.

---

## 7. Evidence

Everything in §1 and §5 is re-runnable:

| claim | how |
|---|---|
| cert rows / `sem_assumes` table | `python3 -c` over `certify/certs/*.jcert.json` (`delta_rows`, `sem_assumes`) |
| the 26 `opaque_` sites | `spikes/slot-frame/run.sh census` |
| the name-global guard is the sole blocker | `spikes/slot-frame/run.sh e3` |
| decidability cost | `spikes/slot-frame/run.sh e2` |
| boot-heap eigenclasses (ids 40/41, empty tables) | `lake env lean --run ../spikes/slot-frame/Probe3.lean` |
| module vs class metaclass chains | `lake env lean --run ../spikes/slot-frame/Probe4.lean`, against `ruby -e 'module M; end; p M.singleton_class.superclass'` |
| `fwd` is strip-introduced, not in the source | `grep -c '(\.\.\.)'` over the eight slice sources (all 0) vs `grep -n 'eql?'` on the `class_sugar_strip` output |
| the three `alias` sites | `grep -rn '^\s*alias '` over the eight slice sources |
| `M.new` is unsupported, not wrong | `harness/desugar-dt/bin/export-json` + `lean/.lake/build/bin/rubycore` |
