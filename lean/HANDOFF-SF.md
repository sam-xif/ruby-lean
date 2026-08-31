# HANDOFF — the slot frame (SF), 2026-08-28

Design: `../docs/semantics/slot-frame.md` (§10 lists the files). This note is the
*next-session* view: what is load-bearing, what is decoration until SF-T3, and
the proof plan for the one missing bridge.

## Built and green

`lake build Judgment Metatheory HJudge` all clean; `RubyCore.Proof.Static.Frame`
is axiom-clean (`propext`, `Quot.sound`, `Classical.choice`).

* **The algebra** — `Types/SlotClaim.lean`. `Holds` (Prop) / `holdsB` (kernel
  Bool) / `holdsB_iff`. `compose` concatenates with a `defined`-agreement guard.
* **The walk** — `Types/SlotWalk.lean`. Fuel-bounded, *not* `partial`, precisely
  so SF-T3 can induct over it.
* **SF-T1** `ResolvesAt_defineMethod_frame` / `_slot` — resolution survives a
  same-name `def` off the owned segment. The design's stated risk (that this
  would fight the shadow clause) did not materialize: `crubyShadow` reads only
  `className`.
* **SF-T2** `Holds_defineMethod` — a whole footprint framed by one
  non-conflicting write.
* **`holds_compose`** (composition is conjunction) and **`row_lookupIn`** (SF7's
  `Row` entails its resolution).
* **SF-T4's wire half** — `JCert.footprint`, `frameOkB` in `validateJ`.

## The one thing that is *not* proved, and must not be assumed

`frameOkB` passing does **not** yet imply a claim survives running the program.
Missing: *every `defineMethod` the machine performs while running `p` is one of
`installsOf p`'s enumerated installs.* Both endpoints exist (SF-T2 frames one
write; the walk enumerates the sites); the bridge is an induction over `stepFn`.

Until it lands the frame is **additive**: `validateJ_certifies` is still carried
by `declaresName`'s name-global guard, and adding `frameOkB` only strengthens
`validateJ`'s hypothesis, so every existing accept and every existing theorem is
untouched. The caveat is written into `frameOkB`'s docstring so it cannot be
read off the code as more than it is.

### The bridge needs a *statement* first (2026-08-30)

`../docs/semantics/typing-the-slice-milestones.md` §3 (milestone **M0**) revises the
plan below rather than replacing it. The diagnosis: `SlotClaim.Holds` is a
**single-state** predicate, and `frameOkB` conflates a decided instance of it
(`holdsB Boot.initHeap`) with `framedProgB`, a claim about the *program text* — an
admission route wearing the property's clothes. The property the route should establish
is defined nowhere, which is why the obligation below reads as unbounded: it is phrased
over the checker's enumeration, so it has no natural induction hypothesis and no other
route can discharge it.

Define it in `SemJudge`'s idiom first — `SemFrame … fp` = in every conformant state at
which `fp.Holds` holds, `fp.Holds` holds at every **reachable** state (intermediate
states, not just results: a row is consumed at every dispatch). Then the plan below is
the *syntactic route's adequacy theorem*, three more routes exist (direct semantic,
Iris WP, subsumption via `holds_compose`), and consumers can be stated with `frameOkB`
absent from the statement. M0 must land before the frame replaces `declaresName`, or
that replaces a proof with a check.

### Proof plan for the syntactic route (this is SF-T3's core)

1. State it as a step-level obligation: `stepFn` at a machine state whose control
   is a subterm of `p` either leaves the method tables alone, or performs a
   `defineMethod cls name md` for which `.defM (className cls) name ∈ installsOf p`.
2. The definee is the load-bearing coordinate: the walk tracks it lexically, the
   machine tracks it in the frame. Those two must be related — expect a lemma
   "the machine's definee at a subterm equals the walk's `definee` for that
   subterm", which is where `sclass`/`defs` being `opaque_` earns its keep.
3. With that, `Holds` preservation across `step` is SF-T2 plus the enumeration,
   and across `ReachableResult` it is the obvious induction.

Do **not** start by re-keying `Decls` rows per `(class, name)` (§7.1's
demolition). That is a large refactor whose payoff depends on this bridge; the
frame cannot replace `declaresName` before it can preserve a claim across a run.

## Smaller open items

* `bootResolver` knows boot classes only, so a footprint naming a
  program-declared class is rejected. SF9 says claims live at the conformant
  *start* state; resolving against the post-prefix heap is the fix.
* `defs` / `class << self` are `opaque_` (no eigenclass in the heap model), so a
  `defs`-bearing program needs a trivial footprint today.
* `Types/SlotClaimEg.lean` is the executable spec of the intended behaviour —
  §1's two measured blockers, SF8's table in both polarities, the walk on
  syntax. Extend it before changing semantics; every entry there is a `#guard`.

---

## Session log (2026-08-28) — final verified state

Branch `sam-xif-investigation`, working tree clean. Seven commits, oldest first:

| commit | what |
|---|---|
| `0859d48` | SF1–SF8 + SF-T1/SF-T2 — the algebra and the frame rule for one step |
| `fd34fa9` | `compose` simplified to concatenation; `holds_compose`; `row_lookupIn` |
| `f5b0781` | `SlotClaimEg` — the two measured blockers cleared, SF8 in both polarities |
| `83bfcb7` | `SlotWalk` — §5 step 2, the install inventory |
| `644c9f6` | SF-T4's wire half — `JCert.footprint`, `frameOkB` in `validateJ` |
| `286a5f6` | docs — `slot-frame.md` §10, ladder status, `docs/semantics/README.md` |
| `f474901`, `cde8891` | this handoff + the honesty caveat on `frameOkB` |

(Hashes are this branch as of the commit above; the table is the order, not a
promise about rebases.)

### Verification actually run

* `lake build` (the SUT + `rubycore` exe) — 110 jobs, success.
* `lake build Judgment Metatheory` — 106 jobs, success. `validateJ_certifies`
  needed only its `obtain` pattern widened for the new `&&` conjunct.
* `lake build HJudge` — 298 jobs, success (Iris seat unaffected).
* `#print axioms` on the four new headline theorems: `propext`, `Quot.sound`,
  and `Classical.choice` for `ResolvesAt_defineMethod_slot`. No `sorryAx`.
* Every `#guard` in `SlotClaimEg.lean` and the three new ones in
  `Proof/Judgment/Adequacy.lean` elaborate.

**One pre-existing red, not mine:** `scripts/check-proofs.sh` ends with
`heapOkB (prelude-booted): false` / `FAIL: the prelude-booted heap does not
satisfy the heap half of Inv`. Verified by stashing the whole working tree and
re-running — identical failure without any SF code. Untouched here; it wants its
own session.

### If you are picking this up cold

Read, in order: `../docs/semantics/slot-frame.md` §§1–3 (why locality), then
`Types/SlotClaimEg.lean` (the intended behaviour, executable), then "The one
thing that is *not* proved" above. Do not read `Proof/Static/Frame.lean` first —
its lemmas are elementary and will make the layer look more finished than it is.

---

## Session log (2026-08-29) — E2 and E3 of the experiment memo

`../docs/semantics/slot-frame-experiment.md` E2 (V2, decidability cost) and E3
(the artifact) were run in `../spikes/slot-frame/`; full numbers and the
reproduction script are in `../spikes/slot-frame/RESULTS.md`. Nothing under
`RubyCore/` was touched — the E3 weakening is a name-distinct local copy
(`validateJF`), so `validateJ_certifies` still cannot depend on the unproved
bridge.

**E2 — PASS.** `by decide` on `frameOkB`'s inlined body, baseline-subtracted,
best of two, no `native_decide`:

| program | installs | 3 rows | 10 rows | 25 rows | 50 rows |
|---|---|---|---|---|---|
| `egEven` | 0 | 0.19s | 0.27s | 0.39s | 0.51s |
| `semver.rb` (201 nodes) | 4 | 0.14s | 0.22s | 0.32s | 0.45s |
| `identify.rb` (787 nodes, largest slice AST) | 16 | 0.13s | 0.26s | 0.32s | 0.42s |
| `synth200` (no short-circuit) | 200 | 0.64s | 0.83s | 1.21s | 1.71s |
| `synth800` (no short-circuit) | 800 | 2.10s | 2.74s | 4.06s | 5.73s |

Threshold was "25 rows × a real slice AST in a few seconds": **0.32 s**. Linear
in both dimensions (×16.7 in rows costs ×2.7; ×4 in sites costs ×3.4), so the
memo's redesign branch — per-class name sets instead of per-slot lists — is not
needed and the current footprint shape can be built on. `maxRecDepth` must rise
above the default 512 (2048 for `identify` × 25, 4000 for the whole grid);
`Proof/Judgment/Adequacy.lean` already sets 100000, so certificates pay nothing
new. The real-slice rows short-circuit at their first `opaque_` site, which is
why the `synth` rows are there — they resolve every site and conflict on none,
so they pay the full installs × footprint cross-product.

**E3 — PASS, negative case included.** `"abc".to_s.length + 1.to_s.length` with
three rows (`String#to_s`, `Integer#to_s`, `String#length` — `length` is forced
too, so the set collides at *two* names). Today's `validateJ` rejects and
`rowsGuarded` is the **only** failing conjunct (`frameOk=true check=true
mfrag=true fragHead=true ground=true`): the name-global guard is solely what
rejects it. With the disjunct, `validateJF = true`. Against
`class String; def to_s; 1; end; end` it rejects with `frameOk=false`. Isolating
the frame from the other conjuncts, `frameOkB` alone is `true` on the bare
program, `false` after `def String#to_s` *and* after `def String#length`, `true`
after a benign `def Symbol#shout` (so it is not merely permissive), and `false`
after `def Version#to_s` (the closed-world cost — `bootResolver` cannot place a
program-declared class). The kill criterion "the negative case accepts" did not
fire; no soundness bug in `Install.conflicts`. The accepted program runs on the
model to `Value.int 4`.

**E4, answered as a byproduct — FAIL.** E2 needed real slice ASTs and therefore
the census. All five certificated `vulns/` files carry `opaque_` sites, and every
single one is `def self.x`: `semver.rb` 4/4, `cvss.rb` 5/5, `osv_export.rb` 8/8,
`purl.rb` 2/11, `identify.rb` 7/16. No `anyName`, no `eval`, no `class << self`.
So V3 fails on this slice as written — a nontrivial footprint over any of these
files is rejected today, and **eigenclass modelling is the prerequisite**, per
the memo's own kill row. Note also that E4's stated pass criterion is not the one
the code implements: `InstallN.framedBy` maps `opaque_` to
`SlotClaim.isTrivial`, class-blind, so *any* `opaque_` anywhere kills every
nontrivial claim. Counting only "`opaque_` on classes a row reads" would have
reported zero — a pass — for a check that rejects. Count sites.

**Not run:** E1 (row density, sizes the prize). Its numbers are the input to the
park-or-invest decision, and the E4 result above changes what that decision is
about: on this slice the binding constraint is the eigenclass, not row density.

---

## Session log (2026-08-30) — M0a, M1, M2 (`typing-the-slice-milestones.md`)

All three landed. Details, verification, and re-measured numbers are in
`../docs/semantics/typing-the-slice-milestones.md`'s own record and
`../homebrew/judge-slice.md` §5a (M0a's re-census); this is the short version.

**M0a — strip hygiene.** `difftest/ruby/class_sugar_strip.rb`'s `alias` expansion
no longer emits `(...)` (`fwd`/`pfwd`, the one head in the slice with no rung):
explicit arity when the target `def` is in the same body (`version.rb:650`,
`vulns/purl.rb:56` — adds no head at all), else `*args` (`pkg_version.rb:59` —
`include Comparable`, no in-file `==` to read arity from), gate (`exit 3`) if the
target takes a block (no site does). Re-census over the five strippable files:
no `fwd`/`pfwd` anywhere, every head already on the ladder, and all four
whole-file certs that existed before this session (`semver`, `purl`, `cvss`,
`identify`) still `--certify-j accept` unconditionally, including the committed
`certify/certs/purl.jcert.json` against the regenerated AST (its `sem_assumes`
never mentioned `eql?` to begin with). `version.rb`'s pre-session "~44 → 68"
drift is *not* explained by this fix (measured before/after: 69→67 effective,
155→153 total — exactly the `fwd`+`send-fwd-arg` pair removed, nothing else) and
stays open; a partial, unverified lead (nested `Token` classes) is noted in
`judge-slice.md` §5a.

**M1 — metaclass hygiene.** One-line model fix, `Interp/Dispatch.lean`'s
`eigenclassOf`: the `none` arm (top of the metaclass chain) now answers
`Boot.moduleId` for a module, `Boot.classId` for a class, matching CRuby
(`Class.superclass == Module`). `enterScopedClassBody` already realized the
eigenclass eagerly (symmetric with `enterClassBody`); the plan's second defect
was stale. Verified against `ruby -e` for module/class/nested-module
(`spikes/slot-frame/Probe4.lean`) — ancestors match exactly. Ratchets: tier-0
940→**992** agree (0 disagree, up), tier-4 **25/28** agree (0 disagree,
unchanged). Regression case added
(`difftest/corpus/regressions/module-new-nomethoderror.{rb,json}`) — filed as
the tripwire for a wrong `Module#new` resolution, and it turned out to already
*agree* with CRuby (`NoMethodError`) once the fix landed, no separate builtin
needed; sidecar declared `fixed`, not `open`.

**The trap the plan named, and it was real:** the fix broke
`NoHook`'s "J44 fresh-chain half" (`Proof/Static/Decls.lean`) — its docstring's
own claim that "a freshly-allocated class's walk... tail is always `Class`'s
chain" is now false for *modules*. Not a hardcoded `ObjId` (the T5Loop
precedent); a genuine missing case. Fix: widened `NoHook` to a fourth conjunct,
hook-freeness along `Module`'s chain, mirroring the `Class`-chain clause
structurally at every construction site (`NoHook_grow`, `NoHook_defineMethod`,
`noHookB`/`noHookB_sound`, `noHook` (`IvarOnly`), `noHook_constSetIn`,
`noHook_fresh`, `noHook_freshC`) — six sites, each a copy-paste of the existing
clause at `Boot.moduleId` instead of `Boot.classId`. A first attempt tried to
derive the module clause *from* the class one (a `ChainsIn.classSup` field
recording `Class.superclass = Module`) — abandoned mid-flight, reverted clean,
because it needed the invariant to carry through every allocation site for a
fact `NoHook`'s parallel clause gets for free. `lake build` (110 jobs),
`Judgment Metatheory` (106 jobs), `HJudge` (298 jobs) all clean;
`noHook_fresh`/`noHook_freshC`/`NoHook_grow`/`NoHook_defineMethod`/
`noHookB_sound`/`noHook_constSetIn` all `#print axioms` clean (`propext`,
`Quot.sound`, only `Classical.choice` where it was already there).
`check-proofs.sh` ends exactly at the pre-existing `heapOkB (prelude-booted):
false` — no new red.

**M2 — qualified names pin an id.** `NamesUnique` (`Proof/Static/Decls.lean`)
was already the *general* uniqueness clause (any two class objects sharing a
non-`#`-headed name are the same object) — already proven at boot, already
preserved through every step including fresh module/class allocation
(`classOk_fresh`/`classOk_freshC` already carry it). What was missing was the
corollary stated the way a certificate reads a name: `className_inj_of_namesUnique`,
proved in the same file, `className h k = n → className h k' = n → k = k'`
given both `k`/`k'` are class objects and `n` isn't `#`-headed. `Decls.supers`'
docstring (`Types/Decls.lean`) updated to point at it instead of naming the gap.
Verified with an executable check (`spikes/m2-qualnames/`, Probe4.lean's
idiom rather than an inlined `#guard` — the five ASTs are 200-1300 nodes from
the gitignored vendor checkout): for all five strippable files, the certificate's
static `(owner, name)` spelling resolves, post-run, to a heap object literally
named `qualifyMod owner name` — PASS, including `pkg_version.rb`, which gates
on `Comparable` mid-body but has already allocated `PkgVersion` correctly by
then. `lake build Metatheory Judgment` axiom-clean.
