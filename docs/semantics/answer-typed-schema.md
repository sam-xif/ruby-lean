# The answer-typed schema — the target shape for `ratchet/`, and how to get there

> **Status:** reshaping specification, 2026-09-11. This is a *work order*, not a findings
> artifact: it says what `ratchet/` should look like and how to move it there. The design it
> encodes is [`answer-typed-judgments.md`](answer-typed-judgments.md) (diagnosis §1–§5,
> proposal §6, **built** §10); the shape below is that proposal generalised, plus everything
> the prototype (`ratchet/Denote/Proto/`) learned by closing it end to end.
>
> Evidence tags as in [`README.md`](README.md): **[V]** verified here, **[M]** mechanised
> here, **[D]** documentation/literature, **[?]** open, **[✗→]** a correction of a
> plausible-but-false claim recorded so it is not reintroduced.

---

## 0. How to use this document

You are reshaping `ratchet/` to the schema in §3. Read in this order:

1. **§1 — the two norms specific to this work.** They override habit. Read them twice.
2. **§2 — the standing norms.** Already written down elsewhere; they still bind.
3. **§3 — the schema.** Seven layers, with the target signature of each.
4. **§4 — what is already built.** Reuse it; do not rebuild it.
5. **§5 — what to delete.** An explicit list. Deleting it is part of the job, not a
   clean-up you may skip.
6. **§6 — the migration**, in commit-sized steps, with the one step where the build cannot
   stay green and what to do about it.
7. **§7 — the named gaps**, each already a `Prop` somewhere. Do not rediscover them.
8. **§8 — acceptance criteria.** Checkable; run them.
9. **§9 — the four temptations**, each of which has already been tried and measured.

---

## 1. The two norms this reshaping adds

### Norm A — state the general version of every theorem

**Default to universally quantifying every index a statement mentions.** Specialise only where
a *requirement* prevents generality, and when it does, say so in the docstring, name the
requirement, and give the specialisation a separate name so the general statement is still the
one on file.

This is not style. The prototype's `psemJudge_of_pjudge` was written at `Γ = []` — the
environment a *whole program* starts at — and it was **useless for the only job an adequacy
theorem has**, because a sub-derivation of a larger program lives at a non-empty environment.
Generalising it required **no change to any proof**: the generality was already there and
missing only from the statement (commit `fc5fc5f`). That is the failure mode — a statement
weaker than its own proof, discovered only when something downstream needs the strength.

Concretely, in this work:

* Quantify `κ`, `Γ`, `I`, `τ`, `m` unless something names a specific one.
* When a premise names `ctx0` (as `PJudge.vasgn`'s `capStaleCtx` does), *that* is a real
  requirement — record it as the reason, and keep the theorem general in everything else.
* A whole-program corollary is fine and useful; derive it *from* the general theorem, never
  the other way round. `checkedAt_implies_safe` / `checked_implies_safe` in
  `Denote/Proto/Checker.lean` §3 is the pattern.
* If you cannot see how to generalise, write the general statement down as a named `Prop`
  anyway (§2's standing rule) and prove the specialisation under it.

### Norm B — do not be married to what is already in the code; delete dead code liberally

**A definition that nothing consumes is a liability, not an asset.** This package's value is
that every named thing means something and is either proved or explicitly owed; a file full of
superseded statements destroys that property faster than an unproved one does, because an
unproved statement announces itself and a dead one does not.

* **§5 is a delete list, and it is mandatory.** If you finish the migration with those
  definitions still present, the migration is not finished.
* **Prefer replacing a proof body over adding a second theorem.** `run_split` should keep its
  name and consumers and lose its 82-line induction in favour of the three-line derivation
  from `run_pushK`; that is a strictly better outcome than `run_split` *and* `run_split_A`
  both existing.
* **A refutation is not dead code.** `not_KontFrame`, `not_catchFree_catchK`,
  `not_jumpOpaque_definedGuardK`, `not_semJudgeImpliesStuckFree` all stay: each pins a
  tempting statement as false so it cannot be reintroduced. Distinguish "superseded" (delete)
  from "refuted" (keep, and keep the counterexample).
* **A measurement is not dead code.** `probes/` stays.
* **Do not preserve a theorem because it was expensive.** `WhileStuck2.lean`'s
  `loop_stuck_of_jumps` took a session and is proved modulo two hypotheses that are *false*.
  Its content is recorded in `answer-typed-judgments.md` §2.3 and `WhileAnswer.lean`'s header.
  Delete the file.
* When you delete, say in the commit message **what replaced it** — that is what makes the
  deletion reviewable.

---

## 2. The standing norms, which this does not restate

Read these; they are not repeated here.

| where | what |
|---|---|
| [`certificate-language.md`](certificate-language.md) §7 | the seven working norms in force for trusted-code work: decision records, atomic commits, files under 1,000 lines and one concern each, ratchet discipline (**tier 0, 0 disagreements, at every commit**), **no `native_decide` on the checked path**, oracle-first, and directory isolation |
| [`PROCEDURE-authoring-semantics.md`](PROCEDURE-authoring-semantics.md) §0 | the invariants every semantics artifact must hold |
| `ratchet/AGENTS.md` §Claim-free | a rung carries no certificate the checker may believe; `validate` synthesizes or answers `false` |
| `ratchet/AGENTS.md` §Isolation, §Architecture | why `Ratchet/` imports nothing from `../lean/`, and why `Semantics/` is the one deliberate exception |
| `ratchet/AGENTS.md` §"What is deliberately not built here" | scope fences; check before widening any |
| `ratchet/HANDOFF.md` §"The working rule this session paid for twice" | **write the layer's target down as a named `Prop` before proving the layer under it.** `FrameLocal.lean`'s 532 lines were proved for a target that was never stated, and the target turned out false |
| `Denote/Sem/Obligations.lean` module docstring | obligations are *derived* from the inductive, never transcribed; and a rung counts only when its type is **defeq** to the derived obligation |
| `Denote/Sanity.lean` | `#guard`-conditional theorems rather than `native_decide`, and why; also the vacuity check that a conformance witness exists |
| `ratchet/found-issues.md` §F24 vs §F25 | **run the control.** A rejection is only a finding if the same program with the feature removed is *accepted*; otherwise you have measured an absence |

Two house conventions worth naming because this work will exercise them constantly: every
top-level theorem gets a `#print axioms` line and must show only
`propext`/`Classical.choice`/`Quot.sound`; and **no `sorry`, ever** — an incomplete inductive
with fewer constructors is honest in a way that a complete one with `sorry`ed cases is not
(`Denote/Sem/Invariant.lean`'s `KontOk`).

---

## 3. The schema

Seven layers. Each row's "prototype" column is a working instance at four rules, proved end to
end, which you should read before writing the real one.

| # | layer | target | prototype |
|---|---|---|---|
| 1 | certificate language | `Deriv` | `PHint` |
| 2 | checker | `check` / `validateD : Bool` | `pcheck` / `pvalidate` |
| 3 | checker soundness | `check_sound : check … = some … → Judge …` | `pcheck_sound` |
| 4 | the judgment, answer-typed | `SemJudgeA` | `PSemJudge` |
| 5 | adequacy | 83 derived obligations, one ladder | `psemJudge_of_pjudge` |
| 6 | the invariant | `CtlOk` + `KontOk` + `Inv` | `PInv` |
| 7 | safety | `SafetyObligations` + `InvInit` | `pInv_obligations` |

### 3.1 Layer 4 is the keystone: `SemJudgeA`

Replace `Denote/Sem/Judge.lean`'s `SemJudge` with the answer-typed form. The hypothesis becomes
an **answer** rather than a value, which is the whole point: an escaping run no longer
satisfies the obligation vacuously.

```lean
def SemJudgeA (κ : Ctx) (Γ : Env) (I : Ty) (e : Ratchet.Expr) (τ : Ty)
    (κ' : Ctx) (Γ' : Env) (I' : Ty) : Prop :=
  Plain e ∧
  ∀ m : Machine, StateOk κ Γ I m →
    ∀ (fuel : Nat) (a : Answer) (m₀ : Machine) (rest : Nat),
      runA fuel (evalFrom m e) = .ans a m₀ rest →
      Framed m m₀ ∧ AnsOk τ m₀ a ∧
      (∀ v, a = .val v → StateOk κ Γ' I' m₀ ∧ StateOk κ' Γ' I' m₀)
```

* **Keep `Plain`** — same reason as today (`Judge` has no rule concluding about argument-list
  syntax, and the semantic reading has to say so).
* **Keep `Framed`** and keep it on *both* arms: a rule that pushes a frame must restore it
  whether the sub-run returned or escaped.
* **Keep both outgoing conformance conjuncts** (`κ` and `κ'`), for the reason
  `Denote/Sem/Judge.lean` §"Outgoing conformance" gives: neither direction transports and
  `ConstsOk` makes the down-transport false.
* **The outgoing state is claimed on the `val` arm only.** What holds at an *escape* is
  rule-specific — it is `nxtPrefixOk`'s content at a loop (§F23) and `excName?`'s at a `raise`
  (§F25) — so it belongs in the rule's own premises, surfaced through `AnsOk`, not in the
  judgment's shape. `Denote/Rules/WhileAnswer.lean`'s `AnswerOkAt` is the per-rule form.

`AnsOk` is where the second axis now lives:

```lean
def AnsOk (τ : Ty) (m₀ : Machine) : Answer → Prop
  | .val v => denM τ m₀ v
  | .esc j => EscOk m₀ j
```

**`EscOk` is the one place the prototype cheated, and Norm A forbids repeating it.**
`Denote/Proto/Safety.lean` sends `retJ`/`throwJ` to `False` because they are outside the
fragment. The general form must state the actual obligation, because at an empty continuation
both *step* — to a `raiseErr` carrying `LocalJumpError` / `UncaughtThrowError` — and whether
those classes are in the type-error family is a fact about the heap's class table, not a
constant:

```lean
def EscOk (m₀ : Machine) : Jump → Prop
  | .raiseJ exc  => Semantics.isTypeError m₀.heap exc = false
  | .retJ _ _    => Semantics.isTypeError m₀.heap ⟨LocalJumpError at m₀.heap⟩ = false
  | .throwJ _ _  => Semantics.isTypeError m₀.heap ⟨UncaughtThrowError at m₀.heap⟩ = false
  | _            => True   -- brk/nxt/redo/retry: `unwind []` is `.stuck`, not type-stuck
```

The two middle arms are discharged once, from `StateOk`'s `CoreOk`/class-table components —
they are facts about the *booted hierarchy*, not about the program — so write them as two
named lemmas over `StateOk` and let every rule consume them. If they turn out to need more
than `StateOk` provides, that is a finding: record it in `found-issues.md` and state the
missing component as a `Prop`.

**Why this is lossless [M]:** `StepResult.uncaught` is constructed at **exactly one site** in
the whole interpreter — `RubyCore/Interp/Kont.lean:341`, `unwind`'s `[]` arm on a `raiseJ` —
so every type-stuck outcome is an `esc (.raiseJ exc)` answer, possibly after one `raiseErr`
hop. Folding the two ladders into one answer-indexed obligation therefore loses nothing.
`grep -rn "\.uncaught" RubyCore/Interp*.lean RubyCore/Interp/*.lean` is the check; re-run it if
the interpreter changes.

### 3.2 Layer 5: the ladder survives the restatement, mechanically

`Denote/Sem/Obligations.lean` derives the 83 obligations by substituting one constant for
another inside each `Judge` constructor's type. **Changing `SemJudge` to `SemJudgeA` is one
edit to `judgeFamily`'s second column.** Everything else — the derivation command, the
`Obl.*`/`Sem.*` naming, `Denote/Ladder.lean`'s counting, `Denote/Adequacy.lean`'s
`AdequacyHyps` fold — is reusable verbatim. Do not rewrite it.

**And the two-ladder framing goes away.** `Denote/Adequacy.lean`'s `StuckFreeTarget` exists
because `SemJudge` had no progress content; under `SemJudgeA` it is a *consequence* of
`AdequacyTarget`, not a parallel statement. Delete it and say so (§5).

### 3.3 Layer 6: `CtlOk`, `KontOk`, `Inv`

`Denote/Sem/Invariant.lean` states the shape; the work is `KontOk`. Four things fix it, all
already established:

1. **36 constructors, not 15** [V]. `probes/kont_census.lean` walks every corpus program under
   the real `stepFn`: 36 of 49 `Kont` constructors are ever pushed, and restricting to the
   judged fragment removes **nothing**, because `Judge` covers `send` and the send spine
   reaches most of the frame set on its own. Plan against 36.
2. **Two clauses per frame**, a value clause and an escape clause. The escape clause is where
   the premises §2.1 called unconsumable finally get consumed.
3. **Indexed by the answer type `τa`** — the type the *empty* continuation accepts. Discovered
   the hard way (`Denote/Proto/Safety.lean` §9): with `nil` accepting anything, the invariant
   proves **safety while proving nothing about types**, because `Inv`'s `∃ τ` forgets what the
   certificate claimed. This is Wright–Felleisen's context typing `E : τ ⇒ τ_ans` [D].
4. **Indexed by the live `catch` tags.** `catchFree_iff_tagsOf_nil` [M] shows `CatchFree K` is
   exactly "`K` intercepts nothing", i.e. the empty protocol; a reachable machine inside a
   `catch` has a non-empty one. This is Essence-of-Ruby's exception context `T` and Hazel's
   protocol [D]. See §7 for what it costs.

`CtlOk` must also carry the **image condition**: the machine holds `RubyCore.Expr` and the
judgment is over `Ratchet.Expr`, so the `.eval` arm asserts the expression in flight is
`toRuby e₀` for a judged `e₀`, and `preserved` owes "an `Inv` machine never steps out of
`toRuby`'s image". No `SemJudge` obligation has ever had to say this.

### 3.4 Layers 1–3: the certificate and its checker

`Deriv` mirrors `Judge`'s constructors and should be **derived from the inductive** the way the
obligations are, not hand-written — 83 hand-transcribed constructors is 83 chances to let a
certificate mean something the rule does not.

**Where hints carry information and where they do not** is the design question, and the
prototype answers it: a hint is a *tag* wherever the rule is syntax-directed (a literal's type,
a variable's from `Γ`, an assignment's from its right-hand side) and *load-bearing* wherever it
is not. `Judge.brk` types `break` at any `τ`; `PHint.brk` therefore carries the type and no
checker can infer it. Expect the same at `raise`, at the `.never` family, and at every join.
That is the general reason a certificate language exists.

`check_sound` is one induction on the certificate. Per Norm A it must be `∀` over `κ`, `Γ`,
`I` — `pcheck_sound` already is, and the prototype's *downstream* theorems were the ones that
forgot.

### 3.5 Layer 7: safety, already proved

`Denote/Sem/Invariant.lean`'s `safety_of_invariant` takes `SafetyObligations Inv` — `preserved`
plus `noBadStep` — and is proved for an **abstract** `Inv`. Instantiate it; do not restate it.
Note what is not an obligation: **progress in the usual sense.** Ruby programs legitimately
raise, diverge and gate, so the bad-state predicate is `typeStuck` and the second obligation is
a bad-*step* exclusion. That is why divergence is free (`.outOfFuel` is not type-stuck) and why
no termination argument appears anywhere.

### 3.6 The two routes to safety, and which one scales

```
validateD p cert = true
        |  check_sound
        v
   Judge κ Γ I p τ κ' Γ' I'
        |                          \
        |  InvInit                  \  adequacy (layer 5)
        v                            v
   Inv τ (evalFrom m p)          SemJudgeA … p τ …
        |  safety_of_invariant        |  stuckFree_of_semJudgeA
        v                             v
                   StuckFree m p
```

Both are proved at prototype scale (`checked_implies_safe` / `checked_implies_safe'`) and they
agree. **The left route is the one that scales**; the right needs `UncaughtInv` (§7) to rule out
a run that halts without delivering an answer. Build the left; keep the right as the statement
that makes `SemJudgeA` the right *shape*, and prove it generally when `UncaughtInv` lands.

---

## 4. Already built — reuse, do not rebuild

| what | where | note |
|---|---|---|
| `Answer`, `answerPoint`, `runA`, `ARes.out`, **`run_pushK`** | `Denote/Sem/Answer.lean` | the master equation; one hypothesis (`CatchFree`), five outcomes accounted for |
| `SafeKont`, `Delivers`, `HaltBlind`, `safe_pushK{,_le}`, `delivers_safeA`, `runA_add`, `runA_rest_le`, `run_le_eq`, `answerPoint_of_ans`, `deliverA_nil_self` | `Denote/Sem/SafeKont.lean` | the fuel arithmetic a back edge needs; `SafeKont` is a **per-rule** tool, not a whole-machine invariant (§9) |
| `catchFree_iff_tagsOf_nil`, `tagsOf`, the handler-family `CatchFree` lemmas, `not_jumpOpaque_definedGuardK` | `Denote/Sem/AnswerCatch.lean` | why `CatchFree` survives; the protocol reframing |
| `SafetyObligations`, **`safety_of_invariant`**, `InvInit`, `stuckFree_of_obligations`, `eq_pushK_evalFrom` | `Denote/Sem/Invariant.lean` | the reduction, proved abstractly |
| `not_semJudgeImpliesStuckFree`, `semJudge_of_never_value`, `evals_brk_never` | `Denote/Sem/NoProgress.lean` | why layer 4 has to change at all |
| `StateOk` and its whole lemma set (`StateOk_ext`, `StateOk_reCtl`, `StateOk_setLocal`, `MethodsExact.lookup`, …) | `Denote/Sem/State.lean`, `Denote/Sem/Frame.lean` | **unchanged by this work.** 1,633 lines you do not touch |
| the obligation-derivation command and the ladder | `Denote/Sem/Obligations.lean`, `Denote/Ladder.lean` | one edit, §3.2 |
| the whole worked prototype | `Denote/Proto/` | read it first; delete it last (§5) |
| the frame rule and `done_inv` | `../lean/RubyCore/Proof/KontFrame*.lean`, `NotDone.lean` | in the other package, by import |

---

## 5. Delete list

Mandatory, per Norm B. Each row says what replaces it.

| delete | replaced by |
|---|---|
| `Denote/Sem/Decompose.lean`: `run_split`'s 82-line induction | the 41-line derivation from `run_pushK` (`AnswerValue.lean`'s `run_split_A`) — **keep the name `run_split`**, replace the body, then delete `AnswerValue.lean` |
| `Decompose.lean`: `jump_empty_never_value`, `JumpOpaque`, `jumpOpaque_asgnK` | nothing — once no caller needs the value-only split, the side condition has no consumer. If `run_split` survives with consumers, keep `JumpOpaque` and delete only the 27-line support lemma |
| `Decompose.lean`: `EvalsDecompose` (the stated-and-superseded `def`) | `run_pushK` |
| `Denote/Sem/Frame.lean`: `KontFrame`, `KontFrameCatchFree`, `EvalsDecompose` `def`s | proved elsewhere and now consumed elsewhere. **Keep `not_KontFrame`** and its `#guard`s — that is a refutation |
| `Denote/Rules/VasgnStuck.lean`: `JumpStuckFree`, `jumpStuckFree_asgnK`, `stuckFreeRun_pushK`, `stuckFreeRun_pushK_le` | `run_pushK` + `safe_pushK{,_le}`. Delete the whole file once `Judge.vasgn` is restated; its measurements live in `answer-typed-judgments.md` §10.2 |
| `Denote/Rules/WhileStuck.lean` (the timeboxed probe) | its conclusions are in `answer-typed-judgments.md` §2.3 |
| `Denote/Rules/WhileStuck2.lean` | `Denote/Rules/WhileAnswer.lean`. The file proves a theorem modulo two **false** hypotheses; the refutation prose is preserved in §2.3 and in `WhileAnswer.lean`'s header |
| `Denote/Rules/VasgnAnswer.lean` | it is a *control experiment* against a deleted file. Fold its cost table into the commit message and delete |
| `Denote/Sem/AnswerValue.lean` | after `run_split`'s body is replaced (row 1) nothing else is in it |
| `Denote/Adequacy.lean`: `StuckFreeTarget` | a consequence of `AdequacyTarget` under `SemJudgeA` (§3.2). Say so where it was |
| `Denote/Sem/State.lean`: `StuckFree` **or** `SafeKont.lean`'s `SafeA` | keep the machine-level one (`SafeA`, the general statement — Norm A) and define `StuckFree m e := SafeA (evalFrom m e)`. `stuckFree_iff_safeA` then becomes `rfl` and can also go |
| `Denote/Sem/Judge.lean`: `Evals`, and `EvalsAll`/`DenAllAt`/`DenPairsAt` if the answer-typed list judgments do not need them | `runA`. `Evals m e v m'` is `∃ fuel rest m₀, runA fuel (evalFrom m e) = .ans (.val v) m₀ rest ∧ …`; keep it only as an abbreviation if a consumer reads better for it |
| `Denote/Proto/` (both files) | the real layers. **Trigger: delete when layer 6 is green for at least one real `Judge` rule and one real corpus rung**, not before — until then it is the only end-to-end evidence the schema closes |

Do **not** delete: `probes/` (measurements), `found-issues.md` (findings), any `not_*`
refutation, `Denote/Sanity.lean`.

---

## 6. The migration, in commit-sized steps

Steps 1–2 keep the build green and the ladder unmoved. Step 3 is where the ladder is
restated; read that step in full before starting it.

1. **Retire the two decompositions.** Replace `run_split`'s body with the `run_pushK`
   derivation; delete `stuckFreeRun_pushK{,_le}`, `JumpStuckFree`, `jumpStuckFree_asgnK`,
   `jump_empty_never_value`, `AnswerValue.lean`, `WhileStuck.lean`, `WhileStuck2.lean`,
   `VasgnAnswer.lean`. Zero rung churn: `run_split` keeps its name and its 48 consumers.
   Unify `StuckFree`/`SafeA` in the same commit.
2. **`EscOk`, general form.** The two class-table lemmas for `retJ`/`throwJ` (§3.1). If they
   need something `StateOk` does not provide, stop and record it — do not weaken `EscOk` to
   `False` or `True`.
3. **`SemJudgeA`, and the ladder restatement.** One edit to `judgeFamily`, then measure: run
   the ladder and see how many of the 48 discharges survive mechanically (this answers
   `answer-typed-judgments.md` §8's third open question, now cheaply).

   **The ladder number will drop, and reporting it honestly is part of the step.**
   `ratchet/AGENTS.md`'s "a rung once climbed never un-climbs" is a statement about `validate`
   and the *syntactic* ladder; the semantic ladder's obligations are **derived from a
   definition**, so changing the definition restates them. That is a restatement, not a
   regression, and the commit must (a) record the pre-migration number, (b) report the new
   one, (c) list which rungs survived unchanged, which needed one new case, and which need
   real work. Do not migrate `judgeFamily` and the rungs in the same commit — the measurement
   in between is the valuable artifact.
4. **Migrate the rungs**, in the order the surviving-rung measurement suggests: leaves first,
   the `.const` family next, then the declaration family, then the call family. One commit per
   coherent group, each with its `#print axioms`.
5. **`KontOk`.** 36 constructors, in `probes/kont_census.lean`'s order, two clauses each. Write
   the *target* `Prop` for `preserved` first (§2's standing rule) and keep the inductive
   incomplete-but-`sorry`-free while it grows.
6. **`Inv`, `preserved`, `noBadStep`**, then instantiate `safety_of_invariant`.
7. **`Deriv`, `check`, `check_sound`, `validateD`** at real scale, with the derivation command
   for `Deriv` (§3.4). Negative controls from day one — a checker that accepts everything
   satisfies `check_sound` just as well.
8. **Delete `Denote/Proto/`** and land the end-to-end theorem at a real corpus rung.

---

## 7. Named gaps — do not rediscover these

| gap | where it is stated | what it blocks |
|---|---|---|
| **`UncaughtInv`** — `.uncaught` is only ever `unwind`'s empty-continuation arm on a `raiseJ`; the converse of `done_inv`, and it **does not exist** (`RubyCore/Proof/NotDone.lean` has the one and not the other) | `Denote/Proto/Checker.lean` §5 | the general right route (`SemJudgeA → safety`). Belongs in `RubyCore/Proof/`, next to `done_inv` |
| **The protocol-indexed frame rule** — `stepFn_T (tagsOf K ++ T) (pushK K m) = frameR K (stepFn_T T m)`, of which today's `stepFn_frame` is the `T = []` instance. Needs an ambient-tag parameter on `stepFn`: an **interface** change, behaviour-preserving (top level passes `[]`), difftest-checkable for exactly that reason, threading through the send spine | `Denote/Sem/AnswerCatch.lean` §`CatchFree` is the degenerate case of a protocol | `KontOk` at a machine inside a `catch`. **[✗→]** relocating the tag set into a `Machine` field does *not* substitute: the non-locality is semantic, not representational |
| **`catchK` is reached by no corpus rung** [V] | `probes/kont_census.lean`; `answer-typed-judgments.md` §10 / `found-issues.md` §F27 | the tag index would be built untested. **Add a `catch`/`throw` corpus rung before writing the constructor** |
| **6 of the 36 frames correspond to no `Judge` premise** — `frameK`, `blkFrameK`, `iterK`, `newK`, `methodAddedK`, `blkCoerceK`, all pushed from the dispatch/send spine, none mentioned anywhere in `Ratchet/Judge.lean` | `found-issues.md` §F27 | these are the **call boundary**: a `frameK` means you are inside a callee whose typing is a *different* derivation, so `KontOk` needs a **stack** of descriptions, not a position in one. `Judge.callDef`'s `Asm` machinery is what makes that stack finite |
| **`Judge.while'`'s condition rejects every compound `&&`/`||`** because the desugarer's `__dt_t1` temp is a new local in `Γc` — pure over-strictness, no soundness content | `found-issues.md` §F26 | not this work, but it will be in your way constantly while testing. Two candidate fixes recorded there |

---

## 8. Acceptance criteria

Run these; do not assert them.

1. `lake build` green in `ratchet/` **and** `../lean/`; **no `sorry`** anywhere
   (`grep -rn sorry` over the changed files).
2. Every top-level theorem has a `#print axioms` line showing only
   `propext`/`Classical.choice`/`Quot.sound`.
3. The corpus agreement gate (`scripts/run_agreement.sh`, which `run_ratchet.sh` runs first)
   and difftest tier 0 under `--sut lean`: **0 disagreements**, and the agree count
   **byte-stable** against the pre-migration number. This work changes no
   interpreter behaviour except possibly step 7 of §7's protocol index — if the number moves,
   that is a red flag, not progress (`certificate-language.md` §7 norm 4).
4. `scripts/run_ratchet.sh`: the syntactic ladder **unmoved** — `178/259` certified, `35`
   expect_validate mismatches. It is a statement about `validate`, which this work does not
   touch, so any movement here is a bug you introduced.
5. `lake exe semladder`: the restated number, with the pre-migration number (**48 of 83**)
   recorded in the commit message (§6 step 3).
6. `lake exe checkrungs`: **177/177** hand derivations + **148/148** negative controls,
   unmoved.
7. Every `Prop` this work names is either proved or listed in §7. `grep` for `def.*: Prop` in
   the changed files and account for each.
8. Every row of §5's delete list is gone.
9. One theorem of the shape `validateD p cert = true → StateOk … m → StuckFree m p`, at a
   **real corpus rung**, with every hypothesis discharged and a `#guard` on the `Bool`.
10. Negative controls exist for `check`: at minimum a certificate/syntax mismatch, an
    ill-typed program, and a certificate tree of the wrong depth, each `#guard`ed false.

---

## 9. Four temptations, each already measured

1. **"Fix `catch` so continuations decompose unconditionally."** Making `throw` unwind like
   `raise` **breaks CRuby fidelity** [V]: `begin; throw :t; rescue UncaughtThrowError; "x"; end`
   really does return `"x"`, and the same block under `catch(:t)` really does escape. `throw`
   is *defined* by a question about its context. The repair is the protocol index (§7), not a
   semantics change.
2. **"Use `SafeKont` as the invariant."** `safe_pushK` requires `CatchFree m.kont` and a
   reachable machine can carry a `catchK`, so the answer-typed decomposition is a **per-rule**
   tool. The whole-machine invariant must describe the continuation syntactically. This is why
   `KontOk` cannot be avoided.
3. **"Fix `Γ` (or `κ`, or `m`) to keep the statement short."** Norm A. This exact mistake was
   made and caught; generalising cost nothing and the restriction had already made an adequacy
   theorem useless.
4. **"Keep the old theorem alongside the new one, just in case."** Norm B. §5 is the list.

And one that is not a temptation but a standing risk: **`SemJudge`'s vacuity is a property of
the *shape*, not of any one rule.** `not_semJudgeImpliesStuckFree` is on file so that a future
restatement cannot quietly reintroduce a value-only hypothesis. If you find yourself writing an
obligation whose only hypothesis is that the run produced a value, you have undone this work.
