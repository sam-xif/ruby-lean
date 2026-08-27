#!/bin/bash
# Build the metatheory and re-verify axiom cleanliness — `PLAN.md` §4 norm 5,
# "build the `Proof/` files at batch boundaries; a green ratchet does not mean the
# proofs still work".
#
# That norm existed and was not followed, and the cost was three independent
# breaks sitting undetected for 24 commits (L119):
#
#   * L101 put `matchGlobal` in front of the gvar read, so `Step.varGvar`'s
#     "a gvar read is `getGlobal`" stopped being true → `Step.sound` failed, and
#     with it every file that imports it (14 of 15);
#   * L103 retired the global `reprPure` flag, so `StaticSoundness` was still
#     case-splitting on a `reprSensitive` constant that no longer existed;
#   * the boot heap grew from 37 to 40 objects, so `T5Loop`'s hard-coded `clsA`
#     id pointed at an existing boot object.
#
# None of them is deep. All three were invisible because `Proof/` is off the
# default build target — which is the right call for build times and the wrong
# call for drift, so this script is the compromise: one command, run it at batch
# boundaries.
#
#   scripts/check-proofs.sh
#
# Exit 0 iff every proof file builds and every headline theorem depends on
# nothing beyond Lean's own three axioms.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 1

echo "== building RubyCore/Proof/ (lake build Metatheory)"
if ! lake build Metatheory 2>&1 | tail -3; then
  echo "FAIL: the metatheory does not build"
  exit 1
fi
if lake build Metatheory 2>&1 | grep -qE "^error:"; then
  echo "FAIL: the metatheory does not build"
  exit 1
fi

# `#print axioms` on the results that are claimed elsewhere (AGENTS.md, PLAN.md
# §9). "Axiom-clean" here means *exactly* Lean's three — `sorryAx` or any
# project-local axiom is a failure.
AX=$(mktemp /tmp/rubycore-axioms-XXXXXX.lean)
trap 'rm -f "$AX"' EXIT
cat > "$AX" <<'LEAN'
import RubyCore.Proof.StaticSoundness
import RubyCore.Proof.PreludeInv
import RubyCore.Proof.Adequacy
import RubyCore.Proof.T5
import RubyCore.Proof.T5Loop
import RubyCore.Proof.SorbetConcrete
import RubyCore.Proof.AncestorsGrow
import RubyCore.Proof.Static.Mono
import RubyCore.Proof.Static.Assn
import RubyCore.Proof.Static.OpenSelf
import RubyCore.Proof.Static.Iter
import RubyCore.Proof.Static.Discharge
import RubyCore.Proof.Cert.Sound
import RubyCore.Proof.Cert.Ledger
import RubyCore.Proof.Judgment.Cert
import RubyCore.Proof.Judgment.Sem
#print axioms RubyCore.Proof.invariant_sound
#print axioms RubyCore.Proof.invariant_result_sound
#print axioms RubyCore.Proof.invariant_sound_from
#print axioms RubyCore.Proof.Static.check_sound
#print axioms RubyCore.Proof.Static.check_sound_withPrelude
#print axioms RubyCore.Proof.Static.check_sound_withPrelude'
-- D12 — the *reported* verdict's soundness. `decisionOf`'s `accept` is the same
-- predicate `check_sound` is stated over (`decision_accept_iff`), which is the
-- one-line reason making the verdict total moved no theorem.
#print axioms RubyCore.Proof.Static.decision_sound_withPrelude
#print axioms RubyCore.Proof.Step.sound
#print axioms RubyCore.Proof.Step.complete
#print axioms RubyCore.Proof.Step.deterministic
#print axioms RubyCore.Proof.Step.adequacy
#print axioms RubyCore.Proof.T5Loop.t5_loop_type_safe
#print axioms RubyCore.Proof.ancestors_congr_grow
#print axioms RubyCore.Proof.saturatedB_sound
#print axioms RubyCore.Proof.Static.DeclsOk_grow
#print axioms RubyCore.Proof.Static.inv_grow_value
#print axioms RubyCore.Proof.Static.infer_mono
#print axioms RubyCore.Proof.Judgment.judge_sound
#print axioms RubyCore.Proof.Judgment.judge_sound_cert
#print axioms RubyCore.Proof.Judgment.step_okJ
#print axioms RubyCore.Proof.Judgment.judge_mono
#print axioms RubyCore.Proof.Judgment.egEven_judge_safe
#print axioms RubyCore.Proof.Judgment.egUserCall_judge_safe
-- J30 — the semantic judgment: `judge_semJudge` is the fundamental lemma
-- (adequacy of the syntactic `Judge` for the reachability-defined `SemJudge`),
-- `semJudge_sound` composes type safety through it, and `judge_result_vty` is
-- the J29 answer-type payoff (terminating values inhabit the judged type).
#print axioms RubyCore.Proof.Judgment.judge_semJudge
#print axioms RubyCore.Proof.Judgment.semJudge_sound
#print axioms RubyCore.Proof.Judgment.judge_sound_via_sem
#print axioms RubyCore.Proof.Judgment.judge_result_vty
#print axioms RubyCore.Proof.Judgment.egIf_result_int
-- The assertion language (L165). `denote_declAssn` is the faithfulness theorem —
-- `⟦declAssn D⟧ h ↔ DeclsOk D h`, both directions — and it is what closes
-- `assertion-language.md` §9.3's honest weak point for the declaration fragment:
-- the syntax-to-semantics map is *checked*, not merely defined. `assn_sound_from`
-- is the invariant restated over it, inheriting every consecution case.
#print axioms RubyCore.Proof.Static.denote_declAssn
#print axioms RubyCore.Proof.Static.entail_sound
-- Wall 1's machine step (L244). The five reductions a block send passes through,
-- audited here because nothing else imports them yet — an off-target file with no
-- consumer is exactly how `Proof/` rotted for 24 commits (L119).
#print axioms RubyCore.Proof.Static.finishSend_lit
#print axioms RubyCore.Proof.Static.invoke_iter_each
#print axioms RubyCore.Proof.Static.startIter_eq
#print axioms RubyCore.Proof.Static.iterStep_cons
#print axioms RubyCore.Proof.Static.callClosure_req1
-- L261: the lambda literal's step, the same allocation with no dispatch after it.
#print axioms RubyCore.Proof.Static.startArgs_lambda
#print axioms RubyCore.Proof.Static.assn_sound_from
#print axioms RubyCore.Proof.Static.assn_check_sound
-- R4 (open self). `inferOpen_mono` is §7.5's owed monotonicity lemma;
-- `inferOpen_factors` is the factoring theorem — open-self typing reduces to
-- nominal typing — and `userConforms_of_inferBody` lands it in the invariant's
-- own currency.
#print axioms RubyCore.Proof.Static.inferOpen_mono
#print axioms RubyCore.Proof.Static.inferOpen_factors
#print axioms RubyCore.Proof.Static.userConforms_of_inferBody
-- L168 — the parameter-open form. Same theorem, instantiated at a non-empty `Γ`:
-- `inferOpen_factors` was quantified over the environment from the start, so §7.3's
-- `Γ_b` costs the metatheory nothing. `egParam_nominal` is the end-to-end witness —
-- open run, solver's `θ`, `satStoreB` check, nominal `infer` accept — kept in the
-- audit because it is the only place the four layers are exercised together over a
-- body with a parameter.
#print axioms RubyCore.Proof.Static.inferBodyWith_sound
#print axioms RubyCore.Proof.Static.egParam_nominal
-- L170 — the written receiverless call, `foo()`. `inv_implicit_send0` is L164's
-- `vcall` consecution case quantified over the `SendSite`, and it is the whole
-- proof obligation the rule adds: the two constructs differ by one `SendSite`
-- constructor and `visError?` is `none` for every site but `.explicit`.
#print axioms RubyCore.Proof.Static.inv_implicit_send0
#print axioms RubyCore.Proof.Static.egImplicitCall_safe
-- L172 — a literal `self` receiver. `KontOk.recvK`/`recvK0` take the site as a
-- parameter, `infer`'s `isSelf` guard is gone, and `site_explicit` was withdrawn
-- with it. The witness is in the audit because the corpus cannot show that the
-- `.selfRecv` path dispatches like the `.explicit` one.
#print axioms RubyCore.Proof.Static.egSelfRecv_safe
-- L174 — the array literal, the second producer of a class-typed value. Same
-- `Heap.alloc` of a non-class object as L151's string literal, at `Boot.arrayId`;
-- `LitClsOk` (which is what `StrClsOk` became when it stopped being about one
-- literal) carries the name/id join for both.
#print axioms RubyCore.Proof.Static.egArray_safe
-- L262 — the whole-program pass's one theorem. `discharge` *drops* requirements, so its
-- whole soundness content is that a dropped one was met: a `θ` satisfying the cancelled
-- store, at a program whose own provisions hold, satisfies the store `inferOpen` built.
-- Audited here because `Proof/Static/Discharge.lean` has no other consumer yet, and an
-- off-target file with no consumer is exactly how `Proof/` rotted for 24 commits (L119).
#print axioms RubyCore.Proof.Static.discharge_sound
-- L266/L267 — the two facts the certificate language needed from the standing
-- machinery: a row added at a *fixed* heap, and `initiation` parametric in the table.
-- Audited because `DeclsOk_addRow_here`'s only consumer is off in `Proof/Cert/`, and
-- `initiation_at` is what `check_sound` now factors through.
#print axioms RubyCore.Proof.Static.DeclsOk_addRow_here
#print axioms RubyCore.Proof.Static.DeclsOk_of_subDecls
#print axioms RubyCore.Proof.Static.initiation_at
-- C1 (`docs/semantics/certificate-language.md`) — the composed program-level
-- soundness theorem: *this certificate, this program, therefore no reachable
-- `typeStuck`, conditional only on the printed residue.* The three worked corollaries
-- are the milestone's gate and they are one per rung of the verdict ladder:
-- unconditional with no extension, unconditional with the residue *discharged*, and
-- conditional on a residue that cannot be.
-- The certificate theorems. **Six names were removed here, deliberately**, and the
-- audit is where that has to be legible rather than a file quietly getting shorter
-- (`certificate-language.md` §10.5):
--
--   validate_sound, validate_sound_carries      -> validate_sound_of_ctl,
--                                                  validate_sound_assumes
--   check_accept_of_validate_empty              -> gone: it was `validate` at the empty
--                                                  certificate equals `check p = accept`,
--                                                  and `validate` no longer calls `infer`
--   egVcall_certified, egEven_certified,
--   egDiv_certified                             -> await C-1; their *validation* facts
--                                                  and egEven's discharged residue are
--                                                  audited below in their place
--
-- `validate_sound_of_ctl` carries C-1's one open premise (`CtlOk` at `Machine.init p`).
-- When C-1 lands, the three `_certified` corollaries come back and these lines with
-- them.
#print axioms RubyCore.Proof.Cert.validate_sound_of_ctl
#print axioms RubyCore.Proof.Cert.validate_sound_assumes
#print axioms RubyCore.Proof.Cert.validate_sound_unconditional
#print axioms RubyCore.Proof.Cert.declsOk_of_validate
#print axioms RubyCore.Proof.Cert.egVcall_validates
#print axioms RubyCore.Proof.Cert.egEven_validates
#print axioms RubyCore.Proof.Cert.egEven_residue_discharged
#print axioms RubyCore.Proof.Cert.egDiv_validates
#print axioms RubyCore.Proof.Cert.chkBlockClaim_table_ret
-- C2 — the ledger. `satProvs_ledgerStore` is `discharge_sound`'s open premise (L262:
-- "the second premise is real and is not discharged here") closed by the certificate
-- *stating* the requirement/provision pairing `discharge` had to search for.
-- `egLedger_satStore` is the first place both of `discharge_sound`'s premises are met.
#print axioms RubyCore.Proof.Cert.satProvs_ledgerStore
#print axioms RubyCore.Proof.Cert.ledger_satStore
#print axioms RubyCore.Proof.Cert.validateFull_sound
#print axioms RubyCore.Proof.Cert.egLedger_satStore
LEAN

echo "== axioms"
OUT=$(lake env lean "$AX" 2>&1)
echo "$OUT"
if echo "$OUT" | grep -qE "sorryAx|error"; then
  echo "FAIL: a theorem is missing, or depends on sorry / an unexpected axiom"
  exit 1
fi
# F0's certificate (`homebrew/widening-the-fragment.md` §3). `check_sound_withPrelude`
# assumes `heapOkB` of the prelude-booted heap, and that Bool cannot be decided in
# the kernel (`Lean.Json.parse` does not reduce; L94 bans `native_decide`), so it is
# decided by running it. The probe computes the *same* function the lemma names —
# `RubyCore/HeapCert.lean`, outside `Proof/` precisely so there is one copy.
echo "== F0 certificate (heapOkB at the prelude-booted heap)"
if ! lake env lean --run scripts/heapok_probe.lean; then
  echo "FAIL: the prelude-booted heap does not satisfy the heap half of Inv"
  exit 1
fi

# L144's certificate, and it is here for the same reason F0's is: `ancestors_congr_grow`
# — the ancestor congruence across an *allocating* step — assumes `Saturated`, i.e. the
# ancestor walk has finished before its fuel runs out. `saturatedB` decides it, the
# probe runs it at the prelude-booted heap, and if a prelude change ever makes a walk
# fuel-sensitive the hypothesis silently stops being satisfiable. The probe also
# reports the clause `HANDOFF.md` proposed instead (the chain descending in `ObjId`),
# which is **false** at the booted heap — 10 edges — and is kept visible on purpose.
echo "== L144 certificate (saturatedB at the prelude-booted heap)"
if ! lake env lean --run scripts/ancestors_probe.lean; then
  echo "FAIL: the ancestor walk is not saturated at the booted heap, or an edge points out of bounds"
  exit 1
fi

# F1b.9's measurement, kept as a check rather than a one-off. A declaration row is
# keyed on a class *name*, so `DeclsOk`'s obligation quantifies over every class
# object with that name while a `def` installs on exactly one — `ClassOk`'s
# uniqueness clause is what closes the gap, and this reports the general fact it
# restricts. If a prelude change ever makes two class objects share a name, the row
# stops being witnessable and this says so before a proof does.
echo "== F1b.9 measurement (no two class objects share a name)"
if ! lake env lean --run scripts/names_probe.lean; then
  echo "FAIL: two class objects share a name at the booted heap"
  exit 1
fi

# L176's measurement for the constant-table rung. It is a *pre*-condition report,
# not a theorem's certificate: the clause a name-keyed constant table needs is
# "nothing strictly in front of Object on the definee's chain owns this name", and
# this decides it over the two classes that population actually contains. It also
# reports the five names Object and `T` both own, which is why the clause is stated
# over the *reach* and not over every class object — get that wrong and the clause
# is unprovable rather than merely strong.
echo "== L176 measurement (a name-keyed constant table is not shadowed)"
if ! lake env lean --run scripts/consts_probe.lean; then
  echo "FAIL: a class in front of Object on an admitted chain owns a constant, or Object is unreachable"
  exit 1
fi

# L180's measurement for the class-object arm — the rung L179 showed gates all 28
# `const` bodies. Mostly a report (the eigenclass split is heterogeneous and there
# is no clause to ratchet yet), but the *one* fact today's design rests on is a
# ratchet: `valueTy?` types a `.ref` only when `plainRecv`, and `entry_dispatch`
# discharges `invoke`'s three receiver-shape special cases from exactly that. A
# class object that became `plainRecv` would falsify the dispatch lemma silently.
echo "== L180 measurement (no class object is plainRecv)"
if ! lake env lean --run scripts/classobj_probe.lean; then
  echo "FAIL: a class object is plainRecv — entry_dispatch's receiver split is unsound"
  exit 1
fi

# L186's measurement for rung 3: is a `Module#===` row on the class-object arm
# *witnessable*? Both of `DeclsOk`'s obligations are heap facts about the class
# object's dispatch chain, and the hazard is real — `prelude/prelude.rb:44` defines
# `Object#===` in Ruby (so `fromPrelude = true`, which `ResolvesAt` refuses) and
# `Object` is on every class object's chain. The row survives only because `Module`
# comes first, which is an ordering fact about `ancestors` and not something the
# type language can promise. Ratcheted, because a prelude change could reorder it.
echo "== L186 measurement (a Module#=== row on the class-object arm is witnessable)"
if ! lake env lean --run scripts/classeq_probe.lean; then
  echo "FAIL: `===` on a class object no longer resolves to the Module#=== builtin"
  exit 1
fi

# L189's admissibility table for `reopenableClasses`. Not a ratchet on a clause but
# on a *table*: it decides `ClassOk`'s seven per-name conjuncts for every plausible
# candidate, so widening the table is a `decide` rather than an argument — and every
# refusal is informative (`Float` owns NAN/INFINITY; `Array`/`Hash`/`Range` lose sole
# ownership to `T::Array`/`T::Hash`/`T::Range`; `Regexp` is a singleton-dispatch id;
# `Comparable`/`Kernel`/`T` are modules).
echo "== L189 measurement (which class names are admissible)"
lake env lean --run scripts/reopen_probe.lean

echo "OK: metatheory builds; every theorem above rests on propext + Classical.choice + Quot.sound only; heapOkB and saturatedB hold at the booted heap; class names are unique"
