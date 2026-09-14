#!/usr/bin/env bash
# The **typed** ratchet: Sorbet in the loop, end to end.
#
#   corpus/NNN.rb  (annotated, the source of truth)
#     1. srb -p symbol-table   -> the signature manifest        ] untrusted
#     2. the strip stack       -> the plain program             ] untrusted
#     3. export-json           -> the AST                       ] untrusted
#     4. emit_deriv.py         -> a `Deriv`, or a named block   ] untrusted
#     5. lake exe ratchetd     -> `validateD`'s Bool            ] TRUSTED, and only this
#
# ## GREEN and RED
#
# The last line is the verdict, and it means one thing:
#
#   **GREEN** -- nothing is started and incomplete. Every rung with a proof has a correct one,
#   every certified rule is exercised end to end or exempt within its recorded ceiling, every
#   floor holds, the model agrees with CRuby, and reach has not dropped. What remains is
#   *ascent*: rungs nobody has started, blocked on rules nobody has proved. That is the
#   ordinary state of an unfinished ladder and it is not a failure.
#
#   **RED** -- something is started and incomplete. Chiefly: **a rung `validateD` accepts
#   that has no end-to-end safety proof.** Accepting it means a certificate for it exists and
#   checks, so the rung is on the ladder from that moment; without a safety proof the ladder
#   is claiming a rung the safety determination does not reach. Also: a theorem about a
#   different program than its rung's; an exemption list wider than its ceiling; a floor that
#   moved; a rule registered without its floor raised; a stage that errored.
#
# **A rung is climbed when it is typed AND proved `StuckFree`** -- not when the checker alone
# is satisfied. That is why there are two reach numbers and only one of them is the ladder:
# `ratchetd`'s LADDER REACH counts the leading run the *checker* accepts, `semladder`'s SAFETY
# REACH counts the leading run that is also proved. Every rung between them is half-climbed.
#
# The distinction is deliberate: "251 rungs unproved" is GREEN, because none of them has been
# begun -- the checker rejects them, or they need rules nobody has proved and no certificate
# claims them. One rung begun and left is RED, because a half-climbed rung is the thing a
# ratchet exists to catch.
#
# ## Two modes, and what the quiet one is for
#
# By default this prints **the goal list and nothing else**: the unmet rungs in corpus order,
# truncated at 20, with the tally of what blocks them. That is the output of a commit-time
# gate -- the answer to "am I green, and what is next", which is the question anyone running
# this actually has. Everything each stage says on the way is captured to a log and dropped.
#
# `--verbose` streams all of it: the Lean build, the corpus pipeline, the agreement replay,
# the reach table, the registry columns and the per-rung cross-check.
#
# **Quiet never hides a failure.** Every stage's exit code is checked; the first one that
# fails prints what it was, why it matters, and the tail of its captured output, then stops.
# The flag chooses how much is said when everything is fine, never when it is not.
#
# ## The stages, in the order that matters
#
#   0. **The negative controls** (`Ratchet/DerivControls.lean`, `Denote/Typed/Controls.lean`,
#      `#guard`ed at build time): a checker that accepts everything would pass every rung
#      below, so the controls are checked before any count is reported.
#   1. **Stages 1-4** over every rung, into `build/`.
#   2. **Agreement** (`--sut lean`) over the *stripped* programs -- the ones the certificates
#      are about. A rung the model runs differently from CRuby is a rung whose type is a
#      statement about a fiction. Skip with RATCHET_SKIP_AGREEMENT=1.
#   3. **The report** (`lake exe ratchetd`), whose exit code is non-zero on a moved Sorbet
#      verdict, a new upstream failure, or a drop in ladder reach.
#   4. **The safety proof, cross-checked against the corpus** (`lake exe semladder`). The
#      end-to-end theorems in `Denote/Typed/Safety.lean` name their rung in a docstring; this
#      reads the rung the pipeline actually built and compares its sig-stripped program
#      against the `Expr` each theorem is about, so "rung 004 is proved safe" cannot be true
#      of a theorem and false of the ladder. It also reports which registered rules those
#      rungs **exercise** -- read off the proof terms, not guessed from the programs
#      (`Denote/Typed/RuleAudit.lean`) -- and names the ones they do not (today: `var` and
#      `vasgn`, structurally; see `found-issues.md` §F30).
#
#      Four ways it goes non-zero, beyond a moved floor:
#        * a safety theorem is about a different program than its rung's;
#        * a built rung uses **only registered rules** and has no safety theorem -- the
#          registry can already justify it and nothing has (`SAFETY COVERAGE REGRESSED`);
#        * the `unexercised` exemption list grew past its ceiling (`COVERAGE HATCH WIDENED`);
#        * a rung count or the registry size fell below its floor.
#
# `validateD` types (`Ratchet/Check.lean`); a `true` means a `DJudge` derivation exists.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
RATCHET_DIR="$PWD"

VERBOSE=0
PASSTHROUGH=()
for arg in "$@"; do
  case "$arg" in
    --verbose|-v) VERBOSE=1 ;;
    --help|-h)
      sed -n '2,71p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
      exit 0 ;;
    *) PASSTHROUGH+=("$arg") ;;
  esac
done

LOGDIR="$(mktemp -d)"
CURRENT_STAGE=""
cleanup() { rm -rf "$LOGDIR"; }
trap cleanup EXIT

# fail <label> <why> [logfile]
fail() {
  local label="$1" why="$2" log="${3:-}"
  {
    echo
    echo "RATCHET RED -- ${label}"
    echo
    echo "  ${why}"
    if [[ -n "$log" && -s "$log" ]]; then
      echo
      # Prefer the error lines themselves. A lake log is mostly `#print axioms` info and
      # deprecation warnings, so a blind tail buries the one thing worth reading.
      if grep -qE '^error' "$log"; then
        echo "  --- the errors ---"
        grep -E '^error' -A 6 "$log" \
          | grep -vE '^(trace|info|warning|--|Note:)' | head -30 | sed 's/^/  | /'
      else
        echo "  --- last 40 lines of that stage ---"
        tail -40 "$log" | sed 's/^/  | /'
      fi
      echo
      echo "  (re-run with --verbose for the whole thing)"
    fi
  } >&2
  exit 1
}

# stage <label> <why-it-matters> -- <command...>
stage() {
  local label="$1" why="$2"; shift 3   # drop label, why, and the literal `--`
  CURRENT_STAGE="$label"
  if [[ "$VERBOSE" == 1 ]]; then
    echo "=== ${label} ==="
    "$@" || fail "$label" "$why"
    echo
  else
    local log="${LOGDIR}/$(echo "$label" | tr -c 'a-zA-Z0-9' '_').log"
    "$@" >"$log" 2>&1 || fail "$label" "$why" "$log"
    LAST_LOG="$log"
  fi
}

stage "build: the negative controls and the proofs" \
  "A Lean source does not compile, or a #guard/#guard_msgs control failed. These are the gates
  that cannot be skipped -- the coverage cross-check (Denote/Typed/RuleAudit.lean), the
  registration refusals (Denote/Typed/Controls.lean), and the safety theorems themselves." \
  -- lake build Ratchet.DerivControls Denote.Typed.Safety Denote.Typed.RuleAudit \
                ratchetd semladder

stage "stages 1-4: sorbet -> strip -> desugar -> emit" \
  "The untrusted pipeline errored building build/*.rung.json. Usually srb is missing or a
  strip transform hit a construct it cannot handle; a rung that merely falls outside the
  fragment is recorded as blocked, not as a failure, so this is a real error." \
  -- python3 scripts/build_corpus.py ${PASSTHROUGH[@]+"${PASSTHROUGH[@]}"}
CORPUS_LOG="${LAST_LOG:-}"

if [[ "${RATCHET_SKIP_AGREEMENT:-0}" == "1" ]]; then
  [[ "$VERBOSE" == 1 ]] && echo "=== agreement: SKIPPED (RATCHET_SKIP_AGREEMENT=1) ===" && echo
  AGREE_LINE="agreement SKIPPED"
else
  stage "agreement: CRuby vs the Lean semantics" \
    "The Lean model and CRuby disagree on a sig-stripped program, or the replay harness
  errored. A rung the model runs differently from CRuby is a rung whose certificate is a
  statement about a fiction, so this gates the safety claim rather than decorating it." \
    -- bash -c 'cd "$1"/../difftest && uv run python -m difftest replay "$1/build" --sut lean' _ "$RATCHET_DIR"
  if [[ "$VERBOSE" == 1 ]]; then
    AGREE_LINE=""
  else
    AGREE_LINE="$(grep -o '"agree": *[0-9]*' "$LAST_LOG" | head -1 | tr -d ' ' | tr ':' ' ' \
                  | awk '{print $2" agree"}')"
    DIS="$(grep -c '"disagreements": \[\]' "$LAST_LOG" || true)"
    [[ "$DIS" == "0" ]] && AGREE_LINE="${AGREE_LINE}, DISAGREEMENTS" || AGREE_LINE="${AGREE_LINE}, 0 disagree"
  fi
fi

stage "stage 5: the typed ladder (reach)" \
  "Ladder reach dropped below its recorded floor, a Sorbet verdict moved, or a new upstream
  failure appeared. All three are ratchets: a rung once climbed never un-climbs." \
  -- ./.lake/build/bin/ratchetd build

SAFETY_WHY="See the RATCHET RED line printed above, which names which gate fired: a safety
  theorem about the wrong program, a rung started and left incomplete, the exemption list
  widened past its ceiling, or a recorded floor moved."

SL_LOG="${LOGDIR}/semladder.log"
if [[ "$VERBOSE" == 1 ]]; then
  echo "=== the safety proof, cross-checked against the corpus -- and the unmet goals ==="
  SL_ARGS=(build)
else
  # Quiet: one line of pipeline facts, then the goal list, which is the whole point.
  REACH="$(grep -m1 '^LADDER REACH:' "$LAST_LOG" 2>/dev/null | sed 's/^LADDER REACH: //; s/ (.*//')"
  echo "pipeline: reach ${REACH:-?}${AGREE_LINE:+ · }${AGREE_LINE:-}"
  SL_ARGS=(build --quiet)
fi
set +e
./.lake/build/bin/semladder "${SL_ARGS[@]}" 2>&1 | tee "$SL_LOG"
SL_RC=${PIPESTATUS[0]}
set -e
if [[ "$SL_RC" -ne 0 ]]; then
  # semladder names its own gate, so a second banner would only repeat it. One is added
  # only if it failed *without* saying so -- a crash rather than a finding.
  grep -q '^RATCHET RED' "$SL_LOG" || fail "the safety proof and its gates" "$SAFETY_WHY"
  exit 1
fi

# Every stage passed, and this is the only layer that knows that -- the build, the corpus
# pipeline, agreement, reach and the safety gates are five separate exit codes and they are
# all zero. So this is where the verdict belongs.
echo
echo "RATCHET GREEN -- nothing is started and incomplete. Every rung with a proof has a"
echo "  correct one, every certified rule is exercised or exempt within its ceiling, and"
echo "  every recorded floor holds. The only work left is to keep ascending: the first rung"
echo "  in the list above is next, and the tally says which rule unblocks the most of them."
