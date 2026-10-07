#!/usr/bin/env bash
# The control-drift tripwire.
#
# `Books/TypeSoundness/Controls/All.lean` is the one place every negative control is named, so
# "the gate checks every control" can be true. It is not, today: the *active*
# typed-ratchet gate builds a curated list of named controls, not `All`, and the
# whole-library `lake build` that does reach `All` is report-only in CI while the
# semantic rebuild is in progress (issue #25). A control that fails — a wrong
# `#guard`, a broken proof — is therefore invisible to a green `make gate` and
# only surfaces in a report-only job that nobody reads.
#
# This script closes that gap without blocking the climbing work: it builds
# `Books.TypeSoundness.Controls.All` and, on failure, prints *which* control modules failed and
# *why* (the first error line for each). CI runs it report-only; the intent is
# that it becomes blocking once the semantic rebuild completes and every control
# builds again.
#
#   scripts/check_controls.sh            # build All, list failing control modules
#   scripts/check_controls.sh --verbose  # also echo the raw lake build output
#
# Exit 0 iff every control under `Books.TypeSoundness.Controls.All` builds.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.." || exit 1

verbose=0
case "${1:-}" in
  --verbose|-v) verbose=1 ;;
  --help|-h)
    echo "Usage: scripts/check_controls.sh [--verbose]"
    exit 0 ;;
  "") ;;
  *) echo "Unknown argument: $1" >&2; exit 2 ;;
esac

log="$(mktemp)"
trap 'rm -f "$log"' EXIT

# `All` is the aggregate the docstring names. `--no-build` would only typecheck
# cached oleans, so build it: a control that was never built has no olean, and
# that absence is exactly the drift we are catching.
if lake build Books.TypeSoundness.Controls.All >"$log" 2>&1; then
  echo "CONTROL DRIFT: none — Books.TypeSoundness.Controls.All builds."
  [[ "$verbose" == 1 ]] && cat "$log"
  exit 0
fi

# On failure, `lake` prints each failing module as a `✖ [n/N] Building <Module>`
# line and follows it with the `error:` lines. Collect the failing control
# modules and the first error line that belongs to each.
# (A `while read` loop, not `mapfile`: macOS ships bash 3.2.)
failing=()
while IFS= read -r m; do failing+=("$m"); done < <(
  grep -oE '(Building|Running) Books\.TypeSoundness\.Controls\.[A-Za-z0-9_]+' "$log" |
    sed -E 's/^(Building|Running) //' | sort -u
)

echo "CONTROL DRIFT: Books.TypeSoundness.Controls.All does not build."
if [[ ${#failing[@]} -eq 0 ]]; then
  echo "  (no failing control module matched; the failure is upstream of the controls)"
  echo "  first error lines:"
  grep -E '^error' "$log" | head -10 | sed 's/^/    /'
else
  echo "  ${#failing[@]} failing control module(s):"
  for m in "${failing[@]}"; do
    # The first error line naming this module, if any; otherwise just the name.
    line="$(grep -E "^error: .*${m//.//}\.lean" "$log" | head -1)"
    if [[ -n "$line" ]]; then
      printf '    %-55s %s\n' "$m" "${line#*lean:}"
    else
      printf '    %s\n' "$m"
    fi
  done
fi

# A per-file summary is what a reader acts on; the raw trace is for debugging.
if [[ "$verbose" == 1 ]]; then
  echo "--- raw lake build output ---"
  cat "$log"
fi

exit 1
