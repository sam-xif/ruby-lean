#!/usr/bin/env bash
# The semantic denotation's gate. `Denote/Examples.lean` is a file of `#guard`s, each of
# which runs a real program under the real `stepFn` from the real prelude-booted heap and
# asks `denB`/`closB`/`arrowCheck` about the value it produced -- so elaborating the library
# *is* the check, and `lake build` exits nonzero if the denotation and the semantics ever
# disagree. The `#print axioms` lines in each proof file print their bill on the way past.
#
# Separate from `run_ratchet.sh`/`run_check_rungs.sh` for the same reason `checkrungs` is a
# separate exe: the ratchet's headline number stays a pure statement about `validate`, and
# `Denote/` moves no rungs. See `AGENTS.md` §Semantic denotation status.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

lake build Denote
echo
echo "Denotation vs. the real semantics (from Denote/Examples.lean):"
lake env lean --run <(cat <<'LEAN'
import Denote.Examples
def main : IO Unit := IO.println Ratchet.Denote.Examples.report
LEAN
) 2>/dev/null || \
  printf '%s\n' "  (report unavailable; the #guards above are the gate)"
