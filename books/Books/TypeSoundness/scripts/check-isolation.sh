#!/usr/bin/env bash
# The layering check.
#
#   scripts/check-isolation.sh
#
# The type checker (`Books/TypeSoundness/Checker/`) is isolated from the model
# (`RubyCore`): its `Expr` and `Ty` are copied text, not imports, so the checker
# can be read, audited and re-implemented without the model in scope. The rest
# of the book is where the two meet, because the soundness proof relates them.
#
# The checker sits in the same Lake library as that proof, so the compiler does
# not refuse the import. This script does, and `scripts/check-soundness.sh` runs
# it as its first stage.
#
# Exit 0 iff every import under `Books/TypeSoundness/Checker/` is of another
# checker module, of the vendored `Json` library or of Lean, the executable
# (`Checker/Main.lean`) does not reach `import Lean`, and the model's package
# imports nothing from this one.
set -uo pipefail
cd "$(dirname "$0")/../../.." || exit 1   # books/

rc=0

# 1. The checker sees only itself and Json. Anything else (the model, or a proof
#    module, which would bring the model with it) is refused.
BAD=$(grep -rnE '^import +' Books/TypeSoundness/Checker/ --include='*.lean' \
      | grep -vE ':import +(Books\.TypeSoundness\.Checker\.[A-Za-z0-9_.]+|Json(\.[A-Za-z0-9_.]+)?|Lean)\s*$')
if [[ -n "$BAD" ]]; then
  echo "FAIL: the checker imports something outside itself:"
  while IFS= read -r line; do echo "  $line"; done <<<"$BAD"
  rc=1
fi

# 2. The model does not depend on the checker or on any proof.
BAD=$(grep -rnE '^import +(Books|Checker)\b' --include='*.lean' --exclude-dir=.lake ../ruby-lean 2>/dev/null)
if [[ -n "$BAD" ]]; then
  echo "FAIL: the model's package imports from books/:"
  while IFS= read -r line; do echo "  $line"; done <<<"$BAD"
  rc=1
fi

# 3. The checker's executable does not import Lean's metaprogramming library.
#    Only the modules that generate or check source may (Checker/Audit/Derive.lean
#    and the files importing it); none of them is reachable from the executable,
#    which would otherwise link all of Lean and could not be built for the browser.
BAD=$(python3 - <<'PY'
import re
from pathlib import Path

def deps(module):
    path = Path(*module.split(".")).with_suffix(".lean")
    if not path.exists():
        return []
    return re.findall(r"^import\s+(\S+)", path.read_text(), re.M)

seen, todo, parent = set(), ["Books.TypeSoundness.Checker.Main"], {}
while todo:
    m = todo.pop()
    if m in seen:
        continue
    seen.add(m)
    for d in deps(m):
        parent.setdefault(d, m)
        todo.append(d)
if "Lean" in seen:
    chain, m = ["Lean"], "Lean"
    while m in parent:
        m = parent[m]
        chain.append(m)
    print(" <- ".join(chain))
PY
)
if [[ -n "$BAD" ]]; then
  echo "FAIL: the checker's executable imports Lean: $BAD"
  rc=1
fi

[[ $rc == 0 ]] && echo "OK: the checker imports only itself and Json, its executable does not import Lean, and the model imports nothing from books/."
exit $rc
