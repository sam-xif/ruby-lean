/-
A vendored copy of Lean's JSON library, at the root namespace (`Json`, not
`Lean.Json`), so that nothing in this project has to `import Lean.Data.Json`.

That import is not free: it links `libLean` — the frontend, the elaborator, the
kernel — into every executable that uses it. On toolchain v4.32.2 a hello-world
Lean executable is 2.26 MB; the same executable with `import Lean.Data.Json`
added and nothing else changed is 98.86 MB. `rubycore` was 102 MB and
`validate-one`, whose own code is 27 lines, was 99 MB.

The three files under `Json/` are upstream's, with the outer namespace dropped
and the `Lean.Data.*` imports repointed. Each carries its own note saying so.
See `Json/Basic.lean` for the full list of changes.
-/
import Json.Basic
import Json.Parser
import Json.Printer
import Json.FromToJson
