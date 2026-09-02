import Denote.Join
import Denote.Rules.Core
import Denote.Rules.Alloc
import Denote.Rules.Lit
import Denote.Rules.Nil
import Denote.Rules.Asgn
import Denote.Rules.Read
import Denote.Rules.Seq
import Denote.Rules.Regexp
import Denote.Rules.Cls
import Denote.Rules.Rescue
import Denote.Rules.Const

/-!
# `Denote/Rules.lean` — every discharged rung, in one import

`Denote/Ladder.lean` counts a rule as discharged by looking for `Sem.<Family>.<rule>` **in
the environment**, so a rung only counts if the file proving it is in the ladder's import
graph. This is that graph: one line per rule file, and the single line `Denote/Ladder.lean`
imports.

Adding a rung is therefore two edits — the theorem, and its file's line here — and no edit at
all to the counting mechanism, which is the part `Denote/Sem/notes.md` marks "never
hand-edited".
-/
