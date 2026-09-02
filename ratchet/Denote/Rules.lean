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
import Denote.Rules.Bare
import Denote.Rules.Args
import Denote.Rules.Lambda
import Denote.Rules.Vasgn
import Denote.Rules.Never
import Denote.Rules.Path
import Denote.Rules.Query
import Denote.Rules.CaseEq
import Denote.Rules.ClsToS
import Denote.Rules.ClassOf
import Denote.Rules.NewInst
import Denote.Sem.Frame

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
