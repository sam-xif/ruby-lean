import Denote.Rules.Core
import Denote.Sem.Obligations

/-!
# `Denote/Rules/Cls.lean` — the two class-body families, `cons` case

`JudgeConsts` and `JudgeNested` are the two members of the family whose syntactic form carries
**no `Env` threading and no result type** (`Denote/Sem/Judge.lean`): they are well-formedness
side conditions on a `class`/`module` statement. Their semantic readings were written as
∀-over-the-list predicates for exactly that reason, and the consequence shows up here — a
`cons` rung is *list bookkeeping*, not machine reasoning:

* **`JudgeConsts.cons`** hands over its head's two facts (`constLitTy?` and the entry's own
  `SemJudge`) and delegates the tail to its own `SemJudgeConsts` premise.
* **`JudgeNested.cons`** does the same one level up, and the only step with content is
  `classMethods?`'s **injectivity at the head**: the obligation's reader supplies its own
  decomposition of `body`, the premise supplies the rule's, and the two agree because
  `classMethods?` is a function. `cs` is then the same list on both sides and the premise
  applies.

**Both rungs are cheap, and the deeper recursion is *not* here.** `SemJudgeNested` reads one
level deep by design (its docstring records that as a scaffolding choice with a stated risk),
and these two rungs are what that design buys: the recursion is carried by the constructor's
own premise, which is what makes the `cons` case provable without an induction principle over
nestings. The risk it records is unchanged — it is `Judge.classStmt`'s rung that will say
whether one-level-deep is enough, and `classStmt` is blocked for an unrelated reason
(`../Sem/notes.md` §The sixth stall point).
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

theorem Sem.JudgeConsts.cons : Obl.JudgeConsts.cons := by
  intro κ n e τ cs hlit hj hcs n' e' hmem
  rcases List.mem_cons.mp hmem with h | h
  · cases h; exact ⟨τ, hlit, hj⟩
  · exact hcs n' e' h

theorem Sem.JudgeNested.cons : Obl.JudgeNested.cons := by
  intro κ pfx isMod n body ms sms incs exts preps cs nst rest
    hcm _hmods _hconst hcs _hnst hrest
  intro isMod' n' body' hmem ms' sms' incs' exts' preps' cs' nst' hcm'
  rcases List.mem_cons.mp hmem with h | h
  · -- The head: `classMethods?` is a function, so the reader's decomposition is the rule's.
    cases h
    rw [hcm] at hcm'
    cases hcm'
    exact hcs
  · exact hrest isMod' n' body' h ms' sms' incs' exts' preps' cs' nst' hcm'

#print axioms Sem.JudgeConsts.cons
#print axioms Sem.JudgeNested.cons

end Ratchet.Denote
