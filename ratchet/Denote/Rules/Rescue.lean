import Denote.Join
import Denote.Rules.Core
import Denote.Sem.Obligations

/-!
# `Denote/Rules/Rescue.lean` — a rescue clause list

`JudgeRescues.cons` is the one `cons` rule in the whole family that is **not** blocked by the
continuation wall (`../Sem/notes.md` §The fifth stall point), and the reason is a property of
its signature rather than of its proof: `JudgeRescues` threads **no outgoing state**. Its
`cons` rule pins `Γ' = Γh ++ Γ` and `I' = I` as premises — a handler's assignments must not
escape a clause that may not have run — so the premise about the head handler is a statement
about *the same run* the conclusion asks about, and nothing has to be decomposed or
transported between two of them.

What is left is the **join**. `JudgeRescues`' type index is the join over all clauses (what
`Judge.beginRescue` consumes), so the per-clause claim is "in `joinT τ τr`" while the head
premise gives "in `τ`" and the tail gives "in `τr`". That is `Denote/Join.lean`'s pair of
upper-bound lemmas, and this rung is the first consumer of them; `Judge.if'`, `ifNoElse`,
`arrayLit`, `hashLit` and `while'` will be the others.

The one step with content beyond that is `rescueClasses?`/`rescueBind?` being **functions**:
the obligation's reader supplies its own `names` and `Γh`, the rule supplies the premise's, and
the two agree. Same move as `classMethods?` in `Cls.lean`.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

theorem Sem.JudgeRescues.cons : Obl.JudgeRescues.cons := by
  intro κ Γ Γh Γ' I I' cls binding handler names τ τr rest
    hcls _hexc hbind hhandler hΓ' hI' hrest
  subst hΓ'; subst hI'
  intro cls' binding' handler' hmem names' Γh' hcls' hbind'
  first
    | refine ⟨by first | trivial | simp [PlainAll, Plain]
                       | simp_all [PlainAll, Plain], ?_⟩
    | skip
  intro m hm v m' hev
  rcases List.mem_cons.mp hmem with heq | htl
  · -- The head clause: the reader's `names`/`Γh` are the rule's, and the head premise applies
    -- to exactly this run.
    cases heq
    rw [hcls] at hcls'; cases hcls'
    rw [hbind] at hbind'; cases hbind'
    obtain ⟨hstack, hden, hok⟩ := hhandler.2 m hm v m' hev
    exact ⟨hstack, denM_joinT_left hden, hok⟩
  · obtain ⟨hstack, hden, hok⟩ :=
      hrest cls' binding' handler' htl names' Γh' hcls' hbind' m hm v m' hev
    exact ⟨hstack, denM_joinT_right hden, hok⟩

#print axioms Sem.JudgeRescues.cons

end Ratchet.Denote
