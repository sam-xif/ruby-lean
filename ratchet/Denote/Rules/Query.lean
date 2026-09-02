import Denote.Sem.Query
import Denote.Rules.Never

/-!
# `Denote/Rules/Query.lean` — `recv.is_a?(C)`

The first rung whose run goes all the way through a **dispatch**: receiver, argument, lookup,
builtin. Everything hard is in `../Sem/Send.lean` (the argument walk), `../Sem/Query.lean` (the
dispatch chain) and `../Sem/State.lean`'s `QueryOk` (the heap facts the dispatch reads); what
is left here is the assembly, plus the one thing the rule owes its own premises —
`found-issues.md` §F6.

## Why the conclusion is easy once the chain is walked

`Ty.bool`'s denotation is "is a boolean", and `Object#is_a?` answers `isA`, a `Bool`. So this
rung needs **no signature table**: it never has to know *which* boolean. That is what makes it
the cheap end of the dispatch family, and why `classOf`/`clsToS` (which answer a class and a
string) are the natural next two.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

theorem Sem.Judge.isAQuery : Obl.Judge.isAQuery := by
  intro κ Γ Γ₁ Γ₂ I I₁ I₂ recv args σ cn hrecv hargs _hdisp hisa hmmfree
  refine ⟨trivial, ?_⟩
  intro m hm v m' hev
  obtain ⟨fuel, hrun⟩ := hev
  rcases fuel with _ | f
  · rw [run_zero] at hrun; exact absurd hrun (by simp)
  · -- **the receiver link**
    rw [run_succ, stepFn_send_push] at hrun
    dsimp only at hrun
    obtain ⟨nb, v₀, m₀, hin, hc₀, hk₀, hout⟩ :=
      run_split _ (catchFree_recvK "is_a?" (toRubyList args) .none _)
        (jumpOpaque_recvK "is_a?" (toRubyList args) .none _) f (evalFrom m recv) v m' hrun
    obtain ⟨hstack, _, hok₁⟩ := hrecv.2 m hm v₀ m₀ ⟨nb, hin⟩
    obtain ⟨f₂, hf₂⟩ := hout
    revert hf₂
    rcases f₂ with _ | f₃
    · intro hf₂; rw [run_zero] at hf₂; exact absurd hf₂ (by simp)
    · intro hf₂
      -- **the argument link**: step the `.recvK` delivery, then walk the arguments
      have hsr : StepRunsTo (Interp.stepFn
          (deliver m₀ v₀ [.recvK "is_a?" (toRubyList args) .none
            (match toRuby recv with | .self' => .selfRecv | _ => .explicit)])) v m' := by
        refine stepRunsTo_of_run ?_ hf₂
        exact RubyCore.Proof.applyKont_notDone
          (deliver m₀ v₀ [.recvK "is_a?" (toRubyList args) .none
            (match toRuby recv with | .self' => .selfRecv | _ => .explicit)]) v₀
          (by simp [deliver])
      rw [stepFn_recvK] at hsr
      have hm₀ : ({ m₀ with ctl := .value v₀, kont := [] } : Machine) = m₀ := by
        rw [← hc₀, ← hk₀]
      rw [hm₀] at hsr
      obtain ⟨vs, m₁, hallEv, hk₁, hfin⟩ :=
        run_args _ "is_a?" v₀ .none args [] m₀ v m' hk₀ hargs.1 hsr
      obtain ⟨hst₂, hden, hok₂⟩ := hargs.2 m₀ hok₁ vs m₁ hallEv
      -- **the argument is a class reference**, and the machine it left is `m₁`
      rcases args with _ | ⟨a, arest⟩
      · exact absurd hden (by simp [DenAllAt])
      · rcases arest with _ | ⟨a2, arest2⟩
        · rcases vs with _ | ⟨av, vrest⟩
          · exact absurd hden (by simp [DenAllAt])
          · rcases vrest with _ | ⟨av2, vrest2⟩
            · obtain ⟨ma, _, hdenA, hrest⟩ := hden
              have hma : ma = m₁ := (hrest : m₁ = ma).symm
              subst hma
              obtain ⟨ka, _, rfl, hka⟩ := denM_clsOf_ref hdenA
              -- **the dispatch**
              simp only [List.nil_append] at hfin
              obtain ⟨m₂, hstep, f₄, hf₄⟩ := hfin
              rw [show Interp.finishSend ma v₀ _ "is_a?" [Value.ref ka] .none
                    = Interp.invoke ma v₀ _ "is_a?" [Value.ref ka] none [] from rfl,
                 invoke_isA] at hstep
              cases hlk : Interp.methodOn ma.heap (classOf ma.heap v₀) "is_a?" with
              | some p =>
                obtain ⟨owner, md⟩ := p
                obtain ⟨hq1, _⟩ := hok₂.query "is_a?" "Object#is_a?" (by simp [queryBuiltins])
                  hisa (classOf ma.heap v₀)
                obtain ⟨hb, hu, hv, hp, hsh⟩ := hq1 owner md hlk
                rcases invokeDispatch_isA hlk hb hu hv hp hsh hka with hd | ⟨r, hd⟩
                · rw [hd] at hstep
                  cases hstep
                  -- the value is in flight under an empty continuation: one more step ends it
                  revert hf₄
                  rcases f₄ with _ | f₅
                  · intro hf₄; rw [run_zero] at hf₄; exact absurd hf₄ (by simp)
                  · intro hf₄
                    rw [run_succ, show Interp.stepFn (Interp.withCtl ma
                          (.value (.bool (isA ma.heap v₀ ka))))
                        = .done (.bool (isA ma.heap v₀ ka)) (Interp.withCtl ma
                          (.value (.bool (isA ma.heap v₀ ka)))) from by
                          rw [show Interp.withCtl ma (Ctl.value (.bool (isA ma.heap v₀ ka)))
                                = reCtl ma (.value (.bool (isA ma.heap v₀ ka))) [] from by
                                rw [Interp.withCtl, reCtl, hk₁]
                              ]
                          exact stepFn_value_nil _ _] at hf₄
                    dsimp only at hf₄
                    cases hf₄
                    refine ⟨?_, ?_, ?_⟩
                    · show (Interp.withCtl ma _).stack = m.stack
                      rw [Interp.withCtl]
                      show ma.stack = m.stack
                      rw [hst₂, hstack]
                    · -- `Ty.bool`'s denotation is "is a boolean", and this is one
                      simp [denM, isBoolV]
                    · rw [show Interp.withCtl ma (Ctl.value (Value.bool (isA ma.heap v₀ ka)))
                            = reCtl ma (.value (.bool (isA ma.heap v₀ ka))) [] from by
                          rw [Interp.withCtl, reCtl, hk₁]]
                      exact StateOk_reCtl hok₂ _ _
                · rw [hd] at hstep; exact absurd hstep (by simp)
              | none =>
                obtain ⟨_, hq2⟩ := hok₂.query "is_a?" "Object#is_a?" (by simp [queryBuiltins])
                  hisa (classOf ma.heap v₀)
                rcases invokeDispatch_isA_miss hlk (hq2 hlk) with ⟨r, hd⟩ | ⟨cls, msg, hd⟩
                · rw [hd] at hstep; exact absurd hstep (by simp)
                · rw [hd] at hstep
                  cases hstep
                  exact absurd hf₄ (jump_empty_never_value f₄ _ v m'
                    ⟨_, raiseErr_ctl _ _ _⟩ (by rw [raiseErr_kont, hk₁]))
            · exact absurd hden (by simp [DenAllAt])
        · -- two or more arguments: the type list runs out one step in, so the mismatch is in
          -- `DenAllAt`'s *tail* and has to be reached through the existential
          rcases vs with _ | ⟨av, vrest⟩
          · exact absurd hden (by simp [DenAllAt])
          · obtain ⟨mm, _, _, hrest⟩ := hden
            exact absurd hrest (by cases vrest <;> simp [DenAllAt])

#print axioms Sem.Judge.isAQuery

end Ratchet.Denote
