import Denote.Sem.Query
import Denote.Rules.Query

/-!
# `Denote/Rules/CaseEq.lean` — `C === v`, and the transport a send needs

`Judge.caseEqQuery` is `Module#===`, what `case v when C` desugars to. It is the second rung
through a dispatch and it looks like the first (`Denote/Rules/Query.lean`) — but it is the rung
that forced the `Framed` conjunct, and that is the interesting part.

## Why a `.clsOf` receiver needs something `StateOk` cannot give

The run evaluates the receiver first, then the argument, then dispatches. So the receiver's
type is established at `m₀` and *read* at `m₁`, with an arbitrary expression's evaluation in
between — and the fact the dispatch reads is that the receiver is a class object, which is a
fact about the heap. `StateOk` is a predicate on one machine, so it cannot bridge that; nothing
in the ratchet could, until `SemJudge`'s first conjunct became `Framed` (see its docstring),
whose `cls` field is "once a class, always a class". The argument premise's own `Framed m₀ m₁`
is the transport, and this rung's whole extra move over `is_a?` is one application of it.

`is_a?` did not need it because there the class reference is the **argument**, typed at the
machine the dispatch happens at. Swap the operands and the transport becomes load-bearing —
which is the general shape for every remaining call rule, and the reason the conjunct was
worth adding to the definition rather than worked around here.

## The rule's own premises

`found-issues.md` §F7: the rule's `smroGet? κ.classes cn "=== " = none` guard sees only
singleton methods on `cn` itself, while the dispatch walks the eigenclass chain — so a
`class Module; def ===(o); "boom"; end; end` binds ahead of the builtin and the guard never
notices. `nameFree κ "==="` is the missing assumption, and it is what lets `ClsQueryOk`
(`../Sem/State.lean`) apply.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

theorem Sem.Judge.caseEqQuery : Obl.Judge.caseEqQuery := by
  intro κ Γ Γ₁ Γ₂ I I₁ I₂ recv args cn σ hrecv hargs _hsmro hce _hmmfree
  refine ⟨trivial, ?_⟩
  intro m hm v m' hev
  obtain ⟨fuel, hrun⟩ := hev
  rcases fuel with _ | f
  · rw [run_zero] at hrun; exact absurd hrun (by simp)
  · -- **the receiver link**
    rw [run_succ, stepFn_send_push] at hrun
    dsimp only at hrun
    obtain ⟨nb, v₀, m₀, hin, hc₀, hk₀, hout⟩ :=
      run_split _ (catchFree_recvK "===" (toRubyList args) .none _)
        (jumpOpaque_recvK "===" (toRubyList args) .none _) f (evalFrom m recv) v m' hrun
    obtain ⟨hframe₁, hdenR, hok₁⟩ := hrecv.2 m hm v₀ m₀ ⟨nb, hin⟩
    -- the receiver is a live class object, **at `m₀`**
    obtain ⟨k, _, rfl, hk⟩ := denM_clsOf_ref hdenR
    obtain ⟨f₂, hf₂⟩ := hout
    revert hf₂
    rcases f₂ with _ | f₃
    · intro hf₂; rw [run_zero] at hf₂; exact absurd hf₂ (by simp)
    · intro hf₂
      -- **the argument link**
      have hsr : StepRunsTo (Interp.stepFn
          (deliver m₀ (.ref k) [.recvK "===" (toRubyList args) .none
            (match toRuby recv with | .self' => .selfRecv | _ => .explicit)])) v m' := by
        refine stepRunsTo_of_run ?_ hf₂
        exact RubyCore.Proof.applyKont_notDone
          (deliver m₀ (.ref k) [.recvK "===" (toRubyList args) .none
            (match toRuby recv with | .self' => .selfRecv | _ => .explicit)]) (.ref k)
          (by simp [deliver])
      rw [stepFn_recvK] at hsr
      have hm₀ : ({ m₀ with ctl := .value (.ref k), kont := [] } : Machine) = m₀ := by
        rw [← hc₀, ← hk₀]
      rw [hm₀] at hsr
      obtain ⟨vs, m₁, hallEv, hk₁, hfin⟩ :=
        run_args _ "===" (.ref k) .none args [] m₀ v m' hk₀ hargs.1 hsr
      obtain ⟨hframe₂, hden, hok₂⟩ := hargs.2 m₀ hok₁ vs m₁ hallEv
      -- one argument, of an unconstrained type: `Module#===` is total on it
      rcases args with _ | ⟨a, arest⟩
      · exact absurd hden (by simp [DenAllAt])
      · rcases arest with _ | ⟨a2, arest2⟩
        · rcases vs with _ | ⟨av, vrest⟩
          · exact absurd hden (by simp [DenAllAt])
          · rcases vrest with _ | ⟨av2, vrest2⟩
            · obtain ⟨ma, _, _, hrest⟩ := hden
              have hma : ma = m₁ := (hrest : m₁ = ma).symm
              subst hma
              -- **the transport**: class-ness of the receiver, carried across the argument's
              -- evaluation by the argument premise's own `Framed`
              have hka : (ma.heap.classPayload? k).isSome = true := hframe₂.cls k hk
              -- **the dispatch**
              simp only [List.nil_append] at hfin
              obtain ⟨m₂, hstep, f₄, hf₄⟩ := hfin
              rw [show Interp.finishSend ma (.ref k) _ "===" [av] .none
                    = Interp.invoke ma (.ref k) _ "===" [av] none [] from rfl,
                 invoke_caseEq] at hstep
              cases hlk : Interp.methodOn ma.heap (classOf ma.heap (.ref k)) "===" with
              | some p =>
                obtain ⟨owner, md⟩ := p
                obtain ⟨hq1, _⟩ := hok₂.clsQuery "===" "Module#===" (by simp [clsQueryBuiltins])
                  hce k hka
                obtain ⟨hb, hu, hv, hp, hsh⟩ := hq1 owner md hlk
                rcases invokeDispatch_caseEq hlk hb hu hv hp hsh hka with hd | ⟨r, hd⟩
                · rw [hd] at hstep
                  cases hstep
                  revert hf₄
                  rcases f₄ with _ | f₅
                  · intro hf₄; rw [run_zero] at hf₄; exact absurd hf₄ (by simp)
                  · intro hf₄
                    rw [run_succ, show Interp.stepFn (Interp.withCtl ma
                          (.value (.bool (isA ma.heap av k))))
                        = .done (.bool (isA ma.heap av k)) (Interp.withCtl ma
                          (.value (.bool (isA ma.heap av k)))) from by
                          rw [show Interp.withCtl ma (Ctl.value (.bool (isA ma.heap av k)))
                                = reCtl ma (.value (.bool (isA ma.heap av k))) [] from by
                                rw [Interp.withCtl, reCtl, hk₁]
                              ]
                          exact stepFn_value_nil _ _] at hf₄
                    dsimp only at hf₄
                    cases hf₄
                    refine ⟨(hframe₁.trans hframe₂).trans (Framed_withCtl _ _), ?_, ?_⟩
                    · simp [denM, isBoolV]
                    · rw [show Interp.withCtl ma (Ctl.value (Value.bool (isA ma.heap av k)))
                            = reCtl ma (.value (.bool (isA ma.heap av k))) [] from by
                          rw [Interp.withCtl, reCtl, hk₁]]
                      exact StateOk_reCtl hok₂ _ _
                · rw [hd] at hstep; exact absurd hstep (by simp)
              | none =>
                obtain ⟨_, hq2⟩ := hok₂.clsQuery "===" "Module#===" (by simp [clsQueryBuiltins])
                  hce k hka
                rcases invokeDispatch_caseEq_miss hlk (hq2 hlk) with ⟨r, hd⟩ | ⟨cls, msg, hd⟩
                · rw [hd] at hstep; exact absurd hstep (by simp)
                · rw [hd] at hstep
                  cases hstep
                  exact absurd hf₄ (jump_empty_never_value f₄ _ v m'
                    ⟨_, raiseErr_ctl _ _ _⟩ (by rw [raiseErr_kont, hk₁]))
            · exact absurd hden (by simp [DenAllAt])
        · rcases vs with _ | ⟨av, vrest⟩
          · exact absurd hden (by simp [DenAllAt])
          · obtain ⟨mm, _, _, hrest⟩ := hden
            exact absurd hrest (by cases vrest <;> simp [DenAllAt])

#print axioms Sem.Judge.caseEqQuery

end Ratchet.Denote
