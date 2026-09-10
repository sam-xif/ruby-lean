import Denote.Rules.CaseEq

/-!
# `Denote/Rules/ClassOf.lean` — `x.class`, and the rung that was **false** last week

`Judge.classOf` types `x.class` as `.clsOf n` from a receiver premise of `.inst n I`. Under the
old denotation this obligation was **not provable, because it was not true**
(`found-issues.md` §F8): `denM (.inst n I)` was `isAName` — *is-a* — so an instance of a
declared subclass `D < C` satisfied `.inst "C"`, while the conclusion `.clsOf "C"` is the
*exact* class object. `D.new.class` is `D`.

§F12 is the fix, and it is a change to the **denotation** rather than to the rule:
`denM (.inst n I)` is now `isExactInst`, "a live object whose `realClassOf` is the class the
name resolves to". That is what the judgment always meant — `Judge` produces an `.inst n` only
by allocating exactly `n` or from a `self` whose class `κ.frame.recvClass` names exactly, and
`Ty.cls` keeps the is-a reading for `rescue`, which is the one place the slack is used (§F11).

With that, the two ends of this rung meet definitionally: `Object#class` answers `realClassOf`,
and `isExactInst` *is* `realClassOf` composed with `classNamed?`. The rest is the `is_a?`
recipe with an empty argument list.

The two `nameFree` premises are new too, and they are not the same kind of thing as §F6's:
`class` is a Ruby keyword, so no *program* can override it — but `κ` is a data structure and
the judgment quantifies over all of them, so the rule was relying on the grammar to imply
something about `Judge` that `Judge` does not enforce. Both discharge by `rfl` at every real
context.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

theorem Sem.Judge.classOf : Obl.Judge.classOf := by
  intro κ Γ Γ₁ Γ₂ I I₁ I₂ recv args n ivars hrecv hargs hcls _hmmfree
  refine ⟨trivial, ?_⟩
  intro m hm v m' hev
  obtain ⟨fuel, hrun⟩ := hev
  rcases fuel with _ | f
  · rw [run_zero] at hrun; exact absurd hrun (by simp)
  · rw [run_succ, stepFn_send_push] at hrun
    dsimp only at hrun
    obtain ⟨nb, v₀, m₀, hin, hc₀, hk₀, hout⟩ :=
      run_split _ (catchFree_recvK "class" (toRubyList args) .none _)
        (jumpOpaque_recvK "class" (toRubyList args) .none _) f (evalFrom m recv) v m' hrun
    obtain ⟨hframe₁, hdenR, hok₁, -⟩ := hrecv.2 m hm v₀ m₀ ⟨nb, hin⟩
    obtain ⟨f₂, hf₂⟩ := hout
    revert hf₂
    rcases f₂ with _ | f₃
    · intro hf₂; rw [run_zero] at hf₂; exact absurd hf₂ (by simp)
    · intro hf₂
      have hsr : StepRunsTo (Interp.stepFn
          (deliver m₀ v₀ [.recvK "class" (toRubyList args) .none
            (match toRuby recv with | .self' => .selfRecv | _ => .explicit)])) v m' := by
        refine stepRunsTo_of_run ?_ hf₂
        exact RubyCore.Proof.applyKont_notDone
          (deliver m₀ v₀ [.recvK "class" (toRubyList args) .none
            (match toRuby recv with | .self' => .selfRecv | _ => .explicit)]) v₀
          (by simp [deliver])
      rw [stepFn_recvK] at hsr
      have hm₀ : ({ m₀ with ctl := .value v₀, kont := [] } : Machine) = m₀ := by
        rw [← hc₀, ← hk₀]
      rw [hm₀] at hsr
      obtain ⟨vs, m₁, hallEv, hk₁, hfin⟩ :=
        run_args _ "class" v₀ .none args [] m₀ v m' hk₀ hargs.1 hsr
      obtain ⟨hframe₂, hden, hok₂⟩ := hargs.2 m₀ hok₁ vs m₁ hallEv
      rcases args with _ | ⟨a, arest⟩
      · rcases vs with _ | ⟨av, vrest⟩
        · have hma : m₁ = m₀ := hden
          subst hma
          simp only [List.nil_append] at hfin
          obtain ⟨m₂, hstep, f₄, hf₄⟩ := hfin
          rw [show Interp.finishSend m₁ v₀ _ "class" [] .none
                = Interp.invoke m₁ v₀ _ "class" [] none [] from rfl,
             invoke_clsq] at hstep
          cases hlk : Interp.methodOn m₁.heap (RubyCore.classOf m₁.heap v₀) "class" with
          | some p =>
            obtain ⟨owner, md⟩ := p
            obtain ⟨hq1, _⟩ := hok₂.query "class" "Object#class" (by simp [queryBuiltins])
              hcls (RubyCore.classOf m₁.heap v₀)
            obtain ⟨hb, hu, hv, hp, hsh⟩ := hq1 owner md hlk
            rcases invokeDispatch_clsq hlk hb hu hv hp hsh with hd | ⟨r, hd⟩
            · rw [hd] at hstep
              cases hstep
              revert hf₄
              rcases f₄ with _ | f₅
              · intro hf₄; rw [run_zero] at hf₄; exact absurd hf₄ (by simp)
              · intro hf₄
                have hwc : Interp.withCtl m₁ (Ctl.value (.ref (RubyCore.realClassOf m₁.heap v₀)))
                    = reCtl m₁ (.value (.ref (RubyCore.realClassOf m₁.heap v₀))) [] := by
                  rw [Interp.withCtl, reCtl, hk₁]
                rw [run_succ, hwc, stepFn_value_nil] at hf₄
                dsimp only at hf₄
                cases hf₄
                refine ⟨hframe₁.trans (Framed_reCtl _ _ _), ?_, ⟨StateOk_reCtl hok₂ _ _, StateOk_reCtl hok₂ _ _⟩⟩
                -- **the two ends meet**: the receiver's type says `realClassOf v₀` *is* the
                -- class `n` resolves to, and that is the value the builtin answered
                obtain ⟨k, hcn, hrc⟩ := denM_inst_exact hdenR
                rw [denM]
                -- `unfold`, not `rw`: the arm equation would unify `classNamed?` with a
                -- metavariable instead of with `hcn`'s answer
                unfold isClassRefNamed
                simp [show (reCtl m₁ (Ctl.value (Value.ref
                    (RubyCore.realClassOf m₁.heap v₀))) []).heap = m₁.heap from rfl, hcn, hrc]
            · rw [hd] at hstep; exact absurd hstep (by simp)
          | none =>
            obtain ⟨_, hq2⟩ := hok₂.query "class" "Object#class" (by simp [queryBuiltins])
              hcls (RubyCore.classOf m₁.heap v₀)
            rcases invokeDispatch_clsq_miss hlk (hq2 hlk) with ⟨r, hd⟩ | ⟨cls, msg, hd⟩
            · rw [hd] at hstep; exact absurd hstep (by simp)
            · rw [hd] at hstep
              cases hstep
              exact absurd hf₄ (jump_empty_never_value f₄ _ v m'
                ⟨_, raiseErr_ctl _ _ _⟩ (by rw [raiseErr_kont, hk₁]))
        · exact absurd hden (by simp [DenAllAt])
      · exact absurd hden (by cases vs <;> simp [DenAllAt])

#print axioms Sem.Judge.classOf

end Ratchet.Denote
