import Books.TypeSoundness.Rules.Init.InitExpr
import Books.TypeSoundness.Denotation.Join

/-! Initializer forms for fields whose type depends on an argument: a String literal, an
`if` on a Boolean parameter, and widening a value's type to a union before it is written. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem SemInitA.strLit {κ : Ctx} {Γ : Env} {I : Ty} {s : String} :
    SemInitA κ Γ I (.str s) (.cls "String") κ Γ I := by
  intro anchor m hm
  let M := reCtl { m with heap := pushHeap m.heap (strObj s) } (.value (.ref m.heap.objs.size)) []
  obtain ⟨hok, hden⟩ := strLit_alloc_ok (s := s) [] hm.typed
  have he : Ext m M :=
    (ext_push (m := m) (strObj s) hm.typed.sat hm.typed.core.basicSelf
      (fun c => by simp [strObj]) rfl rfl (by simpa [strObj] using hm.typed.core.stringBasic)).trans
      (Ext_toReCtl _ _ _)
  apply InitRunSpec.step (answerPoint_evalFrom _ _) (stepFn_str m s)
  have hgrow : InitGrow anchor M.heap := hm.growth.trans he.initGrow
  obtain ⟨o, hs, hlo, hhi, hfz⟩ := hm.fresh
  refine InitRunSpec.answer (a := .val (.ref m.heap.objs.size)) (m := M)
    ⟨⟨hgrow, rfl, .of_eq rfl rfl, fun τ _ v hv => denM_ext he hv, rfl, id⟩, hden,
      fun _ _ => ⟨hok, hgrow, ⟨o, hs, hlo, Nat.lt_of_lt_of_le hhi he.size, ?_⟩⟩⟩
  rw [he.get o hhi]; exact hfz

/-- A value's type may be widened to a join before it is written to a field. -/
theorem SemInitA.widenL {κ κ' : Ctx} {Γ Γ' : Env} {I I' ρ σ : Ty} {e : Checker.Expr}
    (h : SemInitA κ Γ I e ρ κ' Γ' I') : SemInitA κ Γ I e (joinT ρ σ) κ' Γ' I' :=
  fun anchor m hm => (h anchor m hm).weaken (fun _ _ hn hd => ⟨hn, denM_joinT_left hd⟩)

theorem SemInitA.widenR {κ κ' : Ctx} {Γ Γ' : Env} {I I' ρ σ : Ty} {e : Checker.Expr}
    (h : SemInitA κ Γ I e ρ κ' Γ' I') : SemInitA κ Γ I e (joinT σ ρ) κ' Γ' I' :=
  fun anchor m hm => (h anchor m hm).weaken (fun _ _ hn hd => ⟨hn, denM_joinT_right hd⟩)

/-- `if x` on a local: whichever branch runs, both end in the same fields. -/
theorem SemInitA.ifVar {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ σ τ₁ τ₂ : Ty} {x : String}
    {t e : Checker.Expr} (hx : envGet? Γ x = some σ)
    (ht : SemInitA κ Γ I t τ₁ κ' Γ' I') (he : SemInitA κ Γ I e τ₂ κ' Γ' I')
    (hτ : τ = joinT τ₁ τ₂) :
    SemInitA κ Γ I (.if' (.var .lvar x) t (some e)) τ κ' Γ' I' := by
  subst hτ
  intro anchor m hm
  let k : Kont := .ifK (toRuby t) (some (toRuby e))
  apply InitRunSpec.step (answerPoint_evalFrom _ _)
    (show Interp.stepFn _ = .next (pushK [k] (evalFrom m (.var .lvar x))) from rfl)
  apply InitRunSpec.step (by rfl) (show Interp.stepFn _ = .next (deliverA (.val (m.getLocal x)) m [k]) from by
    simpa only [pushK, evalFrom, deliverA, Answer.ctl, reCtl, getLocal_reCtl, List.nil_append] using
      step_var_ctl (m := pushK [k] (evalFrom m (.var .lvar x))) (x := x) rfl)
  have hbranch : Interp.stepFn (deliverA (.val (m.getLocal x)) m [k]) =
      .next (evalFrom m (if (m.getLocal x).truthy then t else e)) := by
    simp only [Interp.stepFn, deliverA, Answer.ctl, Interp.applyKont, k]
    cases hv : (m.getLocal x).truthy <;> simp [hv, Interp.withCtl, evalFrom, toRuby]
  apply InitRunSpec.step (by rfl) hbranch
  cases htr : (m.getLocal x).truthy
  · simpa only [Bool.false_eq_true, ite_false] using
      (he anchor m hm).weaken (fun _ _ hn hd => ⟨hn, denM_joinT_right hd⟩)
  · simpa only [ite_true] using
      (ht anchor m hm).weaken (fun _ _ hn hd => ⟨hn, denM_joinT_left hd⟩)

#print axioms SemInitA.strLit
#print axioms SemInitA.ifVar
end Checker.Soundness.Typed
