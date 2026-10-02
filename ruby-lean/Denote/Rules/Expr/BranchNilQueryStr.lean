import Denote.Rules.Expr.BranchNilQuery

/-! `if x.nil?` on a nilable String local. Object#nil? at a String answers false, or
gates as unsupported at a byte-string operand. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem RunWith.unsupported {origin start : Machine} {Γ : Env} {τ I : Ty} {κ : Ctx}
    {P : Value → Machine → Prop} {msg : String}
    (ha : answerPoint start = none) (hs : Interp.stepFn start = .unsupported msg) :
    RunWith origin start Γ τ κ I P := by
  refine ⟨(RunSpec.unsupported (origin := origin) (Γ := Γ) (τ := τ) (κ := κ) (I := I) ha hs).1, ?_⟩
  intro fuel a m rest hr
  cases fuel with
  | zero => rw [runA_zero ha] at hr; cases hr
  | succ f => rw [runA_succ ha, hs] at hr; cases hr

theorem str_nil_run (m : Machine) (o : ObjId) :
    Builtins.run "Object#nil?" (.ref o) [] m = .ok (.bool false) m ∨
      ∃ msg, Builtins.run "Object#nil?" (.ref o) [] m = .unsupported msg := by
  have hq : ("Object#nil?".endsWith "#==" || "Object#nil?".endsWith "#eql?" ||
      "Object#nil?".endsWith "#!=" || Builtins.pureEqualityBids.contains "Object#nil?") = false := by
    decide +kernel
  simp only [Builtins.run]
  split
  · exact .inr ⟨_, rfl⟩
  · simp only [hq, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    left; rfl

theorem nilQuery_cond_str {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {x : String}
    (hm : StateOk κ Γ I m)
    (hv : m.getLocal x = .nil ∨ ∃ o s, m.getLocal x = .ref o ∧
      classOf m.heap (.ref o) = Boot.stringId ∧ (m.heap.get o).payload = .str s)
    (hfree : nameFreeN κ "nil?" = true) :
    RunWith m (evalFrom m (.send (some (.var .lvar x)) "nil?" [] none)) Γ .bool κ I
      (fun v n => v = .bool (isNilV (m.getLocal x)) ∧ n.getLocal x = m.getLocal x) := by
  let k : Kont := .recvK "nil?" [] .none .explicit
  apply RunWith.step (answerPoint_evalFrom _ _)
    (show Interp.stepFn _ = .next (pushK [k] (evalFrom m (.var .lvar x))) from rfl)
  apply RunWith.step (by rfl) (show Interp.stepFn _ = .next (deliverA (.val (m.getLocal x)) m [k]) from by
    simpa only [pushK, evalFrom, deliverA, Answer.ctl, reCtl, getLocal_reCtl, List.nil_append] using
      step_var_ctl (m := pushK [k] (evalFrom m (.var .lvar x))) (x := x) rfl)
  let M := deliverA (.val (m.getLocal x)) m []
  have hM : StateOk κ Γ I M := StateOk_deliverA hm
  have hinv : Interp.stepFn (deliverA (.val (m.getLocal x)) m [k]) =
      Interp.invoke M (m.getLocal x) .explicit "nil?" [] none [] := rfl
  have hans : ∀ b, b = isNilV (m.getLocal x) →
      Interp.invoke M (m.getLocal x) .explicit "nil?" [] none [] = .next (Interp.withCtl M (.value (.bool b))) →
      RunWith m (deliverA (.val (m.getLocal x)) m [k]) Γ .bool κ I
        (fun v n => v = .bool (isNilV (m.getLocal x)) ∧ n.getLocal x = m.getLocal x) := by
    intro b hb hstep
    apply RunWith.step (by rfl) (hinv.trans hstep)
    apply RunWith.answer (a := .val (.bool b)) (m := M)
      (fun v n c ks hp => ⟨hp.1, by rw [getLocal_reCtl]; exact hp.2⟩)
    exact ⟨⟨Framed_reCtl m _ [], by simp [AnsOk, denM, isBoolV], fun _ _ => hM⟩,
      fun v hv => by cases hv; exact ⟨by rw [hb], getLocal_reCtl m _ [] x⟩⟩
  rcases hv with hn | ⟨o, s, hi, hc, hs⟩
  · apply hans true (by rw [hn]; rfl)
    rw [hn, primitive_invoke (bid := "NilClass#nil?") (k := Boot.nilClassId) hM
      (by simp [primitiveMethods]) rfl (by rfl) (by intro o ho; cases ho) (by rfl) (by rfl) hfree,
      nil_nil_run]
    rfl
  · have hinv' : Interp.invoke M (m.getLocal x) .explicit "nil?" [] none [] =
        builtinStep (Builtins.run "Object#nil?" (.ref o) [] M) := by
      rw [hi]
      exact primitive_invoke (bid := "Object#nil?") (k := Boot.stringId) hM
        (by simp [primitiveMethods]) hc (by rfl) (by intro o' ho'; cases ho'; exact ⟨s, hs⟩)
        (by simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
          nativeReal, rationalPayload?, complexPayload?, Builtins.toAryDefer?,
          Builtins.strCmpDefer?, Builtins.strCmpTwin?, hs]) (by rfl) hfree
    rcases str_nil_run M o with h | ⟨msg, h⟩
    · apply hans false (by rw [hi]; rfl)
      rw [hinv', h]
      rfl
    · exact RunWith.unsupported (by rfl) (hinv.trans (hinv'.trans (by rw [h]; rfl)))
  
#print axioms nilQuery_cond_str

theorem SemSafeCtxA.ifNilQueryStr {κ κ' : Ctx} {Γ Γ₁ Γ₂ : Env} {I I' : Ty} {x : String}
    {τ₁ τ₂ : Ty} {t e : Ratchet.Expr}
    (hx : envGet? Γ x = some (.nilable (.cls "String"))) (hfree : nameFreeN κ "nil?" = true)
    (hg : isANoOk κ.wholeCls (["String", "Comparable"] ++ rootAncestors) = true)
    (ht : SemSafeCtxA κ (envSet Γ x .nilT) I t τ₁ κ' Γ₁ I')
    (he : SemSafeCtxA κ (envSet Γ x (.cls "String")) I e τ₂ κ' Γ₂ I') :
    SemSafeCtxA κ Γ I (.if' (.send (some (.var .lvar x)) "nil?" [] none) t (some e))
      (joinT τ₁ τ₂) κ' (joinEnv Γ₁ Γ₂) I' := by
  intro m hm
  let k : Kont := .ifK (toRuby t) (some (toRuby e))
  have hv0 : denM (.nilable (.cls "String")) m (m.getLocal x) := by
    simpa [stripAlias] using (hm.env.1 x _ hx).1
  have hv : m.getLocal x = .nil ∨ ∃ o s, m.getLocal x = .ref o ∧
      classOf m.heap (.ref o) = Boot.stringId ∧ (m.heap.get o).payload = .str s := by
    rw [denM] at hv0
    rcases hv0 with h | h
    · left; cases hg' : m.getLocal x <;> rw [hg'] at h <;> simp_all [isNilV]
    · right
      obtain ⟨o, s, ho, hs⟩ := string_payload hm h hg
      exact ⟨o, s, ho, by rw [← ho]; exact string_class hm h hg, hs⟩
  apply RunSpec.step (answerPoint_evalFrom _ _)
    (show Interp.stepFn _ = .next (pushK [k] (evalFrom m (.send (some (.var .lvar x)) "nil?" [] none))) from rfl)
  apply (nilQuery_cond_str hm hv hfree).bindSpec hm.rootClean (by intro c hc; simp at hc; subst hc; rfl)
  intro a n hr
  cases a with
  | esc j =>
    apply RunSpec.step (by rfl)
      (show Interp.stepFn _ = .next (deliverA (.esc j) n []) from by cases j <;> rfl)
    exact RunSpec.answer ⟨hr.1.1, hr.1.2.1, fun _ hv => by cases hv⟩
  | val w =>
    obtain ⟨hw, hloc⟩ := hr.2 w rfl
    subst hw
    have hn : StateOk κ Γ I n := hr.1.2.2 _ rfl
    have hbranch : Interp.stepFn (deliverA (.val (.bool (isNilV (m.getLocal x)))) n [k]) =
        .next (evalFrom n (if isNilV (m.getLocal x) then t else e)) := by
      simp only [Interp.stepFn, deliverA, Answer.ctl, Interp.applyKont, k]
      cases hb : isNilV (m.getLocal x) <;> simp [Value.truthy, Interp.withCtl, evalFrom, toRuby]
    apply RunSpec.step (by rfl) hbranch
    apply RunSpec.rebase _ hr.1.1
    cases hb : isNilV (m.getLocal x)
    · have hstr : denM (.cls "String") n (n.getLocal x) := by
        rw [hloc]
        have hv1 := hv0
        rw [denM] at hv1
        rcases hv1 with h | h
        · cases hg' : m.getLocal x <;> rw [hg'] at h hb <;> simp_all [isNilV]
        · exact hr.1.1.firstOrder _ rfl _ h
      have hs : StateOk κ (envSet Γ x (.cls "String")) I n :=
        { hn with env := envOk_refine hn.env hx hstr rfl }
      simpa only [Bool.false_eq_true, ite_false] using
        (he.weaken (fun _ _ hm hd => ⟨StateOk_joinEnv false hm, denM_joinT_right hd⟩)) n hs
    · have hnil : denM .nilT n (n.getLocal x) := by
        rw [hloc]; simpa [denM] using hb
      have hs : StateOk κ (envSet Γ x .nilT) I n := { hn with env := envOk_refine hn.env hx hnil rfl }
      simpa only [ite_true] using
        (ht.weaken (fun _ _ hm hd => ⟨StateOk_joinEnv true hm, denM_joinT_left hd⟩)) n hs

#print axioms SemSafeCtxA.ifNilQueryStr
end Ratchet.Denote.Typed
