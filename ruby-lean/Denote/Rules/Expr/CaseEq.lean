import Denote.Rules.Expr.BranchIsA

/-! `case x when C`: the desugarer binds a temporary to `x` and tests `C === tmp`.
`vasgnAlias` records the temporary as an alias (`Ty.sameAs`), and `ifCaseEq` refines both
names by `isATy`/`notATy`. `Module#===` is the ancestor test with the sides swapped; its
dispatch at any class object is `ClsQueryOk`. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemSafeCtxA.vasgnAlias {κ : Ctx} {Γ : Env} {I σ : Ty} {t x : String}
    (hx : envGet? Γ x = some σ) (ha : isAliasTy σ = false) (hne : x ≠ t)
    (hc : capStale t σ σ = false) (hk : capStaleCtx t σ κ = false) :
    SemSafeCtxA κ Γ I (.vasgn .lvar t (.var .lvar x)) σ κ
      (envSet (killClosOver (killAliasesTo Γ t) t σ) t (.sameAs x σ))
      (killClosOverSpine I t σ) := by
  intro m hm
  let v := m.getLocal x
  apply RunSpec.step (answerPoint_evalFrom _ _)
    (show Interp.stepFn (evalFrom m (.vasgn .lvar t (.var .lvar x))) =
      .next (pushK [.asgnK .lvar t] (evalFrom m (.var .lvar x))) from rfl)
  have hread : Interp.stepFn (pushK [.asgnK .lvar t] (evalFrom m (.var .lvar x))) =
      .next (deliverA (.val v) m [.asgnK .lvar t]) := by
    simpa only [pushK, evalFrom, deliverA, Answer.ctl, reCtl, getLocal_reCtl, List.nil_append] using
      step_var_ctl (m := pushK [.asgnK .lvar t] (evalFrom m (.var .lvar x))) (x := x) rfl
  apply RunSpec.step (by rfl) hread
  let base := reCtl m (.value v) []
  have hn : StateOk κ Γ I base := StateOk_reCtl hm _ _
  have hd : denM σ base v := denM_reCtl.mpr (denM_getLocal hm hx ha)
  have hout : StateOk κ (envSet (killClosOver (killAliasesTo Γ t) t σ) t (.sameAs x σ))
      (killClosOverSpine I t σ) (base.setLocal t v) :=
    StateOk_setLocal hn hd hc hk (ρ := .sameAs x σ) rfl
      (by
        intro y σ' hy
        cases hy
        rw [getLocal_setLocal_ne _ _ _ hne]
        exact (getLocal_reCtl m _ _ x).symm)
  apply RunSpec.step (by rfl)
    (show Interp.stepFn (deliverA (.val v) m [.asgnK .lvar t]) =
      .next (deliverA (.val v) (base.setLocal t v) []) from rfl)
  exact RunSpec.answer ⟨(Framed_reCtl m _ []).trans (Framed_setLocal base t v (by
      rw [← currentFrame_headD hn.frameInRange.1]; exact hn.localAlias)),
    denM_setLocal hd hc hd, fun _ _ => hout⟩

#print axioms SemSafeCtxA.vasgnAlias

theorem caseEq_run (m : Machine) (v : Value) (k : ObjId)
    (hk : (m.heap.classPayload? k).isSome = true) :
    Builtins.run "Module#===" (.ref k) [v] m = .ok (.bool (isA m.heap v k)) m ∨
      ∃ msg, Builtins.run "Module#===" (.ref k) [v] m = .unsupported msg := by
  have hq : ("Module#===".endsWith "#==" || "Module#===".endsWith "#eql?" ||
      "Module#===".endsWith "#!=" || Builtins.pureEqualityBids.contains "Module#===") = false := by
    decide +kernel
  simp only [Builtins.run]
  split
  · exact .inr ⟨_, rfl⟩
  · simp only [hq, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    left
    change Builtins.runModules "Module#===" (.ref k) [v] m = _
    simp [Builtins.runModules, Builtins.binArg, hk]

theorem caseEq_deferTwin (h : Heap) (k : ObjId) (v : Value) :
    Builtins.deferTwin? h "Module#===" (.ref k) [v] = none := by
  simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
    Builtins.toAryDefer?, Builtins.strCmpDefer?, Builtins.strCmpTwin?, Builtins.coerceTwin?]

theorem invoke_caseEq_plain (m : Machine) (o : ObjId) (site : SendSite) (args : List Value) :
    Interp.invoke m (.ref o) site "===" args none [] =
      Interp.invoke.invokeDispatch m (.ref o) site "===" args none [] := by
  rw [Interp.invoke.eq_def]
  simp only [show (("===" : String) == "send" || "===" == "public_send" || "===" == "__send__") = false
    from by decide, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  cases hp : (m.heap.get o).payload <;> simp
  done

/-- `C === t` at a local: the ancestor test's answer at a machine that differs from the
start only in control, or a gate. -/
theorem caseEq_cond {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {t cn : String} {k : ObjId}
    (hm : StateOk κ Γ I m) (hnamed : classNamed? m.heap cn = some k)
    (hlex : Interp.lexicalConstant m cn = some (.ref k)) (hfree : nameFreeN κ "===" = true) :
    RunWith m (evalFrom m (.send (some (.const cn)) "===" [.var .lvar t] none)) Γ .bool κ I
      (fun w n => w = .bool (isA m.heap (m.getLocal t) k) ∧ ∃ c ks, n = reCtl m c ks) := by
  let v := m.getLocal t
  let k₁ : Kont := .recvK "===" [toRuby (.var .lvar t)] .none .explicit
  let k₂ : Kont := .argsK (.ref k) .explicit "===" [] [] .none
  apply RunWith.step (answerPoint_evalFrom _ _)
    (show Interp.stepFn _ = .next (pushK [k₁] (evalFrom m (.const cn))) from rfl)
  have hconst : Interp.stepFn (pushK [k₁] (evalFrom m (.const cn))) =
      .next (deliverA (.val (.ref k)) m [k₁]) := by
    have hl : Interp.lexicalConstant (pushK [k₁] (evalFrom m (.const cn))) cn = some (.ref k) := hlex
    have := step_lit_ctl (m := pushK [k₁] (evalFrom m (.const cn))) (e := .const cn) (w := .ref k) rfl
      (by simp [toRuby, Interp.evalExpr, hl])
    simpa only [pushK, evalFrom, deliverA, Answer.ctl, reCtl, List.nil_append] using this
  apply RunWith.step (by rfl) hconst
  apply RunWith.step (by rfl) (recv_one_step m (.ref k) "===" (.var .lvar t) rfl)
  have hread : Interp.stepFn (pushK [k₂] (evalFrom m (.var .lvar t))) =
      .next (deliverA (.val v) m [k₂]) := by
    simpa only [pushK, evalFrom, deliverA, Answer.ctl, reCtl, getLocal_reCtl, List.nil_append] using
      step_var_ctl (m := pushK [k₂] (evalFrom m (.var .lvar t))) (x := t) rfl
  apply RunWith.step (by rfl) hread
  let M := deliverA (.val v) m []
  have hM : StateOk κ Γ I M := StateOk_deliverA hm
  have hinv : Interp.stepFn (deliverA (.val v) m [k₂]) =
      Interp.invoke M (.ref k) .explicit "===" [v] none [] := rfl
  have hk : (M.heap.classPayload? k).isSome = true := by
    have hk := hnamed
    change (m.heap.classPayload? k).isSome = true
    unfold classNamed? at hk
    split at hk
    · split at hk
      · cases hk; assumption
      · cases hk
    · cases hk
  obtain ⟨hfound, hex⟩ := hM.clsQuery "===" "Module#===" (by simp [clsQueryBuiltins]) hfree
    (classOf M.heap (.ref k)) (.inr (.inr ⟨k, hk, rfl⟩))
  obtain ⟨⟨owner, md⟩, hl⟩ := Option.isSome_iff_exists.mp hex
  obtain ⟨hb, hu, hvis, hpre, hsh⟩ := hfound owner md hl
  have hdisp : Interp.invoke M (.ref k) .explicit "===" [v] none [] =
      builtinStep (Builtins.run "Module#===" (.ref k) [v] M) := by
    rw [invoke_caseEq_plain]
    exact invokeDispatch_builtin (owner := owner) (md := md)
      (by rw [lookup_eq_methodOn]; exact hl) hb hu hvis hpre hsh
      (caseEq_deferTwin _ _ _) (by rfl)
  rcases caseEq_run M v k hk with h | ⟨msg, h⟩
  · apply RunWith.step (by rfl) (hinv.trans (hdisp.trans (by rw [h]; rfl)))
    apply RunWith.answer (a := .val (.bool (isA M.heap v k))) (m := M)
      (fun v n c ks hp => ⟨hp.1, by
        obtain ⟨c', ks', rfl⟩ := hp.2
        exact ⟨c, ks, rfl⟩⟩)
    exact ⟨⟨Framed_reCtl m _ [], by simp [AnsOk, denM, isBoolV], fun _ _ => hM⟩,
      fun v hv => by cases hv; exact ⟨rfl, _, _, rfl⟩⟩
  · exact RunWith.unsupported (by rfl) (hinv.trans (hdisp.trans (by rw [h]; rfl)))

#print axioms caseEq_cond

/-- Refine an alias binding: the temporary still names `x`'s value. -/
theorem envOk_refine_alias {Γ : Env} {t x : String} {τ σ : Ty} {m : Machine} (h : EnvOk Γ m)
    (ht : envGet? Γ t = some τ) (hσ : denM σ m (m.getLocal t))
    (heq : m.getLocal t = m.getLocal x) : EnvOk (envSet Γ t (.sameAs x σ)) m := by
  refine ⟨?_, ?_⟩
  · intro y ρ hy
    by_cases hyt : y = t
    · subst hyt
      rw [envGet?_envSet_self] at hy
      cases hy
      exact ⟨hσ, fun z ρ' he => by cases he; exact heq⟩
    · rw [envGet?_envSet_ne _ _ _ _ hyt] at hy
      exact h.1 y ρ hy
  · intro y hy
    by_cases hyt : y = t
    · subst hyt; rw [envGet?_envSet_self] at hy; cases hy
    · rw [envGet?_envSet_ne _ _ _ _ hyt] at hy
      exact h.2 y hy

theorem SemSafeCtxA.ifCaseEq {κ κ' : Ctx} {Γ Γ₁ Γ₂ : Env} {I I' : Ty} {t x cn : String}
    {ρ τ₁ τ₂ : Ty} {th el : Ratchet.Expr}
    (ht : envGet? Γ t = some (.sameAs x ρ)) (hx : envGet? Γ x = some ρ)
    (hg : ifIsAB κ ρ cn = true) (hfree3 : nameFreeN κ "===" = true)
    (hth : SemSafeCtxA κ (envSet (envSet Γ x (isATy κ.classes κ.wholeCls cn ρ)) t
      (.sameAs x (isATy κ.classes κ.wholeCls cn ρ))) I th τ₁ κ' Γ₁ I')
    (hel : SemSafeCtxA κ (envSet (envSet Γ x (notATy κ.classes κ.wholeCls cn ρ)) t
      (.sameAs x (notATy κ.classes κ.wholeCls cn ρ))) I el τ₂ κ' Γ₂ I') :
    SemSafeCtxA κ Γ I (.if' (.send (some (.const cn)) "===" [.var .lvar t] none) th (some el))
      (joinT τ₁ τ₂) κ' (joinEnv Γ₁ Γ₂) I' := by
  simp only [ifIsAB, Bool.and_eq_true, Bool.not_eq_true'] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hrecv, hcls⟩, hcf⟩, hbound⟩, hfree⟩, hTfo⟩, hTal⟩, hFfo⟩, hFal⟩ := hg
  have hne : t ≠ x := by
    rintro rfl
    rw [ht] at hx
    have := Option.some.inj hx
    rw [← this] at hrecv
    simp [isARecvB, isALeafB] at hrecv
  intro m hm
  let k : Kont := .ifK (toRuby th) (some (toRuby el))
  obtain ⟨c, hnamed, hlex⟩ := isA_class_named hm hcf hcls
  have halias : m.getLocal t = m.getLocal x := (hm.env.1 t _ ht).2 x ρ rfl
  have hv0 : denM ρ m (m.getLocal t) := (hm.env.1 t _ ht).1
  obtain ⟨_, hT, hF⟩ := recv_facts hm hcf hbound hfree hnamed ρ _ hrecv hv0
  apply RunSpec.step (answerPoint_evalFrom _ _)
    (show Interp.stepFn _ = .next (pushK [k] (evalFrom m
      (.send (some (.const cn)) "===" [.var .lvar t] none))) from rfl)
  apply (caseEq_cond hm hnamed hlex hfree3).bindSpec hm.rootClean
    (by intro c hc; simp at hc; subst hc; rfl)
  intro a n hr
  cases a with
  | esc j =>
    apply RunSpec.step (by rfl)
      (show Interp.stepFn _ = .next (deliverA (.esc j) n []) from by cases j <;> rfl)
    exact RunSpec.answer ⟨hr.1.1, hr.1.2.1, fun _ hv => by cases hv⟩
  | val w =>
    obtain ⟨hw, c', ks', hre⟩ := hr.2 w rfl
    subst hw
    have hloc : n.getLocal t = m.getLocal t := by rw [hre]; exact getLocal_reCtl m _ _ t
    have hlocx : n.getLocal x = m.getLocal t := by
      rw [hre, halias]; exact getLocal_reCtl m _ _ x
    have hn : StateOk κ Γ I n := hr.1.2.2 _ rfl
    have hbranch : Interp.stepFn (deliverA (.val (.bool (isA m.heap (m.getLocal t) c))) n [k]) =
        .next (evalFrom n (if isA m.heap (m.getLocal t) c then th else el)) := by
      simp only [Interp.stepFn, deliverA, Answer.ctl, Interp.applyKont, k]
      cases hb' : isA m.heap (m.getLocal t) c <;> simp [Value.truthy, Interp.withCtl, evalFrom]
    apply RunSpec.step (by rfl) hbranch
    apply RunSpec.rebase _ hr.1.1
    have henv : ∀ σ, isAliasTy σ = false → denM σ n (m.getLocal t) →
        EnvOk (envSet (envSet Γ x σ) t (.sameAs x σ)) n := by
      intro σ hal hd
      have h1 : EnvOk (envSet Γ x σ) n := envOk_refine hn.env hx (by rw [hlocx]; exact hd) hal
      exact envOk_refine_alias h1 (by rw [envGet?_envSet_ne _ _ _ _ hne]; exact ht)
        (by rw [hloc]; exact hd) (by rw [hloc, hlocx])
    cases hb' : isA m.heap (m.getLocal t) c
    · have hs : StateOk κ _ I n :=
        { hn with env := henv _ hFal (hr.1.1.firstOrder _ hFfo _ (hF hb')) }
      simpa only [Bool.false_eq_true, ite_false] using
        (hel.weaken (fun _ _ hm hd => ⟨StateOk_joinEnv false hm, denM_joinT_right hd⟩)) n hs
    · have hs : StateOk κ _ I n :=
        { hn with env := henv _ hTal (hr.1.1.firstOrder _ hTfo _ (hT hb')) }
      simpa only [ite_true] using
        (hth.weaken (fun _ _ hm hd => ⟨StateOk_joinEnv true hm, denM_joinT_left hd⟩)) n hs

#print axioms SemSafeCtxA.ifCaseEq
end Ratchet.Denote.Typed
