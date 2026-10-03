import Denote.Rules.Expr.BranchNilQueryStr
import Denote.Sem.Class.BuiltinBases
import Denote.Rules.Primitive.Primitive

/-! `if x.is_a?(C)` on an Integer/String union local, with `C` a core class name the
context has not rebound. The native Object#is_a? answers the ancestor test, which the
builtin chains decide in both directions. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

/-- A core chain's head names its boot class, and the read resolves there. -/
theorem core_const_lookup {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {base : ObjId}
    {ch : List String} {cn : String} (hm : StateOk κ Γ I m) (hcf : coreConstFreeN κ = true)
    (hb : (base, ch) ∈ builtinBases) (hh : ch.head? = some cn) :
    classNamed? m.heap cn = some base ∧ Interp.lexicalConstant m cn = some (.ref base) := by
  have hn := ((hm.baseChains base ch hb).1 hcf).1 cn hh
  refine ⟨hn, ?_⟩
  have hl : constLookup m.heap cn = some (.ref base) := by
    have ho := classNamed_constOwn hn
    cases hp : m.heap.classPayload? Boot.objectId <;> simpa [constOwn, constLookup, hp] using ho
  exact (hm.constScope cn).trans hl

theorem core_isA_self {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {base : ObjId}
    {ch : List String} {cn : String} (hm : StateOk κ Γ I m) (hcf : coreConstFreeN κ = true)
    (hb : (base, ch) ∈ builtinBases) (hh : ch.head? = some cn) :
    (ancestors m.heap base).contains base = true := by
  obtain ⟨j, hj, hc⟩ := ((hm.baseChains base ch hb).1 hcf).2 cn (List.mem_of_mem_head? hh)
  rw [((hm.baseChains base ch hb).1 hcf).1 cn hh] at hj
  cases hj
  exact hc

theorem core_isA_other {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {base k : ObjId}
    {ch : List String} {cn : String} (hm : StateOk κ Γ I m)
    (hb : (base, ch) ∈ builtinBases) (hok : isANoOk κ.wholeCls ch = true)
    (hbound : κ.boundConsts.contains cn = false) (hn : classNamed? m.heap cn = some k)
    (hnot : cn ∉ ch) : (ancestors m.heap base).contains k = false := by
  cases hc : (ancestors m.heap base).contains k
  · rfl
  · exact absurd (((hm.baseChains base ch hb).2 hok).1 cn k hbound hn hc) hnot

theorem isA_run (m : Machine) (recv : Value) (k : ObjId)
    (hk : (m.heap.classPayload? k).isSome = true) :
    Builtins.run "Object#is_a?" recv [.ref k] m = .ok (.bool (isA m.heap recv k)) m ∨
      ∃ msg, Builtins.run "Object#is_a?" recv [.ref k] m = .unsupported msg := by
  have hq : ("Object#is_a?".endsWith "#==" || "Object#is_a?".endsWith "#eql?" ||
      "Object#is_a?".endsWith "#!=" || Builtins.pureEqualityBids.contains "Object#is_a?") = false := by
    decide +kernel
  simp only [Builtins.run]
  split
  · exact .inr ⟨_, rfl⟩
  · simp only [hq, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    left
    change Builtins.runObjects "Object#is_a?" recv [.ref k] m = _
    simp [Builtins.runObjects, hk]

/-- `x.is_a?(C)` answers the ancestor test at an unchanged local, or gates. -/
theorem isA_cond {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {x cn : String} {base : ObjId}
    {ch : List String} (hm : StateOk κ Γ I m) (hcf : coreConstFreeN κ = true)
    (hb : (base, ch) ∈ builtinBases) (hh : ch.head? = some cn)
    (hv : (∃ i, m.getLocal x = .int i) ∨ ∃ o s, m.getLocal x = .ref o ∧
      classOf m.heap (.ref o) = Boot.stringId ∧ (m.heap.get o).payload = .str s)
    (hfree : nameFreeN κ "is_a?" = true) :
    RunWith m (evalFrom m (.send (some (.var .lvar x)) "is_a?" [.const cn] none)) Γ .bool κ I
      (fun w n => w = .bool (isA m.heap (m.getLocal x) base) ∧ n.getLocal x = m.getLocal x) := by
  obtain ⟨hnamed, hlex⟩ := core_const_lookup hm hcf hb hh
  let k₁ : Kont := .recvK "is_a?" [toRuby (.const cn)] .none .explicit
  let vx := m.getLocal x
  let k₂ : Kont := .argsK vx .explicit "is_a?" [] [] .none
  apply RunWith.step (answerPoint_evalFrom _ _)
    (show Interp.stepFn _ = .next (pushK [k₁] (evalFrom m (.var .lvar x))) from rfl)
  apply RunWith.step (by rfl) (show Interp.stepFn _ = .next (deliverA (.val vx) m [k₁]) from by
    simpa only [pushK, evalFrom, deliverA, Answer.ctl, reCtl, getLocal_reCtl, List.nil_append] using
      step_var_ctl (m := pushK [k₁] (evalFrom m (.var .lvar x))) (x := x) rfl)
  apply RunWith.step (by rfl) (recv_one_step m vx "is_a?" (.const cn) rfl)
  have hconst : Interp.stepFn (pushK [k₂] (evalFrom m (.const cn))) =
      .next (deliverA (.val (.ref base)) m [k₂]) := by
    have hl : Interp.lexicalConstant (pushK [k₂] (evalFrom m (.const cn))) cn = some (.ref base) := hlex
    have := step_lit_ctl (m := pushK [k₂] (evalFrom m (.const cn))) (e := .const cn) (w := .ref base) rfl
      (by simp [toRuby, Interp.evalExpr, hl])
    simpa only [pushK, evalFrom, deliverA, Answer.ctl, reCtl, List.nil_append] using this
  apply RunWith.step (by rfl) hconst
  let M := deliverA (.val (.ref base)) m []
  have hM : StateOk κ Γ I M := StateOk_deliverA hm
  have hinv : Interp.stepFn (deliverA (.val (.ref base)) m [k₂]) =
      Interp.invoke M vx .explicit "is_a?" [.ref base] none [] := rfl
  have hk : (M.heap.classPayload? base).isSome = true := by
    have hk := hnamed
    change (m.heap.classPayload? base).isSome = true
    unfold classNamed? at hk
    split at hk
    · split at hk
      · cases hk; assumption
      · cases hk
    · cases hk
  have hinv' : Interp.invoke M vx .explicit "is_a?" [.ref base] none [] =
      builtinStep (Builtins.run "Object#is_a?" vx [.ref base] M) := by
    rcases hv with ⟨i, hi⟩ | ⟨o, s, hi, hc, hs⟩
    · change Interp.invoke M (m.getLocal x) _ _ _ _ _ = builtinStep (Builtins.run _ (m.getLocal x) _ _)
      rw [hi]
      exact primitive_invoke (bid := "Object#is_a?") (k := Boot.integerId) hM
        (by simp [primitiveMethods]) rfl (by rfl) (by intro o ho; cases ho)
        (by simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
          nativeReal, rationalPayload?, complexPayload?, Builtins.toAryDefer?,
          Builtins.strCmpDefer?, Builtins.strCmpTwin?, Builtins.coerceTwin?]) (by rfl) hfree
    · change Interp.invoke M (m.getLocal x) _ _ _ _ _ = builtinStep (Builtins.run _ (m.getLocal x) _ _)
      rw [hi]
      exact primitive_invoke (bid := "Object#is_a?") (k := Boot.stringId) hM
        (by simp [primitiveMethods]) hc (by rfl) (by intro o' ho'; cases ho'; exact ⟨s, hs⟩)
        (by simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
          nativeReal, rationalPayload?, complexPayload?, Builtins.toAryDefer?,
          Builtins.strCmpDefer?, Builtins.strCmpTwin?, Builtins.coerceTwin?, hs]) (by rfl) hfree
  rcases isA_run M vx base hk with h | ⟨msg, h⟩
  · apply RunWith.step (by rfl) (hinv.trans (hinv'.trans (by rw [h]; rfl)))
    apply RunWith.answer (a := .val (.bool (isA M.heap vx base))) (m := M)
      (fun v n c ks hp => ⟨hp.1, by rw [getLocal_reCtl]; exact hp.2⟩)
    exact ⟨⟨Framed_reCtl m _ [], by simp [AnsOk, denM, isBoolV], fun _ _ => hM⟩,
      fun v hv => by cases hv; exact ⟨rfl, getLocal_reCtl m _ [] x⟩⟩
  · exact RunWith.unsupported (by rfl) (hinv.trans (hinv'.trans (by rw [h]; rfl)))

#print axioms isA_cond
theorem SemSafeCtxA.ifIsAUnion {κ κ' : Ctx} {Γ Γ₁ Γ₂ : Env} {I I' : Ty} {x cn : String}
    {σ τ tT tF τ₁ τ₂ : Ty} {t e : Ratchet.Expr}
    (hx : envGet? Γ x = some (.union σ τ))
    (hsides : (σ = .int ∧ τ = .cls "String") ∨ (σ = .cls "String" ∧ τ = .int))
    (hcase : (cn = "Integer" ∧ tT = .int ∧ tF = .cls "String") ∨
      (cn = "String" ∧ tT = .cls "String" ∧ tF = .int))
    (hcf : coreConstFreeN κ = true) (hfree : nameFreeN κ "is_a?" = true)
    (hokI : isANoOk κ.wholeCls intChain = true) (hokS : isANoOk κ.wholeCls strChain = true)
    (ht : SemSafeCtxA κ (envSet Γ x tT) I t τ₁ κ' Γ₁ I')
    (he : SemSafeCtxA κ (envSet Γ x tF) I e τ₂ κ' Γ₂ I') :
    SemSafeCtxA κ Γ I (.if' (.send (some (.var .lvar x)) "is_a?" [.const cn] none) t (some e))
      (joinT τ₁ τ₂) κ' (joinEnv Γ₁ Γ₂) I' := by
  intro m hm
  let k : Kont := .ifK (toRuby t) (some (toRuby e))
  have hbI : (Boot.integerId, intChain) ∈ builtinBases := by simp [builtinBases, intChain]
  have hbS : (Boot.stringId, strChain) ∈ builtinBases := by simp [builtinBases, strChain]
  have hboundI : κ.boundConsts.contains "Integer" = false := by
    have := List.all_eq_true.mp hcf "Integer" (by simp [coreChainNames])
    simpa using this
  have hboundS : κ.boundConsts.contains "String" = false := by
    have := List.all_eq_true.mp hcf "String" (by simp [coreChainNames])
    simpa using this
  obtain ⟨hnI, _⟩ := core_const_lookup hm hcf hbI rfl
  obtain ⟨hnS, _⟩ := core_const_lookup hm hcf hbS rfl
  have hv0 : denM (.union σ τ) m (m.getLocal x) := by
    simpa [stripAlias] using (hm.env.1 x _ hx).1
  -- the value is an Integer or a String instance, and its denotation follows
  have hcls : (∃ i, m.getLocal x = .int i) ∨ ∃ o s, m.getLocal x = .ref o ∧
      classOf m.heap (.ref o) = Boot.stringId ∧ (m.heap.get o).payload = .str s := by
    have hv1 : denM .int m (m.getLocal x) ∨ denM (.cls "String") m (m.getLocal x) := by
      rcases hsides with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [denM] at hv0; exact hv0
      · rw [denM] at hv0; exact hv0.symm
    rcases hv1 with h | h
    · left; cases hg : m.getLocal x <;> rw [hg] at h <;> simp_all [denM, isIntV]
    · right
      obtain ⟨o, s, ho, hs⟩ := string_payload hm h hokS
      exact ⟨o, s, ho, by rw [← ho]; exact string_class hm h hokS, hs⟩
  -- the base the condition tests, with both answers' consequences
  obtain ⟨base, ch, hb, hh, hT, hF⟩ : ∃ base ch, (base, ch) ∈ builtinBases ∧ ch.head? = some cn ∧
      (isA m.heap (m.getLocal x) base = true → denM tT m (m.getLocal x)) ∧
      (isA m.heap (m.getLocal x) base = false → denM tF m (m.getLocal x)) := by
    have hIntIsA : ∀ i, isA m.heap (.int i) Boot.integerId = true := fun i =>
      core_isA_self hm hcf hbI rfl
    have hIntNotS : ∀ i, isA m.heap (.int i) Boot.stringId = false := fun i =>
      core_isA_other hm hbI hokI hboundS hnS (by decide)
    have hStrIsS : ∀ o, classOf m.heap (.ref o) = Boot.stringId →
        isA m.heap (.ref o) Boot.stringId = true := fun o hc => by
      simp only [isA, hc]; exact core_isA_self hm hcf hbS rfl
    have hStrNotI : ∀ o, classOf m.heap (.ref o) = Boot.stringId →
        isA m.heap (.ref o) Boot.integerId = false := fun o hc => by
      simp only [isA, hc]; exact core_isA_other hm hbS hokS hboundI hnI (by decide)
    have hdenS : ∀ o s, m.getLocal x = .ref o → classOf m.heap (.ref o) = Boot.stringId →
        (m.heap.get o).payload = .str s → denM (.cls "String") m (m.getLocal x) := by
      intro o s ho hc _
      rw [ho]
      simp only [denM, isAName, hm.core.stringNamed, isA]
      rw [hc]; exact hm.core.stringSelf
    rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · refine ⟨Boot.integerId, intChain, hbI, rfl, fun h => ?_, fun h => ?_⟩
      · rcases hcls with ⟨i, hi⟩ | ⟨o, s, ho, hc, hs⟩
        · rw [hi]; simp [denM, isIntV]
        · rw [ho, hStrNotI o hc] at h; cases h
      · rcases hcls with ⟨i, hi⟩ | ⟨o, s, ho, hc, hs⟩
        · rw [hi, hIntIsA i] at h; cases h
        · exact hdenS o s ho hc hs
    · refine ⟨Boot.stringId, strChain, hbS, rfl, fun h => ?_, fun h => ?_⟩
      · rcases hcls with ⟨i, hi⟩ | ⟨o, s, ho, hc, hs⟩
        · rw [hi, hIntNotS i] at h; cases h
        · exact hdenS o s ho hc hs
      · rcases hcls with ⟨i, hi⟩ | ⟨o, s, ho, hc, hs⟩
        · rw [hi]; simp [denM, isIntV]
        · rw [ho, hStrIsS o hc] at h; cases h
  apply RunSpec.step (answerPoint_evalFrom _ _)
    (show Interp.stepFn _ = .next (pushK [k] (evalFrom m
      (.send (some (.var .lvar x)) "is_a?" [.const cn] none))) from rfl)
  apply (isA_cond hm hcf hb hh hcls hfree).bindSpec hm.rootClean
    (by intro c hc; simp at hc; subst hc; rfl)
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
    have hbranch : Interp.stepFn (deliverA (.val (.bool (isA m.heap (m.getLocal x) base))) n [k]) =
        .next (evalFrom n (if isA m.heap (m.getLocal x) base then t else e)) := by
      simp only [Interp.stepFn, deliverA, Answer.ctl, Interp.applyKont, k]
      cases hb' : isA m.heap (m.getLocal x) base <;> simp [Value.truthy, Interp.withCtl, evalFrom]
    apply RunSpec.step (by rfl) hbranch
    apply RunSpec.rebase _ hr.1.1
    have hFO : ∀ ρ, (ρ = .int ∨ ρ = .cls "String") → FirstOrder ρ = true := by
      intro ρ hρ; rcases hρ with rfl | rfl <;> rfl
    have hTside : tT = .int ∨ tT = .cls "String" := by
      rcases hcase with ⟨_, h, _⟩ | ⟨_, h, _⟩ <;> simp [h]
    have hFside : tF = .int ∨ tF = .cls "String" := by
      rcases hcase with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> simp [h]
    have halT : isAliasTy tT = false := by rcases hTside with h | h <;> simp [h, isAliasTy]
    have halF : isAliasTy tF = false := by rcases hFside with h | h <;> simp [h, isAliasTy]
    cases hb' : isA m.heap (m.getLocal x) base
    · have hd : denM tF n (n.getLocal x) := by
        rw [hloc]; exact hr.1.1.firstOrder _ (hFO _ hFside) _ (hF hb')
      have hs : StateOk κ (envSet Γ x tF) I n := { hn with env := envOk_refine hn.env hx hd halF }
      simpa only [Bool.false_eq_true, ite_false] using
        (he.weaken (fun _ _ hm hd => ⟨StateOk_joinEnv false hm, denM_joinT_right hd⟩)) n hs
    · have hd : denM tT n (n.getLocal x) := by
        rw [hloc]; exact hr.1.1.firstOrder _ (hFO _ hTside) _ (hT hb')
      have hs : StateOk κ (envSet Γ x tT) I n := { hn with env := envOk_refine hn.env hx hd halT }
      simpa only [ite_true] using
        (ht.weaken (fun _ _ hm hd => ⟨StateOk_joinEnv true hm, denM_joinT_left hd⟩)) n hs

#print axioms SemSafeCtxA.ifIsAUnion
end Ratchet.Denote.Typed
