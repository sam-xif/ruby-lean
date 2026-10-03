import Denote.Rules.Expr.BranchIsA

/-! General `if x.nil?` narrowing. At every admitted leaf the query is the native
NilClass#nil?/Object#nil? row, so its answer is the value's nil-ness; the branches see
`nilYesTy`/`nonNilTy`. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

/-- Native dispatch of the query with the value's nil-ness as its answer (or a gate), and
each answer placing the value in the corresponding refinement. -/
def NilFacts (m : Machine) (τ : Ty) (v : Value) : Prop :=
  (Interp.invoke m v .explicit "nil?" [] none [] =
      .next (Interp.withCtl m (.value (.bool (isNilV v)))) ∨
    ∃ msg, Interp.invoke m v .explicit "nil?" [] none [] = .unsupported msg) ∧
  (isNilV v = true → denM (nilYesTy τ) m v) ∧
  (isNilV v = false → denM (nonNilTy τ) m v)

theorem scalar_nil_run (m : Machine) (v : Value) (hv : ∀ o, v ≠ .ref o)
    (hn : isNilV v = false) :
    Builtins.run "Object#nil?" v [] m = .ok (.bool false) m := by
  cases v <;> first
    | exact absurd rfl (hv _)
    | (simp [isNilV] at hn; done)
    | (simp only [Builtins.run, List.any_cons, List.any_nil, Builtins.unrepresentableByteStr,
        Builtins.strPayload?, Builtins.complexEqualityImpure, Bool.false_or, Bool.or_false,
        Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
       rfl)

theorem nilQ_deferTwin (h : Heap) (v : Value) :
    Builtins.deferTwin? h "Object#nil?" v [] = none := by
  simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
    Builtins.toAryDefer?, Builtins.strCmpDefer?, Builtins.strCmpTwin?, Builtins.coerceTwin?]

theorem invoke_nilQ_plain (m : Machine) (o : ObjId) (site : SendSite) (args : List Value) :
    Interp.invoke m (.ref o) site "nil?" args none [] =
      Interp.invoke.invokeDispatch m (.ref o) site "nil?" args none [] := by
  rw [Interp.invoke.eq_def]
  simp only [show (("nil?" : String) == "send" || "nil?" == "public_send" || "nil?" == "__send__") = false
    from by decide, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  cases hp : (m.heap.get o).payload <;> simp
  done

theorem nil_leaf_facts {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {τ : Ty} {v : Value}
    (hm : StateOk κ Γ I m) (hfree : nameFreeN κ "nil?" = true)
    (hleaf : nilLeafB κ τ = true) (hd : denM τ m v) : NilFacts m τ v := by
  -- a non-reference scalar: Object#nil? answers false
  have scalar : ∀ k, classOf m.heap v = k → (k, "nil?", "Object#nil?") ∈ primitiveMethods →
      (∀ o, v ≠ .ref o) → isNilV v = false → nonNilTy τ = τ → NilFacts m τ v := by
    intro k hc hrow href hn hT
    refine ⟨.inl ?_, ⟨fun h => (by rw [hn] at h; cases h), fun _ => (by rw [hT]; exact hd)⟩⟩
    rw [primitive_invoke (bid := "Object#nil?") (k := k) hm hrow hc (by rfl)
      (by intro o ho; exact absurd ho (href o)) (nilQ_deferTwin _ _) (by rfl) hfree,
      scalar_nil_run m v href hn, hn]
    rfl
  -- a reference: Object#nil? answers false or gates
  have refd : ∀ o, v = .ref o →
      Interp.invoke m (.ref o) .explicit "nil?" [] none [] =
        builtinStep (Builtins.run "Object#nil?" (.ref o) [] m) →
      nonNilTy τ = τ → NilFacts m τ v := by
    intro o hv hinv hT
    subst hv
    refine ⟨?_, ⟨fun h => (by simp [isNilV] at h), fun _ => (by rw [hT]; exact hd)⟩⟩
    rcases str_nil_run m o with h | ⟨msg, h⟩
    · left; rw [hinv, h]; rfl
    · right; exact ⟨msg, by rw [hinv, h]; rfl⟩
  cases τ with
  | int =>
    cases v <;> simp [denM, isIntV] at hd
    exact scalar Boot.integerId rfl (by simp [primitiveMethods]) (by intro o ho; cases ho) rfl rfl
  | float =>
    cases v <;> simp [denM, isFltV] at hd
    exact scalar Boot.floatId rfl (by simp [primitiveMethods]) (by intro o ho; cases ho) rfl rfl
  | sym =>
    cases v <;> simp [denM, isSymV] at hd
    exact scalar Boot.symbolId rfl (by simp [primitiveMethods]) (by intro o ho; cases ho) rfl rfl
  | nilT =>
    cases v <;> simp [denM, isNilV] at hd
    refine ⟨.inl ?_, ⟨fun _ => (by simp [nilYesTy, denM, isNilV]), fun h => (by simp [isNilV] at h)⟩⟩
    rw [primitive_invoke (bid := "NilClass#nil?") (k := Boot.nilClassId) hm
      (by simp [primitiveMethods]) rfl (by rfl) (by intro o ho; cases ho) (by rfl) (by rfl) hfree,
      nil_nil_run]
    rfl
  | cls n =>
    have hn : n = "String" := by
      simp only [nilLeafB] at hleaf
      split at hleaf <;> simp_all
    subst hn
    have hg : isANoOk κ.wholeCls (["String", "Comparable"] ++ rootAncestors) = true := by
      simpa [nilLeafB] using hleaf
    obtain ⟨o, s, ho, hs⟩ := string_payload hm hd hg
    have hc : classOf m.heap (.ref o) = Boot.stringId := by rw [← ho]; exact string_class hm hd hg
    exact refd o ho (primitive_invoke (bid := "Object#nil?") (k := Boot.stringId) hm
      (by simp [primitiveMethods]) hc (by rfl) (by intro o' ho'; cases ho'; exact ⟨s, hs⟩)
      (nilQ_deferTwin _ _) (by rfl) hfree) rfl
  | inst n J =>
    cases hg : clsGet? κ.classes n with
    | none => simp [nilLeafB, hg] at hleaf
    | some c =>
    simp only [nilLeafB, hg, Bool.and_eq_true, Bool.not_eq_true'] at hleaf
    obtain ⟨hkind, hnd⟩ := hleaf
    have hcm : c ∈ κ.classes := List.mem_of_find?_eq_some hg
    have hcn : c.name = n := by simpa using List.find?_some hg
    subst hcn
    have hex : isExactInst m.heap v c.name = true := by rw [denM] at hd; exact hd.1
    unfold isExactInst at hex
    cases hr : classNamed? m.heap c.name with
    | none => simp [hr] at hex
    | some r =>
    cases v with
    | ref o =>
      simp only [hr, Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none, beq_iff_eq] at hex
      obtain ⟨⟨_, heig⟩, hkl⟩ := hex
      have hcls : classOf m.heap (.ref o) = r := by simp [classOf, heig, hkl]
      obtain ⟨owner, md, hl, hb, _, _, _, _⟩ := primitive_lookup hm (k := Boot.objectId)
        (name := "nil?") (bid := "Object#nil?") (by simp [primitiveMethods]) hfree
      have hfound : Interp.methodOn m.heap r "nil?" = some (owner, md) :=
        (hm.methodOn_root_of_absent hcm hr hkind hnd).trans hl
      obtain ⟨_, hu, hvis, hpre, hsh⟩ := (hm.nilQuery hfree r).1 owner md hfound
      exact refd o rfl (by
        rw [invoke_nilQ_plain]
        exact invokeDispatch_builtin (owner := owner) (md := md)
          (by rw [lookup_eq_methodOn, hcls]; exact hfound) hb hu hvis hpre
          (by simpa only [hcls] using hsh) (nilQ_deferTwin _ _) (by rfl)) rfl
    | _ => simp [hr] at hex
  | _ => simp [nilLeafB] at hleaf

theorem nil_recv_facts {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) (hfree : nameFreeN κ "nil?" = true) :
    ∀ (ρ : Ty) (v : Value), nilRecvB κ ρ = true → denM ρ m v → NilFacts m ρ v := by
  intro ρ
  induction ρ with
  | union σ τ ihσ ihτ =>
    intro v hr hd
    simp only [nilRecvB, Bool.and_eq_true] at hr
    rw [denM] at hd
    rcases hd with hd | hd
    · obtain ⟨hdisp, hT, hF⟩ := ihσ v hr.1 hd
      exact ⟨hdisp, fun h => denM_joinT_left (hT h), fun h => denM_joinT_left (hF h)⟩
    · obtain ⟨hdisp, hT, hF⟩ := ihτ v hr.2 hd
      exact ⟨hdisp, fun h => denM_joinT_right (hT h), fun h => denM_joinT_right (hF h)⟩
  | nilable ρ ih =>
    intro v hr hd
    simp only [nilRecvB] at hr
    rw [denM] at hd
    rcases hd with hd | hd
    · obtain ⟨hdisp, _, _⟩ := nil_leaf_facts (τ := .nilT) hm hfree rfl (by simpa [denM] using hd)
      exact ⟨hdisp, fun _ => (by simpa [nilYesTy, denM] using hd), fun h => (by rw [hd] at h; cases h)⟩
    · obtain ⟨hdisp, _, hF⟩ := ih v hr hd
      exact ⟨hdisp, fun h => (by simpa [nilYesTy, denM] using h), hF⟩
  | _ => intro v hr hd; exact nil_leaf_facts hm hfree (by simpa [nilRecvB] using hr) hd

#print axioms nil_recv_facts

theorem SemSafeCtxA.ifNilQuery {κ κ' : Ctx} {Γ Γ₁ Γ₂ : Env} {I I' : Ty} {x : String}
    {ρ τ₁ τ₂ : Ty} {t e : Ratchet.Expr}
    (hx : envGet? Γ x = some ρ) (hg : ifNilQB κ ρ = true)
    (ht : SemSafeCtxA κ (envSet Γ x (nilYesTy ρ)) I t τ₁ κ' Γ₁ I')
    (he : SemSafeCtxA κ (envSet Γ x (nonNilTy ρ)) I e τ₂ κ' Γ₂ I') :
    SemSafeCtxA κ Γ I (.if' (.send (some (.var .lvar x)) "nil?" [] none) t (some e))
      (joinT τ₁ τ₂) κ' (joinEnv Γ₁ Γ₂) I' := by
  simp only [ifNilQB, Bool.and_eq_true, Bool.not_eq_true'] at hg
  obtain ⟨⟨⟨hrecv, hfree⟩, hTal⟩, hFal⟩ := hg
  intro m hm
  let k : Kont := .ifK (toRuby t) (some (toRuby e))
  let k₁ : Kont := .recvK "nil?" [] .none .explicit
  let v := m.getLocal x
  have hρ : stripAlias ρ = ρ := by
    cases ρ <;> simp_all [stripAlias, nilRecvB, nilLeafB]
  have hv0 : denM ρ m v := by
    have := (hm.env.1 x _ hx).1
    rwa [hρ] at this
  obtain ⟨_, hT, hF⟩ := nil_recv_facts hm hfree ρ _ hrecv hv0
  let M := deliverA (.val v) m []
  have hM : StateOk κ Γ I M := StateOk_deliverA hm
  obtain ⟨hdisp, _, _⟩ := nil_recv_facts hM hfree ρ v hrecv (denM_deliverA.mpr hv0)
  apply RunSpec.step (answerPoint_evalFrom _ _)
    (show Interp.stepFn _ = .next (pushK [k] (evalFrom m
      (.send (some (.var .lvar x)) "nil?" [] none))) from rfl)
  have hcond : RunWith m (evalFrom m (.send (some (.var .lvar x)) "nil?" [] none)) Γ .bool κ I
      (fun w n => w = .bool (isNilV v) ∧ ∃ c ks, n = reCtl m c ks) := by
    apply RunWith.step (answerPoint_evalFrom _ _)
      (show Interp.stepFn _ = .next (pushK [k₁] (evalFrom m (.var .lvar x))) from rfl)
    apply RunWith.step (by rfl) (show Interp.stepFn _ = .next (deliverA (.val v) m [k₁]) from by
      simpa only [pushK, evalFrom, deliverA, Answer.ctl, reCtl, getLocal_reCtl, List.nil_append] using
        step_var_ctl (m := pushK [k₁] (evalFrom m (.var .lvar x))) (x := x) rfl)
    have hinv : Interp.stepFn (deliverA (.val v) m [k₁]) =
        Interp.invoke M v .explicit "nil?" [] none [] := rfl
    rcases hdisp with h | ⟨msg, h⟩
    · apply RunWith.step (by rfl) (hinv.trans h)
      apply RunWith.answer (a := .val (.bool (isNilV v))) (m := M)
        (fun v n c ks hp => ⟨hp.1, by
          obtain ⟨c', ks', rfl⟩ := hp.2
          exact ⟨c, ks, rfl⟩⟩)
      exact ⟨⟨Framed_reCtl m _ [], by simp [AnsOk, denM, isBoolV], fun _ _ => hM⟩,
        fun v hv => by cases hv; exact ⟨rfl, _, _, rfl⟩⟩
    · exact RunWith.unsupported (by rfl) (hinv.trans h)
  apply hcond.bindSpec hm.rootClean (by intro c hc; simp at hc; subst hc; rfl)
  intro a n hr
  cases a with
  | esc j =>
    apply RunSpec.step (by rfl)
      (show Interp.stepFn _ = .next (deliverA (.esc j) n []) from by cases j <;> rfl)
    exact RunSpec.answer ⟨hr.1.1, hr.1.2.1, fun _ hv => by cases hv⟩
  | val w =>
    obtain ⟨hw, c', ks', hre⟩ := hr.2 w rfl
    subst hw
    have hloc : n.getLocal x = v := by rw [hre]; exact getLocal_reCtl m _ _ x
    have hn : StateOk κ Γ I n := hr.1.2.2 _ rfl
    have hbranch : Interp.stepFn (deliverA (.val (.bool (isNilV v))) n [k]) =
        .next (evalFrom n (if isNilV v then t else e)) := by
      simp only [Interp.stepFn, deliverA, Answer.ctl, Interp.applyKont, k]
      cases hb' : isNilV v <;> simp [Value.truthy, Interp.withCtl, evalFrom]
    apply RunSpec.step (by rfl) hbranch
    apply RunSpec.rebase _ hr.1.1
    cases hb' : isNilV v
    · have hd : denM (nonNilTy ρ) n (n.getLocal x) := by
        rw [hloc, hre]; exact denM_reCtl.mpr (hF hb')
      have hs : StateOk κ (envSet Γ x (nonNilTy ρ)) I n :=
        { hn with env := envOk_refine hn.env hx hd hFal }
      simpa only [Bool.false_eq_true, ite_false] using
        (he.weaken (fun _ _ hm hd => ⟨StateOk_joinEnv false hm, denM_joinT_right hd⟩)) n hs
    · have hd : denM (nilYesTy ρ) n (n.getLocal x) := by
        rw [hloc, hre]; exact denM_reCtl.mpr (hT hb')
      have hs : StateOk κ (envSet Γ x (nilYesTy ρ)) I n :=
        { hn with env := envOk_refine hn.env hx hd hTal }
      simpa only [ite_true] using
        (ht.weaken (fun _ _ hm hd => ⟨StateOk_joinEnv true hm, denM_joinT_left hd⟩)) n hs

#print axioms SemSafeCtxA.ifNilQuery
end Ratchet.Denote.Typed
