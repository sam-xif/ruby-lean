import Denote.Rules.Expr.BranchNilQueryStr
import Denote.Sem.Class.BuiltinBases
import Denote.Rules.Primitive.Primitive
import Denote.Sem.Names.RootLookup

/-! `if x.is_a?(C)` on an Integer/String union local, with `C` a core class name the
context has not rebound. The native Object#is_a? answers the ancestor test, which the
builtin chains decide in both directions. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

/-- Every core chain name sits in some builtin chain. -/
theorem coreChainName_base {cn : String} (h : cn ∈ coreChainNames) :
    ∃ base ch, (base, ch) ∈ builtinBases ∧ cn ∈ ch := by
  have hall : coreChainNames.all (fun n => builtinBases.any (fun p => p.2.contains n)) = true := by
    decide
  have := List.all_eq_true.mp hall cn h
  obtain ⟨p, hp, hc⟩ := List.any_eq_true.mp this
  exact ⟨p.1, p.2, hp, by simpa using hc⟩

/-- The tested name resolves to a class object, and the constant read finds it. -/
theorem isA_class_named {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {cn : String}
    (hm : StateOk κ Γ I m) (hcf : coreConstFreeN κ = true) (hcls : isAClassB κ cn = true) :
    ∃ k, classNamed? m.heap cn = some k ∧ Interp.lexicalConstant m cn = some (.ref k) := by
  have hnamed : ∃ k, classNamed? m.heap cn = some k := by
    simp only [isAClassB, Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true,
      beq_iff_eq] at hcls
    rcases hcls with h | ⟨c, hc, rfl⟩
    · obtain ⟨base, ch, hb, hin⟩ := coreChainName_base h
      obtain ⟨j, hj, _⟩ := ((hm.baseChains base ch hb).1 hcf).2 cn hin
      exact ⟨j, hj⟩
    · obtain ⟨k, hk, _⟩ := hm.classes c hc
      exact ⟨k, hk⟩
  obtain ⟨k, hn⟩ := hnamed
  refine ⟨k, hn, ?_⟩
  have hl : constLookup m.heap cn = some (.ref k) := by
    have ho := classNamed_constOwn hn
    cases hp : m.heap.classPayload? Boot.objectId <;> simpa [constOwn, constLookup, hp] using ho
  exact (hm.constScope cn).trans hl

/-- At an undisturbed builtin chain the ancestor test is the chain's membership test. -/
theorem chain_isA {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {base k : ObjId}
    {ch : List String} {cn : String} (hm : StateOk κ Γ I m) (hcf : coreConstFreeN κ = true)
    (hb : (base, ch) ∈ builtinBases) (hok : isANoOk κ.wholeCls ch = true)
    (hbound : κ.boundConsts.contains cn = false) (hn : classNamed? m.heap cn = some k) :
    (ancestors m.heap base).contains k = ch.contains cn := by
  cases hc : ch.contains cn
  · cases hx : (ancestors m.heap base).contains k
    · rfl
    · have := ((hm.baseChains base ch hb).2 hok).1 cn k hbound hn hx
      simp [this] at hc
  · obtain ⟨j, hj, hcj⟩ := ((hm.baseChains base ch hb).1 hcf).2 cn (by simpa using hc)
    rw [hn] at hj; cases hj
    exact hcj

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

/-- What the rule needs of one leaf value: native dispatch of the test, and each answer
placing the value in the corresponding refinement. -/
def IsAFacts (κ : Ctx) (m : Machine) (cn : String) (k : ObjId) (τ : Ty) (v : Value) : Prop :=
  (Interp.invoke m v .explicit "is_a?" [.ref k] none [] =
      builtinStep (Builtins.run "Object#is_a?" v [.ref k] m)) ∧
  (isA m.heap v k = true → denM (isATy κ.classes κ.wholeCls cn τ) m v) ∧
  (isA m.heap v k = false → denM (notATy κ.classes κ.wholeCls cn τ) m v)

theorem isA_deferTwin (h : Heap) (v : Value) (k : ObjId) :
    Builtins.deferTwin? h "Object#is_a?" v [.ref k] = none := by
  simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
    Builtins.toAryDefer?, Builtins.strCmpDefer?, Builtins.strCmpTwin?, Builtins.coerceTwin?]

/-- A scalar builtin leaf: the value has exactly its builtin class. -/
theorem builtin_leaf_facts {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {τ : Ty} {v : Value}
    {cn : String} {k : ObjId} (hm : StateOk κ Γ I m) (hcf : coreConstFreeN κ = true)
    (hbound : κ.boundConsts.contains cn = false) (hfree : nameFreeN κ "is_a?" = true)
    (hleaf : isALeafB κ τ = true) (hni : ∀ n J, τ ≠ .inst n J)
    (hd : denM τ m v) (hk : classNamed? m.heap cn = some k) : IsAFacts κ m cn k τ v := by
  have fin : ∀ base ch, (base, ch) ∈ builtinBases → isANoOk κ.wholeCls ch = true →
      classOf m.heap v = base → (base, "is_a?", "Object#is_a?") ∈ primitiveMethods →
      (∀ o, v = .ref o → ∃ s, (m.heap.get o).payload = .str s) →
      isATy κ.classes κ.wholeCls cn τ = (if ch.contains cn then τ else .never) →
      notATy κ.classes κ.wholeCls cn τ = (if ch.contains cn then .never else τ) →
      IsAFacts κ m cn k τ v := by
    intro base ch hb hok hc hrow hpay hT hF
    have hisA : isA m.heap v k = ch.contains cn := by
      simp only [isA, hc]; exact chain_isA hm hcf hb hok hbound hk
    refine ⟨primitive_invoke (bid := "Object#is_a?") (k := base) hm hrow hc (by rfl) hpay
      (isA_deferTwin _ _ _) (by rfl) hfree, fun h => ?_, fun h => ?_⟩
    · rw [hT, ← hisA, h]; exact hd
    · rw [hF, ← hisA, h]; exact hd
  cases τ with
  | int =>
    have hok : isANoOk κ.wholeCls (["Integer", "Numeric", "Comparable"] ++ rootAncestors) = true := by
      simpa [isALeafB, builtinAncestors] using hleaf
    cases v <;> simp [denM, isIntV] at hd
    exact fin Boot.integerId _ (by simp [builtinBases]) hok rfl (by simp [primitiveMethods])
      (by intro o ho; cases ho)
      (by simp only [isATy, isAAnswer, builtinAncestors, Option.bind, hok, ↓reduceIte]; split <;> simp_all)
      (by simp only [notATy, isAAnswer, builtinAncestors, Option.bind, hok, ↓reduceIte]; split <;> simp_all)
  | float =>
    have hok : isANoOk κ.wholeCls (["Float", "Numeric", "Comparable"] ++ rootAncestors) = true := by
      simpa [isALeafB, builtinAncestors] using hleaf
    cases v <;> simp [denM, isFltV] at hd
    exact fin Boot.floatId _ (by simp [builtinBases]) hok rfl (by simp [primitiveMethods])
      (by intro o ho; cases ho)
      (by simp only [isATy, isAAnswer, builtinAncestors, Option.bind, hok, ↓reduceIte]; split <;> simp_all)
      (by simp only [notATy, isAAnswer, builtinAncestors, Option.bind, hok, ↓reduceIte]; split <;> simp_all)
  | nilT =>
    have hok : isANoOk κ.wholeCls ("NilClass" :: rootAncestors) = true := by
      simpa [isALeafB, builtinAncestors] using hleaf
    cases v <;> simp [denM, isNilV] at hd
    exact fin Boot.nilClassId _ (by simp [builtinBases]) hok rfl (by simp [primitiveMethods])
      (by intro o ho; cases ho)
      (by simp only [isATy, isAAnswer, builtinAncestors, Option.bind, hok, ↓reduceIte]; split <;> simp_all)
      (by simp only [notATy, isAAnswer, builtinAncestors, Option.bind, hok, ↓reduceIte]; split <;> simp_all)
  | sym =>
    have hok : isANoOk κ.wholeCls (["Symbol", "Comparable"] ++ rootAncestors) = true := by
      simpa [isALeafB, builtinAncestors] using hleaf
    cases v <;> simp [denM, isSymV] at hd
    exact fin Boot.symbolId _ (by simp [builtinBases]) hok rfl (by simp [primitiveMethods])
      (by intro o ho; cases ho)
      (by simp only [isATy, isAAnswer, builtinAncestors, Option.bind, hok, ↓reduceIte]; split <;> simp_all)
      (by simp only [notATy, isAAnswer, builtinAncestors, Option.bind, hok, ↓reduceIte]; split <;> simp_all)
  | cls n =>
    by_cases hn : n = "String"
    · subst hn
      have hok : isANoOk κ.wholeCls (["String", "Comparable"] ++ rootAncestors) = true := by
        simpa [isALeafB, builtinAncestors] using hleaf
      obtain ⟨o, s, rfl, hs⟩ := string_payload hm hd hok
      exact fin Boot.stringId _ (by simp [builtinBases]) hok (string_class hm hd hok)
        (by simp [primitiveMethods]) (by intro o' ho'; cases ho'; exact ⟨s, hs⟩)
        (by simp only [isATy, isAAnswer, builtinAncestors, Option.bind, hok, ↓reduceIte]; split <;> simp_all)
        (by simp only [notATy, isAAnswer, builtinAncestors, Option.bind, hok, ↓reduceIte]; split <;> simp_all)
    · simp [isALeafB, hn] at hleaf
  | inst n J => exact absurd rfl (hni n J)
  | _ => simp [isALeafB] at hleaf

/-- `is_a?` has no receiver-payload special case: every reference dispatches. -/
theorem invoke_isA_plain (m : Machine) (o : ObjId) (site : SendSite) (args : List Value) :
    Interp.invoke m (.ref o) site "is_a?" args none [] =
      Interp.invoke.invokeDispatch m (.ref o) site "is_a?" args none [] := by
  rw [Interp.invoke.eq_def]
  simp only [show (("is_a?" : String) == "send" || "is_a?" == "public_send" || "is_a?" == "__send__") = false
    from by decide, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  cases hp : (m.heap.get o).payload <;> simp
  done

theorem namedChain_mem {h : Heap} {ns : List String} {ks : List ObjId} (hp : NamedChain h ns ks)
    {cn : String} (hc : cn ∈ ns) : ∃ k ∈ ks, classNamed? h cn = some k := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hc
  obtain ⟨before, k, after, rfl, _, hk, _⟩ := hp.split
  exact ⟨k, by simp, hk⟩

/-- An exact instance of a declared class that leaves `is_a?` alone: lookup falls through
to Object's native row, and the answer is the declared chain's membership test. -/
theorem inst_leaf_facts {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {n : String} {J : Ty}
    {v : Value} {cn : String} {k : ObjId} (hm : StateOk κ Γ I m)
    (hfree : nameFreeN κ "is_a?" = true) (hleaf : isALeafB κ (.inst n J) = true)
    (hd : denM (.inst n J) m v) (hk : classNamed? m.heap cn = some k) :
    IsAFacts κ m cn k (.inst n J) v := by
  -- the declared class
  cases hg : clsGet? κ.classes n with
  | none => simp [isALeafB, hg] at hleaf
  | some c =>
  simp only [isALeafB, hg, Bool.and_eq_true, Bool.not_eq_true'] at hleaf
  obtain ⟨hkind, hnd⟩ := hleaf
  have hcm : c ∈ κ.classes := List.mem_of_find?_eq_some hg
  have hcn : c.name = n := by simpa using List.find?_some hg
  subst hcn
  -- the value is an exact instance: its dispatch class is the class object
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
    -- dispatch
    obtain ⟨owner, md, hl, _, _, _, _, _⟩ := primitive_lookup hm (k := Boot.objectId)
      (name := "is_a?") (bid := "Object#is_a?") (by simp [primitiveMethods]) hfree
    have hfound : Interp.methodOn m.heap r "is_a?" = some (owner, md) :=
      (hm.methodOn_root_of_absent hcm hr hkind hnd).trans hl
    obtain ⟨hb, hu, hvis, hpre, hsh⟩ := (hm.query "is_a?" "Object#is_a?"
      (by simp [queryBuiltins]) hfree r).1 owner md hfound
    have hdisp : Interp.invoke m (.ref o) .explicit "is_a?" [.ref k] none [] =
        builtinStep (Builtins.run "Object#is_a?" (.ref o) [.ref k] m) := by
      rw [invoke_isA_plain]
      exact invokeDispatch_builtin (owner := owner) (md := md)
        (by rw [lookup_eq_methodOn, hcls]; exact hfound) hb hu
        (by simpa [queryVisibility] using hvis) hpre (by simpa only [hcls] using hsh)
        (isA_deferTwin _ _ _) (by rfl)
    -- the answer
    cases ha : ancestors? κ.classes c.name with
    | none => simp [noDeclaredSelectorB, ha] at hnd
    | some ch =>
    have hchain : NamedChain m.heap (ch ++ c.rootTail) (ancestors m.heap r) :=
      hm.classChains c hcm r hr ch ha
    have hisA : isA m.heap (.ref o) k = (ancestors m.heap r).contains k := by simp [isA, hcls]
    refine ⟨hdisp, fun h => ?_, fun h => ?_⟩
    · -- a true answer cannot be refined away
      have hT : isATy κ.classes κ.wholeCls cn (.inst c.name J) = .inst c.name J := by
        simp only [isATy, isAAnswer, hg, ha, Option.bind]
        split
        · rename_i hfalse
          split at hfalse
          · cases hfalse
          · split at hfalse
            · rename_i hnot _
              rw [hisA] at h
              obtain ⟨cn', hcn', hnamed'⟩ := hchain.cover (by simpa using h)
              have := hm.core.namesInj cn cn' k hk hnamed'
              subst this
              exact absurd (by simpa using hcn') hnot
            · cases hfalse
        · rfl
      rw [hT]; exact hd
    · have hF : notATy κ.classes κ.wholeCls cn (.inst c.name J) = .inst c.name J := by
        simp only [notATy, isAAnswer, hg, ha, Option.bind]
        split
        · rename_i htrue
          split at htrue
          · rename_i hin
            obtain ⟨j, hj, hnamed'⟩ := namedChain_mem hchain (by simpa using hin)
            rw [hk] at hnamed'; cases hnamed'
            rw [hisA] at h
            simp [hj] at h
          · split at htrue <;> cases htrue
        · rfl
      rw [hF]; exact hd
  | _ => simp [hr] at hex

#print axioms inst_leaf_facts
/-- Soundness of the `is_a?` refinements at an admitted receiver type. -/
theorem recv_facts {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {cn : String} {k : ObjId}
    (hm : StateOk κ Γ I m) (hcf : coreConstFreeN κ = true)
    (hbound : κ.boundConsts.contains cn = false) (hfree : nameFreeN κ "is_a?" = true)
    (hk : classNamed? m.heap cn = some k) :
    ∀ (ρ : Ty) (v : Value), isARecvB κ ρ = true → denM ρ m v → IsAFacts κ m cn k ρ v := by
  have leaf : ∀ (τ : Ty) (v : Value), isALeafB κ τ = true → denM τ m v →
      IsAFacts κ m cn k τ v := by
    intro τ v hl hd
    cases τ <;> first
      | exact inst_leaf_facts hm hfree hl hd hk
      | exact builtin_leaf_facts hm hcf hbound hfree hl (by intro n J h; cases h) hd hk
  intro ρ
  induction ρ with
  | union σ τ ihσ ihτ =>
    intro v hr hd
    simp only [isARecvB, Bool.and_eq_true] at hr
    rw [denM] at hd
    rcases hd with hd | hd
    · obtain ⟨hdisp, hT, hF⟩ := ihσ v hr.1 hd
      exact ⟨hdisp, fun h => denM_joinT_left (hT h), fun h => denM_joinT_left (hF h)⟩
    · obtain ⟨hdisp, hT, hF⟩ := ihτ v hr.2 hd
      exact ⟨hdisp, fun h => denM_joinT_right (hT h), fun h => denM_joinT_right (hF h)⟩
  | nilable ρ ih =>
    intro v hr hd
    simp only [isARecvB, Bool.and_eq_true] at hr
    rw [denM] at hd
    rcases hd with hd | hd
    · have hdn : denM .nilT m v := by simpa [denM] using hd
      have hok : isANoOk κ.wholeCls ("NilClass" :: rootAncestors) = true := by
        simpa [isALeafB, builtinAncestors] using hr.2
      obtain ⟨hdisp, hT, hF⟩ := leaf .nilT v hr.2 hdn
      have hTe : isATy κ.classes κ.wholeCls cn .nilT = isANilPart κ.classes κ.wholeCls cn := by
        simp only [isATy, isAAnswer, builtinAncestors, Option.bind, isANilPart, hok, ↓reduceIte]
        split <;> simp_all
      have hFe : notATy κ.classes κ.wholeCls cn .nilT = notANilPart cn := by
        simp only [notATy, isAAnswer, builtinAncestors, Option.bind, notANilPart, hok, ↓reduceIte]
        split <;> simp_all
      exact ⟨hdisp, fun h => denM_joinT_left (hTe ▸ hT h), fun h => denM_joinT_left (hFe ▸ hF h)⟩
    · obtain ⟨hdisp, hT, hF⟩ := ih v hr.1 hd
      exact ⟨hdisp, fun h => denM_joinT_right (hT h), fun h => denM_joinT_right (hF h)⟩
  | _ => intro v hr hd; exact leaf _ v (by simpa [isARecvB] using hr) hd

#print axioms recv_facts

/-- `r.is_a?(C)` for a receiver that reads in one step: the ancestor test's answer at a
machine that differs from the start only in control, or a gate. -/
theorem isA_cond {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {r : Ratchet.Expr} {cn : String}
    {k : ObjId} {vx : Value}
    (hm : StateOk κ Γ I m) (hnamed : classNamed? m.heap cn = some k)
    (hlex : Interp.lexicalConstant m cn = some (.ref k))
    (hsend : Interp.stepFn (evalFrom m (.send (some r) "is_a?" [.const cn] none)) =
      .next (pushK [.recvK "is_a?" [toRuby (.const cn)] .none .explicit] (evalFrom m r)))
    (hread : Interp.stepFn (pushK [.recvK "is_a?" [toRuby (.const cn)] .none .explicit]
        (evalFrom m r)) =
      .next (deliverA (.val vx) m [.recvK "is_a?" [toRuby (.const cn)] .none .explicit]))
    (hdisp : Interp.invoke (deliverA (.val (.ref k)) m []) vx .explicit "is_a?"
        [.ref k] none [] =
      builtinStep (Builtins.run "Object#is_a?" vx [.ref k]
        (deliverA (.val (.ref k)) m []))) :
    RunWith m (evalFrom m (.send (some r) "is_a?" [.const cn] none)) Γ .bool κ I
      (fun w n => w = .bool (isA m.heap vx k) ∧ ∃ c ks, n = reCtl m c ks) := by
  let k₁ : Kont := .recvK "is_a?" [toRuby (.const cn)] .none .explicit
  let k₂ : Kont := .argsK vx .explicit "is_a?" [] [] .none
  apply RunWith.step (answerPoint_evalFrom _ _)
    hsend
  apply RunWith.step (by rfl) hread
  apply RunWith.step (by rfl) (recv_one_step m vx "is_a?" (.const cn) rfl)
  have hconst : Interp.stepFn (pushK [k₂] (evalFrom m (.const cn))) =
      .next (deliverA (.val (.ref k)) m [k₂]) := by
    have hl : Interp.lexicalConstant (pushK [k₂] (evalFrom m (.const cn))) cn = some (.ref k) := hlex
    have := step_lit_ctl (m := pushK [k₂] (evalFrom m (.const cn))) (e := .const cn) (w := .ref k) rfl
      (by simp [toRuby, Interp.evalExpr, hl])
    simpa only [pushK, evalFrom, deliverA, Answer.ctl, reCtl, List.nil_append] using this
  apply RunWith.step (by rfl) hconst
  let M := deliverA (.val (.ref k)) m []
  have hM : StateOk κ Γ I M := StateOk_deliverA hm
  have hinv : Interp.stepFn (deliverA (.val (.ref k)) m [k₂]) =
      Interp.invoke M vx .explicit "is_a?" [.ref k] none [] := rfl
  have hk : (M.heap.classPayload? k).isSome = true := by
    have hk := hnamed
    change (m.heap.classPayload? k).isSome = true
    unfold classNamed? at hk
    split at hk
    · split at hk
      · cases hk; assumption
      · cases hk
    · cases hk
  rcases isA_run M vx k hk with h | ⟨msg, h⟩
  · apply RunWith.step (by rfl) (hinv.trans (hdisp.trans (by rw [h]; rfl)))
    apply RunWith.answer (a := .val (.bool (isA M.heap vx k))) (m := M)
      (fun v n c ks hp => ⟨hp.1, by
        obtain ⟨c', ks', rfl⟩ := hp.2
        exact ⟨c, ks, rfl⟩⟩)
    exact ⟨⟨Framed_reCtl m _ [], by simp [AnsOk, denM, isBoolV], fun _ _ => hM⟩,
      fun v hv => by cases hv; exact ⟨rfl, _, _, rfl⟩⟩
  · exact RunWith.unsupported (by rfl) (hinv.trans (hdisp.trans (by rw [h]; rfl)))

#print axioms isA_cond

theorem SemSafeCtxA.ifIsA {κ κ' : Ctx} {Γ Γ₁ Γ₂ : Env} {I I' : Ty} {x cn : String}
    {ρ τ₁ τ₂ : Ty} {t e : Ratchet.Expr}
    (hx : envGet? Γ x = some ρ) (hg : ifIsAB κ ρ cn = true)
    (ht : SemSafeCtxA κ (envSet Γ x (isATy κ.classes κ.wholeCls cn ρ)) I t τ₁ κ' Γ₁ I')
    (he : SemSafeCtxA κ (envSet Γ x (notATy κ.classes κ.wholeCls cn ρ)) I e τ₂ κ' Γ₂ I') :
    SemSafeCtxA κ Γ I (.if' (.send (some (.var .lvar x)) "is_a?" [.const cn] none) t (some e))
      (joinT τ₁ τ₂) κ' (joinEnv Γ₁ Γ₂) I' := by
  simp only [ifIsAB, Bool.and_eq_true, Bool.not_eq_true'] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hrecv, hcls⟩, hcf⟩, hbound⟩, hfree⟩, hTfo⟩, hTal⟩, hFfo⟩, hFal⟩ := hg
  intro m hm
  let k : Kont := .ifK (toRuby t) (some (toRuby e))
  obtain ⟨c, hnamed, hlex⟩ := isA_class_named hm hcf hcls
  have hρ : stripAlias ρ = ρ := by
    cases ρ <;> simp_all [stripAlias, isARecvB, isALeafB]
  have hv0 : denM ρ m (m.getLocal x) := by
    have := (hm.env.1 x _ hx).1
    rwa [hρ] at this
  obtain ⟨_, hT, hF⟩ := recv_facts hm hcf hbound hfree hnamed ρ _ hrecv hv0
  have hM : StateOk κ Γ I (deliverA (.val (.ref c)) m []) := StateOk_deliverA hm
  obtain ⟨hdisp, _, _⟩ := recv_facts hM hcf hbound hfree (cn := cn) (k := c) hnamed ρ _ hrecv
    (denM_deliverA.mpr hv0)
  apply RunSpec.step (answerPoint_evalFrom _ _)
    (show Interp.stepFn _ = .next (pushK [k] (evalFrom m
      (.send (some (.var .lvar x)) "is_a?" [.const cn] none))) from rfl)
  have hread : Interp.stepFn (pushK [.recvK "is_a?" [toRuby (.const cn)] .none .explicit]
        (evalFrom m (.var .lvar x))) =
      .next (deliverA (.val (m.getLocal x)) m [.recvK "is_a?" [toRuby (.const cn)] .none .explicit]) := by
    simpa only [pushK, evalFrom, deliverA, Answer.ctl, reCtl, getLocal_reCtl, List.nil_append] using
      step_var_ctl (m := pushK [.recvK "is_a?" [toRuby (.const cn)] .none .explicit]
        (evalFrom m (.var .lvar x))) (x := x) rfl
  apply (isA_cond hm hnamed hlex rfl hread hdisp).bindSpec hm.rootClean
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
    have hloc : n.getLocal x = m.getLocal x := by rw [hre]; exact getLocal_reCtl m _ _ x
    have hn : StateOk κ Γ I n := hr.1.2.2 _ rfl
    have hbranch : Interp.stepFn (deliverA (.val (.bool (isA m.heap (m.getLocal x) c))) n [k]) =
        .next (evalFrom n (if isA m.heap (m.getLocal x) c then t else e)) := by
      simp only [Interp.stepFn, deliverA, Answer.ctl, Interp.applyKont, k]
      cases hb' : isA m.heap (m.getLocal x) c <;> simp [Value.truthy, Interp.withCtl, evalFrom]
    apply RunSpec.step (by rfl) hbranch
    apply RunSpec.rebase _ hr.1.1
    cases hb' : isA m.heap (m.getLocal x) c
    · have hd : denM (notATy κ.classes κ.wholeCls cn ρ) n (n.getLocal x) := by
        rw [hloc]; exact hr.1.1.firstOrder _ hFfo _ (hF hb')
      have hs : StateOk κ (envSet Γ x (notATy κ.classes κ.wholeCls cn ρ)) I n :=
        { hn with env := envOk_refine hn.env hx hd hFal }
      simpa only [Bool.false_eq_true, ite_false] using
        (he.weaken (fun _ _ hm hd => ⟨StateOk_joinEnv false hm, denM_joinT_right hd⟩)) n hs
    · have hd : denM (isATy κ.classes κ.wholeCls cn ρ) n (n.getLocal x) := by
        rw [hloc]; exact hr.1.1.firstOrder _ hTfo _ (hT hb')
      have hs : StateOk κ (envSet Γ x (isATy κ.classes κ.wholeCls cn ρ)) I n :=
        { hn with env := envOk_refine hn.env hx hd hTal }
      simpa only [ite_true] using
        (ht.weaken (fun _ _ hm hd => ⟨StateOk_joinEnv true hm, denM_joinT_left hd⟩)) n hs

#print axioms SemSafeCtxA.ifIsA
end Ratchet.Denote.Typed
