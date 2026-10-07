import Books.TypeSoundness.Rules.Inherited.InheritedConstructorExpr
import Books.TypeSoundness.Rules.Inherited.InheritedRun
import Books.TypeSoundness.Conformance.Names.NativePrefix
import Books.TypeSoundness.Conformance.Class.ClassGuards
import Checker.Guards.MemberRoute

/-! Inherited call forms with only checked routes, static guards and full body premises.
Every receiver, owner, body, annotation and context is a parameter. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem mem_takeWhile_before {before after : List ObjId} {k j : ObjId}
    (h : j ∈ (before ++ k :: after).takeWhile (· != k)) : j ∈ before := by
  induction before with
  | nil => simp at h
  | cons x xs ih =>
    by_cases hx : (x != k) = true
    · simp only [List.cons_append, List.takeWhile_cons, hx, ite_true, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)
    · simp only [List.cons_append, List.takeWhile_cons, hx] at h
      simp at h

theorem NamedChain.mem_named {h : Heap} {ns : List String} {ks : List ObjId} {j : ObjId}
    (hc : NamedChain h ns ks) (hj : j ∈ ks) : ∃ cn ∈ ns, classNamed? h cn = some j := by
  induction ns generalizing ks with
  | nil => cases ks with
    | nil => cases hj
    | cons _ _ => exact hc.elim
  | cons cn ns ih => cases ks with
    | nil => exact hc.elim
    | cons k ks =>
      obtain ⟨hk, hrest⟩ := hc
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ⟨cn, List.mem_cons_self, hk⟩
      · obtain ⟨cn', hm, hn⟩ := ih hrest hj
        exact ⟨cn', List.mem_cons_of_mem _ hm, hn⟩

/-- Classes between an exact receiver and the owning ancestor are program classes:
no CRuby singleton or optional-library method shadows a native-free selector. -/
theorem inherited_shadow_free {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {c : Cls}
    {owner name : String} {r k : ObjId} {pre post : List String}
    (hm : StateOk κ Γ I m) (hc : c ∈ κ.classes) (hr : classNamed? m.heap c.name = some r)
    (ha : ancestors? κ.classes c.name = some (pre ++ owner :: post))
    (hpre : ∀ cn ∈ pre, ∃ old ∈ κ.classes, old.name = cn)
    (hk : classNamed? m.heap owner = some k) (hf : nativeInstanceFreeB name = true) :
    Interp.crubyShadow m.heap ((ancestors m.heap r).takeWhile (· != k)) name = none := by
  obtain ⟨before, k', after, heq, hnc, hk', _⟩ := hm.classChains.before_owner hc hr ha
  have hkk : k' = k := Option.some.inj (hk'.symm.trans hk)
  subst hkk
  have site (j : ObjId) (hj : j ∈ (ancestors m.heap r).takeWhile (· != k')) :
      ∃ cn, InstanceSite κ cn j m.heap := by
    rw [heq] at hj
    obtain ⟨cn, hcn, hn⟩ := NamedChain.mem_named hnc (mem_takeWhile_before hj)
    obtain ⟨old, hold, rfl⟩ := hpre cn hcn
    exact ⟨_, hm.classSites.at_class hold hn⟩
  apply nativeInstanceFreeB_shadow hf
  · intro j hj
    obtain ⟨_, s⟩ := site j hj
    simp only [Interp.nativeSingletonMethod, s.detached, Option.any_none]
  · intro j hj
    obtain ⟨_, s⟩ := site j hj
    have hl := s.library
    simp only [Interp.libraryNamespace] at hl
    simp only [Interp.featureMethod, Interp.featureHas, Interp.libraryNamespace, hl, s.detached,
      Option.bind_none, Option.any_none, Bool.or_false]

theorem SemSafeCtxA.newInherited {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ Γb : Env} {I I₁ I₂ Ib τ : Ty}
    {c : Cls} {owner : String} {d : Defn} {ps : List SigParam} {recv : Checker.Expr} {args : List Checker.Expr}
    (hr : SemSafeCtxA κ Γ I recv (.clsOf c.name) κ₁ Γ₁ I₁)
    (ha : SemAllCtxA κ₁ Γ₁ I₁ args (ps.map (·.2)) κ₂ Γ₂ I₂)
    (hs : explicitReceiverB recv = true) (hc : c ∈ κ₂.classes)
    (route : MemberRoute κ₂.classes c.name owner d)
    (hn : d.name = "initialize") (hnew : smroGet? κ₂.classes c.name "new" = none)
    (halloc : c.name ∈ κ₂.pos.plainAlloc)
    (hp : d.params = ps.map (fun p => Checker.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (_hret : FirstOrder τ = true) (hout : FirstOrder Ib = true)
    (hb : SemInitA (initializerBodyCtxAt κ₂ c.name owner) ps .ivar0 d.body τ
      (initializerBodyCtxAt κ₂ c.name owner) Γb Ib)
    (hg : mainCallB κ₂ Γ₂ I₂ = true) :
    SemSafeCtxA κ Γ I (.send (some recv) "new" args none) (.inst c.name Ib) κ₂ Γ₂ I₂ := by
  simp only [mainCallB, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨ht, hΓ⟩, hasms, hmain, hw, hcl, hco⟩ := hg
  exact hr.constructInherited ha (explicitReceiverB_sound hs) hc route.member route.installed hn
    route.chain route.clear hnew halloc hp hps (by simpa only [route.nameOk] using hb)
    (reframeTypesB_sound ht) hasms (.main hmain hw hcl)
    (fun x => (constGet?_empty (κ := initializerBodyCtxAt κ₂ c.name route.cls.name) hco x).trans
      (constGet?_empty hco x).symm) (List.all_eq_true.mp hΓ) hout

theorem SemSafeCtxA.callInherited {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ Γb : Env} {I I₁ I₂ Ib τ : Ty}
    {c : Cls} {owner : String} {d : Defn} {ps : List SigParam} {recv : Checker.Expr} {args : List Checker.Expr}
    (hr : SemSafeCtxA κ Γ I recv (.inst c.name Ib) κ₁ Γ₁ I₁)
    (ha : SemAllCtxA κ₁ Γ₁ I₁ args (ps.map (·.2)) κ₂ Γ₂ I₂)
    (hs : explicitReceiverB recv = true) (hc : c ∈ κ₂.classes)
    (route : MemberRoute κ₂.classes c.name owner d)
    (hn : d.name ≠ "initialize") (hname : directCallNameB d.name = true)
    (hnative : nativeInstanceFreeB d.name = true)
    (hp : d.params = ps.map (fun p => Checker.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hret : FirstOrder τ = true) (hself : FirstOrder Ib = true)
    (hb : SemSafeCtxA (instanceBodyCtx κ₂ ⟨c.name, owner, d.name, false⟩ Ib) ps Ib d.body τ
      (instanceBodyCtx κ₂ ⟨c.name, owner, d.name, false⟩ Ib) Γb Ib)
    (hg : instanceCallB κ₂ Γ₂ I₂ = true) :
    SemSafeCtxA κ Γ I (.send (some recv) d.name args none) τ κ₂ Γ₂ I₂ := by
  simp only [instanceCallB, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨ht, hΓ⟩, hw⟩, hasms, hco⟩ := hg
  apply hr.sendVia ha (explicitReceiverB_sound hs) hself (by
    intro t ht
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
    exact (hps p hp).1)
  intro m hm hk recv hv args hargs
  obtain ⟨n, hs, hrun⟩ := declared_inherited_run hp hps hret
    (by simpa only [route.nameOk] using hb) hm (reframeTypesB_sound ht) hasms hc
    route.member route.installed route.chain route.clear (callWorldB_sound hw) hk hself hv
    (by simpa using denAll_length hargs) hargs
    (fun x => (constGet?_empty (κ := instanceBodyCtx κ₂ ⟨c.name, route.cls.name, d.name, false⟩ Ib) hco x).trans
      (constGet?_empty hco x).symm) (List.all_eq_true.mp hΓ)
    (fun _ _ => Or.inr (directCallNameB_sound hname)) hn (fun k' hk' => by
      obtain ⟨r, rsite⟩ := hm.classSites.of_class hc
      rw [exactInst_classOf (by rw [denM] at hv; exact hv.1) rsite.named]
      exact inherited_shadow_free hm hc rsite.named route.chain
        (fun cn h => let ⟨o, ho, hn, _⟩ := route.clear cn h; ⟨o, ho, hn⟩) hk' hnative)
  rw [hs]
  exact hrun

#print axioms SemSafeCtxA.newInherited
#print axioms SemSafeCtxA.callInherited
end Checker.Soundness.Typed
