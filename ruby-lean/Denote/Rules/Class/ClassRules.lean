import Denote.Rules.Class.ClassHeaderRun
import Denote.Rules.Instance.MemberDefine
import Denote.Rules.Constructor.ConstructorExpr
import Denote.Rules.Instance.InstanceImplicit
import Denote.Sem.Class.ClassGuards
import Denote.Sem.Names.NativeGuards

/-! Constructor-ready semantic forms: every side condition is syntax/type data or a
proved body premise. No heap predicate, fixed class name, or signature-only admission is
left for the checker to supply. These are the interfaces for the forthcoming DJudge rules. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemSafeCtxA.classDecl {κ κb : Ctx} {Γ Γb : Env} {I Ib τ : Ty}
    {name : String} {body : Ratchet.Expr}
    (hb : SemSafeCtxA (classHeaderCtx (classBodyCtx κ name) name) [] .ivar0 body τ κb Γb Ib)
    (hg : classRuleB κ κb Γ I τ name = true) :
    SemSafeCtxA κ Γ I (.class' name none body) τ (returnScopeCtx κ κb) Γ I := by
  simp only [classRuleB, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ht, hΓ⟩, hτ⟩, ha, hr, hf, hin, hw, hcl, hq, hco⟩,
    htab⟩, hnative⟩, hfresh⟩, hne⟩, hnew⟩, hquiet⟩, hplain⟩, hframe⟩ := hg
  intro m hm
  exact class_header_runSpec hm (reframeTypesB_sound ht) ha hr hf hin hw hcl hq
    (fun x => (constGet?_empty hco x).trans
      (constGet?_empty (κ := returnScopeCtx κ κb) hco x).symm)
    (List.all_eq_true.mp hΓ) hτ (plainClassTablesB_sound htab)
    (classNativeFrameB_to_semB hnative) hfresh hne hnew (classNativeQuietB_sound hquiet)
    hplain hframe hb

theorem SemSafeCtxA.memberDef {κ : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {c : Cls} {d : Defn}
    {ps : List SigParam}
    (hp : d.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hret : FirstOrder τ = true) (hself : FirstOrder Ib = true)
    (hb : SemSafeCtxA (instanceBodyCtx (instanceDeclCtx κ c d) ⟨c.name, c.name, d.name⟩ Ib)
      ps Ib d.body τ (instanceBodyCtx (instanceDeclCtx κ c d) ⟨c.name, c.name, d.name⟩ Ib) Γb Ib)
    (hn : d.name ≠ "initialize") (hc : c ∈ κ.classes)
    (hg : memberRuleB κ Γ I c d = true) :
    SemSafeCtxA κ Γ I (.def' d.name d.params d.body) .sym (instanceDeclCtx κ c d) Γ I := by
  simp only [memberRuleB, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨ht, hΓ⟩, ha, hr, hroot, hnew, hmiss, hquiet⟩, hplain⟩, hf⟩, htab⟩ := hg
  exact SemSafeCtxA.memberDecl hp hps hret hself hb hn hr hc (reframeTypesB_sound ht)
    (List.all_eq_true.mp hΓ) ha hplain hroot hf htab hnew hmiss hquiet

theorem SemSafeCtxA.initDef {κ : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {c : Cls} {d : Defn}
    {ps : List SigParam} (hn : d.name = "initialize")
    (hp : d.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hret : FirstOrder τ = true) (hout : FirstOrder Ib = true)
    (hb : SemInitA (initializerBodyCtx (instanceDeclCtx κ c d) c.name) ps .ivar0 d.body τ
      (initializerBodyCtx (instanceDeclCtx κ c d) c.name) Γb Ib)
    (hc : c ∈ κ.classes) (hg : memberRuleB κ Γ I c d = true) :
    SemSafeCtxA κ Γ I (.def' d.name d.params d.body) .sym (instanceDeclCtx κ c d) Γ I := by
  simp only [memberRuleB, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨ht, hΓ⟩, ha, hr, hroot, _, _, _⟩, hplain⟩, hf⟩, htab⟩ := hg
  exact SemSafeCtxA.initializerDecl hn hp hps hret hout hb hr hc (reframeTypesB_sound ht)
    (List.all_eq_true.mp hΓ) ha hplain hroot hf htab

theorem SemSafeCtxA.newInst {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ Γb : Env} {I I₁ I₂ Ib τ : Ty}
    {c : Cls} {d : Defn} {ps : List SigParam} {recv : Ratchet.Expr} {args : List Ratchet.Expr}
    (hr : SemSafeCtxA κ Γ I recv (.clsOf c.name) κ₁ Γ₁ I₁)
    (ha : SemAllCtxA κ₁ Γ₁ I₁ args (ps.map (·.2)) κ₂ Γ₂ I₂)
    (hs : explicitReceiverB recv = true) (hc : c ∈ κ₂.classes) (hd : d ∈ c.methods)
    (hn : d.name = "initialize") (hnew : smroGet? κ₂.classes c.name "new" = none)
    (halloc : c.name ∈ κ₂.pos.plainAlloc)
    (hp : d.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (_hret : FirstOrder τ = true) (hout : FirstOrder Ib = true)
    (hb : SemInitA (initializerBodyCtx κ₂ c.name) ps .ivar0 d.body τ
      (initializerBodyCtx κ₂ c.name) Γb Ib)
    (hg : mainCallB κ₂ Γ₂ I₂ = true) :
    SemSafeCtxA κ Γ I (.send (some recv) "new" args none) (.inst c.name Ib) κ₂ Γ₂ I₂ := by
  simp only [mainCallB, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨ht, hΓ⟩, hasms, hmain, hw, hcl, hco⟩ := hg
  exact hr.construct ha (explicitReceiverB_sound hs) hc hd hn hnew halloc hp hps hb
    (reframeTypesB_sound ht) hasms hmain hw hcl
    (fun x => (constGet?_empty (κ := initializerBodyCtx κ₂ c.name) hco x).trans
      (constGet?_empty hco x).symm)
    (List.all_eq_true.mp hΓ) hout

theorem SemSafeCtxA.callMethodSig {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ Γb : Env} {I I₁ I₂ Ib τ : Ty}
    {c : Cls} {d : Defn} {ps : List SigParam} {recv : Ratchet.Expr} {args : List Ratchet.Expr}
    (hr : SemSafeCtxA κ Γ I recv (.inst c.name Ib) κ₁ Γ₁ I₁)
    (ha : SemAllCtxA κ₁ Γ₁ I₁ args (ps.map (·.2)) κ₂ Γ₂ I₂)
    (hs : explicitReceiverB recv = true) (hc : c ∈ κ₂.classes) (hd : d ∈ c.methods)
    (hn : d.name ≠ "initialize") (hname : directCallNameB d.name = true)
    (hp : d.params = ps.map (fun p => Ratchet.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hret : FirstOrder τ = true) (hself : FirstOrder Ib = true)
    (hb : SemSafeCtxA (instanceBodyCtx κ₂ ⟨c.name, c.name, d.name⟩ Ib) ps Ib d.body τ
      (instanceBodyCtx κ₂ ⟨c.name, c.name, d.name⟩ Ib) Γb Ib)
    (hg : instanceCallB κ₂ Γ₂ I₂ = true) :
    SemSafeCtxA κ Γ I (.send (some recv) d.name args none) τ κ₂ Γ₂ I₂ := by
  simp only [instanceCallB, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨ht, hΓ⟩, hw⟩, hasms, hco⟩ := hg
  exact hr.instanceCall_at ha (explicitReceiverB_sound hs) hc hd hn (directCallNameB_sound hname)
    hp hps hret hself hb (reframeTypesB_sound ht) hasms (callWorldB_sound hw)
    (fun x => (constGet?_empty (κ := instanceBodyCtx κ₂ ⟨c.name, c.name, d.name⟩ Ib) hco x).trans
      (constGet?_empty hco x).symm)
    (List.all_eq_true.mp hΓ)

theorem SemSafeCtxA.vcallMethodSig {κ : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {c : Cls} {d : Defn}
    (hs : κ.selfTy = some (.inst c.name Ib)) (hc : c ∈ κ.classes) (hd : d ∈ c.methods)
    (hn : d.name ≠ "initialize") (hname : directCallNameB d.name = true) (hp : d.params = [])
    (hret : FirstOrder τ = true) (hself : FirstOrder Ib = true)
    (hb : SemSafeCtxA (instanceBodyCtx κ ⟨c.name, c.name, d.name⟩ Ib) [] Ib d.body τ
      (instanceBodyCtx κ ⟨c.name, c.name, d.name⟩ Ib) Γb Ib)
    (hg : instanceCallB κ Γ I = true) :
    SemSafeCtxA κ Γ I (.vcall d.name) τ κ Γ I := by
  simp only [instanceCallB, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨ht, hΓ⟩, hw⟩, hasms, hco⟩ := hg
  exact SemSafeCtxA.instanceVcall hs hc hd hn (directCallNameB_sound hname) hp hret hself hb
    (reframeTypesB_sound ht) hasms (callWorldB_sound hw)
    (fun x => (constGet?_empty (κ := instanceBodyCtx κ ⟨c.name, c.name, d.name⟩ Ib) hco x).trans
      (constGet?_empty hco x).symm) (List.all_eq_true.mp hΓ)

#print axioms SemSafeCtxA.classDecl
#print axioms SemSafeCtxA.memberDef
#print axioms SemSafeCtxA.initDef
#print axioms SemSafeCtxA.newInst
#print axioms SemSafeCtxA.callMethodSig
#print axioms SemSafeCtxA.vcallMethodSig
end Ratchet.Denote.Typed
