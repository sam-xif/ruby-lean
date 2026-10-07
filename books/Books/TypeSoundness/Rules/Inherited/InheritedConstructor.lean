import Books.TypeSoundness.Rules.Constructor.ConstructorResolve
import Books.TypeSoundness.Conformance.Names.InheritedLookup

/-! Inherited initialize: allocation belongs to the receiver class, lexical scope to the
first defining owner. Ordered lookup and the full annotated body are separate premises. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem declared_inherited_constructor_run {κ : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {m : Machine}
    {receiver owner : Cls} {d : Defn} {pre post : List String}
    {ps : List SigParam} {args : List Value} {sendSite : SendSite}
    (hm : StateOk κ Γ I m) (hrc : receiver ∈ κ.classes) (hoc : owner ∈ κ.classes)
    (hd : d ∈ owner.methods) (hn : d.name = "initialize")
    (hchain : ancestors? κ.classes receiver.name = some (pre ++ owner.name :: post))
    (hmiss : ∀ cn ∈ pre, ∃ old ∈ κ.classes, old.name = cn ∧ d.name ∉ ownNames κ.classes cn)
    (hnew : smroGet? κ.classes receiver.name "new" = none)
    (halloc : receiver.name ∈ κ.pos.plainAlloc)
    (hparams : d.params = ps.map (fun p => Checker.Param.req p.1))
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hbody : SemInitA (initializerBodyCtxAt κ receiver.name owner.name) ps .ivar0 d.body τ
      (initializerBodyCtxAt κ receiver.name owner.name) Γb Ib)
    (ht : ReframeFO κ I) (ha : κ.asms = []) (hw : CallWorld κ)
    (hconst : ∀ x, constGet? (initializerBodyCtxAt κ receiver.name owner.name) x = constGet? κ x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) (hIb : FirstOrder Ib = true)
    (hkont : m.kont = []) (hargs : DenAll (ps.map (·.2)) m args) :
    ∃ r, classNamed? m.heap receiver.name = some r ∧
      StepSpec m Γ (.inst receiver.name Ib) (Interp.finishSend m (.ref r) sendSite "new" args .none) κ I := by
  obtain ⟨r, site⟩ := hm.classSites.of_class hrc
  obtain ⟨k, ownerSite⟩ := hm.classSites.of_class hoc
  obtain ⟨j, md, hj, hl, hp, hb, hu, code⟩ :=
    declared_inherited_code hm hrc site.named hoc hd hchain hmiss
  have he : j = k := Option.some.inj (hj.symm.trans ownerSite.named)
  subst j
  rw [hn] at hl code
  have dispatch := (hm.declCls receiver hrc r site.named).2.2.2.2.1 (hm.ordinary_decl hrc halloc) hnew
  obtain ⟨j, hj, alloc⟩ := hm.allocators receiver.name halloc
  have he : j = r := Option.some.inj (hj.symm.trans site.named)
  subst j
  have hparam : md.params = (ps.map (·.1)).map RubyCore.Param.req :=
    hp.trans (by rw [hparams]; exact toRubyParams_required ps)
  exact ⟨r, site.named, constructor_runSpec_at (sendSite := sendSite)
    (κb := initializerBodyCtxAt κ receiver.name owner.name)
    hm ht ha ht alloc site ownerSite ⟨dispatch.1, dispatch.2⟩ code hl hu hparam hb
    (by simpa using denAll_length hargs) hargs hps hconst hw rfl hconst hΓ rfl hIb hkont hbody⟩

#print axioms declared_inherited_constructor_run
end Checker.Soundness.Typed
