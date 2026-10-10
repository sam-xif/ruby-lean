import Books.TypeSoundness.Checker.Guards.MethodCtx
import Books.TypeSoundness.Conformance.Instance.InstanceTable
import Books.TypeSoundness.Conformance.Names.MemberDeclared

/-! A top-level definition preserves declared class records at distinct heap owners.
Root-name conformance rules out hidden aliases to Object; source-name inequality alone
would not establish that separation. Singleton rows retain their distinct metaclass owner. -/
set_option autoImplicit false
namespace Checker.Soundness
open RubyCore Checker

theorem StateOk_defineTopMethod_classes {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {d : Defn} {md : MethodDef}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (ha : κ.asms = []) (hclasses : topDeclClassesB κ d.name = true)
    (hn : nameFreeN κ d.name = false) (hmiss : "method_missing" ≠ d.name)
    (hquiet : "method_added" ≠ d.name)
    (hc : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hfresh : ∀ old ∈ κ.defs, old.name ≠ d.name)
    (hp : md.params = toRubyParams d.params) (hb : md.body = toRuby d.body)
    (hu : md.undefined = false) (hcode : TopMethodCode md) :
    StateOk { κ with pos := { κ.pos with defs := d :: κ.defs } } Γ I
      { m with heap := defineMethod m.heap Boot.objectId d.name md } := by
  simp only [topDeclClassesB, Bool.or_eq_true, Bool.and_eq_true] at hclasses
  obtain ⟨⟨⟨hms, hshn⟩, hinhn⟩, hclasses2⟩ := hclasses
  have hsh : singletonHookName ≠ d.name := by
    intro he; rw [← he] at hshn; simp [singletonHookName] at hshn
  have hinh : "inherited" ≠ d.name := by
    intro he; rw [← he] at hinhn; simp at hinhn
  have hmain : d.name ∉ mainSingletonNames := by
    intro hn
    have hf : mainSingletonNames.contains d.name = false := by
      simpa only [Bool.not_eq_true'] using hms
    rw [List.contains_iff_mem.mpr hn] at hf
    cases hf
  rcases hclasses2 with hempty | ⟨hnew, howners⟩
  · exact StateOk_defineTopMethod hm ht hΓ ha (List.isEmpty_iff.mp hempty)
      hn hmiss hquiet hsh hinh hc hfresh hp hb hu hcode hmain
  have hsep (c : Cls) (hmem : c ∈ κ.classes)
      (hk : classNamed? m.heap c.name = some Boot.objectId) : False := by
    have hnot : c.name ∉ rootAncestors := by
      simpa using List.all_eq_true.mp howners c hmem
    exact declared_not_object hm hk hnot rfl
  obtain ⟨e, he, _⟩ := hm.core.classReady.objectEigen
  apply StateOk_methodWrite (hprefix := hm.toStateCore.objectWrite d.name)
    (hhooks := fun _ => ClassHookWriteOk.object _ _)
    hm ht hΓ ha hn hmiss hquiet hsh hinh
  · exact ClassesOk_methodWrite_old hm.classes (by rw [he]; rfl)
      (fun c hmem hk => False.elim (hsep c hmem hk))
  · exact DefsOk_defineMethod hm.defs hc hfresh hp hb hu hcode hmain
  · exact hm.declCls.methodWrite (Ne.symm (bne_iff_ne.mp hnew)) hmiss
  · exact hm.ownNames.methodWrite (fun c hmem hk => False.elim (hsep c hmem hk))
  · exact hm.rootInit.defineTop
  · exact primitiveInitB_defineMethod_outside hm.primitiveInit hm.core.classReady.chains
      (by decide) (by decide) (by decide)

#print axioms StateOk_defineTopMethod_classes
end Checker.Soundness
