import Books.TypeSoundness.Conformance.Names.InheritedLookup
import Books.TypeSoundness.Checker.Guards.SuperRoute

/-! Translate a checked super route to the real superFound lookup. The physical chain is
unique even when names alias; an earlier occurrence of the defining owner cannot survive
ancestors' deduplication. Annotation-domain body safety remains a separate obligation. -/
set_option autoImplicit false
namespace Checker.Soundness
open RubyCore Checker

private theorem dedup_nodup (xs acc : List ObjId) (ha : acc.Nodup) :
    (xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) acc).Nodup := by
  induction xs generalizing acc with
  | nil => exact ha
  | cons x xs ih =>
    simp only [List.foldl_cons]
    split
    · exact ih _ ha
    · rename_i hx
      apply ih
      have hn : x ∉ acc := by simpa using hx
      refine List.nodup_append.mpr ⟨ha, by simp, ?_⟩
      intro a ha b hb
      have hb : b = x := by simpa using hb
      subst b
      intro he
      exact hn (he ▸ ha)

theorem ancestors_nodup (h : Heap) (k : ObjId) : (ancestors h k).Nodup :=
  dedup_nodup _ [] (by simp)

theorem superFound_after {h : Heap} {r current : ObjId} {name : String}
    {before after : List ObjId} (hch : Proof.ChainsIn h) (ha : ancestors h r = before ++ current :: after) :
    Interp.superFound h r current name = Proof.lookupScan h name after := by
  have hn := List.nodup_append.mp (ha ▸ ancestors_nodup h r)
  have hd : ∀ k ∈ before, (k != current) = true := by
    intro k hk
    exact bne_iff_ne.mpr (hn.2.2 k hk current List.mem_cons_self)
  simp only [Interp.superFound, ha, List.dropWhile_append_of_pos hd,
    List.dropWhile_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.drop_succ_cons,
    List.drop_zero]
  apply Proof.lookupInChain_eq_scan
  have ha' := Proof.ancestors_length_bound hch r
  have hb := Proof.ancestors_length_bound hch Boot.objectId
  rw [ha, List.length_append, List.length_cons] at ha'
  omega

private theorem lookup_go_own {h : Heap} {k : ObjId} {name : String} {rest : List ObjId}
    {md : MethodDef} (hm : (h.classPayload? k).bind
      (fun cp => (cp.methods.find? (·.1 == name)).map (·.2)) = some md) (hv : md.visibilityOnly = false) :
    Proof.lookupScan h name (k :: rest) = some (k, md) := by
  simp only [Proof.lookupScan]
  cases hc : h.classPayload? k with
  | none => simp [hc] at hm
  | some cp =>
    cases hf : cp.methods.find? (·.1 == name) with
    | none => simp [hc, hf] at hm
    | some p =>
      have he : p.2 = md := by simpa [hc, hf] using hm
      simp only [hf, he, hv, Bool.not_false, if_true]

/-- Recover code strictly after the current owner. Neither physical lookup nor a method
signature is assumed; the caller must still check arguments and supply the body proof. -/
theorem declared_super_code {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {receiver : Cls} {current owner : String} {d : Defn} {r currentId : ObjId}
    (hm : StateOk κ Γ I m) (hrc : receiver ∈ κ.classes)
    (hr : classNamed? m.heap receiver.name = some r)
    (hc : classNamed? m.heap current = some currentId)
    (route : SuperRoute κ.classes receiver.name current owner d) :
    ∃ k md, classNamed? m.heap owner = some k ∧
      Interp.superFound m.heap r currentId d.name = some (k, md) ∧
      md.params = toRubyParams d.params ∧ md.body = toRuby d.body ∧
      md.undefined = false ∧ InstanceMethodCode k d.name md := by
  obtain ⟨k, hk, methods, _⟩ := hm.classes route.cls route.member
  obtain ⟨md, hmd, hp, hb, hu, code⟩ := methods d route.installed
  obtain ⟨before, j, tail, hchain, _, hj, htail⟩ := hm.classChains.before_owner hrc hr route.chain
  have he : j = currentId := Option.some.inj (hj.symm.trans hc)
  subst j
  have ht : NamedChain m.heap (route.between ++ route.cls.name :: (route.after ++ receiver.rootTail)) tail := by
    simpa only [List.append_assoc, List.cons_append] using htail
  obtain ⟨between, j, after, he, hbetween, hj, _⟩ := ht.split
  have hkj : j = k := Option.some.inj (hj.symm.trans hk)
  subst j
  refine ⟨k, md, by simpa only [route.nameOk] using hk, ?_, hp, hb, hu, code⟩
  rw [superFound_after hm.core.classReady.chains hchain, he]
  rw [lookup_go_skip (fun j hj => ?_)]
  · exact lookup_go_own hmd code.visibilityOnly
  · obtain ⟨cn, hcn, hnamed⟩ := hbetween.cover hj
    obtain ⟨old, hold, hname, hmiss⟩ := route.clear cn hcn
    exact hm.ownMethod_absent hold (by simpa only [hname] using hnamed) (by simpa only [hname] using hmiss)


/-- With a direct-parent route, the ancestors after the current owner start at the owner. -/
theorem declared_super_chain {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {receiver : Cls} {current owner : String} {d : Defn} {r currentId : ObjId}
    (hm : StateOk κ Γ I m) (hrc : receiver ∈ κ.classes)
    (hr : classNamed? m.heap receiver.name = some r)
    (hc : classNamed? m.heap current = some currentId)
    (route : SuperRoute κ.classes receiver.name current owner d) :
    ∃ k after, classNamed? m.heap owner = some k ∧
      ((ancestors m.heap r).dropWhile (· != currentId)).drop 1 = k :: after := by
  obtain ⟨before, j, tail, hchain, _, hj, htail⟩ := hm.classChains.before_owner hrc hr route.chain
  have he : j = currentId := Option.some.inj (hj.symm.trans hc)
  subst j
  have ht : NamedChain m.heap (route.between ++ route.cls.name :: (route.after ++ receiver.rootTail)) tail := by
    simpa only [List.append_assoc, List.cons_append] using htail
  obtain ⟨between, k, after, he, hbetween, hk, _⟩ := ht.split
  have hb : between = [] := by
    have hd := route.direct
    rw [hd] at hbetween
    cases between with
    | nil => rfl
    | cons _ _ => exact hbetween.elim
  subst hb
  refine ⟨k, after, by simpa only [route.nameOk] using hk, ?_⟩
  have hn := List.nodup_append.mp (hchain ▸ ancestors_nodup m.heap r)
  have hd : ∀ x ∈ before, (x != currentId) = true := by
    intro x hx
    exact bne_iff_ne.mpr (hn.2.2 x hx currentId List.mem_cons_self)
  rw [hchain, List.dropWhile_append_of_pos hd]
  simp [he]

#print axioms ancestors_nodup
#print axioms superFound_after
#print axioms declared_super_code
end Checker.Soundness
