import Books.TypeSoundness.Conformance.Class.ClassConstScopeActual
import Books.TypeSoundness.Conformance.Class.ClassMetadataActual
import Books.TypeSoundness.Conformance.Names.RootLookup

/-! Repair the old instance-constant transfer: future globals need Object reachability
or the module fallback, in addition to equality for the current constant table. -/
set_option autoImplicit false
namespace Checker.Soundness.FreshClassActual
open RubyCore Checker RubyCore.Proof RubyCore.Proof.Judgment
variable {p : ObjId}
variable {m : Machine} {name : String} {e : ObjId}
local notation "h₁" => heap m name e p

private theorem firstM_absent {xs : List ObjId} {f : ObjId → Option Value}
    (hp : xs.firstM f = none) : ∀ j ∈ xs, f j = none := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases ha : f a with
    | some v => simp only [List.firstM, ha] at hp; cases hp
    | none =>
      have ht : xs.firstM f = none := by simpa [List.firstM, ha] using hp
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ha
      · exact ih ht j hj

private theorem firstM_registered (xs : List ObjId) (v : Value)
    (f : ObjId → Option Value)
    (hp : ∀ j ∈ xs, f j = if j = Boot.objectId then some v else none) :
    xs.firstM f = if Boot.objectId ∈ xs then some v else none := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.firstM, hp a (by simp)]
    by_cases ha : a = Boot.objectId
    · subst a; simp
    · have ht := ih (fun j hj => hp j (List.mem_cons_of_mem a hj))
      simp [ha, ht, Ne.symm ha]

theorem const_from_old_fresh {k : ObjId} (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true) (hk : k < m.heap.objs.size)
    (hp : constLookupFrom m.heap k name = none) :
    constLookupFrom h₁ k name =
      if Boot.objectId ∈ ancestors m.heap k then some (.ref m.heap.objs.size) else none := by
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ hc.boot.2.2.2.2
  rw [const_from_eq_firstM] at hp
  rw [const_from_eq_firstM, ancestors_old hc hs hd hk]
  apply firstM_registered
  intro j hj
  have hjl := ancestors_mem_lt hc hk j hj
  rw [constOwn_old hd hjl, htop]
  by_cases he : j = Boot.objectId
  · subst j
    rw [constOwn_constSetIn_self ho hc.boot.2.2.2.2]
    simp
  · rw [constOwn_constSetIn_ne _ _ _ _ _ _ (Or.inl he), firstM_absent hp j hj]
    simp [he]

theorem instance_constants_old {κ : Ctx} {cn : String} {k : ObjId}
    (site : InstanceSite κ cn k m.heap) (hc : ClassReady m.heap) (hs : Saturated m.heap)
    (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none)
    (hmain : ∀ n, constLookupFrom m.heap Boot.objectId n = constLookup m.heap n)
    (hreach : Boot.objectId ∈ ancestors m.heap k ∨ (m.heap.classPayload? k).any (·.isModule) = true) :
    ∀ n, instanceConstResolve h₁ k n = constLookup h₁ n := by
  have hk := site.live
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ hc.chains.boot.2.2.2.2
  have hmod : ((h₁).classPayload? k).any (·.isModule) = (m.heap.classPayload? k).any (·.isModule) :=
    metadata_any_old hd hk (·.isModule) (fun _ => rfl)
  intro n
  by_cases he : n = name
  · subst n
    have heq := site.constants name
    rw [Subclass.const_eq_own, hn] at heq
    have hold : constOwn m.heap k name = none := by
      cases hv : constOwn m.heap k name with
      | none => rfl
      | some v => simp only [instanceConstResolve, List.firstM, hv] at heq; cases heq
    have hfrom : constLookupFrom m.heap k name = none := by
      cases hv : constLookupFrom m.heap k name with
      | none => rfl
      | some v =>
        simp only [instanceConstResolve, List.firstM, hold, Option.orElse_none, hv,
          Option.orElse_some] at heq
        cases heq
    have hown : constOwn h₁ k name = if k = Boot.objectId then some (.ref m.heap.objs.size) else none := by
      rw [constOwn_old hd hk, htop]
      by_cases hko : k = Boot.objectId
      · subst k; rw [constOwn_constSetIn_self ho hc.chains.boot.2.2.2.2]; simp
      · rw [constOwn_constSetIn_ne _ _ _ _ _ _ (Or.inl hko), hold]; simp [hko]
    rw [instanceConstResolve, const_self htop ho]
    by_cases hko : k = Boot.objectId
    · simp only [List.firstM, hown, if_pos hko]; rfl
    · simp only [List.firstM, hown, hko, ite_false, show (failure : Option Value) = none from rfl,
        Option.orElse_none, show (none <|> (none : Option Value)) = none from rfl,
        const_from_old_fresh hc.chains hs htop ho hk hfrom, hmod]
      rcases hreach with hr | hr
      · simp only [if_pos hr]; rfl
      · rw [hr]
        rw [main_constants hc hs htop ho hmain, const_self htop ho]
        split <;> rfl
  · unfold instanceConstResolve
    simp only [List.firstM]
    rw [constOwn_other htop hc.chains.boot.2.2.2.2 hk he]
    rw [const_from_old_other hc.chains hs htop hk he]
    rw [const_from_old_other hc.chains hs htop hc.chains.boot.2.2.2.2 he]
    rw [hmod, const_other htop hc.chains.boot.2.2.2.2 he]
    exact site.constants n

/-- The existing declared chain supplies reachability once static ancestry resolves. -/
theorem instance_object_reach {C : CTable} {c : Cls} {k : ObjId} {ns : List String}
    (hp : ClassChains C m.heap) (hr : RootNames m.heap) (hc : c ∈ C)
    (hk : classNamed? m.heap c.name = some k) (hkind : c.isModule = false)
    (ha : Checker.ancestors? C c.name = some ns) : Boot.objectId ∈ ancestors m.heap k := by
  obtain ⟨before, he, _⟩ := hp.root_tail hr hc hk hkind ha
  rw [he]
  exact List.mem_append_right _ (by simp [rootIds])

#print axioms instance_constants_old
#print axioms instance_object_reach
end Checker.Soundness.FreshClassActual
