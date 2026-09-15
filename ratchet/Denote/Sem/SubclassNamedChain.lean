import Denote.Sem.SubclassDeclared

/-! Fresh ancestry prepends one class to the actual parent's complete chain. Retained
name/id correspondence and reverse membership are separate obligations, including aliases. -/
set_option autoImplicit false
namespace Ratchet.Denote.Subclass
open RubyCore Ratchet

variable {h : Heap} {name q : String} {parent eParent : ObjId} {ns : List String}
local notation "h₁" => heap h Boot.objectId name q parent eParent

theorem ordered_chain (hc : Proof.ChainsIn h) (hs : Proof.Saturated h)
    (ho : (h.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn h Boot.objectId name = none) (hl : parent < h.objs.size)
    (hp : NamedChain h ns (ancestors h parent)) :
    NamedChain h₁ (name :: ns) (ancestors h₁ h.objs.size) := by
  rw [ancestors_class hc hs hl]
  exact ⟨named_fresh ho,
    hp.names (fun _ _ hk => named hc.boot.2.2.2.2 hn hk)⟩

theorem named_chain (hc : ClassReady h) (hs : Proof.Saturated h)
    (ho : (h.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn h Boot.objectId name = none) (hl : parent < h.objs.size)
    (hpos : ∀ cn ∈ ns, ∃ k, classNamed? h cn = some k ∧ (ancestors h parent).contains k = true)
    (hneg : ∀ cn k, classNamed? h cn = some k → (ancestors h parent).contains k = true → cn ∈ ns) :
    (∀ cn ∈ name :: ns, ∃ k, classNamed? h₁ cn = some k ∧ (ancestors h₁ h.objs.size).contains k = true) ∧
    (∀ cn k, classNamed? h₁ cn = some k → (ancestors h₁ h.objs.size).contains k = true → cn ∈ name :: ns) := by
  constructor
  · intro cn hcn
    rcases List.mem_cons.mp hcn with rfl | hcn
    · exact ⟨h.objs.size, named_fresh ho,
        by simp only [ancestors_class hc.chains hs hl, List.contains_cons, beq_self_eq_true, Bool.true_or]⟩
    · obtain ⟨k, hk, ha⟩ := hpos cn hcn
      refine ⟨k, named hc.chains.boot.2.2.2.2 hn hk, ?_⟩
      rw [ancestors_class hc.chains hs hl]
      exact List.contains_iff_mem.mpr (List.mem_cons_of_mem _ (List.contains_iff_mem.mp ha))
  · intro cn k hk ha
    rw [ancestors_class hc.chains hs hl] at ha
    rcases List.mem_cons.mp (List.contains_iff_mem.mp ha) with rfl | hmem
    · rw [named_fresh_only hc.constRefs hc.chains.boot.2.2.2.2 hk]
      exact List.mem_cons_self
    · have hkl := Proof.ClsGrow.ancestors_mem_lt hc.chains hl k hmem
      exact List.mem_cons_of_mem _ (hneg cn k (named_old_back ho hkl hk) (List.contains_iff_mem.mpr hmem))

#print axioms ordered_chain
#print axioms named_chain
end Ratchet.Denote.Subclass
