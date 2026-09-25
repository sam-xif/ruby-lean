import Ratchet.Guards.ModuleHeader
import Denote.Sem.Module.ModuleReady

/-! A fresh module satisfies module metadata and ordered ancestry. This initial-table
publication does not yet establish full StateOk or preserve earlier declared rows. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshModule
open RubyCore Ratchet RubyCore.Proof RubyCore.Proof.Judgment

variable {h : Heap} {name : String}
local notation "h₁" => freshModHeap h Boot.objectId name name

theorem fresh_name_only (hc : ConstRefsLive h) (ho : Boot.objectId < h.objs.size)
    {cn : String} (hn : classNamed? h₁ cn = some h.objs.size) : cn = name := by
  by_cases hne : cn = name
  · exact hne
  exfalso
  have hn := classNamed_constOwn hn
  rw [constOwn_old_fresh ho ho,
    constOwn_constSetIn_ne _ _ _ _ _ _ (Or.inr hne)] at hn
  exact (Nat.lt_irrefl _) (hc cn h.objs.size hn)

theorem ordered_chain (ho : (h.classPayload? Boot.objectId).isSome = true) :
    NamedChain h₁ [name] (ancestors h₁ h.objs.size) := by
  rw [ancestors_fresh_k]
  exact ⟨named_new (lt_size_of_classPayload ho) ho, trivial⟩

theorem classChains_header (ho : (h.classPayload? Boot.objectId).isSome = true) :
    ClassChains [moduleHeader name] h₁ := by
  intro c hc k hk ns hns
  have he : c = moduleHeader name := List.mem_singleton.mp hc
  subst c
  change ancestors? [moduleHeader name] name = some ns at hns
  rw [moduleHeader_ancestors] at hns
  cases hns
  have he := Option.some.inj ((named_new (name := name) (lt_size_of_classPayload ho) ho).symm.trans hk)
  subst k
  exact ordered_chain ho

theorem declared_header {κ : Ctx} {m : Machine} (hc : ClassReady m.heap)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true) (ht : κ.classes = []) :
    DeclClassOk (moduleHeaderCtx κ name)
      { m with heap := freshModHeap m.heap Boot.objectId name name } := by
  intro c hmem k hk
  change c ∈ moduleHeader name :: κ.classes at hmem
  rw [ht] at hmem
  have he : c = moduleHeader name := List.mem_singleton.mp hmem
  subst c
  have he := Option.some.inj ((named_new (name := name) hc.chains.boot.2.2.2.2 ho).symm.trans hk)
  subst k
  refine ⟨by simp [moduleHeader], (Nat.ne_of_lt hc.chains.boot.1).symm,
    (Nat.ne_of_lt hc.chains.boot.2.1).symm, ?_, by simp [moduleHeader], ?_⟩
  · simp only [freshModHeap_cp_k, Option.map_some, moduleHeader]
  · intro ns hns _
    change ancestors? (moduleHeader name :: κ.classes) name = some ns at hns
    rw [moduleHeader_ancestors] at hns
    cases hns
    change (∀ cn ∈ [name], ∃ j, classNamed? _ cn = some j ∧ (ancestors _ _).contains j = true) ∧
      (∀ cn j, classNamed? _ cn = some j → (ancestors _ _).contains j = true → cn ∈ [name])
    rw [ancestors_fresh_k]
    constructor
    · intro cn hcn
      have he := List.mem_singleton.mp hcn
      subst cn
      exact ⟨m.heap.objs.size, named_new hc.chains.boot.2.2.2.2 ho, by simp⟩
    · intro cn j hcn hj
      have he : j = m.heap.objs.size := by simpa using hj
      subst j
      exact List.mem_singleton.mpr (fresh_name_only hc.constRefs hc.chains.boot.2.2.2.2 hcn)

#print axioms classChains_header
#print axioms declared_header
end Ratchet.Denote.FreshModule
