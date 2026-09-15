import RubyCore.Proof.Judgment.ModFresh

/-! Class-allocating growth: old edges and walks are reused once, while producers
describe only the fresh ids. These heap contracts do not accept a program or a body. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore RubyCore.Proof RubyCore.Proof.Judgment

theorem chainsIn_of_clsGrow {h h' : Heap} (hg : ClsGrow h h') (hc : ChainsIn h)
    (hk : ∀ o, h.objs.size ≤ o → o < h'.objs.size → (h'.get o).klass < h'.objs.size)
    (he : ∀ o, h.objs.size ≤ o → o < h'.objs.size →
      ∀ e, (h'.get o).eigen = some e → e < h'.objs.size)
    (hp : ∀ o cp, h.objs.size ≤ o → o < h'.objs.size → h'.classPayload? o = some cp →
      (∀ s, cp.superclass = some s → s < h'.objs.size) ∧
      (∀ i ∈ cp.includes, i < h'.objs.size) ∧ (∀ p ∈ cp.prepends, p < h'.objs.size)) :
    ChainsIn h' := by
  have hb {k : ObjId} (hl : k < h.objs.size) : k < h'.objs.size := Nat.lt_of_lt_of_le hl hg.size
  refine ⟨⟨hb hc.boot.1, hb hc.boot.2.1, hb hc.boot.2.2.1,
    hb hc.boot.2.2.2.1, hb hc.boot.2.2.2.2⟩, ?_, ?_, ?_⟩
  · intro o ho
    by_cases hl : o < h.objs.size
    · rw [hg.get o hl]; exact hb (hc.klass o hl)
    · exact hk o (Nat.le_of_not_lt hl) ho
  · intro o ho e he'
    by_cases hl : o < h.objs.size
    · rw [hg.get o hl] at he'; exact hb (hc.eigen o hl e he')
    · exact he o (Nat.le_of_not_lt hl) ho e he'
  · intro o cp ho hp'
    by_cases hl : o < h.objs.size
    · rw [hg.payloadOld hl] at hp'
      obtain ⟨hs, hi, hp⟩ := hc.chain o cp hl hp'
      exact ⟨fun s h => hb (hs s h), fun i h => hb (hi i h), fun p h => hb (hp p h)⟩
    · exact hp o cp (Nat.le_of_not_lt hl) ho hp'

/-- Fresh singleton module walks and class heads leading into the old heap preserve
both fuel saturations. At least two new slots leave one step of slack for the new head. -/
theorem saturated_of_clsGrow_heads {h h' : Heap} (hg : ClsGrow h h')
    (hc : ChainsIn h) (hs : Saturated h) (hz : h.objs.size + 2 ≤ h'.objs.size)
    (hm : ∀ k, h.objs.size ≤ k → k < h'.objs.size →
      ∀ f, modAncestors.go h' k (f + 1) = [k])
    (ha : ∀ k, h.objs.size ≤ k → k < h'.objs.size →
      ∃ p, p < h.objs.size ∧ ∀ f, ancestors.go h' k (f + 1) = k :: ancestors.go h' p f) :
    Saturated h' := by
  have hz' : h'.objs.size = (h'.objs.size - 1) + 1 := by omega
  constructor
  · intro k
    by_cases hk : k < h.objs.size
    · rw [ClsGrow.modAncestors_go_old hg hc _ k hk,
        ClsGrow.modAncestors_go_old hg hc _ k hk,
        modAncestors_go_ge hs.1 (by omega : h.objs.size + 1 ≤ h'.objs.size + 1),
        modAncestors_go_ge hs.1 (by omega : h.objs.size + 1 ≤ h'.objs.size)]
    · by_cases hl : k < h'.objs.size
      · rw [hm k (Nat.le_of_not_lt hk) hl, hz', hm k (Nat.le_of_not_lt hk) hl]
      · rw [modanc_go_oob hl, hz', modanc_go_oob hl]
  · intro k
    by_cases hk : k < h.objs.size
    · rw [ClsGrow.ancestors_go_old hg hc hs _ k hk,
        ClsGrow.ancestors_go_old hg hc hs _ k hk,
        ancestors_go_ge hs.2 (by omega : h.objs.size + 1 ≤ h'.objs.size + 1),
        ancestors_go_ge hs.2 (by omega : h.objs.size + 1 ≤ h'.objs.size)]
    · by_cases hl : k < h'.objs.size
      · obtain ⟨p, hp, hstep⟩ := ha k (Nat.le_of_not_lt hk) hl
        rw [hstep, hz', hstep]
        congr 1
        rw [ClsGrow.ancestors_go_old hg hc hs _ p hp,
          ClsGrow.ancestors_go_old hg hc hs _ p hp,
          ancestors_go_ge hs.2 (by omega : h.objs.size + 1 ≤ (h'.objs.size - 1) + 1),
          ancestors_go_ge hs.2 (by omega : h.objs.size + 1 ≤ h'.objs.size - 1)]
      · rw [anc_go_oob hl, hz', anc_go_oob hl]

#print axioms chainsIn_of_clsGrow
#print axioms saturated_of_clsGrow_heads
end Ratchet.Denote
