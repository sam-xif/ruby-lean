import Denote.Ty.Val

/-! Ordered correspondence between declared names and every physical lookup owner.
Unlike named membership, this excludes unnamed insertions and changed order. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

def NamedChain (h : Heap) : List String → List ObjId → Prop
  | [], [] => True
  | cn :: ns, k :: ks => classNamed? h cn = some k ∧ NamedChain h ns ks
  | _, _ => False

def namedChainB (h : Heap) : List String → List ObjId → Bool
  | [], [] => true
  | cn :: ns, k :: ks => classNamed? h cn == some k && namedChainB h ns ks
  | _, _ => false

theorem namedChainB_sound {h : Heap} {ns : List String} {ks : List ObjId}
    (hp : namedChainB h ns ks = true) : NamedChain h ns ks := by
  induction ns generalizing ks with
  | nil => cases ks <;> simp_all [namedChainB, NamedChain]
  | cons cn ns ih =>
    cases ks with
    | nil => cases hp
    | cons k ks =>
      simp only [namedChainB, Bool.and_eq_true, beq_iff_eq] at hp
      exact ⟨hp.1, ih hp.2⟩

theorem NamedChain.names {h h' : Heap} {ns : List String} {ks : List ObjId}
    (hp : NamedChain h ns ks)
    (hn : ∀ cn k, classNamed? h cn = some k → classNamed? h' cn = some k) :
    NamedChain h' ns ks := by
  induction ns generalizing ks with
  | nil => cases ks <;> exact hp
  | cons cn ns ih =>
    cases ks with
    | nil => cases hp
    | cons k ks => exact ⟨hn cn k hp.1, ih hp.2⟩

theorem NamedChain.cover {h : Heap} {ns : List String} {ks : List ObjId}
    (hp : NamedChain h ns ks) {k : ObjId} (hk : k ∈ ks) :
    ∃ cn ∈ ns, classNamed? h cn = some k := by
  induction ns generalizing ks with
  | nil => cases ks with
    | nil => cases hk
    | cons _ _ => cases hp
  | cons cn ns ih =>
    cases ks with
    | nil => cases hk
    | cons j js =>
      rcases List.mem_cons.mp hk with rfl | hk
      · exact ⟨cn, List.mem_cons_self, hp.1⟩
      · obtain ⟨n, hn, he⟩ := ih hp.2 hk
        exact ⟨n, List.mem_cons_of_mem cn hn, he⟩

theorem NamedChain.split {h : Heap} {pre post : List String} {cn : String} {ks : List ObjId}
    (hp : NamedChain h (pre ++ cn :: post) ks) :
    ∃ before k after, ks = before ++ k :: after ∧ NamedChain h pre before ∧
      classNamed? h cn = some k ∧ NamedChain h post after := by
  induction pre generalizing ks with
  | nil =>
    cases ks with
    | nil => cases hp
    | cons k ks => exact ⟨[], k, ks, rfl, trivial, hp.1, hp.2⟩
  | cons n ns ih =>
    cases ks with
    | nil => cases hp
    | cons j js =>
      obtain ⟨before, k, after, he, hpre, hk, hpost⟩ := ih hp.2
      exact ⟨j :: before, k, after, by simp only [List.cons_append, he],
        ⟨hp.1, hpre⟩, hk, hpost⟩

theorem NamedChain.unique {h : Heap} {ns : List String} {ks js : List ObjId}
    (hk : NamedChain h ns ks) (hj : NamedChain h ns js) : ks = js := by
  induction ns generalizing ks js with
  | nil => cases ks <;> cases js <;> simp_all [NamedChain]
  | cons cn ns ih =>
    cases ks with
    | nil => cases hk
    | cons k ks =>
      cases js with
      | nil => cases hj
      | cons j js =>
        have he := Option.some.inj (hk.1.symm.trans hj.1)
        simp only [he, ih hk.2 hj.2]

theorem NamedChain.split_append {h : Heap} {pre post : List String} {ks : List ObjId}
    (hp : NamedChain h (pre ++ post) ks) :
    ∃ before after, ks = before ++ after ∧ NamedChain h pre before ∧ NamedChain h post after := by
  induction pre generalizing ks with
  | nil => exact ⟨[], ks, rfl, trivial, hp⟩
  | cons cn pre ih =>
    cases ks with
    | nil => cases hp
    | cons k ks =>
      obtain ⟨before, after, he, hb, ha⟩ := ih hp.2
      exact ⟨k :: before, after, by simp only [List.cons_append, he], ⟨hp.1, hb⟩, ha⟩

end Ratchet.Denote
