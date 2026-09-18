import Ratchet.Guards.ClassHeader
import Denote.Sem.Names.NamedChain
import Denote.Ty.Ext

/-! Declared ancestry describes the complete ordered physical chain. An unknown static
chain grants no claim; inherited lookup must first resolve it successfully. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

def ClassChains (C : CTable) (h : Heap) : Prop :=
  ∀ c ∈ C, ∀ k, classNamed? h c.name = some k → ∀ ns,
    ancestors? C c.name = some ns → NamedChain h (ns ++ rootAncestors) (ancestors h k)

def classChainsB (C : CTable) (h : Heap) : Bool :=
  C.all fun c => (classNamed? h c.name).all fun k =>
    (ancestors? C c.name).all fun ns => namedChainB h (ns ++ rootAncestors) (ancestors h k)

theorem classChainsB_sound {C : CTable} {h : Heap} (hp : classChainsB C h = true) :
    ClassChains C h := by
  intro c hc k hk ns hns
  have hb := List.all_eq_true.mp hp c hc
  rw [hk, hns] at hb
  exact namedChainB_sound hb

theorem ClassChains.empty (h : Heap) : ClassChains [] h := by
  intro c hc; cases hc

theorem ClassChains.owner_named {C : CTable} {h : Heap} {c : Cls} {k owner : ObjId}
    {ns : List String} (hp : ClassChains C h) (hc : c ∈ C)
    (hk : classNamed? h c.name = some k) (hn : ancestors? C c.name = some ns)
    (ho : owner ∈ ancestors h k) : ∃ cn ∈ ns ++ rootAncestors, classNamed? h cn = some owner :=
  (hp c hc k hk ns hn).cover ho

theorem ClassChains.heap {C : CTable} {h h' : Heap} (hp : ClassChains C h)
    (hn : ∀ cn, classNamed? h' cn = classNamed? h cn)
    (ha : ∀ k, ancestors h' k = ancestors h k) : ClassChains C h' := by
  intro c hc k hk ns hns
  rw [hn] at hk
  rw [ha]
  exact (hp c hc k hk ns hns).names (fun cn _ he => (hn cn).trans he)

theorem ClassChains.ext {C : CTable} {m n : Machine} (hp : ClassChains C m.heap)
    (he : Ext m n) : ClassChains C n.heap := hp.heap he.classNamed?_eq he.ancestors

theorem ClassChains.publish_member {C : CTable} {h : Heap} {c : Cls} {d : Defn}
    (hp : ClassChains C h) (hc : c ∈ C) (ht : DeclLookupFrame C (classWithMethod c d :: C)) :
    ClassChains (classWithMethod c d :: C) h := by
  intro old hold k hk ns hns
  rcases List.mem_cons.mp hold with rfl | hold
  · exact hp c hc k hk ns (ht.chain c hc ns hns)
  · exact hp old hold k hk ns (ht.chain old hold ns hns)

theorem ClassChains.publish_header {C : CTable} {h : Heap} {name : String}
    (hp : ClassChains C h) (ht : HeaderTableFrame C name)
    (hn : ∀ k, classNamed? h name = some k → NamedChain h (name :: rootAncestors) (ancestors h k)) :
    ClassChains (classHeader name :: C) h := by
  intro old hold k hk ns hns
  rcases List.mem_cons.mp hold with rfl | hold
  · change ancestors? (classHeader name :: C) name = some ns at hns
    rw [classHeader_ancestors] at hns
    cases hns
    exact hn k hk
  · exact hp old hold k hk ns (ht.chain old hold ns hns)

end Ratchet.Denote
