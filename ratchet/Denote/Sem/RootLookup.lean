import Denote.Sem.InheritedLookup
import Ratchet.MemberRoute

/-! A declared-chain absence test reduces actual dispatch to the implicit root tail.
The remaining root lookup is explicit: an empty class table never certifies Object's code. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

theorem RootNames.namedChain {h : Heap} (hr : RootNames h) : NamedChain h rootAncestors rootIds :=
  ⟨hr.named "Object" Boot.objectId (by simp [rootNameIds]),
    hr.named "Kernel" Boot.kernelId (by simp [rootNameIds]),
    hr.named "BasicObject" Boot.basicObjectId (by simp [rootNameIds]), trivial⟩

theorem ClassChains.root_tail {C : CTable} {h : Heap} {c : Cls} {r : ObjId} {ns : List String}
    (hp : ClassChains C h) (hr : RootNames h) (hc : c ∈ C)
    (hk : classNamed? h c.name = some r) (ha : ancestors? C c.name = some ns) :
    ∃ before, ancestors h r = before ++ rootIds ∧ NamedChain h ns before := by
  obtain ⟨before, after, he, hb, ht⟩ := (hp c hc r hk ns ha).split_append
  exact ⟨before, by rw [he, ht.unique hr.namedChain], hb⟩

theorem StateOk.methodOn_root_of_absent {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {c : Cls} {r : ObjId} {name : String} (hm : StateOk κ Γ I m) (hc : c ∈ κ.classes)
    (hk : classNamed? m.heap c.name = some r)
    (hn : noDeclaredSelectorB κ.classes c.name name = true) :
    Interp.methodOn m.heap r name = Interp.methodOn m.heap Boot.objectId name := by
  cases ha : ancestors? κ.classes c.name with
  | none => simp [noDeclaredSelectorB, ha] at hn
  | some ns =>
    have hp : prefixClearB κ.classes ns name = true := by simpa [noDeclaredSelectorB, ha] using hn
    obtain ⟨before, he, hb⟩ := hm.classChains.root_tail hm.core.rootNames hc hk ha
    rw [methodOn_eq_go, methodOn_eq_go, he, hm.core.classReady.objectChain]
    apply lookup_go_skip
    intro j hj
    obtain ⟨cn, hcn, hnamed⟩ := hb.cover hj
    obtain ⟨old, hold, ho, hmiss⟩ := prefixClearB_sound hp cn hcn
    exact hm.ownMethod_absent hold (by simpa only [ho] using hnamed) (by simpa only [ho] using hmiss)

theorem StateOk.userInit_eq_root {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {c : Cls} {r : ObjId} (hm : StateOk κ Γ I m) (hc : c ∈ κ.classes)
    (hk : classNamed? m.heap c.name = some r)
    (hn : noDeclaredSelectorB κ.classes c.name "initialize" = true) :
    Interp.userInit? m.heap r = Interp.userInit? m.heap Boot.objectId := by
  simp only [Interp.userInit?, hm.methodOn_root_of_absent hc hk hn]

theorem StateOk.userInit_none {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {c : Cls} {r : ObjId} (hm : StateOk κ Γ I m) (hc : c ∈ κ.classes)
    (hk : classNamed? m.heap c.name = some r)
    (hn : noDeclaredSelectorB κ.classes c.name "initialize" = true)
    (hr : rootInitFreeB κ.defs = true) : Interp.userInit? m.heap r = none :=
  (hm.userInit_eq_root hc hk hn).trans (hm.rootInit hr)

#print axioms StateOk.methodOn_root_of_absent
#print axioms StateOk.userInit_eq_root
#print axioms StateOk.userInit_none
end Ratchet.Denote
