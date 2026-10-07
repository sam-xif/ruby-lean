import Books.TypeSoundness.Conformance.Names.RootLookup
import Checker.Guards.ClassGuards

/-! Discharge old-site Object reachability from the static ancestry guard. -/
set_option autoImplicit false
namespace Checker.Soundness
open RubyCore Checker

theorem StateOk.classReach {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} (hm : StateOk κ Γ I m)
    (hg : classReachB κ.classes = true) :
    ∀ cn ∈ κ.classes.map (·.name), ∀ k, InstanceSite κ cn k m.heap →
      Boot.objectId ∈ ancestors m.heap k ∨ (m.heap.classPayload? k).any (·.isModule) = true := by
  intro cn hcn k site
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcn
  have hrow := List.all_eq_true.mp hg c hc
  cases hmod : c.isModule with
  | false =>
    simp only [hmod, Bool.false_or] at hrow
    obtain ⟨ns, hns⟩ := Option.isSome_iff_exists.mp hrow
    obtain ⟨before, ha, _⟩ := hm.classChains.root_tail hm.core.rootNames hc site.named hmod hns
    left; rw [ha]; simp [rootIds]
  | true =>
    right
    have hd := (hm.declCls c hc k site.named).2.2.2.1
    rw [hmod] at hd
    cases hp : m.heap.classPayload? k <;> simp_all

#print axioms StateOk.classReach
end Checker.Soundness
