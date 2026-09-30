import Denote.Sem.Instance.InstanceSite

/-! Fresh module objects inherit singleton dispatch from Module. Retain that base's
capabilities independently of Class/Object ancestry and of the current receiver (§F47). -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

def moduleHookQuietB (h : Heap) : Bool :=
  (Interp.methodOn h Boot.moduleId "method_added").any fun (_, md) =>
    !md.undefined && md.builtin == some "Module#method_added"

structure ModuleBaseAt (free : String → Bool) (h : Heap) : Prop where
  names : NamesAt free h Boot.moduleId
  hook : moduleHookQuietB h = true
  constants : ConstFallback h Boot.moduleId

abbrev ModuleBase (κ : Ctx) := ModuleBaseAt (nameFreeN κ)

def moduleBaseB (free : String → Bool) (h : Heap) : Bool :=
  namesAtB free h Boot.moduleId && moduleHookQuietB h && constFallbackB h Boot.moduleId

theorem moduleBaseB_sound {free : String → Bool} {h : Heap}
    (hb : moduleBaseB free h = true) : ModuleBaseAt free h := by
  simp only [moduleBaseB, Bool.and_eq_true] at hb
  exact ⟨namesAtB_sound hb.1.1, hb.1.2, constFallbackB_sound hb.2⟩

theorem ModuleBase.recontext {κ κ' : Ctx} {h : Heap} (hp : ModuleBase κ h)
    (hn : ∀ n, nameFreeN κ n = false → nameFreeN κ' n = false) : ModuleBase κ' h :=
  ⟨hp.names.recontext hn, hp.hook, hp.constants⟩

theorem ModuleBase.transport {κ : Ctx} {h h' : Heap} (hp : ModuleBase κ h)
    (hm : ∀ n, Interp.methodOn h' Boot.moduleId n = Interp.methodOn h Boot.moduleId n)
    (hc : ConstFallback h' Boot.moduleId) : ModuleBase κ h' :=
  ⟨fun n hn owner md hl => hp.names n hn owner md (by rwa [hm] at hl),
    by simpa only [moduleHookQuietB, hm] using hp.hook, hc⟩

theorem ModuleBase.ext {κ : Ctx} {m n : Machine} (hp : ModuleBase κ m.heap)
    (he : Ext m n) (hch : Proof.ChainsIn m.heap) : ModuleBase κ n.heap :=
  hp.transport (fun name => he.methodOn_eq hch Boot.moduleId name)
    (hp.constants.ext he)

theorem ModuleBase.ivarOnly {κ : Ctx} {h h' : Heap} (hp : ModuleBase κ h)
    (hi : Proof.IvarOnly h h') : ModuleBase κ h' :=
  hp.transport (fun name => by
    unfold Interp.methodOn
    rw [hi.ancestors_eq, hi.lookup_go_eq])
    (hp.constants.ivarOnly hi)

#print axioms moduleBaseB_sound
#print axioms ModuleBase.ext
#print axioms ModuleBase.ivarOnly
end Ratchet.Denote
