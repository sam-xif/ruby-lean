import Denote.Sem.Instance.ClassHooks

/-! `def self.x` queues singleton_method_added on the class object. Its native lives in
BasicObject, after Object in every metaclass chain, so a user definition anywhere on
Object's metaclass chain (or Module's, for modules) would run instead. The first own
entry on both chains must be the native; writes of that selector are excluded by name. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

def singletonHookName : String := "singleton_method_added"
def singletonHookBid : String := "BasicObject#singleton_method_added"

def singletonHookSites (h : Heap) : List ObjId := [classOf h (.ref Boot.objectId), Boot.moduleId]

def singletonHooksQuietB (h : Heap) : Bool :=
  (singletonHookSites h).all fun k =>
    (firstOwnMethod h (ancestors h k) singletonHookName).any fun md =>
      !md.undefined && !md.visibilityOnly && md.builtin == some singletonHookBid

/-- The class-scope fact consumed by a singleton definition's hook dispatch. -/
def singletonDefHookQuietB (h : Heap) (k : ObjId) : Bool :=
  (lookup h (.ref k) singletonHookName).any fun (_, md) =>
    !md.undefined && md.builtin == some singletonHookBid

theorem singletonHooksQuietB_congr {h h' : Heap}
    (hs : singletonHookSites h' = singletonHookSites h)
    (ha : ∀ k ∈ singletonHookSites h, ancestors h' k = ancestors h k)
    (hf : ∀ k ∈ singletonHookSites h, ∀ j ∈ ancestors h k,
      (h'.classPayload? j).bind (fun cp => (cp.methods.find? (·.1 == singletonHookName)).map (·.2)) =
      (h.classPayload? j).bind (fun cp => (cp.methods.find? (·.1 == singletonHookName)).map (·.2))) :
    singletonHooksQuietB h' = singletonHooksQuietB h := by
  unfold singletonHooksQuietB
  rw [hs]
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  apply forall_congr'
  intro k
  apply imp_congr_right
  intro hk
  rw [ha k hk, firstOwnMethod_congr (hf k hk)]

theorem singletonHooksQuietB_defineMethod {h : Heap} {cls : ObjId} {name : String}
    {md : MethodDef} (hn : singletonHookName ≠ name) :
    singletonHooksQuietB (defineMethod h cls name md) = singletonHooksQuietB h := by
  have hs : singletonHookSites (defineMethod h cls name md) = singletonHookSites h := by
    simp only [singletonHookSites, Proof.classOf_defineMethod]
  apply singletonHooksQuietB_congr hs (fun k _ => Proof.ancestors_defineMethod ..)
  intro k _ j _
  have row (g : Heap) :
      (g.classPayload? j).bind (fun cp => (cp.methods.find? (·.1 == singletonHookName)).map (·.2)) =
      ((g.classPayload? j).map (fun cp => (cp.methods.find? (·.1 == singletonHookName), cp.isModule))).bind
        (fun pair => pair.1.map (·.2)) := by
    cases g.classPayload? j <;> rfl
  rw [row, row, Proof.lookupFields_defineMethod _ _ _ _ _ _ hn]

theorem singletonHooksQuietB_methodOn {h : Heap} (hq : singletonHooksQuietB h = true)
    (hc : Proof.ChainsIn h) {k : ObjId} (hk : k ∈ singletonHookSites h) :
    ∃ owner md, Interp.methodOn h k singletonHookName = some (owner, md) ∧
      md.undefined = false ∧ md.builtin = some singletonHookBid := by
  have hh := List.all_eq_true.mp hq k hk
  cases hf : firstOwnMethod h (ancestors h k) singletonHookName with
  | none => simp only [hf, Option.any] at hh; cases hh
  | some md =>
    simp only [hf, Option.any, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hh
    have hb := Proof.ancestors_length_bound hc k
    obtain ⟨owner, he⟩ := firstOwnMethod_lookup_go (rest := []) (fuel := 2 * h.objs.size + 2)
      hf hh.1.2 (by omega)
    refine ⟨owner, md, ?_, hh.1.1, hh.2⟩
    simpa only [Interp.methodOn, lookupInChain, List.append_nil] using he

theorem singletonDefHookQuietB_of_methodOn {h : Heap} {k j : ObjId}
    (hco : classOf h (.ref k) = j)
    (hm : ∃ owner md, Interp.methodOn h j singletonHookName = some (owner, md) ∧
      md.undefined = false ∧ md.builtin = some singletonHookBid) :
    singletonDefHookQuietB h k = true := by
  obtain ⟨owner, md, hl, hu, hb⟩ := hm
  have he : lookup h (.ref k) singletonHookName = Interp.methodOn h j singletonHookName := by
    rw [← hco]; rfl
  simp [singletonDefHookQuietB, he, hl, hu, hb]

#print axioms singletonHooksQuietB_defineMethod
#print axioms singletonHooksQuietB_methodOn
end Ratchet.Denote
