import Ratchet.Judge
import Denote.Local

/-! Runtime facts required by ordinary top-level definitions and calls. The context
explicitly requests this world; unrestricted contexts do not assume it. -/

set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

def definitionHookQuietB (h : Heap) (k : ObjId) : Bool :=
  match lookup h (.ref k) "method_added" with
  | none => true
  | some (owner, md) => md.undefined || owner == Boot.objectId ||
      owner == Boot.kernelId || owner == Boot.basicObjectId

def objectHookQuietB (h : Heap) : Bool := definitionHookQuietB h Boot.objectId

/-- The default used by ordinary `def`; `initialize` has its separate privacy override. -/
def defaultDefVis (m : Machine) : Visibility :=
  if m.currentFrame.kind == .toplevel then .priv else m.currentFrame.defVis

structure MainReady (m : Machine) : Prop where
  self : m.currentFrame.self = .ref Boot.mainId
  owner : m.currentFrame.defmod = Boot.objectId
  cref : m.currentFrame.cref = [Boot.objectId]
  captured : m.currentFrame.captured = none
  phase : m.preludeMode = false
  live : Boot.mainId < m.heap.objs.size
  payload : (m.heap.get Boot.mainId).payload = .none
  chain : ancestors m.heap (classOf m.heap (.ref Boot.mainId)) =
    [Boot.objectId, Boot.kernelId, Boot.basicObjectId]
  object : isAName m.heap (.ref Boot.mainId) "Object" = true
  classLive : (m.heap.classPayload? Boot.objectId).isSome = true
  hook : objectHookQuietB m.heap = true

def RuntimeOk (κ : Ctx) (m : Machine) : Prop := κ.scope.runtimeMain = true → MainReady m

def mainReadyB (m : Machine) : Bool :=
  decide (m.currentFrame.defmod = Boot.objectId ∧ m.currentFrame.cref = [Boot.objectId] ∧
    m.currentFrame.captured = none ∧ m.preludeMode = false ∧ Boot.mainId < m.heap.objs.size) &&
  (match m.currentFrame.self with | .ref o => o == Boot.mainId | _ => false) &&
  (match (m.heap.get Boot.mainId).payload with | .none => true | _ => false) &&
  (ancestors m.heap (classOf m.heap (.ref Boot.mainId)) ==
    [Boot.objectId, Boot.kernelId, Boot.basicObjectId]) &&
  isAName m.heap (.ref Boot.mainId) "Object" &&
  (m.heap.classPayload? Boot.objectId).isSome && objectHookQuietB m.heap

theorem mainReadyB_sound {m : Machine} (h : mainReadyB m = true) : MainReady m := by
  simp only [mainReadyB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨ho, hc, hcap, hphase, hlive⟩, hs⟩, hp⟩, ha⟩, hi⟩, hcl⟩, hh⟩ := h
  refine ⟨?_, ho, hc, hcap, hphase, hlive, ?_, ha, hi, hcl, hh⟩
  · cases he : m.currentFrame.self <;> simp_all
  · cases he : (m.heap.get Boot.mainId).payload <;> simp_all

theorem MainReady.reframe {m n : Machine} (h : MainReady m)
    (hh : n.heap = m.heap) (hs : n.currentFrame.self = m.currentFrame.self)
    (ho : n.currentFrame.defmod = m.currentFrame.defmod)
    (hc : n.currentFrame.cref = m.currentFrame.cref)
    (hcap : n.currentFrame.captured = m.currentFrame.captured)
    (hphase : n.preludeMode = m.preludeMode) : MainReady n :=
  ⟨hs.trans h.self, ho.trans h.owner, hc.trans h.cref, hcap.trans h.captured,
    hphase.trans h.phase, by simpa only [hh] using h.live,
    by simpa only [hh] using h.payload, by simpa only [hh] using h.chain,
    by simpa only [hh] using h.object, by simpa only [hh] using h.classLive,
    by simpa only [hh] using h.hook⟩

theorem MainReady.setLocal {m : Machine} (h : MainReady m) (x : String) (v : Value) :
    MainReady (m.setLocal x v) :=
  h.reframe (setLocal_heap ..) (currentFrame_setLocal_self ..)
    (currentFrame_setLocal_defmod ..) (currentFrame_setLocal_cref ..)
    (currentFrame_setLocal_captured ..) rfl

theorem MainReady.ext {m n : Machine} (h : MainReady m) (he : Ext m n)
    (hphase : n.preludeMode = m.preludeMode) : MainReady n := by
  have hmain := he.get Boot.mainId h.live
  have hobj := he.get Boot.objectId (Nat.lt_trans (by decide) h.live)
  have hlookup : lookup n.heap (.ref Boot.objectId) "method_added" =
      lookup m.heap (.ref Boot.objectId) "method_added" := by
    have hg (ks : List ObjId) : lookup.go n.heap "method_added" ks =
        lookup.go m.heap "method_added" ks := by
      induction ks with
      | nil => rfl
      | cons k ks ih => simp only [lookup.go, he.payload, ih]
    simp only [lookup, classOf, hobj, he.ancestors, hg]
  refine ⟨by rw [he.currentFrame_eq]; exact h.self,
    by rw [he.currentFrame_eq]; exact h.owner,
    by rw [he.currentFrame_eq]; exact h.cref,
    by rw [he.currentFrame_eq]; exact h.captured,
    hphase.trans h.phase, Nat.lt_of_lt_of_le h.live he.size,
    by rw [hmain]; exact h.payload, ?_, he.isAName_mono h.object,
    by rw [he.payload]; exact h.classLive, ?_⟩
  · simpa only [classOf, hmain, he.ancestors] using h.chain
  · simpa only [objectHookQuietB, definitionHookQuietB, hlookup] using h.hook

#print axioms mainReadyB_sound
#print axioms MainReady.ext
example (m : Machine) : ¬ MainReady { m with preludeMode := true } := by
  intro h; cases h.phase
end Ratchet.Denote
