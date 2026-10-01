import Ratchet.Static.All
import Denote.Ty.Local
import Denote.Sem.Instance.MainPrefix
import Denote.Sem.Instance.ClassHooks
import Denote.Sem.Heap.AllocationReady

/-! Runtime facts required by ordinary top-level definitions and calls. The context
explicitly requests this world; unrestricted contexts do not assume it. -/

set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

/-- Ordinary definitions retain the native no-op callback. The callback is still
queued by the mutation protocol; it is not an immediate definition transition. -/
def definitionHookQuietB (h : Heap) (k : ObjId) : Bool :=
  (lookup h (.ref k) "method_added").any fun (_, md) =>
    !md.undefined && md.builtin == some "Module#method_added"

def objectHookQuietB (h : Heap) : Bool := definitionHookQuietB h Boot.objectId

/-- The default used by ordinary `def`; `initialize` has its separate privacy override. -/
def defaultDefVis (m : Machine) : Visibility :=
  if m.currentFrame.kind == .toplevel then .priv else m.currentFrame.defVis

structure MainReady (m : Machine) : Prop where
  self : m.currentFrame.self = .ref Boot.mainId
  owner : m.currentFrame.defmod = Boot.objectId
  cref : m.currentFrame.cref = []
  captured : m.currentFrame.captured = none
  phase : m.preludeMode = false
  live : Boot.mainId < m.heap.objs.size
  payload : (m.heap.get Boot.mainId).payload = .none
  chain : ancestors m.heap (classOf m.heap (.ref Boot.mainId)) =
    [classOf m.heap (.ref Boot.mainId), Boot.objectId, Boot.kernelId, Boot.basicObjectId]
  object : isAName m.heap (.ref Boot.mainId) "Object" = true
  classLive : (m.heap.classPayload? Boot.objectId).isSome = true
  hook : objectHookQuietB m.heap = true
  detached : (m.heap.classPayload? Boot.objectId).bind (·.attached) = none
  unfrozen : (m.heap.get Boot.objectId).frozen = false
  origin : m.currentFrame.libraryOrigin = false
  mainNames : mainOwnNamesB m.heap = true
  classHooks : classHooksQuietB m.heap = true
  classFlags : objectClassFlagsB m.heap = true

def RuntimeOk (κ : Ctx) (m : Machine) : Prop := κ.scope.runtimeMain = true → MainReady m

theorem MainReady.objectWrite {m : Machine} (h : MainReady m) (name : String)
    (hc : ancestors m.heap Boot.objectId = [Boot.objectId, Boot.kernelId, Boot.basicObjectId]) :
    MainPrefixWriteOk m.heap Boot.objectId name := by
  apply Or.inl
  intro he
  have hs := h.chain
  rw [← he, hc] at hs
  have hl := congrArg List.length hs
  simp at hl

theorem MainReady.writable {m : Machine} (h : MainReady m) :
    frozenMethodReceiver? m.heap Boot.objectId = none := by
  simp only [frozenMethodReceiver?, h.detached, Option.getD_none, h.unfrozen,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte]

def mainReadyBaseB (m : Machine) : Bool :=
  decide (m.currentFrame.defmod = Boot.objectId ∧ m.currentFrame.cref = [] ∧
    m.currentFrame.captured = none ∧ m.preludeMode = false ∧ Boot.mainId < m.heap.objs.size) &&
  (match m.currentFrame.self with | .ref o => o == Boot.mainId | _ => false) &&
  (match (m.heap.get Boot.mainId).payload with | .none => true | _ => false) &&
  (ancestors m.heap (classOf m.heap (.ref Boot.mainId)) ==
    [classOf m.heap (.ref Boot.mainId), Boot.objectId, Boot.kernelId, Boot.basicObjectId]) &&
  isAName m.heap (.ref Boot.mainId) "Object" &&
  (m.heap.classPayload? Boot.objectId).isSome && objectHookQuietB m.heap

def mainReadyB (m : Machine) : Bool :=
  mainReadyBaseB m &&
    decide ((m.heap.classPayload? Boot.objectId).bind (·.attached) = none) &&
    !(m.heap.get Boot.objectId).frozen && !m.currentFrame.libraryOrigin && mainOwnNamesB m.heap && classHooksQuietB m.heap && objectClassFlagsB m.heap

theorem mainReadyB_sound {m : Machine} (h : mainReadyB m = true) : MainReady m := by
  simp only [mainReadyB, mainReadyBaseB, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨h, hflags⟩ := h
  obtain ⟨h, hhooks⟩ := h
  obtain ⟨h, hprefix⟩ := h
  obtain ⟨h, horigin⟩ := h
  obtain ⟨h, hd, hf⟩ := (and_assoc.mp h)
  obtain ⟨⟨⟨⟨⟨⟨⟨ho, hc, hcap, hphase, hlive⟩, hs⟩, hp⟩, ha⟩, hi⟩, hcl⟩, hh⟩ := h
  refine ⟨?_, ho, hc, hcap, hphase, hlive, ?_, ha, hi, hcl, hh, hd, hf, horigin, hprefix, hhooks, hflags⟩
  · cases he : m.currentFrame.self <;> simp_all
  · cases he : (m.heap.get Boot.mainId).payload <;> simp_all

theorem MainReady.reframe {m n : Machine} (h : MainReady m)
    (hh : n.heap = m.heap) (hs : n.currentFrame.self = m.currentFrame.self)
    (ho : n.currentFrame.defmod = m.currentFrame.defmod)
    (hc : n.currentFrame.cref = m.currentFrame.cref)
    (hcap : n.currentFrame.captured = m.currentFrame.captured)
    (hphase : n.preludeMode = m.preludeMode)
    (horigin : n.currentFrame.libraryOrigin = m.currentFrame.libraryOrigin) : MainReady n :=
  ⟨hs.trans h.self, ho.trans h.owner, hc.trans h.cref, hcap.trans h.captured,
    hphase.trans h.phase, by simpa only [hh] using h.live,
    by simpa only [hh] using h.payload, by simpa only [hh] using h.chain,
    by simpa only [hh] using h.object, by simpa only [hh] using h.classLive,
    by simpa only [hh] using h.hook,
    by simpa only [hh] using h.detached, by simpa only [hh] using h.unfrozen,
    horigin.trans h.origin, by simpa only [hh] using h.mainNames, by simpa only [hh] using h.classHooks, by simpa only [hh] using h.classFlags⟩

theorem MainReady.setLocal {m : Machine} (h : MainReady m) (x : String) (v : Value) :
    MainReady (m.setLocal x v) :=
  h.reframe (setLocal_heap ..) (currentFrame_setLocal_self ..)
    (currentFrame_setLocal_defmod ..) (currentFrame_setLocal_cref ..)
    (currentFrame_setLocal_captured ..) rfl (currentFrame_setLocal_libraryOrigin ..)

theorem MainReady.ext {m n : Machine} (h : MainReady m) (he : Ext m n)
    (hphase : n.preludeMode = m.preludeMode) (hc : Proof.ChainsIn m.heap) : MainReady n := by
  have hmain := he.get Boot.mainId h.live
  have hobj := he.get Boot.objectId (Nat.lt_trans (by decide) h.live)
  have hlookup : lookup n.heap (.ref Boot.objectId) "method_added" =
      lookup m.heap (.ref Boot.objectId) "method_added" := by
    change Interp.methodOn n.heap (classOf n.heap (.ref Boot.objectId)) "method_added" =
      Interp.methodOn m.heap (classOf m.heap (.ref Boot.objectId)) "method_added"
    simp only [classOf, hobj, he.methodOn_eq hc]
  refine ⟨by rw [he.currentFrame_eq]; exact h.self,
    by rw [he.currentFrame_eq]; exact h.owner,
    by rw [he.currentFrame_eq]; exact h.cref,
    by rw [he.currentFrame_eq]; exact h.captured,
    hphase.trans h.phase, Nat.lt_of_lt_of_le h.live he.size,
    by rw [hmain]; exact h.payload, ?_, he.isAName_mono h.object,
    by rw [he.payload]; exact h.classLive, ?_,
    by rw [he.payload]; exact h.detached,
    by rw [hobj]; exact h.unfrozen,
    by rw [he.currentFrame_eq]; exact h.origin, ?_, ?_, ?_⟩
  · simpa only [classOf, hmain, he.ancestors] using h.chain
  · simpa only [objectHookQuietB, definitionHookQuietB, hlookup] using h.hook
  · simpa only [mainOwnNamesB, ownMethods, classOf, hmain, he.payload] using h.mainNames

  · rw [classHooksQuietB_congr (h := m.heap)
      (by simp only [objectCallbackPrefix, classOf, hobj, he.ancestors])
      (fun name k _ => by rw [he.payload])]
    exact h.classHooks
  · simpa only [objectClassFlagsB, he.payload] using h.classFlags

#print axioms mainReadyB_sound
#print axioms MainReady.ext
example (m : Machine) : ¬ MainReady { m with preludeMode := true } := by
  intro h; cases h.phase
end Ratchet.Denote
