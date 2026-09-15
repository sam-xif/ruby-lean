import Denote.Sem.ClassNew

/-! The top-level receiver's heap obligations must outlive its activation.
This view has a fixed frame; it is not an execution or an admission route. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

def mainView (h : Heap) : Machine :=
  { (default : Machine) with
    heap := h
    preludeMode := false
    frames := #[{
      self := .ref Boot.mainId
      defmod := Boot.objectId
      cref := [Boot.objectId]
      kind := .toplevel }]
    stack := [0] }

theorem MainReady.view {m : Machine} (h : MainReady m) : MainReady (mainView m.heap) :=
  ⟨rfl, rfl, rfl, rfl, rfl, h.live, h.payload, h.chain, h.object, h.classLive, h.hook⟩

theorem MainReady.of_view {m : Machine} (h : MainReady (mainView m.heap))
    (hs : m.currentFrame.self = .ref Boot.mainId)
    (ho : m.currentFrame.defmod = Boot.objectId) (hc : m.currentFrame.cref = [Boot.objectId])
    (hcap : m.currentFrame.captured = none) (hp : m.preludeMode = false) : MainReady m :=
  ⟨hs, ho, hc, hcap, hp, h.live, h.payload, h.chain, h.object, h.classLive, h.hook⟩

def mainConstResolve (h : Heap) (n : String) : Option Value :=
  (constOwn h Boot.objectId n).orElse (fun _ => constLookupFrom h Boot.objectId n)

structure MainSiteAt (free : String → Bool) (h : Heap) : Prop where
  ready : MainReady (mainView h)
  names : ∀ n ∈ shadowableNames, ∀ owner md,
    Interp.methodOn h (classOf h (.ref Boot.mainId)) n = some (owner, md) →
      md.builtin.isSome = true ∨ md.undefined = true ∨ free n = false
  bare : ∀ n, BareNameError n → free n = true → lookup h (.ref Boot.mainId) n = none
  missing : free "method_missing" = true → ∀ owner md,
    Interp.methodOn h (classOf h (.ref Boot.mainId)) "method_missing" = some (owner, md) →
      md.builtin.isSome = true
  constants : ∀ n, mainConstResolve h n = constLookup h n
  newDispatch : free "new" = true → NewDispatch h (classOf h (.ref Boot.objectId))

abbrev MainSite (κ : Ctx) := MainSiteAt (nameFreeN κ)

theorem MainSite.recontext {κ κ' : Ctx} {h : Heap} (site : MainSite κ h)
    (hn : ∀ n, nameFreeN κ n = false → nameFreeN κ' n = false) : MainSite κ' h := by
  have ht (n : String) (h : nameFreeN κ' n = true) : nameFreeN κ n = true := by
    cases he : nameFreeN κ n with
    | true => rfl
    | false => rw [hn n he] at h; cases h
  exact ⟨site.ready, fun n hm o md hl => (site.names n hm o md hl).imp id (Or.imp id (hn n)),
    fun n hb hf => site.bare n hb (ht n hf), fun hf => site.missing (ht _ hf), site.constants,
    fun hf => site.newDispatch (ht _ hf)⟩

theorem MainSite.ext {κ : Ctx} {m n : Machine} (site : MainSite κ m.heap) (he : Ext m n) :
    MainSite κ n.heap := by
  have hv : Ext (mainView m.heap) (mainView n.heap) :=
    { he with stack := rfl, frames := rfl }
  have hco : classOf n.heap (.ref Boot.mainId) = classOf m.heap (.ref Boot.mainId) := by
    simp only [classOf, he.get Boot.mainId site.ready.live]
  have hmo (name : String) :
      Interp.methodOn n.heap (classOf n.heap (.ref Boot.mainId)) name =
        Interp.methodOn m.heap (classOf m.heap (.ref Boot.mainId)) name := by
    simp only [Interp.methodOn, hco, he.payload, he.ancestors]
  have hl (name : String) : lookup n.heap (.ref Boot.mainId) name =
      lookup m.heap (.ref Boot.mainId) name := by
    have hg (ks : List ObjId) : lookup.go n.heap name ks = lookup.go m.heap name ks := by
      induction ks with
      | nil => rfl
      | cons k ks ih => simp only [lookup.go, he.payload, ih]
    simp only [lookup, hco, he.ancestors, hg]
  refine ⟨site.ready.ext hv rfl,
    fun name hm o md hmd => site.names name hm o md (by rwa [hmo] at hmd),
    fun name hb hf => (hl name).trans (site.bare name hb hf),
    fun hf o md hmd => site.missing hf o md (by rwa [hmo] at hmd), fun name => by
      simpa only [mainConstResolve, constOwn, constLookupFrom, constLookup, he.payload,
        he.ancestors] using site.constants name, ?_⟩
  intro hf
  have hc : classOf n.heap (.ref Boot.objectId) = classOf m.heap (.ref Boot.objectId) := by
    simp only [classOf, he.get Boot.objectId (lt_size_of_classPayload site.ready.classLive)]
  apply (site.newDispatch hf).transport
  · simp only [Interp.methodOn, hc, he.payload, he.ancestors]
  · simp only [Interp.methodOn, hc, he.payload, he.ancestors]
  · intro owner; simp only [hc, he.ancestors, Interp.crubyShadow, className, he.payload]

#print axioms MainSite.ext
end Ratchet.Denote
