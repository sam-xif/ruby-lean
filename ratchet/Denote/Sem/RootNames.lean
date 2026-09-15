import Denote.Sem.ConstLive

/-! The nominal root tail used by declared classes: canonical bindings and no unlisted
global aliases of the three physical root ids. Primitive ancestor rows do not imply this. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

def rootNameIds : List (String × ObjId) :=
  [("Object", Boot.objectId), ("Kernel", Boot.kernelId), ("BasicObject", Boot.basicObjectId)]
def rootIds : List ObjId := [Boot.objectId, Boot.kernelId, Boot.basicObjectId]

structure RootNames (h : Heap) : Prop where
  named : ∀ cn k, (cn, k) ∈ rootNameIds → classNamed? h cn = some k
  only : ∀ cn k, classNamed? h cn = some k → k ∈ rootIds → cn ∈ rootAncestors

def rootNamesB (h : Heap) : Bool :=
  rootNameIds.all (fun p => classNamed? h p.1 == some p.2) &&
    (h.classPayload? Boot.objectId).all (fun cp => cp.consts.all (fun (cn, v) =>
      match v with
      | .ref k => !rootIds.contains k || rootAncestors.contains cn
      | _ => true))

theorem rootNamesB_sound {h : Heap} (hb : rootNamesB h = true) : RootNames h := by
  simp only [rootNamesB, Bool.and_eq_true] at hb
  obtain ⟨hn, ha⟩ := hb
  refine ⟨fun cn k hk => beq_iff_eq.mp (List.all_eq_true.mp hn (cn, k) hk), ?_⟩
  intro cn k hk hr
  have hv := classNamed_constOwn hk
  cases hp : h.classPayload? Boot.objectId with
  | none => simp [constOwn, hp] at hv
  | some cp =>
    simp only [hp, Option.all_some, List.all_eq_true] at ha
    simp only [constOwn, hp, Option.bind_some] at hv
    cases hf : cp.consts.find? (·.1 == cn) with
    | none => simp [hf] at hv
    | some p =>
      have hn : p.1 = cn := by simpa using List.find?_some hf
      have hv' : p.2 = .ref k := by simpa only [hf, Option.map_some, Option.some.injEq] using hv
      have hb := ha p (List.mem_of_find?_eq_some hf)
      simpa only [hv', hn, List.contains_iff_mem.mpr hr, Bool.not_true, Bool.false_or,
        List.contains_iff_mem] using hb

theorem RootNames.transport {h h' : Heap} (hc : RootNames h)
    (he : ∀ cn, classNamed? h' cn = classNamed? h cn) : RootNames h' :=
  ⟨fun cn k hk => (he cn).trans (hc.named cn k hk),
    fun cn k hk hr => hc.only cn k ((he cn).symm ▸ hk) hr⟩

theorem RootNames.live {h : Heap} (hc : RootNames h) (hl : ConstRefsLive h)
    {k : ObjId} (hk : k ∈ rootIds) : k < h.objs.size := by
  have hm : k ∈ rootNameIds.map (·.2) := hk
  obtain ⟨⟨cn, j⟩, hj, rfl⟩ := List.mem_map.mp hm
  exact hl cn j (classNamed_constOwn (hc.named cn j hj))

theorem RootNames.ext {m n : Machine} (hc : RootNames m.heap) (he : Ext m n) : RootNames n.heap :=
  hc.transport he.classNamed?_eq

theorem RootNames.defineMethod {h : Heap} {cls : ObjId} {name : String} {md : MethodDef}
    (hc : RootNames h) : RootNames (defineMethod h cls name md) :=
  hc.transport (by
    intro cn
    have hl (g : Heap) : constLookup g cn = constOwn g Boot.objectId cn := by
      cases hp : g.classPayload? Boot.objectId <;> simp [constLookup, constOwn, hp]
    simp only [classNamed?, hl, Proof.constOwn_defineMethod, Proof.classPayload?_isSome_defineMethod])

theorem RootNames.ivarOnly {h h' : Heap} (hc : RootNames h) (hi : Proof.IvarOnly h h') : RootNames h' :=
  hc.transport (by intro cn; simp only [classNamed?, constLookup, hi.classPayload])

#print axioms rootNamesB_sound
end Ratchet.Denote
