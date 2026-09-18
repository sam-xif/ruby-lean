import Denote.Sem.Instance.InstanceSite

/-! Global constant references denote allocated objects. Without this invariant allocation
can turn a previously non-class constant into an unadvertised alias of a fresh class. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

def ConstRefsLive (h : Heap) : Prop :=
  ∀ cn k, constOwn h Boot.objectId cn = some (.ref k) → k < h.objs.size

def constRefsLiveB (h : Heap) : Bool :=
  (h.classPayload? Boot.objectId).all fun cp => cp.consts.all fun (_, v) =>
    match v with
    | .ref k => k < h.objs.size
    | _ => true

theorem constRefsLiveB_sound {h : Heap} (hb : constRefsLiveB h = true) : ConstRefsLive h := by
  intro cn k hk
  cases hp : h.classPayload? Boot.objectId with
  | none => simp [constOwn, hp] at hk
  | some cp =>
    simp only [constRefsLiveB, hp, Option.all_some, List.all_eq_true] at hb
    simp only [constOwn, hp, Option.bind_some] at hk
    cases hf : cp.consts.find? (·.1 == cn) with
    | none => simp [hf] at hk
    | some p =>
      have hv : p.2 = .ref k := by simpa only [hf, Option.map_some, Option.some.injEq] using hk
      have hvb := hb p (List.mem_of_find?_eq_some hf)
      simpa only [hv, decide_eq_true_eq] using hvb

theorem ConstRefsLive.transport {h h' : Heap} (hc : ConstRefsLive h)
    (hs : h.objs.size ≤ h'.objs.size)
    (he : ∀ cn, constOwn h' Boot.objectId cn = constOwn h Boot.objectId cn) : ConstRefsLive h' := by
  intro cn k hk
  exact Nat.lt_of_lt_of_le (hc cn k ((he cn).symm ▸ hk)) hs

theorem ConstRefsLive.ext {m n : Machine} (hc : ConstRefsLive m.heap) (he : Ext m n) :
    ConstRefsLive n.heap :=
  hc.transport he.size (by intro cn; simp only [constOwn, he.payload])

theorem ConstRefsLive.defineMethod {h : Heap} {cls : ObjId} {name : String} {md : MethodDef}
    (hc : ConstRefsLive h) : ConstRefsLive (defineMethod h cls name md) :=
  hc.transport (by rw [Proof.objs_size_defineMethod]; exact Nat.le_refl _)
    (fun _ => Proof.constOwn_defineMethod ..)

theorem ConstRefsLive.ivarOnly {h h' : Heap} (hc : ConstRefsLive h) (hi : Proof.IvarOnly h h') :
    ConstRefsLive h' := hc.transport (by rw [hi.size]; exact Nat.le_refl _) (fun _ => hi.constOwn_eq ..)

theorem classNamed_constOwn {h : Heap} {cn : String} {k : ObjId}
    (hk : classNamed? h cn = some k) : constOwn h Boot.objectId cn = some (.ref k) := by
  unfold classNamed? at hk
  split at hk
  · rename_i o ho
    split at hk
    · cases hk
      cases hp : h.classPayload? Boot.objectId <;> simpa [constOwn, constLookup, hp] using ho
    · cases hk
  · cases hk

#print axioms constRefsLiveB_sound
end Ratchet.Denote
