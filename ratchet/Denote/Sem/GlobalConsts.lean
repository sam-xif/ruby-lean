import Denote.Sem.ConstLive

/-! The global-name bound interprets static freshness for arbitrary classes. Extra listed
names are conservative; omitting any bound name must fail conformance and the boot gate. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

def GlobalConstsOk (names : List String) (h : Heap) : Prop :=
  ∀ cn v, constOwn h Boot.objectId cn = some v → cn ∈ names

def globalConstsOkB (names : List String) (h : Heap) : Bool :=
  (h.classPayload? Boot.objectId).all fun cp => cp.consts.all fun p => names.contains p.1

theorem globalConstsOkB_sound {names : List String} {h : Heap}
    (hb : globalConstsOkB names h = true) : GlobalConstsOk names h := by
  intro cn v hv
  cases hp : h.classPayload? Boot.objectId with
  | none => simp [constOwn, hp] at hv
  | some cp =>
    simp only [globalConstsOkB, hp, Option.all_some, List.all_eq_true] at hb
    simp only [constOwn, hp, Option.bind_some] at hv
    cases hf : cp.consts.find? (·.1 == cn) with
    | none => simp [hf] at hv
    | some p =>
      have hn : p.1 = cn := by simpa using List.find?_some hf
      simpa only [hn, List.contains_iff_mem] using hb p (List.mem_of_find?_eq_some hf)

theorem GlobalConstsOk.absent {names : List String} {h : Heap} {cn : String}
    (hc : GlobalConstsOk names h) (hn : names.contains cn = false) :
    constOwn h Boot.objectId cn = none := by
  cases hv : constOwn h Boot.objectId cn with
  | none => rfl
  | some v => have hm := hc cn v hv; simp [hm] at hn

theorem GlobalConstsOk.transport {names : List String} {h h' : Heap}
    (hc : GlobalConstsOk names h)
    (he : ∀ cn, constOwn h' Boot.objectId cn = constOwn h Boot.objectId cn) :
    GlobalConstsOk names h' := by
  intro cn v hv
  exact hc cn v ((he cn).symm ▸ hv)

theorem GlobalConstsOk.ext {names : List String} {m n : Machine}
    (hc : GlobalConstsOk names m.heap) (he : Ext m n) : GlobalConstsOk names n.heap :=
  hc.transport (by intro cn; simp only [constOwn, he.payload])

theorem GlobalConstsOk.defineMethod {names : List String} {h : Heap} {cls : ObjId}
    {name : String} {md : MethodDef} (hc : GlobalConstsOk names h) :
    GlobalConstsOk names (defineMethod h cls name md) :=
  hc.transport (fun _ => Proof.constOwn_defineMethod ..)

theorem GlobalConstsOk.ivarOnly {names : List String} {h h' : Heap}
    (hc : GlobalConstsOk names h) (hi : Proof.IvarOnly h h') : GlobalConstsOk names h' :=
  hc.transport (fun _ => hi.constOwn_eq ..)

#print axioms globalConstsOkB_sound
#print axioms GlobalConstsOk.absent
end Ratchet.Denote
