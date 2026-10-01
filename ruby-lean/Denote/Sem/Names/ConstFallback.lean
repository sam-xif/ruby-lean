import Denote.Ty.Ext

/-! A fallback ancestor walk cannot introduce a constant absent from the global table.
Global bindings win before fallback, so ancestor values need not equal global values. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

def ConstFallback (h : Heap) (k : ObjId) : Prop :=
  ∀ name, constLookup h name = none → constLookupFrom h k name = none

def constFallbackB (h : Heap) (k : ObjId) : Bool :=
  (ancestors h k).all fun j => (h.classPayload? j).all fun cp =>
    cp.consts.all fun p => (constLookup h p.1).isSome

theorem constFallbackB_sound {h : Heap} {k : ObjId} (hb : constFallbackB h k = true) :
    ConstFallback h k := by
  intro name hn
  let f (j : ObjId) : Option Value := match h.classPayload? j with
    | some cp => (cp.consts.find? (·.1 == name)).map (·.2)
    | none => none
  have row : ∀ j ∈ ancestors h k, f j = none := by
    intro j hj
    have hp := List.all_eq_true.mp hb j hj
    cases hc : h.classPayload? j with
    | none => simp only [f, hc]
    | some cp =>
      simp only [hc, Option.all_some] at hp
      have hf : cp.consts.find? (·.1 == name) = none := by
        apply List.find?_eq_none.mpr
        intro p hm
        simp only [beq_iff_eq]
        intro he
        have hv := List.all_eq_true.mp hp p hm
        rw [he, hn] at hv
        cases hv
      simp only [f, hc, hf, Option.map_none]
  change (ancestors h k).firstM f = none
  generalize ancestors h k = js at row ⊢
  induction js with
  | nil => rfl
  | cons j js ih =>
    simp only [List.firstM, row j (List.mem_cons_self),
      ih (fun x hx => row x (List.mem_cons_of_mem j hx))]
    rfl

theorem ConstFallback.transport {h h' : Heap} {k j : ObjId} (hp : ConstFallback h k)
    (hg : ∀ n, constLookup h' n = constLookup h n)
    (hf : ∀ n, constLookupFrom h' j n = constLookupFrom h k n) : ConstFallback h' j := by
  intro n hn
  rw [hg] at hn
  rw [hf]
  exact hp n hn

theorem ConstFallback.ext {m n : Machine} {k : ObjId} (hp : ConstFallback m.heap k)
    (he : Ext m n) : ConstFallback n.heap k :=
  hp.transport he.constLookup_eq (fun _ => by simp only [constLookupFrom, he.payload, he.ancestors])

theorem ConstFallback.methodWrite {h : Heap} {k cls : ObjId} {name : String} {md : MethodDef}
    (hp : ConstFallback h k) : ConstFallback (defineMethod h cls name md) k := by
  apply hp.transport _ (fun _ => Proof.constLookupFrom_defineMethod ..)
  intro n
  have eqn (g : Heap) : constLookup g n = constOwn g Boot.objectId n := by
    unfold constLookup constOwn
    cases g.classPayload? Boot.objectId <;> rfl
  rw [eqn, eqn, Proof.constOwn_defineMethod]

theorem ConstFallback.ivarOnly {h h' : Heap} {k : ObjId} (hp : ConstFallback h k)
    (hi : Proof.IvarOnly h h') : ConstFallback h' k :=
  hp.transport (fun _ => by simp only [constLookup, hi.classPayload])
    (fun _ => by simp only [constLookupFrom, hi.classPayload, hi.ancestors_eq])

#print axioms constFallbackB_sound
end Ratchet.Denote
