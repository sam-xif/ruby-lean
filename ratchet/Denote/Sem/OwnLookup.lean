import Denote.Sem.OwnNames
import Denote.Sem.MethodHeap

/-! Resolve an inherited row only after ruling out every earlier physical owner.
Neither a set of named ancestors nor the ancestor's positive row supplies that absence. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

theorem lookup_go_skip {h : Heap} {name : String} {pre rest : List ObjId}
    (hp : ∀ k ∈ pre, (h.classPayload? k).bind
      (fun cp => (cp.methods.find? (·.1 == name)).map (·.2)) = none) :
    lookup.go h name (pre ++ rest) = lookup.go h name rest := by
  induction pre with
  | nil => rfl
  | cons k ks ih =>
    have hk := hp k List.mem_cons_self
    have hr := ih (fun j hj => hp j (List.mem_cons_of_mem k hj))
    simp only [List.cons_append, lookup.go]
    cases hc : h.classPayload? k with
    | none => exact hr
    | some cp =>
      cases hf : cp.methods.find? (·.1 == name) with
      | none => simpa only [hf] using hr
      | some p => simp [hc, hf] at hk

theorem methodOn_after_prefix {C : CTable} {h : Heap} {r k : ObjId} {name : String}
    {pre rest : List ObjId} {md : MethodDef}
    (hp : ClassOwnNames C h) (ha : ancestors h r = pre ++ k :: rest)
    (hn : ∀ j ∈ pre, ∃ c ∈ C, classNamed? h c.name = some j ∧ name ∉ ownNames C c.name)
    (hm : (h.classPayload? k).bind
      (fun cp => (cp.methods.find? (·.1 == name)).map (·.2)) = some md) :
    Interp.methodOn h r name = some (k, md) := by
  rw [methodOn_eq_go, ha, lookup_go_skip (fun j hj => by
    obtain ⟨c, hc, hk, habsent⟩ := hn j hj
    exact hp.absent hc hk habsent)]
  simp only [lookup.go]
  cases hc : h.classPayload? k with
  | none => simp [hc] at hm
  | some cp =>
    cases hf : cp.methods.find? (·.1 == name) with
    | none => simp [hc, hf] at hm
    | some p =>
      have he : p.2 = md := by simpa [hc, hf] using hm
      simp only [hf, he]

/-- Recover the actual inherited code from positive rows and owner-local absence.
The caller still owes its full annotation-domain body proof and native-dispatch guards. -/
theorem classesOk_methodOn_after_prefix {C : CTable} {m : Machine} {c : Cls} {d : Defn}
    {r : ObjId} (hc : ClassesOk C m) (hp : ClassOwnNames C m.heap)
    (hclass : c ∈ C) (hd : d ∈ c.methods)
    (hchain : ∀ k, classNamed? m.heap c.name = some k → ∃ pre rest,
      ancestors m.heap r = pre ++ k :: rest ∧
      ∀ j ∈ pre, ∃ old ∈ C, classNamed? m.heap old.name = some j ∧
        d.name ∉ ownNames C old.name) :
    ∃ k md, classNamed? m.heap c.name = some k ∧
      Interp.methodOn m.heap r d.name = some (k, md) ∧
      md.params = toRubyParams d.params ∧ md.body = toRuby d.body ∧
      md.undefined = false ∧ InstanceMethodCode k d.name md := by
  obtain ⟨k, hk, hmethods⟩ := hc c hclass
  obtain ⟨md, hm, hparams, hbody, hu, hcode⟩ := hmethods d hd
  obtain ⟨pre, rest, ha, hn⟩ := hchain k hk
  exact ⟨k, md, hk, methodOn_after_prefix hp ha hn hm, hparams, hbody, hu, hcode⟩

#print axioms methodOn_after_prefix
#print axioms classesOk_methodOn_after_prefix
end Ratchet.Denote
