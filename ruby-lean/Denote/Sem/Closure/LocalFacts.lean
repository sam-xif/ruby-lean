import Ratchet.Static.LocalFacts
import Denote.Sem.Closure.Reify
import Denote.Sem.Closure.Bindings

/-! Physical capture origins and slot domains for a flow-sensitive local record.
Code/types and native method-table readiness remain separate conformance obligations. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

def CurrentProc (m : Machine) (v : Value) : Prop :=
  ∃ cl, procClosure? m.heap v = some cl ∧
    cl.captured = some (m.stack.headD 0) ∧ classOf m.heap v = Boot.procId

def currentProcB (m : Machine) (v : Value) : Bool :=
  match procClosure? m.heap v with
  | none => false
  | some cl => cl.captured == some (m.stack.headD 0) && classOf m.heap v == Boot.procId

theorem currentProcB_iff {m : Machine} {v : Value} :
    currentProcB m v = true ↔ CurrentProc m v := by
  cases hp : procClosure? m.heap v <;> simp [currentProcB, CurrentProc, hp]

structure LocalFactsOk (f : LocalFacts) (m : Machine) : Prop where
  slots : ∀ names, f.slots = some names → FrameSlots names m
  currentProcs : ∀ x ∈ f.currentProcs, CurrentProc m (m.getLocal x)
  bound : ∀ x ∈ f.bound, frameBinds m (m.stack.headD 0) x = true

theorem LocalFactsOk.unknown (m : Machine) : LocalFactsOk .unknown m := by
  constructor
  · intro _ h; cases h
  · intro _ h; cases h
  · intro _ h; cases h

theorem LocalFactsOk.empty {m : Machine} (h : FrameSlots [] m) : LocalFactsOk .empty m :=
  ⟨fun _ he => by cases he; exact h, (fun _ he => by cases he), (fun _ he => by cases he)⟩

theorem CurrentProc.ext {m n : Machine} {v : Value} (h : CurrentProc m v) (he : Ext m n) :
    CurrentProc n v := by
  obtain ⟨cl, hp, hc, hk⟩ := h
  cases v with
  | ref o =>
    have ho := he.get o (lt_of_procClosure? hp)
    refine ⟨cl, ?_, by simpa only [he.stack] using hc, ?_⟩
    · simpa only [procClosure?, ho] using hp
    · simpa only [classOf, ho] using hk
  | _ => cases hp

theorem CurrentProc.setLocal {m : Machine} {v : Value} (h : CurrentProc m v)
    (x : String) (w : Value) : CurrentProc (m.setLocal x w) v := h

theorem CurrentProc.framed {m n : Machine} {v : Value} (h : CurrentProc m v)
    (hf : Framed m n) : CurrentProc n v := by
  obtain ⟨cl, hp, hc, hk⟩ := h
  exact ⟨cl, hf.procs.payload v cl hp, by simpa only [hf.stack] using hc,
    (hf.procs.dispatch v cl hp).trans hk⟩

theorem LocalFactsOk.ext {f : LocalFacts} {m n : Machine}
    (h : LocalFactsOk f m) (he : Ext m n) : LocalFactsOk f n := by
  refine ⟨?_, ?_, ?_⟩
  · intro names hn x
    simpa only [frameBinds, he.frames, he.stack] using h.slots names hn x
  · intro x hx
    have hr : n.getLocal x = m.getLocal x := he.getLocal_eq x
    rw [hr]
    exact (h.currentProcs x hx).ext he
  · intro x hx
    simpa only [frameBinds, he.frames, he.stack] using h.bound x hx

/-- All writes preserve other names' capture origins. Slot insertion needs an uncaptured
activation; a captured write may instead update an existing ancestor slot. -/
theorem LocalFactsOk.write {f : LocalFacts} {m : Machine} (h : LocalFactsOk f m)
    (hl : m.stack.headD 0 < m.frames.size)
    (hu : (m.frames.getD (m.stack.headD 0) default).captured = none)
    (x : String) (v : Value) (current : Bool) (hv : current = true → CurrentProc m v) :
    LocalFactsOk (f.write x current) (m.setLocal x v) := by
  constructor
  · intro names hn
    cases hs : f.slots with
    | none => simp [LocalFacts.write, hs] at hn
    | some old =>
      simp only [LocalFacts.write, hs, Option.map_some, Option.some.injEq] at hn
      subst names
      exact (h.slots old hs).setLocal hl hu x v
  · intro y hy
    simp only [LocalFacts.write, List.mem_append, List.mem_filter, bne_iff_ne] at hy
    rcases hy with hy | ⟨hy, hne⟩
    · cases hc : current <;> simp only [hc, Bool.false_eq_true, if_true, if_false,
        List.not_mem_nil, List.mem_singleton] at hy
      subst y
      rw [getLocal_setLocal_self m x v hl]
      exact (hv hc).setLocal x v
    · rw [getLocal_setLocal_ne m x v hne]
      exact (h.currentProcs y hy).setLocal x v
  · intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact frameBinds_setLocal_self m y v hl hu
    · exact (BindingsPres.setLocal m x v).bound _ hl y (h.bound y hy)

theorem LocalFactsOk.copy {f : LocalFacts} {m : Machine} (h : LocalFactsOk f m)
    (hl : m.stack.headD 0 < m.frames.size)
    (hu : (m.frames.getD (m.stack.headD 0) default).captured = none) (x y : String) :
    LocalFactsOk (f.copy x y) (m.setLocal x (m.getLocal y)) :=
  h.write hl hu x (m.getLocal y) _ (fun hy => h.currentProcs y (by simpa using hy))

theorem currentProc_reified (m : Machine) (code : ClosureCode) :
    CurrentProc (reifiedMachine m (toRubyParams code.params) code.locals (toRuby code.body) code.lam)
      (.ref m.heap.objs.size) :=
  ⟨_, reified_payload m _ _ _ _, rfl, by simp [reifiedMachine, classOf, pushHeap_get_self]⟩

theorem LocalFactsOk.store {f : LocalFacts} {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (h : LocalFactsOk f m) (hm : StateOk κ Γ I m)
    (hu : (m.frames.getD (m.stack.headD 0) default).captured = none)
    (x : String) (code : ClosureCode) :
    LocalFactsOk (f.write x true)
      ((reifiedMachine m (toRubyParams code.params) code.locals (toRuby code.body) code.lam).setLocal
        x (.ref m.heap.objs.size)) :=
  (h.ext (reified_ext hm _ _ _ _)).write hm.frameInRange.2 hu x _ true
    (fun _ => currentProc_reified m code)

/-- Type and origin facts must refer to the same live descriptor. No code, capture or
dispatch property is recovered by matching a syntax-table entry. -/
theorem LocalFactsOk.code {f : LocalFacts} {m : Machine} {x : String}
    {code : ClosureCode} {cap selfT : Ty} (h : LocalFactsOk f m) (hx : x ∈ f.currentProcs)
    (hv : denM (.clos code cap selfT) m (m.getLocal x)) :
    ∃ cl, procClosure? m.heap (m.getLocal x) = some cl ∧ ClosureMatches code cl ∧
      cl.captured = some (m.stack.headD 0) ∧ classOf m.heap (m.getLocal x) = Boot.procId := by
  obtain ⟨cl, hp, hc, hk⟩ := h.currentProcs x hx
  rw [denM] at hv
  obtain ⟨cl', hp', hcode, _⟩ := hv
  have he : cl' = cl := Option.some.inj (hp'.symm.trans hp)
  subst cl'
  exact ⟨cl, hp, hcode, hc, hk⟩

#print axioms LocalFactsOk.write
#print axioms CurrentProc.framed
#print axioms LocalFactsOk.copy
#print axioms LocalFactsOk.store
#print axioms LocalFactsOk.code
end Ratchet.Denote
