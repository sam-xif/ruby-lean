import Denote.Rules.Closure.Entry

/-! Complete body environments for required parameters, nil-initialized block locals,
and a live capture. The capture's absence clause is independent of its lower-bound spine. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private def BindingDen (m : Machine) (p : String × Ty) (b : String × Value) : Prop :=
  p.1 = b.1 ∧ denM p.2 m b.2

private inductive BindingsDen (m : Machine) : Env → List (String × Value) → Prop
  | nil : BindingsDen m [] []
  | cons {p b ps bs} : BindingDen m p b → BindingsDen m ps bs →
      BindingsDen m (p :: ps) (b :: bs)

private theorem BindingsDen.append {m : Machine} {a b : Env} {xs ys : List (String × Value)}
    (ha : BindingsDen m a xs) (hb : BindingsDen m b ys) : BindingsDen m (a ++ b) (xs ++ ys) := by
  induction ha with
  | nil => exact hb
  | cons h _ ih => exact .cons h ih

private theorem binding_lookup {m : Machine} {own cap : Env} {bs : List (String × Value)}
    {get : String → Value} (hb : BindingsDen m own bs)
    (hc : ∀ x τ, envGet? cap x = some τ → denM τ m (get x))
    {x : String} {τ : Ty} (hx : envGet? (own ++ cap) x = some τ) :
    denM τ m (((bs.find? (·.1 == x)).map (·.2)).getD (get x)) := by
  induction hb with
  | nil => exact hc x τ hx
  | @cons p b ps bs hp hb ih =>
    obtain ⟨hn, hv⟩ := hp
    by_cases he : p.1 = x
    · have ht : p.2 = τ := by simpa [envGet?, he] using hx
      simpa [← hn, he, ← ht] using hv
    · have ht : envGet? (ps ++ cap) x = some τ := by simpa [envGet?, he] using hx
      simpa [← hn, he] using ih ht

private theorem binding_absent {m : Machine} {own cap : Env} {bs : List (String × Value)}
    {get : String → Value} (hb : BindingsDen m own bs)
    (hc : ∀ x, envGet? cap x = none → get x = .nil)
    {x : String} (hx : envGet? (own ++ cap) x = none) :
    ((bs.find? (·.1 == x)).map (·.2)).getD (get x) = .nil := by
  induction hb with
  | nil => exact hc x hx
  | @cons p b ps bs hp hb ih =>
    have he : p.1 ≠ x := by intro he; simp [envGet?, he] at hx
    have ht : envGet? (ps ++ cap) x = none := by simpa [envGet?, he] using hx
    simpa [← hp.1, he] using ih ht

private theorem parameter_bindings {m : Machine} {ps : List SigParam} {args : List Value}
    (h : DenAll (ps.map (·.2)) m args) :
    BindingsDen m ps ((ps.map (·.1)).zip args) := by
  induction ps generalizing args with
  | nil => exact .nil
  | cons p ps ih =>
    cases args with
    | nil => cases h
    | cons v vs => exact .cons ⟨rfl, h.1⟩ (ih h.2)

private theorem local_bindings (m : Machine) (ls : List String) :
    BindingsDen m (blockLocals ls) (ls.map (fun x => (x, Value.nil))) := by
  induction ls with
  | nil => exact .nil
  | cons x ls ih => exact .cons ⟨rfl, by simp [denM, isNilV]⟩ ih

/-- Complete binding needs type transport across the frame push, not a blanket ban on
closure values. Captured absence and non-alias binding remain separate obligations. -/
theorem requiredClosureFrame_envOk_from {source m : Machine} {cl : Closure} {ps : List SigParam}
    {args : List Value} {cap : Env} (hargs : DenAll (ps.map (·.2)) source args)
    (hlive : CaptureLive m cl.captured)
    (hcap : ∀ x τ, envGet? cap x = some τ → denM τ source (closLocal m cl x))
    (habs : ∀ x, envGet? cap x = none → closLocal m cl x = .nil)
    (htypes : ∀ p ∈ ps ++ blockLocals cl.locals ++ cap, isAliasTy p.2 = false)
    (hmove : ∀ p ∈ ps ++ blockLocals cl.locals ++ cap, ∀ v, denM p.2 source v →
      denM p.2 (pushMethodFrame m (requiredClosureFrame m cl (ps.map (·.1)) args)) v) :
    EnvOk (ps ++ blockLocals cl.locals ++ cap)
      (pushMethodFrame m (requiredClosureFrame m cl (ps.map (·.1)) args)) := by
  let n := pushMethodFrame m (requiredClosureFrame m cl (ps.map (·.1)) args)
  have hb := (parameter_bindings hargs).append (local_bindings source cl.locals)
  have hread (x : String) : n.getLocal x =
      (((((ps.map (·.1)).zip args) ++ cl.locals.map (fun y => (y, Value.nil))).find?
        (·.1 == x)).map (·.2)).getD (closLocal m cl x) := by
    rw [requiredClosureFrame_getLocal m cl _ args none none hlive]
    cases (((ps.map (·.1)).zip args) ++ cl.locals.map (fun y => (y, Value.nil))).find?
      (·.1 == x) <;> rfl
  constructor
  · intro x τ hx
    obtain ⟨z, hz⟩ := envGet?_mem hx
    have ht := htypes (z, τ) hz
    have hs : stripAlias τ = τ := by cases τ <;> simp_all [stripAlias, isAliasTy]
    refine ⟨?_, ?_⟩
    · rw [hs, hread]
      exact hmove (z, τ) hz _ (binding_lookup hb hcap hx)
    · intro y ρ hy
      rw [hy] at ht
      cases ht
  · intro x hx
    rw [hread]
    exact binding_absent hb habs hx

/-- Ordinary closure calls use the active caller as their value-typing source. -/
theorem requiredClosureFrame_envOk_of_transport {m : Machine} {cl : Closure} {ps : List SigParam}
    {args : List Value} {cap : Env} (hargs : DenAll (ps.map (·.2)) m args)
    (hlive : CaptureLive m cl.captured)
    (hcap : ∀ x τ, envGet? cap x = some τ → denM τ m (closLocal m cl x))
    (habs : ∀ x, envGet? cap x = none → closLocal m cl x = .nil)
    (htypes : ∀ p ∈ ps ++ blockLocals cl.locals ++ cap, isAliasTy p.2 = false)
    (hmove : ∀ p ∈ ps ++ blockLocals cl.locals ++ cap, ∀ v, denM p.2 m v →
      denM p.2 (pushMethodFrame m (requiredClosureFrame m cl (ps.map (·.1)) args)) v) :
    EnvOk (ps ++ blockLocals cl.locals ++ cap)
      (pushMethodFrame m (requiredClosureFrame m cl (ps.map (·.1)) args)) :=
  requiredClosureFrame_envOk_from hargs hlive hcap habs htypes hmove

/-- First-order captures discharge transport using the unchanged heap. -/
theorem requiredClosureFrame_envOk {m : Machine} {cl : Closure} {ps : List SigParam}
    {args : List Value} {cap : Env} (hargs : DenAll (ps.map (·.2)) m args)
    (hlive : CaptureLive m cl.captured)
    (hcap : ∀ x τ, envGet? cap x = some τ → denM τ m (closLocal m cl x))
    (habs : ∀ x, envGet? cap x = none → closLocal m cl x = .nil)
    (htypes : ∀ p ∈ ps ++ blockLocals cl.locals ++ cap,
      FirstOrder p.2 = true ∧ isAliasTy p.2 = false) :
    EnvOk (ps ++ blockLocals cl.locals ++ cap)
      (pushMethodFrame m (requiredClosureFrame m cl (ps.map (·.1)) args)) :=
  requiredClosureFrame_envOk_of_transport hargs hlive hcap habs
    (fun p hp => (htypes p hp).2)
    (fun p hp _ hv => (denM_heap_only (m₁ := m)
      (m₂ := pushMethodFrame m (requiredClosureFrame m cl (ps.map (·.1)) args))
      (htypes p hp).1 rfl).mp hv)

#print axioms requiredClosureFrame_envOk_of_transport
#print axioms requiredClosureFrame_envOk_from
#print axioms requiredClosureFrame_envOk
end Ratchet.Denote.Typed
