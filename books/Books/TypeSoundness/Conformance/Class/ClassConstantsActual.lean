import Books.TypeSoundness.Conformance.Class.ClassNamesActual
import Books.TypeSoundness.Conformance.Subclass.SubclassNames

/-! Repair the existing constant/live/root-name transfers for the actual class heap. -/
set_option autoImplicit false
namespace Checker.Soundness.FreshClassActual
open RubyCore Checker RubyCore.Proof RubyCore.Proof.Judgment
variable {p : ObjId}

variable {m : Machine} {name : String} {e : ObjId}
local notation "h₁" => heap m name e p

theorem constOwn_old {o : ObjId} (hd : m.lexicalNamespace < m.heap.objs.size)
    (ho : o < m.heap.objs.size) (cn : String) :
    constOwn h₁ o cn = constOwn (constSetIn m.heap m.lexicalNamespace name (.ref m.heap.objs.size)) o cn := by
  unfold constOwn
  rw [(grow hd).payloadOld (by rw [hmid_size]; exact ho)]

theorem const_self (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true) :
    constLookup h₁ name = some (.ref m.heap.objs.size) := by
  have hl := lt_size_of_classPayload ho
  rw [Subclass.const_eq_own, constOwn_old (htop ▸ hl) hl, htop]
  exact constOwn_constSetIn_self ho hl

theorem const_other (htop : m.lexicalNamespace = Boot.objectId)
    (ho : Boot.objectId < m.heap.objs.size) {cn : String} (hn : cn ≠ name) :
    constLookup h₁ cn = constLookup m.heap cn := by
  rw [Subclass.const_eq_own, Subclass.const_eq_own, constOwn_old (htop ▸ ho) ho, htop]
  exact constOwn_constSetIn_ne m.heap Boot.objectId Boot.objectId name cn _ (Or.inr hn)

theorem named_fresh (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true) :
    classNamed? h₁ name = some m.heap.objs.size := by
  simp only [classNamed?, const_self htop ho, Heap.classPayload?,
    get_class (htop ▸ lt_size_of_classPayload ho), namedObject, Option.isSome_some, ite_true]

theorem named_old (htop : m.lexicalNamespace = Boot.objectId)
    (ho : Boot.objectId < m.heap.objs.size) (hf : constOwn m.heap Boot.objectId name = none)
    {cn : String} {k : ObjId} (hk : classNamed? m.heap cn = some k) :
    classNamed? h₁ cn = some k := by
  have hcn : cn ≠ name := by
    intro he; subst cn
    simp only [classNamed?, Subclass.const_eq_own, hf] at hk
    cases hk
  unfold classNamed? at hk ⊢
  rw [const_other htop ho hcn]
  cases hl : constLookup m.heap cn with
  | none => simp only [hl] at hk; cases hk
  | some v =>
    cases v <;> try (simp only [hl] at hk; cases hk)
    rename_i o
    simp only [hl] at hk ⊢
    split at hk
    · rename_i hp
      rw [classPayload_live (htop ▸ ho) (lt_size_of_classPayload hp), hp]
      exact hk
    · cases hk

theorem named_old_back (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    {cn : String} {k : ObjId} (hl : k < m.heap.objs.size) (hk : classNamed? h₁ cn = some k) :
    classNamed? m.heap cn = some k := by
  by_cases hn : cn = name
  · subst cn
    rw [named_fresh htop ho] at hk
    exact False.elim ((Nat.ne_of_lt hl) (Option.some.inj hk).symm)
  · unfold classNamed? at hk ⊢
    rw [const_other htop (lt_size_of_classPayload ho) hn] at hk
    split at hk
    · split at hk
      · rename_i hp
        cases hk
        have hp₀ : (m.heap.classPayload? k).isSome = true := by
          rw [← classPayload_live (name := name) (e := e) (p := p)
            (htop ▸ lt_size_of_classPayload ho) hl]
          exact hp
        simp only [hp₀, ite_true]
      · cases hk
    · cases hk

theorem constRefsLive (hc : ConstRefsLive m.heap)
    (hd : m.lexicalNamespace < m.heap.objs.size) (ho : Boot.objectId < m.heap.objs.size) :
    ConstRefsLive h₁ := by
  intro cn k hk
  rw [constOwn_old hd ho] at hk
  have hk' : k = m.heap.objs.size ∨ k < m.heap.objs.size := by
    by_cases htop : Boot.objectId = m.lexicalNamespace
    · rw [← htop] at hk
      by_cases hn : cn = name
      · subst cn
        cases hp : m.heap.classPayload? Boot.objectId with
        | none => simp [constSetIn, constOwn, hp] at hk
        | some cp =>
          rw [constOwn_constSetIn_self (by simp [hp]) ho] at hk
          exact Or.inl (Value.ref.inj (Option.some.inj hk)).symm
      · rw [constOwn_constSetIn_ne _ _ _ _ _ _ (Or.inr hn)] at hk
        exact Or.inr (hc cn k hk)
    · rw [constOwn_constSetIn_ne _ _ _ _ _ _ (Or.inl htop)] at hk
      exact Or.inr (hc cn k hk)
  rw [size m name e]
  rcases hk' with rfl | hk'
  · exact Nat.lt_add_of_pos_right (by decide : 0 < 2)
  · exact Nat.lt_of_lt_of_le hk' (Nat.le_add_right _ _)

theorem rootNames (hc : RootNames m.heap) (hl : ConstRefsLive m.heap)
    (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none) : RootNames h₁ := by
  refine ⟨fun cn k hk => named_old htop (lt_size_of_classPayload ho) hn (hc.named cn k hk), ?_⟩
  intro cn k hk hr
  exact hc.only cn k (named_old_back htop ho (hc.live hl hr) hk) hr

theorem constOwn_other (htop : m.lexicalNamespace = Boot.objectId)
    (ho : Boot.objectId < m.heap.objs.size)
    {k : ObjId} (hk : k < m.heap.objs.size) {cn : String} (hn : cn ≠ name) :
    constOwn h₁ k cn = constOwn m.heap k cn := by
  rw [constOwn_old (htop ▸ ho) hk, htop]
  exact constOwn_constSetIn_ne m.heap Boot.objectId k name cn _ (Or.inr hn)

theorem const_from_old_other (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (htop : m.lexicalNamespace = Boot.objectId) {k : ObjId} (hk : k < m.heap.objs.size)
    {cn : String} (hn : cn ≠ name) : constLookupFrom h₁ k cn = constLookupFrom m.heap k cn := by
  have ho := hc.boot.2.2.2.2
  have hfirst (g : Heap) (j : ObjId) :
      constLookupFrom g j cn = (ancestors g j).firstM (fun o => constOwn g o cn) := by
    unfold constLookupFrom
    apply firstM_congr
    intro o _
    cases hp : g.classPayload? o <;> simp [constOwn, hp]
  rw [hfirst, hfirst, ancestors_old hc hs (htop ▸ ho) hk]
  apply firstM_congr
  intro j hj
  exact constOwn_other htop ho (ancestors_mem_lt hc hk j hj) hn

theorem fallback_old {k : ObjId} (hc : ChainsIn m.heap) (hs : Saturated m.heap)
    (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true) (hk : k < m.heap.objs.size)
    (hp : ConstFallback m.heap k) : ConstFallback h₁ k := by
  intro cn hn
  have hne : cn ≠ name := by intro he; subst cn; rw [const_self htop ho] at hn; cases hn
  rw [const_from_old_other hc hs htop hk hne]
  exact hp cn ((const_other htop hc.boot.2.2.2.2 hne).symm.trans hn)

#print axioms named_old
#print axioms constRefsLive
#print axioms rootNames
#print axioms fallback_old
end Checker.Soundness.FreshClassActual
