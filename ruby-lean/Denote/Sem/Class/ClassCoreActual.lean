import Denote.Sem.Class.ClassDataActual

/-! Reuse Subclass.core's field transfers with the repaired actual heap facts. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClassActual
open RubyCore Ratchet RubyCore.Proof
variable {p : ObjId}

theorem core {m : Machine} {name : String} {e : ObjId}
    (hc : CoreOk m.heap) (hs : Saturated m.heap)
    (htop : m.lexicalNamespace = Boot.objectId)
    (ho : (m.heap.classPayload? Boot.objectId).isSome = true)
    (hn : constOwn m.heap Boot.objectId name = none)
    (hpl : p < m.heap.objs.size)
    (he : (m.heap.get p).eigen = some e) : CoreOk (heap m name e p) := by
  have hch := hc.classReady.chains
  have hd : m.lexicalNamespace < m.heap.objs.size := htop ▸ hch.boot.2.2.2.2
  have hl : ∀ k, k ≤ Boot.procId → k < m.heap.objs.size :=
    fun _ hk => Nat.lt_of_le_of_lt hk hch.boot.2.2.2.1
  have hr := hc.classReady.constRefs "Regexp" _ (classNamed_constOwn hc.regexpNamed)
  refine {
    classReady := classReady hc.classReady hs hd hpl he
    rootNames := rootNames hc.rootNames hc.classReady.constRefs htop ho hn
    metaConstants := by
      rw [classOf_old hd hch.boot.2.2.2.2]
      exact fallback_old hch hs htop ho (ClsGrow.classOf_lt hch hch.boot.2.2.2.2) hc.metaConstants
    basicSelf := ?_
    moduleBasic := by rw [ancestors_old hch hs hd hch.boot.2.1]; exact hc.moduleBasic
    stringNamed := named_old htop hch.boot.2.2.2.2 hn hc.stringNamed
    stringSelf := ?_
    stringBasic := ?_
    regexpNamed := named_old htop hch.boot.2.2.2.2 hn hc.regexpNamed
    regexpSelf := ?_
    regexpBasic := ?_
    procBasic := ?_
    arrayBasic := ?_
    hashBasic := ?_
    coreNamed := ?_
    intMeta := by rw [classOf_old hd (hl _ (by decide))]; exact hc.intMeta
    strMeta := by rw [classOf_old hd (hl _ (by decide))]; exact hc.strMeta
    namesInj := by
      intro a b k ha hb
      have key : ∀ x, classNamed? (heap m name e p) x = some k →
          (k < m.heap.objs.size ∧ classNamed? m.heap x = some k) ∨ x = name := by
        intro x hx
        by_cases hx' : x = name
        · exact .inr hx'
        · left
          have href := classNamed_constOwn hx
          rw [constOwn_other htop hch.boot.2.2.2.2 hch.boot.2.2.2.2 hx'] at href
          have hl := hc.classReady.constRefs x k href
          exact ⟨hl, named_old_back htop ho hl hx⟩
      rcases key a ha with ⟨hl, ha'⟩ | rfl
      · rcases key b hb with ⟨_, hb'⟩ | rfl
        · exact hc.namesInj a b k ha' hb'
        · rw [named_fresh htop ho] at hb; cases hb; exact absurd hl (Nat.lt_irrefl _)
      · rcases key b hb with ⟨hl, _⟩ | rfl
        · rw [named_fresh htop ho] at ha; cases ha; exact absurd hl (Nat.lt_irrefl _)
        · rfl }
  · rw [ancestors_old hch hs hd (hl _ (by decide))]; exact hc.basicSelf
  · rw [ancestors_old hch hs hd (hl _ (by decide))]; exact hc.stringSelf
  · rw [ancestors_old hch hs hd (hl _ (by decide))]; exact hc.stringBasic
  · rw [ancestors_old hch hs hd hr]; exact hc.regexpSelf
  · rw [ancestors_old hch hs hd hr]; exact hc.regexpBasic
  · rw [ancestors_old hch hs hd (hl _ (by decide))]; exact hc.procBasic
  · rw [ancestors_old hch hs hd (hl _ (by decide))]; exact hc.arrayBasic
  · rw [ancestors_old hch hs hd (hl _ (by decide))]; exact hc.hashBasic
  · intro cn hcn v hv
    by_cases hn' : cn = name
    · subst cn
      rw [const_self htop ho] at hv
      cases hv
      exact ⟨m.heap.objs.size, rfl,
        by simp only [Heap.classPayload?, get_class hd, namedObject, Option.isSome_some]⟩
    · rw [const_other htop hch.boot.2.2.2.2 hn'] at hv
      obtain ⟨o, rfl, hp⟩ := hc.coreNamed cn hcn v hv
      exact ⟨o, rfl, (classPayload_live hd (lt_size_of_classPayload hp)).trans hp⟩

#print axioms core
end Ratchet.Denote.FreshClassActual
