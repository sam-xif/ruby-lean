import Denote.Sem.ClassHeap
import Denote.Sem.GlobalConsts

/-! Fresh entry adds just the executed binding to the upper bound; future declarations
are never pre-published. The statement is independent of the new class's name or body. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore
open RubyCore.Proof.Judgment (freshClsHeap)

theorem globalConsts {names : List String} {h : Heap} {name : String} {e : ObjId}
    (ho : Boot.objectId < h.objs.size) (hc : GlobalConstsOk names h) :
    GlobalConstsOk (name :: names) (freshClsHeap h Boot.objectId name name e) := by
  intro cn v hv
  by_cases hn : cn = name
  · subst cn; exact List.mem_cons_self
  · apply List.mem_cons_of_mem
    apply hc cn v
    have he := const_other (e := e) ho hn
    simp only [constLookup_eq_own] at he
    exact he ▸ hv

#print axioms globalConsts
end Ratchet.Denote.FreshClass
