import Denote.Sem.Core.Framed

/-! Named class identity is already a first-order denotation; no new frame clause. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

theorem Framed.classNamed {m n : Machine} (h : Framed m n) {cn : String} {k : ObjId}
    (hk : classNamed? m.heap cn = some k) : classNamed? n.heap cn = some k := by
  have hv := h.firstOrder (.clsOf cn) rfl (.ref k) (by simp [denM, isClassRefNamed, hk])
  cases hn : classNamed? n.heap cn with
  | none => simp [denM, isClassRefNamed, hn] at hv
  | some j =>
    have he : j = k := by simpa only [denM, isClassRefNamed, hn, beq_iff_eq] using hv
    simpa only [he]

#print axioms Framed.classNamed
end Ratchet.Denote
