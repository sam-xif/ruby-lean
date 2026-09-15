import Ratchet.Judge

/-! Only top-level definitions can waive default initialization at the implicit root.
An unrelated class's initialize must not disable this obligation. -/
namespace Ratchet

def rootInitFreeB (D : DefTable) : Bool := !(D.any (fun d => d.name == "initialize"))

theorem rootInitFreeB_cons {D : DefTable} {d : Defn} (h : rootInitFreeB (d :: D) = true) :
    d.name ≠ "initialize" ∧ rootInitFreeB D = true := by
  simpa [rootInitFreeB, Bool.not_or, Bool.and_eq_true] using h

end Ratchet
