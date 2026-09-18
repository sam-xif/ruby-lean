import Ratchet.Guards.ClassCtx
import Denote.Sem.Core.State

/-! Class entry obtains physical freshness from the incoming context, for every name.
The positive declaration table alone is not an absence proof. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

theorem StateOk.freshClassName {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {name : String}
    (hm : StateOk κ Γ I m) (hn : freshClassNameB κ name = true) :
    constOwn m.heap Boot.objectId name = none :=
  hm.globalConsts.absent (by simpa only [freshClassNameB, Bool.not_eq_true'] using hn)

#print axioms StateOk.freshClassName
end Ratchet.Denote
