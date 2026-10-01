import Ratchet.Check.CallbackCache
import Ratchet.Check.CheckMethodFlow

/-! Explicit-block definitions retain their all-code proofs and declared domains.
Context changes recheck every body, including methods that are never called. -/
set_option autoImplicit false
namespace Ratchet

structure CallableBoundCallback (κ : Ctx) (I : Ty) (name : String) where
  decl : Defn
  nameOk : decl.name = name
  body : CheckedBoundCallbackBody κ I decl
  installed : decl ∈ κ.defs

def findBoundCallback (κ : Ctx) (I : Ty) (name : String) :
    List CachedBoundCallback → Option (CallableBoundCallback κ I name)
  | [] => none
  | c :: cs =>
    let found : Option (CallableBoundCallback κ I name) := do
      if hn : c.decl.name = name then do
        let ⟨hc⟩ ← ctxEq? c.ctx κ
        if hi : c.spine = I then do
          let ⟨hd⟩ ← defnMem? c.decl κ.defs
          some ⟨c.decl, hn, by simpa only [hc, hi] using c.body, hd⟩
        else none
      else none
    found.orElse (fun _ => findBoundCallback κ I name cs)

def refreshBoundCallbackBodies (fuel : Nat) (κ : Ctx) (I : Ty) :
    List CachedBoundCallback → Option (List CachedBoundCallback)
  | [] => some []
  | c :: cs => do
    let ⟨_⟩ ← defnMem? c.decl κ.defs
    let body ← checkBoundCallbackBody fuel κ I c.decl
      (.defBlock c.decl.name [] c.body.blockArgs c.body.blockRet c.body.ret c.deriv)
    let tail ← refreshBoundCallbackBodies fuel κ I cs
    some (⟨κ, I, c.decl, body, c.deriv⟩ :: tail)

end Ratchet
