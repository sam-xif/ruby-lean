-- Generated from Ratchet/Check/CallbackCache.lean by scripts/generate_audited_checker.py.
-- Edit the raw source and regenerate; Lean checks the indexed proof and trace.
import Ratchet.Audit.Erase
import Ratchet.Audit.BodyCache
import Ratchet.Audit.CheckCallbackBody

/-! Callback signatures belong to checked definitions. A changed context rechecks every
body at the same domains, including uncalled methods; calls only select exact artifacts. -/
set_option autoImplicit false
namespace Ratchet.Audit
open Ratchet

structure CallableCallback (κ : Ctx) (I : Ty) (name : String) where
  decl : Defn
  nameOk : decl.name = name
  body : CheckedCallbackBody κ I decl
  installed : decl ∈ κ.defs

def findCallback (κ : Ctx) (I : Ty) (name : String) : List CachedCallback → Option (CallableCallback κ I name)
  | [] => none
  | c :: cs =>
    let found : Option (CallableCallback κ I name) := do
      if hn : c.decl.name = name then do
        let ⟨hc⟩ ← ctxEq? c.ctx κ
        if hi : c.spine = I then do
          let ⟨hd⟩ ← defnMem? c.decl κ.defs
          some ⟨c.decl, hn, by simpa only [hc, hi] using c.body, hd⟩
        else none
      else none
    found.orElse (fun _ => findCallback κ I name cs)

def refreshCallbackBodies (fuel : Nat) (κ : Ctx) (I : Ty) : List CachedCallback → Option (List CachedCallback)
  | [] => some []
  | c :: cs => do
    let ⟨_⟩ ← defnMem? c.decl κ.defs
    let body ← checkCallbackBody fuel κ I c.decl
      (.defBlock c.decl.name c.body.params c.body.blockArgs c.body.blockRet c.body.ret c.deriv)
    let tail ← refreshCallbackBodies fuel κ I cs
    some (⟨κ, I, c.decl, body, c.deriv⟩ :: tail)

end Ratchet.Audit
