import Denote.Sem.Heap.ScalarPres
import Denote.Sem.Core.Reframe

/-! Full conformance through a field replacement that preserves all first-order types. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

theorem StateOk.bindIvar_scalar {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {o : ObjId} {x : String} {v : Value} (hm : StateOk κ Γ I m) (ht : ReframeFO κ I)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hs : m.currentFrame.self = .ref o)
    (hv : ScalarEq (ivarOf m.heap (.ref o) x) v) :
    StateOk κ Γ I (Interp.bindIvar m x v) := by
  have hf := Framed.bindIvar_scalar hs (hm.selfLive o hs) hv
  have hw := bindIvar_ivarOnly m x v
  have hlookup (k : ObjId) (name : String) :
      constLookupFrom (Interp.bindIvar m x v).heap k name = constLookupFrom m.heap k name := by
    simp only [constLookupFrom, hw.classPayload, hw.ancestors_eq]
  have hresolve (name : String) : constResolveAt (Interp.bindIvar m x v) name = constResolveAt m name := by
    simp only [constResolveAt, bindIvar_currentFrame, hw.constOwn_eq, hlookup]
  apply StateOk_bindIvar hm x v
  · exact env_bindIvar hm.env (by
      intro y τ hy
      obtain ⟨z, hz⟩ := envGet?_mem hy
      exact hf.firstOrder _ (hΓ (z, τ) hz) _ (hm.env.1 y τ hy).1)
  · exact hf.selfSpine (by simp) hm.selfLive ht.spine hm.selfSpine
  · cases hb : κ.blockTy with
    | none => simpa only [BlockTyOk, hb, bindIvar_currentFrame] using hm.blockTy
    | some τ =>
      obtain ⟨w, hb', hd⟩ := (show ∃ w, m.currentFrame.blk = some w ∧ denM τ m w by
        simpa only [BlockTyOk, hb] using hm.blockTy)
      exact ⟨w, by simpa only [bindIvar_currentFrame] using hb', hf.firstOrder τ (ht.block τ hb) w hd⟩
  · cases hs' : κ.selfTy with
    | none => trivial
    | some τ =>
      have hd : denM τ m m.currentFrame.self := by simpa only [SelfTyOk, hs'] using hm.selfTy
      simpa only [SelfTyOk, hs', bindIvar_currentFrame] using hf.firstOrder τ (ht.self τ hs') _ hd
  · intro name τ hn
    obtain ⟨w, hw', hd⟩ := hm.consts name τ hn
    exact ⟨w, by rw [hresolve]; exact hw', hf.firstOrder τ (ht.consts name τ hn) w hd⟩
  · intro owner name τ k hn hk w hfound
    rw [bindIvar_classNamed] at hk
    rw [hlookup] at hfound
    exact hf.firstOrder τ (ht.paths _ τ hn) w (hm.constPaths owner name τ k hn hk w hfound)

#print axioms StateOk.bindIvar_scalar
end Ratchet.Denote
