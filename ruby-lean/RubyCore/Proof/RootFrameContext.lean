import RubyCore.Proof.RootFrameSupport

/-! Catch tags are the remaining native whole-stack observation. Block-call
lifetimes, inspection guards and Hash locks are carried explicitly in state. -/
namespace RubyCore.Proof.Root

/-- The continuation forms consulted by native whole-stack probes. -/
def observedKont : Kont → Bool
  | .catchK _ => true
  | _ => false

def ContextFree (K : List Kont) : Prop := ∀ k ∈ K, observedKont k = false

theorem ContextFree.any_false {K : List Kont} (hK : ContextFree K) (p : Kont → Bool)
    (hp : ∀ k, observedKont k = false → p k = false) : K.any p = false := by
  simp only [List.any_eq_false]
  intro k hk
  exact (Bool.not_eq_true _).mpr (hp k (hK k hk))

theorem ContextFree.hashLockFree {K : List Kont} (hK : ContextFree K) : HashLockFree K := by
  exact hashLockFree_all K

theorem any_rootFrame (K : List Kont) (m : Machine) (p : Kont → Bool)
    (hK : K.any p = false) :
    (pushRootK K m).kont.any p = m.kont.any p := by
  simp only [pushRootK_kont]
  split <;> simp [List.any_append, hK]

end RubyCore.Proof.Root
