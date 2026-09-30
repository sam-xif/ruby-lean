import RubyCore.Proof.RootFrameSupport

/-! Native stack probes observe catch scopes, inspection
recursion guards, and Hash iteration locks. Framing is valid when the appended
context contributes none of those observations. -/
namespace RubyCore.Proof.Root

/-- The continuation forms consulted by native whole-stack probes. -/
def observedKont : Kont → Bool
  | .catchK _ | .objectInspectK .. | .frozenErrorK .. => true
  | .iterK _ _ _ (.hashEach ..) _ _ _ => true
  | _ => false

def ContextFree (K : List Kont) : Prop := ∀ k ∈ K, observedKont k = false

theorem ContextFree.any_false {K : List Kont} (hK : ContextFree K) (p : Kont → Bool)
    (hp : ∀ k, observedKont k = false → p k = false) : K.any p = false := by
  simp only [List.any_eq_false]
  intro k hk
  exact (Bool.not_eq_true _).mpr (hp k (hK k hk))

theorem ContextFree.hashLockFree {K : List Kont} (hK : ContextFree K) : HashLockFree K := by
  intro o
  apply hK.any_false
  intro k hk
  cases k <;> try rfl
  rename_i cl brk rest kind acc ret cur
  cases kind <;> simp_all [observedKont, holdsHash]

theorem any_rootFrame (K : List Kont) (m : Machine) (p : Kont → Bool)
    (hK : K.any p = false) :
    (pushRootK K m).kont.any p = m.kont.any p := by
  simp only [pushRootK_kont]
  split <;> simp [List.any_append, hK]

end RubyCore.Proof.Root
