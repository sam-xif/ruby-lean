import Denote.Bridge

/-! A green active gate requires the real final soundness theorems to use only
Lean's standard axioms. Building a theorem containing sorry is insufficient. -/
namespace Ratchet.Denote.Typed

def requireStandardAxioms (names : List Lean.Name) : Lean.Elab.Command.CommandElabM Unit := do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter (!allowed.contains ·)
    unless unexpected.isEmpty do
      throwError "active soundness theorem {name} uses unsupported axioms: {unexpected}"

run_cmd requireStandardAxioms [``validateD_certified, ``validateD_safe,
  ``validateD_safe_boot, ``validateD_safe_run]
end Ratchet.Denote.Typed
