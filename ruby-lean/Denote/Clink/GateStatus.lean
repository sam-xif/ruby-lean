import Denote.Clink.Registration

/-! The profile census is checkable without any semantic proof imports. Counts
here are selected rules, not certified proofs; Registry checks the latter. -/
set_option autoImplicit false
open Lean Elab Command
namespace Ratchet.Denote.Typed

def authoringDClinks : CommandElabM (List String) := do
  let env ← getEnv
  let mut names := []
  for ind in dJudgmentInductives do
    let some (.inductInfo info) := env.find? ind
      | throwError m!"{ind} is not an inductive"
    names := names ++ info.ctors.map (toString ∘ dRuleSuffix)
  return names

elab "check_dclink_profile" : command => do
  let names ← authoringDClinks
  let errors := clinkPolicyErrors names clinkProfile
  unless errors.isEmpty do throwError m!"clink profile: {errors}"
  unless names.length == 105 do
    throwError m!"clink profile: authoring census changed ({names.length}, expected 105)"
  unless clinkEnabled "intLit" do
    throwError "clink profile: intLit must remain enabled as the non-vacuity anchor"
  logInfo m!"clink profile {clinkProfileName}: {names.filter clinkEnabled |>.length} selected, \
{names.filter (!clinkEnabled ·) |>.length} gated, {names.length} total (proofs not checked here)"

elab "require_complete_dclink_profile" : command => do
  let gated := (← authoringDClinks).filter (!clinkEnabled ·)
  unless gated.isEmpty do
    throwError m!"full corpus audit requires all clinks; {gated.length} are gated by \
{clinkProfileName}. Use scripts/run_typed_ratchet.sh --clink-rebuild for the active proof subset."

check_dclink_profile
end Ratchet.Denote.Typed
