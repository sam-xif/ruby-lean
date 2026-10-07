import Books.TypeSoundness.Registry.Family
import Books.TypeSoundness.Registry.Policy

/-! Registration checks apply to explicit commands and automatic discovery. -/
set_option autoImplicit false
open Lean Meta Elab Command
namespace Checker.Soundness.Typed
open Checker Checker.Soundness

def dclinkTy (target : Name := `Checker.Soundness.Typed.dsemFam) : Lean.Expr :=
  mkApp3 (mkConst ``Clink) (mkConst ``DFam) (mkConst ``dsynFam) (mkConst target)

/-- Suffix shared by constructor names, registry names, and semantic obligations. -/
def dRuleSuffix (ctor : Name) : Name :=
  if ctor.getPrefix == ``Checker.DJudge then Name.mkSimple ctor.getString!
  else Name.mkSimple ctor.getPrefix.getString! ++ Name.mkSimple ctor.getString!

def dsemName (ctor : Name) : Name :=
  `Checker.Soundness.Typed.SemSafeCtxA ++
    (if ctor == ``Checker.DJudge.seq then `sequence else dRuleSuffix ctor)

def dclinkName (ctor : Name) : Name := `Checker.Soundness.Typed.DClink ++ dRuleSuffix ctor

def registerDClink (ctor : Name)
    (target : Name := `Checker.Soundness.Typed.dsemFam)
    (proofName : Name := dsemName ctor)
    (clinkName : Name := dclinkName ctor)
    (enabled : String → Bool := clinkEnabled)
    (profileName : String := clinkProfileName)
    (manifest : Option Name := some `Checker.Soundness.Typed.dAvailableFamFields) : CommandElabM Unit := do
  let env ← getEnv
  let some (.ctorInfo ci) := env.find? ctor
    | throwError m!"register_dclink: {ctor} is not a constructor"
  unless dFamField.any (fun (ind, _) => ind == ci.induct) do
    throwError m!"register_dclink: {ctor} belongs to {ci.induct}, which is not in DFam.\n\
      The list companions join when a rule concluding about them acquires a proof \
      (Books/TypeSoundness/Registry/Registry.lean, header)."
  -- **The premise check.** `ruleForm` rewrites only the heads in `dFamField`; every other
  -- constant passes through *raw*. So a rule whose premise mentions an uncarried judgment
  -- would get a form like `DJudgeSeq Γ es τ Γ' → F.judge Γ (.seq es) τ Γ'` — a premise that is
  -- the **syntactic** relation rather than the family's. That re-admits every rule, including
  -- the unregistered ones, inside a judgment whose whole meaning is "derivable using only
  -- registered rules". Refused mechanically, by reading the constructor, rather than by
  -- trusting that nobody writes `register_dclink DJudge.seq`.
  let reached := dUncarriedJudgments.filter (ci.type.getUsedConstants.contains ·)
  unless reached.isEmpty do
    throwError m!"register_dclink: {ctor}'s premises reach \
{String.intercalate ", " (reached.map toString)}, which DFam does not carry.\n\
      `ruleForm` would leave that premise as the raw inductive, so the clink's obligation \
would quantify over derivations built from UNREGISTERED rules -- the registry's discipline, \
escaped through a side door.\n\
      Give DFam a field for it (and `dFamField` a row) before registering this rule \
(Books/TypeSoundness/Registry/Registry.lean, header)."
  let rule := toString (dRuleSuffix ctor)
  unless enabled rule do
    throwError m!"register_dclink: {ctor} is gated out by the {profileName} profile"
  if let some manifestName := manifest then
    let some (.defnInfo available) := env.find? manifestName
      | throwError "register_dclink: build_dclink_target must run first"
    let .lit (.strVal text) := available.value
      | throwError "register_dclink: invalid semantic field manifest"
    let absent := dFamField.filter fun (ind, field) =>
      ci.type.getUsedConstants.contains ind && !(text.splitOn " ").contains (toString field)
    unless absent.isEmpty do
      throwError m!"register_dclink: {ctor} needs unavailable semantic fields: {absent.map Prod.snd}"
  let sem := proofName
  unless (env.find? sem).isSome do
    throwError m!"register_dclink: {ctor} has no answer-typed proof.\n\
      Write `theorem {sem} : SemJudgeA …` in Books/TypeSoundness/Judgment/JudgeA.lean first.\n\
      A rule with no proof is not a rule (Books/TypeSoundness/Registry/Spec.lean)."
  let value ← liftTermElabM do
    let form ← ruleForm ``DFam dFamField ci.type
    let expected := mkApp form (mkConst target)
    unless (← isDefEq (← inferType (mkConst sem)) expected) do
      throwError m!"register_dclink: {ctor}'s semantic proof has the wrong constructor-derived type"
    let v := mkAppN (mkConst ``Clink.mk)
      #[mkConst ``DFam, mkConst ``dsynFam, mkConst target,
        mkStrLit s!"{ci.induct.getString!}.{ctor.getString!}", form, mkConst ctor, mkConst sem]
    let ty ← inferType v
    unless (← isDefEq ty (dclinkTy target)) do
      throwError m!"register_dclink: {ctor}'s clink is not a {dclinkTy target} (it is a {ty})"
    instantiateMVars v
  liftCoreM <| addAndCompile (.defnDecl
    { name := clinkName, levelParams := [], type := dclinkTy target, value := value,
      hints := .opaque, safety := .safe })

elab "register_dclink " id:ident : command => registerDClink (`Checker ++ id.getId)

end Checker.Soundness.Typed
