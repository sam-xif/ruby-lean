import Denote.Clink.Spec
import Denote.Sem.Obligations
import Lean.Elab.Command

/-!
# `Denote/Clink/Derive.lean` — `register_clink`, the only way a rule enters the judgment

One command. `register_clink Judge.vasgn` does four things, and the third is the gate:

1. reads `Ratchet.Judge.vasgn`'s type out of the environment;
2. abstracts the eight family heads into a parameter, producing the rule's `form : RuleF`
   — the same substitution `Denote/Sem/Obligations.lean` performs, except that the
   replacement is a **projection of a bound `Fam`** rather than a second constant, which is
   what makes one authored rule yield both readings;
3. looks for `Sem.Judge.vasgn` and **fails the build if it is absent**;
4. declares `Clink.Judge.vasgn : Clink` with `syn := Judge.vasgn` and `sem := Sem.Judge.vasgn`.

Step 4 is where the kernel does the work this whole design rests on. `Clink.syn`'s type is
`form synFam` and `Clink.sem`'s is `form semFam`; both are *computed from the rule*, so the
constructor and the proof are each checked against a statement neither of them chose. A
`Sem.*` theorem proving something weaker, or something about a different rule, does not
typecheck here — which is the same guarantee `Denote/Ladder.lean`'s `isDefEq` check gave as a
*report*, now enforced as a *declaration*.

## Why not accept a hand-written `form`

Because then `form` would be a third transcription and could disagree with both readings —
exactly the failure `Obligations.lean`'s module docstring was written to prevent ("83 chances
to weaken an obligation by a typo"). The constructor is the single source; `form` is derived
from it; `syn` and `sem` are it, instantiated.

## What the command does *not* do

It does not prove anything. `Sem.<Family>.<rule>` is written by hand, in `Denote/Rules/`,
against the obligation `Obligations.lean` derived — and until it exists, `register_clink`
refuses and the rule stays out of `JudgeC`. That refusal is the reshaping.
-/

set_option autoImplicit false

open Lean Meta Elab Command Term

namespace Ratchet.Denote

/-- The family head → the `Fam` field that replaces it. The one hand-written table, checked
against the kernel's own view of the mutual family by `Obligations.lean`'s `run_cmd` (and
against the signatures by every `register_clink`, since a wrong pairing makes `form synFam`
fail to match the constructor). -/
def famField : List (Name × Name) :=
  [(``Ratchet.Judge, ``Ratchet.Denote.Fam.judge),
   (``Ratchet.JudgeAll, ``Ratchet.Denote.Fam.all),
   (``Ratchet.JudgeKw, ``Ratchet.Denote.Fam.kw),
   (``Ratchet.JudgePairs, ``Ratchet.Denote.Fam.pairs),
   (``Ratchet.JudgeSeq, ``Ratchet.Denote.Fam.seq),
   (``Ratchet.JudgeRescues, ``Ratchet.Denote.Fam.rescues),
   (``Ratchet.JudgeConsts, ``Ratchet.Denote.Fam.consts),
   (``Ratchet.JudgeNested, ``Ratchet.Denote.Fam.nested)]

/-- The registry's clink type: source `synFam`, target `semFam`. `Clink` is parameterised by
both (`Spec.lean` §2) so that restating the semantic reading is a new registry rather than an
edit to the mechanism; this is the pairing the committed registry uses. -/
def clinkTy : Lean.Expr :=
  mkApp3 (mkConst ``Clink) (mkConst ``Fam) (mkConst ``synFam) (mkConst ``semFam)

/-- `Clink.Judge.vasgn` from `Ratchet.Judge.vasgn`. -/
def clinkName (ctor : Name) : Name :=
  match ctor with
  | .str (.str _ fam) rule => `Ratchet.Denote.Clink ++ Name.mkSimple fam ++ Name.mkSimple rule
  | _ => `Ratchet.Denote.Clink ++ ctor

/-- The rule, with the family abstracted: `fun F : <famTy> => <ctor type>[<head> := F.<field>, …]`.

Parameterised by the family record and its field table, so the typed ladder's own family
(`Denote/Typed/Clink.lean`'s `DFam`) reuses it rather than copying it.

`withLocalDeclD` rather than a raw `bvar`, because `Expr.replace` visits subterms under
binders and a de Bruijn index would be wrong at every depth but the outermost. An `fvar` is
depth-independent, and `mkLambdaFVars` puts the binder back. -/
def ruleForm (famTy : Name) (table : List (Name × Name)) (ctorType : Lean.Expr) :
    MetaM Lean.Expr :=
  withLocalDeclD `F (mkConst famTy) fun f => do
    let body := Lean.Expr.replace (fun x =>
      match x with
      | .const n _ => (table.lookup n).map (fun fld => mkApp (mkConst fld) f)
      | _ => none) ctorType
    mkLambdaFVars #[f] body

/-- Declare `Clink.<Family>.<rule>`, or fail with the reason.

The failure modes are all reported rather than worked around: no such constructor, no
`Sem.*` proof on file, or a `Sem.*` whose type is not the derived obligation (in which case
the kernel rejects the `sem` field and says so). -/
def registerClink (ctor : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some (.ctorInfo ci) := env.find? ctor
    | throwError m!"register_clink: {ctor} is not a constructor of the Judge family"
  unless famField.any (fun (ind, _) => ind == ci.induct) do
    throwError m!"register_clink: {ctor} belongs to {ci.induct}, which is not in the family"
  let sem := semName ctor
  unless (env.find? sem).isSome do
    throwError m!"register_clink: {ctor} has no semantic proof.\n\
      Write `theorem {sem} : {oblName ctor} := …` in Denote/Rules/ first.\n\
      A rule with no proof is not a rule (Denote/Clink/Spec.lean)."
  let value ← liftTermElabM do
    let form ← ruleForm ``Fam famField ci.type
    let v := mkAppN (mkConst ``Clink.mk)
      #[mkConst ``Fam, mkConst ``synFam, mkConst ``semFam,
        mkStrLit s!"{ci.induct.getString!}.{ctor.getString!}", form, mkConst ctor, mkConst sem]
    -- Kernel-check here rather than at `addDecl`, so the error names the field.
    let ty ← inferType v
    unless (← isDefEq ty clinkTy) do
      throwError m!"register_clink: {ctor}'s clink is not a {clinkTy} (it is a {ty})"
    instantiateMVars v
  liftCoreM <| addAndCompile (.defnDecl
    { name := clinkName ctor, levelParams := [], type := clinkTy, value := value,
      hints := .opaque, safety := .safe })

/-- `register_clink Judge.vasgn` — the name is relative to `Ratchet`, as it is written in
`Ratchet/Judge.lean`. -/
elab "register_clink " id:ident : command => do
  registerClink (`Ratchet ++ id.getId)

/-- Every constructor of the family that has a semantic proof on file, registered; the rest
reported. Returns the two lists so the registry file can bake them into its report.

This is the command that makes the registry *live*: add a `Sem.*` theorem and the rule joins
`JudgeC` on the next build; add a `Judge` constructor with no proof and it does not, and the
coverage line says so. Neither direction needs anyone to remember to edit a list. -/
def registerAll : CommandElabM (List Name × List Name) := do
  let env ← getEnv
  let ctors ← match familyCtors env with
    | .ok cs => pure cs
    | .error msg => throwError msg
  let mut registered : List Name := []
  let mut without : List Name := []
  for (_, c) in ctors do
    if (env.find? (semName c)).isSome then
      registerClink c
      registered := registered ++ [c]
    else
      without := without ++ [c]
  return (registered, without)

end Ratchet.Denote
