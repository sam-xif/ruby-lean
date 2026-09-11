import Denote.Typed.JudgeA
import Denote.Clink.Form

/-!
# `Denote/Typed/Clink.lean` — the typed ladder's clink registry

`Denote/Clink/Spec.lean`'s mechanism, instantiated at `Ratchet/Check.lean`'s judgment and
`Denote/Typed/JudgeA.lean`'s **answer-typed** semantic reading. Nothing is copied: `Clink`,
`Closed`, `closed_target`/`closed_source` and `register_clink`'s form derivation are generic
in the family record type, and this file supplies the record.

**These are the project's first answer-typed clinks.** The 48 in `Denote/Clink/Registry.lean`
are `SemJudge`-shaped — *if the run returns a value, the value is in the type* — which
`Denote/Sem/NoProgress.lean` proves says nothing about a run that escapes. The eight here are
`SemJudgeA`-shaped: the hypothesis is an **answer**, and the conclusion says whether the run
reached a **type-stuck** outcome. So a rule registered here carries the content the old shape
was missing, and the two registries are deliberately separate rather than merged: they are
clinks against different statements, and merging them would let the weaker one launder as the
stronger.

## The family has one member, and that is the current state rather than a simplification

`DFam` carries `judge` only. `DJudgeAll`/`DJudgeSeq` join it when the first rule concluding
about them acquires a proof — which needs an answer-typed reading of a *list* evaluation, and
that reading has no consumer yet (`prim` and `seq` are both behind `RunAPushK`,
`Denote/Typed/JudgeA.lean` §4). Adding a field now would mean inventing a statement nothing
checks; `register_dclink` refuses a constructor whose inductive is not in the table, so the
list rules are refused by name rather than by omission.

## What the registry covers

Eight rules — the seven literals and `var` — and therefore exactly the programs those rules
derive: a single literal, or a single local read. That is **corpus rungs 001–008**, which are
the eight literal rungs. Rungs 009–018 are checked by `Ratchet/Check.lean` and are *not* in
this judgment, because `prim`, `seq`, `vasgn` and `if'` are not registered.
-/

set_option autoImplicit false

open Lean Meta Elab Command

namespace Ratchet.Denote.Typed

open RubyCore Ratchet Ratchet.Denote

/-! ## §1 The family -/

/-- The typed judgment as a record of predicates. One member today; see the header. -/
structure DFam where
  judge : Env → Ratchet.Expr → Ty → Env → Prop

/-- The syntactic reading: `Ratchet/Check.lean`'s own relation. -/
def dsynFam : DFam := { judge := DJudge }

/-- The **answer-typed semantic reading, conjoined with the invariant**
(`Denote/Typed/JudgeA.lean` §1b). This is the field that makes a clink here mean something: a
rule cannot join the judgment without proving both that the answer is in the type *and* that a
machine evaluating it under a well-typed continuation is safe. -/
def dsemFam : DFam := { judge := SemSafeA }

/-! ## §2 Registration

`register_dclink DJudge.intLit`: read the constructor, derive its `form` by replacing the
judgment head with a projection of a `DFam` parameter, demand the proof, declare the clink.
The proof must be named `SemA.<rule>` and live in `Denote/Typed/JudgeA.lean`; absence is a
build failure, and so is a proof of a different statement (the field's type is computed from
the rule). -/

/-- The one-row field table: `DJudge` ↦ `DFam.judge`. A constructor of `DJudgeAll` or
`DJudgeSeq` is refused here, by name — see the header for why that is the honest state. -/
def dFamField : List (Name × Name) := [(``Ratchet.DJudge, ``DFam.judge)]

def dclinkTy : Lean.Expr :=
  mkApp3 (mkConst ``Clink) (mkConst ``DFam) (mkConst ``dsynFam) (mkConst ``dsemFam)

/-- `SemA.intLit` from `Ratchet.DJudge.intLit` — where the answer-typed proof must live. -/
def dsemName (ctor : Name) : Name :=
  match ctor with
  | .str _ rule => `Ratchet.Denote.Typed.SemA ++ Name.mkSimple rule
  | _ => `Ratchet.Denote.Typed.SemA ++ ctor

def dclinkName (ctor : Name) : Name :=
  match ctor with
  | .str _ rule => `Ratchet.Denote.Typed.DClink ++ Name.mkSimple rule
  | _ => `Ratchet.Denote.Typed.DClink ++ ctor

def registerDClink (ctor : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some (.ctorInfo ci) := env.find? ctor
    | throwError m!"register_dclink: {ctor} is not a constructor"
  unless dFamField.any (fun (ind, _) => ind == ci.induct) do
    throwError m!"register_dclink: {ctor} belongs to {ci.induct}, which is not in DFam.\n\
      The list companions join when a rule concluding about them acquires a proof \
      (Denote/Typed/Clink.lean, header)."
  let sem := dsemName ctor
  unless (env.find? sem).isSome do
    throwError m!"register_dclink: {ctor} has no answer-typed proof.\n\
      Write `theorem {sem} : SemJudgeA …` in Denote/Typed/JudgeA.lean first.\n\
      A rule with no proof is not a rule (Denote/Clink/Spec.lean)."
  let value ← liftTermElabM do
    let form ← ruleForm ``DFam dFamField ci.type
    let v := mkAppN (mkConst ``Clink.mk)
      #[mkConst ``DFam, mkConst ``dsynFam, mkConst ``dsemFam,
        mkStrLit s!"DJudge.{ctor.getString!}", form, mkConst ctor, mkConst sem]
    let ty ← inferType v
    unless (← isDefEq ty dclinkTy) do
      throwError m!"register_dclink: {ctor}'s clink is not a {dclinkTy} (it is a {ty})"
    instantiateMVars v
  liftCoreM <| addAndCompile (.defnDecl
    { name := dclinkName ctor, levelParams := [], type := dclinkTy, value := value,
      hints := .opaque, safety := .safe })

elab "register_dclink " id:ident : command => registerDClink (`Ratchet ++ id.getId)

/-- Every `DJudge` constructor with an answer-typed proof on file, registered; the rest
reported. Live in both directions, exactly as `registerAll` is. -/
elab "build_dclink_registry" : command => do
  let env ← getEnv
  let some (.inductInfo vi) := env.find? ``Ratchet.DJudge
    | throwError "Ratchet.DJudge is not an inductive"
  let mut reg : List Name := []
  let mut unreg : List Name := []
  for c in vi.ctors do
    if (env.find? (dsemName c)).isSome then
      registerDClink c
      reg := reg ++ [c]
    else
      unreg := unreg ++ [c]
  let listExpr : Lean.Expr :=
    reg.foldr
      (fun c acc =>
        mkApp3 (mkConst ``List.cons [levelZero]) dclinkTy (mkConst (dclinkName c)) acc)
      (mkApp (mkConst ``List.nil [levelZero]) dclinkTy)
  liftCoreM <| addAndCompile (.defnDecl
    { name := `Ratchet.Denote.Typed.dclinks, levelParams := [],
      type := mkApp (mkConst ``List [levelZero]) dclinkTy,
      value := listExpr, hints := .abbrev, safety := .safe })
  let mkStr (nm : Name) (xs : List Name) : CommandElabM Unit :=
    liftCoreM <| addAndCompile (.defnDecl
      { name := nm, levelParams := [], type := mkConst ``String,
        value := mkStrLit (String.intercalate " " (xs.map (·.getString!))),
        hints := .opaque, safety := .safe })
  mkStr `Ratchet.Denote.Typed.dclinkRegistered reg
  mkStr `Ratchet.Denote.Typed.dclinkUnregistered unreg

build_dclink_registry

/-! ## §3 The certified judgment and its soundness

`Denote/Clink/Spec.lean`'s `JudgeC` constructs a `Fam`, so it does not apply here; the
one-member counterpart is three lines. The soundness theorem is the same one line, and it is
**unconditional**: instantiate the family at `dsemFam` and discharge closure from the clinks'
own `sem` fields. -/

def DJudgeC (R : List (Clink dsynFam dsemFam)) : DFam where
  judge Γ e τ Γ' := ∀ F : DFam, Closed R F → F.judge Γ e τ Γ'

/-- **Every derivation in the certified typed judgment is semantically true and safe.**
Unconditional at every registry size: the hypothesis is discharged from the clinks' own `sem`
fields, so this theorem was green when the registry had one rule in it and cannot stop being
green as it grows. -/
theorem dregistry_sound {Γ : Env} {e : Ratchet.Expr} {τ : Ty} {Γ' : Env}
    (h : (DJudgeC dclinks).judge Γ e τ Γ') : SemSafeA Γ e τ Γ' :=
  h dsemFam (closed_target dclinks)

/-- The answer-typed half: for every run that reaches an answer, the value is in the type or
the escape is not type-stuck. -/
theorem dregistry_semJudge {Γ : Env} {e : Ratchet.Expr} {τ : Ty} {Γ' : Env}
    (h : (DJudgeC dclinks).judge Γ e τ Γ') : SemJudgeA Γ e τ Γ' := (dregistry_sound h).1

/-- **The invariant half**, as the clinks state it: a machine evaluating a certified
expression under a continuation that accepts its type is safe. Quantified over the
continuation and the answer type, which is what makes it usable at a machine part-way through
a larger program. -/
theorem dregistry_safeUnder {Γ : Env} {e : Ratchet.Expr} {τ : Ty} {Γ' : Env}
    (h : (DJudgeC dclinks).judge Γ e τ Γ') : SafeUnder Γ e τ Γ' := (dregistry_sound h).2

/-- **Safety of every program the fragment types**, which is the theorem the ladder exists to
produce: from any conformant machine, a certified program never reaches a type-stuck outcome —
at any fuel, whether it returns, escapes, diverges or gates.

One line, and the line is the point: it is `dregistry_safeUnder` at the **empty continuation**
(`DKontOk.nil`, with the answer type pinned to the program's own). The invariant does the
work; this instantiates it. `Denote/Typed/Safety.lean` lands it on the corpus's own rungs at
the real prelude-booted machine. -/
theorem dregistry_safe {Γ : Env} {e : Ratchet.Expr} {τ : Ty} {Γ' : Env}
    (h : (DJudgeC dclinks).judge Γ e τ Γ')
    {m : Machine} (hm : StateOk Ratchet.ctx0 Γ .ivar0 m) : StuckFree m e :=
  dregistry_safeUnder h τ (evalFrom m e) (StateOk_reCtl hm _ _) rfl DKontOk.nil

/-- …and it is a `DJudge` derivation, so `Ratchet/Check.lean`'s checker and this judgment are
about the same rules. -/
theorem dregistry_syn {Γ : Env} {e : Ratchet.Expr} {τ : Ty} {Γ' : Env}
    (h : (DJudgeC dclinks).judge Γ e τ Γ') : DJudge Γ e τ Γ' :=
  h dsynFam (closed_source dclinks)

/-! ## §4 The report and the gate -/

def dRegisteredRules : List String :=
  if dclinkRegistered.isEmpty then [] else dclinkRegistered.splitOn " "

def dUnregisteredRules : List String :=
  if dclinkUnregistered.isEmpty then [] else dclinkUnregistered.splitOn " "

-- Non-empty, so `dregistry_sound` is not vacuously about nothing.
#guard dclinks.length > 0

-- The registry and its report agree about its size.
#guard dclinks.length == dRegisteredRules.length

-- Eight registered, and the five unregistered rules are the composite ones, all of which are
-- behind `RunAPushK` (`Denote/Typed/JudgeA.lean` §4). A sixth appearing here without a proof
-- is a rule authored without its justification, and this guard is what says so.
#guard dRegisteredRules.length == 8
#guard dUnregisteredRules == ["vasgn", "seq", "prim", "if'"]

#print axioms dregistry_sound
#print axioms dregistry_syn

end Ratchet.Denote.Typed
