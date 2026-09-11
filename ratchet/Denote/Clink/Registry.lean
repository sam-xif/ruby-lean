import Denote.Clink.Derive
import Denote.Rules

/-!
# `Denote/Clink/Registry.lean` — the registry, and what it is *not* a fraction of

Every `Judge` constructor with a semantic proof on file becomes a `Clink`; the registry is
the list of them; `JudgeC clinks` is the judgment they generate. Both halves are live: add a
`Sem.*` theorem in `Denote/Rules/` and the rule joins the judgment on the next build, add a
`Judge` constructor without one and it does not.

## The number this file reports, and the number it deliberately does not

The old report was **48 of 83** — rules justified over a denominator of rules *authored*,
with the gap standing for work owed on rules that were already in the judgment and already
reachable by a certificate. That framing is what `implementation-notes.md`'s EMERGENCY EXIT
ran out of: three sessions of verified work moved 47 → 48 → 48 → 48, because the unit of
measurement (one rule) and the unit of delivery (a layer) did not match, and because the
terminal step (one 83-case induction) could not be taken early.

Under the reshape there is no debt and no denominator:

* **Registered clinks** — each one proved, by construction. `judgeC_sem` holds for this
  registry *today*, unconditionally, and held for the registry of size 1.
* **Unregistered `Judge` constructors** — reported as **coverage**, because that is what they
  are: expressions `JudgeC` cannot type. They are not undischarged obligations; they are not
  in the judgment. Nothing is owed for them, and nothing unsound can be certified with them.

The consequence worth being explicit about: a certificate checked against `JudgeC clinks` is
sound whatever this number is, and one checked against `Judge` is not. `Ratchet/Validate.lean`
and `Ratchet/Deriv.lean` still target `Judge`, so **the reach of the checker is the honest
number to improve, and it is bounded by the registry rather than by the rule list.**

## Growth, from here

To add a rule: write the `Judge` constructor, write `Sem.<Family>.<rule>` against the derived
`Obl.<Family>.<rule>`, and build. That is the whole protocol, and it has no step in which the
rule exists without the proof. To add a rule whose obligation turns out **false** — the
§F19/§F23/§F24 case, which happened seven times under the old discipline — there is no step
at all: the proof does not exist, the clink does not build, the rule never enters `JudgeC`.
-/

set_option autoImplicit false

open Lean Meta Elab Command

namespace Ratchet.Denote

/-! ## §1 The registry, built by the command

Three constants, declared together so they cannot disagree: the registry itself and the two
report strings (strings rather than a `List String` literal for `Denote/Ladder.lean`'s
recorded reason — a `toExpr`-generated list-of-tuples makes the code generator fall over
here). -/

def clinksName : Name := `Ratchet.Denote.clinks
def registeredName : Name := `Ratchet.Denote.clinkRegistered
def unregisteredName : Name := `Ratchet.Denote.clinkUnregistered

/-- Register every provable rule, then bake the registry and the coverage lists. -/
elab "build_clink_registry" : command => do
  let (registered, without) ← registerAll
  let label (c : Name) : String :=
    match c with
    | .str (.str _ fam) rule => s!"{fam}.{rule}"
    | _ => c.toString
  let listExpr : Lean.Expr :=
    registered.foldr
      (fun c acc =>
        mkApp3 (mkConst ``List.cons [levelZero]) clinkTy (mkConst (clinkName c)) acc)
      (mkApp (mkConst ``List.nil [levelZero]) clinkTy)
  liftCoreM <| addAndCompile (.defnDecl
    { name := clinksName, levelParams := [],
      type := mkApp (mkConst ``List [levelZero]) clinkTy,
      -- `.abbrev`, not `.opaque`: a *derivation* has to discharge `c ∈ clinks`, and with an
      -- opaque registry there is nothing for `simp`/`List.Mem` to look at. The report
      -- strings below stay opaque -- nothing proves anything about them.
      value := listExpr, hints := .abbrev, safety := .safe })
  let mkStr (nm : Name) (xs : List Name) : CommandElabM Unit :=
    liftCoreM <| addAndCompile (.defnDecl
      { name := nm, levelParams := [], type := mkConst ``String,
        value := mkStrLit (String.intercalate " " (xs.map label)),
        hints := .opaque, safety := .safe })
  mkStr registeredName registered
  mkStr unregisteredName without

build_clink_registry

/-! ## §2 The soundness of the committed registry

Specialisations of `Denote/Clink/Spec.lean`'s one-line theorems at `clinks`. They are here
rather than inlined at use sites so that `#print axioms` has something to name, and so that
the statement a reader wants — *this* registry's judgment is semantically true — is on file
under a name. -/

/-- **Every `JudgeC clinks` derivation is semantically true.** Unconditional: no hypothesis
about the registry, no 83-case induction, no terminal clink. -/
theorem registry_sound {κ Γ I e τ κ' Γ' I'} (h : (JudgeC clinks).judge κ Γ I e τ κ' Γ' I') :
    SemJudge κ Γ I e τ κ' Γ' I' := judgeC_target h

/-- The same for the statement-sequence member, the one companion a whole-program derivation
goes through. -/
theorem registry_sound_seq {κ Γ I es τ κ' Γ' I'} (h : (JudgeC clinks).seq κ Γ I es τ κ' Γ' I') :
    SemJudgeSeq κ Γ I es τ κ' Γ' I' := judgeC_target_seq h

/-- And the registry is a **sub-judgment of the authoring surface**: anything it derives,
`Judge` derives. The converse is false while the coverage list below is non-empty, which is
the honest statement of where the work is. -/
theorem registry_syn {κ Γ I e τ κ' Γ' I'} (h : (JudgeC clinks).judge κ Γ I e τ κ' Γ' I') :
    Judge κ Γ I e τ κ' Γ' I' := judgeC_source h

/-! ## §3 The report -/

def registeredRules : List String :=
  if clinkRegistered.isEmpty then [] else clinkRegistered.splitOn " "

def unregisteredRules : List String :=
  if clinkUnregistered.isEmpty then [] else clinkUnregistered.splitOn " "

/-- `"Judge.intLit"` -> `"Judge"`. -/
def clinkFam (label : String) : String := (label.splitOn ".").headD label

private def pad (s : String) (n : Nat) : String :=
  if s.length ≥ n then s else s ++ String.ofList (List.replicate (n - s.length) ' ')

def clinkReport : String :=
  let fams := ["Judge", "JudgeAll", "JudgeKw", "JudgePairs", "JudgeSeq", "JudgeRescues",
               "JudgeConsts", "JudgeNested"]
  let rows := fams.filterMap fun fam =>
    let reg := (registeredRules.filter (fun r => clinkFam r == fam)).length
    let unreg := (unregisteredRules.filter (fun r => clinkFam r == fam)).length
    if reg + unreg == 0 then none
    else some s!"  {pad fam 14} {pad (toString reg) 4} registered   {unreg} not in the judgment"
  String.intercalate "\n"
    ([ "=== CLINK REGISTRY: rules in the certified judgment `JudgeC clinks` ===", ""]
      ++ rows
      ++ [ "  " ++ String.ofList (List.replicate 46 '-')
         , s!"  {pad "total" 14} {pad (toString registeredRules.length) 4} registered   \
{unregisteredRules.length} not in the judgment"
         , ""
         , "Every registered rule carries its own proof (`Clink.sem`); `registry_sound` is"
         , "unconditional and holds at every registry size. The right-hand column is"
         , "COVERAGE, not debt: an unregistered rule is not in `JudgeC` at all, so nothing"
         , "is owed for it and nothing unsound can be certified with it."
         , ""
         , "not in the judgment (a rule joins by acquiring a `Sem.<Family>.<rule>` proof):" ]
      ++ (unregisteredRules.take 12).map (fun r => s!"  {r}")
      ++ (if unregisteredRules.length > 12 then
            [s!"  ... and {unregisteredRules.length - 12} more"] else []))

/-! ## §4 The gate

Two `#guard`s and a `run_cmd`, all three build-time. They do not make the design sound --
the `Clink.sem` field does that -- they catch the ways the *registry* could drift from the
environment it is read out of. -/

-- The registry is non-empty, so `registry_sound` is not vacuously about nothing.
#guard clinks.length > 0

-- The registry and its report agree about its size. A mismatch would mean the list literal
-- and the string were built from different walks.
#guard clinks.length == registeredRules.length

/-! ### The growth gate

The report above is a measurement. **This is the gate**, and it is the part that answers "how
do we stop the judgment set growing unsoundly again".

`Judge` still has 35 constructors with no proof — they are legacy, they are what
`Ratchet/Validate.lean` and `Ratchet/Deriv.lean` still reach for, and they are frozen below
*by name*. A rule added to `Ratchet/Judge.lean` from now on is not on that list, so:

* **with a `Sem.<Family>.<rule>` proof** it registers, joins `JudgeC`, and the gate is silent;
* **without one** it lands in `unregisteredRules`, fails the subset check, and **the build
  goes red**.

So the discipline "a rule and its semantic justification are authored together" is enforced
for every rule after this commit, and the 35 exceptions are enumerated rather than implied.
The list only ever shrinks: proving one moves it to the registered column, and a stale entry
here is harmless (the check is a subset, not an equality), so closing a legacy rule needs no
edit to this list. -/

/-- The 35 `Judge` constructors that predate the clink discipline. Frozen: the gate below
fails if anything not on this list is unregistered. **Only ever shrink this.** -/
def legacyUnclinked : List String :=
  ["Judge.if'", "Judge.ifNoElse", "Judge.arrayLit", "Judge.hashLit", "Judge.defStmt",
   "Judge.callAsm", "Judge.callDef", "Judge.callDefKw", "Judge.classStmt", "Judge.newInst",
   "Judge.callMethod", "Judge.callMissing", "Judge.selfCall", "Judge.superCall",
   "Judge.zsuperCall", "Judge.callSMethod", "Judge.selfNew", "Judge.moduleStmt",
   "Judge.selfSCall", "Judge.closCall", "Judge.iterBlock", "Judge.iterSymPass",
   "Judge.iterClosPass", "Judge.callDefBlk", "Judge.callMethodBlk", "Judge.callSMethodBlk",
   "Judge.selfCallBlk", "Judge.yieldExpr", "Judge.vcallAsm", "Judge.vcallDef", "Judge.prim",
   "Judge.casgn", "Judge.begin'", "Judge.while'", "Judge.cpathAsgn"]

-- **The growth gate.** Every unregistered rule must be a named legacy exception; a new rule
-- authored without its semantic proof fails here, by name, at build time.
#guard unregisteredRules.all (fun r => legacyUnclinked.contains r)

-- The control for it: the list is not vacuously satisfied by being everything. If these ever
-- coincide, the gate above has stopped saying anything.
#guard registeredRules.length > 0 && legacyUnclinked.length < registeredRules.length

-- Every `Judge` constructor is in exactly one of the two columns, checked against the
-- kernel's own constructor list -- so a rule added to `Ratchet/Judge.lean` cannot be missing
-- from the report, and a registered rule cannot fail to be a rule.
run_cmd do
  let env ← getEnv
  let ctors ← match familyCtors env with
    | .ok cs => pure cs
    | .error msg => throwError msg
  let labels := ctors.map (fun (ind, c) => s!"{ind.getString!}.{c.getString!}")
  let reg := registeredRules
  let unreg := unregisteredRules
  unless labels.length == reg.length + unreg.length do
    throwError m!"clink registry: {labels.length} constructors but \
{reg.length} + {unreg.length} reported"
  for l in labels do
    unless reg.contains l || unreg.contains l do
      throwError m!"clink registry: {l} is in neither column"
  for l in reg do
    unless labels.contains l do
      throwError m!"clink registry: {l} is registered but is not a constructor"

#print axioms registry_sound
#print axioms registry_sound_seq
#print axioms registry_syn

end Ratchet.Denote
