import Denote.Typed.Safety

/-!
# `Denote/Typed/RuleAudit.lean` — which rules the safety proof **actually** uses

`Denote/Typed/Safety.lean` §4 answers "which registered rules does the end-to-end safety
claim exercise?" *syntactically*: `rulesUsed` maps an `Expr` head to a rule name, and the
answer is read off the programs in `safeRungs`. That is a **prediction**, and it rests on a
property stated there as prose — *each `Expr` head admits exactly one `DJudge` rule*. Nothing
checked it. A second rule on an existing head would make the predictor over-claim coverage,
silently, in the direction that turns the coverage gate green.

This module computes the same set the other way: **off the proof term**. A derivation in the
certified judgment is Church-encoded, so it *is* the rule applied to the closure hypothesis —

    theorem derivD_strLit … := fun _ hF => hF DClink.strLit (by simp [dclinks])

— and the rules a proof uses are the clink constants handed to that hypothesis. The two
answers are then required to agree, per rung (§3). The prose is now a checked fact.

## Why not `Expr.getUsedConstants`

Because it reports **every** rule for every rung. The `by simp [dclinks]` membership
side-condition unfolds the nine-element registry list into the proof term, so a flat constant
scan of `derivD_intLit` returns all nine clinks. That is not a near-miss: it is a gate that
reads "full coverage" unconditionally. The extraction below is therefore *structural* — a
clink counts only in argument position of an application whose head is a **bound variable**
(`hF`). The membership proof is an argument too, but it is not a clink constant, so it drops
out.

## Failure directions

Under-reporting is safe: if a derivation is ever built in a shape the walk does not
recognise, its rules go missing, `rulesExercised` shrinks, and the coverage gate in §4 goes
**red**. Over-reporting is the dangerous one, and it needs a rule-*generic* lemma to apply a
clink to a bound variable. None does today — `dregistry_safe`, `dInv_safe` and `dInv_init`
discharge closure through `Clink.sem` projections, not by application — and §2's controls pin
that by asserting each rung's rule set **exactly**, not as a superset.

## A hazard worth recording

The extractor lives in a top-level `RuleAudit` namespace rather than under
`Ratchet.Denote.Typed`, because inside `namespace Ratchet` the identifier `Expr` resolves to
`Ratchet.Expr` and every `Lean.Expr` operation fails to elaborate. The generated constant is
placed into `Ratchet.Denote.Typed` explicitly.
-/

namespace RuleAudit
open Lean Elab Command Meta

/-! ## §1 The extractor -/

def isClink (n : Name) : Bool := (`Ratchet.Denote.Typed.DClink).isPrefixOf n

/-- Clink constants handed to a **bound variable** — the closure hypothesis `hF`. See the
module docstring for why this is structural rather than a flat constant scan. -/
partial def clinksApplied (e : Lean.Expr) (acc : Array Name) : Array Name :=
  let acc :=
    if e.isApp && (e.getAppFn.isBVar || e.getAppFn.isFVar) then
      e.getAppArgs.foldl (init := acc) fun acc a =>
        match a with
        | .const n _ => if isClink n then acc.push n else acc
        | _ => acc
    else acc
  match e with
  | .app f a => clinksApplied a (clinksApplied f acc)
  | .lam _ t b _ => clinksApplied b (clinksApplied t acc)
  | .forallE _ t b _ => clinksApplied b (clinksApplied t acc)
  | .letE _ t v b _ => clinksApplied b (clinksApplied v (clinksApplied t acc))
  | .mdata _ b => clinksApplied b acc
  | .proj _ _ b => clinksApplied b acc
  | _ => acc

def mentions (ty : Lean.Expr) (n : Name) : Bool := ty.getForallBody.getUsedConstants.contains n

/-- Descend only into constants that are themselves derivations or safety statements. Without
this the walk drags in the whole `Semantics/` closure: 24s rather than 0.6s, for the same
answer. -/
def isDeriv (ty : Lean.Expr) : Bool :=
  mentions ty ``Ratchet.Denote.Typed.DJudgeC || mentions ty ``Ratchet.Denote.StuckFree

/-- A rung theorem: safety, at the booted machine. -/
def isRungThm (ty : Lean.Expr) : Bool :=
  mentions ty ``Ratchet.Denote.StuckFree && mentions ty ``Ratchet.Denote.bootMachine

/-- **The rules `n`'s proof uses**, read off the proof term.

`value?` needs `allowOpaque := true` or theorems return `none` and this answers `[]` for
everything — which the `#guard`s below would catch, but loudly rather than by accident. -/
def rulesOfProof (env : Environment) (n : Name) : List String := Id.run do
  let mut seen : NameSet := {}
  let mut work := [n]
  let mut hits : Array Name := #[]
  while !work.isEmpty do
    let c := work.head!; work := work.tail!
    if seen.contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    let some v := ci.value? (allowOpaque := true) | continue
    hits := clinksApplied v hits
    for c' in v.getUsedConstants do
      if !isClink c' && (c' == n || (env.find? c').any (fun i => isDeriv i.type)) then
        work := work ++ [c']
  return hits.toList.eraseDups.map (·.getString!)

/-- The rung theorems, discovered from **`safeRungs_safe`'s own proof term** — the theorem
already proved over `safeRungs`, which `SemLadder.lean` already ties to the corpus. So this
module adds no hand-maintained list of names: delete a rung's theorem and it leaves here too,
by the same edit that makes `safeRungs_safe` fail to typecheck. -/
def rungThms (env : Environment) : List Name :=
  match (env.find? ``Ratchet.Denote.Typed.safeRungs_safe).bind
          (·.value? (allowOpaque := true)) with
  | none => []
  | some v =>
    v.getUsedConstants.toList.filter fun c =>
      (env.find? c).any (fun i => isRungThm i.type)

/-! ## §2 …emitted as ordinary data, so the gates below are `#guard`s -/

def strTy : Lean.Expr := mkConst ``String
def listStrTy : Lean.Expr := mkApp (mkConst ``List [Level.zero]) strTy
def pairTy : Lean.Expr := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) strTy listStrTy

def mkStrList (xs : List String) : Lean.Expr :=
  xs.foldr (fun s acc => mkApp3 (mkConst ``List.cons [Level.zero]) strTy (mkStrLit s) acc)
           (mkApp (mkConst ``List.nil [Level.zero]) strTy)

def mkTable (xs : List (String × List String)) : Lean.Expr :=
  xs.foldr
    (fun p acc =>
      let pair := mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) strTy listStrTy
                    (mkStrLit p.1) (mkStrList p.2)
      mkApp3 (mkConst ``List.cons [Level.zero]) pairTy pair acc)
    (mkApp (mkConst ``List.nil [Level.zero]) pairTy)

/-- Generates `Ratchet.Denote.Typed.rulesFromProofs`. Live in both directions, exactly as
`build_dclink_registry` is: it reads the environment, never a list someone maintains. -/
elab "emit_rule_audit" : command => do
  let env ← getEnv
  let table := (rungThms env).map fun t => (t.getString!, rulesOfProof env t)
  if table.isEmpty then
    throwError "emit_rule_audit: no rung theorems discovered -- the extractor is vacuous, \
which would make every gate downstream of it green for the wrong reason"
  liftCoreM <| addAndCompile (.defnDecl
    { name := `Ratchet.Denote.Typed.rulesFromProofs, levelParams := [],
      type := mkApp (mkConst ``List [Level.zero]) pairTy,
      value := mkTable table, hints := .abbrev, safety := .safe })

emit_rule_audit

end RuleAudit

namespace Ratchet.Denote.Typed

/-! ## §3 The cross-check: the predictor and the proof agree, per rung

This is the gate the module exists for. `rulesUsed` (syntactic, `Safety.lean` §4) and
`rulesFromProofs` (read off the proof term) are two independent answers to the same question,
and they must match on every rung. A disagreement means one of two things, both worth a red
build: the head→rule table drifted from `DJudge`, or a rung's proof used a different rule than
its program's shape implies. -/

/-- The safety theorem for a rung: `001-int-lit` ↦ `safe_001_int_lit`. A convention, and a
self-checking one — get it wrong and the lookup below returns `[]` and the guard fails. -/
def rungThmName (rung : String) : String :=
  "safe_" ++ String.ofList (rung.toList.map fun c => if c == '-' then '_' else c)

def proofRules (thm : String) : List String :=
  ((rulesFromProofs.find? (·.1 == thm)).map (·.2)).getD []

/-- Set equality on small lists: `rulesUsed` carries duplicates and program order, the proof
walk carries traversal order. -/
def sameRules (a b : List String) : Bool :=
  a.all (b.contains ·) && b.all (a.contains ·)

-- **The cross-check.** Every rung's predicted rule set equals the set its proof uses.
#guard safeRungs.all fun q => sameRules (rulesUsed q.2) (proofRules (rungThmName q.1))

-- …and the table covers every rung, so the guard above cannot pass by looking nothing up.
#guard rulesFromProofs.length == safeRungs.length
#guard safeRungs.all fun q => (rulesFromProofs.find? (·.1 == rungThmName q.1)).isSome

-- No rung's proof is empty, which is what a silently-broken extractor produces.
#guard rulesFromProofs.all fun p => !p.2.isEmpty

/-! ### Controls on the extractor itself

Asserted **exactly**, not as a superset: the failure mode this module is defending against is
over-reporting, and a `⊇` control cannot see it. If a rule-generic lemma ever starts applying
a clink to a bound variable, these are what go red. -/

#guard proofRules "safe_001_int_lit" == ["intLit"]
#guard proofRules "safe_004_str_lit" == ["strLit"]
#guard proofRules "safe_008_neg_int_lit" == ["intLit"]

/-! ## §4 The coverage gate, now over the proof-derived set

`Safety.lean`'s version of this runs over `rulesPredicted`; this one is the authoritative
statement, because its left-hand side is what the proofs do rather than what the table says
they do. -/

/-- **The rules the end-to-end safety proof exercises**, unioned over the rungs and derived
from the proof terms. This is the number `SemLadder.lean` reports. -/
def rulesExercised : List String := (rulesFromProofs.flatMap (·.2)).eraseDups

-- Every registered rule is exercised end to end, or is a named exception.
#guard dRegisteredRules.all fun r => rulesExercised.contains r || unexercised.contains r

-- The exceptions are real: registered, and genuinely not exercised.
#guard unexercised.all fun r => dRegisteredRules.contains r && !rulesExercised.contains r

-- And no rung's proof used a rule that is not registered, which is impossible by
-- construction (`DJudgeC dclinks` admits only registered rules) and therefore a good control
-- on the extractor rather than on the registry.
#guard rulesExercised.all fun r => dRegisteredRules.contains r

end Ratchet.Denote.Typed
