import Books.TypeSoundness.Checker.Judgment.DJudge
import Lean

/-! Derive rule-indexed judgments from the authoring constructors. Each conclusion
records its own rule and every premise trace, including uniform callback premises.

These are the functions only. `Generate.lean` uses them to write the traced
judgments out as source (`Judgments.lean`), and `JudgmentsCheck.lean` uses them to
check that file. Nothing the checker's executable imports depends on this module,
because it needs Lean's metaprogramming library. -/
open Lean Meta Elab Command
namespace Checker.Audit

def families : List Name :=
  [``Checker.DJudge, ``Checker.DJudgeAll, ``Checker.DJudgeSeq, ``Checker.DJudgePairs,
   ``Checker.DJudgeRec, ``Checker.DJudgeRecAll, ``Checker.InitJudge,
   ``Checker.InitJudgeSeq, ``Checker.InitJudgeAll, ``Checker.DFlow,
   ``Checker.DFlowSeq, ``Checker.DFlowAll, ``Checker.DMethod,
   ``Checker.DMethodAll, ``Checker.DMethodSeq, ``Checker.DMethodFlow,
   ``Checker.DMethodFlowSeq]

def auditName (n : Name) : Name := `Checker.Audit ++ n.replacePrefix `Checker .anonymous

/-- The authoring judgment a traced one was derived from. -/
def rawName (n : Name) : Name := n.replacePrefix `Checker.Audit `Checker

/-- Make the first `n` binders of a `∀` implicit. -/
def implicitBinders : Nat → Lean.Expr → Lean.Expr
  | 0, e => e
  | n+1, .forallE nm dom body _ => .forallE nm dom (implicitBinders n body) .implicit
  | _, e => e

def ruleName (n : Name) : String :=
  if n.getPrefix == ``Checker.DJudge then n.getString!
  else s!"{n.getPrefix.getString!}.{n.getString!}"

def traceTy : Lean.Expr := mkApp (mkConst ``List [Level.zero]) (mkConst ``String)

def rewriteJudgments (e trace : Lean.Expr) : Lean.Expr :=
  e.replace fun x =>
    match x.getAppFn with
    | .const n _ =>
      if families.contains n then
        some (mkAppN (mkConst (auditName n)) (#[trace] ++ x.getAppArgs))
      else none
    | _ => none

partial def traceConstructor (ty : Lean.Expr) (rule : String) : MetaM Lean.Expr :=
  let rec visit (e : Lean.Expr) (subst : Array Lean.Expr) (traces : Array Lean.Expr) : MetaM Lean.Expr := do
    match e with
    | .forallE nm dom body bi =>
      let dom := dom.instantiateRev subst
      if dom.getUsedConstants.any families.contains then
        withLocalDecl (Name.mkSimple s!"used_{traces.size}") .implicit traceTy fun used =>
          withLocalDecl nm bi (rewriteJudgments dom used) fun x => do
            let tail ← visit body (subst.push x) (traces.push used)
            mkForallFVars #[used, x] tail
      else
        withLocalDecl nm bi dom fun x => do
          let tail ← visit body (subst.push x) traces
          mkForallFVars #[x] tail
    | _ =>
      let nil := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``String)
      let appended := traces.foldr (fun t acc =>
        mkApp3 (mkConst ``List.append [Level.zero]) (mkConst ``String) t acc) nil
      let used := mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``String)
        (mkStrLit rule) appended
      return rewriteJudgments (e.instantiateRev subst) used
  visit ty #[] #[]

end Checker.Audit
