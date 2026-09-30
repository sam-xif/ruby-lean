import Ratchet.Judgment.DJudge
import Lean

/-! Derive rule-indexed judgments from the authoring constructors. Each conclusion
records its own rule and every premise trace, including uniform callback premises.
The generated declarations are kernel checked against their constructor types. -/
open Lean Meta Elab Command
namespace Ratchet.Audit

def families : List Name :=
  [``Ratchet.DJudge, ``Ratchet.DJudgeAll, ``Ratchet.DJudgeSeq, ``Ratchet.DJudgePairs,
   ``Ratchet.DJudgeRec, ``Ratchet.DJudgeRecAll, ``Ratchet.InitJudge,
   ``Ratchet.InitJudgeSeq, ``Ratchet.InitJudgeAll, ``Ratchet.DFlow,
   ``Ratchet.DFlowSeq, ``Ratchet.DFlowAll, ``Ratchet.DMethod,
   ``Ratchet.DMethodAll, ``Ratchet.DMethodSeq, ``Ratchet.DMethodFlow,
   ``Ratchet.DMethodFlowSeq]

def auditName (n : Name) : Name := `Ratchet.Audit ++ n.replacePrefix `Ratchet .anonymous

def ruleName (n : Name) : String :=
  if n.getPrefix == ``Ratchet.DJudge then n.getString!
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

elab "derive_audited_judgments" : command => do
  let groups := [[``Ratchet.InitJudge, ``Ratchet.InitJudgeSeq, ``Ratchet.InitJudgeAll],
    families.filter fun n => ![``Ratchet.InitJudge, ``Ratchet.InitJudgeSeq, ``Ratchet.InitJudgeAll].contains n]
  for group in groups do
    let types ← liftTermElabM <| group.mapM fun n => do
      let info ← getConstInfoInduct n
      let ty := mkForall `used .implicit traceTy info.type
      let ctors ← info.ctors.mapM fun c => do
        let ci ← getConstInfoCtor c
        return { name := auditName c, type := ← traceConstructor ci.type (ruleName c) : Constructor }
      return { name := auditName n, type := ty, ctors := ctors : InductiveType }
    liftCoreM <| addAndCompile (.inductDecl [] 0 types false)

derive_audited_judgments
end Ratchet.Audit
