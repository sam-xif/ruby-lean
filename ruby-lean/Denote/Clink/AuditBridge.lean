import Denote.Clink.Registry
import Ratchet.Audit.Erase
import Ratchet.Audit.Permissions

/-! Constructor-derived certification of traced judgments. Only enabled clinks
are referenced; the permission index accounts for every recursive and uniform
premise. These generators produce ordinary kernel-checked proofs. -/
open Lean Meta Elab Command Tactic
namespace Ratchet.Denote.Typed
open Ratchet.Audit

#guard families == dJudgmentInductives

def certificateName (n : Name) : Name := `Ratchet.Denote.Typed.Audited ++ n.replacePrefix `Ratchet.Audit .anonymous

partial def activeMember (clink xs : Lean.Expr) : MetaM Lean.Expr := do
  let list ← whnf xs
  let args := list.getAppArgs
  unless list.getAppFn.isConstOf ``List.cons && args.size == 3 do
    throwError "enabled clink is absent from the active registry"
  if ← isDefEq args[1]! clink then
    return mkApp3 (mkConst ``List.Mem.head [Level.zero]) args[0]! clink args[2]!
  let tail ← activeMember clink args[2]!
  return mkApp5 (mkConst ``List.Mem.tail [Level.zero]) args[0]! clink args[1]! args[2]! tail

elab "certify_audit_case" ctor:ident F:ident hF:ident : tactic => withMainContext do
  let raw ← getConstInfoCtor ctor.getId
  let traced ← getConstInfoCtor (auditName ctor.getId)
  let group := (← getConstInfoInduct raw.induct).all
  let domains : Array Lean.Expr ← forallTelescope raw.type fun xs _ => xs.mapM fun x => return (← inferType x)
  let count := traced.type.getForallArity
  let recursive := domains.filter fun d => d.getUsedConstants.any group.contains
  let locals := (← getLCtx).getFVarIds.map mkFVar
  let fields := locals.extract (locals.size - count - recursive.size - 1) locals.size
  let he := fields.back!
  let mut rest ← mkAppM ``trace_tail #[he]
  let mut args := #[]
  let mut cursor := 0
  let mut ih := count
  let f ← getFVarFromUserName F.getId
  let hf ← getFVarFromUserName hF.getId
  for dom in domains do
    if dom.getUsedConstants.any families.contains then
      let premise := fields[cursor+1]!
      let flag ← mkAppM ``trace_left #[rest]
      rest ← mkAppM ``trace_right #[rest]
      cursor := cursor + 2
      let proof ← if dom.getUsedConstants.any group.contains then do
        let induction := fields[ih]!
        ih := ih + 1
        forallTelescope (← inferType premise) fun codes _ => do
          mkLambdaFVars codes (mkApp (mkAppN induction codes) flag)
      else do
        let d ← inferType premise
        let name := (certificateName d.getAppFn.constName!).str "certified"
        pure <| mkAppN (mkConst name) (d.getAppArgs ++ #[premise, f, hf, flag])
      args := args.push proof
    else
      args := args.push fields[cursor]!
      cursor := cursor + 1
  let clink := mkConst (dclinkName ctor.getId)
  let member ← activeMember clink (mkConst ``dclinks)
  let value := mkAppN (mkAppN hf #[clink, member]) args
  let goal ← getMainGoal
  unless ← isDefEq (← inferType value) (← goal.getType) do
    throwError "audited clink certificate mismatch"
  goal.assign value
  replaceMainGoal []

elab "certify_audited" rec:ident h:ident F:ident hF:ident : tactic => do
  let .recInfo ri ← getConstInfo rec.getId | throwError "expected a mutual recursor"
  let mut text := s!"refine {rec.getId} "
  for (n, i) in ri.all.zipIdx do
    let ii ← getConstInfoInduct (rawName n)
    let args := (List.range ii.numIndices).map fun j => s!"a{j}"
    let some fld := dFamField.lookup (rawName n) | throwError "unknown judgment family"
    text := text ++ s!"(motive_{i+1} := " ++ "fun {used} " ++
      s!"{String.intercalate " " args} _ => Ratchet.Audit.rulesEnabled Ratchet.clinkEnabled used = true → {fld} {F.getId} {String.intercalate " " args}) "
  text := text ++ String.intercalate " " (List.replicate ri.numMinors "?_") ++ s!" {h.getId}\nall_goals intros\n"
  for n in ri.all do
    let ii ← getConstInfoInduct (rawName n)
    for c in ii.ctors do
      unless ruleName c == toString (dRuleSuffix c) do throwError "rule naming drift"
      if clinkEnabled (ruleName c) then
        text := text ++ s!"· certify_audit_case {c} {F.getId} {hF.getId}\n"
      else
        text := text ++ "· simp_all [Ratchet.Audit.rulesEnabled, List.all_cons, Ratchet.clinkEnabled, Ratchet.clinkProfile]\n"
  let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `tactic ("(\n  " ++ text.replace "\n" "\n  " ++ "\n)")
  evalTactic stx

elab "derive_audit_certificates" : command => do
  let order := [``Ratchet.InitJudge, ``Ratchet.InitJudgeSeq, ``Ratchet.InitJudgeAll] ++
    families.filter fun n => ![``Ratchet.InitJudge, ``Ratchet.InitJudgeSeq, ``Ratchet.InitJudgeAll].contains n
  for raw in order do
    let n := auditName raw
    let some fld := dFamField.lookup raw | throwError "unknown family"
    let typeText ← liftTermElabM do
      let info ← getConstInfoInduct n
      forallTelescope info.type fun xs _ => do
        withLocalDeclD `h (mkAppN (mkConst n) xs) fun h =>
          withLocalDeclD `F (mkConst ``DFam) fun f => do
            withLocalDeclD `hF (← mkAppM ``Closed #[mkConst ``dclinks, f]) fun hf => do
              let enabled ← mkAppM ``rulesEnabled #[mkConst ``Ratchet.clinkEnabled, xs[0]!]
              let yes ← mkEq enabled (mkConst ``Bool.true)
              withLocalDeclD `he yes fun he => do
                let ty ← mkForallFVars (xs ++ #[h, f, hf, he])
                  (mkAppN (mkApp (mkConst fld) f) (xs.extract 1 xs.size))
                let ty := implicitBinders xs.size ty
                withOptions (fun o => (o.setBool `pp.explicit true).setBool `pp.fullNames true) do
                  return (← ppExpr ty).pretty
    let ii ← getConstInfoInduct raw
    let args := (List.range ii.numIndices).map fun j => s!"a{j}"
    let name := (certificateName n).str "certified"
    let text := s!"theorem _root_.{name} : {typeText} := by\n  intro used {String.intercalate " " args} h F hF he\n  revert he\n  certify_audited {n}.rec h F hF"
    let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `command text
    elabCommand stx

derive_audit_certificates
end Ratchet.Denote.Typed
