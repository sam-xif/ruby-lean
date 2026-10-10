import Books.TypeSoundness.Checker.Audit.Derive

open Lean Meta Elab Command Tactic
namespace Checker.Audit

def rawName (n : Name) : Name := n.replacePrefix `Checker.Audit `Checker

elab "erase_audit_case" ctor:ident : tactic => withMainContext do
  let raw ← getConstInfoCtor ctor.getId
  let traced ← getConstInfoCtor (auditName ctor.getId)
  let group := (← getConstInfoInduct raw.induct).all
  let domains : Array Lean.Expr ← forallTelescope raw.type fun xs _ => xs.mapM fun x => return (← inferType x)
  let count := traced.type.getForallArity
  let recursive := domains.filter fun d => d.getUsedConstants.any group.contains
  let locals := (← getLCtx).getFVarIds.map mkFVar
  unless locals.size >= count + recursive.size do throwError "missing audit case binders"
  let fields := locals.extract (locals.size - count - recursive.size) locals.size
  let mut args := #[]
  let mut cursor := 0
  let mut ih := count
  for dom in domains do
    if dom.getUsedConstants.any families.contains then
      let premise := fields[cursor + 1]!
      cursor := cursor + 2
      if dom.getUsedConstants.any group.contains then
        args := args.push fields[ih]!
        ih := ih + 1
      else
        let d ← inferType premise
        let fn := mkConst ((d.getAppFn.constName!).str "toRaw")
        args := args.push (mkAppN fn (d.getAppArgs.push premise))
    else
      args := args.push fields[cursor]!
      cursor := cursor + 1
  let value := mkAppN (mkConst ctor.getId) args
  let goal ← getMainGoal
  unless ← isDefEq (← inferType value) (← goal.getType) do
    throwError "audit erasure constructor mismatch"
  goal.assign value
  replaceMainGoal []

elab "erase_audited" rec:ident h:ident : tactic => do
  let .recInfo ri ← getConstInfo rec.getId | throwError "expected a mutual recursor"
  let mut text := s!"refine {rec.getId} "
  for (n, i) in ri.all.zipIdx do
    let ii ← getConstInfoInduct (rawName n)
    let args := (List.range ii.numIndices).map fun j => s!"a{j}"
    text := text ++ s!"(motive_{i+1} := " ++ "fun {used} " ++ s!"{String.intercalate " " args} _ => {rawName n} {String.intercalate " " args}) "
  text := text ++ String.intercalate " " (List.replicate ri.numMinors "?_") ++ s!" {h.getId}\nall_goals intros\n"
  for n in ri.all do
    let ii ← getConstInfoInduct (rawName n)
    for c in ii.ctors do
      text := text ++ s!"· erase_audit_case {c}\n"
  let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `tactic ("(\n  " ++ text.replace "\n" "\n  " ++ "\n)")
  evalTactic stx

def implicitBinders : Nat → Lean.Expr → Lean.Expr
  | 0, e => e
  | n+1, .forallE nm dom body _ => .forallE nm dom (implicitBinders n body) .implicit
  | _, e => e

elab "derive_audit_erasure" : command => do
  let order := [``Checker.InitJudge, ``Checker.InitJudgeSeq, ``Checker.InitJudgeAll] ++
    families.filter fun n => ![``Checker.InitJudge, ``Checker.InitJudgeSeq, ``Checker.InitJudgeAll].contains n
  for raw in order do
    let n := auditName raw
    let typeText ← liftTermElabM do
      let info ← getConstInfoInduct n
      forallTelescope info.type fun xs _ => do
        let dom := mkAppN (mkConst n) xs
        withLocalDeclD `h dom fun h => do
          let ty ← mkForallFVars (xs.push h) (mkAppN (mkConst raw) (xs.extract 1 xs.size))
          let ty := implicitBinders xs.size ty
          withOptions (fun o => (o.setBool `pp.explicit true).setBool `pp.fullNames true) do
            return (← ppExpr ty).pretty
    let ii ← getConstInfoInduct raw
    let args := (List.range ii.numIndices).map fun j => s!"a{j}"
    let text := s!"theorem _root_.{n}.toRaw : {typeText} := by\n  intro used {String.intercalate " " args} h\n  erase_audited {n}.rec h"
    let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `command text
    elabCommand stx

derive_audit_erasure

theorem DJudge.plainArg {used : List String} {κ κ' : Ctx} {I I' : Ty}
    {Γ Γ' : Env} {e : Checker.Expr} {τ : Ty}
    (h : DJudge (used := used) Γ e τ Γ' κ I κ' I') : plainArgB e = true :=
  (DJudge.toRaw h).plainArg

def DJudge.rules {used : List String} {κ κ' : Ctx} {I I' : Ty}
    {Γ Γ' : Env} {e : Checker.Expr} {τ : Ty}
    (_h : DJudge (used := used) Γ e τ Γ' κ I κ' I') : List String := used

/-- Existential trace metadata for an optional uniform ordinary-body witness. -/
structure TraceLift (P : List String → Prop) where
  {used : List String}
  down : P used
def TraceLift.up {P : List String → Prop} {used : List String} (down : P used) : TraceLift P := ⟨down⟩
end Checker.Audit
