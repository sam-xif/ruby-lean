import Ratchet.Lang.Ty
import Ratchet.Lang.Expr
import Ratchet.Lang.JsonUtil

/-! Untrusted certificate hints. Check.lean reconstructs source judgments and rejects
wrong literals, names, signatures, arity and subcertificates. A decoded hint alone grants
nothing: only validateD acceptance crosses the registered semantic bridge. -/

namespace Ratchet

-- `Json` is this project's vendored copy of Lean's (`Json.lean`), at the root
-- namespace, so there is nothing to open.

/-- One formal parameter of a declared signature: the name the body binds, and the type
Sorbet declared for it. Names are carried because the body is checked in an environment
built from them (`paramEnv`'s job today), and a certificate that named them differently
from the `def` would be about a different program -- which `derivShapeOk` catches. -/
abbrev SigParam := String × Ty

mutual
/-- A derivation. One constructor per rule; a field for every choice the rule leaves open
(a join type, a declared signature) and nothing for what the syntax already determines.

The split is `AGENTS.md` §The answer-typed design §3.4's: a hint is a **tag** where the rule is
syntax-directed and **load-bearing** where it is not. `intLit` carries the literal only so
the shape check can see it is about the right literal; `if'` carries its join because two
branches of different type have no inferable one. -/
inductive Deriv where
  | intLit (n : Int)
  | fltLit (bits : UInt64)
  | strLit (s : String)
  | symLit (s : String)
  | truLit
  | flsLit
  | nilLit
  /-- Opt into the effect-indexed local-flow judgment. -/
  | flow (d : Deriv)
  /-- Code is reconstructed from the source block, never supplied by the certificate. -/
  | closureLiteral
  /-- The stored source body is rechecked at the call's live local types. -/
  | closureCall (body : Deriv) (ret : Ty)
  /-- General receiver/arguments; parameter types are reconstructed from their certificates. -/
  | requiredClosureCall (recv : Deriv) (args : List Deriv) (body : Deriv) (ret : Ty)
  /-- Receiver and body hints only; source syntax and checked receiver supply all types. -/
  | eachBlock (recv body : Deriv)
  /-- Map result types come from the checked body; the hint carries no type claim. -/
  | mapBlock (recv body : Deriv)
  /-- A bare-name miss from the explicitly supported absence table. -/
  | bareName (name : String)
  | selfExpr
  /-- `Judge.var`: a local/ivar/cvar/gvar read. The type comes from the environment. -/
  | var (k : VarKind) (name : String)
  /-- `Judge.vasgn`. -/
  | vasgn (k : VarKind) (name : String) (d : Deriv)
  /-- `Judge.seq` / `JudgeSeq`. -/
  | seq (ds : List Deriv)
  /-- `Judge.if'` / `Judge.ifNoElse`. `join` is load-bearing: nothing in the syntax
      determines the type of an `if` whose branches differ. -/
  | ifD (c t : Deriv) (e : Option Deriv) (join : Ty)
  /-- `DJudge.ifTruthy`: `if x` narrowing a nilable local in both branches. -/
  | ifTruthy (x : String) (t e : Deriv) (join : Ty)
  /-- `Judge.arrayLit`. `elem` is the join over the elements, load-bearing for the same
      reason (and `.never` for `[]`). -/
  | arrayLit (elems : List Deriv) (elem : Ty)
  /-- `Judge.hashLit`. Keys and values as parallel lists rather than a list of pairs, to
      keep this inductive out of nested-product territory. -/
  | hashLit (keys vals : List Deriv) (key val : Ty)
  /-- `Judge.prim`: a send resolved by the builtin signature table. `recvTy`/`retTy`
      record which `PrimSig` row the emitter chose -- a row the checker must re-derive,
      never believe. -/
  | prim (recv : Deriv) (m : String) (args : List Deriv) (recvTy retTy : Ty)
  /-- **Where Sorbet's answer lands.** A `def` with a declared signature: the body is
      checked once, at `params -> ret`, and the method is registered at that signature.
      No `Judge` rule yet (see the header). -/
  | defDecl (name : String) (params : List SigParam) (ret : Ty) (body : Deriv)
  /-- Block signatures are untrusted definition-side hints, checked before any call. -/
  | defBlock (name : String) (params : List SigParam) (blockArgs : List Ty) (blockRet ret : Ty) (body : Deriv)
  /-- The installed checked signature supplies the callback domain. -/
  | callBlock (name : String) (body : Deriv) (ret : Ty)
  /-- Yield arguments are checked against the surrounding method's block signature. -/
  | yieldArgs (args : List Deriv)
  /-- Call the supplied method callback; its checked declaration supplies the signature. -/
  | callbackCall (recv : Deriv) (args : List Deriv)
  /-- An implicit-self call to a method declared by a `defDecl`. -/
  | callSig (name : String) (args : List Deriv) (ret : Ty)
  /-- Explicit initializer super; parent code and annotations come from retained sources. -/
  | superInit (args : List Deriv)
  /-- An explicit-receiver call to a method declared by a `defDecl` on the receiver's
      class. -/
  | callMethodSig (recv : Deriv) (name : String) (args : List Deriv) (ret : Ty)
  /-- `Judge.classStmt`. -/
  | classDecl (name : String) (sup : Option String) (body : Deriv)
  /-- A fresh module with a checked body and separate locals. -/
  | moduleDecl (name : String) (body : Deriv)
  /-- `Judge.newInst`. `ty` is the instance type the emitter claims, ivar spine included. -/
  | newInst (cls : String) (args : List Deriv) (ty : Ty)
  /-- Implicit construction from class-valued self; owner and fields are rechecked. -/
  | newImplicit (cls : String) (args : List Deriv) (ty : Ty)
  /-- An own singleton call, separate from the ordinary instance table. -/
  | callSingleton (recv : Deriv) (name : String) (args : List Deriv) (ret : Ty)
  /-- `Judge.ivarRead`. -/
  | ivarRead (name : String) (ty : Ty)
  /-- `Judge.ivarAsgn`. -/
  | ivarAsgn (name : String) (d : Deriv)
  /-- `Judge.constCls` / `Judge.constBuiltin`: a constant naming a class object. -/
  | constCls (name : String)
deriving Inhabited
end

/-! ## Decoding

The wire format is `JsonUtil.lean`'s: `{"rule": ..., <named fields>}`, hand-written on
both sides so the emitter (`scripts/emit_deriv.rb`, Ruby) never has to reverse-engineer
a Lean derive convention. A field that is a type is `Ty`'s `{"tag": ...}` encoding. -/

private def varKindOfJson? (j : Json) : Except String VarKind := do
  match ← j.getStr? with
  | "lvar" => return .lvar
  | "ivar" => return .ivar
  | "cvar" => return .cvar
  | "gvar" => return .gvar
  | other => throw s!"Deriv: unknown var kind '{other}'"

partial def Deriv.ofJson? (j : Json) : Except String Deriv := do
  let rule ← j.getObjValAs? String "rule"
  let ty (k : String) : Except String Ty := do Ty.ofJson? (← j.getObjVal? k)
  let kid (k : String) : Except String Deriv := do Deriv.ofJson? (← j.getObjVal? k)
  let kids (k : String) : Except String (List Deriv) := jList j k Deriv.ofJson?
  let name (k : String) : Except String String := j.getObjValAs? String k
  match rule with
  | "intLit" => return .intLit (← j.getObjValAs? Int "n")
  | "fltLit" => return .fltLit (UInt64.ofNat (← j.getObjValAs? Nat "bits"))
  | "strLit" => return .strLit (← name "s")
  | "symLit" => return .symLit (← name "s")
  | "truLit" => return .truLit
  | "flsLit" => return .flsLit
  | "nilLit" => return .nilLit
  | "flow" => return .flow (← kid "body")
  | "closureLiteral" => return .closureLiteral
  | "closureCall" => return .closureCall (← kid "body") (← ty "ret")
  | "requiredClosureCall" =>
    return .requiredClosureCall (← kid "recv") (← kids "args") (← kid "body") (← ty "ret")
  | "eachBlock" => return .eachBlock (← kid "recv") (← kid "body")
  | "mapBlock" => return .mapBlock (← kid "recv") (← kid "body")
  | "bareName" => return .bareName (← name "name")
  | "selfExpr" => return .selfExpr
  | "var" => return .var (← varKindOfJson? (← j.getObjVal? "kind")) (← name "name")
  | "vasgn" =>
    return .vasgn (← varKindOfJson? (← j.getObjVal? "kind")) (← name "name") (← kid "value")
  | "seq" => return .seq (← kids "stmts")
  | "if" =>
    return .ifD (← kid "cond") (← kid "then") (← jOpt j "else" Deriv.ofJson?) (← ty "join")
  | "ifTruthy" => return .ifTruthy (← name "name") (← kid "then") (← kid "else") (← ty "join")
  | "arrayLit" => return .arrayLit (← kids "elems") (← ty "elem")
  | "hashLit" => return .hashLit (← kids "keys") (← kids "vals") (← ty "key") (← ty "val")
  | "prim" =>
    return .prim (← kid "recv") (← name "method") (← kids "args") (← ty "recvTy") (← ty "retTy")
  | "defDecl" =>
    let ps ← jList j "params" (fun p => do
      return ((← p.getObjValAs? String "name"), ← Ty.ofJson? (← p.getObjVal? "ty")))
    return .defDecl (← name "name") ps (← ty "ret") (← kid "body")
  | "defBlock" =>
    let ps ← jList j "params" (fun p => do
      return ((← p.getObjValAs? String "name"), ← Ty.ofJson? (← p.getObjVal? "ty")))
    return .defBlock (← name "name") ps (← jList j "blockArgs" Ty.ofJson?)
      (← ty "blockRet") (← ty "ret") (← kid "body")
  | "yield" => return .yieldArgs (← kids "args")
  | "callbackCall" => return .callbackCall (← kid "recv") (← kids "args")
  | "callSig" => return .callSig (← name "name") (← kids "args") (← ty "ret")
  | "callBlock" => return .callBlock (← name "name") (← kid "body") (← ty "ret")
  | "superInit" => return .superInit (← kids "args")
  | "callMethodSig" =>
    return .callMethodSig (← kid "recv") (← name "name") (← kids "args") (← ty "ret")
  | "classDecl" =>
    return .classDecl (← name "name") (← jOpt j "super" (·.getStr?)) (← kid "body")
  | "moduleDecl" => return .moduleDecl (← name "name") (← kid "body")
  | "newInst" => return .newInst (← name "cls") (← kids "args") (← ty "ty")
  | "newImplicit" => return .newImplicit (← name "cls") (← kids "args") (← ty "ty")
  | "callSingleton" => return .callSingleton (← kid "recv") (← name "name") (← kids "args") (← ty "ret")
  | "ivarRead" => return .ivarRead (← name "name") (← ty "ty")
  | "ivarAsgn" => return .ivarAsgn (← name "name") (← kid "value")
  | "constCls" => return .constCls (← name "name")
  | other => throw s!"Deriv.ofJson?: unknown rule '{other}'"

/-! ## The checker lives in `Ratchet/Check/Check.lean`

This file is layer 1 only: the certificate language and its decoder. The checker that used
to sit here -- `derivShapeOk`, a shape check that verified a certificate was *about* a
program and checked no types at all -- is **deleted**, replaced by `Ratchet/Check/Check.lean`'s
`check`, which does both: it matches the program, derives the type itself, compares every
`Ty` the certificate claims, and returns the `DJudge` derivation. The shape check's one
property (a certificate for the wrong program is rejected) is a consequence of `check`
dispatching on the expression; `Ratchet/Controls/DerivControls.lean` keeps the controls that pin it.

`validateD` keeps its name and its consumers (`Ratchet/Check/Rung.lean`, `MainTyped.lean`) and
lives in `Check.lean` next to what it calls.
-/

end Ratchet
