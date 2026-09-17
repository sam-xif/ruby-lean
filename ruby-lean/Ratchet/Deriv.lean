import Ratchet.Ty
import Ratchet.Expr
import Ratchet.JsonUtil

/-!
# `Deriv` — the certificate language, and the stub that checks one

`../AGENTS.md` §The answer-typed design §3.4: layer 1 of the seven, the thing an
**untrusted** emitter writes and the kernel reads. This file is that layer plus a
deliberately incomplete layer 2 (`validateD`), which is where this commit stops.

## Why a certificate at all, when `Ratchet/Validate.lean` synthesizes

`validate` infers, and inference is why the ladder is capped: `Judge.callDef` types a
method body **once per call-site argument shape**, because Ruby writes no parameter
types and there is therefore nothing to check a call against. Sorbet's `sig` is exactly
the missing input, and it cannot be handed to an inference algorithm without trusting it
-- so it is handed in as *certificate data* instead, and re-checked. That is
`sorbet-cert/README.md` §3's argument, and the reason a declared type cannot produce a
wrong accept: it arrives as a field of `Deriv.defDecl`, and the checker re-checks the
body at exactly that type. A wrong signature produces a body that fails to certify.

## What is different from `Judge`

Two constructors here have **no `Judge` rule yet**, and they are the point of the
reshaping rather than an oversight:

* `defDecl` -- check a method body **once**, at its declared signature, and register it.
  `Judge.defStmt` types a `def` as `.sym` and says nothing about the body.
* `callSig` / `callMethodSig` -- a call checked against a *declared* signature, rather
  than `Judge.callDef`'s re-check of the body at the call site's argument types.

Both are owed a `Judge` rule and a soundness lemma (`check_sound`, layer 3). Neither
exists here; see §"Not built" below. The remaining constructors mirror an existing
`Judge` rule one-for-one and are named after it.

## Not built (and not pretended)

* **`check`** -- the real layer 2: `Ctx -> Env -> Ty -> Expr -> Deriv -> Option (Ty x Env x Ty)`.
  `validateD` below is a **shape check only**: it verifies the certificate is a
  derivation *about this program*, and nothing about types. It is not sound and does not
  claim to be; it is the half of `check` that has to be right before the typing half is
  worth writing, and it is enough to run the pipeline end to end.
* **`check_sound`** -- layer 3, `check ... = some ... -> Judge ...`.
* The `Judge` rules `defDecl`/`callSig` need.
-/

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
  /-- An implicit-self call to a method declared by a `defDecl`. -/
  | callSig (name : String) (args : List Deriv) (ret : Ty)
  /-- An explicit-receiver call to a method declared by a `defDecl` on the receiver's
      class. -/
  | callMethodSig (recv : Deriv) (name : String) (args : List Deriv) (ret : Ty)
  /-- `Judge.classStmt`. -/
  | classDecl (name : String) (sup : Option String) (body : Deriv)
  /-- `Judge.newInst`. `ty` is the instance type the emitter claims, ivar spine included. -/
  | newInst (cls : String) (args : List Deriv) (ty : Ty)
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
  | "bareName" => return .bareName (← name "name")
  | "selfExpr" => return .selfExpr
  | "var" => return .var (← varKindOfJson? (← j.getObjVal? "kind")) (← name "name")
  | "vasgn" =>
    return .vasgn (← varKindOfJson? (← j.getObjVal? "kind")) (← name "name") (← kid "value")
  | "seq" => return .seq (← kids "stmts")
  | "if" =>
    return .ifD (← kid "cond") (← kid "then") (← jOpt j "else" Deriv.ofJson?) (← ty "join")
  | "arrayLit" => return .arrayLit (← kids "elems") (← ty "elem")
  | "hashLit" => return .hashLit (← kids "keys") (← kids "vals") (← ty "key") (← ty "val")
  | "prim" =>
    return .prim (← kid "recv") (← name "method") (← kids "args") (← ty "recvTy") (← ty "retTy")
  | "defDecl" =>
    let ps ← jList j "params" (fun p => do
      return ((← p.getObjValAs? String "name"), ← Ty.ofJson? (← p.getObjVal? "ty")))
    return .defDecl (← name "name") ps (← ty "ret") (← kid "body")
  | "callSig" => return .callSig (← name "name") (← kids "args") (← ty "ret")
  | "callMethodSig" =>
    return .callMethodSig (← kid "recv") (← name "name") (← kids "args") (← ty "ret")
  | "classDecl" =>
    return .classDecl (← name "name") (← jOpt j "super" (·.getStr?)) (← kid "body")
  | "newInst" => return .newInst (← name "cls") (← kids "args") (← ty "ty")
  | "ivarRead" => return .ivarRead (← name "name") (← ty "ty")
  | "ivarAsgn" => return .ivarAsgn (← name "name") (← kid "value")
  | "constCls" => return .constCls (← name "name")
  | other => throw s!"Deriv.ofJson?: unknown rule '{other}'"

/-! ## The checker lives in `Ratchet/Check.lean`

This file is layer 1 only: the certificate language and its decoder. The checker that used
to sit here -- `derivShapeOk`, a shape check that verified a certificate was *about* a
program and checked no types at all -- is **deleted**, replaced by `Ratchet/Check.lean`'s
`check`, which does both: it matches the program, derives the type itself, compares every
`Ty` the certificate claims, and returns the `DJudge` derivation. The shape check's one
property (a certificate for the wrong program is rejected) is a consequence of `check`
dispatching on the expression; `Ratchet/DerivControls.lean` keeps the controls that pin it.

`validateD` keeps its name and its consumers (`Ratchet/Rung.lean`, `MainTyped.lean`) and
lives in `Check.lean` next to what it calls.
-/

end Ratchet
