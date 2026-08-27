import RubyCore.Judgment.Check
import RubyCore.Cert.Json

/-!
# The `Deriv` wire format (J25) — a J-certificate is a JSON document

`judgment-layer.md` §4(3): the derivation is serialized data an untrusted emitter
produces in any language; this codec is the boundary. Node kinds mirror the
constructor names; the chosen data (`Ty`s, `Env`s) reuse the C-ladder's codecs
(`Cert/Json.lean`), so a J-certificate's rows section is byte-compatible with the
C-certificates' `delta_rows`. Decode errors reject the certificate — a malformed
one is exactly as uncertified as a wrong one.
-/

namespace RubyCore.Judgment

open RubyCore.Types
open RubyCore.Cert (tyToJson tyOfJson rowClaimToJson rowClaimOfJson)
open Lean (Json)

def envToJson (Γ : Env) : Json :=
  Json.arr (Γ.toArray.map fun (x, τ) =>
    Json.mkObj [("x", Json.str x), ("t", tyToJson τ)])

def envOfJson (j : Json) : Except String Env := do
  let arr ← j.getArr?
  arr.toList.mapM fun e => do
    pure ((← (← e.getObjVal? "x").getStr?), (← tyOfJson (← e.getObjVal? "t")))

mutual

partial def derivToJson : Deriv → Json
  -- J31: the semantic-axiom leaf. The node itself is field-free (the claimed
  -- expression is the ambient one at the node's position); the *claim list*
  -- (`JCert.semAssumes`) is Lean-side data in v1 — carrying it on the wire needs
  -- an `Expr` encoder mirroring the harness export format, a recorded bill.
  | .semantic i => Json.mkObj [("k", "semantic"), ("i", Json.num i)]
  | .int => Json.mkObj [("k", "int")]
  | .flt => Json.mkObj [("k", "flt")]
  | .str => Json.mkObj [("k", "str")]
  | .sym => Json.mkObj [("k", "sym")]
  | .tru => Json.mkObj [("k", "tru")]
  | .fls => Json.mkObj [("k", "fls")]
  | .nil => Json.mkObj [("k", "nil")]
  | .self => Json.mkObj [("k", "self")]
  | .varLvar => Json.mkObj [("k", "varLvar")]
  | .vasgnLvar rhs => Json.mkObj [("k", "vasgnLvar"), ("rhs", derivToJson rhs)]
  | .seq ds => Json.mkObj [("k", "seq"), ("ds", derivSeqToJson ds)]
  | .ifElse c t e τj Γc =>
    Json.mkObj [("k", "ifElse"), ("c", derivToJson c), ("t", derivToJson t),
      ("e", derivToJson e), ("join", tyToJson τj), ("env", envToJson Γc)]
  | .ifNone c t τj Γc =>
    Json.mkObj [("k", "ifNone"), ("c", derivToJson c), ("t", derivToJson t),
      ("join", tyToJson τj), ("env", envToJson Γc)]
  | .while' Γl c b =>
    Json.mkObj [("k", "while"), ("head", envToJson Γl), ("c", derivToJson c),
      ("b", derivToJson b)]
  | .ifNarrowElse t e τj Γc =>
    Json.mkObj [("k", "ifNarrowElse"), ("t", derivToJson t), ("e", derivToJson e),
      ("join", tyToJson τj), ("env", envToJson Γc)]
  | .ifNarrowNone t τj Γc =>
    Json.mkObj [("k", "ifNarrowNone"), ("t", derivToJson t),
      ("join", tyToJson τj), ("env", envToJson Γc)]
  | .vcall => Json.mkObj [("k", "vcall")]
  | .const => Json.mkObj [("k", "const")]
  | .cpathAbs => Json.mkObj [("k", "cpathAbs")]
  | .cpathScoped base => Json.mkObj [("k", "cpathScoped"), ("base", derivToJson base)]
  | .retSome rhs => Json.mkObj [("k", "retSome"), ("rhs", derivToJson rhs)]
  | .retNil => Json.mkObj [("k", "retNil")]
  | .varIvar => Json.mkObj [("k", "varIvar")]
  | .varGvar => Json.mkObj [("k", "varGvar")]
  | .vasgnIvar rhs => Json.mkObj [("k", "vasgnIvar"), ("rhs", derivToJson rhs)]
  | .vasgnGvar rhs => Json.mkObj [("k", "vasgnGvar"), ("rhs", derivToJson rhs)]
  | .array ds => Json.mkObj [("k", "array"), ("elems", derivArgsToJson ds)]
  | .send r a =>
    Json.mkObj [("k", "send"), ("recv", derivRecvToJson r), ("args", derivArgsToJson a)]
  | .defDecl τs σ bs b =>
    Json.mkObj ([("k", Json.str "defDecl"),
      ("params", Json.arr (τs.toArray.map tyToJson)), ("ret", tyToJson σ),
      ("body", derivToJson b)] ++
      (match bs with
       | some s => [("blk", Json.mkObj
           [("params", Json.arr (s.params.toArray.map tyToJson)),
            ("ret", tyToJson s.ret)])]
       | none => []))
  | .defPromote b => Json.mkObj [("k", "defPromote"), ("body", derivToJson b)]
  | .classTop b => Json.mkObj [("k", "classTop"), ("body", derivToJson b)]
  | .sub d σ Γ'' =>
    Json.mkObj [("k", "sub"), ("d", derivToJson d), ("ty", tyToJson σ),
      ("env", envToJson Γ'')]

partial def derivRecvToJson : DerivRecv → Json
  | .self => Json.mkObj [("k", "self")]
  | .expl d => Json.mkObj [("k", "expl"), ("d", derivToJson d)]

partial def derivSeqToJson : DerivSeq → Json
  | .nil => Json.arr #[]
  | .single d => Json.arr #[derivToJson d]
  | .cons d rest =>
    match derivSeqToJson rest with
    | .arr a => Json.arr (#[derivToJson d] ++ a)
    | _ => Json.arr #[derivToJson d]

partial def derivArgsToJson : DerivArgs → Json
  | .nil => Json.arr #[]
  | .cons d rest =>
    match derivArgsToJson rest with
    | .arr a => Json.arr (#[derivToJson d] ++ a)
    | _ => Json.arr #[derivToJson d]

end

mutual

partial def derivOfJson (j : Json) : Except String Deriv := do
  let k ← (← j.getObjVal? "k").getStr?
  match k with
  | "semantic" => pure (.semantic (← (← j.getObjVal? "i").getNat?))
  | "int" => pure .int
  | "flt" => pure .flt
  | "str" => pure .str
  | "sym" => pure .sym
  | "tru" => pure .tru
  | "fls" => pure .fls
  | "nil" => pure .nil
  | "self" => pure .self
  | "varLvar" => pure .varLvar
  | "vasgnLvar" => pure (.vasgnLvar (← derivOfJson (← j.getObjVal? "rhs")))
  | "seq" => pure (.seq (← derivSeqOfJson (← j.getObjVal? "ds")))
  | "ifElse" =>
    pure (.ifElse (← derivOfJson (← j.getObjVal? "c"))
      (← derivOfJson (← j.getObjVal? "t")) (← derivOfJson (← j.getObjVal? "e"))
      (← tyOfJson (← j.getObjVal? "join")) (← envOfJson (← j.getObjVal? "env")))
  | "ifNone" =>
    pure (.ifNone (← derivOfJson (← j.getObjVal? "c"))
      (← derivOfJson (← j.getObjVal? "t"))
      (← tyOfJson (← j.getObjVal? "join")) (← envOfJson (← j.getObjVal? "env")))
  | "while" =>
    pure (.while' (← envOfJson (← j.getObjVal? "head"))
      (← derivOfJson (← j.getObjVal? "c")) (← derivOfJson (← j.getObjVal? "b")))
  | "vcall" => pure .vcall
  | "ifNarrowElse" =>
    pure (.ifNarrowElse (← derivOfJson (← j.getObjVal? "t"))
      (← derivOfJson (← j.getObjVal? "e"))
      (← tyOfJson (← j.getObjVal? "join")) (← envOfJson (← j.getObjVal? "env")))
  | "ifNarrowNone" =>
    pure (.ifNarrowNone (← derivOfJson (← j.getObjVal? "t"))
      (← tyOfJson (← j.getObjVal? "join")) (← envOfJson (← j.getObjVal? "env")))
  | "const" => pure .const
  | "cpathAbs" => pure .cpathAbs
  | "cpathScoped" => pure (.cpathScoped (← derivOfJson (← j.getObjVal? "base")))
  | "retSome" => pure (.retSome (← derivOfJson (← j.getObjVal? "rhs")))
  | "retNil" => pure .retNil
  | "varIvar" => pure .varIvar
  | "varGvar" => pure .varGvar
  | "vasgnIvar" => pure (.vasgnIvar (← derivOfJson (← j.getObjVal? "rhs")))
  | "vasgnGvar" => pure (.vasgnGvar (← derivOfJson (← j.getObjVal? "rhs")))
  | "array" => pure (.array (← derivArgsOfJson (← j.getObjVal? "elems")))
  | "send" =>
    pure (.send (← derivRecvOfJson (← j.getObjVal? "recv"))
      (← derivArgsOfJson (← j.getObjVal? "args")))
  | "defDecl" => do
    let ps ← (← (← j.getObjVal? "params").getArr?).toList.mapM tyOfJson
    let ret ← tyOfJson (← j.getObjVal? "ret")
    let bs ← match j.getObjVal? "blk" with
      | .ok bj => do
        let bps ← (← (← bj.getObjVal? "params").getArr?).toList.mapM tyOfJson
        let bret ← tyOfJson (← bj.getObjVal? "ret")
        pure (some { params := bps, ret := bret : BlockSig })
      | .error _ => pure none
    pure (.defDecl ps ret bs (← derivOfJson (← j.getObjVal? "body")))
  | "defPromote" => pure (.defPromote (← derivOfJson (← j.getObjVal? "body")))
  | "classTop" => pure (.classTop (← derivOfJson (← j.getObjVal? "body")))
  | "sub" =>
    pure (.sub (← derivOfJson (← j.getObjVal? "d"))
      (← tyOfJson (← j.getObjVal? "ty")) (← envOfJson (← j.getObjVal? "env")))
  | other => throw s!"unknown derivation node {other}"

partial def derivRecvOfJson (j : Json) : Except String DerivRecv := do
  let k ← (← j.getObjVal? "k").getStr?
  match k with
  | "self" => pure .self
  | "expl" => pure (.expl (← derivOfJson (← j.getObjVal? "d")))
  | other => throw s!"unknown receiver node {other}"

partial def derivSeqOfJson (j : Json) : Except String DerivSeq := do
  let arr ← j.getArr?
  match arr.toList with
  | [] => pure .nil
  | [d] => pure (.single (← derivOfJson d))
  | d :: rest => do
    let hd ← derivOfJson d
    let tl ← derivSeqOfJson (Json.arr rest.toArray)
    pure (.cons hd tl)

partial def derivArgsOfJson (j : Json) : Except String DerivArgs := do
  let arr ← j.getArr?
  match arr.toList with
  | [] => pure .nil
  | d :: rest => do
    let hd ← derivOfJson d
    let tl ← derivArgsOfJson (Json.arr rest.toArray)
    pure (.cons hd tl)

end

/-- The J-certificate document: `{"delta_rows": […], "delta_consts": […],
    "delta_scoped_consts": […], "deriv": {…}}` (the constant sections since
    J38b; both optional and empty by default). -/
def JCert.toJson (c : JCert) : Json :=
  Json.mkObj [("delta_rows", Json.arr (c.deltaRows.toArray.map rowClaimToJson)),
    ("delta_consts", Json.arr (c.deltaConsts.toArray.map fun e =>
      Json.mkObj [("name", Json.str e.1), ("type", tyToJson e.2)])),
    ("delta_scoped_consts", Json.arr (c.deltaScopedConsts.toArray.map fun e =>
      Json.mkObj [("cls", Json.str e.1.1), ("name", Json.str e.1.2),
                  ("type", tyToJson e.2)])),
    ("deriv", derivToJson c.deriv)]

def JCert.ofJson (j : Json) : Except String JCert := do
  let rows ← match j.getObjVal? "delta_rows" with
    | .ok rj => do (← rj.getArr?).toList.mapM rowClaimOfJson
    | .error _ => pure []
  let consts ← match j.getObjVal? "delta_consts" with
    | .ok cj => do
      (← cj.getArr?).toList.mapM fun e => do
        pure ((← e.getObjValAs? String "name"), (← tyOfJson (← e.getObjVal? "type")))
    | .error _ => pure []
  let scs ← match j.getObjVal? "delta_scoped_consts" with
    | .ok cj => do
      (← cj.getArr?).toList.mapM fun e => do
        pure (((← e.getObjValAs? String "cls"), (← e.getObjValAs? String "name")),
          (← tyOfJson (← e.getObjVal? "type")))
    | .error _ => pure []
  pure { deltaRows := rows, deltaConsts := consts, deltaScopedConsts := scs,
         deriv := (← derivOfJson (← j.getObjVal? "deriv")) }

end RubyCore.Judgment
