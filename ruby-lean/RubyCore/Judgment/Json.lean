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
  | .regexpLit => Json.mkObj [("k", "regexpLit")]
  | .defForget => Json.mkObj [("k", "defForget")]
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
  | .hash ds => Json.mkObj [("k", "hash"), ("pairs", derivPairsToJson ds)]
  | .casgn rhs => Json.mkObj [("k", "casgn"), ("rhs", derivToJson rhs)]
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
  | .module' b => Json.mkObj [("k", "module"), ("body", derivToJson b)]
  | .classM b => Json.mkObj [("k", "classM"), ("body", derivToJson b)]
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

/-- Pairs serialize as a flat array of `{"key": …, "val": …}` objects. -/
partial def derivPairsToJson : DerivPairs → Json
  | .nil => Json.arr #[]
  | .cons k v rest =>
    let entry := Json.mkObj [("key", derivToJson k), ("val", derivToJson v)]
    match derivPairsToJson rest with
    | .arr a => Json.arr (#[entry] ++ a)
    | _ => Json.arr #[entry]

end

mutual

partial def derivOfJson (j : Json) : Except String Deriv := do
  let k ← (← j.getObjVal? "k").getStr?
  match k with
  | "semantic" => pure (.semantic (← (← j.getObjVal? "i").getNat?))
  | "int" => pure .int
  | "flt" => pure .flt
  | "regexpLit" => pure .regexpLit
  | "defForget" => pure .defForget
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
  | "hash" => pure (.hash (← derivPairsOfJson (← j.getObjVal? "pairs")))
  | "casgn" => pure (.casgn (← derivOfJson (← j.getObjVal? "rhs")))
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
  | "module" => pure (.module' (← derivOfJson (← j.getObjVal? "body")))
  | "classM" => pure (.classM (← derivOfJson (← j.getObjVal? "body")))
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


partial def derivPairsOfJson (j : Json) : Except String DerivPairs := do
  match ← j.getArr? with
  | #[] => pure .nil
  | arr =>
    match arr.toList with
    | [] => pure .nil
    | e :: rest => do
      let k ← derivOfJson (← e.getObjVal? "key")
      let v ← derivOfJson (← e.getObjVal? "val")
      pure (.cons k v (← derivPairsOfJson (Json.arr rest.toArray)))

end

/-- **A semantic claim on the wire (J48)** — the J31 claim list, previously
    Lean-side only. The claimed expression rides as a harness-export AST node
    (export.rb's format), decoded by the same `Decode.expr` the program itself
    comes in through — so the emitter serializes `e` exactly as it serializes
    the program. Decode-only: `SemAxiomsOk` is a *proof* residue discharged
    Lean-side against the decoded list (an accept with claims is conditional,
    reported as `carries_sem_assumes`), so nothing round-trips out. -/
def semClaimOfJson (j : Json) : Except String SemClaim := do
  let e ← RubyCore.Decode.expr (← j.getObjVal? "e")
  let τ ← match j.getObjVal? "ty" with
    | .ok tj => tyOfJson tj
    | .error _ => pure .any
  let rows ← match j.getObjVal? "rows" with
    | .ok rj => do
      (← rj.getArr?).toList.mapM fun x => do
        let r ← rowClaimOfJson x
        pure (r.cls, r.name, r.sig)
    | .error _ => pure []
  let reqCls ← match j.getObjVal? "req_cls" with
    | .ok .null => pure none
    | .ok cj => some <$> cj.getStr?
    | .error _ => pure none
  let reqMod ← match j.getObjVal? "req_mod" with
    | .ok bj => bj.getBool?
    | .error _ => pure false
  let fresh ← match j.getObjVal? "fresh_names" with
    | .ok fj => do (← fj.getArr?).toList.mapM (·.getStr?)
    | .error _ => pure []
  pure { e := e, τ := τ, rows := rows, reqCls := reqCls, reqMod := reqMod,
         freshNames := fresh }

/-- The J-certificate document: `{"delta_rows": […], "delta_consts": […],
    "delta_scoped_consts": […], "delta_modules": […], "sem_assumes": […],
    "deriv": {…}}` (the constant sections since J38b, the module and claim
    sections since J48; all optional and empty by default). `sem_assumes` is
    decode-only (no Lean-side `Expr` encoder), so `toJson` requires it empty
    at the use sites (round-trip tests). -/
def JCert.toJson (c : JCert) : Json :=
  Json.mkObj [("delta_rows", Json.arr (c.deltaRows.toArray.map rowClaimToJson)),
    ("delta_consts", Json.arr (c.deltaConsts.toArray.map fun e =>
      Json.mkObj [("name", Json.str e.1), ("type", tyToJson e.2)])),
    ("delta_scoped_consts", Json.arr (c.deltaScopedConsts.toArray.map fun e =>
      Json.mkObj [("cls", Json.str e.1.1), ("name", Json.str e.1.2),
                  ("type", tyToJson e.2)])),
    ("delta_modules", Json.arr (c.deltaModules.toArray.map fun e =>
      Json.mkObj [("owner", Json.str e.1), ("name", Json.str e.2)])),
    ("delta_classes", Json.arr (c.deltaClasses.toArray.map fun e =>
      Json.mkObj [("owner", Json.str e.1), ("name", Json.str e.2)])),
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
  let ms ← match j.getObjVal? "delta_modules" with
    | .ok mj => do
      (← mj.getArr?).toList.mapM fun e => do
        pure ((← e.getObjValAs? String "owner"), (← e.getObjValAs? String "name"))
    | .error _ => pure []
  let kls ← match j.getObjVal? "delta_classes" with
    | .ok mj => do
      (← mj.getArr?).toList.mapM fun e => do
        pure ((← e.getObjValAs? String "owner"), (← e.getObjValAs? String "name"))
    | .error _ => pure []
  let sems ← match j.getObjVal? "sem_assumes" with
    | .ok sj => do (← sj.getArr?).toList.mapM semClaimOfJson
    | .error _ => pure []
  pure { deltaRows := rows, deltaConsts := consts, deltaScopedConsts := scs,
         deltaModules := ms, deltaClasses := kls, semAssumes := sems,
         deriv := (← derivOfJson (← j.getObjVal? "deriv")) }

end RubyCore.Judgment
