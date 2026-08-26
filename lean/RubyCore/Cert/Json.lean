import RubyCore.Cert.Validate

/-!
# C0 — the certificate's serialization

`docs/semantics/certificate-language.md` §2 constraint 5: *versioned, canonical,
diffable*. This is the wire format between `certify/` (untrusted emitters) and
`validate` (trusted checker), and §7 norm 7's interaction rule is that it is the
**only** channel: nothing in `certify/` links against the Lean tree.

## Why this is its own file (V4)

`Lean.Json.parse` does not reduce in the kernel (L135). So a module on the *checked*
path may not import it, or `validate c p = true` stops being a kernel computation and
§2 constraint 2 is violated for a reason that has nothing to do with the validator.
`Format.lean` and `Validate.lean` therefore know nothing about JSON, this file imports
them, and only `Main.lean` imports this.

## The type encoding is structured, not rendered

`Ty` goes out as `{"k":"cls","n":"Foo"}` rather than as `tyName`'s `"Foo"`. Rendering
is for *humans* and it is ambiguous in exactly the place a certificate cannot afford
— `nomTy` sends `"Integer"` to `.int` and `"TrueClass"` to `.cls "TrueClass"`, so a
name does not determine an arm — and a decoder that had to re-parse
`T.nilable(T::Array[String])` would be a second implementation of `tyName` with its
own bugs. The rendered form stays available in the *report* (`Assn.render`), which is
what §11's explainability is about and is not read back.

**A decode failure is a reject, never a crash.** `ofJson` answers `Except String`, and
`Main.lean` reports the message: a malformed certificate is exactly as uncertified as
a wrong one, which is §1's *"a bad certificate costs a body we failed to certify"*.
-/

namespace RubyCore.Cert

open RubyCore.Types
open Lean (Json)

/-! ## 1. `Ty` -/

partial def tyToJson : Ty → Json
  | .int => Json.mkObj [("k", "int")]
  | .bool => Json.mkObj [("k", "bool")]
  | .nilT => Json.mkObj [("k", "nil")]
  | .sym => Json.mkObj [("k", "sym")]
  | .float => Json.mkObj [("k", "float")]
  | .any => Json.mkObj [("k", "any")]
  | .cls n => Json.mkObj [("k", "cls"), ("n", Json.str n)]
  | .clsOf n => Json.mkObj [("k", "clsOf"), ("n", Json.str n)]
  | .nilable τ => Json.mkObj [("k", "nilable"), ("t", tyToJson τ)]
  | .arrayOf τ => Json.mkObj [("k", "arrayOf"), ("t", tyToJson τ)]

partial def tyOfJson (j : Json) : Except String Ty := do
  let k ← (← j.getObjVal? "k").getStr?
  match k with
  | "int" => pure .int
  | "bool" => pure .bool
  | "nil" => pure .nilT
  | "sym" => pure .sym
  | "float" => pure .float
  | "any" => pure .any
  | "cls" => pure (.cls (← (← j.getObjVal? "n").getStr?))
  | "clsOf" => pure (.clsOf (← (← j.getObjVal? "n").getStr?))
  | "nilable" => pure (.nilable (← tyOfJson (← j.getObjVal? "t")))
  | "arrayOf" => pure (.arrayOf (← tyOfJson (← j.getObjVal? "t")))
  | other => throw s!"unknown type kind {other}"

/-! ## 2. `ATy`, `Sig`, `ASig`, `Row` -/

partial def atyToJson : ATy → Json
  | .nom τ => Json.mkObj [("k", "nom"), ("t", tyToJson τ)]
  | .var α => Json.mkObj [("k", "var"), ("v", Json.num α)]
  | .nilOf a => Json.mkObj [("k", "nilOf"), ("a", atyToJson a)]

partial def atyOfJson (j : Json) : Except String ATy := do
  let k ← (← j.getObjVal? "k").getStr?
  match k with
  | "nom" => pure (.nom (← tyOfJson (← j.getObjVal? "t")))
  | "var" => pure (.var (← (← j.getObjVal? "v").getNat?))
  | "nilOf" => pure (.nilOf (← atyOfJson (← j.getObjVal? "a")))
  | other => throw s!"unknown atype kind {other}"

/-- A `Sig` is a `MethodDecl`. `blk` is emitted only when present, and the decoder
    refuses it: `rowGuards` refuses a block-taking row anyway (L242), so accepting one
    here would only move the rejection later. -/
def sigToJson (σ : Sig) : Json :=
  Json.mkObj [("params", Json.arr (σ.params.map tyToJson).toArray),
              ("ret", tyToJson σ.ret)]

def sigOfJson (j : Json) : Except String Sig := do
  let ps ← (← j.getObjVal? "params").getArr?
  let params ← ps.toList.mapM tyOfJson
  let ret ← tyOfJson (← j.getObjVal? "ret")
  pure { params := params, ret := ret }

def asigToJson (σ : ASig) : Json :=
  Json.mkObj [("params", Json.arr (σ.params.map atyToJson).toArray),
              ("ret", atyToJson σ.ret)]

def asigOfJson (j : Json) : Except String ASig := do
  let ps ← (← j.getObjVal? "params").getArr?
  let params ← ps.toList.mapM atyOfJson
  let ret ← atyOfJson (← j.getObjVal? "ret")
  pure { params := params, ret := ret }

/-- `Row.entries` in `Row.normalize` order on the way out — §2 constraint 5's
    *canonical* — so that two certificates diff meaningfully. The decoder does not
    re-sort: `Row.get?` is a `find?` and reads the first entry of a name, so
    re-ordering on the way in could change what a row means. -/
def rowToJson (R : Row) : Json :=
  Json.mkObj [("entries", Json.arr (R.normalize.entries.map fun e =>
                Json.mkObj [("name", Json.str e.1), ("sig", asigToJson e.2)]).toArray),
              ("tail", match R.tail with | some ρ => Json.num ρ | none => Json.null)]

def rowOfJson (j : Json) : Except String Row := do
  let es ← (← j.getObjVal? "entries").getArr?
  let entries ← es.toList.mapM fun e => do
    pure ((← (← e.getObjVal? "name").getStr?), (← asigOfJson (← e.getObjVal? "sig")))
  let tail ← match j.getObjVal? "tail" with
    | .ok Json.null => pure none
    | .ok v => pure (some (← v.getNat?))
    | .error _ => pure none
  pure { entries := entries, tail := tail }

/-! ## 3. `Assn`

Flat, as a list of atoms plus the shape `Assn.all` rebuilds — which is lossy about
*association* and deliberately so: `Assn.and` is associative and commutative in its
denotation (`denote` is a conjunction), and the four atom lists
(`declAtoms`/`reqAtoms`/`oblAtoms`/`eqAtoms`) are what every consumer reads. Emitting
the tree would make two certificates with the same atoms diff as different. -/

def assnAtoms (A : Assn) : List Json :=
  (A.declAtoms.map fun a =>
      Json.mkObj [("k", "decl"), ("ty", tyToJson a.1), ("name", Json.str a.2.1),
                  ("sig", sigToJson a.2.2)]) ++
  (A.reqAtoms.map fun r =>
      Json.mkObj [("k", "req"), ("ty", atyToJson r.1), ("name", Json.str r.2.1),
                  ("sig", asigToJson r.2.2)]) ++
  (A.oblAtoms.map fun o =>
      Json.mkObj [("k", "obl"), ("cls", Json.str o.1), ("row", rowToJson o.2)]) ++
  (A.eqAtoms.map fun e =>
      Json.mkObj [("k", "eqv"), ("var", Json.num e.1), ("aty", atyToJson e.2)])

def assnToJson (A : Assn) : Json := Json.arr (assnAtoms A).toArray

def atomOfJson (j : Json) : Except String Assn := do
  let k ← (← j.getObjVal? "k").getStr?
  match k with
  | "decl" =>
    pure (.decl (← tyOfJson (← j.getObjVal? "ty")) (← (← j.getObjVal? "name").getStr?)
      (← sigOfJson (← j.getObjVal? "sig")))
  | "req" =>
    pure (.req (← atyOfJson (← j.getObjVal? "ty")) (← (← j.getObjVal? "name").getStr?)
      (← asigOfJson (← j.getObjVal? "sig")))
  | "obl" =>
    pure (.obl (← (← j.getObjVal? "cls").getStr?) (← rowOfJson (← j.getObjVal? "row")))
  | "eqv" =>
    pure (.eqv (← (← j.getObjVal? "var").getNat?) (← atyOfJson (← j.getObjVal? "aty")))
  | other => throw s!"unknown assertion atom kind {other}"

def assnOfJson (j : Json) : Except String Assn := do
  let xs ← j.getArr?
  pure (Assn.all (← xs.toList.mapM atomOfJson))

/-! ## 4. The certificate -/

def provToJson : Provenance → Json
  | .assumed src => Json.mkObj [("k", "assumed"), ("src", Json.str src)]
  | .fromDef i => Json.mkObj [("k", "fromDef"), ("i", Json.num i)]

def provOfJson (j : Json) : Except String Provenance := do
  let k ← (← j.getObjVal? "k").getStr?
  match k with
  | "assumed" => pure (.assumed (← (← j.getObjVal? "src").getStr?))
  | "fromDef" => pure (.fromDef (← (← j.getObjVal? "i").getNat?))
  | other => throw s!"unknown provenance {other}"

def rowClaimToJson (r : RowClaim) : Json :=
  Json.mkObj [("cls", Json.str r.cls), ("name", Json.str r.name),
              ("sig", sigToJson r.sig), ("why", provToJson r.why)]

def rowClaimOfJson (j : Json) : Except String RowClaim := do
  pure { cls := ← (← j.getObjVal? "cls").getStr?,
         name := ← (← j.getObjVal? "name").getStr?,
         sig := ← sigOfJson (← j.getObjVal? "sig"),
         why := ← provOfJson (← j.getObjVal? "why") }

def bodyCertToJson (b : BodyCert) : Json :=
  Json.mkObj [("owner", Json.str b.owner), ("name", Json.str b.name),
              ("sig", sigToJson b.sig)]

def bodyCertOfJson (j : Json) : Except String BodyCert := do
  pure { owner := ← (← j.getObjVal? "owner").getStr?,
         name := ← (← j.getObjVal? "name").getStr?,
         sig := ← sigOfJson (← j.getObjVal? "sig") }

def stepToJson (s : DischargeStep) : Json :=
  Json.mkObj [("var", Json.num s.var), ("name", Json.str s.name),
              ("required", asigToJson s.required), ("provided", asigToJson s.provided)]

def stepOfJson (j : Json) : Except String DischargeStep := do
  pure { var := ← (← j.getObjVal? "var").getNat?,
         name := ← (← j.getObjVal? "name").getStr?,
         required := ← asigOfJson (← j.getObjVal? "required"),
         provided := ← asigOfJson (← j.getObjVal? "provided") }

def Cert.toJson (c : Cert) : Json :=
  Json.mkObj [
    ("version", Json.num c.version),
    ("theta", Json.arr (c.theta.map fun e =>
        Json.mkObj [("var", Json.num e.1), ("ty", tyToJson e.2)]).toArray),
    ("delta_rows", Json.arr (c.deltaRows.map rowClaimToJson).toArray),
    ("bodies", Json.arr (c.bodies.map bodyCertToJson).toArray),
    ("ledger", Json.arr (c.ledger.map stepToJson).toArray),
    ("assumes", assnToJson c.assumes)]

/-- Every field is optional and defaults to the empty certificate's, which is what
    makes the format additive: a `certify/` emitter that knows nothing about `ledger`
    emits no `ledger` key and the certificate still decodes. `version` is the one
    exception — a certificate that does not say which format it is in is not a
    certificate — and `validate`'s first conjunct is what enforces the value. -/
def Cert.ofJson (j : Json) : Except String Cert := do
  let version ← (← j.getObjVal? "version").getNat?
  let opt : {α : Type} → String → (Json → Except String α) → Except String (List α) :=
    fun key f => match j.getObjVal? key with
      | .error _ => pure []
      | .ok v => do (← v.getArr?).toList.mapM f
  let theta ← opt "theta" fun e => do
    pure ((← (← e.getObjVal? "var").getNat?), (← tyOfJson (← e.getObjVal? "ty")))
  let deltaRows ← opt "delta_rows" rowClaimOfJson
  let bodies ← opt "bodies" bodyCertOfJson
  let ledger ← opt "ledger" stepOfJson
  let assumes ← match j.getObjVal? "assumes" with
    | .error _ => pure Assn.emp
    | .ok v => assnOfJson v
  pure { version := version, theta := theta, deltaRows := deltaRows, bodies := bodies,
         ledger := ledger, assumes := assumes }

/-! ## 5. The verdict, as JSON

Read `means` for what an accept is: §2 constraint 4 makes the residue first-class, so
the strength of the conclusion is a *field* and not something a consumer has to infer
from the presence of `carries`. That is L265's `means` discipline applied to a stronger
verdict. -/

def verdictToJson (c : Cert) (p : Expr) : Json :=
  let ok := validate c p
  Json.mkObj ([
    ("status", Json.str (if ok then "accept" else "reject")),
    ("version", Json.num c.version),
    -- **The fourth ratchet, reported whether or not the certificate accepts.** It is
    -- the *gradient* — `homebrew/fragment-gap.py`'s header on why an all-or-nothing
    -- signal is useless as a ratchet — and it is deliberately outside the `if` below
    -- for that reason: no slice file types as a whole program (L265), so a per-body
    -- number gated on `status` would read 0 for the whole slice forever.
    ("bodies_claimed", Json.num c.bodies.length),
    ("bodies_certified", Json.num (bodiesCertified c p)),
    -- Per claim, whether it replayed. The gradient at its finest grain, and what an
    -- emitter reads back to iterate (`certify/implementation-notes.md` E5): the
    -- untrusted side proposes signatures and this is the adjudication.
    ("body_results", Json.arr (c.bodies.map fun b =>
        Json.mkObj [("owner", Json.str b.owner), ("name", Json.str b.name),
                    ("ret", Json.str (tyName b.sig.ret)),
                    ("ok", Json.bool (bodyOk c p b))]).toArray)] ++
    (if ok then
      [("unconditional", Json.bool c.unconditional),
       ("means", Json.str (if c.unconditional then
            "no reachable outcome of this program is type-stuck"
          else
            "no reachable outcome of this program is type-stuck, given `carries`")),
       ("carries", Json.str c.rowAssn.render),
       ("carries_rows", Json.num c.deltaRows.length),
       ("reports", Json.str c.reportAssn.render)]
     else
      -- Which conjunct failed. A reject that does not say why is the `unknown`
      -- §11 exists to retire.
      [("why", Json.str
          (if c.version != RubyCore.Cert.version then "version"
           else if !rowsGuarded (declsOf p) c.deltaRows then "row-guards"
           else if !rowsDeclared c then "row-not-in-assumes"
           else if !eqsOk c then "theta-inconsistent"
           else if !bodiesOk c p then "body-claim"
           else "nominal"))]))

end RubyCore.Cert
