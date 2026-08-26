import RubyCore.Cert.Ledger

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

/-! ### Node claims (V10), and the resolution step V15 forces

`Cert.claims` is keyed on the **subterm** a claim is about, because a claim keyed on a
position cannot be stated at a machine state (`Cert/Format.lean` V15). Emitters,
though, naturally write *positions* — and a position is also what diffs and reads
well. So the wire format keeps the `Path` and this file resolves it:

```
JSON  {"path": [0], "claim": {...}}        →  (subtermAt p [0], claim with addr := [0])
```

`Cert.resolveClaims` is the step, and it is **not** part of `ofJson`: decoding does
not know the program. `Main.lean` calls it after decoding, once the program is in
hand. A claim whose path addresses nothing resolves to nothing and is **dropped**,
which refuses rather than accepts.

`childAt` is the numbering, and it is the *only* place the numbering is defined now —
`chk` no longer computes paths at all, so there is nothing for an emitter to
disagree with. Children are numbered left to right in evaluation order. -/

def childAt : Expr → Nat → Option Expr
  | .vasgn _ _ r, 0 => some r
  | .casgn _ r, 0 => some r
  | .cpath (some b) _, 0 => some b
  | .cpathAsgn (some b) _ _, 0 => some b
  | .cpathAsgn none _ r, 0 => some r
  | .cpathAsgn (some _) _ r, 1 => some r
  | .send (some r) _ _ _, 0 => some r
  | .send (some _) _ as bl, i =>
    if i ≤ as.length then as[i - 1]? else if i == as.length + 1 then bl else none
  | .send none _ as bl, i =>
    if i ≤ as.length then as[i - 1]? else if i == as.length + 1 then bl else none
  | .block _ _ b, 0 => some b
  | .blockpass (some b), 0 => some b
  | .yield' as, i => as[i]?
  | .if' c _ _, 0 => some c
  | .if' _ t _, 1 => some t
  | .if' _ _ (some e), 2 => some e
  | .while' c _, 0 => some c
  | .while' _ b, 1 => some b
  | .dowhile b _, 0 => some b
  | .dowhile _ c, 1 => some c
  | .for' _ co _, 0 => some co
  | .for' _ _ b, 1 => some b
  | .def' _ _ b, 0 => some b
  | .defs r _ _ _, 0 => some r
  | .defs _ _ _ b, 1 => some b
  | .array es, i => es[i]?
  | .splat (some o), 0 => some o
  | .ret (some x), 0 => some x
  | .brk (some x), 0 => some x
  | .nxt (some x), 0 => some x
  | .class' _ none b, 0 => some b
  | .class' _ (some su) _, 0 => some su
  | .class' _ (some _) b, 1 => some b
  | .module' _ b, 0 => some b
  | .scopedClass (some ba) _ _, 0 => some ba
  | .scopedClass _ _ b, 1 => some b
  | .scopedModule (some ba) _ _, 0 => some ba
  | .scopedModule _ _ b, 1 => some b
  | .sclass o _, 0 => some o
  | .sclass _ b, 1 => some b
  | .begin' b _ _ _, 0 => some b
  | .super' as bl, i => if i < as.length then as[i]? else bl
  | .zsuper bl, 0 => bl
  | .defined x, 0 => some x
  | .seq es, i => es[i]?
  | _, _ => none

/-- Walk a path from the root, outermost step first — which is the *reverse* of the
    innermost-first order a `Path` is written in, so the caller reverses once and this
    recurses on the list. Structural, so no fuel needed here: `Json.lean` is off the
    checked path anyway (L135), but a plain list recursion is free. -/
def subtermFwd (e : Expr) : List Nat → Option Expr
  | [] => some e
  | i :: rest => (childAt e i).bind (fun ch => subtermFwd ch rest)

/-- Resolve an address against a program. -/
def subtermAt (e : Expr) (π : Path) : Option Expr := subtermFwd e π.reverse

/-- Resolve every claim's address to the subterm it addresses, dropping the ones that
    address nothing. Called by `Main.lean` after decoding, because decoding does not
    know the program. -/
def Cert.resolveClaims (p : Expr) (c : Cert) : Cert :=
  { c with claims := c.claims.filterMap fun entry =>
      (subtermAt p entry.2.addr).map (fun sub => (sub, entry.2)) }

def envToJson (Γ : Env) : Json :=
  Json.arr (Γ.map fun e => Json.mkObj [("name", Json.str e.1), ("ty", tyToJson e.2)]).toArray

def envOfJson (j : Json) : Except String Env := do
  pure (← (← j.getArr?).toList.mapM fun e => do
    pure ((← (← e.getObjVal? "name").getStr?), (← tyOfJson (← e.getObjVal? "ty"))))

def nodeClaimToJson (cl : NodeClaim) : Json :=
  Json.mkObj ([("ty", tyToJson cl.ty),
               ("path", Json.arr (List.map (fun i : Nat => Json.num i) cl.addr).toArray)] ++
    (match cl.env with | some Γ => [("env", envToJson Γ)] | none => []) ++
    (match cl.tys with
     | some τs => [("tys", Json.arr (τs.map tyToJson).toArray)]
     | none => []))

def nodeClaimOfJson (j : Json) : Except String NodeClaim := do
  let ty ← tyOfJson (← j.getObjVal? "ty")
  let addr ← match j.getObjVal? "path" with
    | .error _ => pure []
    | .ok v => do pure (← (← v.getArr?).toList.mapM fun x => x.getNat?)
  let env ← match j.getObjVal? "env" with
    | .error _ => pure none
    | .ok v => do pure (some (← envOfJson v))
  let tys ← match j.getObjVal? "tys" with
    | .error _ => pure none
    | .ok v => do pure (some (← (← v.getArr?).toList.mapM tyOfJson))
  pure { ty := ty, addr := addr, env := env, tys := tys }

/-- A claim on the wire. The key is a placeholder until `Cert.resolveClaims` runs —
    `Expr.nil` matches nothing a program is likely to claim about, and an unresolved
    certificate therefore *refuses* the claim rather than misapplying it. -/
def claimOfJson (j : Json) : Except String (Expr × NodeClaim) := do
  pure (.nil, (← nodeClaimOfJson (← j.getObjVal? "claim")))

def claimToJson (e : Expr × NodeClaim) : Json :=
  Json.mkObj [("claim", nodeClaimToJson e.2)]

def Cert.toJson (c : Cert) : Json :=
  Json.mkObj [
    ("version", Json.num c.version),
    ("theta", Json.arr (c.theta.map fun e =>
        Json.mkObj [("var", Json.num e.1), ("ty", tyToJson e.2)]).toArray),
    ("delta_rows", Json.arr (c.deltaRows.map rowClaimToJson).toArray),
    ("bodies", Json.arr (c.bodies.map bodyCertToJson).toArray),
    ("ledger", Json.arr (c.ledger.map stepToJson).toArray),
    ("claims", Json.arr (c.claims.map claimToJson).toArray),
    ("fuel", Json.num c.fuel),
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
  let claims ← opt "claims" claimOfJson
  -- **The fuel defaults rather than being required**, for the reason every other
  -- field does: an emitter that has never heard of it still produces a decodable
  -- certificate, and the default refuses rather than accepts on a program too deep
  -- for it (V9).
  let fuel ← match j.getObjVal? "fuel" with
    | .error _ => pure 64
    | .ok v => v.getNat?
  let assumes ← match j.getObjVal? "assumes" with
    | .error _ => pure Assn.emp
    | .ok v => assnOfJson v
  pure { version := version, theta := theta, deltaRows := deltaRows, bodies := bodies,
         ledger := ledger, claims := claims, fuel := fuel, assumes := assumes }

/-! ## 5. The verdict, as JSON

Read `means` for what an accept is: §2 constraint 4 makes the residue first-class, so
the strength of the conclusion is a *field* and not something a consumer has to infer
from the presence of `carries`. That is L265's `means` discipline applied to a stronger
verdict. -/

def verdictToJson (c : Cert) (p : Expr) : Json :=
  let ok := validateFull c p
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
    -- **C2's ledger.** Reported outside the `if` for `bodies_certified`'s reason: the
    -- number of cancellations a certificate *states* is a gradient, and `ledger_ok` is
    -- what `Proof/Cert/Ledger.lean`'s `satProvs_ledgerStore` is conditional on.
    ("ledger_steps", Json.num c.ledger.length),
    ("ledger_ok", Json.bool (ledgerOk c p)),
    -- Outside the `if` for the same reason: how many rows a certificate *carries* is a
    -- fact about the certificate, not about the verdict, and a rejected certificate's
    -- row count is what an emitter reads while iterating.
    ("carries_rows", Json.num c.deltaRows.length),
    -- **The two dimensions of the verdict** (V14), both outside the `if` because a
    -- reader iterating on an emitter needs to know *which* tier a reject missed.
    -- `certifies` is the sound tier — `validate` plus a program every head of which
    -- `infer` has an arm for, plus no load-bearing node claim. `validate` alone is
    -- the coverage ratchet, and the gap between the two numbers is the schema work
    -- §10 of the design document lists.
    ("claims_made", Json.num c.claims.length),
    ("claim_free", Json.bool c.claimFree),
    ("in_fragment", Json.bool (inferFrag c.fuel p)),
    ("certifies", Json.bool (Cert.certifies c p)),
    -- Per claim, whether it replayed. The gradient at its finest grain, and what an
    -- emitter reads back to iterate (`certify/implementation-notes.md` E5): the
    -- untrusted side proposes signatures and this is the adjudication.
    ("body_results", Json.arr (c.bodies.map fun b =>
        Json.mkObj [("owner", Json.str b.owner), ("name", Json.str b.name),
                    ("ret", Json.str (tyName b.sig.ret)),
                    ("ok", Json.bool (bodyOk c p b))]).toArray)] ++
    (if ok then
      [("unconditional", Json.bool c.unconditional),
       ("tier", Json.str (if Cert.certifies c p then "sound" else "covered")),
       ("means", Json.str (if !Cert.certifies c p then
            "this program checks at the claimed table under the claimed nodes; the accept is not yet transferred to `Inv` (see `in_fragment`/`claim_free`)"
          else if c.unconditional then
            "no reachable outcome of this program is type-stuck"
          else
            "no reachable outcome of this program is type-stuck, given `carries`")),
       ("carries", Json.str c.rowAssn.render),
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
           else if !chkOk c p then "chk"
           else "ledger"))]))

end RubyCore.Cert
