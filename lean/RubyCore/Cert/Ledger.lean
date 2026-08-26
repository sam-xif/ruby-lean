import RubyCore.Cert.Validate

/-!
# C2 — the ledger

`docs/semantics/certificate-language.md` §6 **C2**: *"`DischargeStep` list; validator
checks `SatProvs` pairwise instead of re-running `discharge`'s search; the `pinPair`
equalities re-derived and compared."*

## What it closes

L262 proved `discharge_sound` and recorded an honest gap in as many words:

> **The second premise is real and is not discharged here.** `SatProvs D θ st` says
> `sigOf D (θ α) n` really is the signature the `def` supplied — a fact about the
> **table**, not about `θ`. […] Stating it as a premise is the honest split;
> pretending it were free would make the theorem vacuous in exactly the direction
> that matters.

The ledger is what discharges it, and the reason a *certificate* can do what
`Types/Program.lean` could not is §1's whole thesis: `discharge` has to **find** the
requirement/provision pairing, and finding it is a search over the store. The
certificate **states** the pairing, one `DischargeStep` per cancellation, and the
validator does one `sigOf` lookup per step. No search.

## Two checks per step, and they are different obligations

* **`ledgerStepOk`** — `sigOf D (θ α) n` really is the provided signature. This *is*
  `SatProvs`' body, read at one step: a fact about the table, decided by one lookup.
* **`ledgerEqsOk`** — the `pinPair` equalities the cancellation owes are **re-derived**
  (`dischargeSig`, not stored) and checked against `θ`. Re-deriving rather than
  storing is the point: a stored equality would be one more thing to trust, and
  `dischargeSig` is the same function `discharge` uses, so a step whose two signatures
  are not equatable is refused here exactly as `discharge` refuses to cancel it.

`dischargeSig` answering `none` makes `ledgerEqsOk` false, which is L262's three
refusals arriving as rejections rather than as silent non-cancellations.

## The store the ledger determines

A `DischargeStep` carries **both** halves — `required` and `provided` at the same
`(var, name)` — so the ledger determines a whole `Store`: its `rows` are the
requirements and its `provs` the provisions. `ledgerStore?` builds it, and it answers
`none` on a conflict (two steps at one `(var, name)` with different signatures), which
is `Row.insert`'s ★★ and `addProv`'s, upstream, refusing to choose.

That store is what `Proof/Cert/Ledger.lean` states `SatProvs` about, and composing
with `discharge_sound` gives `SatStore` for it from the *cancelled* store alone —
which is the division of labour L262 describes: the untrusted solver is handed
`discharge Σ`, the small thing, and its answer discharges every requirement
`inferOpen` recorded.
-/

namespace RubyCore.Cert

open RubyCore.Types

/-! ## 1. The store the ledger determines -/

/-- One step, applied: the requirement into `rows`, the provision into `provs`.

    `none` on a conflict at either polarity. Both go through `Row.insert`, so
    re-stating the *same* step twice is accepted (a capability fact is duplicable —
    `assertion-language.md` §2) and re-stating it at a different signature is refused.
    It is not *syntactically* idempotent — `setRow`/`addProv` prepend — and §3's
    example says where the equality does hold. -/
def stepInto (st : Store) (s : DischargeStep) : Option Store :=
  ((st.rowOf s.var).insert s.name s.required).bind fun R =>
    (st.setRow s.var R).addProv s.var s.name s.provided

/-- The whole ledger's store. Structural over the list, so it reduces in the kernel. -/
def ledgerFold : Store → List DischargeStep → Option Store
  | st, [] => some st
  | st, s :: rest =>
    match stepInto st s with
    | none => none
    | some st' => ledgerFold st' rest

def Cert.ledgerStore? (c : Cert) : Option Store := ledgerFold {} c.ledger

/-! ## 2. The two checks -/

/-- `SatProvs`' body at one step: the table really does supply this signature at the
    substituted receiver. One `sigOf` lookup. -/
def ledgerStepOk (D : Decls) (θ : TyVar → Ty) (s : DischargeStep) : Bool :=
  sigOf D (θ s.var) s.name
    == some (s.provided.params.map (ATy.subst θ), s.provided.ret.subst θ)

/-- The equalities the cancellation owes, **re-derived** and checked against `θ`. -/
def ledgerEqsOk (θ : TyVar → Ty) (s : DischargeStep) : Bool :=
  match dischargeSig s.required s.provided with
  | some es => es.all fun e => θ e.1 == e.2.subst θ
  | none => false

/-- The ledger, checked. `ledgerStore?` must exist — a conflicting ledger is refused
    rather than partially believed. -/
def ledgerOk (c : Cert) (p : Expr) : Bool :=
  c.ledgerStore?.isSome &&
  c.ledger.all fun s => ledgerStepOk (c.table p) c.thetaFn s && ledgerEqsOk c.thetaFn s

/-- **`validate` plus the ledger.** A separate entry point rather than a seventh
    conjunct of `validate`, and for a mechanical reason worth recording: `ledgerOk`
    lives here and `validate` lives in `Cert/Validate.lean`, which this file imports,
    so folding it in would be a cycle. The split is also the honest one — the ledger's
    theorem (`Proof/Cert/Ledger.lean`) concludes `SatStore`, not `¬ typeStuck`, so it
    is a different obligation and not a stronger version of the same one. -/
def validateFull (c : Cert) (p : Expr) : Bool := validate c p && ledgerOk c p

/-! ## 3. Checked facts

L262's three worked examples, restated as *ledger* claims — the same shapes, with the
pairing stated instead of searched for. `decide`, not `native_decide` (§7 norm 5):
everything here is a `find?` over a two-entry list and `String.decEq`. -/

/-- **L262's headline**, as a ledger. `def get; value; end` beside `def value; 1; end`:
    the requirement is `value : () → α₁`, the provision `value : () → Integer`, and the
    equality the cancellation owes is `α₁ = Integer` — re-derived by `dischargeSig`,
    not stored. -/
def egStep : DischargeStep :=
  { var := 0, name := "value", required := { params := [], ret := .var 1 },
    provided := { params := [], ret := .nom .int } }

example : dischargeSig egStep.required egStep.provided = some [(1, .nom .int)] := by decide

/-- …and `θ` has to meet it. This is the whole content of the second check. -/
example : ledgerEqsOk (fun α => if α == 1 then .int else .any) egStep = true := by decide

/-- A `θ` that sends `α₁` elsewhere is refused. -/
example : ledgerEqsOk (fun _ => Ty.sym) egStep = false := by decide

/-- **The arity disagreement L262 keeps rather than cancels** is refused here too, and
    by the same function: `pinPairs` is length-indexed, so `dischargeSig` answers
    `none` and no `θ` can rescue it. -/
example :
    ledgerEqsOk (fun _ => Ty.int)
      { var := 0, name := "value", required := { params := [.nom .int], ret := .var 1 },
        provided := { params := [], ret := .nom .int } } = false := by decide

/-- Two steps at one `(var, name)` with different signatures: no store, so no ledger.
    `Row.insert`'s ★★ refusing to choose, one layer up. -/
example :
    ({ ledger := [egStep, { egStep with provided := { params := [], ret := .nom .sym } }] }
      : Cert).ledgerStore? = none := by
  decide

/-- …and the same step twice is accepted, because a capability fact is duplicable
    (`assertion-language.md` §2). It is **not** syntactically idempotent, and that is
    `Store`'s documented prepend-shadowing rather than a defect: `setRow`/`addProv`
    prepend, `rowOf`/`provOf` read the first hit, so a repeated step leaves a dead
    duplicate behind and every lookup is unchanged. Asserted at the lookups, which is
    where it is true and where every consumer reads. -/
example :
    (({ ledger := [egStep, egStep] } : Cert).ledgerStore?.map (fun st =>
        (st.rowOf 0, st.provOf 0)))
      = (({ ledger := [egStep] } : Cert).ledgerStore?.map (fun st =>
        (st.rowOf 0, st.provOf 0))) := by
  decide

/-- The store one step determines: the requirement in `rows`, the provision in
    `provs`. Both halves, which is what makes `discharge` applicable to it. -/
example :
    ({ ledger := [egStep] } : Cert).ledgerStore?
      = some { rows := [(0, { entries := [("value", { params := [], ret := .var 1 })] })],
               provs := [(0, { entries := [("value", { params := [], ret := .nom .int })] })] } := by
  decide

/-- **And `discharge` cancels it to exactly the equality it owed** — which is L262's
    first example verbatim, now over a store the *certificate* supplied rather than one
    `inferProgram` computed. -/
example :
    (({ ledger := [egStep] } : Cert).ledgerStore?).map discharge
      = some { rows := [(0, { entries := [] })],
               eqs := [(1, .nom .int)],
               provs := [(0, { entries := [("value", { params := [], ret := .nom .int })] })] } := by
  decide

end RubyCore.Cert
