import RubyCore.Cert.Format

/-!
# C0 — the validator

`docs/semantics/certificate-language.md` §6 C0, and §2's four non-negotiables are
what the shape below is answering. `validate c p : Bool` is a conjunction of five
decidable checks (V5), each of which is a *re-check of a recorded choice* and none of
which searches:

| # | check | the choice it re-checks |
|---|---|---|
| 1 | `c.version == Cert.version` | — (§2 constraint 5) |
| 2 | `rowsGuarded (declsOf p) c.deltaRows` | which rows the table is extended by |
| 3 | `rowsDeclared c` | that the extension is *visible* in `assumes` |
| 4 | `nominalOk c p` | the consequence: the program types at that table |
| 5 | `eqsOk c` + `bodiesOk c p` | the solver’s `θ`, and the per-body claims |

## What is trusted, precisely — and it is only (2)+(3)

`validate_sound` (`Proof/Cert/Sound.lean`) consumes exactly two things: `DeclsOk` for
the table the certificate names, and `CtlOk` at `Machine.init p`. The second is (4),
which is a *fact* — `infer` computed it. The first is where the certificate's trust
lives, and it is bounded by the extension: `declsOf p`'s own `DeclsOk` is F1a's
(`tableOk_declsOk`, `rfl` at the boot heap), and each claimed row costs exactly one
`EntryOk` obligation, which (3) forces to appear as a `decl` atom of `assumes`.

**So the ladder of verdict strength is `deltaRows`, and nothing else** (V6, corrected):

* `deltaRows = []` — the theorem has *no hypothesis*. `validate_unconditional` states
  that separately, because an unconditional accept is a different claim and should not
  have to be read out of a quantifier.
* `deltaRows ≠ []` — the theorem is conditional on exactly those rows' `EntryOk`s,
  which are the `decl` atoms `explainResidue` prints.

## What the `req`/`obl`/`eqv` atoms of `assumes` are *not*

They are the **emitter's report**, not a hypothesis of the program-level theorem, and
saying so is the honest half of this milestone. `validate_sound` does not consume
them, because the whole-program open pass does not feed `check`: L262 and
`Proof/Static/OpenSelf.lean`'s header both say why (*"`check` does not call
`inferOpen`, so there is no theorem of the form open-self accepts `p` ⇒ `p` does not
type-stick"*), and closing that gap is `discharge_sound`'s open premise, i.e. C2.

What (5) nevertheless buys is real and cheap: `eqsOk` re-checks the *solver's answer*
against every equality the open pass recorded, so an inconsistent `θ` is rejected
rather than carried. It is `satStoreB`'s second clause, at the assertion instead of at
the store, and it is kernel-`decide`able where (4) is not — see §4.
-/

namespace RubyCore.Cert

open RubyCore.Types

/-! ## 1. The extension is visible

Every claimed row must appear as a `decl` atom of `assumes`. `entailAtom` is the
existing membership test (`Types/Assn.lean` §5), reused rather than re-spelled so that
the validator's check and `denote_of_mem_declAtoms`' read-out cannot drift — which is
the same reason `RowClaim.atom` is a function. -/

/-- Every claimed row is a `decl` atom of `assumes`. -/
def rowsDeclared (c : Cert) : Bool :=
  c.deltaRows.all fun r => entailAtom c.assumes (nomTy r.cls) r.name r.sig

/-! ## 2. The consequence

`check` with the table as a parameter — and §1's decoupling is about *who searches*,
not about what is provable (§8 risk 2), so this being `check`-shaped is the design
rather than a shortfall: the nominal judgement is deterministic and syntax-directed,
and the search a certificate relocates is the choice of table. -/

/-- The program types at the table the certificate names — the one fact `CtlOk`
    consumes at `Machine.init p`, and (with the table itself) the only part of
    `validate` that `validate_sound` reads. -/
def nominalOk (c : Cert) (p : Expr) : Bool :=
  (infer (c.table p) [] p true { cls := "Object" }).isSome

/-! ## 3. The per-body claims

C0 is signatures-only (§4 D1), so a `BodyCert` records *which signature this body was
typed at* and the validator re-derives the interior. The check is deliberately
`UserConforms`-shaped (`Proof/Static/Decls.lean`): its four clauses are
`d.params = []`, `d.blk = none`, `defFree md.body`, and *the body infers below `d.ret`
in the context `enterUserMethod` builds*. That is what makes the fourth ratchet's unit
— *bodies certified by replayed certificate* — the same unit the invariant consumes,
rather than a number of its own. -/

mutual

/-- The parameters and body of `cls#name`, as the program writes them.

    `cur` is the enclosing class scope, threaded rather than reconstructed for
    `Types/Program.lean`'s reason: `self` inside `class C … end` is a different thing
    from `self` inside a `def`, and the row's key is the *definee*.

    It deliberately does **not** descend into a `def` body, into an `if`, or into a
    `while`: a `def` inside any of those is not a fact about the program (L263's first
    refusal), so a certificate may not claim its row. -/
def findDef (cur cls name : String) : Expr → Option (List Param × Expr)
  | .def' n ps body => if cur == cls && n == name then some (ps, body) else none
  | .class' c _ body => findDef c cls name body
  | .module' c body => findDef c cls name body
  | .scopedClass _ c body => findDef c cls name body
  | .scopedModule _ c body => findDef c cls name body
  | .seq es => findDefList cur cls name es
  | .begin' body _ _ _ => findDef cur cls name body
  | _ => none

def findDefList (cur cls name : String) : List Expr → Option (List Param × Expr)
  | [] => none
  | e :: rest =>
    match findDef cur cls name e with
    | some r => some r
    | none => findDefList cur cls name rest

end

/-- The table the `bodies` section is checked at: `Cert.table` plus the section's own
    claimed rows. Each is added only if its name is fresh, so the fold is shadow-free
    for `rowsGuarded`'s reason. -/
def Cert.bodyTable (c : Cert) (p : Expr) : Decls :=
  c.bodies.foldl
    (fun D b => if declaresName D b.name then D else addRow D b.owner b.name b.sig)
    (c.table p)

/-- One body's claim, re-checked at `bodyTable`. -/
def bodyOk (c : Cert) (p : Expr) (b : BodyCert) : Bool :=
  match findDef "Object" b.owner b.name p with
  | none => false
  | some (ps, body) =>
    ps.isEmpty && b.sig.params.isEmpty && b.sig.blk == none && defFree body &&
      (match infer (c.bodyTable p) [] body false
          { cls := b.owner, selfCls := some b.owner, ret := none, meth := some b.name,
            params := some [] } with
       | some (τ, _, D') => subTy τ b.sig.ret && D' == c.bodyTable p
       | none => false)

def bodiesOk (c : Cert) (p : Expr) : Bool := c.bodies.all (bodyOk c p)

/-- **The fourth ratchet's number**, reported whether or not `validate` accepts,
    because it is the gradient. -/
def bodiesCertified (c : Cert) (p : Expr) : Nat :=
  (c.bodies.filter (bodyOk c p)).length

/-! ## 4. The solver's answer, re-checked

`satStoreB`'s second clause read at the assertion rather than at the store. This is
the one check that is *purely* about `theta`, and it is where §1's claim that "the
solver never enters the TCB" is cashed: the solver emits `θ`, and `θ α == a.subst θ`
is one `decide` per atom. -/

def eqsOk (c : Cert) : Bool :=
  c.assumes.eqAtoms.all fun e => c.thetaFn e.1 == e.2.subst c.thetaFn

/-! ## 5. `validate` -/

/-- **The validator.** See the table in the header for what each conjunct re-checks.

    Ordered cheapest-first so that a malformed certificate is rejected before
    `nominalOk` runs `infer` — which matters, because `infer` is the expensive
    conjunct and the only one that is not kernel-reducible (§6). -/
def validate (c : Cert) (p : Expr) : Bool :=
  c.version == RubyCore.Cert.version &&
  rowsGuarded (declsOf p) c.deltaRows &&
  rowsDeclared c &&
  eqsOk c &&
  bodiesOk c p &&
  nominalOk c p

/-- **Is the accept unconditional?** Exactly when the table is not extended: the
    theorem's hypothesis quantifies over the claimed rows' `EntryOk`s and there are
    none. Kept as a `Bool` beside `validate` so that the fourth ratchet counts the two
    populations separately (V6), which is §8 risk 3's requested mitigation. -/
def Cert.unconditional (c : Cert) : Bool := c.deltaRows.isEmpty

/-! ## 6. Reporting

The residue, rendered exactly as `--assn-program` renders an assertion, because §2
constraint 4 is that the residue is *output* and not prose. Two lines and they are
different claims: `carries:` is what the conclusion is conditional on, `reports:` is
what the emitter said and the program-level theorem does not read (§1's honest half). -/

/-- The sub-assertion the conclusion is conditional on: one `decl` atom per claimed
    row, in the order the table applies them. -/
def Cert.rowAssn (c : Cert) : Assn :=
  Assn.all (c.deltaRows.map fun r => Assn.decl (nomTy r.cls) r.name r.sig)

/-- `assumes` with the claimed rows removed — the part `validate_sound` does not
    consume. -/
def Cert.reportAssn (c : Cert) : Assn :=
  Assn.all
    ((c.assumes.reqAtoms.map fun r => Assn.req r.1 r.2.1 r.2.2) ++
     (c.assumes.oblAtoms.map fun o => Assn.obl o.1 o.2) ++
     (c.assumes.eqAtoms.map fun e => Assn.eqv e.1 e.2))

/-! ## 7. Checked facts, and the C0 gate

**Kernel reducibility, measured rather than assumed** (§2 constraint 2, §8 risk 1).
Four of `validate`'s six conjuncts are `decide`-able at a literal certificate — they
are `List.all` over ground data, which is what §2 predicted. The two that are not are
`nominalOk` and `bodiesOk`, and the reason is **not** the certificate:

> `infer` is well-founded-recursive (three mutually recursive functions over
> `Expr`/`List Expr`/`Option Expr`), so kernel reduction gets stuck.

That is `static-soundness-poc.md` §8.1(4), unchanged, and it is why `check p =
.accept` has been discharged by `simp` over the equation lemmas since P0a. So the
certificate inherits the cost rather than creating it, and the fix §8 risk 1 names —
*reduction-friendly validator data structures, never `native_decide`* — is a
restructuring of `infer`, which is `Types/Core.lean` and out of scope here (§7 norm
7). Recorded as C0's honest answer to its own gate.

Everything below is therefore `decide` where the data is ground and `simp` where
`infer` is named, exactly as `Types/Program.lean`'s examples are. -/

/-- **The round-trip** (§6 C0): a program `check` already accepts validates against
    the **empty** certificate — no table extension, no residue, nothing assumed. This
    is `egVcall` (`Proof/StaticSoundness.lean`), the L265 headline's shape at the one
    class the nominal fragment can both reopen and produce a value of. -/
def egVcall : Expr :=
  .class' "String" none
    (.seq [ .def' "value" [] (.int 1),
            .def' "get" [] (.vcall "value"),
            .send (some (.str "x")) "get" [] none ])

example : validate {} egVcall = true := by
  simp [validate, egVcall, rowsGuarded, rowsDeclared, eqsOk, bodiesOk, bodyOk, findDef, findDefList, nominalOk, Cert.table, Cert.bodyTable,
    Assn.eqAtoms, infer, inferArgs, subTys, subTy, inferSeq, inferElems, declsOf,
    declaresName, baseDecls, readableClasses, reopenableClasses, defFree, defFreeAll,
    addRow, declsFor, sigOf, declFor, declOf?, tyClassNames, groundClassNames, isSelf]

example : Cert.unconditional ({} : Cert) = true := by decide

/-- …and the **body** claims replay too: `String#value : () → Integer` and
    `String#get : () → Integer` are the two rows the program's own `def`s supply, and
    the validator re-derives each body at its claimed signature. This is the fourth
    ratchet's unit — two bodies certified by replayed certificate. -/
def egVcallCert : Cert :=
  { bodies := [{ owner := "String", name := "value", sig := { params := [], ret := .int } },
               { owner := "String", name := "get", sig := { params := [], ret := .int } }] }

/-- …and the **body** claims replay too: `String#value : () → Integer` and
    `String#get : () → Integer` are the two rows the program's own `def`s supply, and
    the validator re-derives each body at its claimed signature. This is the fourth
    ratchet's unit — two bodies certified by replayed certificate.

    Note *which* table each body is checked at: `bodyTable`, which holds the two
    claims themselves. `get`'s body is `value`, so checking against `c.table p` alone
    would refuse it — the mutual-recursion discipline §3's header records. -/
example : validate egVcallCert egVcall = true := by
  simp [validate, egVcallCert, egVcall, rowsGuarded, rowsDeclared, eqsOk, bodiesOk,
    bodyOk, findDef, findDefList, nominalOk, Cert.table, Cert.bodyTable, Assn.eqAtoms,
    infer, inferArgs, subTys, subTy, inferSeq, inferElems, declsOf,
    declaresName, baseDecls, readableClasses, reopenableClasses, defFree, defFreeAll,
    addRow, declsFor, sigOf, declFor, declOf?, tyClassNames, groundClassNames, isSelf]

/-- **A body claimed at the wrong signature is refused**, which is what makes the
    check a check: `get` answers `Integer`, and a certificate claiming `Symbol` is
    rejected rather than believed. -/
example :
    validate { bodies := [{ owner := "String", name := "get",
                            sig := { params := [], ret := .sym } }] } egVcall = false := by
  simp [validate, egVcall, rowsGuarded, rowsDeclared, eqsOk, bodiesOk, bodyOk, findDef,
    findDefList, nominalOk, Cert.table, Cert.bodyTable, Assn.eqAtoms,
    infer, inferArgs, subTys, subTy, inferSeq, inferElems, declsOf,
    declaresName, baseDecls, readableClasses, reopenableClasses, defFree, defFreeAll,
    addRow, declsFor, sigOf, declFor, declOf?, tyClassNames, groundClassNames, isSelf]

/-- **A body the program does not write is refused**, rather than vacuously accepted —
    which is the difference between `findDef` answering `none` and a `List.all` over an
    empty list. -/
example :
    validate { bodies := [{ owner := "String", name := "absent",
                            sig := { params := [], ret := .int } }] } egVcall = false := by
  simp [validate, egVcall, rowsGuarded, rowsDeclared, eqsOk, bodiesOk, bodyOk, findDef,
    findDefList, Cert.table, Assn.eqAtoms, declsOf]

/-! ### The extension: `1 / 2`

The standing example of this initiative. `srb` accepts `1 / 2`; `check` abstains,
because `/` is absent from `baseDecls` — and the absence is *deliberate*
(`Types/Decls.lean`: *"Entries whose conformance is not proved may not appear … `/`
and `%` raise `ZeroDivisionError`"*). So this is the case that exercises a **residue
that cannot be discharged**, and the certificate's job is to make that legible rather
than to hide it: the accept says *`1 / 2` does not type-stick **given** that
`Integer#/` conforms to `(Integer) → Integer`*, which is a claim a reader can check
and reject. -/

def egDiv : Expr := .send (some (.int 1)) "/" [.int 2] none

def egDivCert : Cert :=
  { deltaRows := [{ cls := "Integer", name := "/",
                    sig := { params := [.int], ret := .int }, why := .assumed "rbi" }],
    assumes := .decl .int "/" { params := [.int], ret := .int } }

/-- `check` abstains… -/
example : check egDiv = .unknown := by
  simp [check, egDiv, infer, inferArgs, subTys, subTy, illTyped, tableRefutes, defTy,
    sigOf, declFor, declOf?, declsFor, baseDecls, tyClassNames, declsOf]

/-- …and the certificate validates. -/
example : validate egDivCert egDiv = true := by
  simp [validate, egDivCert, egDiv, rowsGuarded, rowGuards, rowsDeclared, entailAtom,
    Assn.declAtoms, Assn.eqAtoms, eqsOk, bodiesOk, bodyOk, findDef, findDefList, nominalOk, Cert.table, Cert.bodyTable, nomTy,
    infer, inferArgs, subTys, subTy, declsOf, declaresName, baseDecls, addRow,
    declsFor, sigOf, declFor, declOf?, tyClassNames, groundClassNames, isSelf,
    Provenance.honoured]

/-- **It is a residual accept, and the ratchet counts it as one.** -/
example : Cert.unconditional egDivCert = false := by decide

/-- **A claimed row that `assumes` does not mention is refused** — which is the check
    that keeps the trust legible (V3). Same certificate, `assumes := emp`. -/
example :
    validate { egDivCert with assumes := .emp } egDiv = false := by
  simp [validate, egDivCert, egDiv, rowsGuarded, rowGuards, rowsDeclared, entailAtom,
    Assn.declAtoms, declsOf, declaresName, baseDecls, Provenance.honoured, nomTy]

/-- …and so is one whose `assumes` atom is at a *different* signature from the row it
    is supposed to license. The atom is what the theorem reads, so a mismatch would be
    a claimed row with no hypothesis behind it. -/
example :
    validate { egDivCert with assumes := .decl .int "/" { params := [], ret := .int } }
      egDiv = false := by
  simp [validate, egDivCert, egDiv, rowsGuarded, rowGuards, rowsDeclared, entailAtom,
    Assn.declAtoms, declsOf, declaresName, baseDecls, Provenance.honoured, nomTy]

/-- **The `eqv` check fires** (V5's fifth conjunct): an assertion recording `α₃ =
    Integer` against a `theta` that sends `α₃` somewhere else is an inconsistent
    solver answer, and `eqsOk` is one `decide` per atom. This is the L265 headline's
    residue shape — `α3 = Integer` — being re-checked rather than believed. -/
example :
    validate { theta := [(3, .sym)], assumes := .eqv 3 (.nom .int) } egVcall = false := by
  simp [validate, egVcall, rowsGuarded, rowsDeclared, eqsOk, Assn.eqAtoms, Cert.thetaFn,
    ATy.subst, declsOf]

/-- …and passes at the `theta` the solver should have produced. -/
example :
    validate { theta := [(3, .int)], assumes := .eqv 3 (.nom .int) } egVcall = true := by
  simp [validate, egVcall, rowsGuarded, rowsDeclared, eqsOk, Assn.eqAtoms, Cert.thetaFn,
    ATy.subst, bodiesOk, bodyOk, findDef, findDefList, nominalOk, Cert.table, Cert.bodyTable, declsOf,
    infer, inferArgs, subTys, subTy, inferSeq, inferElems,
    declaresName, baseDecls, readableClasses, reopenableClasses, defFree, defFreeAll,
    addRow, declsFor, sigOf, declFor, declOf?, tyClassNames, groundClassNames, isSelf]

end RubyCore.Cert
