import RubyCore.Cert.Check

/-!
# The validator

`docs/semantics/certificate-language.md` §6 C0, and §2's four non-negotiables are
what the shape below is answering. **Rewritten at V9–V14**: the conjunct that used to
be `nominalOk` — `(infer (c.table p) [] p true …).isSome` — is now `chkOk`, and the
whole file is downstream of that one change. `Cert/Check.lean`'s header is the
argument for it; this file is what the argument bought.

`validate c p : Bool` is a conjunction of six decidable checks, each of which is a
*re-check of a recorded choice* and none of which searches:

| # | check | the choice it re-checks |
|---|---|---|
| 1 | `c.version == Cert.version` | — (§2 constraint 5) |
| 2 | `rowsGuarded (declsOf p) c.deltaRows` | which rows the table is extended by |
| 3 | `rowsDeclared c` | that the extension is *visible* in `assumes` |
| 4 | `eqsOk c` | the solver's `θ`, against every equality the open pass recorded |
| 5 | `bodiesOk c p` | the per-body typings, at their claimed signatures |
| 6 | `chkOk c p` | the consequence: the program checks at that table, under those node claims |

## What changed, and it is three things

**(a) The whole conjunction now `decide`s.** Every example below is `by decide`,
where the C0 version needed a fifteen-name `simp` list over `infer`'s equation
lemmas at each one. That is §8 risk 1's cost paid off rather than inherited: `chk` is
structurally recursive on fuel (V9), so the kernel reduces it, so *"replayed in
Lean"* means the kernel decided the replay and not that a tactic did. §9.3 recorded
the opposite as an inherited fact; it was inherited from a function this file no
longer calls.

**(b) Coverage is no longer `infer`'s coverage.** `chk` has an arm for all 45 `Expr`
heads, so a certificate can address a `begin`/`rescue`, a `hash`, a `for`, a
parameterized `def`. §9.1's *"a certificate cannot say anything the nominal judgement
cannot check"* was a fact about `nominalOk`, and it is retired.

**(c) An accept is now two-tiered, and the tiers have names.** `validate c p` is the
coverage verdict — the fourth ratchet's unit. `Cert.certifies c p` adds
`inferFrag c.fuel p && c.claimFree` and is the *sound* verdict, the one
`validate_sound` reads. §2 constraint 4 says the residue is output rather than
prose; this is that principle applied to the frontier itself, which used to be
implicit in `infer`'s trailing `| _ => none`.

## What is trusted, precisely

`validate_sound` (`Proof/Cert/Sound.lean`) consumes exactly two things: `DeclsOk` for
the table the certificate names, and `CtlOk` at `Machine.init p`. The second comes
from (6) *via `chk_infer`* — which is the bridging lemma §3's price table budgeted
for and §9.1 reported as unnecessary. It was unnecessary while the validator *was*
`infer`; the moment the validator is its own function, the bridge is exactly the
obligation §3 named, and `Proof/Cert/Check.lean` is where it is discharged.

The first is where the certificate's trust lives, and it is bounded by the
extension: `declsOf p`'s own `DeclsOk` is F1a's (`tableOk_declsOk`, `rfl` at the boot
heap), and each claimed row costs exactly one `EntryOk` obligation, which (3) forces
to appear as a `decl` atom of `assumes`.

**The ladder of verdict strength is now two-dimensional** (V14): `deltaRows` says how
much of the *table* is assumed, and `claims` says how much of the *derivation* is.
`Cert.unconditional` and `Cert.claimFree` report the two, and the fourth ratchet
counts the four populations apart.

## What the `req`/`obl`/`eqv` atoms of `assumes` are *not*

They are the **emitter's report**, not a hypothesis of the program-level theorem, and
saying so is the honest half of this milestone. `validate_sound` does not consume
them, because the whole-program open pass does not feed the nominal one: L262 and
`Proof/Static/OpenSelf.lean`'s header both say why, and closing that gap is
`discharge_sound`'s open premise, i.e. C2.

What (4) nevertheless buys is real and cheap: `eqsOk` re-checks the *solver's answer*
against every equality the open pass recorded, so an inconsistent `θ` is rejected
rather than carried.
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

`chk` at the table the certificate names, with the certificate's fuel, from the
toplevel position at the root path. This is the conjunct that used to be
`nominalOk`, and the only difference visible here is the function's name — which is
the point: §1's decoupling is about *who searches*, and relocating the search from a
verified inference pass to a checked-in-the-kernel replay is what the pivot was
for. -/

/-- The program checks at the table the certificate names — the one fact `CtlOk`
    consumes at `Machine.init p`, and (with the table itself) the only part of
    `validate` that `validate_sound` reads. -/
def chkOk (c : Cert) (p : Expr) : Bool :=
  (chk c c.fuel (c.table p) [] p true { cls := "Object" } []).isSome

/-! ## 3. The per-body claims

A `BodyCert` records *which signature this body was typed at* and the validator
re-derives the interior. The check is deliberately `UserConforms`-shaped
(`Proof/Static/Decls.lean`): its clauses are the arity agreement, `d.blk = none`,
`defFree`ness of the body, and *the body checks below `d.ret` in the context
`enterUserMethod` builds*. That is what makes the fourth ratchet's unit — *bodies
certified by replayed certificate* — the same unit the invariant consumes, rather
than a number of its own.

**Parameters are now allowed** (V14). C0's `bodyOk` required `ps.isEmpty` and
`b.sig.params.isEmpty`, because `infer`'s `def` arm does; §9.6 records the
consequence — the slice's 7 `open_params` accepts *"which `bodyOk` cannot claim by
construction"*. `chk`'s claimed `def` arm binds declared parameters, so the
restriction goes, and the body's parameters are bound at the signature's types. -/

/-- The list arm of `findDef`, with the recursive call as a parameter — the same
    shape `Cert/Check.lean`'s helpers have, and for the same reason (V9): a `mutual`
    block over `Expr`/`List Expr` compiles to well-founded recursion, which does not
    reduce in the kernel, which would have put `bodiesOk` back on the wrong side of
    §8 risk 1 after `chk` had got it off. Measured: the first draft of this file was
    a `mutual` and `bodiesCertified` would not `decide`. -/
def findDefList (g : Path → Expr → Option (List Param × Expr × Path))
    (i : Nat) (π : Path) : List Expr → Option (List Param × Expr × Path)
  | [] => none
  | e :: rest =>
    match g (i :: π) e with
    | some r => some r
    | none => findDefList g (i + 1) π rest

/-- The parameters, body **and path** of `cls#name`, as the program writes them.

    `cur` is the enclosing class scope, threaded rather than reconstructed for
    `Types/Program.lean`'s reason: `self` inside `class C … end` is a different thing
    from `self` inside a `def`, and the row's key is the *definee*.

    **The path is new at V14** and it is what makes node claims usable inside a
    method body: `c.claims` is keyed on paths from the *program* root, so a body
    checked at a fabricated root would look up claims that are not there. Returning
    the address the walk arrived at is the whole fix.

    It deliberately does **not** descend into a `def` body, into an `if`, or into a
    `while`: a `def` inside any of those is not a fact about the program (L263's
    first refusal), so a certificate may not claim its row. -/
def findDef (cls name : String) : Nat → String → Path → Expr →
    Option (List Param × Expr × Path)
  | 0, _, _, _ => none
  | n + 1, cur, π, e =>
    match e with
    | .def' nm ps body => if cur == cls && nm == name then some (ps, body, π) else none
    | .class' c _ body => findDef cls name n c (0 :: π) body
    | .module' c body => findDef cls name n c (0 :: π) body
    | .scopedClass _ c body => findDef cls name n c (1 :: π) body
    | .scopedModule _ c body => findDef cls name n c (1 :: π) body
    | .seq es => findDefList (fun π' e' => findDef cls name n cur π' e') 0 π es
    | .begin' body _ _ _ => findDef cls name n cur (0 :: π) body
    | _ => none

/-- The table the `bodies` section is checked at: `Cert.table` plus the section's own
    claimed rows. Each is added only if its name is fresh, so the fold is shadow-free
    for `rowsGuarded`'s reason. -/
def Cert.bodyTable (c : Cert) (p : Expr) : Decls :=
  c.bodies.foldl
    (fun D b => if declaresName D b.name then D else addRow D b.owner b.name b.sig)
    (c.table p)

/-- One body's claim, re-checked at `bodyTable`. -/
def bodyOk (c : Cert) (p : Expr) (b : BodyCert) : Bool :=
  match findDef b.owner b.name c.fuel "Object" [] p with
  | none => false
  | some (ps, body, π) =>
    b.sig.blk == none && b.sig.params.length == ps.length && defFreeF c.fuel body &&
      (match chk c c.fuel (c.bodyTable p) (bindParams c.fuel ps b.sig.params []) body false
          { cls := b.owner, selfCls := some b.owner, ret := some b.sig.ret,
            meth := some b.name, params := some b.sig.params } (0 :: π) with
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

/-! ## 5. `validate`, and the two tiers -/

/-- **The validator.** See the table in the header for what each conjunct re-checks.

    Ordered cheapest-first so that a malformed certificate is rejected before `chk`
    runs — which matters less than it did, since `chk` is no longer the one
    non-reducible conjunct, but costs nothing to keep. -/
def validate (c : Cert) (p : Expr) : Bool :=
  c.version == RubyCore.Cert.version &&
  rowsGuarded (declsOf p) c.deltaRows &&
  rowsDeclared c &&
  eqsOk c &&
  bodiesOk c p &&
  chkOk c p

/-- **The sound tier** — `validate`, plus the two conditions under which the accept
    transfers to `Inv` and therefore to *no reachable `typeStuck`*:

    * `inferFrag c.fuel p` — every head of the program is one where `chk` and `infer`
      are the same function (`Cert/Check.lean` §5);
    * `c.claimFree` — no node claim is load-bearing, since a claim is precisely a
      place where `chk` answers and `infer` does not.

    Two `Bool`s rather than a side condition in a docstring, because §2 constraint 4
    is that the strength of a verdict is *output*. `validate_sound` takes this
    conjunction; `validate` alone is the coverage ratchet. -/
def Cert.certifies (c : Cert) (p : Expr) : Bool :=
  validate c p && inferFrag c.fuel p && c.claimFree

/-- **Is the accept unconditional?** Exactly when the table is not extended: the
    theorem's hypothesis quantifies over the claimed rows' `EntryOk`s and there are
    none. Kept as a `Bool` beside `validate` so that the fourth ratchet counts the
    populations separately (V6), which is §8 risk 3's requested mitigation. -/
def Cert.unconditional (c : Cert) : Bool := c.deltaRows.isEmpty

/-! ## 6. Reporting

The residue, rendered exactly as `--assn-program` renders an assertion, because §2
constraint 4 is that the residue is *output* and not prose. Two lines and they are
different claims: `carries:` is what the conclusion is conditional on, `reports:` is
what the emitter said and the program-level theorem does not read (§1's honest
half). -/

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

/-! ## 7. Checked facts, and the C0 gate re-measured

**Kernel reducibility, measured rather than assumed** (§2 constraint 2, §8 risk 1),
and the measurement has changed sign. C0 reported:

> Four of `validate`'s six conjuncts are `decide`-able at a literal certificate. …
> The two that are not are `nominalOk` and `bodiesOk`, and the reason is **not** the
> certificate: `infer` is well-founded-recursive, so kernel reduction gets stuck.

**All six now are**, and every example below is one `decide`. `native_decide` appears
nowhere; nothing in this file is discharged by `simp` over equation lemmas. The
prescribed fix of §8 risk 1 — *reduction-friendly validator data structures* — turned
out not to need `Types/Core.lean` restructured, only not called. -/

/-! ### The round trip

A program the nominal fragment accepts validates against the **empty** certificate —
no table extension, no residue, nothing assumed, no node claimed. This is `egVcall`
(`Proof/StaticSoundness.lean`), the L265 headline's shape at the one class the
nominal fragment can both reopen and produce a value of. -/

def egVcall : Expr :=
  .class' "String" none
    (.seq [ .def' "value" [] (.int 1),
            .def' "get" [] (.vcall "value"),
            .send (some (.str "x")) "get" [] none ])

example : validate {} egVcall = true := by decide

/-- …and it is in the **sound** tier: every head is one `infer` has an arm for, and
    nothing is claimed. This is the `Bool` `validate_sound` reads. -/
example : Cert.certifies {} egVcall = true := by decide

example : Cert.unconditional ({} : Cert) = true := by decide

/-- …and the **body** claims replay too: `String#value : () → Integer` and
    `String#get : () → Integer` are the two rows the program's own `def`s supply, and
    the validator re-derives each body at its claimed signature. This is the fourth
    ratchet's unit — two bodies certified by replayed certificate.

    Note *which* table each body is checked at: `bodyTable`, which holds the two
    claims themselves. `get`'s body is `value`, so checking against `c.table p` alone
    would refuse it — the mutual-recursion discipline §3's header records. -/
def egVcallCert : Cert :=
  { bodies := [{ owner := "String", name := "value", sig := { params := [], ret := .int } },
               { owner := "String", name := "get", sig := { params := [], ret := .int } }] }

example : validate egVcallCert egVcall = true := by decide

/-- **A body claimed at the wrong signature is refused**, which is what makes the
    check a check: `get` answers `Integer`, and a certificate claiming `Symbol` is
    rejected rather than believed. -/
example :
    validate { bodies := [{ owner := "String", name := "get",
                            sig := { params := [], ret := .sym } }] } egVcall = false := by
  decide

/-- **A body the program does not write is refused**, rather than vacuously accepted —
    which is the difference between `findDef` answering `none` and a `List.all` over an
    empty list. -/
example :
    validate { bodies := [{ owner := "String", name := "absent",
                            sig := { params := [], ret := .int } }] } egVcall = false := by
  decide

/-- **Fuel too small is a refusal, not an accept** (V9). The safe direction, and it is
    the whole argument for letting the certificate carry the bound. -/
example : validate { fuel := 2 } egVcall = false := by decide

/-! ### The extension: `1 / 2`

The standing example of this initiative. `srb` accepts `1 / 2`; the nominal judgement
abstains, because `/` is absent from `baseDecls` — and the absence is *deliberate*
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

/-- Without the row the program does not check… -/
example : chkOk {} egDiv = false := by decide

/-- …and with it, the certificate validates — and is still in the sound tier, since
    a *table* extension is not a node claim. -/
example : validate egDivCert egDiv = true := by decide
example : Cert.certifies egDivCert egDiv = true := by decide

/-- **It is a residual accept, and the ratchet counts it as one.** -/
example : Cert.unconditional egDivCert = false := by decide

/-- **A claimed row that `assumes` does not mention is refused** — which is the check
    that keeps the trust legible (V3). Same certificate, `assumes := emp`. -/
example : validate { egDivCert with assumes := .emp } egDiv = false := by decide

/-- …and so is one whose `assumes` atom is at a *different* signature from the row it
    is supposed to license. The atom is what the theorem reads, so a mismatch would be
    a claimed row with no hypothesis behind it. -/
example :
    validate { egDivCert with assumes := .decl .int "/" { params := [], ret := .int } }
      egDiv = false := by decide

/-- **The `eqv` check fires**: an assertion recording `α₃ = Integer` against a `theta`
    that sends `α₃` somewhere else is an inconsistent solver answer, and `eqsOk` is
    one `decide` per atom. This is the L265 headline's residue shape — `α3 = Integer`
    — being re-checked rather than believed. -/
example :
    validate { theta := [(3, .sym)], assumes := .eqv 3 (.nom .int) } egVcall = false := by
  decide

/-- …and passes at the `theta` the solver should have produced. -/
example :
    validate { theta := [(3, .int)], assumes := .eqv 3 (.nom .int) } egVcall = true := by
  decide

/-! ### The coverage tier — what C0 could not address at all

Four programs, one per class of head that had no `infer` arm. Each **validates** and
each is *outside* the sound tier, and both facts are checked: that is the two-tier
verdict working as designed rather than as a caveat. -/

/-- A `begin`/`rescue` region — the L231/L233 join wall. Both exits are `Integer`, so
    `joinAll` answers without a claim and the region checks. -/
def egBegin : Expr :=
  .begin' (.send (some (.int 1)) "+" [.int 2] none)
    [([.const "StandardError"], some (.lvar, "e"), .int 0)] none none

example : validate {} egBegin = true := by decide
/-- …and it is honestly outside the sound tier: `CtlOk` has no `begin` case. -/
example : inferFrag 64 egBegin = false := by decide
example : Cert.certifies {} egBegin = false := by decide

/-- A `hash` literal, a `defined?`, and a `module` — three heads, no claims needed. -/
def egMisc : Expr :=
  .seq [ .hash [(.sym "a", .int 1), (.sym "b", .str "x")],
         .defined (.var .lvar "nope"),
         .module' "M" (.int 3) ]

example : validate {} egMisc = true := by decide
example : Cert.certifies {} egMisc = false := by decide

/-- **A `for` loop over an array literal**, whose target binds in the enclosing scope
    and leaks — which is why the answer's environment is the extended one. -/
def egFor : Expr :=
  .for' [(.lvar, "i")] (.array [.int 1, .int 2]) (.var .lvar "i")

example : validate { claims := [([], { ty := .int })] } egFor = true := by decide

/-- **A claim is not a licence.** The same `for` loop with the target claimed at
    `Symbol` fails, because the body reads `i` and then nothing accepts it where an
    `Integer` was needed — a wrong claim costs the body and cannot buy the accept.
    Here the failure is sharper still: the loop body must leave the environment where
    it found it, and it does, but the enclosing `+` refuses. -/
def egForUse : Expr :=
  .for' [(.lvar, "i")] (.array [.int 1, .int 2])
    (.send (some (.var .lvar "i")) "+" [.int 1] none)

example : validate { claims := [([], { ty := .int })] } egForUse = true := by decide
example : validate { claims := [([], { ty := .sym })] } egForUse = false := by decide

/-! ### C5 — a claimed join the deterministic rule refuses

`if c then 1 else :s end` has branches at `Integer` and `Symbol`. `joinTy` refuses:
it answers the four cases the fragment produces and *"answering `.any` for the rest
would be an upper bound but a useless one"*. So this is the stackmap case — the
certificate states the join and `chk` checks that **both branches are below it**,
which is Rose's lightweight bytecode verification and the milestone C5 asked for. -/

def egJoin : Expr := .if' .tru (.int 1) (some (.sym "s"))

/-- Unclaimed, it is refused — the join has no deterministic answer. -/
example : validate {} egJoin = false := by decide

/-- Claimed at `any`, both branches are below it and the region checks. -/
example : validate { claims := [([], { ty := .any })] } egJoin = true := by decide

/-- Claimed at `Integer`, the `else` branch is *not* below it and the claim is
    refused. This is the check that makes the stackmap a stackmap. -/
example : validate { claims := [([], { ty := .int })] } egJoin = false := by decide

/-- A claimed join is a node claim, so the accept is in the coverage tier only —
    even though every *head* of the program is in `inferFrag`. Both dimensions of
    V14's ladder, visible at one program. -/
example : inferFrag 64 egJoin = true := by decide
example : Cert.certifies { claims := [([], { ty := .any })] } egJoin = false := by decide

/-! ### C6 — a parameterized `def`, certified at a claimed signature

`def twice(a); a; end` is §4 D2's own example and §9.6's `open_params` population:
`infer`'s `def` arm refuses it on its **first** guard (`params.isEmpty`), so no
certificate could ever claim its body. `chk`'s claimed `def` arm binds the declared
parameter types and checks the body below the declared return. -/

def egParam : Expr :=
  .class' "String" none (.def' "twice" [.req "a"] (.var .lvar "a"))

/-- Unclaimed, refused — exactly as `infer` refuses it. -/
example : validate {} egParam = false := by decide

/-- Claimed at `(Integer) → Integer`, the body checks. The path `[0]` is the
    `def` node: the class body, which is child 0 of the root, *is* the `def`. -/
example :
    validate { claims := [([0], { ty := .int, tys := some [.int] })] } egParam = true := by
  decide

/-- …and claimed at `(Integer) → Symbol` it is refused: the body answers the
    parameter's type, which is `Integer`. -/
example :
    validate { claims := [([0], { ty := .sym, tys := some [.int] })] } egParam = false := by
  decide

/-- **And the body is certifiable**, which is the fourth ratchet's unit and the thing
    §9.6 said `bodyOk` *"cannot claim by construction"*. It can now. -/
example :
    bodiesCertified
      { claims := [([0], { ty := .int, tys := some [.int] })],
        bodies := [{ owner := "String", name := "twice",
                     sig := { params := [.int], ret := .int } }] } egParam = 1 := by
  decide

end RubyCore.Cert
