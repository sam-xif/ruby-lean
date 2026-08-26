import RubyCore.Types.Assn

/-!
# C0 — the certificate grammar

`docs/semantics/certificate-language.md` §3, milestone **C0**. This file is the
*format* and nothing else: the datatype, the substitution it determines, the table
it determines, and the per-claim well-formedness guards. The checker is
`Cert/Validate.lean`; the theorem is `Proof/Cert/Sound.lean`; the JSON codec is
`Cert/Json.lean`. Three files because they are three concerns (§7 norm 3), and the
split is load-bearing for one of them: `Lean.Json.parse` does not reduce in the
kernel (L135), so nothing on the *checked* path may import the codec.

## What a certificate is here

§1.1: **a claimed static shadow of the run.** Concretely, and this is the whole of
C0's design decision (V1):

> A certificate names the **declaration table** the program is to be checked
> against, plus the evidence that the extension over `declsOf p` is legitimate.

Everything else in the strawman grammar of §3 hangs off that. The reason it is the
table and not, say, a per-expression derivation is `CtlOk` (`Proof/Static/Konts.lean`):
the invariant's control clause *is* `infer F Γ e … = some …` at the invariant's own
table `F`, so the one thing a certificate can supply that changes which programs are
provable — without touching `Types/Core.lean` or re-opening preservation (§7 norm 7)
— is `F`.

## The three sections, and which side of the trust boundary each lands on

* **`theta`** — the solver's answer, wholly untrusted. It enters soundness only
  through `denote`, which is stated `∀`-free in `θ`: `⟦A⟧ D θ h` is a proposition
  *about* this `θ`, so a wrong `θ` cannot make a right theorem, it makes a
  hypothesis nobody can discharge.
* **`deltaRows`** — the table extension. Each row is a `decl` atom that has to
  appear in `assumes`, so the extension is legible in the conclusion rather than
  hidden in the table (§1's *"trust is legible"*).
* **`assumes`** — the residue. `validate_sound` quantifies over `⟦assumes⟧`, so an
  accept with `assumes = emp` is unconditional and one with a residue is exactly as
  strong as the residue is true.

## V2 — `.fromDef` is in the grammar and refused by the validator, and why

§3's `Provenance` has two arms, and the `.fromDef` one is described as *"the
validator re-checks body `i` at this sig: CHECKED, zero trust"*. **Measured against
the machinery, a `.fromDef` row cannot be sound at `Machine.init p` at all**, and the
reason is not the validator's:

`MethodRowsOk` obliges `EntryOk F h τ n d` for every row of `F`, at *this* heap. A
row that a program's own `def` supplies is witnessed by `UserEntryOk`, whose
resolution clause is `∀ k, TyClass h τ k → ResolvesUser h k n md` — and at the boot
heap the method is **not installed yet**. So the claim is false, not merely
unproved, and a certificate that carried it would be conditional on a false
assumption: the worst of the two failure modes §8.3 warns about.

The population is also not lost. `infer` *threads* the table (F1b.10): a `def` the
nominal rule admits adds its own row for the rest of the program, so a program whose
rows come from its own `def`s needs no `deltaRows` at all — which is why C0's
round-trip property (everything `--check` accepts re-validates with `assumes = emp`)
holds. What is genuinely out of reach is a row for a `def` the nominal rule *refuses*
(a parameterized one, or one on a class outside `reopenableClasses`), and that is a
**heap-phase** claim — §4's D3, milestone C9 — not a provenance.

So the arm stays in the grammar (the format is versioned, and C9 is where it becomes
checkable), `validate` refuses it by name rather than guessing (§7 norm 4), and
`Provenance.assumed` is the only arm C0–C4 can honour.
-/

namespace RubyCore.Cert

open RubyCore.Types

/-! ## 1. The version

Versioned like `export.rb`'s `Export::VERSION` (§2 constraint 5). Bumped whenever a
field's *meaning* changes; adding a defaulted field does not need a bump, because
`Json.lean`'s decoder defaults it. -/

/-- The certificate format version. -/
def version : Nat := 1

/-! ## 2. Provenance and the row claim -/

/-- Where a claimed row came from — §3's `Provenance`.

    See V2 in the header for why only `.assumed` is honoured at C0–C4. -/
inductive Provenance where
  /-- The program's own `def` at index `i` supplies it. **Reserved for C9**
      (heap phases): the claim is about the heap *after* the `def` runs, and
      `Machine.init`'s heap is before. `validate` refuses it. -/
  | fromDef (i : Nat)
  /-- Sourced outside the program — an RBI sig (C4), a hand-written mock, an LLM.
      Flows into `assumes` as a `decl` atom, so the trust is in the conclusion. -/
  | assumed (src : String)
deriving DecidableEq, Repr, Inhabited

/-- Is this provenance one C0 can honour? A `Bool` rather than a pattern match at
    the use site so that the refusal has a name to be reported under. -/
def Provenance.honoured : Provenance → Bool
  | .assumed _ => true
  | .fromDef _ => false

/-- §3's `RowClaim`: one row of the table the certificate names, with its
    provenance.

    Keyed by a **class name** and not by a `Ty`, unlike `Assn.decl`. That is
    `addRow`'s key and `nomTy` is the map to the atom's key — the same one
    `Assn.declC` takes, and the same reason `assertion-language.md` §6 gives for
    having both spellings. -/
structure RowClaim where
  cls : String
  name : String
  sig : Sig
  why : Provenance
deriving DecidableEq, Repr, Inhabited

/-- The `decl` atom a claim is obliged to appear as in `assumes`. One function so
    that the validator's check and the theorem's read-out cannot drift. -/
def RowClaim.atom (r : RowClaim) : Ty × String × Sig := (nomTy r.cls, r.name, r.sig)

/-! ## 2a. Node addresses and node claims (V9–V11)

**The import above is one line and it is the point of this revision.** It was
`RubyCore.Types.Program`, which reaches `Types/Core.lean` and therefore `infer`; it is
now `RubyCore.Types.Assn`, whose own import closure is `Decls → Ty → Syntax` and
contains **no inference pass at all**. So "the validator does not depend on `infer`"
is not a claim about discipline, it is a fact about the module graph, and
`Cert/Check.lean` could not call `infer` if it wanted to. See V12.

What replaces `infer` on the checked path is `chk` (`Cert/Check.lean`), and it needs
two things the C0 grammar had no room for.

**A way to name a node.** `Path` is the list of child indices from the root,
**innermost first** — the child `i` of the node at `π` is at `i :: π`. Consed rather
than appended because the checker builds it on the way *down*, and a cons is one
allocation where a `++` is a traversal; the price is that a path reads
right-to-left, which is why every emitter must build it the same way (`certify/`
does, E-side).

**A way to state a claim about that node.** §4 D1's stackmap table, generalized:
between claims the checker propagates deterministically, and at a claimed node it
*reads the answer instead of computing it*. One structure with three fields rather
than three sections, because every consumer looks the node up once.

A node claim is **not** covered by `validate_sound`. `claims = []` is a hypothesis of
the bridge (`Proof/Cert/Check.lean`), so a certificate that claims a node buys
coverage and gives up the theorem — which is the same two-tier bargain `deltaRows`
strikes, one level down, and it is reported the same way (`Cert.claimFree`). -/

/-- A node address: child indices from the root, innermost first. -/
abbrev Path := List Nat

/-- What the certificate may say about one node — §4 D1's stackmap entry.

    All three fields are read by `chk` only where the deterministic rule has *no*
    answer, never to override one: a claim cannot make an accept out of a rule that
    fired and refused. That is what keeps a bad claim a lost body rather than a false
    accept, and it is the reason `chk` consults `claimAt` in the `none` branch of each
    match and nowhere else. -/
structure NodeClaim where
  /-- The type this node is claimed to have. -/
  ty : Ty
  /-- The environment the node's continuation is typed at — a join point's
      stackmap (C5). `none` means "the entry environment", which is what every
      deterministic arm passes. -/
  env : Option Env := none
  /-- A list of types the node's rule needs and cannot derive from the program: a
      call site's instantiation of a parameterized callee (C6, D2a), or the declared
      parameter types of a `def` that takes parameters. -/
  tys : Option (List Ty) := none
deriving DecidableEq, Repr, Inhabited

/-! ## 3. The per-body claim

C0 is **signatures-only** (§4 D1): the validator re-propagates between claims, so a
`BodyCert` records the *choice* — which signature this body was typed at — and
nothing about the interior. `joins` (C5) and `insts` (C6) are the fields that make
it a stackmap; they are deliberately absent rather than stubbed, for the reason
`Types/Assn.lean`'s header gives about §6.5's deferred arms: a field no rule reads
is a `DecidableEq` cost and a reader's false expectation. -/

/-- One method body's claimed typing. -/
structure BodyCert where
  owner : String
  name : String
  sig : Sig
deriving DecidableEq, Repr, Inhabited

/-! ## 4. The ledger (C2)

`DischargeStep` is §3's, and it is here rather than in `Cert/Ledger.lean` because it
is *format* — the checker of it is what lives there. The `pinPair` equalities a
cancellation owes are **not** stored: the validator re-derives them, which is what
makes the section a claim about the pairing and not about the arithmetic. -/

/-- One cancellation: at variable `var`, the requirement `required` on `name` is
    answered by the provision `provided`. -/
structure DischargeStep where
  var : TyVar
  name : String
  required : ASig
  provided : ASig
deriving DecidableEq, Repr, Inhabited

/-! ## 5. The certificate -/

/-- §3's `Cert`. Every field defaulted, so the **empty certificate** is a legal
    value and is exactly the self-certification of a program `check` already
    accepts: no table extension, no residue, nothing assumed. That degenerate case
    is C0's round-trip property and the base case of every theorem below. -/
structure Cert where
  version : Nat := RubyCore.Cert.version
  /-- The ground instantiation of every type variable the assertion mentions. -/
  theta : List (TyVar × Ty) := []
  /-- The table extension over `declsOf p`, in the order it is applied. -/
  deltaRows : List RowClaim := []
  /-- Per-body typing claims (C0: signatures-only). -/
  bodies : List BodyCert := []
  /-- Which provision answers which requirement (C2). -/
  ledger : List DischargeStep := []
  /-- Per-node claims, keyed by `Path` — §4 D1's stackmap table (V10). Empty is
      the sound tier: `Cert.claimFree` reports it and the bridge requires it. -/
  claims : List (Path × NodeClaim) := []
  /-- **The checker's fuel, carried by the certificate** (V9).

      `chk` is structurally recursive on this `Nat`, which is what makes the whole
      validator kernel-reducible — `infer`'s well-founded recursion is exactly why
      four of C0's six conjuncts `decide`d and two did not (§9.3), and a fuel
      parameter is the standard fix, already the shape of the model's own interpreter.

      **Carried rather than computed**, and the direction it fails in is the reason:
      too little fuel makes `chk` answer `none`, which *rejects*. So a wrong fuel
      costs a body, never an accept — the same argument `thetaFn`'s `.any` default
      makes. A computed `sizeOf p` would have been the other kind of dependency: a
      derived `Nat` the kernel has to reduce before it can start. -/
  fuel : Nat := 64
  /-- The residue the conclusion is conditional on. `emp` is an unconditional
      accept, and §2 constraint 4 is the reason this is a field rather than prose:
      the verdict-strength ladder is an ordering on residues. -/
  assumes : Assn := .emp
deriving DecidableEq, Repr, Inhabited

namespace Cert

/-- The substitution the certificate determines, as the total function `ATy.subst`
    and `SatStore` are stated over.

    **The default is `.any`, and the direction it fails in is the point.** `sigOf D
    .any n = none` for every `n` (`tyClassNames .any = []`), so a variable the
    certificate forgot to instantiate makes every requirement on it *fail* the
    validator rather than pass it. A defaulted `.int` would have been the other
    direction. -/
def thetaFn (c : Cert) : TyVar → Ty :=
  fun α => match c.theta.find? (·.1 == α) with
    | some (_, τ) => τ
    | none => .any

/-- The claim at a node, if the certificate makes one. A `List.find?` over ground
    data, so it reduces in the kernel like everything else on the checked path. -/
def claimAt (c : Cert) (π : Path) : Option NodeClaim :=
  (c.claims.find? (·.1 == π)).map (·.2)

/-- **Does this certificate claim any node?** The sound tier is `true`: the bridge to
    `infer` (`Proof/Cert/Check.lean`) has `claims = []` as a hypothesis, because a
    claimed node is precisely a place where `chk` answers and `infer` does not.

    Reported beside `Cert.unconditional` for the same reason that one is (V6): a
    verdict whose strength a reader has to reconstruct from a quantifier is not a
    verdict, and the fourth ratchet counts the two populations apart. -/
def claimFree (c : Cert) : Bool := c.claims.isEmpty

/-- The table the certificate names: `declsOf p`, extended left to right.

    `addRow` prepends, so a later claim shadows an earlier one at the same
    `(cls, name)` — which `rowGuards` below is what forbids: every claim is checked
    against the table *it is added to*, and `declaresName` refuses a name already
    present. So the fold is injective on names by construction, which is the fact
    `DeclsOk` needs at each step. -/
def table (c : Cert) (p : Expr) : Decls :=
  c.deltaRows.foldl (fun D r => addRow D r.cls r.name r.sig) (declsOf p)

/-- The prefix of the table after the first `k` claims — the intermediate value the
    soundness induction is stated over. `table` is this at `k = length`. -/
def tableUpTo (c : Cert) (p : Expr) (k : Nat) : Decls :=
  (c.deltaRows.take k).foldl (fun D r => addRow D r.cls r.name r.sig) (declsOf p)

theorem tableUpTo_zero (c : Cert) (p : Expr) : c.tableUpTo p 0 = declsOf p := rfl

theorem table_eq_tableUpTo (c : Cert) (p : Expr) :
    c.table p = c.tableUpTo p c.deltaRows.length := by
  unfold table tableUpTo
  rw [List.take_length]

end Cert

/-! ## 6. The per-claim guards

**One of them is load-bearing and the other two are hygiene** (V3), and which is
which is a fact about `Proof/Static/Decls.lean`'s `DeclsOk_addRow_here` (L266)
rather than a matter of taste. That lemma's obligation for the *new* row is

```
EntryOk (addRow D c name σ) h τ₀ name σ    for every τ₀ with tyClassNames τ₀ = [c]
```

and `tyClassNames_singleton_inv` (L266) says there is at most **one** such `τ₀`,
namely `nomTy c` — which is exactly `RowClaim.atom`'s key. So a single `decl` atom
in `assumes` discharges it, and the only hypothesis the *validator* has to check is

* **`declaresName D r.name = false`** — the freshness `subDecls_addRow` needs, and
  what makes the extension's rows disjoint from every row already present *and*
  from each other. It is name-*global* (`assertion-language.md` §R2), so this is
  the certificate paying the same price `infer`'s `def` rule pays, and it is what
  makes the fold in `Cert.table` shadow-free.

**Note which guards are deliberately *absent*.** L264's promotion carries five:
`cls ≠ "Object"`, `name ≠ "initialize"`, `reopenableClasses.contains cls`,
`groundClassNames.contains cls = false`, `declaresName D name = false`. Only the
last survives here, and the four that do not are all about whether a row can be
**witnessed by a `def` the program contains** — a toplevel or `initialize` method
is private so `ResolvesUser` refuses it; the `reopenable` list is where `ClassOk`'s
uniqueness clause is stated; and `groundClassNames` is `DeclsOk_addRow`'s guard
against a row keyed on the `.cls` arm at a ground name, which `nomTy` never
produces (`nomTy "Integer"` is `.int`, not `.cls "Integer"`).

A certificate row is not witnessed by a `def`. It is witnessed by `assumes`, whose
reader can see it — so the four guards would forbid exactly the rows this
initiative exists to ingest (`Integer#even?` from an RBI, `Comparable`, every
program class) and forbid them for reasons that do not apply. Recorded because it
is the one place C0 is *weaker* in its guards than L264, and because the
replacement — one visible `decl` atom per row — has to be checkable rather than
asserted. -/

/-- May this row be added to this table? -/
def rowGuards (D : Decls) (r : RowClaim) : Bool :=
  declaresName D r.name == false &&
  -- A block-taking row is not something `sigOf` will ever hand to a rule (L242), so
  -- claiming one is claiming a capability no rule can spend. Refused rather than
  -- silently ignored.
  r.sig.blk == none &&
  r.why.honoured

/-- Every claim, against the table it is added to. Structural over the list, so it
    reduces in the kernel — which the whole validator has to (§2 constraint 2). -/
def rowsGuarded (D : Decls) : List RowClaim → Bool
  | [] => true
  | r :: rest => rowGuards D r && rowsGuarded (addRow D r.cls r.name r.sig) rest

/-! ## 7. Checked facts

Kept in the build for `Types/Decls.lean`'s reason: a capability nothing asserts is a
capability nothing notices breaking. -/

/-- The empty certificate names exactly `declsOf p`. -/
example (p : Expr) : ({} : Cert).table p = declsOf p := rfl

/-- …and its substitution is total and useless, which is the safe default. -/
example : ({} : Cert).thetaFn 7 = Ty.any := rfl

/-- A claimed row lands in the table at the class arm. `Integer#/` is the standing
    example throughout this initiative: `srb` accepts `1 / 2`, `check` abstains
    because `/` is absent from `baseDecls`, and the absence is *deliberate* — the
    row is not conformant, since `1 / 0` raises. So it is the case that exercises a
    **residue that cannot be discharged**, which is the honest half of the ladder. -/
example :
    sigOf (({ deltaRows := [{ cls := "Integer", name := "/",
                              sig := { params := [.int], ret := .int },
                              why := .assumed "rbi" }] } : Cert).table (.nil))
      .int "/" = some ([Ty.int], Ty.int) := by
  decide

/-- The guards pass for that row: `/` is fresh in `baseDecls`, the row takes no
    block, and the provenance is honoured. A row on a **ground** class name is
    admitted — see V3 — because `nomTy "Integer"` is `.int`, the type `declFor`
    actually reads such a row at, and not the `.cls "Integer"` arm L189's guard is
    about. -/
example :
    rowsGuarded (declsOf .nil)
      [{ cls := "Integer", name := "/", sig := { params := [.int], ret := .int },
         why := .assumed "rbi" }] = true := by
  decide

/-- And a `.fromDef` claim is refused by the guards, which is V2 as a checked fact
    rather than a comment. -/
example :
    rowsGuarded (declsOf .nil)
      [{ cls := "Integer", name := "/", sig := { params := [.int], ret := .int },
         why := .fromDef 0 }] = false := by
  decide

/-- A row shadowing a name the table already has is refused — the freshness clause,
    which is what makes the fold's rows name-disjoint. -/
example :
    rowsGuarded (declsOf .nil)
      [{ cls := "String", name := "+", sig := { params := [.int], ret := .int },
         why := .assumed "rbi" }] = false := by
  decide

/-- And two claims at the same name are refused by the *second* one seeing the
    first's row — which is the reason `rowsGuarded` threads the table instead of
    checking each claim against `declsOf p`. -/
example :
    rowsGuarded (declsOf .nil)
      [{ cls := "String", name := "shout", sig := { params := [], ret := .int },
         why := .assumed "rbi" },
       { cls := "Symbol", name := "shout", sig := { params := [], ret := .int },
         why := .assumed "rbi" }] = false := by
  decide

end RubyCore.Cert
