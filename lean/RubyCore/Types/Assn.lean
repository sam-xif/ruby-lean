import RubyCore.Types.Decls

/-!
# The assertion language — rows, requirements, obligations

`homebrew/assertion-language.md`, rungs **R1** (the datatype and its printer) and
the Layer-3 half of **R4** (rows and the constraint store). This file is
**Layer 3** in that document's three-layer split:

```
Layer 3   entail / infer : Assn → Assn → Bool     -- executable, decidable, HERE
Layer 2   ⟦·⟧ : Assn → Heap → Prop                -- Proof/Static/Assn.lean
Layer 1   init / cons / safe over stepFn          -- the metatheory, unchanged
```

Nothing here is trusted. Everything here is *decidable*, which is the property
§9.4 gives as the reason an assertion language and not Iris: `entail` is a linear
merge over a sorted normal form, so a checker can be extracted where an entailment
in a proof assistant's logic cannot.

## Three deliberate departures from the document's §6 grammar, each recorded

1. **`Ty` does not gain a `var α` arm.** §6 writes `Ty τ ::= … | var α`. Adding an
   arm to `Ty` re-opens every `match` on it in the metatheory — `TyClass`,
   `tyClassNames`, `valueTy?`, and each of `Static/Mono.lean`'s 42 cases — for a
   constructor no *value* can ever inhabit. Instead `ATy` (below) is `Ty` plus a
   variable, and it appears **only** in the assertion language. The nominal
   fragment of `Assn` therefore mentions exactly today's `Ty`, which is what makes
   §9.1's atoms literally the existing predicates rather than new ones.

2. **`C ▷ n : σ` is keyed by `Ty`, not by a class name.** §6 says it "is today's
   `Decls` entry", and it nearly is — but the artifact the *invariant* quantifies
   over is `declFor D τ n`, which is keyed by a **type**, and `Ty.bool` is two
   classes while `Ty.cls "Integer"` is no classes at all (`Types/Decls.lean`,
   `tyClassNames`). Keying the atom by the class name would make the syntax-to-
   semantics map lossy in exactly the place §9.3 says a skeptical reader looks
   first. `Assn.declC` is the class-name spelling, defined as `nomTy C`'s instance.

3. **The deferred arms of §6.5 (`A * A`, `p.@x ↦ τ`, `C ▷ᵂ n`, `closed α`) are
   absent, not stubbed.** §6.5 asks for them to be *recorded* so a later grammar
   is not incompatible; the record is that document. A constructor with no `⟦·⟧`
   would be new unchecked surface for zero benefit (§1's cost side).
-/

namespace RubyCore.Types

/-! ## 1. Types, extended with a variable

A **row variable**/**type variable** is a `Nat`. One namespace for both, because
§4.1's well-formedness condition ("`ρ` lacks `n₁…n_k`") is maintained by
construction here — a row *is* the map, so there is no second `ρ` to collide with
— and a separate `RowVar` type would buy only a `DecidableEq` that `Nat` already
has. -/
abbrev TyVar := Nat

/-- A type in the assertion language: a nominal type (today's `Ty`, which is what
    `declFor`/`EntryOk`/`ValueTy` are stated over), or an **unresolved receiver**.

    §6's `var α`. It is a separate inductive rather than an arm of `Ty` for the
    reason in this file's header: no runtime value inhabits it, so putting it in
    `Ty` would cost every case analysis in the metatheory and buy nothing. -/
inductive ATy where
  | nom (τ : Ty)
  | var (α : TyVar)
deriving DecidableEq, Repr, Inhabited

/-- The class names the four ground arms of `Ty` denote, inverted: the `Ty` a
    class **name** names.

    `TrueClass`/`FalseClass` deliberately go to `.cls`, not to `.bool`: `.bool` is
    the type of a value that may be *either*, and `declFor` demands the two agree
    (`Types/Decls.lean`), so a name-keyed atom cannot be the two-class type. What
    that costs is that `.cls "TrueClass"` has no declarations at all
    (`tyClassNames` subtracts the ground names), which is the same uselessness
    `Types/Decls.lean` records and the same right failure direction. -/
def nomTy : String → Ty
  | "Integer" => .int
  | "NilClass" => .nilT
  | "Symbol" => .sym
  | c => .cls c

/-- A `Ty`, rendered. Used by the printer, and the partial inverse of `nomTy`. -/
def tyName : Ty → String
  | .int => "Integer"
  | .bool => "Boolean"
  | .nilT => "NilClass"
  | .sym => "Symbol"
  | .cls c => c

def ATy.render : ATy → String
  | .nom τ => tyName τ
  | .var α => s!"α{α}"

/-! ## 2. Signatures and rows -/

/-- A signature is a `MethodDecl` — parameters and a return type — because that
    is the artifact `Decls` already holds and `ConformsAt` is already stated over.
    §6's `Sig σ ::= (τ₁,…,τ_k) → τ` is this, spelled differently. -/
abbrev Sig := MethodDecl

def Sig.render (σ : Sig) : String :=
  "(" ++ String.intercalate ", " (σ.params.map tyName) ++ ") → " ++ tyName σ.ret

/-- **A signature over the extended type language** — the one `require`'s row case
    records. §7.2 writes `β fresh` for the return of a requirement on an
    unresolved receiver, and this is where `β` lives: an `ASig` may mention type
    variables where a `Sig` may not.

    Splitting the two rather than making `Sig` polymorphic is the same decision
    this file's header records about `Ty`: `Sig` is `MethodDecl`, the artifact the
    *table* holds and `ConformsAt` is stated over, and nothing in the metatheory
    should have to case on a constructor no declaration can contain. -/
structure ASig where
  params : List ATy := []
  ret : ATy
deriving DecidableEq, Repr, Inhabited

/-- A substitution, applied. Total, because `θ` is total — §9.1's `⟦var α ~ n : σ⟧
    is `∀ θ, …`, so there is no "unsolved variable" case to handle in the
    semantics; an unsolved variable is a claim about *every* instantiation, which
    is exactly why §7.7 refuses a residual one at toplevel. -/
def ATy.subst (θ : TyVar → Ty) : ATy → Ty
  | .nom τ => τ
  | .var α => θ α

def ASig.subst (θ : TyVar → Ty) (σ : ASig) : Sig :=
  { params := σ.params.map (ATy.subst θ), ret := ATy.subst θ σ.ret }

/-- The embedding of a declared signature. `σ.toA.subst θ = σ` for every `θ`,
    which is the fact that makes the nominal fragment substitution-independent. -/
def Sig.toA (σ : Sig) : ASig := { params := σ.params.map .nom, ret := .nom σ.ret }

/-- A signature with no variables left, if there are none. What `dischargeRow`
    needs in order to compare against the table. -/
def ATy.toNom? : ATy → Option Ty
  | .nom τ => some τ
  | .var _ => none

def ATy.nomList? : List ATy → Option (List Ty)
  | [] => some []
  | a :: rest =>
    match a.toNom?, ATy.nomList? rest with
    | some τ, some ps => some (τ :: ps)
    | _, _ => none

def ASig.toNom? (σ : ASig) : Option Sig :=
  match σ.ret.toNom?, ATy.nomList? σ.params with
  | some r, some ps => some { params := ps, ret := r }
  | _, _ => none

def ASig.render (σ : ASig) : String :=
  "(" ++ String.intercalate ", " (σ.params.map ATy.render) ++ ") → " ++ σ.ret.render

/-- **A row** (§4.1): a finite map from method names to signatures, plus an
    optional tail variable.

    `entries` is kept **sorted strictly ascending by name** (§8.1's normal form),
    which does three jobs at once: it gives `Row` a canonical form, hence a usable
    `DecidableEq`; it makes §4.1's lacks-condition *maintained* rather than
    checked, since a map cannot hold two `n`s; and it makes `entail`'s frame
    inference a linear merge rather than a search (§8.2).

    `tail = none` is the **closed** row `⟨…⟩`; `tail = some ρ` is `⟨… | ρ⟩`. The
    tail is inert in the semantics — `⟦C ⊒ R⟧` discards it (§8.2, "the row's tail
    is discarded here, which is exactly the open/inexact reading and is sound
    because requirements are positive") — and is carried so that the printed form
    says which of the two it is. **Exactness (`closed α`) is §6.5 and deferred**;
    a closed row here is not an exactness claim, it is a row with no named
    remainder. -/
structure Row where
  entries : List (String × ASig) := []
  tail : Option TyVar := none
deriving DecidableEq, Repr, Inhabited

namespace Row

def empty : Row := {}

def get? (R : Row) (n : String) : Option ASig :=
  (R.entries.find? (·.1 == n)).map (·.2)

/-- **Insert, prepend-shadowing** — and the shape is `Types/Decls.lean`'s
    `addRow`, deliberately, for the same reason that file gives: `get?` reads
    `List.find?`, which stops at the first hit, so the only fact any proof needs
    is `List.find?`'s own equation. An insert that placed the entry *in order*
    would need a sortedness invariant carried through every recursion of
    `inferOpen`, and `Proof/Static/OpenSelf.lean`'s monotonicity lemma —
    §7.5's, the one R4 owes — would be a list-permutation argument rather than
    two lines.

    Returns `none` when `n` is already present at a **different** signature, which
    is `require`'s ★★ (§7.2): the deliberately weak first cut refuses where an
    intersection type belongs, and §13.2 says to measure how often that happens
    before fixing it. Re-inserting the *same* signature is idempotent, which is
    what makes a row a set of persistent facts (§2: capability facts are
    duplicable).

    §8.1's normal form is therefore a property of `normalize`, not of the
    representation. `wf` states it and `render` establishes it, which is where it
    is actually needed: a canonical form is for *comparing and printing* rows, and
    neither `insert` nor `get?` cares. -/
def insert (R : Row) (n : String) (σ : ASig) : Option Row :=
  match R.get? n with
  | some τ => if σ == τ then some R else none
  | none => some { R with entries := (n, σ) :: R.entries }

/-- Sorted by name — §8.1's normal form, as an operation. -/
def normalize (R : Row) : Row :=
  { R with entries := R.entries.mergeSort (fun a b => decide (a.1 ≤ b.1)) }

/-- The normal-form check (§8.1): strictly ascending, hence duplicate-free. -/
def wf (R : Row) : Bool := go R.entries
where
  go : List (String × ASig) → Bool
    | [] => true
    | [_] => true
    | (a, _) :: (b, σ) :: rest => a < b && go ((b, σ) :: rest)

def render (R : Row) : String :=
  let body := String.intercalate ", "
    (R.normalize.entries.map fun e => e.1 ++ " : " ++ e.2.render)
  match R.tail with
  | none => "⟨ " ++ body ++ " ⟩"
  | some ρ => "⟨ " ++ body ++ (if R.entries.isEmpty then "" else " ") ++ s!"| ρ{ρ} ⟩"

end Row

/-! ## 3. The assertion -/

/-- §6's `Assn`, less the four deferred arms of §6.5.

    * `decl τ n σ` is `C ▷ n : σ` at `τ = nomTy C` — **a declaration**, the thing
      `Decls` holds and `DeclsOk` quantifies over.
    * `req τ n σ` is `τ ~ n : σ` — **a requirement**, and `τ : ATy`, so this is
      the one arm that can mention an unresolved receiver.
    * `obl c R` is `C ⊒ R` — **an obligation**: class `c` must satisfy row `R`.

    A `decl` is what the checker *has*; a `req`/`obl` is what it *needs*. That
    split is the whole of §11: `unknown` prints the requirements it could not
    discharge against the declarations it had. -/
inductive Assn where
  | emp
  | and (A B : Assn)
  | decl (τ : Ty) (n : String) (σ : Sig)
  | req (τ : ATy) (n : String) (σ : ASig)
  | obl (c : String) (R : Row)
deriving DecidableEq, Repr, Inhabited

namespace Assn

/-- `C ▷ n : σ` spelled with a class name (§6). -/
def declC (c n : String) (σ : Sig) : Assn := .decl (nomTy c) n σ

/-- Conjoin a list. `∧` and not `*`: §2 — a capability fact is *knowledge*, it is
    duplicable, and for a duplicable `P`, `P * Q ⊣⊢ P ∧ Q`. The separating
    conjunction is §6.5 and is deferred until the ivar measurement (§12 R6). -/
def all : List Assn → Assn
  | [] => .emp
  | [A] => A
  | A :: rest => .and A (all rest)

/-- **The declaration atoms an assertion asserts.** Layer 3's whole content is
    this list and the two below: `entail` compares them, and `Proof/Static/Assn.lean`
    proves `⟦A⟧` is exactly the conjunction of their denotations. -/
def declAtoms : Assn → List (Ty × String × Sig)
  | .emp => []
  | .and A B => declAtoms A ++ declAtoms B
  | .decl τ n σ => [(τ, n, σ)]
  | .req _ _ _ => []
  | .obl _ _ => []

/-- The requirements — what the checker could not discharge locally. -/
def reqAtoms : Assn → List (ATy × String × ASig)
  | .emp => []
  | .and A B => reqAtoms A ++ reqAtoms B
  | .decl _ _ _ => []
  | .req τ n σ => [(τ, n, σ)]
  | .obl _ _ => []

/-- The class obligations. -/
def oblAtoms : Assn → List (String × Row)
  | .emp => []
  | .and A B => oblAtoms A ++ oblAtoms B
  | .decl _ _ _ => []
  | .req _ _ _ => []
  | .obl c R => [(c, R)]

def render : Assn → String
  | .emp => "emp"
  | .and A B => render A ++ " ∧ " ++ render B
  | .decl τ n σ => tyName τ ++ " ▷ " ++ n ++ " : " ++ σ.render
  | .req τ n σ => τ.render ++ " ~ " ++ n ++ " : " ++ σ.render
  | .obl c R => c ++ " ⊒ " ++ R.render

end Assn

/-! ## 4. The declarations, as an assertion

§6: *"the declaration fragment of `Assn` is a **re-notation** of an artifact that
exists."* This is the re-notation, and `Proof/Static/Assn.lean`'s
`denote_declAssn` is the proof that it is faithful — which is the one thing §9.3
says nothing checks, checked.

The enumeration has to be **complete for `declFor`**, not for the table's rows,
because `DeclsOk` quantifies over `declFor`. Three facts make the list below
exactly right, and each is a clause of `tyClassNames`:

* the four ground arms are keyed at *their* class names, not at `.cls` of them;
* `.cls c` is empty when `c` is a ground name, so no `.cls` atom duplicates a
  ground one;
* every other `.cls c` with a declaration has `c` among the table's keys, since
  `declOf?` reads `declsFor`, which reads `D.find?`.
-/

/-- Every method name any class in `tyClassNames τ` mentions. A superset of the
    names `declFor D τ` answers `some` at, which is all completeness needs. -/
def declNames (D : Decls) (τ : Ty) : List String :=
  (tyClassNames τ).flatMap fun c => (declsFor D c).map (·.1)

/-- The types `declFor D` can answer `some` at: the four ground arms, and the
    class arm at each key of the table. -/
def declTys (D : Decls) : List Ty :=
  Ty.int :: Ty.bool :: Ty.nilT :: Ty.sym :: D.rows.map (fun cd => Ty.cls cd.1)

/-- **The graph of `declFor D`, as a list.** `Proof/Static/Assn.lean` proves
    `(τ,n,d) ∈ declAtoms D ↔ declFor D τ n = some d`, and that biconditional is
    what makes `declAssn` faithful in both directions. -/
def declAtoms (D : Decls) : List (Ty × String × Sig) :=
  (declTys D).flatMap fun τ =>
    (declNames D τ).filterMap fun n => (declFor D τ n).map fun d => (τ, n, d)

/-- The table, as an assertion. -/
def declAssn (D : Decls) : Assn :=
  Assn.all ((declAtoms D).map fun a => .decl a.1 a.2.1 a.2.2)

/-! ## 5. Discharge (§7.6) and entailment (§8.2)

Two independent decidable jobs, exactly as §8.2 splits them.
-/

/-- §7.6 `discharge-nominal`: one `declOf?` lookup. `subsume` is **stated and not
    taken** in the first cut (§7.6, ★ in §7.2), because `Sub` is equality today —
    so this is an equality test and not a subtyping one. -/
def dischargeNom (D : Decls) (τ : Ty) (n : String) (σ : Sig) : Bool :=
  declFor D τ n == some σ

/-- §8.2's `D ⊨ R at C`. **The tail is discarded**, which is the open/inexact
    reading and is sound because requirements are positive facts. -/
def dischargeRow (D : Decls) (c : String) (R : Row) : Bool :=
  R.entries.all fun e =>
    match e.2.toNom? with
    | some σ => dischargeNom D (nomTy c) e.1 σ
    | none => false

/-- **The whole verdict condition of §7.7**, on one assertion: every nominal
    requirement is discharged, every class obligation is discharged, and no
    requirement is left on a type *variable* (§7.7's "`Σ` has no free type
    variable at toplevel"). -/
def dischargeAll (D : Decls) (A : Assn) : Bool :=
  (A.reqAtoms.all fun r =>
      match r.1, r.2.2.toNom? with
      | .nom τ, some σ => dischargeNom D τ r.2.1 σ
      | _, _ => false) &&
    A.oblAtoms.all fun o => dischargeRow D o.1 o.2

/-- **Entailment** (§8.2): `entail A B` iff every atom of `B` is available from
    `A`. Declarations are matched syntactically; requirements and obligations are
    matched against `A`'s declarations, which is `discharge` again — an assertion
    entails a requirement exactly when it *declares* what the requirement asks
    for.

    The **frame is the leftover** (§8.2): whatever atoms of `A` go unused. On a
    sorted normal form that is a linear merge, and `frameOf` below computes it. -/
def entailAtom (A : Assn) (τ : Ty) (n : String) (σ : Sig) : Bool :=
  A.declAtoms.contains (τ, n, σ)

def entail (A B : Assn) : Bool :=
  (B.declAtoms.all fun a => entailAtom A a.1 a.2.1 a.2.2) &&
    (B.reqAtoms.all fun r =>
        match r.1, r.2.2.toNom? with
        | .nom τ, some σ => entailAtom A τ r.2.1 σ
        | _, _ => false) &&
    (B.oblAtoms.all fun o =>
        o.2.entries.all fun e =>
          match e.2.toNom? with
          | some σ => entailAtom A (nomTy o.1) e.1 σ
          | none => false)

/-! ### R2, stated — class-relative `declares`

§12's R2 and `HANDOFF.md` §constraint 2. `declaresName` (`Types/Decls.lean`) is **name-global**:
a `def` of a name the table mentions on *any* class is refused, so once each admitted `def` adds
a row (L163) a second `def` of the same name anywhere in the program is `unknown`. On the slice
that is `to_s` on eight `Token` classes, `hash` on four, `<=>` on thirteen.

`declaresIn` is the class-relative form. **It is the statement, not the rung** — §13.5 says so in
as many words: *"Rows do not discharge the `declaresName` obligation; they make it statable."*
What is still owed is heap-side and unchanged: `DeclsOk_defineMethod` takes name-globality from
`ResolvesAt_defineMethod`'s `mname ≠ name` over an **arbitrary** dispatch class, so the
class-relative version has to say *the defining class is not among `k`'s ancestors* — an
ancestors-relative, hence heap-dependent, argument, on the wrong side of the
`ResolvesAt`/`ConformsAt` line.

`infer` still reads `declaresName`, deliberately: swapping it is a rule change, and a rule change
is `HANDOFF.md` constraint 4's atomic unit. What the definition below buys today is that the
*obligation* can be written per `(class, name)` — which is exactly what `Assn.obl`/`dischargeRow`
already are, and why two classes each defining `to_s` do not collide in an assertion. -/
def declaresIn (D : Decls) (c name : String) : Bool :=
  (declOf? D c name).isSome

/-- The free half of the relation between the two, and the only half that is free:
    a name **no** class declares is declared on no *particular* class either. The
    converse is what `infer`'s guard would need and is what the heap-side argument
    above is about. -/
theorem declaresIn_of_declaresName {D : Decls} {c name : String}
    (h : declaresName D name = false) : declaresIn D c name = false := by
  unfold declaresIn declaresName at *
  cases hd : declOf? D c name with
  | none => simp [hd]
  | some _ =>
    exfalso
    unfold declOf? declsFor at hd
    cases hf : D.rows.find? (·.1 == c) with
    | none => rw [hf] at hd; simp at hd
    | some cd =>
      rw [hf] at hd
      dsimp only at hd
      cases he : cd.2.find? (·.1 == name) with
      | none => rw [he] at hd; simp at hd
      | some e =>
        have hmem : cd ∈ D.rows := List.mem_of_find?_eq_some hf
        have hme : e ∈ cd.2 := List.mem_of_find?_eq_some he
        have hn : (e.1 == name) = true := by
          have := List.find?_some he; simpa using this
        have : D.rows.any (fun cd => cd.2.any fun md => md.1 == name) = true := by
          refine List.any_eq_true.mpr ⟨cd, hmem, ?_⟩
          exact List.any_eq_true.mpr ⟨e, hme, hn⟩
        rw [this] at h
        exact absurd h (by simp)

/-- Frame inference (§8.2): the atoms of `A` that `B` did not consume. Not used
    by any verdict — it is what a certificate would carry (§8.4) and what §11
    prints as *had*. -/
def frameOf (A B : Assn) : List (Ty × String × Sig) :=
  A.declAtoms.filter fun a => !(B.declAtoms.contains a)

/-! ## 6. The constraint store (§8.1)

`Σ` in the judgement `D ; Γ ; Σ ; κ ⊢ e : τ ⊣ Γ' ; D' ; Σ'`. Threaded exactly as
`D` is (§7), and for the same reason L160 gives: `initiation` is owed at the boot
heap, so a constraint discovered by the program's own text cannot live in a store
fixed up front.
-/

/-- §8.1's normal form. `rows` is the map from a type variable to what has been
    required of it; `nom` the nominal requirements; `obl` the class obligations. -/
structure Store where
  rows : List (TyVar × Row) := []
  nom : List (Ty × String × Sig) := []
  obl : List (String × Row) := []
deriving DecidableEq, Repr, Inhabited

namespace Store

def empty : Store := {}

def rowOf (st : Store) (α : TyVar) : Row :=
  match st.rows.find? (·.1 == α) with
  | some (_, R) => R
  | none => Row.empty

/-- Replace `α`'s row. Prepending shadows, exactly as `addRow` does for `Decls`
    and for the same reason (`Types/Decls.lean`): `find?` stops at the first hit,
    so the only fact anything needs is `List.find?`'s own equation. -/
def setRow (st : Store) (α : TyVar) (R : Row) : Store :=
  { st with rows := (α, R) :: st.rows }

/-- `Σ ∖ α` (§7.3): discharge `α`'s row into a class obligation and drop the
    variable. This is the step that turns *the residual row on self* into
    `c ⊒ R`, and it is the whole content of the `def` rule's conclusion. -/
def closeAt (st : Store) (α : TyVar) (c : String) : Store :=
  let R := st.rowOf α
  { rows := st.rows.filter (·.1 != α),
    nom := st.nom,
    obl := if R.entries.isEmpty then st.obl else (c, R) :: st.obl }

def addNom (st : Store) (τ : Ty) (n : String) (σ : Sig) : Store :=
  if st.nom.contains (τ, n, σ) then st else { st with nom := (τ, n, σ) :: st.nom }

/-- Merge one row into another, entry by entry. `none` is ★★ (§7.2): the same
    name required at two different signatures is refused rather than intersected. -/
def mergeRow (acc : Row) : List (String × ASig) → Option Row
  | [] => some acc
  | e :: rest => match acc.insert e.1 e.2 with
    | some acc' => mergeRow acc' rest
    | none => none

/-- `Σ₁ ⊎ Σ₂` (§7.5): a **union**, not a merge with a side condition, because the
    store only ever grows — requirements are positive facts. Rows at a shared
    variable are merged entry-by-entry and the merge can *fail*, which is ★★
    again (§7.2). -/
def unionRows (base : List (TyVar × Row)) : List (TyVar × Row) → Option (List (TyVar × Row))
  | [] => some base
  | (α, R) :: rest =>
    let cur : Row := match base.find? (·.1 == α) with
      | some (_, R') => R'
      | none => Row.empty
    match mergeRow cur R.entries with
    | none => none
    | some acc =>
      unionRows ((α, { acc with tail := R.tail.orElse fun _ => cur.tail })
                  :: base.filter (·.1 != α)) rest

def union (st₁ st₂ : Store) : Option Store :=
  match unionRows st₁.rows st₂.rows with
  | none => none
  | some rows =>
    some { rows := rows,
           nom := st₁.nom ++ st₂.nom.filter (fun r => !(st₁.nom.contains r)),
           obl := st₁.obl ++ st₂.obl.filter (fun o => !(st₁.obl.contains o)) }

/-- The store, as an assertion — which is how a store becomes something with a
    `⟦·⟧`, and therefore how R4's output becomes R1's output. -/
def toAssn (st : Store) : Assn :=
  Assn.all <|
    (st.rows.flatMap fun r => r.2.entries.map fun e => Assn.req (.var r.1) e.1 e.2) ++
    (st.nom.map fun r => Assn.req (.nom r.1) r.2.1 r.2.2.toA) ++
    (st.obl.map fun o => Assn.obl o.1 o.2)

def render (st : Store) : String := st.toAssn.render

end Store

/-! ## 7. `require` (§7.2)

*"`require` is the whole design in one function."* Three clauses in the document;
**one of them is new code and the other two already exist**, which is worth
saying plainly rather than wrapping them.

* The **nominal** clause — `require(D, Σ, cls C, n, τ⃗)` — is `sigOf D τ n`
  followed by `params = τ⃗`. That is *literally* what `infer`'s send arms already
  do (`Types/Core.lean`), and what `inferOpen`'s nominal arms do. A wrapper
  around it would be a rename, and it would be a rename on one side only: the
  factoring theorem (`Proof/Static/OpenSelf.lean`) is an arm-by-arm match between
  the two functions, and an arm that differs for no reason is an arm whose proof
  case has to be invented.
* The **ground** clause is the nominal one at a ground class, which is `sigOf`
  again — `tyClassNames` is what makes `.int` and `"Integer"` the same key.
* The **row** clause is `requireRow`, below, and it is the only thing R4 adds.
-/

/-- §7.2's second clause: a send whose receiver's type is still a variable
    **records** the requirement instead of checking it, which is what types a body
    against an unresolved receiver (§4.3).

    Two departures from the document's pseudocode, and both are simplifications
    the normal form of §8.1 makes available:

    * **`β fresh` is allocated only when the row has no entry for `n`.** §7.2
      writes it unconditionally and then compares; comparing a *fresh* variable
      against a stored signature would refuse the second call to a method the row
      already knows about, which is not what ★★ is for. When an entry exists this
      returns the stored return type, whatever it is.
    * **The arity test is the only test.** ★★ — the refusal where an intersection
      type belongs — is `Row.insert`'s, not this function's, and it fires only on
      a genuine disagreement about the same name.

    `fresh` is the caller's counter; `Types/OpenSelf.lean` threads it in `OState`
    and is the only consumer. -/
def requireRow (st : Store) (α : TyVar) (n : String) (args : List ATy) (fresh : TyVar) :
    Option (ATy × Store) :=
  match (st.rowOf α).get? n with
  | some σ => if σ.params == args then some (σ.ret, st) else none
  | none =>
    match (st.rowOf α).insert n { params := args, ret := .var fresh } with
    | some R' => some (.var fresh, st.setRow α R')
    | none => none

/-! ## 8. §11 — explainability, which is the cheapest benefit

*"`unknown` today carries no information."* This is the report that fixes it, and
it is an **output of the checker rather than a duplicate of it**, which retires
`fragment-gap.py`'s drift risk (`SUPPORTED` has been wrong twice) in the same
change.
-/

/-- What the checker concluded about one method body, in the form §11 prints. -/
inductive BodyVerdict where
  /-- The body types, **under** this precondition on its own class (§7.3's
      `R = Σ'(α)`), plus whatever the store still requires of *other* variables —
      §4.3's nested rows, which belong to no class name yet. An empty `need` and
      an `emp` `rest` is an unconditional accept.

      `ret` is an `ATy` and not a `Ty` on purpose: a body whose return type is
      still a variable is **not** a failure, it is a body whose type is
      determined by its precondition. `def get; value; end` has type `α₁` under
      `C ⊒ ⟨value : () → α₁⟩`, which is exactly as much as can be known before
      `value` is declared — and printing it is the per-method-body gradient §1's
      ledger asks for. -/
  | acceptedUnder (ret : ATy) (need : Row) (rest : Assn)
  /-- **The body types with its parameters open** (L168). Identical to
      `acceptedUnder` except that the body was checked in a *non-empty*
      environment: each required positional parameter is bound to a fresh type
      variable, listed in `params`, and the store's requirements on those
      variables are the parameters' preconditions.

      Kept a separate constructor rather than folded into `acceptedUnder`, and the
      reason is the honesty the census exists for. `acceptedUnder` factors through
      a nominal `infer` run **at the empty environment**, which is the environment
      `infer`'s own `def` rule checks a zero-parameter body in — so its accept is
      one substitution away from the nominal judgement `check` uses. This one
      factors through `infer` at `substEnv θ Γ_b` (`inferBodyWith_sound`), which
      is a nominal judgement about the *body* and not about any `def` rule that
      exists: `infer`'s `def` arm still requires `params.isEmpty`. So a body
      reported here is a body whose typing is settled and whose **declaration** is
      not, and a census that merged the two would read as an accept-rate the
      checker does not have. -/
  | acceptedOpenParams (ret : ATy) (need : Row) (rest : Assn)
      (params : List (String × ATy))
  /-- The body does not type, and here is the atom that stopped it. -/
  | blocked (τ : ATy) (n : String) (params : List ATy)
  /-- Outside `infer`'s domain — the construct census's `unknown`. -/
  | outOfFragment (head : String)
deriving Repr

/-- §11's three lines: what was needed, what was had, what is missing. -/
def explain (D : Decls) (c : String) (v : BodyVerdict) : String :=
  match v with
  | .acceptedUnder ret need rest =>
    let base := s!"accept : {ret.render}"
    let r1 := if need.entries.isEmpty then base
              else base ++ s!"\n  requires: {c} ⊒ {need.render}"
    match rest with
    | .emp => r1
    | _ => r1 ++ s!"\n  and:      {rest.render}"
  | .acceptedOpenParams ret need rest ps =>
    let pl := String.intercalate ", " (ps.map fun e => e.1 ++ " : " ++ e.2.render)
    let base := s!"accept : {ret.render}\n  params:   ({pl})"
    let r1 := if need.entries.isEmpty then base
              else base ++ s!"\n  requires: {c} ⊒ {need.render}"
    match rest with
    | .emp => r1
    | _ => r1 ++ s!"\n  and:      {rest.render}"
  | .blocked τ n ps =>
    let had := Row.mk ((declsFor D c).map fun e => (e.1, Sig.toA e.2)) none
    let missing := s!"{c} ▷ {n}"
    s!"unknown\n  needed:  {τ.render} ~ {n} : ({String.intercalate ", " (ps.map ATy.render)}) → _" ++
      s!"\n  had:     {c} ⊒ {had.render}" ++
      s!"\n  missing: {missing}"
  | .outOfFragment head => s!"unknown\n  out of fragment: {head}"

/-- The name of an expression's head, for §11's `out of fragment:` line. A
    census's whole value is in *which* construct blocked, so an `outOfFragment`
    that says only `"other"` is the same silence `unknown` already was. -/
def headName : Expr → String
  | .int _ => "int" | .flt _ => "float" | .str _ => "str" | .sym _ => "sym"
  | .tru => "true" | .fls => "false" | .nil => "nil" | .self' => "self"
  | .var k _ => match k with
    | .lvar => "lvar" | .ivar => "ivar" | .gvar => "gvar" | .cvar => "cvar"
  | .vasgn k _ _ => match k with
    | .lvar => "lasgn" | .ivar => "iasgn" | .gvar => "gasgn" | .cvar => "casgn"
  | .const _ => "const" | .casgn _ _ => "casgn" | .cpath _ _ => "cpath"
  | .cpathAsgn _ _ _ => "cpathAsgn"
  | .send _ _ args blk =>
    if blk.isSome then "send-with-block"
    else s!"send-{args.length}-args"
  | .vcall _ => "vcall" | .kwargs _ => "kwargs" | .fwd => "fwd"
  | .block _ _ _ => "block" | .yield' _ => "yield" | .blockpass _ => "blockpass"
  | .if' _ _ _ => "if" | .while' _ _ => "while" | .dowhile _ _ => "dowhile"
  | .for' _ _ _ => "for" | .def' _ _ _ => "def" | .array _ => "array"
  | .hash _ => "hash" | .splat _ => "splat" | .ret _ => "return"
  | .brk _ => "break" | .nxt _ => "next" | .retry' => "retry" | .redo' => "redo"
  | .class' _ _ _ => "class" | .module' _ _ => "module"
  | .scopedClass _ _ _ => "scopedClass" | .scopedModule _ _ _ => "scopedModule"
  | .sclass _ _ => "sclass" | .defs _ _ _ _ => "defs"
  | .begin' _ _ _ _ => "begin" | .super' _ _ => "super" | .zsuper _ => "zsuper"
  | .undef _ => "undef" | .seq _ => "seq"
  | _ => "other"

/-! ## 9. Checked facts

Kept in the build rather than as comments, for the reason `Types/Decls.lean`
keeps its own: a capability nothing asserts is a capability nothing notices
breaking.
-/

/-- The base table's three `Integer` rows, recovered as declaration atoms. -/
example : (Ty.int, "+", ({ params := [Ty.int], ret := Ty.int } : Sig)) ∈ declAtoms baseDecls := by
  decide

/-- The nullary row too, so the enumeration is not accidentally arity-specific. -/
example : (Ty.int, "zero?", ({ params := [], ret := Ty.bool } : Sig)) ∈ declAtoms baseDecls := by
  decide

/-- Nothing is declared on the two-class type, and the enumeration agrees with
    `declFor` about that rather than about the table's keys. -/
example : (declAtoms baseDecls).all (fun a => a.1 != Ty.bool) = true := by decide

/-- §4.3's worked example, as a row: the precondition `def hash = value.hash`
    puts on its own class, with no declaration for `Version#value` anywhere. -/
def egVersionRow : Row :=
  { entries := [("value", { params := [], ret := .nom (.cls "Version") })], tail := some 1 }

/-- The row is well-formed in §8.1's sense, which is what `render` normalizes to.
    (The rendered *string* is not asserted here: `List.mergeSort` does not reduce
    in the kernel, and a `native_decide` for a printer would put `ofReduceBool` in
    the build for a cosmetic fact — L94's rule, applied where it is cheapest to
    obey.) -/
example : egVersionRow.wf = true := by decide

/-- The row is in normal form, which `insert` is what maintains. -/
example : (Row.empty.insert "value" { params := [], ret := .nom .int }).isSome := by decide

/-- ★★ (§7.2): a second, *different* signature for the same name is refused
    rather than intersected. §13.2 records this as a known refusal. -/
example :
    ((Row.empty.insert "n" { params := [], ret := .nom .int }).bind
      (·.insert "n" { params := [], ret := .nom .bool })) = none := by decide

/-- …and the *same* signature twice is idempotent, because a capability fact is
    duplicable (§2). -/
example :
    ((Row.empty.insert "n" { params := [], ret := .nom .int }).bind
      (·.insert "n" { params := [], ret := .nom .int }))
      = (Row.empty.insert "n" { params := [], ret := .nom .int }) := by decide

/-- Discharge, against the base table. -/
example : dischargeNom baseDecls .int "+" { params := [.int], ret := .int } = true := by decide
example : dischargeNom baseDecls .int "/" { params := [.int], ret := .int } = false := by decide

/-- An obligation discharged at a class name — the `classBody` rule's premise. -/
example :
    dischargeRow baseDecls "Integer"
      { entries := [("zero?", { params := [], ret := .nom .bool })] } = true := by decide

/-- Entailment is reflexive on the declaration fragment, which is the sanity
    check `entail_sound` alone would not catch (a `false`-always `entail` is
    sound). -/
example : entail (declAssn baseDecls) (declAssn baseDecls) = true := by decide

end RubyCore.Types
