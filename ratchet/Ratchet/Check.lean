import Ratchet.Deriv

/-!
# `Ratchet/Check.lean` — the certificate checker, and the judgment it decides

Layers 1–3 of `../docs/semantics/answer-typed-schema.md` §3, built **standalone**. Nothing
here imports `Ratchet/Judge.lean` or `Ratchet/Validate.lean`, and that is deliberate: the
old `chk` is an *inference* algorithm over an 83-rule inductive of which 35 rules have no
semantic justification and 7 are known false as stated. Growing that is the thing the clink
discipline (`Denote/Clink/`) exists to stop. So the typed ladder gets its own judgment,
authored one rule at a time, and this file is the whole of it.

What is reused is **type-level only** — `Ratchet/Ty.lean`'s `Ty`, `Env`, `envGet?`, `envSet`,
`joinT`, `joinEnv` — and `Ratchet/Expr.lean`'s syntax. Neither mentions a judgment.

## The three layers, and which one is trusted

| layer | here | note |
|---|---|---|
| 1 | `Deriv` (`Ratchet/Deriv.lean`) | what the untrusted emitter writes |
| 2 | `check` | decides whether a certificate is a derivation *of this program*, **and types it** |
| 3 | `check_sound` | `check … = some … → DJudge …`, by induction on the fuel |

`check` **re-derives every type a certificate claims** and compares. A `Deriv.prim` carries
`recvTy` and `retTy`; `check` computes both from the sub-derivation and the primitive table
and rejects a mismatch. That is why a wrong certificate cannot produce a wrong accept, and it
is the property `Ratchet/DerivControls.lean` §4 pins.

## Why fuel

`check` recurses on a `Nat` rather than structurally on `Deriv`, for the reason `chk` did: a
`partial def` cannot be reasoned about, and `Deriv` is a nested inductive (`List Deriv`
fields) whose structural recursion Lean will accept but whose *induction* in a mutual block
with two list companions is a fight. Fuel makes `check_sound` one `induction fuel`. Fuel
exhaustion answers `none`, so it can only cost completeness.

## What is deliberately not in the judgment yet

`DJudge` has thirteen rules. Everything else a `Deriv` can express — `defDecl`, `callSig`,
`callMethodSig`, `classDecl`, `newInst`, `ivarRead`, `ivarAsgn`, `constCls`, `arrayLit`,
`hashLit`, `selfExpr` — answers `none`, by name, in `check`'s last arms. They join a rule at
a time, and each one joining is a rung.

Also not here, and *not* an oversight: `DJudge` carries no `Ctx` and no ivar spine. The
fragment it covers declares nothing, has no `self`, and opens no class, so a context would be
a field nothing reads. `Ratchet/Judge.lean`'s `Ctx` is where the declaration machinery lives
and it is the wrong thing to copy in ahead of a rule that needs it.
-/

set_option autoImplicit false

namespace Ratchet

/-! ## §1 The primitive table

The rules for sends this fragment can type, as an inductive (`DPrim`) with a decision
procedure (`dprim?`) and a soundness lemma between them. Seven rows.

**Seven, not ninety.** `Judge.lean`'s `PrimSig` has ~90 rows and `Denote/`'s
`Sem.Judge.prim` — the obligation that every one of them is true of CRuby — is one of the 35
rules with no proof, priced at "~200 conformance facts, two per row"
(`implementation-notes.md`, EMERGENCY EXIT). A table that grows a row at a time is a table
whose semantic obligation can grow a row at a time too, which is the whole argument for
starting again here rather than inheriting.

Each row is a claim about CRuby that is **not yet proved from the semantics** — see
§Semantic status at the bottom of this file for exactly what is and is not owed. -/

inductive DPrim : Ty → String → List Ty → Ty → Prop
  /-- `Integer#+`, `-`, `*`, `/` at an `Integer` argument. `/` included: integer division by
      zero raises `ZeroDivisionError`, which is outside the
      `NoMethodError`/`ArgumentError`/`TypeError` family this ladder is about, so the row is
      about types and not about totality. -/
  | intAdd : DPrim .int "+" [.int] .int
  | intSub : DPrim .int "-" [.int] .int
  | intMul : DPrim .int "*" [.int] .int
  | intDiv : DPrim .int "/" [.int] .int
  /-- `Integer#<`. The other three comparisons are absent until a rung needs one. -/
  | intLt : DPrim .int "<" [.int] .bool
  /-- `String#+` at a `String` argument — a `TypeError` at any other, which is why the
      argument type is pinned rather than free. -/
  | strAdd : DPrim (.cls "String") "+" [.cls "String"] (.cls "String")
  /-- `!` on a boolean. Ruby's `!` is defined on every object, but this row is the only one
      the fragment can justify: on an arbitrary receiver the result is still `Boolean`, and
      claiming that needs to know the program has not redefined `!` — the `nameFree`-shaped
      premise this judgment has no context to state. So: booleans only, and the restriction
      is recorded rather than assumed away. -/
  | notBool : DPrim .bool "!" [] .bool

/-- The decidable counterpart. A miss is `none`, never a guess. -/
def dprim? : Ty → String → List Ty → Option Ty
  | .int, "+", [.int] => some .int
  | .int, "-", [.int] => some .int
  | .int, "*", [.int] => some .int
  | .int, "/", [.int] => some .int
  | .int, "<", [.int] => some .bool
  | .cls "String", "+", [.cls "String"] => some (.cls "String")
  | .bool, "!", [] => some .bool
  | _, _, _ => none

theorem dprim?_sound {σ : Ty} {m : String} {as : List Ty} {τ : Ty}
    (h : dprim? σ m as = some τ) : DPrim σ m as τ := by
  unfold dprim? at h
  split at h
  · rw [Option.some.injEq] at h; subst h; exact .intAdd
  · rw [Option.some.injEq] at h; subst h; exact .intSub
  · rw [Option.some.injEq] at h; subst h; exact .intMul
  · rw [Option.some.injEq] at h; subst h; exact .intDiv
  · rw [Option.some.injEq] at h; subst h; exact .intLt
  · rw [Option.some.injEq] at h; subst h; exact .strAdd
  · rw [Option.some.injEq] at h; subst h; exact .notBool
  · exact absurd h (by simp)

/-! ## §2 The judgment

`DJudge Γ e τ Γ'`: in local environment `Γ`, the expression `e` has type `τ` and leaves `Γ'`.
Two companions, for the two places a rule needs a list: a send's arguments (`DJudgeAll`,
which also reports their types) and a statement sequence (`DJudgeSeq`).

Every rule is one line and says one thing. That is the property worth protecting: the old
judgment's rules acquired premises over time (`nameFree`, `ctxKept`, `capStaleCtx`,
`primDispatchOk`) because each was found to be *needed* by a semantic obligation or a
soundness bug, and the reason they could accumulate unnoticed is that nothing forced a rule
and its justification to arrive together. -/

mutual
inductive DJudge : Env → Expr → Ty → Env → Prop
  /-- An integer literal, negative ones included: `-5` desugars to `int (-5)`, not to a
      unary send. -/
  | intLit {Γ : Env} {n : Int} : DJudge Γ (.int n) .int Γ
  /-- A float literal, carried as IEEE-754 bits by the syntax layer. -/
  | fltLit {Γ : Env} {b : UInt64} : DJudge Γ (.flt b) .float Γ
  /-- A string literal is an *instance* of `String`; `Ty` has no string arm. -/
  | strLit {Γ : Env} {s : String} : DJudge Γ (.str s) (.cls "String") Γ
  | symLit {Γ : Env} {s : String} : DJudge Γ (.sym s) .sym Γ
  | truLit {Γ : Env} : DJudge Γ .tru .bool Γ
  | flsLit {Γ : Env} : DJudge Γ .fls .bool Γ
  | nilLit {Γ : Env} : DJudge Γ .nil .nilT Γ
  /-- Reading a local. The type comes from the environment, so there is nothing for a
      certificate to choose and `Deriv.var` carries only the name. -/
  | var {Γ : Env} {x : String} {τ : Ty} :
      envGet? Γ x = some τ → DJudge Γ (.var .lvar x) τ Γ
  /-- Assignment. Its *value* is the right-hand side's (Ruby's `x = e` evaluates to `e`) and
      its *effect* is to record that type for `x`. The binding lands in `Γ₁` — the
      environment the right-hand side left behind — not in `Γ`, because the right-hand side
      may itself assign (`y = (x = 1) + 1`). -/
  | vasgn {Γ Γ₁ : Env} {x : String} {e : Expr} {τ : Ty} :
      DJudge Γ e τ Γ₁ → DJudge Γ (.vasgn .lvar x e) τ (envSet Γ₁ x τ)
  /-- A statement sequence, via `DJudgeSeq`. -/
  | seq {Γ Γ' : Env} {es : List Expr} {τ : Ty} :
      DJudgeSeq Γ es τ Γ' → DJudge Γ (.seq es) τ Γ'
  /-- A send with an explicit receiver, resolved by the primitive table. Receiver first, then
      arguments left to right — Ruby's own evaluation order, which is what makes threading
      `Γ` through them in this order the right claim. -/
  | prim {Γ Γ₁ Γ₂ : Env} {recv : Expr} {m : String} {args : List Expr}
      {σ τ : Ty} {argTys : List Ty} :
      DJudge Γ recv σ Γ₁ → DJudgeAll Γ₁ args argTys Γ₂ → DPrim σ m argTys τ →
      DJudge Γ (.send (some recv) m args none) τ Γ₂
  /-- `if c then t else e end`. The type is the join of the branches; the outgoing
      environment is the **pointwise** join, which is a soundness requirement rather than a
      precision one (`Ratchet/Ty.lean`'s `joinEnv`: carrying the pre-`if` environment forward
      certifies a program that really raises `TypeError`).

      The condition's outgoing environment `Γc` is what *both* branches start from: Ruby
      evaluates the condition before either. No narrowing — a `nilable` or `union` condition
      refines nothing here, and the rule that would do the refining is a separate rule with a
      separate justification. -/
  | if' {Γ Γc Γ₁ Γ₂ : Env} {c t e : Expr} {σ τ₁ τ₂ : Ty} :
      DJudge Γ c σ Γc → DJudge Γc t τ₁ Γ₁ → DJudge Γc e τ₂ Γ₂ →
      DJudge Γ (.if' c t (some e)) (joinT τ₁ τ₂) (joinEnv Γ₁ Γ₂)

inductive DJudgeAll : Env → List Expr → List Ty → Env → Prop
  | nil {Γ : Env} : DJudgeAll Γ [] [] Γ
  | cons {Γ Γ₁ Γ₂ : Env} {e : Expr} {es : List Expr} {τ : Ty} {τs : List Ty} :
      DJudge Γ e τ Γ₁ → DJudgeAll Γ₁ es τs Γ₂ → DJudgeAll Γ (e :: es) (τ :: τs) Γ₂

inductive DJudgeSeq : Env → List Expr → Ty → Env → Prop
  /-- The sequence's type is its **last** statement's. -/
  | last {Γ Γ' : Env} {e : Expr} {τ : Ty} : DJudge Γ e τ Γ' → DJudgeSeq Γ [e] τ Γ'
  | cons {Γ Γ₁ Γ₂ : Env} {e e' : Expr} {es : List Expr} {σ τ : Ty} :
      DJudge Γ e σ Γ₁ → DJudgeSeq Γ₁ (e' :: es) τ Γ₂ → DJudgeSeq Γ (e :: e' :: es) τ Γ₂
end

/-! ## §3 The checker, which *builds* the derivation

`check` does not return a `Ty` and leave soundness to a separate induction — it returns the
`DJudge` term. So layer 3 is not a theorem about layer 2, it is layer 2's **type**, and the
oracle that judges a rung is the Lean typechecker: if `check` compiles, every answer it can
ever give carries a derivation.

That is the same move as `Denote/Clink/`'s `Clink.sem` one level down, and it was chosen over
`check : … → Option (Ty × Env)` plus `check_sound` for a reason worth recording: the latter is
one `induction fuel` with a `split` over a 23-arm match, and every arm of it is a place where
the proof can be *weaker* than the function (an arm whose `none` case is discharged by
`simp` proves nothing about the arm's real behaviour). Here there is no gap to be weaker
across.

**Everything is computed from the program and *compared* against the certificate.** The
program is the authority: `check` matches `e`, derives the type itself, and then asks whether
the certificate agrees. A certificate that names a different literal, a different method, or a
different join is rejected — not because soundness needs it (it does not; the derivation is
about `e` either way) but because a checker that ignores its certificate is not checking one,
and the whole pipeline downstream of `scripts/emit_deriv.py` would be unfalsifiable.
`Ratchet/DerivControls.lean` pins each of those rejections.

### Why fuel

`Deriv` is a nested inductive and `check` is mutual with two list companions; fuel makes the
recursion structural and obviously terminating. Exhaustion answers `none`, so it can only cost
completeness. -/

/-- A checked answer: a type, an outgoing environment, **and the derivation**. The third
field is why `check`'s type is the soundness statement. -/
structure Certified (Γ : Env) (e : Expr) where
  ty : Ty
  out : Env
  judged : DJudge Γ e ty out

/-- The same for a send's argument list: the argument types, in order, with their
derivation. -/
structure CertifiedAll (Γ : Env) (es : List Expr) where
  tys : List Ty
  out : Env
  judged : DJudgeAll Γ es tys out

/-- And for a statement sequence. -/
structure CertifiedSeq (Γ : Env) (es : List Expr) where
  ty : Ty
  out : Env
  judged : DJudgeSeq Γ es ty out

mutual
/-- Check a certificate against a program, returning its derivation.

Dispatch is on the **expression**, because the expression is what the derivation has to be
about; the certificate is then required to be the matching rule. The other order would let a
certificate choose which rule to try, which is the same mistake as letting it choose a type. -/
def check (fuel : Nat) (Γ : Env) (e : Expr) (d : Deriv) : Option (Certified Γ e) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match e, d with
    | .int k, .intLit k' => if k == k' then some ⟨.int, Γ, .intLit⟩ else none
    | .flt b, .fltLit b' => if b == b' then some ⟨.float, Γ, .fltLit⟩ else none
    | .str s, .strLit s' => if s == s' then some ⟨.cls "String", Γ, .strLit⟩ else none
    | .sym s, .symLit s' => if s == s' then some ⟨.sym, Γ, .symLit⟩ else none
    | .tru, .truLit => some ⟨.bool, Γ, .truLit⟩
    | .fls, .flsLit => some ⟨.bool, Γ, .flsLit⟩
    | .nil, .nilLit => some ⟨.nilT, Γ, .nilLit⟩
    | .var .lvar x, .var .lvar x' =>
      if x == x' then
        match hg : envGet? Γ x with
        | some τ => some ⟨τ, Γ, .var hg⟩
        | none => none
      else none
    | .vasgn .lvar x ev, .vasgn .lvar x' dv =>
      if x == x' then
        match check n Γ ev dv with
        | some ⟨τ, Γ₁, hv⟩ => some ⟨τ, envSet Γ₁ x τ, .vasgn hv⟩
        | none => none
      else none
    | .seq es, .seq ds =>
      match checkSeq n Γ es ds with
      | some ⟨τ, Γ', hs⟩ => some ⟨τ, Γ', .seq hs⟩
      | none => none
    | .send (some recv) m args none, .prim dr dm dargs σc τc =>
      if dm == m then
        match check n Γ recv dr with
        | some ⟨σ, Γ₁, hr⟩ =>
          if σ == σc then
            match checkAll n Γ₁ args dargs with
            | some ⟨argTys, Γ₂, ha⟩ =>
              match hp : dprim? σ m argTys with
              | some τ =>
                if τ == τc then some ⟨τ, Γ₂, .prim hr ha (dprim?_sound hp)⟩ else none
              | none => none
            | none => none
          else none
        | none => none
      else none
    | .if' c t (some el), .ifD dc dt (some de) j =>
      match check n Γ c dc with
      | some ⟨_, Γc, hc⟩ =>
        match check n Γc t dt, check n Γc el de with
        | some ⟨τ₁, Γ₁, ht⟩, some ⟨τ₂, Γ₂, he⟩ =>
          if joinT τ₁ τ₂ == j then some ⟨joinT τ₁ τ₂, joinEnv Γ₁ Γ₂, .if' hc ht he⟩ else none
        | _, _ => none
      | none => none
    -- Out of the judgment. Every remaining certificate rule -- `defDecl`, `callSig`,
    -- `callMethodSig`, `classDecl`, `newInst`, `ivarRead`, `ivarAsgn`, `constCls`,
    -- `arrayLit`, `hashLit`, `selfExpr` -- and every expression head with no rule, answers
    -- `none`. Each joins by acquiring a `DJudge` rule, and each joining is a rung.
    | _, _ => none

def checkAll (fuel : Nat) (Γ : Env) (es : List Expr) (ds : List Deriv) :
    Option (CertifiedAll Γ es) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match es, ds with
    | [], [] => some ⟨[], Γ, .nil⟩
    | e :: es', d :: ds' =>
      match check n Γ e d with
      | some ⟨τ, Γ₁, he⟩ =>
        match checkAll n Γ₁ es' ds' with
        | some ⟨τs, Γ₂, hr⟩ => some ⟨τ :: τs, Γ₂, .cons he hr⟩
        | none => none
      | none => none
    -- A certificate with the wrong number of arguments is rejected here, in both
    -- directions. `Ratchet/DerivControls.lean` §3 is the control.
    | _, _ => none

def checkSeq (fuel : Nat) (Γ : Env) (es : List Expr) (ds : List Deriv) :
    Option (CertifiedSeq Γ es) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match es, ds with
    | [e], [d] =>
      match check n Γ e d with
      | some ⟨τ, Γ', he⟩ => some ⟨τ, Γ', .last he⟩
      | none => none
    | e :: e' :: es', d :: d' :: ds' =>
      match check n Γ e d with
      | some ⟨_, Γ₁, he⟩ =>
        match checkSeq n Γ₁ (e' :: es') (d' :: ds') with
        | some ⟨τ, Γ₂, hr⟩ => some ⟨τ, Γ₂, .cons he hr⟩
        | none => none
      | none => none
    | _, _ => none
end

/-! ## §4 The entry point

`validate` in the sense the ladder means it: a program, a certificate, a `Bool`. The `Bool`
is `isSome` of a value whose type contains the derivation, so `true` *is* "there is a
`DJudge` derivation of this program", with no theorem in between.

Fuel: 200 is far beyond anything in the corpus (the deepest rung nests ~12 levels) and is not
a soundness parameter -- running out answers `false`. -/

def fuelD : Nat := 200

/-- The certified judgment, as a proposition about a program: it types at *some* type in the
empty environment. -/
def DTyped (p : Expr) : Prop := ∃ τ Γ', DJudge [] p τ Γ'

/-- **The ladder's verdict.** `true` iff the certificate checks. -/
def validateD (p : Expr) (d : Deriv) : Bool := (check fuelD [] p d).isSome

/-- …and the verdict means what it says, by construction rather than by induction: this is
one `match`, because the `Certified` the checker returned carries the derivation. -/
theorem validateD_typed {p : Expr} {d : Deriv} (h : validateD p d = true) : DTyped p := by
  unfold validateD at h
  match hc : check fuelD [] p d with
  | some c => exact ⟨c.ty, c.out, c.judged⟩
  | none => rw [hc] at h; exact absurd h (by simp)

/-! ## §5 Semantic status — what a `true` does and does not mean

`validateD p d = true` means: **there is a `DJudge` derivation of `p`**, and the checker
handed it over rather than asserting it. That is layers 1–3 of the schema, closed.

It does **not** mean `p` is type-safe, and the gap is exactly the one `Denote/Clink/` was
built to keep visible: `DJudge`'s thirteen rules have **no semantic proofs**. None of them is
a `Clink`, so none is in a certified judgment, and the honest reading of the ladder's reach is
*coverage of the checker*, not justification.

Why the 48 proofs already on file do not transfer for free: `Denote/Sem/Obligations.lean`'s
`Obl.Judge.*` are statements about `SemJudge` alone (no `Judge` occurs in them), so they are
reusable *facts* — but they are stated at `Judge`'s index shape, with a `Ctx` and an ivar
spine, and `DJudge` deliberately has neither (§Not in the judgment). Reconciling the two is a
piece of work with a known shape and it has not been done; claiming the 48 here would be
claiming a theorem about a different judgment.

What is owed, in the order it gets cheaper:

| rule | what its semantic obligation needs |
|---|---|
| the seven literals, `var`, `vasgn`, `seq` | the `Env`-only counterpart of `StateOk`, then one `stepFn` unfolding each. The corresponding `Obl.Judge.*` are all **proved** at `Judge`'s shape, so this is a reconciliation, not a discovery |
| `if'` | `joinT`/`joinEnv` soundness — that a join is an upper bound on both branches under `denM`. Stated nowhere yet; `Denote/notes.md` §"not built" lists `subTy` soundness, which is the same fact |
| `prim` | one conformance fact per row: that CRuby's `Integer#+` really returns an `Integer` from the prelude-booted heap. `DPrim` has **7** rows against `PrimSig`'s ~90 precisely so this is a countable obligation rather than the ~200-fact block that stalled the old ladder three sessions running |

## §6 Relationship to `Ratchet/Judge.lean` and `Ratchet/Validate.lean`

They are untouched and still live: `lake exe ratchet corpus-untyped` and `lake exe checkrungs
corpus-untyped` run the legacy syntactic ladder (178/259 rungs, 177 hand derivations, 148
negative controls), and that evidence is real. Nothing here imports them, and nothing there
imports this.

The intent is replacement, not coexistence, and the condition is stated rather than assumed:
when the typed ladder's reach covers the corpus, the legacy ladder is what gets deleted — and
the reason to prefer the new one is not that it reaches further today (it does not, by a lot)
but that every rule it gains can arrive with a proof, one rung at a time, which is the thing
83 rules with 48 proofs cannot be retrofitted into.
-/

end Ratchet
