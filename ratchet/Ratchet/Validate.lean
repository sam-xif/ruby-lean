import Ratchet.Judge

/-!
The trusted checker: `validate : Expr → Bool`, over the **real** `Expr`.

**Tiers 1–3 only.** `chk` decides exactly the fragment `Ratchet/Judge.lean`'s `Judge`
specifies (the eight literals, tier 2's `send` table, and tier 3's
`var`/`vasgn`/`seq`/bare-`vcall`, and tier 4's `if'`), and answers `none` on everything
else — there is no fallback of any kind. The
certificate-claim fallback this checker used to carry is gone (`AGENTS.md`
§Claim-free): a claim was trusted, so a rung certified through one certified nothing,
and the `Bool` was worth less than it looked. Now every `true` is synthesized. Every rung outside that fragment therefore still
reports `false`, which is the honest state of a partly climbed ladder.

`chk` is not the specification; `Judge` is. `Ratchet/Proof/ChkSound.lean` proves the
one direction that matters for trusting a `true` answer:
`chk Γ e = some (τ, Γ') → Judge Γ e τ Γ'`.
-/

namespace Ratchet

/-- The decidable counterpart of `Judge.lean`'s `EqSafe`: the receivers for which `==`
is total. -/
def eqSafe? : Ty → Bool
  | .int | .float | .bool | .nilT | .sym | .cls _ => true
  | _ => false

/-- The executable primitive table — the decidable counterpart of `Judge.lean`'s
`PrimSig`, kept in exact one-to-one correspondence with it (`primSig?_sound`). A miss is
`none`, never a guess. -/
def primSig? : Ty → String → List Ty → Option Ty
  | σ, "==", [_] => if eqSafe? σ then some .bool else none
  | .int, "+", [.int] => some .int
  | .int, "-", [.int] => some .int
  | .int, "*", [.int] => some .int
  | .int, "/", [.int] => some .int
  | .cls "String", "+", [.cls "String"] => some (.cls "String")
  | .int, "<", [.int] => some .bool
  | .int, "<=", [.int] => some .bool
  | .int, ">", [.int] => some .bool
  | .int, ">=", [.int] => some .bool
  | .int, "to_s", [] => some (.cls "String")
  | .int, "zero?", [] => some .bool
  | .cls "String", "length", [] => some .int
  | .bool, "!", [] => some .bool
  | _, _, _ => none

/-- The executable counterpart of `BareNameError`: bare names known to resolve to
nothing at top-level `self`. One row, matching the judgment's one constructor. -/
def bareNameError? : String → Bool
  | "x" => true
  | _ => false

mutual

/-- Synthesize a type and an outgoing environment for `e`, or `none`. The catch-all is
`none`: a node kind with no structural rule is not typed, full stop. -/
def chk (Γ : Env) : Expr → Option (Ty × Env)
  | .int _ => some (.int, Γ)
  | .flt _ => some (.float, Γ)
  | .str _ => some (.cls "String", Γ)
  | .sym _ => some (.sym, Γ)
  | .tru => some (.bool, Γ)
  | .fls => some (.bool, Γ)
  | .nil => some (.nilT, Γ)
  | .var .lvar x =>
    match envGet? Γ x with
    | some τ => some (τ, Γ)
    | none => none
  | .vasgn .lvar x e =>
    match chk Γ e with
    | some (τ, Γ') => some (τ, envSet Γ' x τ)
    | none => none
  | .seq es => chkSeq Γ es
  | .if' c t (some e) =>
    match chk Γ c with
    | some (_, Γc) =>
      match chk Γc t with
      | some (τ₁, Γ₁) =>
        match chk Γc e with
        | some (τ₂, Γ₂) => some (joinT τ₁ τ₂, joinEnv Γ₁ Γ₂)
        | none => none
      | none => none
    | none => none
  | .if' c t none =>
    match chk Γ c with
    | some (_, Γc) =>
      match chk Γc t with
      | some (τ, Γ₁) => some (joinT τ .nilT, joinEnv Γ₁ Γc)
      | none => none
    | none => none
  | .vcall m => if bareNameError? m then some (.any, Γ) else none
  | .send (some recv) m args none =>
    -- Written as explicit nested `match`es rather than `do`/`<|>` on purpose: this is
    -- the trusted checker, and every route to a `some` should be visible on the page
    -- (and should `split` cleanly in `Ratchet/Proof/ChkSound.lean`).
    match chk Γ recv with
    | some (σ, Γ₁) =>
      match chkAll Γ₁ args with
      | some (argTys, Γ₂) =>
        match primSig? σ m argTys with
        | some τ => some (τ, Γ₂)
        | none => none
      | none => none
    | none => none
  | _ => none

/-- Pointwise `chk` over an argument list, threading the environment; `none` if any
argument fails. -/
def chkAll (Γ : Env) : List Expr → Option (List Ty × Env)
  | [] => some ([], Γ)
  | e :: es =>
    match chk Γ e with
    | some (τ, Γ₁) =>
      match chkAll Γ₁ es with
      | some (τs, Γ₂) => some (τ :: τs, Γ₂)
      | none => none
    | none => none

/-- A non-empty statement sequence: every statement must type, the result is the last
one's, and the environment threads. An empty `seq` is `none` (the desugarer never emits
one, and `JudgeSeq` has no rule for it). -/
def chkSeq (Γ : Env) : List Expr → Option (Ty × Env)
  | [] => none
  | [e] => chk Γ e
  | e :: e' :: es =>
    match chk Γ e with
    | some (_, Γ₁) => chkSeq Γ₁ (e' :: es)
    | none => none

end

/-- The ratchet's verdict for one rung: did `chk` synthesize *any* type for the whole
program, starting from the empty environment? -/
def validate (p : Expr) : Bool := (chk [] p).isSome

end Ratchet
