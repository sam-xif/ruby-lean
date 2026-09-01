import Ratchet.Judge

/-!
The trusted checker: `validate : Cert → Expr → Bool`, over the **real** `Expr`.

**Rungs 1–13 only.** `chk` decides exactly the fragment `Ratchet/Judge.lean`'s `Judge`
specifies (tier 1's eight literals, plus `+`/`-`/`*`/`/` on `Integer` and `+` on
`String`), falls back to the certificate's claims at every node kind it cannot
synthesize structurally (`AGENTS.md` §Design notes' first principle — uniform
claim-fallback, not the case-by-case version the pre-restart implementation had), and
answers `none` on everything else. Every rung above 13 therefore still reports `false`,
which is the honest state of a ladder climbed 13 rungs.

`chk` is not the specification; `Judge` is. `Ratchet/Proof/ChkSound.lean` proves the
one direction that matters for trusting a `true` answer:
`chk c e = some τ → Judge c e τ`.
-/

namespace Ratchet

/-- The executable primitive table — the decidable counterpart of `Judge.lean`'s
`PrimSig`, kept in exact one-to-one correspondence with it (`primSig?_sound`). A miss is
`none`, never a guess. -/
def primSig? : Ty → String → List Ty → Option Ty
  | .int, "+", [.int] => some .int
  | .int, "-", [.int] => some .int
  | .int, "*", [.int] => some .int
  | .int, "/", [.int] => some .int
  | .cls "String", "+", [.cls "String"] => some (.cls "String")
  | _, _, _ => none

mutual

/-- Synthesize a type for `e`, or `none`.

The final catch-all is the uniform claim-fallback: any node kind with no structural rule
gets whatever the certificate claims for it, if anything. `send` gets the fallback too
(`<|>`), so an unmodeled builtin can be certified by a claim without widening
`primSig?`. -/
def chk (c : Cert) : Expr → Option Ty
  | .int _ => some .int
  | .flt _ => some .float
  | .str _ => some (.cls "String")
  | .sym _ => some .sym
  | .tru => some .bool
  | .fls => some .bool
  | .nil => some .nilT
  | e@(.send (some recv) m args none) =>
    -- Written as explicit nested `match`es rather than `do`/`<|>` on purpose: this is
    -- the trusted checker, and every route to a `some` should be visible on the page
    -- (and should `split` cleanly in `Ratchet/Proof/ChkSound.lean`).
    match chk c recv, chkAll c args with
    | some σ, some argTys =>
      match primSig? σ m argTys with
      | some τ => some τ
      | none => c.lookup e
    | _, _ => c.lookup e
  | e => c.lookup e

/-- Pointwise `chk` over an argument list; `none` if any argument fails. -/
def chkAll (c : Cert) : List Expr → Option (List Ty)
  | [] => some []
  | e :: es =>
    match chk c e, chkAll c es with
    | some τ, some τs => some (τ :: τs)
    | _, _ => none

end

/-- The ratchet's verdict for one rung: did `chk` synthesize *any* type for the whole
program? -/
def validate (c : Cert) (p : Expr) : Bool := (chk c p).isSome

end Ratchet
