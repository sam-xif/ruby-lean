import Ratchet.Judge

/-!
The trusted checker: `validate : Expr → Bool`, over the **real** `Expr`.

**Rungs 1–13 only.** `chk` decides exactly the fragment `Ratchet/Judge.lean`'s `Judge`
specifies (tier 1's eight literals, plus `+`/`-`/`*`/`/` on `Integer` and `+` on
`String`), and answers `none` on everything else — there is no fallback of any kind. The
certificate-claim fallback this checker used to carry is gone (`AGENTS.md`
§Claim-free): a claim was trusted, so a rung certified through one certified nothing,
and the `Bool` was worth less than it looked. Now every `true` is synthesized. Every rung above 13 therefore still reports `false`,
which is the honest state of a ladder climbed 13 rungs.

`chk` is not the specification; `Judge` is. `Ratchet/Proof/ChkSound.lean` proves the
one direction that matters for trusting a `true` answer:
`chk e = some τ → Judge e τ`.
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

mutual

/-- Synthesize a type for `e`, or `none`. The catch-all is `none`: a node kind with no
structural rule is not typed, full stop. -/
def chk : Expr → Option Ty
  | .int _ => some .int
  | .flt _ => some .float
  | .str _ => some (.cls "String")
  | .sym _ => some .sym
  | .tru => some .bool
  | .fls => some .bool
  | .nil => some .nilT
  | .send (some recv) m args none =>
    -- Written as explicit nested `match`es rather than `do`/`<|>` on purpose: this is
    -- the trusted checker, and every route to a `some` should be visible on the page
    -- (and should `split` cleanly in `Ratchet/Proof/ChkSound.lean`).
    match chk recv, chkAll args with
    | some σ, some argTys => primSig? σ m argTys
    | _, _ => none
  | _ => none

/-- Pointwise `chk` over an argument list; `none` if any argument fails. -/
def chkAll : List Expr → Option (List Ty)
  | [] => some []
  | e :: es =>
    match chk e, chkAll es with
    | some τ, some τs => some (τ :: τs)
    | _, _ => none

end

/-- The ratchet's verdict for one rung: did `chk` synthesize *any* type for the whole
program? -/
def validate (p : Expr) : Bool := (chk p).isSome

end Ratchet
