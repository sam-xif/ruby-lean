import Ratchet.Judge

/-!
The trusted checker: `validate : Expr → Bool`, over the **real** `Expr`.

**Tiers 1–6 only.** `chk` decides exactly the fragment `Ratchet/Judge.lean`'s `Judge`
specifies (the eight literals, tier 2's `send` table, tier 3's
`var`/`vasgn`/`seq`/bare-`vcall`, tier 4's `if'`, tier 5's array/hash literals, and tier
6's top-level `def` plus implicit-self calls), and answers `none` on everything else —
there is no fallback of any kind. The certificate-claim fallback this checker used to carry
is gone (`AGENTS.md` §Claim-free): a claim was trusted, so a rung certified through one
certified nothing, and the `Bool` was worth less than it looked. Now every `true` is
synthesized. Every rung outside that fragment therefore still reports `false`, which is the
honest state of a partly climbed ladder.

`chk` is not the specification; `Judge` is. `Ratchet/Proof/ChkSound.lean` proves the
one direction that matters for trusting a `true` answer:
`chk fuel D Δ Γ e = some (τ, Γ') → Judge D Δ Γ e τ Γ'`.
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
  | .arrayOf τ, "[]", [.int] => some (mkNilable τ)
  | .cls "Hash", "[]", [_] => some .any
  | _, _, _ => none

/-- The executable counterpart of `BareNameError`: bare names known to resolve to
nothing at top-level `self`. One row, matching the judgment's one constructor. -/
def bareNameError? : String → Bool
  | "x" => true
  | _ => false

/-! ## Fuel

`chk` recurses into a method **body** at a call site (`Judge.callDef`), and a body is not a
subterm of the call — so tier 6 is where `chk` stops being structurally recursive. Rather
than invent a measure over the def and assumption tables, `chk` takes a fuel budget: it
matches on it, every recursive call spends one unit, and running out answers `none`.

That has no soundness consequence, and it is worth being precise about why: fuel can only
turn a `some` into a `none`, and `chk_sound` quantifies over every fuel value. A `true`
verdict is still a real derivation; an exhausted budget is one more way for this checker to
be conservative. It *is* a completeness knob, which is why it is a named constant rather
than a magic number at the call site.

`fuelDefault` is generous for this corpus — one unit per level of expression nesting plus
one per body instantiation, and the deepest rung needs well under twenty — and small enough
that `Ratchet/Rungs.lean`'s per-rung `rfl` checks stay fast. -/
def fuelDefault : Nat := 64

mutual

/-- Synthesize a type and an outgoing environment for `e`, or `none`, with methods `D`
defined and instantiations `Δ` assumed. The catch-all is `none`: a node kind with no
structural rule is not typed, full stop. -/
def chk (fuel : Nat) (D : DefTable) (Δ : AsmTable) (Γ : Env) (e : Expr) :
    Option (Ty × Env) :=
  match fuel, e with
  | 0, _ => none
  | _ + 1, .int _ => some (.int, Γ)
  | _ + 1, .flt _ => some (.float, Γ)
  | _ + 1, .str _ => some (.cls "String", Γ)
  | _ + 1, .sym _ => some (.sym, Γ)
  | _ + 1, .tru => some (.bool, Γ)
  | _ + 1, .fls => some (.bool, Γ)
  | _ + 1, .nil => some (.nilT, Γ)
  | _ + 1, .var .lvar x =>
    match envGet? Γ x with
    | some τ => some (τ, Γ)
    | none => none
  | f + 1, .vasgn .lvar x e =>
    match chk f D Δ Γ e with
    | some (τ, Γ') => some (τ, envSet Γ' x τ)
    | none => none
  | f + 1, .seq es => chkSeq f D Δ Γ es
  | f + 1, .if' c t (some e) =>
    match chk f D Δ Γ c with
    | some (_, Γc) =>
      match chk f D Δ Γc t with
      | some (τ₁, Γ₁) =>
        match chk f D Δ Γc e with
        | some (τ₂, Γ₂) => some (joinT τ₁ τ₂, joinEnv Γ₁ Γ₂)
        | none => none
      | none => none
    | none => none
  | f + 1, .if' c t none =>
    match chk f D Δ Γ c with
    | some (_, Γc) =>
      match chk f D Δ Γc t with
      | some (τ, Γ₁) => some (joinT τ .nilT, joinEnv Γ₁ Γc)
      | none => none
    | none => none
  | f + 1, .array es =>
    match chkAll f D Δ Γ es with
    | some (τs, Γ') => some (.arrayOf (elemTy τs), Γ')
    | none => none
  | f + 1, .hash pairs =>
    match chkPairs f D Δ Γ pairs with
    | some Γ' => some (.cls "Hash", Γ')
    | none => none
  | _ + 1, .vcall m =>
    -- Two conditions, nested rather than `&&`ed so each one is a separate `split` in
    -- `ChkSound.lean`: the name must be a known `BareNameError` row *and* nothing may
    -- have defined it (see `Judge.bareName`'s second premise).
    match defGet? D m with
    | some _ => none
    | none => if bareNameError? m then some (.any, Γ) else none
  | _ + 1, .def' _ _ _ => some (.sym, Γ)
  | f + 1, .send none m args none =>
    -- An implicit-self call. Four routes, in this order, and the order is the design:
    -- strictness first (a call with a non-returning argument never dispatches, defined or
    -- not), then the *assumption* (a recursive occurrence must not re-instantiate, or the
    -- recursion never bottoms out), then the def table.
    match chkAll f D Δ Γ args with
    | some (argTys, Γ') =>
      if argTys.contains .never then some (.never, Γ')
      else
        match asmGet? Δ m argTys with
        | some ρ => some (ρ, Γ')
        | none =>
          match defGet? D m with
          | some d =>
            match paramEnv d.params argTys with
            | some Γb =>
              -- **Pass A — the hint.** Type the body with this instantiation assumed to
              -- not return. Nothing downstream trusts the answer; it exists only to
              -- produce a candidate return type, and for a non-recursive method it is
              -- simply the body's type computed twice.
              match chk f D (⟨m, argTys, .never⟩ :: Δ) Γb d.body with
              | some (ρ₀, _) =>
                -- **Pass B — the check.** The candidate is put in the assumption table and
                -- the body re-typed; it counts only if it reproduces itself. This is the
                -- pass `chk_sound` reads, and the only one `Judge.callDef` mentions. The
                -- control in `CheckRungs.lean` shows it is load-bearing: a body whose
                -- recursive branch is type-stuck passes A and fails B.
                match chk f D (⟨m, argTys, ρ₀⟩ :: Δ) Γb d.body with
                | some (ρ₁, _) => if ρ₁ = ρ₀ then some (ρ₀, Γ') else none
                | none => none
              | none => none
            | none => none
          | none => none
    | none => none
  | f + 1, .send (some recv) m args none =>
    -- Written as explicit nested `match`es rather than `do`/`<|>` on purpose: this is
    -- the trusted checker, and every route to a `some` should be visible on the page
    -- (and should `split` cleanly in `Ratchet/Proof/ChkSound.lean`).
    match chk f D Δ Γ recv with
    | some (σ, Γ₁) =>
      match chkAll f D Δ Γ₁ args with
      | some (argTys, Γ₂) =>
        -- Strictness, one condition per `if` so each yields one disjunct of
        -- `Judge.primNever`'s premise.
        if σ = .never then some (.never, Γ₂)
        else if argTys.contains .never then some (.never, Γ₂)
        else
          match primSig? σ m argTys with
          | some τ => some (τ, Γ₂)
          | none => none
      | none => none
    | none => none
  | _ + 1, _ => none

/-- Pointwise `chk` over an argument list, threading the environment; `none` if any
argument fails. -/
def chkAll (fuel : Nat) (D : DefTable) (Δ : AsmTable) (Γ : Env) (es : List Expr) :
    Option (List Ty × Env) :=
  match fuel, es with
  | 0, _ => none
  | _ + 1, [] => some ([], Γ)
  | f + 1, e :: es =>
    match chk f D Δ Γ e with
    | some (τ, Γ₁) =>
      match chkAll f D Δ Γ₁ es with
      | some (τs, Γ₂) => some (τ :: τs, Γ₂)
      | none => none
    | none => none

/-- Key-then-value `chk` over a hash literal's pairs. Returns only the outgoing
environment: the key and value types are discarded (this `Ty` has no parameterised hash
type), but they still have to *exist*, which is the whole content of this function. -/
def chkPairs (fuel : Nat) (D : DefTable) (Δ : AsmTable) (Γ : Env)
    (ps : List (Expr × Expr)) : Option Env :=
  match fuel, ps with
  | 0, _ => none
  | _ + 1, [] => some Γ
  | f + 1, (k, v) :: ps =>
    match chk f D Δ Γ k with
    | some (_, Γ₁) =>
      match chk f D Δ Γ₁ v with
      | some (_, Γ₂) => chkPairs f D Δ Γ₂ ps
      | none => none
    | none => none

/-- A non-empty statement sequence: every statement must type, the result is the last
one's, and the environment threads. An empty `seq` is `none` (the desugarer never emits
one, and `JudgeSeq` has no rule for it).

**Also where `D` grows**, via `extendDefs`: a top-level `def` is visible to the statements
after it and to no earlier one, which is what stops `foo(); def foo; end` validating (see
`DefTable`). -/
def chkSeq (fuel : Nat) (D : DefTable) (Δ : AsmTable) (Γ : Env) (es : List Expr) :
    Option (Ty × Env) :=
  match fuel, es with
  | 0, _ => none
  | _ + 1, [] => none
  | f + 1, [e] => chk f D Δ Γ e
  | f + 1, e :: e' :: es =>
    match chk f D Δ Γ e with
    | some (_, Γ₁) => chkSeq f (extendDefs D e) Δ Γ₁ (e' :: es)
    | none => none

end

/-- The ratchet's verdict for one rung: did `chk` synthesize *any* type for the whole
program, from the empty environment, with nothing defined and nothing assumed? The
`Δ = []` is the load-bearing part — see `AsmTable`. -/
def validate (p : Expr) : Bool := (chk fuelDefault [] [] [] p).isSome

end Ratchet
