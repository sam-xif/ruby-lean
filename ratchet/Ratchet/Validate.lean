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
`chk fuel κ Γ I e = some (τ, Γ', I') → Judge κ Γ I e τ Γ' I'`.
-/

namespace Ratchet

/-- The decidable counterpart of `Judge.lean`'s `EqSafe`: the receivers for which `==`
is total. -/
def eqSafe? : Ty → Bool
  | .int | .float | .bool | .nilT | .sym | .cls _ => true
  | _ => false

/-- The decidable counterpart of `Judge.lean`'s `NilQSafe`: the receivers for which `nil?`
is the builtin one. Recursive at `nilable`, exactly as the relation is. -/
def nilQSafe? : Ty → Bool
  | .int | .float | .bool | .nilT | .sym | .cls _ | .arrayOf _ => true
  | .nilable τ => nilQSafe? τ
  | _ => false

/-- The executable primitive table — the decidable counterpart of `Judge.lean`'s
`PrimSig`, kept in exact one-to-one correspondence with it (`primSig?_sound`). A miss is
`none`, never a guess. -/
def primSig? : Ty → String → List Ty → Option Ty
  | σ, "==", [_] => if eqSafe? σ then some .bool else none
  | σ, "nil?", [] => if nilQSafe? σ then some .bool else none
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

/-- The decidable counterpart of `Judge.lean`'s `Comparable`. -/
def comparable? : Ty → Bool
  | .int | .float | .cls "String" => true
  | _ => false

/-- `IterSig`'s **first half**: the types an iterator binds its block's parameters at, from the
receiver's element type and the call's argument types. Needed before the body is typed. -/
def iterParams? : String → Ty → List Ty → Option (List Ty)
  | "each", τ, [] => some [τ]
  | "map", τ, [] => some [τ]
  | "select", τ, [] => some [τ]
  | "sort_by", τ, [] => some [τ]
  | "inject", τ, [α] => some [α, τ]
  | _, _, _ => none

/-- `IterSig`'s **second half**: the call's result, from the same inputs plus the type the
block's body came back at. The two side conditions live here because both are about `ρ` —
`sort_by`'s comparison and `inject`'s accumulator fixed point (see `IterSig`). -/
def iterResult? : String → Ty → List Ty → Ty → Option Ty
  | "each", τ, [], _ => some (.arrayOf τ)
  | "map", _, [], ρ => some (.arrayOf ρ)
  | "select", τ, [], _ => some (.arrayOf τ)
  | "sort_by", τ, [], ρ => if comparable? ρ then some (.arrayOf τ) else none
  | "inject", _, [α], ρ => if ρ = α then some α else none
  | _, _, _, _ => none

/-- The decidable counterpart of `Judge.lean`'s `BuiltinCls`, row for row. -/
def builtinCls? : String → Bool
  | "Integer" | "Float" | "String" | "Symbol" | "NilClass"
  | "TrueClass" | "FalseClass" | "Array" | "Hash" => true
  | _ => false

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

/-- Synthesize a type and the outgoing local/ivar states for `e`, or `none`, in context `κ`.
The catch-all is `none`: a node kind with no structural rule is not typed, full stop. -/
def chk (fuel : Nat) (κ : Ctx) (Γ : Env) (I : Ty) (e : Expr) :
    Option (Ty × Env × Ty) :=
  match fuel, e with
  | 0, _ => none
  | _ + 1, .int _ => some (.int, Γ, I)
  | _ + 1, .flt _ => some (.float, Γ, I)
  | _ + 1, .str _ => some (.cls "String", Γ, I)
  | _ + 1, .sym _ => some (.sym, Γ, I)
  | _ + 1, .tru => some (.bool, Γ, I)
  | _ + 1, .fls => some (.bool, Γ, I)
  | _ + 1, .nil => some (.nilT, Γ, I)
  | _ + 1, .var .lvar x =>
    match envGet? Γ x with
    | some τ => some (τ, Γ, I)
    | none => none
  | _ + 1, .var .ivar x => some ((ivarGet? I x).getD .nilT, Γ, I)
  | f + 1, .vasgn .lvar x e =>
    match chk f κ Γ I e with
    | some (τ, Γ', I') => some (τ, envSet Γ' x τ, I')
    | none => none
  | f + 1, .vasgn .ivar x e =>
    match chk f κ Γ I e with
    | some (τ, Γ', I') => some (τ, Γ', ivarSet I' x τ)
    | none => none
  | f + 1, .seq es => chkSeq f κ Γ I es
  | f + 1, .if' c t (some e) =>
    match chk f κ Γ I c with
    | some (_, Γc, Ic) =>
      -- Tier 12: each branch is typed in the environment `narrowEnvs` refines for it. The
      -- function is total and the identity on an unrecognized condition, so this arm reads
      -- the same as it did before narrowing existed for every condition below tier 12.
      match chk f κ (narrowEnvs κ.classes c Γc).1 (narrowSpine κ.classes c Ic).1 t with
      | some (τ₁, Γ₁, I₁) =>
        match chk f κ (narrowEnvs κ.classes c Γc).2 (narrowSpine κ.classes c Ic).2 e with
        | some (τ₂, Γ₂, I₂) =>
          -- Both threaded states are joined: locals by `joinEnv`, the ivar spine by
          -- `joinSpine` (tier 12c -- this used to demand `I₁ = I₂`).
          some (joinT τ₁ τ₂, joinEnv Γ₁ Γ₂, joinSpine I₁ I₂)
        | none => none
      | none => none
    | none => none
  | f + 1, .if' c t none =>
    match chk f κ Γ I c with
    | some (_, Γc, Ic) =>
      match chk f κ (narrowEnvs κ.classes c Γc).1 (narrowSpine κ.classes c Ic).1 t with
      | some (τ, Γ₁, I₁) =>
        some (joinT τ .nilT, joinEnv Γ₁ (narrowEnvs κ.classes c Γc).2,
              joinSpine I₁ (narrowSpine κ.classes c Ic).2)
      | none => none
    | none => none
  | f + 1, .array es =>
    match chkAll f κ Γ I es with
    | some (τs, Γ', I') => some (.arrayOf (elemTy τs), Γ', I')
    | none => none
  | f + 1, .hash pairs =>
    match chkPairs f κ Γ I pairs with
    | some (Γ', I') => some (.cls "Hash", Γ', I')
    | none => none
  | f + 1, .vcall m =>
    -- Two routes, and the order matters: implicit-self dispatch to one of `self`'s own
    -- methods first, and only at top level (`selfTy = none`) the `BareNameError` table.
    -- The two are mutually exclusive by `Judge.bareName`'s third premise.
    match κ.selfTy with
    | some (.inst n Iself) =>
      match mroGet? κ.classes n m with
      | some (dc, d) =>
        match paramEnv d.params [] with
        | some Γb =>
          match chk f (κ.inMethod (.inst n Iself) dc m) Γb Iself d.body with
          | some (ρ, _, Iout) => if Iout = Iself then some (ρ, Γ, I) else none
          | none => none
        | none => none
      | none => none
    | some (.clsOf n) =>
      -- Tier 8: `self` is a class-or-module object, so the bare name goes to the *singleton*
      -- table (`Judge.selfSCall`).
      match smroGet? κ.classes n m with
      | some (dc, d) =>
        match paramEnv d.params [] with
        | some Γb =>
          match chk f (κ.inMethod (.clsOf n) dc m) Γb .ivar0 d.body with
          | some (ρ, _, Iout) => if Iout = .ivar0 then some (ρ, Γ, I) else none
          | none => none
        | none => none
      | none => none
    | some _ => none
    | none =>
      -- A bare name at top level: a defined method first (tier 9b — assume-then-verify at
      -- zero arguments, exactly `callDef`), then the `BareNameError` table. The two are
      -- disjoint by `defGet?`.
      match asmGet? κ.asms m [] with
      | some ρ => some (ρ, Γ, I)
      | none =>
        match defGet? κ.defs m with
        | some d =>
          match paramEnv d.params [] with
          | some Γb =>
            match chk f { κ with asms := ⟨m, [], .never⟩ :: κ.asms } Γb .ivar0 d.body with
            | some (ρ₀, _, _) =>
              match chk f { κ with asms := ⟨m, [], ρ₀⟩ :: κ.asms } Γb .ivar0 d.body with
              | some (ρ₁, _, Iout) =>
                if ρ₁ = ρ₀ then (if Iout = .ivar0 then some (ρ₀, Γ, I) else none) else none
              | none => none
            | none => none
          | none => none
        | none => if bareNameError? m then some (.any, Γ, I) else none
  | _ + 1, .self' =>
    match κ.selfTy with
    | some σ => some (σ, Γ, I)
    | none => none
  | _ + 1, .const n =>
    -- A declared class first; only a name the program never declared goes to the builtin
    -- table. The two routes are disjoint by construction, which is what `Judge`'s
    -- `constBuiltin` states as a premise.
    match clsGet? κ.classes n with
    | some _ => some (.clsOf n, Γ, I)
    | none => if builtinCls? n then some (.clsOf n, Γ, I) else none
  | _ + 1, .def' _ _ _ => some (.sym, Γ, I)
  | _ + 1, .module' _ body =>
    match classMethods? body with
    | some (_, _) => some (.any, Γ, I)
    | none => none
  | _ + 1, .class' _ _ body =>
    match classMethods? body with
    | some (_, _) => some (.any, Γ, I)
    | none => none
  | f + 1, .send none m args (some (.block ps [] body)) =>
    -- An implicit-self send carrying a block literal. Two routes: `lambda`/`proc`, which
    -- *are* the block (tier 9a), and everything else, which passes it to a top-level method
    -- (tier 9b). Matched before the block-less arm because it is the only send in this
    -- fragment that carries a block at all.
    match κ.selfTy with
    | none =>
      if (m = "lambda" || m = "proc") && args.isEmpty then
        match closIdx? κ.closures ps body with
        | some idx => some (.clos idx (envToSpine Γ) (κ.selfTy.getD .never), Γ, I)
        | none => none
      else
        match chkAll f κ Γ I args with
        | some (argTys, Γ', I') =>
          match closIdx? κ.closures ps body with
          | some idx =>
            match defGet? κ.defs m with
            | some d =>
              match paramEnvB (some (.clos idx (envToSpine Γ) (κ.selfTy.getD .never)))
                  d.params argTys with
              | some Γb =>
                match chk f
                    { κ with blockTy := some (.clos idx (envToSpine Γ) (κ.selfTy.getD .never)) }
                    Γb .ivar0 d.body with
                | some (ρ, _, Iout) => if Iout = .ivar0 then some (ρ, Γ', I') else none
                | none => none
              | none => none
            | none => none
          | none => none
        | none => none
    | some _ => none
  | f + 1, .send none m args none =>
    -- An implicit-self call. Four routes, in this order, and the order is the design:
    -- strictness first (a call with a non-returning argument never dispatches, defined or
    -- not), then the *assumption* (a recursive occurrence must not re-instantiate, or the
    -- recursion never bottoms out), then the def table.
    match chkAll f κ Γ I args with
    | some (argTys, Γ', I') =>
      if argTys.contains .never then some (.never, Γ', I')
      else
        match asmGet? κ.asms m argTys with
        | some ρ => some (ρ, Γ', I')
        | none =>
          match defGet? κ.defs m with
          | some d =>
            match paramEnv d.params argTys with
            | some Γb =>
              -- **Pass A — the hint.** Type the body with this instantiation assumed to
              -- not return. Nothing downstream trusts the answer; it exists only to
              -- produce a candidate return type, and for a non-recursive method it is
              -- simply the body's type computed twice.
              match chk f { κ with asms := ⟨m, argTys, .never⟩ :: κ.asms } Γb .ivar0
                  d.body with
              | some (ρ₀, _, _) =>
                -- **Pass B — the check.** The candidate is put in the assumption table and
                -- the body re-typed; it counts only if it reproduces itself. This is the
                -- pass `chk_sound` reads, and the only one `Judge.callDef` mentions. The
                -- control in `CheckRungs.lean` shows it is load-bearing: a body whose
                -- recursive branch is type-stuck passes A and fails B.
                match chk f { κ with asms := ⟨m, argTys, ρ₀⟩ :: κ.asms } Γb .ivar0
                    d.body with
                | some (ρ₁, _, Iout) =>
                  if ρ₁ = ρ₀ then (if Iout = .ivar0 then some (ρ₀, Γ', I') else none)
                  else none
                | none => none
              | none => none
            | none => none
          | none =>
            -- Last route: a bare `new` inside a singleton method, where `self` is a class
            -- object rather than an instance (`Judge.selfNew`). Checked after the def table
            -- only because nothing needs the other order; a top-level method actually named
            -- `new` would win, which no rung has.
            match κ.selfTy with
            | some (.clsOf n) =>
              if m = "new" then
                match ctorGet? κ.classes n with
                | some (dc, d) =>
                  match paramEnv d.params argTys with
                  | some Γb =>
                    match chk f (κ.inCtor dc "initialize") Γb .ivar0 d.body with
                    | some (_, _, Iout) => some (.inst n Iout, Γ', I')
                    | none => none
                  | none => none
                | none => none
              else none
            | some _ => none
            | none => none
    | none => none
  | f + 1, .send (some recv) m args (some (.block ps locs body)) =>
    -- Tier 9c: a builtin iterator with a block literal (`Judge.iterBlock`). The receiver must
    -- be an array; the block's body is typed here, at `iterParams?`'s types, in
    -- parameters-then-block-locals-then-enclosing order.
    match chk f κ Γ I recv with
    | some (.arrayOf elem, Γ₁, I₁) =>
      match chkAll f κ Γ₁ I₁ args with
      | some (argTys, Γ₂, I₂) =>
        match iterParams? m elem argTys with
        | some βs =>
          match paramEnv ps βs with
          | some Γb =>
            match chk f κ (Γb ++ blockLocals locs ++ Γ₂) I₂ (bodyResult body) with
            | some (ρ, Γb', Iout) =>
              if Iout = I₂ then
                if capIntact (envToSpine Γ₂) (Γb ++ blockLocals locs ++ Γ₂) Γb' then
                  match iterResult? m elem argTys ρ with
                  | some res => some (res, Γ₂, I₂)
                  | none => none
                else none
              else none
            | none => none
          | none => none
        | none => none
      | none => none
    | _ => none
  | f + 1, .send (some recv) m args (some (.blockpass (some pe))) =>
    -- Tier 9c: the two `&` forms. Both need a one-parameter iterator; which one applies is
    -- decided by the `&` expression -- a Symbol literal is a `to_proc` coercion
    -- (`Judge.iterSymPass`), anything else has to synthesize a `Ty.clos`
    -- (`Judge.iterClosPass`).
    match chk f κ Γ I recv with
    | some (.arrayOf elem, Γ₁, I₁) =>
      match chkAll f κ Γ₁ I₁ args with
      | some (argTys, Γ₂, I₂) =>
        match iterParams? m elem argTys with
        | some [β] =>
          match pe with
          | .sym s =>
            match primSig? β s [] with
            | some ρ =>
              match iterResult? m elem argTys ρ with
              | some res => some (res, Γ₂, I₂)
              | none => none
            | none => none
          | _ =>
            match chk f κ Γ₂ I₂ pe with
            | some (.clos idx cap cself, Γ₃, I₃) =>
              match closGet? κ.closures idx with
              | some c =>
                match paramEnv c.params [β] with
                | some Γb =>
                  match chk f (κ.inClosure cself) (Γb ++ spineToEnv cap) (closSpine cself)
                      (bodyResult c.body) with
                  | some (ρ, Γb', Iout) =>
                    if Iout = closSpine cself then
                      if capIntact cap (Γb ++ spineToEnv cap) Γb' then
                        match iterResult? m elem argTys ρ with
                        | some res => some (res, Γ₃, I₃)
                        | none => none
                      else none
                    else none
                  | none => none
                | none => none
              | none => none
            | _ => none
        | _ => none
      | none => none
    | _ => none
  | f + 1, .send (some recv) m args none =>
    -- Written as explicit nested `match`es rather than `do`/`<|>` on purpose: this is
    -- the trusted checker, and every route to a `some` should be visible on the page
    -- (and should `split` cleanly in `Ratchet/Proof/ChkSound.lean`).
    match chk f κ Γ I recv with
    | some (σ, Γ₁, I₁) =>
      match chkAll f κ Γ₁ I₁ args with
      | some (argTys, Γ₂, I₂) =>
        -- Strictness, one condition per `if` so each yields one disjunct of
        -- `Judge.primNever`'s premise.
        if σ = .never then some (.never, Γ₂, I₂)
        else if argTys.contains .never then some (.never, Γ₂, I₂)
        else if m = "is_a?" then
          -- Tier 12. Placed *before* the receiver dispatch, and note the consequence: a
          -- receiver whose class overrides `is_a?` fails `isADispatchOk` and this arm answers
          -- `none` rather than falling through to `callMethod`. Conservative, not unsound —
          -- and recorded as a negative control.
          match argTys with
          | [.clsOf _] =>
            if isADispatchOk κ.classes σ then some (.bool, Γ₂, I₂) else none
          | _ => none
        else
          -- Tier 7's dispatch, keyed on what the receiver's type *is*: a class object
          -- allocates, an instance dispatches, anything else goes to the primitive table.
          match σ with
          | .clsOf n =>
            -- A declared singleton method wins over the allocator, which is what Ruby does
            -- for a class that defines `self.new`.
            match smroGet? κ.classes n m with
            | some (dc, d) =>
              match paramEnv d.params argTys with
              | some Γb =>
                match chk f (κ.inMethod (.clsOf n) dc m) Γb .ivar0 d.body with
                | some (ρ, _, Iout) => if Iout = .ivar0 then some (ρ, Γ₂, I₂) else none
                | none => none
              | none => none
            | none =>
              if m = "new" then
                match ctorGet? κ.classes n with
                | some (dc, d) =>
                  match paramEnv d.params argTys with
                  | some Γb =>
                    match chk f (κ.inCtor dc "initialize") Γb .ivar0 d.body with
                    | some (_, _, Iout) => some (.inst n Iout, Γ₂, I₂)
                    | none => none
                  | none => none
                | none =>
                  -- No `initialize` anywhere up the chain: `Object#new` takes zero
                  -- arguments.
                  match instClsGet? κ.classes n with
                  | some _ => if argTys = [] then some (.inst n .ivar0, Γ₂, I₂) else none
                  | none => none
              else none
          | .clos idx cap cself =>
            -- Tier 9: invoke a callable by checking its body at this call site's argument
            -- types, in an environment of parameters-then-captures -- and (tier 11) in the
            -- *creation* site's `self` and ivar spine, both read out of the type.
            if m = "call" || m = "[]" then
              match closGet? κ.closures idx with
              | some c =>
                match paramEnv c.params argTys with
                | some Γb =>
                  match chk f (κ.inClosure cself) (Γb ++ spineToEnv cap) (closSpine cself)
                      (bodyResult c.body) with
                  -- Neither the ivar spine nor any captured local may be retyped by the
                  -- callee (see `capIntact` -- the second one is a real soundness bug if
                  -- omitted, not caution).
                  | some (ρ, Γb', Iout) =>
                    if Iout = closSpine cself then
                      (if capIntact cap (Γb ++ spineToEnv cap) Γb' then some (ρ, Γ₂, I₂)
                       else none)
                    else none
                  | none => none
                | none => none
              | none => none
            else none
          | .inst n Iself =>
            match mroGet? κ.classes n m with
            | some (dc, d) =>
              match paramEnv d.params argTys with
              | some Γb =>
                match chk f (κ.inMethod (.inst n Iself) dc m) Γb Iself d.body with
                -- The callee may not retype any instance variable — see
                -- `Judge.callMethod`, where this equation is the soundness argument for
                -- the whole ivar mechanism.
                | some (ρ, _, Iout) => if Iout = Iself then some (ρ, Γ₂, I₂) else none
                | none => none
              | none => none
            | none => none
          | _ =>
            match primSig? σ m argTys with
            | some τ => some (τ, Γ₂, I₂)
            | none => none
      | none => none
    | none => none
  | f + 1, .yield' args =>
    match κ.blockTy with
    | some (.clos idx cap cself) =>
      match chkAll f κ Γ I args with
      | some (argTys, Γ', I') =>
        match closGet? κ.closures idx with
        | some c =>
          match paramEnvB none c.params argTys with
          | some Γb =>
            match chk f (κ.inClosure cself) (Γb ++ spineToEnv cap) (closSpine cself)
                (bodyResult c.body) with
            | some (ρ, Γb', Iout) =>
              if Iout = closSpine cself then
                (if capIntact cap (Γb ++ spineToEnv cap) Γb' then some (ρ, Γ', I')
                 else none)
              else none
            | none => none
          | none => none
        | none => none
      | none => none
    | some _ => none
    | none => none
  | f + 1, .super' args none =>
    match chkAll f κ Γ I args with
    | some (argTys, Γ', I') =>
      match κ.frame with
      | some fr =>
        match clsGet? κ.classes fr.defClass with
        | some c =>
          match c.super? with
          | some sn =>
            match mroGet? κ.classes sn fr.methName with
            | some (dc, d) =>
              match paramEnv d.params argTys with
              | some Γb =>
                match chk f { κ with frame := some ⟨dc, fr.methName⟩ } Γb I' d.body with
                | some (ρ, _, Iout) => some (ρ, Γ', Iout)
                | none => none
              | none => none
            | none => none
          | none => none
        | none => none
      | none => none
    | none => none
  | _ + 1, _ => none

/-- Pointwise `chk` over an argument list, threading both states; `none` if any
argument fails. -/
def chkAll (fuel : Nat) (κ : Ctx) (Γ : Env) (I : Ty) (es : List Expr) :
    Option (List Ty × Env × Ty) :=
  match fuel, es with
  | 0, _ => none
  | _ + 1, [] => some ([], Γ, I)
  | f + 1, e :: es =>
    match chk f κ Γ I e with
    | some (τ, Γ₁, I₁) =>
      match chkAll f κ Γ₁ I₁ es with
      | some (τs, Γ₂, I₂) => some (τ :: τs, Γ₂, I₂)
      | none => none
    | none => none

/-- Key-then-value `chk` over a hash literal's pairs. Returns only the outgoing states:
the key and value types are discarded (this `Ty` has no parameterised hash type), but they
still have to *exist*, which is the whole content of this function. -/
def chkPairs (fuel : Nat) (κ : Ctx) (Γ : Env) (I : Ty)
    (ps : List (Expr × Expr)) : Option (Env × Ty) :=
  match fuel, ps with
  | 0, _ => none
  | _ + 1, [] => some (Γ, I)
  | f + 1, (k, v) :: ps =>
    match chk f κ Γ I k with
    | some (_, Γ₁, I₁) =>
      match chk f κ Γ₁ I₁ v with
      | some (_, Γ₂, I₂) => chkPairs f κ Γ₂ I₂ ps
      | none => none
    | none => none

/-- A non-empty statement sequence: every statement must type, the result is the last
one's, and both states thread. An empty `seq` is `none` (the desugarer never emits one, and
`JudgeSeq` has no rule for it).

**Also where the syntax tables grow**, via `Ctx.afterStmt`: a top-level `def` or `class` is
visible to the statements after it and to no earlier one, which is what stops
`foo(); def foo; end` validating (see `DefTable`). -/
def chkSeq (fuel : Nat) (κ : Ctx) (Γ : Env) (I : Ty) (es : List Expr) :
    Option (Ty × Env × Ty) :=
  match fuel, es with
  | 0, _ => none
  | _ + 1, [] => none
  | f + 1, [e] => chk f κ Γ I e
  | f + 1, .if' c (.ret (some r)) none :: e' :: es =>
    -- Tier 12's guard clause (`Judge.guard`). Matched *before* the generic `cons` arm, and
    -- only in non-final position — a `return … if …` as the whole body of a sequence still has
    -- no rule, because `.ret` has none.
    match chk f κ Γ I c with
    | some (_, Γc, Ic) =>
      match chk f κ (narrowEnvs κ.classes c Γc).1 (narrowSpine κ.classes c Ic).1 r with
      | some (ρ, _, Ir) =>
        if Ir = (narrowSpine κ.classes c Ic).1 then
          match chkSeq f κ (narrowEnvs κ.classes c Γc).2
              (narrowSpine κ.classes c Ic).2 (e' :: es) with
          | some (τ, Γ', I') => some (joinT ρ τ, Γ', I')
          | none => none
        else none
      | none => none
    | none => none
  | f + 1, e :: e' :: es =>
    match chk f κ Γ I e with
    | some (_, Γ₁, I₁) => chkSeq f (κ.afterStmt e) Γ₁ I₁ (e' :: es)
    | none => none

end

/-- The starting context: no classes, no methods, no assumptions, no `self`. Every
emptiness is load-bearing, and for a different reason — the two syntax tables because
nothing is declared before a program's first statement, the assumption table because a
derivation carrying one is only a conditional claim (`AsmTable`), and `frame`/`selfTy`
because a program's top level is inside no method and runs somewhere `self` is not an
instance of anything this judgment models. -/
def ctx0 : Ctx := ⟨[], [], [], none, [], none, none⟩

/-- `ctx0` with the program's block table filled in. The one component of `Ctx` that is not
empty at the start and never changes afterwards: `collectBlocks` runs once, before checking,
so that `Ty.clos`'s index means the same thing at every point in the derivation (see
`collectBlocks`). -/
def Ctx.withBlocks (κ : Ctx) (p : Expr) : Ctx := { κ with closures := collectBlocks p }

/-- The ratchet's verdict for one rung: did `chk` synthesize *any* type for the whole
program, from the empty local environment and the empty ivar spine, in `ctx0`? -/
def validate (p : Expr) : Bool :=
  (chk fuelDefault (ctx0.withBlocks p) [] .ivar0 p).isSome

end Ratchet
