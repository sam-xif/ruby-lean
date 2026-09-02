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

-- `primSig?` is a 33-row match over `(Ty, String, List Ty)`, and the *splitter* Lean builds for
-- it (which `Ratchet/Proof/ChkSound.lean`'s `primSig?_sound` needs, and which is generated on
-- demand in this module's context rather than in the proof's) exceeds the default budget. Not a
-- soundness knob: a heartbeat limit can only turn a proof into an error.
set_option maxHeartbeats 1000000

/-- The decidable counterpart of `Judge.lean`'s `EqSafe`: the receivers for which `==`
is total. -/
def eqSafe? : Ty → Bool
  | .int | .float | .bool | .nilT | .sym | .cls _ | .hashOf _ _ => true
  | _ => false

/-- The decidable counterpart of `Judge.lean`'s `NilQSafe`: the receivers for which `nil?`
is the builtin one. Recursive at `nilable`, exactly as the relation is. -/
def nilQSafe? : Ty → Bool
  | .int | .float | .bool | .nilT | .sym | .cls _ | .arrayOf _ | .hashOf _ _ => true
  | .nilable τ => nilQSafe? τ
  | _ => false

/-- The `.cls "String"` half of the table, split out (tier 16b) — and the reason is
mechanical rather than conceptual: `primSig?` had grown to 33 rows over
`(Ty, String, List Ty)`, and the *splitter* Lean builds for `split at h` in
`primSig?_sound` outgrew its budget. Two smaller matches cost one extra lemma
(`primSigStr?_sound`) and nothing else.

Note what is *not* here: `==`, `nil?`, `===`, `freeze` and `message` all apply to a `String`
receiver too, and they are guarded rows in `primSig?` matched *before* it delegates here. -/
def primSigStr? : String → List Ty → Option Ty
  | "+", [.cls "String"] => some (.cls "String")
  | "length", [] => some .int
  | "empty?", [] => some .bool
  | "strip", [] => some (.cls "String")
  | "downcase", [] => some (.cls "String")
  | "upcase", [] => some (.cls "String")
  | "tr", [.cls "String", .cls "String"] => some (.cls "String")
  | "delete_prefix", [.cls "String"] => some (.cls "String")
  | "start_with?", [.cls "String"] => some .bool
  | "split", [.cls "String"] => some (.arrayOf (.cls "String"))
  | "sub", [.cls "Regexp", .cls "String"] => some (.cls "String")
  | "gsub", [.cls "Regexp", .cls "String"] => some (.cls "String")
  | "match?", [.cls "Regexp"] => some .bool
  | "match", [.cls "Regexp"] => some (.nilable (.cls "MatchData"))
  | _, _ => none

/-- The `Array` half of the table (tiers 5, 14b and 17a), split out for `primSigStr?`'s
reason. Three of its rows carry a guard on the **element** type rather than the receiver's,
because they call `==`/`hash` on the elements -- see `PrimSig.arrayInclude` -- and one carries
the equality that makes `arrayOf` invariant (`PrimSig.arrayPush`). -/
def primSigArr? : String → List Ty → Ty → Option Ty
  | "length", [], _ => some .int
  | "[]", [.int], τ => some (mkNilable τ)
  | "empty?", [], _ => some .bool
  | "first", [], τ => some (mkNilable τ)
  | "last", [], τ => some (mkNilable τ)
  | "compact", [], τ => some (.arrayOf (nonNilTy τ))
  | "join", [.cls "String"], .cls "String" => some (.cls "String")
  | "<<", [σ], τ => if τ = σ then some (.arrayOf τ) else none
  | "include?", [_], τ => if nilQSafe? τ then some .bool else none
  | "uniq", [], τ => if nilQSafe? τ then some (.arrayOf τ) else none
  | _, _, _ => none

/-- The `Hash` half of the table (tier 17b), split out for `primSigStr?`'s reason — a big
match's splitter, not its rows, is what `split at h` costs.

Every row's key argument carries `NilQSafe`, because every one of them **hashes** it; the key
*parameter* `k` is not required to match, because a missing key is `nil` in Ruby rather than an
error (see `PrimSig.hashIndex`). `k` is therefore unused except by `dig`'s two-level row, and is
taken as a parameter so that the delegation in `primSig?` can pass the whole type apart. -/
def primSigHash? : String → List Ty → Ty → Ty → Option Ty
  | "key?", [σ], _, _ => if nilQSafe? σ then some .bool else none
  | "fetch", [σ], _, v => if nilQSafe? σ then some v else none
  | "fetch", [σ, ρ], _, v => if nilQSafe? σ then some (joinT v ρ) else none
  | "[]", [σ], _, v => if nilQSafe? σ then some (mkNilable v) else none
  | "dig", [σ], _, v => if nilQSafe? σ then some (mkNilable v) else none
  | "dig", [σ, σ2], _, .hashOf _ v =>
    if nilQSafe? σ && nilQSafe? σ2 then some (mkNilable v) else none
  | "length", [], _, _ => some .int
  | _, _, _, _ => none

/-- The executable primitive table — the decidable counterpart of `Judge.lean`'s
`PrimSig`, kept in exact one-to-one correspondence with it (`primSig?_sound`). A miss is
`none`, never a guess. -/
def primSig? : Ty → String → List Ty → Option Ty
  -- The five **guarded** rows first, because each applies to more than one receiver shape --
  -- including `.cls "String"`, which is why they come before the delegation below.
  | σ, "==", [_] => if eqSafe? σ then some .bool else none
  | σ, "nil?", [] => if nilQSafe? σ then some .bool else none
  -- Tier 16: `===` on a value receiver (`case t when "pypi"`), guarded exactly as `==` is.
  | σ, "===", [_] => if eqSafe? σ then some .bool else none
  -- Tier 13: `Object#freeze`, the identity, under `NilQSafe`'s guard (`PrimSig.freezeId`).
  | σ, "freeze", [] => if nilQSafe? σ then some σ else none
  -- Tier 16b: `Exception#message`, guarded by the receiver's *name* (`PrimSig.excMessage`).
  | .cls n, "message", [] => if excCls? n then some (.cls "String") else none
  -- Tiers 2/15/16b: everything else on a `String` receiver.
  | .cls "String", m, as => primSigStr? m as
  -- Tiers 5/17b: everything on a `Hash` receiver, delegated for the same reason.
  | .hashOf k v, m, as => primSigHash? m as k v
  -- Tiers 5/14b/17a: everything on an `Array` receiver, likewise.
  | .arrayOf τ, m, as => primSigArr? m as τ
  | .int, "+", [.int] => some .int
  | .int, "-", [.int] => some .int
  | .int, "*", [.int] => some .int
  | .int, "/", [.int] => some .int
  | .int, "<", [.int] => some .bool
  | .int, "<=", [.int] => some .bool
  | .int, ">", [.int] => some .bool
  | .int, ">=", [.int] => some .bool
  | .int, "to_s", [] => some (.cls "String")
  | .int, "zero?", [] => some .bool
  | .int, "__as_string", [] => some (.cls "String")
  | .sym, "to_s", [] => some (.cls "String")
  | .bool, "!", [] => some .bool
  | .int, "<=>", [.int] => some .int
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
  -- Tier 17's iterators.
  | "any?", τ, [] => some [τ]
  | "all?", τ, [] => some [τ]
  | "find", τ, [] => some [τ]
  | "filter_map", τ, [] => some [τ]
  | "flat_map", τ, [] => some [τ]
  | "each_with_index", τ, [] => some [τ, .int]
  | _, _, _ => none

/-- `IterSig`'s **second half**: the call's result, from the same inputs plus the type the
block's body came back at. The two side conditions live here because both are about `ρ` —
`sort_by`'s comparison and `inject`'s accumulator fixed point (see `IterSig`). -/
def iterResult? : String → Ty → List Ty → Ty → Option Ty
  | "each", τ, [], _ => some (.arrayOf τ)
  | "map", _, [], ρ => some (.arrayOf ρ)
  | "select", τ, [], _ => some (.arrayOf τ)
  | "sort_by", τ, [], ρ => if comparable? ρ then some (.arrayOf τ) else none
  -- Tier 14b: an `arrayOf .never` receiver is provably empty, so the block never runs and the
  -- block's return type is unconstrained (`IterSig.injectEmpty`). Matched *before* the general
  -- row, which is why that row's `ρ = α` never has to consider it.
  | "inject", .never, [α], _ => some α
  | "inject", _, [α], ρ => if ρ = α then some α else none
  | "any?", _, [], _ => some .bool
  | "all?", _, [], _ => some .bool
  | "find", τ, [], _ => some (mkNilable τ)
  | "filter_map", _, [], ρ => some (.arrayOf (truthyTy ρ))
  -- `flat_map`'s block must return an array; the result's element type is that array's.
  | "flat_map", _, [], .arrayOf σ => some (.arrayOf σ)
  | "each_with_index", τ, [], _ => some (.arrayOf τ)
  | _, _, _, _ => none

/-- The decidable counterpart of `Judge.lean`'s `ObjectMethod`. A `List.contains`, so the
proof is `decide` and the *list* is the thing to audit -- see `ObjectMethod` for why that list
being complete is a soundness condition rather than a coverage one. -/
def objectMethod? (m : String) : Bool := objectMethodNames.contains m

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
  -- Tier 15: a regexp literal is opaque (`Judge.regexpLit`).
  | _ + 1, .regexpLit _ _ => some (.cls "Regexp", Γ, I)
  | _ + 1, .str _ => some (.cls "String", Γ, I)
  | _ + 1, .sym _ => some (.sym, Γ, I)
  | _ + 1, .tru => some (.bool, Γ, I)
  | _ + 1, .fls => some (.bool, Γ, I)
  | _ + 1, .nil => some (.nilT, Γ, I)
  | _ + 1, .var .lvar x =>
    match envGet? Γ x with
    -- Tier 12: `stripAlias`, so no expression ever has type `sameAs` (see `Ty.sameAs`).
    | some τ => some (stripAlias τ, Γ, I)
    | none => none
  | _ + 1, .var .ivar x => some ((ivarGet? I x).getD .nilT, Γ, I)
  | _ + 1, .vasgn .lvar t (.var .lvar x) =>
    -- Tier 12: a desugarer temporary assigned from a local records an **alias**
    -- (`Judge.vasgnAlias`). Matched before the general `vasgn` arm, and only for one of the
    -- desugarer's own temporary names -- see `Judge.vasgnAlias` on why the restriction is blast
    -- radius rather than soundness, and `desugarTemps` on why it is a list and not a prefix.
    match envGet? Γ x with
    | some τ =>
      -- `capStale`: the value being bound may itself be a closure that captured `t`, in
      -- which case *its own* record of `t` is what the assignment invalidates and there is
      -- nothing left to widen (`found-issues.md` §F1; `Judge.vasgn`'s `hcap` premise).
      if capStale t (stripAlias τ) (stripAlias τ) = false
         && capStaleCtx t (stripAlias τ) κ = false
         -- `found-issues.md` §F5: the recorded type must not itself be an alias.
         -- `stripAlias` removes one layer, so a *nested* alias in `Γ` would still be one --
         -- unreachable (nothing builds one), and rejected here rather than assumed away.
         && isAliasTy (stripAlias τ) = false then
        if desugarTemps.contains t then
          some (stripAlias τ,
            envSet (killClosOver (killAliasesTo Γ t) t (stripAlias τ)) t
              (.sameAs x (stripAlias τ)),
            killClosOverSpine I t (stripAlias τ))
        else some (stripAlias τ,
            envSet (killClosOver (killAliasesTo Γ t) t (stripAlias τ)) t (stripAlias τ),
            killClosOverSpine I t (stripAlias τ))
      else none
    | none => none
  | f + 1, .vasgn .lvar x e =>
    match chk f κ Γ I e with
    -- `killAliasesTo`: once `x` holds a new object, nothing else holds the same one.
    -- `killClosOver`/`killClosOverSpine`: and nothing else may keep a `Ty.clos` recording
    -- what `x` used to be (`found-issues.md` §F1).
    | some (τ, Γ', I') =>
      if capStale x τ τ = false && capStaleCtx x τ κ = false
         -- `found-issues.md` §F5
         && isAliasTy τ = false then
        some (τ, envSet (killClosOver (killAliasesTo Γ' x) x τ) x τ, killClosOverSpine I' x τ)
      else none
    | none => none
  | f + 1, .vasgn .ivar x e =>
    match chk f κ Γ I e with
    -- §F17: a local (or the right-hand side's own type) can record a claim about `@x`, which
    -- this assignment invalidates — `capStale`'s guard one piece of state over.
    | some (τ, Γ', I') =>
      if ivarStaleFreeEnv x Γ' && ivarStaleFree x τ then some (τ, Γ', ivarSet I' x τ) else none
    | none => none
  | f + 1, .seq es => chkSeq f κ Γ I es
  | f + 1, .if' c t (some e) =>
    match chk f κ Γ I c with
    | some (_, Γc, Ic) =>
      -- Tier 12: each branch is typed in the environment `narrowEnvs` refines for it. The
      -- function is total and the identity on an unrecognized condition, so this arm reads
      -- the same as it did before narrowing existed for every condition below tier 12.
      match chk f κ (narrowEnvs κ c Γc).1 (narrowSpine κ c Ic).1 t with
      | some (τ₁, Γ₁, I₁) =>
        match chk f κ (narrowEnvs κ c Γc).2 (narrowSpine κ c Ic).2 e with
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
      match chk f κ (narrowEnvs κ c Γc).1 (narrowSpine κ c Ic).1 t with
      | some (τ, Γ₁, I₁) =>
        some (joinT τ .nilT, joinEnv Γ₁ (narrowEnvs κ c Γc).2,
              joinSpine I₁ (narrowSpine κ c Ic).2)
      | none => none
    | none => none
  | f + 1, .begin' body rescues none none =>
    -- Tier 16b. `noLocalAsgn body` is what makes typing the handlers in the *entry* environment
    -- sound: a handler runs at an arbitrary point inside the body, and a body with no local
    -- assignment has no intermediate state to get wrong (`Judge.begin'`).
    match chk f κ Γ I body with
    | some (τb, Γb, Ib) =>
      if Γb = Γ && Ib = I && noLocalAsgn body then
        match chkRescues f κ Γ I rescues with
        | some τr => some (joinT τb τr, Γ, I)
        | none => none
      else none
    | none => none
  | f + 1, .while' c body =>
    -- Tier 16. Both the condition and the body must leave every type where they found it, which
    -- is what makes the loop's fixed point trivial (`Judge.while'`).
    match chk f κ Γ I c with
    | some (_, Γc, Ic) =>
      if Γc = Γ && Ic = I then
        match chk f κ Γ I body with
        | some (_, Γb, Ib) => if Γb = Γ && Ib = I then some (.nilT, Γ, I) else none
        | none => none
      else none
    | none => none
  | f + 1, .array es =>
    match chkAll f κ Γ I es with
    | some (τs, Γ', I') => some (.arrayOf (elemTy τs), Γ', I')
    | none => none
  | f + 1, .hash pairs =>
    match chkPairs f κ Γ I pairs with
    | some (kτ, vτ, Γ', I') => some (.hashOf kτ vτ, Γ', I')
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
        | none =>
          -- `defGet?` answering `none` is no longer the same question as "this name is not a
          -- method": since `found-issues.md` §F3 it also answers `none` for a method whose
          -- body declares. `bareName` means the *name* is undefined, so it asks the raw table.
          match defDeclared? κ.defs m with
          | some _ => none
          | none =>
            -- `nameFree κ "method_missing"` is `found-issues.md` §F4: a user
            -- `method_missing` turns the miss this rule reasons from into a *return*, and
            -- the body it runs can rebind an ivar the spine threads out unchanged.
            if bareNameError? m && nameFree κ "method_missing" then some (.any, Γ, I) else none
  | _ + 1, .self' =>
    match κ.selfTy with
    | some σ => some (σ, Γ, I)
    | none => none
  | _ + 1, .const n =>
    -- Tier 13: an assigned constant first, then a declared class, then a builtin class name.
    -- The three routes are *disjoint*, not merely ordered -- `Judge`'s `constCls` and
    -- `constBuiltin` each carry `constGet? κ n = none` as a premise, because a `casgn` to a
    -- class's name really does rebind it. So this `match` could be written in any order and
    -- answer the same.
    match constGet? κ n with
    | some τ => some (τ, Γ, I)
    | none =>
      match clsGet? κ.classes n with
      | some _ => some (.clsOf n, Γ, I)
      -- Tier 16b: and a builtin *exception* class name, which `builtinCls?` deliberately does
      -- not list (`Judge.constExc`).
      | none => if builtinCls? n || excCls? n then some (.clsOf n, Γ, I) else none
  | f + 1, .cpath (some base) n =>
    -- Tier 13c/13e. The base has to *type* as a class-or-module object, not merely look like
    -- one: after `M = 5` the only rule for `.const "M"` is `constEnv` (see
    -- `Judge.constPath`). Then two disjoint routes off the owner name -- a constant in the
    -- table, or a nested class declared under the qualified name.
    match chkOwner? f κ Γ I base with
    | some (owner, Γ₁, I₁) =>
      match envGet? κ.consts (constKeyIn owner n) with
      -- Tier 13d: and not hidden by `private_constant` (`Judge.constPath`'s third premise).
      | some τ =>
        if κ.privConsts.contains (constKeyIn owner n) then none else some (τ, Γ₁, I₁)
      | none =>
        match clsGet? κ.classes (owner ++ "::" ++ n) with
        | some _ => some (.clsOf (owner ++ "::" ++ n), Γ₁, I₁)
        | none => none
    | none => none
  | f + 1, .cpathAsgn (some (.const owner)) n e =>
    -- The *write* side stays at the syntactic base, because `extendConsts` matches on it to
    -- know which key the binding lands on (`Judge.cpathAsgn`).
    if chk f κ Γ I (.const owner) = some (Ty.clsOf owner, Γ, I) then chk f κ Γ I e else none
  | f + 1, .casgn n e =>
    -- Tier 13. The *binding* is not made here: `chkSeq` makes it, via `Ctx.afterStmt`, so a
    -- `casgn` that is not a statement of a sequence types and binds nothing (`Judge.casgn`).
    match chk f κ Γ I e with
    | some (τ, Γ', I') => some (τ, Γ', I')
    | none => none
  | _ + 1, .def' _ _ _ => some (.sym, Γ, I)
  | f + 1, .module' n body =>
    match classMethods? body with
    -- Tier 10: every mixed-in name must be a declared `module` (`Judge.moduleStmt`'s second
    -- premise) -- `include` on a non-Module raises TypeError.
    -- Tier 13: and the body's constants are typed, here, at the definition site
    -- (`chkConsts`).
    | some (_, _, incs, exts, preps, cs, nst) =>
      if allModules κ.classes (incs ++ exts ++ preps) && (constGet? κ n).isNone
          && chkConsts f κ cs && chkNested f κ n nst then
        some (.any, Γ, I)
      else none
    | none => none
  | f + 1, .class' n _ body =>
    match classMethods? body with
    | some (_, _, incs, exts, preps, cs, nst) =>
      if allModules κ.classes (incs ++ exts ++ preps) && (constGet? κ n).isNone
          && chkConsts f κ cs && chkNested f κ n nst then
        some (.any, Γ, I)
      else none
    | none => none
  | f + 1, .send none m args (some (.block ps [] body)) =>
    -- An implicit-self send carrying a block literal. Two routes: `lambda`/`proc`, which
    -- *are* the block (tier 9a), and everything else, which passes it to a top-level method
    -- (tier 9b). Matched before the block-less arm because it is the only send in this
    -- fragment that carries a block at all.
    match κ.selfTy with
    | none =>
      -- `nameFree` is §F2: a toplevel `def lambda` shadows `Kernel#lambda`, so the block is
      -- an argument to *that* method and not a Proc at all.
      if (m = "lambda" || m = "proc") && args.isEmpty && nameFree κ m then
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
              match paramEnvB (some (.clos idx (envToSpine Γ') (κ.selfTy.getD .never)))
                  d.params argTys with
              | some Γb =>
                match chk f
                    { κ with
                      blockTy := some (.clos idx (envToSpine Γ') (κ.selfTy.getD .never)) }
                    Γb .ivar0 d.body with
                | some (ρ, _, Iout) =>
                  if Iout = .ivar0 then some (ρ, killAliases Γ', I') else none
                | none => none
              | none => none
            | none => none
          | none => none
        | none => none
    | some (.inst n Iself) =>
      -- Tier 11: implicit-self dispatch carrying a block (`Judge.selfCallBlk`). Disjoint from
      -- the `none` branch above by construction, which is the job `callDefBlk`'s
      -- `κ.selfTy = none` premise now does.
      match chkAll f κ Γ I args with
      | some (argTys, Γ', I') =>
        match closIdx? κ.closures ps body with
        | some idx =>
          match mroGet? κ.classes n m with
          | some (dc, d) =>
            match paramEnvB (some (.clos idx (envToSpine Γ') (κ.selfTy.getD .never)))
                d.params argTys with
            | some Γb =>
              match chk f
                  { (κ.inMethod (.inst n Iself) dc m) with
                    blockTy := some (.clos idx (envToSpine Γ') (κ.selfTy.getD .never)) }
                  Γb Iself d.body with
              | some (ρ, _, Iout) =>
                if Iout = Iself then some (ρ, killAliases Γ', I') else none
              | none => none
            | none => none
          | none => none
        | none => none
      | none => none
    | some _ => none
  | f + 1, .send none m args none =>
    -- Tier 14c: a trailing `kwargs` node is not a value, so a call that carries one takes an
    -- entirely separate route (`Judge.callDefKw`) rather than being folded into the four below.
    match splitKw? args with
    | some (pos, entries) =>
      match chkAll f κ Γ I pos with
      | some (posTys, Γ₁, I₁) =>
        match chkKw f κ Γ₁ I₁ entries with
        | some (kws, Γ', I') =>
          match defGet? κ.defs m with
          | some d =>
            -- `paramEnvK` is where a missing required keyword and an unexpected keyword are
            -- both rejected, and both really raise ArgumentError.
            match paramEnvK d.params posTys kws with
            | some Γb =>
              match chk f κ Γb .ivar0 d.body with
              | some (ρ, _, Iout) => if Iout = .ivar0 then some (ρ, Γ', I') else none
              | none => none
            | none => none
          | none => none
        | none => none
      | none => none
    | none =>
    -- An implicit-self call. Four routes, in this order, and the order is the design:
    -- strictness first (a call with a non-returning argument never dispatches, defined or
    -- not), then the *assumption* (a recursive occurrence must not re-instantiate, or the
    -- recursion never bottoms out), then the def table.
    match chkAll f κ Γ I args with
    | some (argTys, Γ', I') =>
      if argTys.contains .never then some (.never, Γ', I')
      -- Tier 16b: `raise C` / `raise C, "msg"` does not return, so its type is `.never`
      -- (`Judge.raiseCls`). Matched before the def table, which a method actually named `raise`
      -- would otherwise reach -- no rung has one.
      -- The comment above ("no rung has one") was the argument; §F6's shape makes it a
      -- premise instead, because `Judge` quantifies over contexts that do.
      else if m = "raise" && nameFree κ "raise" && nameFree κ "method_missing" then
        match argTys with
        | [.clsOf n] => if excName? κ.classes n then some (.never, Γ', I') else none
        | [.clsOf n, .cls "String"] =>
          if excName? κ.classes n then some (.never, Γ', I') else none
        | _ => none
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
                    match chk f (κ.inCtor n dc "initialize") Γb .ivar0 d.body with
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
            match chk f κ (Γb ++ blockLocals locs ++ killAliases Γ₂) I₂ (bodyResult body) with
            | some (ρ, Γb', Iout) =>
              if Iout = I₂ then
                if capIntact (envToSpine Γ₂) (Γb ++ blockLocals locs ++ killAliases Γ₂) Γb'
                then
                  match iterResult? m elem argTys ρ with
                  | some res => some (res, killAliases Γ₂, I₂)
                  | none => none
                else none
              else none
            | none => none
          | none => none
        | none => none
      | none => none
    | some (.inst n Iself, Γ₁, I₁) =>
      -- Tier 11: an instance method called with a block (`Judge.callMethodBlk`). A block with
      -- `|x; y|` locals is refused here (`locs = []`), because the block becomes a `Ty.clos`
      -- and `Clos` does not record them -- unlike the iterator route above, which types the
      -- block where it stands.
      -- Matched rather than guarded by `isEmpty` so the empty case *substitutes* `locs`, which
      -- is what makes `Judge.callMethodBlk`'s `.block ps [] body` conclusion available.
      match locs with
      | [] =>
        match chkAll f κ Γ₁ I₁ args with
        | some (argTys, Γ₂, I₂) =>
          match closIdx? κ.closures ps body with
          | some idx =>
            match mroGet? κ.classes n m with
            | some (dc, d) =>
              match paramEnvB (some (.clos idx (envToSpine Γ₂) (κ.selfTy.getD .never)))
                  d.params argTys with
              | some Γb =>
                match chk f
                    { (κ.inMethod (.inst n Iself) dc m) with
                      blockTy := some (.clos idx (envToSpine Γ₂) (κ.selfTy.getD .never)) }
                    Γb Iself d.body with
                | some (ρ, _, Iout) =>
                  if Iout = Iself then some (ρ, killAliases Γ₂, I₂) else none
                | none => none
              | none => none
            | none => none
          | none => none
        | none => none
      | _ => none
    | some (.clsOf n, Γ₁, I₁) =>
      -- Tier 11: a singleton method or module function called with a block
      -- (`Judge.callSMethodBlk`).
      match locs with
      | [] =>
        match chkAll f κ Γ₁ I₁ args with
        | some (argTys, Γ₂, I₂) =>
          match closIdx? κ.closures ps body with
          | some idx =>
            match smroGet? κ.classes n m with
            | some (dc, d) =>
              match paramEnvB (some (.clos idx (envToSpine Γ₂) (κ.selfTy.getD .never)))
                  d.params argTys with
              | some Γb =>
                match chk f
                    { (κ.inMethod (.clsOf n) dc m) with
                      blockTy := some (.clos idx (envToSpine Γ₂) (κ.selfTy.getD .never)) }
                    Γb .ivar0 d.body with
                | some (ρ, _, Iout) =>
                  if Iout = .ivar0 then some (ρ, killAliases Γ₂, I₂) else none
                | none => none
              | none => none
            | none => none
          | none => none
        | none => none
      | _ => none
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
                        | some res => some (res, killAliases Γ₃, I₃)
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
        else if m = "===" then
          -- Tier 12: `Module#===`, the form `case v when C` desugars to. Receiver must be a
          -- class object, and the class object must not override `===` (`Judge.caseEqQuery`).
          match σ, argTys with
          | .clsOf cn, [_] =>
            match smroGet? κ.classes cn "===" with
            -- `found-issues.md` §F7: `smroGet?` sees only singleton methods on `cn`, and the
            -- dispatch walks the whole eigenclass chain, so the boot `Module#===` being intact
            -- has to be checked too — and `method_missing` for the eigenclass that resolves
            -- `===` nowhere.
            | none =>
              if nameFree κ "===" && nameFree κ "method_missing" then some (.bool, Γ₂, I₂)
              else none
            | some _ => none
          -- Tier 16: any other receiver is a *value*, and `===` there is the `PrimSig` row
          -- (`case t when "pypi"` desugars to `"pypi" === t`). Written out rather than falling
          -- through to the dispatch below because this `if` has already committed to `m`.
          | _, _ =>
            match primSig? σ m argTys with
            -- §F11: a nominal receiver's *actual* class may be a declared subclass that
            -- redefines the name (`rescue StandardError => e` binds one)
            | some τ => if primDispatchOk κ.classes σ m then some (τ, Γ₂, I₂) else none
            | none => none
        else if m = "is_a?" then
          -- Tier 12. Placed *before* the receiver dispatch, and note the consequence: a
          -- receiver whose class overrides `is_a?` fails `isADispatchOk` and this arm answers
          -- `none` rather than falling through to `callMethod`. Conservative, not unsound —
          -- and recorded as a negative control.
          match argTys with
          | [.clsOf _] =>
            -- `found-issues.md` §F6: `isADispatchOk` guards the *user table* and only for
            -- `.inst` types, so the boot `is_a?` being intact has to be checked too — and
            -- `method_missing` for the receiver whose class does not resolve `is_a?` at all.
            if isADispatchOk κ.classes σ && nameFree κ "is_a?"
               && nameFree κ "method_missing" then some (.bool, Γ₂, I₂) else none
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
              -- Tier 13f: `Module#to_s` (the class's name). Reached only when `smroGet?`
              -- missed, which *is* `Judge.clsToS`'s guard: a `def self.to_s` would have been
              -- found above and dispatched to instead.
              -- `found-issues.md` §F7 again: the `smroGet?` miss above is about `n` itself,
              -- and `Module#to_s` is reached through the eigenclass chain.
              if m = "to_s" && argTys = [] && nameFree κ "to_s"
                 && nameFree κ "method_missing" then some (.cls "String", Γ₂, I₂)
              else if m = "new" then
                match ctorGet? κ.classes n with
                | some (dc, d) =>
                  match paramEnv d.params argTys with
                  | some Γb =>
                    match chk f (κ.inCtor n dc "initialize") Γb .ivar0 d.body with
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
                      (if capIntact cap (Γb ++ spineToEnv cap) Γb' then
                         some (ρ, killAliases Γ₂, I₂)
                       else none)
                    else none
                  | none => none
                | none => none
              | none => none
            else none
          | .inst n Iself =>
            -- Tier 13f: `Object#class`, matched before dispatch. `mroGet?` cannot find a
            -- user-written `class` (Ruby has no way to write one -- `class` is a keyword), so
            -- unlike `is_a?` this needs no guard beyond the arity (`Judge.classOf`).
            if m = "class" && argTys = [] && nameFree κ "class"
               && nameFree κ "method_missing" then some (.clsOf n, Γ₂, I₂)
            else
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
            | none =>
              -- Tier 10: dispatch found nothing, so `method_missing` gets asked
              -- (`Judge.callMissing`). The `objectMethod?` guard is what stops `to_s`,
              -- `inspect`, `==` and the rest of `Object`'s methods taking this route.
              if objectMethod? m then none
              else
                match mroGet? κ.classes n "method_missing" with
                | some (dc, d) =>
                  match paramEnv d.params (.sym :: argTys) with
                  | some Γb =>
                    match chk f (κ.inMethod (.inst n Iself) dc "method_missing") Γb Iself
                        d.body with
                    | some (ρ, _, Iout) => if Iout = Iself then some (ρ, Γ₂, I₂) else none
                    | none => none
                  | none => none
                | none => none
          | _ =>
            match primSig? σ m argTys with
            -- §F11: a nominal receiver's *actual* class may be a declared subclass that
            -- redefines the name (`rescue StandardError => e` binds one)
            | some τ => if primDispatchOk κ.classes σ m then some (τ, Γ₂, I₂) else none
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
                (if capIntact cap (Γb ++ spineToEnv cap) Γb' then
                   some (ρ, killAliases Γ', I')
                 else none)
              else none
            | none => none
          | none => none
        | none => none
      | none => none
    | some _ => none
    | none => none
  | f + 1, .zsuper none =>
    -- Tier 10: `super` with no argument list, restricted to a running method that takes no
    -- parameters (`Judge.zsuperCall`). The `dcls = fr.defClass` check is not redundant with
    -- dispatch -- it is how the *running* method's `Defn` is recovered, so its arity can be
    -- required empty.
    match κ.frame with
    | some fr =>
      match mroGet? κ.classes fr.recvClass fr.methName with
      | some (dcls, dcur) =>
        if dcls = fr.defClass && dcur.params.isEmpty then
          match mroList? κ.classes fr.recvClass with
          | some mro =>
            match afterInMro mro fr.defClass with
            | some rest =>
              match searchMro κ.classes rest fr.methName with
              | some (dc, d) =>
                match paramEnv d.params [] with
                | some Γb =>
                  match chk f
                      { κ with frame := some ⟨fr.recvClass, dc, fr.methName⟩ } Γb I d.body with
                  | some (ρ, _, Iout) => some (ρ, Γ, Iout)
                  | none => none
                | none => none
              | none => none
            | none => none
          | none => none
        else none
      | none => none
    | none => none
  | f + 1, .super' args none =>
    match chkAll f κ Γ I args with
    | some (argTys, Γ', I') =>
      match κ.frame with
      | some fr =>
        -- Tier 10: `super` is a search in the *receiver's* MRO, starting after the entry the
        -- running method was found in (`Judge.superCall`).
        match mroList? κ.classes fr.recvClass with
        | some mro =>
          match afterInMro mro fr.defClass with
          | some rest =>
            match searchMro κ.classes rest fr.methName with
            | some (dc, d) =>
              match paramEnv d.params argTys with
              | some Γb =>
                match chk f
                    { κ with frame := some ⟨fr.recvClass, dc, fr.methName⟩ } Γb I' d.body with
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

/-- **A class body's constants** (tier 13): each initializer must type at exactly the type
`constLitTy?` reads off its syntax, in the empty local environment, leaving it empty. The
decidable counterpart of `JudgeConsts`, premise for premise.

The equality is against the *whole* triple rather than the type alone, because `JudgeConsts`
requires the empty outgoing environment and spine too — a class body cannot leave a local
behind for the enclosing scope. -/
def chkConsts (fuel : Nat) (κ : Ctx) : List (String × Expr) → Bool
  | [] => true
  | (_, e) :: cs =>
    match fuel with
    | 0 => false
    | f + 1 =>
      match constLitTy? e with
      | some τ =>
        if chk f κ [] .ivar0 e = some (τ, [], .ivar0) then chkConsts f κ cs else false
      | none => false

/-- **A `begin`'s rescue clauses** (tier 16b): the decidable counterpart of `JudgeRescues`,
premise for premise. Returns only a type, because `Judge.begin'` reports the entry environment
whatever happens. -/
def chkRescues : Nat → Ctx → Env → Ty →
    List (List Expr × Option (TargetKind × String) × Expr) → Option Ty
  | 0, _, _, _, _ => none
  | _ + 1, _, _, _, [] => some .never
  | f + 1, κ, Γ, I, (cls, binding, handler) :: rest =>
    match rescueClasses? cls with
    | some names =>
      if names.all (fun n => excName? κ.classes n) then
        match rescueBind? names binding with
        | some Γh =>
          match chk f κ (Γh ++ Γ) I handler with
          | some (τ, Γ', I') =>
            if Γ' = Γh ++ Γ && I' = I then
              match chkRescues f κ Γ I rest with
              | some τr => some (joinT τ τr)
              | none => none
            else none
          | none => none
        | none => none
      else none
    | none => none

/-- **A call site's keyword arguments** (tier 14c): the decidable counterpart of `JudgeKw`,
which means `KwEntry.pair` only. A `**h` splat or a dynamic key answers `none`, and the
program is not typed — see `JudgeKw` for which `Ty` gap each of those is. -/
def chkKw : Nat → Ctx → Env → Ty → List KwEntry → Option (List (String × Ty) × Env × Ty)
  | 0, _, _, _, _ => none
  | _ + 1, _, Γ, I, [] => some ([], Γ, I)
  | f + 1, κ, Γ, I, .pair k v :: es =>
    match chk f κ Γ I v with
    | some (τ, Γ₁, I₁) =>
      match chkKw f κ Γ₁ I₁ es with
      | some (kws, Γ₂, I₂) => some ((k, τ) :: kws, Γ₂, I₂)
      | none => none
    | none => none
  | _ + 1, _, _, _, _ => none

/-- `chk` on a **class-or-module-object-valued** expression, reporting the name it names.

Extracted as its own function purely so that `chk`'s `cpath` arm matches on a flat
`Option (String × Env × Ty)` rather than on a `Ty` nested inside a tuple inside an `Option`:
`ChkSound.lean` proceeds by one `split` per arm, and a three-deep pattern there makes the
match compiler build a splitter that the proof then has to be written against. This is a
readability choice with no semantic content -- `chkOwner?_sound` is the whole of it. -/
def chkOwner? : Nat → Ctx → Env → Ty → Expr → Option (String × Env × Ty)
  | 0, _, _, _, _ => none
  | f + 1, κ, Γ, I, base =>
    match chk f κ Γ I base with
    | some (.clsOf owner, Γ₁, I₁) => some (owner, Γ₁, I₁)
    | _ => none

/-- **A class body's nested declarations** (tier 13e): the decidable counterpart of
`JudgeNested`, premise for premise, recursing into each nested body's own nested list.

Fuel does double duty here — it bounds the nesting depth as well as `chk`'s recursion — and
the `0` case is `false` rather than `true`, because running out means the obligation was not
discharged.

The fuel is matched **first**, before the list, and both recursive calls spend a unit: that is
what keeps this definition structurally recursive on `Nat` rather than well-founded, and a
well-founded one would not kernel-reduce, which `Rungs.lean`'s per-rung `rfl` needs. The same
constraint is why `chkOwner?` matches on fuel it does not otherwise need. -/
def chkNested : Nat → Ctx → String → Nested → Bool
  | 0, _, _, _ => false
  | _ + 1, _, _, [] => true
  | f + 1, κ, pfx, (_, n, body) :: rest =>
    match classMethods? body with
    | some (_, _, incs, exts, preps, cs, nst) =>
      allModules κ.classes (incs ++ exts ++ preps)
        && (envGet? κ.consts (constKeyIn pfx n)).isNone
        && chkConsts f κ cs
        && chkNested f κ (pfx ++ "::" ++ n) nst
        && chkNested f κ pfx rest
    | none => false

/-- Key-then-value `chk` over a hash literal's pairs. Returns only the outgoing states:
and (tier 17b) the joined key and value types, folded as `JudgePairs` folds them. Until then
the types were discarded, because there was no `hashOf` to put them in. -/
def chkPairs (fuel : Nat) (κ : Ctx) (Γ : Env) (I : Ty)
    (ps : List (Expr × Expr)) : Option (Ty × Ty × Env × Ty) :=
  match fuel, ps with
  | 0, _ => none
  | _ + 1, [] => some (.never, .never, Γ, I)
  | f + 1, (k, v) :: ps =>
    match chk f κ Γ I k with
    | some (σ, Γ₁, I₁) =>
      match chk f κ Γ₁ I₁ v with
      | some (ν, Γ₂, I₂) =>
        match chkPairs f κ Γ₂ I₂ ps with
        | some (kr, vr, Γ₃, I₃) => some (joinT σ kr, joinT ν vr, Γ₃, I₃)
        | none => none
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
  | f + 1, .if' c (.nxt none) none :: e' :: es =>
    -- Tier 16's `next if …` guard (`JudgeSeq.nextGuard`), matched before the generic arm for
    -- the same reason the `return` guard is: the rest of the sequence runs only on the path the
    -- `next` did not take, and the sequence's value is `nil` on the path it did.
    match chk f κ Γ I c with
    | some (_, Γc, Ic) =>
      match chkSeq f κ (narrowEnvs κ c Γc).2 (narrowSpine κ c Ic).2 (e' :: es) with
      | some (τ, Γ', I') => some (joinT .nilT τ, Γ', I')
      | none => none
    | none => none
  | f + 1, .if' c (.ret (some r)) none :: e' :: es =>
    -- Tier 12's guard clause (`Judge.guard`). Matched *before* the generic `cons` arm, and
    -- only in non-final position — a `return … if …` as the whole body of a sequence still has
    -- no rule, because `.ret` has none.
    match chk f κ Γ I c with
    | some (_, Γc, Ic) =>
      match chk f κ (narrowEnvs κ c Γc).1 (narrowSpine κ c Ic).1 r with
      | some (ρ, _, Ir) =>
        if Ir = (narrowSpine κ c Ic).1 then
          match chkSeq f κ (narrowEnvs κ c Γc).2
              (narrowSpine κ c Ic).2 (e' :: es) with
          | some (τ, Γ', I') => some (joinT ρ τ, Γ', I')
          | none => none
        else none
      | none => none
    | none => none
  | f + 1, e :: e' :: es =>
    match chk f κ Γ I e with
    | some (σ, Γ₁, I₁) => chkSeq f (κ.afterStmt e σ) Γ₁ I₁ (e' :: es)
    | none => none

end

/-- The starting context: no classes, no methods, no assumptions, no `self`. Every
emptiness is load-bearing, and for a different reason — the two syntax tables because
nothing is declared before a program's first statement, the assumption table because a
derivation carrying one is only a conditional claim (`AsmTable`), and `frame`/`selfTy`
because a program's top level is inside no method and runs somewhere `self` is not an
instance of anything this judgment models. The constant table (tier 13) is empty for the
first of those reasons: a program's first statement is the first thing that could assign
one. -/
def ctx0 : Ctx := ⟨[], [], [], none, [], none, none, [], []⟩

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
