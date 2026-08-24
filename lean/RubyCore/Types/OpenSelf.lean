import RubyCore.Types.Core
import RubyCore.Types.Assn

/-!
# R4 — open self: typing a method body against an unresolved receiver

`homebrew/assertion-language.md` §4.3, §7.2's row case, §7.3, §12 R4. The rung
the ledger ranks highest among the ones with a metatheory cost, because the
fourteen `vcall`-blocked slice bodies are all of this shape:

```ruby
def hash
  value.hash          # `value` is a user-defined accessor with no declared row
end
```

`infer` types this only if `Version#value` already has a row. `inferOpen` types it
with **no row at all**, and emits the row it would need as a *precondition on its
own class*:

```
self : ⟨ value : () → ⟨ hash : () → Integer | ρ₂ ⟩ | ρ₁ ⟩   ⊢   hash : () → Integer
```

## The soundness stance, and it is what makes this rung cheap

This function is **untrusted**, and `Proof/Static/OpenSelf.lean` proves the one
theorem that makes it safe to run:

```
inferOpen … = .ok τ Γ' s'   ∧   the residual store is satisfied by θ   ⟹
  infer … = some (τ.subst θ, …)          -- `inferOpen_factors`
```

*Open-self typing factors through nominal typing.* So R4 adds **no `KontOk`
constructor and no consecution case** — `HANDOFF.md`'s constraint 4 does not fire,
because `infer` is unchanged and `inferOpen` is a front end whose every accept is
re-derived as an `infer` accept. That is the same certifying-not-trusted stance
§8.4 takes, applied to the inference function rather than to the entailment.

**And the chain stops at `infer`.** `check` does not call `inferOpen`, so R4 as
landed accepts no new *programs* and `--assn`'s `accept` means *types under this
precondition*, never *is safe*. See `Proof/Static/OpenSelf.lean`'s header.

## Scope: method bodies

`inferOpen` covers exactly the constructs a **method body** may contain, and
refuses `def'` and `class'` outright. That is not a simplification, it is the
existing rule: `infer`'s `def` arm already requires `defFree body` before it will
add a row (L161's `infer_mono` hypothesis), so a body that declares a method is
already outside the fragment. Because bodies are `def`-free, the declaration table
does not change inside one — which is why `inferOpen` threads a store and not a
table, and why the factoring theorem's conclusion has `D` in both positions.
-/

namespace RubyCore.Types

/-! ## 1. The open judgement's three components -/

/-- Locals, typed in the extended language: a local may hold a value whose type
    is still a variable, because it may have been assigned the result of a call on
    an unresolved receiver. -/
abbrev AEnv := List (String × ATy)

def aenvGet? (Γ : AEnv) (x : String) : Option ATy :=
  (Γ.find? (·.1 == x)).map (·.2)

/-- A member's key always resolves — `envGet?_of_mem`'s twin (L236). -/
theorem aenvGet?_of_mem {Γ : AEnv} {e : String × ATy} (he : e ∈ Γ) :
    ∃ a, aenvGet? Γ e.1 = some a := by
  unfold aenvGet?
  cases hf : Γ.find? (fun p => p.1 == e.1) with
  | none => exact absurd (List.find?_eq_none.mp hf e he) (by simp)
  | some p => exact ⟨p.2, by simp [hf]⟩

/-- **The open-self `SubEnv` check** (L227) — `subEnvB`'s twin at `AEnv`, and the reason
    it is a *separate* function rather than `subEnvB` after substitution: the check runs in
    the open pass, where the types are still variables, so it compares `ATy`s. What makes
    it sound is that it is **stronger** than the nominal check pointwise: an entry that
    matches syntactically matches under every `θ` (`subAEnvB_subst`). -/
def subAEnvB (Γ Γ' : AEnv) : Bool :=
  -- L236: each entry's *lookup* rather than its payload, for `subEnvB`'s reason — an
  -- `AEnv` is an association list, so a shadowed entry must not make the check fail.
  Γ.all fun e => aenvGet? Γ' e.1 == aenvGet? Γ e.1

/-- Order is canonical, as in `envSet`, so that environment *equality* is a usable
    check — the `if`-merge and the loop-stability condition both need it, and the
    factoring theorem needs `substEnv θ` to commute with it. -/
def aenvSet : AEnv → String → ATy → AEnv
  | [], x, τ => [(x, τ)]
  | (y, σ) :: Γ, x, τ => if y == x then (x, τ) :: Γ else (y, σ) :: aenvSet Γ x τ

/-- §7's `κ`, in open-self mode: the definee's class name (unchanged from
    `FrameCtx.cls`), and the **variable** standing for `self`'s type — §7.3's
    `α fresh`, and the field §7 adds to `κ` as `κ.selfTy`. -/
structure OCtx where
  cls : String
  self : TyVar
  -- **L210: the running method's name**, `FrameCtx.meth`'s open counterpart. It is
  -- here rather than a parameter of `inferBody` because the *factoring* theorem has to
  -- name it: the nominal context `Factors` concludes at is built out of this one, and
  -- `UserConforms` now fixes its `meth`. Nothing in `inferOpen` reads it yet — `super`
  -- is the arm that will.
  meth : Option String := none
  /-- **The running method's parameter types, open** (L214) — `FrameCtx.params`'
      counterpart, and unlike `meth` it is *populated*: `openParams` binds each required
      positional to a fresh type variable, and this is that list, in order. So `zsuper`'s
      argument types are exactly the variables the body's own parameters were opened at,
      which is why the open front end can type a `zsuper` in a body with parameters where
      the nominal rule can only reach one with none.

      `Option` for `FrameCtx.params`' reason, and `openParamTys` is what decides it. -/
  params : Option (List ATy) := none
deriving DecidableEq, Repr, Inhabited

/-- The store, plus the fresh-variable counter. Threaded exactly as `D` is (§7),
    for L160's reason. -/
structure OState where
  st : Store := {}
  fresh : TyVar := 0
  /-- **The types every `return` in this body handed back** (L201), newest first.

      A body's return type is what the *tail* answers, and a `return e` has to agree
      with it — but the open pass meets the `return` before it knows the tail. So the
      pass **accumulates** and `inferBody` checks at the end, which is the same shape
      the store already has: `Factors`' `StoreLe s'.st stF` premise is a fact about the
      *final* state, and this adds a second one beside it.

      `List ATy` and not `Ty`: a returned type may still be a variable. -/
  rets : List ATy := []
deriving Repr, Inhabited

/-- The judgement's answer. Three constructors rather than an `Option`, because
    §11's whole point is that `unknown` must **carry the atom it wanted** — and an
    explanation computed by a second function would be the same hand-maintained
    copy that has made `fragment-gap.py`'s `SUPPORTED` wrong twice. -/
inductive OResult where
  | ok (τ : ATy) (Γ : AEnv) (s : OState)
  /-- The requirement that could not be met. `τ ~ n : (params) → _`. -/
  | missing (τ : ATy) (n : String) (params : List ATy)
  /-- Outside `infer`'s domain — the construct census's `unknown`. -/
  | outOfFragment (head : String)
deriving Repr

/-- The argument traversal's answer (L175). A separate type from `OResult`
    because it carries a *list* of types — and it keeps the failure as an
    `OResult` rather than collapsing it, because §11's whole value is in *which*
    construct inside an argument stopped the body. -/
inductive OArgs where
  | ok (τs : List ATy) (Γ : AEnv) (s : OState)
  /-- The requirement one argument could not meet, forwarded verbatim. -/
  | missing (τ : ATy) (n : String) (params : List ATy)
  /-- The construct inside one argument that left the fragment. -/
  | outOfFragment (head : String)
deriving Repr

/-! ## 2. `inferOpen`

Arm for arm, `Types/Core.lean`'s `infer`, with two differences and no others:

* **`self`** has a type in every activation — the variable `ctx.self` — where
  `infer` refuses when `selfCls` is `none`;
* **a send whose receiver's type is a variable** records a requirement instead of
  reading the table (§7.2's second `require` clause).

Everything else, including `isSelf`'s exclusion of a literal `self` receiver
(L164), is copied deliberately: the factoring theorem is an arm-by-arm induction,
and an arm that differs for no reason is an arm whose proof has to be invented. -/
/-- **The block-send rule's captured environment, from the open side** (L258): the
    names of `Γ`, all at `.any`. Equal to `anyEnv (substEnv θ Γ)` at every `θ` — which
    is the whole reason the block body can be handed to the nominal `infer`. -/
def anyOf (Γ : AEnv) : Env := Γ.map (fun e => (e.1, Ty.any))

mutual

def inferOpen (D : Decls) (Γ : AEnv) (e : Expr) (ctx : OCtx) (il : Option AEnv) (s : OState) : OResult :=
  match e with
  | .int _ => .ok (.nom .int) Γ s
  | .tru => .ok (.nom .bool) Γ s
  | .fls => .ok (.nom .bool) Γ s
  | .nil => .ok (.nom .nilT) Γ s
  | .str _ => .ok (.nom (.cls "String")) Γ s
  | .sym _ => .ok (.nom .sym) Γ s
  | .var .lvar x =>
    match aenvGet? Γ x with
    | some τ => .ok τ Γ s
    | none => .outOfFragment "unbound-lvar"
  -- **`self` always has a type here**, and that is the rung. `infer` answers
  -- `none` in a class body because `self` is the class object; inside a method
  -- body it answers `.cls c`, and this answers the variable that *stands for*
  -- `.cls c` before the class is known.
  | .self' => .ok (.var ctx.self) Γ s
  -- **A constant read** (L189), keyed on the same table as `infer`'s arm — which
  -- since L195 is `D.consts` rather than a global list, so the two agree by
  -- construction and the factoring theorem's case is still one `simp`.
  | .const n =>
    match constTy? D n with
    | some τ => .ok (.nom τ) Γ s
    -- **A missing *declaration*, not a missing rule** (L197), and it is the same
    -- correction L196 made for `@x`: `infer` has a `.const` arm (L189, table-keyed
    -- since L195), so a name the table does not carry is refused by the **table**,
    -- which is the category the census counts separately.
    --
    -- The `::` prefix is `@`'s: the atom vocabulary is method rows, so the marker is
    -- what says which kind of declaration is wanted. The receiver is
    -- `T.class_of(Object)` because that is literally what `ConstOk` obliges —
    -- `constOwn h Boot.objectId n` — so the printed atom reads *Object must declare
    -- the constant `n`*.
    --
    -- **What this does *not* claim** is that the declaration is satisfiable, and one
    -- name in the slice shows the difference: `Regexp` can never be declared, because
    -- `ConstOk` wants `ValueTy h v (.clsOf "Regexp")` and `classRecv` excludes
    -- `Boot.regexpId` (L106). The `needed:` category has never claimed satisfiability
    -- — `slice-verdict.md` §1 says an accept reads *types under this precondition*,
    -- never *is safe*, and the same reading applies to a requirement. Treating the
    -- constant case as special would be *less* honest than treating it like every
    -- other missing declaration.
    | none => .missing (.nom (.clsOf "Object")) ("::" ++ n) []
  -- **The `vcall`** — §4.3's construct, and the one the ledger is about. No table
  -- read at all: the requirement goes into the row on `ctx.self`.
  | .vcall mname =>
    match requireRow s.st ctx.self mname [] s.fresh with
    | some (τ, st') => .ok τ Γ { s with st := st', fresh := s.fresh + 1 }
    | none => .missing (.var ctx.self) mname []
  -- **The written receiverless call** (L170), `foo()` — the `vcall` arm's twin,
  -- and the same requirement on `ctx.self`. `infer`'s new arm reads
  -- `sigOf D (.cls c) mname` exactly as its `vcall` arm does, so the factoring
  -- theorem's case is the `vcall` case verbatim.
  | .send none mname [] none =>
    match requireRow s.st ctx.self mname [] s.fresh with
    | some (τ, st') => .ok τ Γ { s with st := st', fresh := s.fresh + 1 }
    | none => .missing (.var ctx.self) mname []
  -- **The unary written receiverless call** (L171). One subexpression, then the
  -- requirement on `ctx.self` — the `vcall` arm's shape with an argument, and the
  -- receiver is still the variable that stands for `self`.
  | .send none mname (arg :: args) none =>
    match inferOpenArgs D Γ (arg :: args) ctx il s with
    | .ok τs Γ₁ s₁ =>
      match requireRow s₁.st ctx.self mname τs s₁.fresh with
      | some (τ, st') => .ok τ Γ₁ { s₁ with st := st', fresh := s₁.fresh + 1 }
      | none => .missing (.var ctx.self) mname τs
    | .missing τ n ps => .missing τ n ps
    | .outOfFragment h => .outOfFragment h
  | .vasgn .lvar x rhs =>
    match inferOpen D Γ rhs ctx il s with
    | .ok τ Γ₁ s₁ => .ok τ (aenvSet Γ₁ x τ) s₁
    | r => r
  -- **`@x = e`** (L191). No guard here, and none is needed: `inferOpen` only ever
  -- runs on a *method body*, so the nominal context it factors into always has
  -- `selfCls = some ctx.cls` (`Factors`) — the open front end's `self` is a type
  -- variable precisely because there is one. So the arm is the right-hand side's
  -- answer, unchanged, and the factoring case is "one subexpression".
  | .vasgn .ivar x rhs =>
    match inferOpen D Γ rhs ctx il s with
    | .ok τ Γ₁ s₁ =>
      -- **A *declared* ivar is refused here** (L196), and the reason is the open
      -- setting rather than the rule: the nominal write checks `subTy τ σ`, and `τ`
      -- may be a type *variable* at this point, so there is nothing to decide against.
      -- The undeclared case is L191's rule unchanged. Nothing is lost today — no
      -- table the tool ships has an ivar row — and what would fix it is the same
      -- constraint the row mechanism already has for method signatures.
      match ivarTy? D ctx.cls x with
      | some _ => .outOfFragment "iasgn-declared"
      | none => .ok τ Γ₁ s₁
    | r => r
  -- **`@x`** (L196). Declared, and the read is the nominal rule's; undeclared, and it
  -- is a **missing declaration** rather than a missing rule — which is the whole
  -- point of the rung, because that is the category the census counts separately.
  -- The printed atom is `α ~ @x : () → σ`, and the `@` is what says which kind of
  -- declaration is wanted.
  -- **`return e`** (L201). The pass records the returned type and answers `.nom .nilT`
  -- — the value never reaches this continuation, so the answer is free and `.nilT` is
  -- what the nominal rule answers too. What makes the record *checkable* is
  -- `inferBody`, which compares every entry against the body's own answer.
  --
  -- A bare `return` records `nilT`, which is exactly what the nominal rule's
  -- `subTy .nilT σ` check reads.
  | .ret e =>
    match e with
    | some e' =>
      match inferOpen D Γ e' ctx il s with
      | .ok τ Γ₁ s₁ => .ok (.nom .nilT) Γ₁ { s₁ with rets := τ :: s₁.rets }
      | r => r
    | none => .ok (.nom .nilT) Γ { s with rets := .nom .nilT :: s.rets }
  | .var .ivar x =>
    match ivarTy? D ctx.cls x with
    | some σ => .ok (.nom (mkNilable σ)) Γ s
    | none => .missing (.var ctx.self) ("@" ++ x) []
  -- **A literal `self` receiver is admitted** (L172), and `inferOpen` gives it the
  -- variable `ctx.self` — so `self.foo(x)` records a requirement on the definee's
  -- class exactly as `foo(x)` does.
  -- **Any positive arity** (L175), mirroring `infer`'s arm: the argument list is
  -- traversed by `inferOpenArgs` and matched against the whole parameter list, or
  -- — on a variable receiver — recorded as a row requirement with that many
  -- parameters.
  | .send (some recv) mname (arg :: args) none =>
    match inferOpen D Γ recv ctx il s with
    | .ok τr Γ₁ s₁ =>
      match inferOpenArgs D Γ₁ (arg :: args) ctx il s₁ with
      | .ok τs Γ₂ s₂ =>
        match τr with
        | .nom t =>
          match sigOf D t mname with
          | some (ps, τret) =>
            if τs == ps.map ATy.nom then .ok (.nom τret) Γ₂ s₂
            else .missing (.nom t) mname τs
          | none => .missing (.nom t) mname τs
        | .var α =>
          match requireRow s₂.st α mname τs s₂.fresh with
          | some (τ, st') => .ok τ Γ₂ { s₂ with st := st', fresh := s₂.fresh + 1 }
          | none => .missing (.var α) mname τs
        -- **A nilable receiver is refused, not recorded** (L193b), and the label says
        -- which rule is missing rather than which row: no row can ever be promised on
        -- a nilable — the receiver may be `nil` — which is `tyClassNames .nilable = []`
        -- arriving in the front end. What this position wants is *narrowing*
        -- (`x.nil?`, `if x`), and that is `PLAN.md` W5 T3.
        -- **L260: a nilable receiver dispatches by union**, and this is the arm the
        -- census's `nilable-receiver` line was. See the arity-zero arm below for the
        -- reasoning; the only difference here is the argument list.
        | .nilOf a =>
          match a with
          | .nom t =>
            match sigOf D (mkNilable t) mname with
            | some (ps, τret) =>
              if τs == ps.map ATy.nom then .ok (.nom τret) Γ₂ s₂
              else .missing (.nom (mkNilable t)) mname τs
            | none =>
              match sigOf D .nilT mname with
              | none => .missing (.nom .nilT) mname τs
              | some _ => .missing (.nom t) mname τs
          | _ =>
            match sigOf D .nilT mname with
            | none => .missing (.nom .nilT) mname τs
            | some _ => .outOfFragment "nilable-receiver"
      | .missing τ n ps => .missing τ n ps
      | .outOfFragment h => .outOfFragment h
    | r => r
  | .send (some recv) mname [] none =>
    match inferOpen D Γ recv ctx il s with
    | .ok τr Γ₁ s₁ =>
      match τr with
      | .nom t =>
        match sigOf D t mname with
        | some ([], τret) => .ok (.nom τret) Γ₁ s₁
        | _ => .missing (.nom t) mname []
      | .var α =>
        match requireRow s₁.st α mname [] s₁.fresh with
        | some (τ, st') => .ok τ Γ₁ { s₁ with st := st', fresh := s₁.fresh + 1 }
        | none => .missing (.var α) mname []
      -- **L260: a nilable receiver dispatches by union.** `x&.m` desugars to
      -- `t = x; if t.nil? then nil else t.m`, so the blocker the census called
      -- `nilable-receiver` is a plain send at a `.nilable σ` — and the sound reading is
      -- the standard one: admissible when **both** arms of the union declare the method
      -- at the same signature, which is what `sigOf` now answers (L260).
      --
      -- The nil arm is checked *first*, because it is the one that is almost always
      -- missing and it is the honest atom to name: at `severity&.to_s&.upcase` the
      -- checker asks for `NilClass ▷ upcase`, which is exactly what a union-typed
      -- checker says.
      --
      -- A receiver whose *under* type is still a variable is out of the fragment rather
      -- than a row requirement: the requirement would have to pin `θ α` to a
      -- non-nilable, and `SatStore`'s row clause is stated over `sigOf`, which by
      -- construction cannot say that.
      | .nilOf a =>
        match a with
        | .nom t =>
          match sigOf D (mkNilable t) mname with
          | some ([], τret) => .ok (.nom τret) Γ₁ s₁
          | _ =>
            match sigOf D .nilT mname with
            | none => .missing (.nom .nilT) mname []
            | some _ => .missing (.nom t) mname []
        | _ =>
          match sigOf D .nilT mname with
          | none => .missing (.nom .nilT) mname []
          | some _ => .outOfFragment "nilable-receiver"
    | r => r
  -- **A send with a block** (L258), the open counterpart of `infer`'s L257 arm.
  --
  -- The block's body is checked by the **nominal** `infer`, not by a recursive
  -- `inferOpen`. That is not a shortcut: the rule erases the captured environment to
  -- `.any` at *every* name (`anyEnv`), so by the time the body is reached there is
  -- nothing open left in it — the parameter's type, the block's return type and the
  -- send's answer all come from the declaration, which is nominal. So this arm needs
  -- no `inBlock` channel on `OCtx` and no new guard on any other arm; the factoring
  -- theorem's case is the observation that `anyEnv (substEnv θ Γ₁)` does not mention
  -- `θ` (`anyOf_subst`).
  --
  -- A receiver with no such declaration is a missing **declaration**, not a missing
  -- rule — `blockSend?` is exactly the question "is there one", and the census counts
  -- the two in different columns.
  | .send (some recv) mname [] (some (.block ps ls body)) =>
    match inferOpen D Γ recv ctx il s with
    | .ok τr Γ₁ s₁ =>
      match τr with
      | .nom t =>
        match blockSend? D t mname ps ls with
        | some (x, σp, βret, τret) =>
          match infer D ((x, σp) :: anyOf Γ₁) body false (blockCtx { cls := ctx.cls }) with
          | some (τb, Γb', D₂) =>
            if subTy τb βret = true ∧ D₂ = D ∧
                subEnvB ((x, σp) :: anyOf Γ₁) Γb' = true then
              .ok (.nom τret) Γ₁ s₁
            else .outOfFragment "send-block-body"
          | none => .outOfFragment "send-block-body"
        | none => .missing (.nom t) mname []
      | .var α => .missing (.var α) mname []
      | .nilOf _ => .outOfFragment "nilable-receiver"
    | r => r
  -- **A send with arguments *and* a block** (L259) — the open counterpart of the
  -- nominal arity-`n` arm, and the same economy: the body goes to `infer`.
  | .send (some recv) mname (arg :: args) (some (.block ps ls body)) =>
    match inferOpen D Γ recv ctx il s with
    | .ok τr Γ₁ s₁ =>
      match inferOpenArgs D Γ₁ (arg :: args) ctx il s₁ with
      | .ok τs Γ₂ s₂ =>
        match τr with
        | .nom t =>
          match blockSendA? D t mname ps ls with
          | some (x, σp, βret, dps, τret) =>
            match infer D ((x, σp) :: anyOf Γ₂) body false (blockCtx { cls := ctx.cls }) with
            | some (τb, Γb', D₂) =>
              if τs == dps.map ATy.nom ∧ subTy τb βret = true ∧ D₂ = D ∧
                  subEnvB ((x, σp) :: anyOf Γ₂) Γb' = true then
                .ok (.nom τret) Γ₂ s₂
              else .outOfFragment "send-block-body"
            | none => .outOfFragment "send-block-body"
          | none => .missing (.nom t) mname τs
        | .var α => .missing (.var α) mname τs
        | .nilOf _ => .outOfFragment "nilable-receiver"
      | .missing τ n ps => .missing τ n ps
      | .outOfFragment h => .outOfFragment h
    | r => r
  -- A body that declares a method is outside the fragment already (`infer`'s own
  -- `defFree` requirement); refusing here keeps the factoring theorem's `D` fixed.
  | .def' _ _ _ => .outOfFragment "def"
  | .class' _ _ _ => .outOfFragment "class"
  -- **An array literal** (L174). The element types are erased, so this is
  -- `inferOpenSeq` with a constant answer — the same reuse of the sequence
  -- traversal `infer`'s own arm makes.
  | .array es =>
    -- L230: `inferOpenElems`, the traversal that admits a splat element — the mirror of
    -- the nominal side's `inferElems`, and the only place a splat is in the fragment.
    match inferOpenElems D Γ es ctx il s with
    | .ok _ Γ' s' => .ok (.nom (.cls "Array")) Γ' s'
    | r => r
  | .seq es => inferOpenSeq D Γ es ctx il s
  | .if' c t els =>
    match inferOpen D Γ c ctx il s with
    | .ok _ Γ₁ s₁ => inferOpenIf D Γ₁ t els ctx il s₁
    | r => r
  | .while' c body =>
    -- **L222: both subexpressions run at `il := true`.** It has to be both, because
    -- `evalExpr` pushes a `whileCondK` for the condition too, so a `next` there has the same
    -- target. The flag is an *explicit parameter* rather than a field of `OCtx` or a
    -- projection of `s`, and L220–L222 measured why: `ctx` is a **fixed** parameter of the
    -- three open-self inductions (generalizing it moves `hself` into the motive), and a flag
    -- read off `s` makes every multi-subexpression arm's IHs mention a *different expression*.
    -- A parameter is an induction target, so every IH mentions it as a variable.
    match inferOpen D Γ c ctx (some Γ) s with
    | .ok _ Γ₁ s₁ =>
      if Γ₁ = Γ then
        match inferOpen D Γ body ctx (some Γ) s₁ with
        | .ok _ Γ₂ s₂ => if Γ₂ = Γ then .ok (.nom .nilT) Γ s₂ else .outOfFragment "while"
        | r => r
      else .outOfFragment "while"
    | r => r
  -- **`::n`** (L203), the absolute constant read — `.const`'s arm with the cref walk
  -- removed, and a miss is a **needed declaration** rather than a refusal, exactly as
  -- L197 made it for `.const`. On the slice the atom is almost always `::Regexp`,
  -- which is a requirement that can never be satisfied (`classRecv` excludes that id,
  -- L106) — and saying so is the point: the body has crossed from the checker's
  -- problem to the table's.
  | .cpath none n =>
    match constTy? D n with
    | some τ => .ok (.nom τ) Γ s
    | none => .missing (.nom (.clsOf "Object")) ("::" ++ n) []
  -- **`C::n`** (L205). The base has to resolve to a *class object* — a type variable
  -- is refused rather than constrained, because the store's requirements are rows and
  -- "is the class object named `C`" is not a row — and an undeclared pair is a needed
  -- declaration, rendered at the container's type so the atom says which namespace it
  -- is about.
  | .cpath (some base) n =>
    match inferOpen D Γ base ctx il s with
    | .ok (.nom (.clsOf cname)) Γ₁ s₁ =>
      match scopedConstTy? D cname n with
      | some τ => .ok (.nom τ) Γ₁ s₁
      | none => .missing (.nom (.clsOf cname)) ("::" ++ n) []
    | .ok _ _ _ => .outOfFragment "cpath-base"
    | r => r
  -- **A float literal** (L202), and it is here for `infer`'s reason: the only case
  -- after it in `inferOpen.induct` is the catch-all, so no existing case number moves.
  | .flt _ => .ok (.nom .float) Γ s
  -- **Bare `super`** (L214), and it is the arm below with the argument list read off the
  -- context. No `inferOpenArgs`, so no threading: the types are `ctx.params`, the
  -- variables `openParams` opened the body's own parameters at.
  | .zsuper none =>
    match ctx.meth, ctx.params with
    | some mn, some ps =>
      if mn ≠ "" then
        match superDecl? D ctx.cls mn with
        | some dd =>
          if ps == dd.params.map ATy.nom then .ok (.nom dd.ret) Γ s
          else .missing (.nom (.cls ctx.cls)) ("super:" ++ mn) ps
        | none => .missing (.nom (.cls ctx.cls)) ("super:" ++ mn) ps
      else .outOfFragment "super-outside-method"
    -- `ctx.params = none` is a parameter shape `zsuperArgs` cannot reconstruct, so the
    -- refusal names the shape rather than the rule.
    | _, _ => .outOfFragment "zsuper-param-shape"
  -- **`super(args)`** (L213), and it is the *nominal-receiver* send arm's shape at a
  -- different table: the class is known (it is `ctx.cls`, the class the body is written
  -- in), so there is no row to *record* — a `super` cannot constrain a type variable,
  -- because its receiver is `self` and its target is fixed by the chain. So an
  -- undeclared `(class, method)` pair is a **needed declaration**, rendered
  -- `T.class_of(C) ~ super:m`, exactly as `::n`'s miss is.
  --
  -- Placed after `.flt` for the same reason `.flt` is placed where it is.
  --
  -- **Split by arity, like the nominal rule**, and for the discipline's reason rather
  -- than the machine's: `inferOpen_factors` is indexed by `inferOpen.induct`'s cases,
  -- and a single arm over `args` would have to case-split on the list *inside* the
  -- proof to reach the two nominal arms. One open arm per nominal arm keeps the
  -- factoring one rewrite each.
  | .super' [] none =>
    match ctx.meth with
    | some mn =>
      if mn ≠ "" then
        match superDecl? D ctx.cls mn with
        | some dd =>
          if dd.params.isEmpty then .ok (.nom dd.ret) Γ s
          else .missing (.nom (.cls ctx.cls)) ("super:" ++ mn) []
        | none => .missing (.nom (.cls ctx.cls)) ("super:" ++ mn) []
      else .outOfFragment "super-outside-method"
    | none => .outOfFragment "super-outside-method"
  | .super' (arg :: args) none =>
    match ctx.meth with
    | some mn =>
      if mn ≠ "" then
        match inferOpenArgs D Γ (arg :: args) ctx il s with
        | .ok τs Γ₁ s₁ =>
          match superDecl? D ctx.cls mn with
          -- `==` against the declared list, not `subATy`, for the nominal-receiver
          -- arm's reason (L175): the open side has no substitution yet, so a *witness*
          -- that the argument types are below the declared ones is not available —
          -- equality is, and `ATy.subst_nom_comp` is what makes the factoring see it.
          | some dd =>
            if τs == dd.params.map ATy.nom then .ok (.nom dd.ret) Γ₁ s₁
            else .missing (.nom (.cls ctx.cls)) ("super:" ++ mn) τs
          | none => .missing (.nom (.cls ctx.cls)) ("super:" ++ mn) τs
        | .missing τ n ps => .missing τ n ps
        | .outOfFragment h => .outOfFragment h
      else .outOfFragment "super-outside-method"
    | none => .outOfFragment "super-outside-method"
  -- **`$x`** (L228), and the miss is a **needed declaration** — the category the census
  -- counts separately, and the right one here: the rule exists, the table is silent. The
  -- atom is rendered at `T.class_of(Object)` for `::n`'s reason (L203): a global has no
  -- receiver at all, so the only honest container is the toplevel.
  | .var .gvar x =>
    match plainGlobal x with
    | true =>
      match globalTy? D x with
      | some σ => .ok (.nom (mkNilable σ)) Γ s
      | none => .missing (.nom (.clsOf "Object")) x []
    | false => .outOfFragment "gvar-special"
  -- **`$x = e`** (L228). Unlike the ivar write (L196), a *declared* global is the only
  -- one the rule admits — so the open arm cannot simply defer: it has to decide
  -- `subATy τ (.nom σ)`, which is exactly `subATy`'s job and is sound at every
  -- substitution (`subATy_subst`). A type *variable* on the right-hand side is refused
  -- rather than constrained, for `iasgn-declared`'s reason: the store's requirements are
  -- rows, and "is a subtype of `σ`" is not a row.
  | .vasgn .gvar x rhs =>
    match plainGlobal x with
    | true =>
      match inferOpen D Γ rhs ctx il s with
      | .ok τ Γ₁ s₁ =>
        match globalTy? D x with
        | some σ => if subATy τ (.nom σ) then .ok τ Γ₁ s₁ else .outOfFragment "gasgn-type"
        | none => .missing (.nom (.clsOf "Object")) x []
      | r => r
    | false => .outOfFragment "gvar-special"
  -- **A bare `next`** (L227), the nominal rule's mirror — the guard on `il` and the
  -- environment check, and nothing else. Two refusals rather than one because they say
  -- different things: `next-outside-loop` is a `next` with no enclosing `while`, where the
  -- machine is `.stuck`; `next-env` is a loop the *body* has widened past its condition's
  -- environment, which is a `LoopOk` failure one construct earlier.
  --
  -- No `top` guard, because the open pass is only ever run on method bodies — that is what
  -- `false` in `Factors`' nominal conclusion says.
  | .nxt none =>
    match il with
    | some Γl =>
      if subAEnvB Γl Γ then .ok (.nom .nilT) Γ s else .outOfFragment "next-env"
    | none => .outOfFragment "next-outside-loop"
  | _ => .outOfFragment (headName e)
termination_by sizeOf e

def inferOpenSeq (D : Decls) (Γ : AEnv) (es : List Expr) (ctx : OCtx) (il : Option AEnv)
    (s : OState) : OResult :=
  match es with
  | [] => .ok (.nom .nilT) Γ s
  | [e] => inferOpen D Γ e ctx il s
  | e :: rest =>
    match inferOpen D Γ e ctx il s with
    | .ok _ Γ₁ s₁ => inferOpenSeq D Γ₁ rest ctx il s₁
    | r => r
termination_by sizeOf es

/-- The argument list, left to right, threading the environment and the store.
    `startArgs`' own loop, in open-self mode. -/
def inferOpenArgs (D : Decls) (Γ : AEnv) (es : List Expr) (ctx : OCtx) (il : Option AEnv)
    (s : OState) : OArgs :=
  match es with
  | [] => .ok [] Γ s
  | e :: rest =>
    match inferOpen D Γ e ctx il s with
    | .ok τ Γ₁ s₁ =>
      match inferOpenArgs D Γ₁ rest ctx il s₁ with
      | .ok τs Γ₂ s₂ => .ok (τ :: τs) Γ₂ s₂
      | r => r
    | .missing τ n ps => .missing τ n ps
    | .outOfFragment h => .outOfFragment h
termination_by sizeOf es

/-- **The elements of an array literal, in open-self mode** (L230) — `inferElems`' mirror,
    and the fifth open function for the same reason the nominal side has a fifth: a splat
    element is admitted **here and nowhere else**, and giving `.splat` an `inferOpen` arm
    would make the *factoring* claim that `infer` accepts a bare splat, which it does not.

    **A splat's operand must be a *nominal* `Array`.** A type *variable* is refused rather
    than constrained, for `cpath-base`'s reason (L205): the store's requirements are rows,
    and "is an `Array`" is not a row. That is a real limitation and it is measured — it is
    why `Vulnerability#identifiers` (`[id, *aliases].uniq`) stays out of the fragment while
    `PkgVersion#self.parse` (`[*path.match(…)]`) crosses to a needed *declaration*. -/
def inferOpenElems (D : Decls) (Γ : AEnv) (es : List Expr) (ctx : OCtx) (il : Option AEnv)
    (s : OState) : OResult :=
  match es with
  | [] => .ok (.nom .nilT) Γ s
  | e :: rest =>
    match e with
    | .splat (some o) =>
      match inferOpen D Γ o ctx il s with
      | .ok (.nom (.cls "Array")) Γ₁ s₁ => inferOpenElems D Γ₁ rest ctx il s₁
      -- **L237: a *variable* operand is a requirement, not a refusal.** `[id, *aliases]`
      -- where `aliases` is still `α` was the `splat-operand` refusal; the store's `eqs`
      -- field — L206's, added for the join — is exactly the atom for it: record `θ α =
      -- Array` and carry on. Nothing here solves for `α`; the untrusted solver chooses
      -- `θ` and `satStoreB` checks, which is the same division of labour every other
      -- store field has.
      --
      -- `addEq` rather than a *bound* (`α ⊒ Array`) is what the assertion language can
      -- say, and it is enough: the nominal rule wants the operand to *be* `Array`, so an
      -- equality is the requirement, not an approximation of one.
      | .ok (.var α) Γ₁ s₁ =>
        inferOpenElems D Γ₁ rest ctx il { s₁ with st := s₁.st.addEq α (.nom (.cls "Array")) }
      | .ok _ _ _ => .outOfFragment "splat-operand"
      | r => r
    | ee =>
      match inferOpen D Γ ee ctx il s with
      | .ok _ Γ₁ s₁ => inferOpenElems D Γ₁ rest ctx il s₁
      | r => r
termination_by sizeOf es

def inferOpenIf (D : Decls) (Γ : AEnv) (t : Expr) (els : Option Expr) (ctx : OCtx)
    (il : Option AEnv) (s : OState) : OResult :=
  match els with
  | some e =>
    match inferOpen D Γ t ctx il s with
    | .ok τt Γt st =>
      match inferOpen D Γ e ctx il st with
      | .ok τe Γe se =>
        -- L193b, mirroring `inferIf`: the types are *joined*, the environments are
        -- still compared. `joinATy` is the only difference from the nominal rule, and
        -- the reason it exists rather than `joinTy` being reused is that this side
        -- joins against a type *variable*.
        -- **L236: two containments and the *entry* environment as the answer**, mirroring
        -- `inferIf` exactly — including the reason it is not a shape test: the factoring
        -- theorem needs the answer to commute with `substEnv θ`, and `Γt = Γe` does not.
        if subAEnvB Γ Γt && subAEnvB Γ Γe then
          -- L206: `joinOpen` rather than `joinATy` — the store is threaded because the
          -- join may *record* a requirement (a variable pinned to the other arm's
          -- type) rather than only answering one.
          match Store.joinOpen se.st τt τe with
          | some (τj, st') => .ok τj Γ { se with st := st' }
          | none => .outOfFragment "if"
        else .outOfFragment "if-env"
      | r => r
    | r => r
  | none =>
    match inferOpen D Γ t ctx il s with
    | .ok τt Γt st =>
      -- L236: `subAEnvB Γ Γt` where this was `Γt = Γ`; the answer was already the entry
      -- environment, so only the refusal changes.
      if subAEnvB Γ Γt then
        match Store.joinOpen st.st τt (.nom Ty.nilT) with
        | some (τj, st') => .ok τj Γ { st with st := st' }
        | none => .outOfFragment "if"
      else .outOfFragment "if-env"
    | r => r
termination_by sizeOf t + sizeOf els

end

/-! ## 3. §7.3 — the `def` rule's conclusion, and §11's report

`R = Σ'(α)` is *the method's precondition*, and `Σ' ∖ α ∧ (c ⊒ R)` is what the
rule leaves behind. Neither of these is on the soundness path; they are the R1
output that §11 is about, computed from the same run rather than by a second
traversal.
-/

/-- §7.3, read off a completed body: the residual row on `self`, which is the
    method's precondition on its own class. -/
def residualRow (ctx : OCtx) (s : OState) : Row := s.st.rowOf ctx.self

/-- §7.3's `Σ' ∖ α ∧ (c ⊒ R)`. -/
def closeBody (ctx : OCtx) (s : OState) : Store := s.st.closeAt ctx.self ctx.cls

/-- **The join of a body's own answer with every `return` it recorded** (L229), and it
    is what makes a method's inferred return type *the union of its exits* rather than the
    type of its last expression.

    L201 checked `subATy a τ` for every recorded `a` and refused otherwise — which is
    exactly right when the body's own answer is already the widest exit, and wrong when it
    is not: `return if x.nil?` records `nilT` in a method whose tail is an `Integer`, and
    the honest answer is `T.nilable(Integer)`, not a refusal. Strictly more permissive
    than the check it replaces: `subATy a τ = true` makes `joinATy a τ = some τ`.

    Folded right-to-left so the recursion is on the list, which is what the soundness
    lemma (`joinRets_sub`) inducts over. A join that cannot be justified is still a
    refusal — `joinATy` answers only the shapes it can. -/
def joinRets : List ATy → ATy → Option ATy
  | [], τ => some τ
  | a :: rest, τ =>
    match joinRets rest τ with
    | some τ₁ => joinATy a τ₁
    | none => none

/-- Type one method body of class `c`, in open-self mode. `α := 0` and the fresh
    counter starts above it, which is the only bookkeeping the caller owes. -/
def inferBody (D : Decls) (c mname : String) (body : Expr) : OResult :=
  -- **L201/L229: the accumulated `return` types are *joined* with the body's own
  -- answer**, and this is the only place the join *can* be — the pass meets a `return`
  -- before it knows the tail. L201 checked `subATy` here and refused a disagreement on the
  -- grounds that "joining them would need the union this fragment does not have"; it does
  -- not — `joinTy` has answered `nil`-shaped joins since L193, which is exactly the shape
  -- a bare `return` produces. A join that *cannot* be justified is still `outOfFragment`.
  match inferOpen D [] body { cls := c, self := 0, meth := some mname, params := some [] }
      none { st := {}, fresh := 1 } with
  | .ok τ Γ' s =>
    match joinRets s.rets τ with
    | some τj => .ok τj Γ' s
    | none => .outOfFragment "return-join"
  | r => r

/-- §11's per-body verdict, as an output of the checker rather than a duplicate of
    it. This is R1's third-ratchet feed and R3's input. -/
def bodyVerdict (D : Decls) (c mname : String) (body : Expr) : BodyVerdict :=
  match inferBody D c mname body with
  | .ok τ _ s =>
    .acceptedUnder τ (residualRow { cls := c, self := 0 } s)
      ((closeBody { cls := c, self := 0 } s).toAssn)
  | .missing τ n ps => .blocked τ n ps
  | .outOfFragment head => .outOfFragment head

/-! ## 3a. §7.3's `Γ_b` — parameters, open (L168)

`fragment-gap.py`'s third ratchet, on its first run, said the slice's largest
single blocker is **`def` with parameters — 67 of its 112 method bodies**, three
times every other blocker combined (`homebrew/HANDOFF.md` §The measurement that
reordered the work — again). Neither of the two earlier rankings had it anywhere,
because both rank constructs *inside* bodies and this is the shape of a **rule**.

What blocked it is written in `bodyReports`' old comment: §7.3's `Γ_b` had
"nothing to factor to", since `infer`'s `def` arm requires `params.isEmpty`. That
is right about the `def` **rule** and wrong about the **body**:
`inferOpen_factors` is quantified over `Γ` — it always was — so an open run with
parameters bound to fresh variables factors through `infer` at
`substEnv θ Γ_b`, which is a nominal judgement that exists today
(`Proof/Static/OpenSelf.lean` `inferBodyWith_sound`). What does *not* exist is the
`def` rule that would install the row, and that is why the verdict has its own
constructor (`BodyVerdict.acceptedOpenParams`) and its own census column rather
than joining `accepted`.

So this rung is the same stance R4 took, one argument along: **untrusted front
end, proved to factor, `check` untouched.** It adds no `KontOk` constructor, no
consecution case, and no arm to `infer`.

**Required positional parameters only.** `Param` has eight arms and the other
seven are refused by name, because each is a *different* binding rule in
`enterUserMethod` (`Interp/Support.lean:452`) and an optional's default is an
expression evaluated in the callee frame — a second body, not a type. Refusing
them by kind rather than in bulk is what keeps the census able to say which wall
the remaining bodies are behind. -/

-- ~~`paramKind`~~ / ~~`firstNonReq`~~ — **withdrawn at L173**, with the refusal
-- they explained. L168 refused six of `Param`'s eight arms *by kind* so the census
-- could say which binding rule a body was behind; L173 binds five of them, so the
-- only kinds left are the two `firstUnbound` names and a per-kind printer has
-- nothing to enumerate. What replaced the information they carried is better: the
-- nine bodies now report the construct **inside their own body** that stops them.

/-- The first parameter `openParams` refuses, by kind. `none` when every
    parameter is one it binds, which is exactly when `openParams` succeeds.

    **Two kinds are left** (L173): `fwd` binds three *internal* locals nobody can
    name (`__fwd_rest`/`__fwd_kw`/`__fwd_blk`, `Interp/Send.lean`'s
    `forwardBundle`), so there is no source-level environment to state; and `destr`
    nests, so its binding is a recursive massign against an argument shape no type
    in `Ty` records. Neither occurs in the slice. -/
def firstUnbound : List Param → Option String
  | [] => none
  | .fwd :: _ => some "fwd"
  | .destr _ :: _ => some "destr"
  | _ :: rest => firstUnbound rest

/-- §7.3's `Γ_b = ∅[x₁ ↦ τ₁, …, x_k ↦ τ_k]` — the environment a method body is
    typed in, one entry per parameter **in source order**, threading the open state
    so that a default's own requirements land in the store.

    Variables start at `1` because `0` is `self` (`inferBody`'s convention), so a
    parameter's variable can never be confused with the receiver's — which matters
    for `residualRow`, whose whole content is *the row on `self`*.

    **What each kind is bound to** (L173), and each is read off what
    `enterUserMethod` really writes (`Interp/Dispatch.lean:96`–`119`) rather than
    guessed:

    * `req` — a **fresh variable**. The caller's type is not known here and is not
      claimed to be: it is `θ`'s to choose (L168).
    * `rest` — `Array`. `*a` is bound by `Builtins.allocArr` on the surplus, always,
      so this is the one parameter kind whose type is *known* rather than assumed.
    * `kwrest` — `Hash`, for the same reason (`allocHash` on the leftover pairs).
    * `block` — a **fresh variable**. `&b` holds a `Proc` **or `nil`**
      (`blk.getD .nil`), which is a union `Ty` cannot write; a variable is the
      honest under-determination, and whatever the body requires of it lands in the
      residual store, so `θ` carries the *a block was given* precondition rather
      than the environment pretending it away.
    * `opt x = d` and `key x: d` — **the default's own type**. The default is an
      expression evaluated in the callee frame, so it is typed here, in the
      environment built so far (a default may read an earlier parameter), and the
      parameter is bound to what it answers. That is a precondition on callers of
      exactly the kind a `req`'s variable is, with the difference that this one is
      *forced* — the omitted-argument path really does bind it.
    * `key x:` with no default — a required keyword, so a fresh variable, as `req`.
    * an **anonymous** `rest`/`kwrest`/`block` binds nothing at all, which is what
      the machine does.

    Refuses `fwd` and `destr`; see `firstUnbound`. -/
def openParams (D : Decls) (ctx : OCtx) : List Param → AEnv → OState →
    Option (AEnv × OState)
  | [], Γ, s => some (Γ, s)
  | .req x :: rest, Γ, s =>
    openParams D ctx rest (Γ ++ [(x, .var s.fresh)]) { s with fresh := s.fresh + 1 }
  | .rest (some x) :: rest, Γ, s =>
    openParams D ctx rest (Γ ++ [(x, .nom (.cls "Array"))]) s
  | .rest none :: rest, Γ, s => openParams D ctx rest Γ s
  | .kwrest (some x) :: rest, Γ, s =>
    openParams D ctx rest (Γ ++ [(x, .nom (.cls "Hash"))]) s
  | .kwrest none :: rest, Γ, s => openParams D ctx rest Γ s
  | .block (some x) :: rest, Γ, s =>
    openParams D ctx rest (Γ ++ [(x, .var s.fresh)]) { s with fresh := s.fresh + 1 }
  | .block none :: rest, Γ, s => openParams D ctx rest Γ s
  | .key x none :: rest, Γ, s =>
    openParams D ctx rest (Γ ++ [(x, .var s.fresh)]) { s with fresh := s.fresh + 1 }
  | .opt x d :: rest, Γ, s =>
    -- L222: a parameter default is not inside the method's loops.
    match inferOpen D Γ d ctx none s with
    | .ok τ _ s' => openParams D ctx rest (Γ ++ [(x, τ)]) s'
    | _ => none
  | .key x (some d) :: rest, Γ, s =>
    match inferOpen D Γ d ctx none s with
    | .ok τ _ s' => openParams D ctx rest (Γ ++ [(x, τ)]) s'
    | _ => none
  | .fwd :: _, _, _ => none
  | .destr _ :: _, _, _ => none

/-- **The parameter types a bare `super` can forward** (L214), or `none` when the shape is
    one `zsuperArgs` refuses to reconstruct.

    All-`.req` only, and that is a *restriction on the rule*, not an approximation of
    `openParams`: for an all-required list `openParams` allocates the fresh variables
    `1, 2, …, n` in order (it starts at `fresh := 1` and increments once per `.req`), so
    this list is exactly the variables the body's own parameters were opened at. Any other
    kind — `opt`, `key`, `rest`, `block` — either does not allocate in that order or is
    re-bundled by `zsuperArgs` into keywords, so the two would disagree and the rule
    refuses instead.

    It is a *mirror* of `openParams`' allocation order, which is the kind of copy this
    project has been burned by (`SUPPORTED`, twice). It is not a soundness risk today and
    the reason is worth stating: a context with a non-empty `params` cannot be **spent**,
    because `StackCtx`'s L214 clause pins every activation the invariant describes to
    `some []`. So a wrong list here can only ever fail to certify, never certify wrongly —
    the same standing as `accept (params open)` has had since L168. -/
def openParamTys (ps : List Param) : Option (List ATy) :=
  if ps.all (fun p => match p with | .req _ => true | _ => false)
  then some ((List.range ps.length).map (fun i => ATy.var (i + 1)))
  else none

/-- Type one method body of class `c` in the environment its parameters give.
    `none` when a parameter kind is one `openParams` does not bind, or when a
    default expression is itself out of the fragment. -/
def inferBodyWith (D : Decls) (c mname : String) (ps : List Param) (body : Expr) :
    Option (AEnv × OResult) :=
  let ctx : OCtx := { cls := c, self := 0, meth := some mname,
                      params := openParamTys ps }
  match openParams D ctx ps [] { st := {}, fresh := 1 } with
  | some (Γb, s) =>
    -- L201's check, at the parameterized entry point too.
    some (Γb, match inferOpen D Γb body ctx none s with
      | .ok τ Γ' s' =>
        match joinRets s'.rets τ with
        | some τj => .ok τj Γ' s'
        | none => .outOfFragment "return-join"
      | r => r)
  | none => none

/-- §11's per-body verdict for a `def` with parameters. Delegates to
    `bodyVerdict` when there are none, so the zero-parameter census column keeps
    exactly the meaning it had. -/
def bodyVerdictWith (D : Decls) (c mname : String) (ps : List Param) (body : Expr) :
    BodyVerdict :=
  if ps.isEmpty then bodyVerdict D c mname body else
  match inferBodyWith D c mname ps body with
  | none => .outOfFragment ("def-params-" ++ (firstUnbound ps).getD "dflt")
  | some (Γb, .ok τ _ s) =>
    .acceptedOpenParams τ (residualRow { cls := c, self := 0 } s)
      ((closeBody { cls := c, self := 0 } s).toAssn) Γb
  | some (_, .missing τ n args) => .blocked τ n args
  | some (_, .outOfFragment head) => .outOfFragment head

/-! ## 3b. §11 and R3 — the per-body census, as an output of the checker

`fragment-gap.py`'s two ratchets are *progress through the files* and *progress
toward a verdict*; neither is `accept`, because a body fully inside `infer`'s
domain still infers `none` if a callee has no row (`HANDOFF.md` §Not on the
critical path). **This is the third ratchet**, and the point is that it is
computed by the checker rather than by a hand-maintained copy of the checker's
match arms — which is what has made `SUPPORTED` wrong twice.
-/

-- Every `def` in the program, with the class it installs on and what open-self
-- inference says about its body. The class defaults to `"Object"`, which is
-- where a toplevel `def` installs (and where, per L162, its row is
-- unwitnessable — so the report says `accept` and the *table* still refuses it,
-- correctly).
mutual

def bodyReports (D : Decls) (cls : String) (e : Expr) : List (String × String × BodyVerdict) :=
  match e with
  -- **A `def` with parameters is typed with its parameters open** (L168), and the
  -- verdict says so: `acceptedOpenParams`, a separate constructor and a separate
  -- census column, because it factors through `infer` at `substEnv θ Γ_b` and not
  -- through any `def` rule (`inferBodyWith`'s header). Until L168 this arm was
  -- refused outright on the grounds that §7.3's `Γ_b` had nothing to factor to —
  -- true of the rule, false of the body, since `inferOpen_factors` is quantified
  -- over `Γ`. A parameter that is not a required positional is still refused, **by
  -- kind**, so the census can say which binding rule the body is behind.
  | .def' n ps body => [(cls, n, bodyVerdictWith D cls n ps body)]
  -- A singleton definition installs on the eigenclass, which is a different key;
  -- reported under the same class name with `self.` prefixed so the count is
  -- complete and the distinction is visible rather than silent.
  | .defs _ n ps body => [(cls, "self." ++ n, bodyVerdictWith D cls n ps body)]
  | .class' name _ body => bodyReports D name body
  | .scopedClass _ name body => bodyReports D name body
  | .module' name body => bodyReports D name body
  | .scopedModule _ name body => bodyReports D name body
  | .sclass _ body => bodyReports D cls body
  | .seq es => bodyReportsList D cls es
  | .begin' body _ _ _ => bodyReports D cls body
  | .if' _ t e =>
    bodyReports D cls t ++ (match e with | some x => bodyReports D cls x | none => [])
  | .while' _ b => bodyReports D cls b
  | .block _ _ b => bodyReports D cls b
  | .send _ _ _ (some b) => bodyReports D cls b
  | _ => []
termination_by sizeOf e

def bodyReportsList (D : Decls) (cls : String) (es : List Expr) :
    List (String × String × BodyVerdict) :=
  match es with
  | [] => []
  | e :: rest => bodyReports D cls e ++ bodyReportsList D cls rest
termination_by sizeOf es

end

/-- R3's number: how many of the program's method bodies open-self inference
    types, and how many of those need nothing from their own class. -/
structure BodyCensus where
  total : Nat := 0
  /-- Typed, under some precondition on the defining class. -/
  accepted : Nat := 0
  /-- Typed **with parameters open** (L168) — the body's typing is settled and its
      declaration is not. Counted apart from `accepted` for the reason
      `BodyVerdict.acceptedOpenParams` is a separate constructor. -/
  acceptedParams : Nat := 0
  /-- Typed with an **empty** residual row — no obligation at all. -/
  unconditional : Nat := 0
  /-- Refused with a named missing atom (§11's `needed:` line). -/
  blocked : Nat := 0
  /-- Refused because a construct is outside `infer`'s domain. -/
  outOfFragment : Nat := 0
deriving Repr, Inhabited

def census (rs : List (String × String × BodyVerdict)) : BodyCensus :=
  rs.foldl (init := {}) fun c r =>
    match r.2.2 with
    | .acceptedUnder _ need rest =>
      { c with total := c.total + 1, accepted := c.accepted + 1,
               unconditional := c.unconditional +
                 (if need.entries.isEmpty && rest == .emp then 1 else 0) }
    | .acceptedOpenParams _ need rest _ =>
      { c with total := c.total + 1, acceptedParams := c.acceptedParams + 1,
               unconditional := c.unconditional +
                 (if need.entries.isEmpty && rest == .emp then 1 else 0) }
    | .blocked _ _ _ => { c with total := c.total + 1, blocked := c.blocked + 1 }
    | .outOfFragment _ =>
      { c with total := c.total + 1, outOfFragment := c.outOfFragment + 1 }

/-! ## 4. Checked facts — the capability, asserted in the build

`HANDOFF.md`'s norm: *a capability nothing asserts is a capability nothing
notices breaking*, and every rung since L151 has been verified this way because
the corpus cannot witness it.

Note these are `simp` over the equation lemmas rather than `decide`:
`inferOpen` is well-founded-recursive, so the kernel does not reduce it — the
same reason `Proof/StaticSoundness.lean` §5 gives for `infer`, and the reason
neither needs `native_decide`. -/

/-- **§4.3's example, typed with no declaration for `value` at all.**

    ```ruby
    def hash
      value.hash
    end
    ```

    The body is `value.hash` — a `vcall` in receiver position of a zero-argument
    send. `inferOpen` gives it type `α2` under the residual store
    `α0 ↦ ⟨value : () → α1⟩, α1 ↦ ⟨hash : () → α2⟩`, which is the flattened form of
    §4.3's principal type `self : ⟨value : () → ⟨hash : () → β | ρ₂⟩ | ρ₁⟩`.
    Compare `infer`, which answers `none`: `sigOf` has no row for `value` on any
    class, and that is exactly the fourteen slice bodies' blocker. -/
def egOpenHashBody : Expr := .send (some (.vcall "value")) "hash" [] none

/-- The residual store, written out. Two rows, and the nesting is the point: the
    requirement on `α1` — *whatever `value` returns must have a `hash`* — is
    recorded against a variable that no class name is attached to. -/
def egOpenHashStore : Store :=
  { rows := [(1, { entries := [("hash", { params := [], ret := .var 2 })] }),
             (0, { entries := [("value", { params := [], ret := .var 1 })] })] }

example : inferBody baseDecls "Version" "m" egOpenHashBody
    = .ok (.var 2) [] { st := egOpenHashStore, fresh := 3 } := by
  simp [joinRets, inferBody, egOpenHashBody, egOpenHashStore, inferOpen, inferOpenArgs, isSelf, requireRow,
    Store.rowOf, Row.get?, Row.insert, Store.setRow, Row.empty]

/-- §7.3's `R = Σ'(α)` — the method's precondition on its own class. -/
example :
    residualRow { cls := "Version", self := 0 }
        { st := egOpenHashStore, fresh := 3 }
      = { entries := [("value", { params := [], ret := .var 1 })] } := by
  simp [residualRow, egOpenHashStore, Store.rowOf]

/-- **`infer` refuses the same body**, which is what makes the rung a capability
    rather than a re-notation. -/
example :
    infer baseDecls [] egOpenHashBody false { cls := "Version", selfCls := some "Version" }
      = none := by
  simp [infer, egOpenHashBody, isSelf, sigOf, declFor, declOf?, declsFor, baseDecls,
    tyClassNames, groundClassNames]

/-- A body that needs nothing: the residual row is empty, so §7.3's obligation is
    `emp` and the accept is unconditional. -/
example : inferBody baseDecls "Version" "m" (.int 1) = .ok (.nom .int) [] { fresh := 1 } := by
  simp [joinRets, inferBody, inferOpen]

/-- A nominal receiver still goes through the table, unchanged: `1 + 2`. -/
example : inferBody baseDecls "Version" "m" (.send (some (.int 1)) "+" [.int 2] none)
    = .ok (.nom .int) [] { fresh := 1 } := by
  simp [joinRets, inferBody, inferOpen, inferOpenArgs, isSelf, sigOf, declFor, declOf?, declsFor, baseDecls,
    tyClassNames]

/-- And a nominal receiver the table refuses is `missing`, **with the atom** —
    §11's `needed:` line, produced by the checker rather than by a census of it.
    This is the whole of R1's benefit, and it costs no metatheory. -/
example : inferBody baseDecls "Version" "m" (.send (some (.int 1)) "/" [.int 2] none)
    = .missing (.nom .int) "/" [.nom .int] := by
  simp [joinRets, inferBody, inferOpen, inferOpenArgs, isSelf, sigOf, declFor, declOf?, declsFor, baseDecls,
    tyClassNames]


/-! ### L168's capability, asserted in the build

`HANDOFF.md`'s norm: the corpus cannot witness a `--assn` verdict, so the
capability is asserted here or it is not asserted at all. -/

/-- **`Γ_b`, in order, one fresh variable per `req`, starting above `self`'s.** The
    offset is what keeps `residualRow` — whose entire content is the row on
    `self` — from reading a parameter's row. -/
example :
    openParams baseDecls { cls := "String", self := 0 } [.req "a", .req "b"] []
        { st := {}, fresh := 1 }
      = some ([("a", .var 1), ("b", .var 2)], { st := {}, fresh := 3 }) := by
  simp [openParams]

/-- **An optional is bound to its default's type** (L173), not to a variable: the
    omitted-argument path really does bind it, so the default is typed here — in
    the environment built so far — and the parameter takes what it answers. -/
example :
    openParams baseDecls { cls := "String", self := 0 } [.opt "a" (.int 1)] []
        { st := {}, fresh := 1 }
      = some ([("a", .nom .int)], { st := {}, fresh := 1 }) := by
  simp [openParams, inferOpen]

/-- **`*rest` is an `Array` and `**kw` is a `Hash`**, which is the one place a
    parameter's type is *known* rather than assumed: `enterUserMethod` binds them
    with `allocArr`/`allocHash` unconditionally. -/
example :
    openParams baseDecls { cls := "String", self := 0 }
        [.rest (some "r"), .kwrest (some "k")] [] { st := {}, fresh := 1 }
      = some ([("r", .nom (.cls "Array")), ("k", .nom (.cls "Hash"))],
              { st := {}, fresh := 1 }) := by
  simp [openParams]

/-- **An anonymous `*`/`**`/`&` binds nothing**, which is what the machine does. -/
example :
    openParams baseDecls { cls := "String", self := 0 }
        [.rest none, .kwrest none, .block none] [] { st := {}, fresh := 1 }
      = some ([], { st := {}, fresh := 1 }) := by
  simp [openParams]

/-- **`&b` is a fresh variable, deliberately.** It holds a `Proc` *or* `nil`
    (`blk.getD .nil`), a union `Ty` cannot write — so the under-determination goes
    into `θ` and whatever the body requires of the block lands in the residual
    store, rather than the environment asserting a type the machine does not
    guarantee. -/
example :
    openParams baseDecls { cls := "String", self := 0 } [.req "a", .block (some "b")] []
        { st := {}, fresh := 1 }
      = some ([("a", .var 1), ("b", .var 2)], { st := {}, fresh := 3 }) := by
  simp [openParams]

/-- **`...` and a destructuring parameter are still refused, by kind.** Both name
    a binding with no source-level environment to state: `fwd` writes three
    internal locals nobody can read by name, `destr` is a recursive massign
    against an argument shape no `Ty` records. Neither occurs in the slice. -/
example :
    bodyVerdictWith baseDecls "String" "m" [.fwd] (.int 1)
      = .outOfFragment "def-params-fwd" := by
  simp [bodyVerdictWith, joinRets, inferBodyWith, openParams, firstUnbound]

/-- And a body whose *default* is out of the fragment is refused too, with the
    census's `dflt` marker — the parameter kinds are all bound, so what stopped it
    is an expression rather than a binding rule.

    The witness was an **ivar read** until L196 admitted one, then a **global read**
    until L228 did; `retry` is the third, and the churn is the kind a widening should
    cause — each substitution is a rule that moved from *missing* to *present*. -/
example :
    bodyVerdictWith baseDecls "String" "m" [.opt "a" .retry'] (.int 1)
      = .outOfFragment "def-params-dflt" := by
  simp [bodyVerdictWith, joinRets, inferBodyWith, openParams, inferOpen, inferOpenArgs, firstUnbound, headName]

/-! ### L196's two branches, both exercised

`baseDecls.ivars` is **empty**, so no table the tool ships takes the read rule's
accepting branch. The rule is not unreachable-code-with-a-proof-attached — `step_ok`
is quantified over every table — but the *report* side is worth pinning at a table
that has a row, because that is the branch a reader will not otherwise see.

A shipped row would need what `T`'s did: a certificate deciding `IvarOk` at the heap
(`constsOkB`'s shape). Nothing needs one yet, which is why there is none.
-/

/-- **Undeclared: a missing declaration**, and the `@` in the atom's name says which
    kind. This is the verdict the slice's four ivar-reading bodies now get, and the
    reason the census moved. -/
example :
    bodyVerdictWith baseDecls "String" "m" [] (.var .ivar "@n")
      = .blocked (.var 0) "@@n" [] := by
  simp [bodyVerdictWith, bodyVerdict, joinRets, inferBody, inferOpen, ivarTy?, baseDecls]

/-- **Declared: `T.nilable(Integer)`, not `Integer`.** An unset ivar reads as `nil`
    (`Interp.lean:142` ends `.getD .nil`), so the answer has to admit it — L193's
    `nilable` paying for itself in a rule that has nothing to do with `if`. -/
example :
    bodyVerdictWith { baseDecls with ivars := [(("String", "@n"), Ty.int)] } "String" "m" []
        (.var .ivar "@n")
      = .acceptedUnder (.nom (.nilable .int)) Row.empty .emp := by
  simp [bodyVerdictWith, bodyVerdict, joinRets, inferBody, inferOpen, ivarTy?, mkNilable,
    residualRow, closeBody, Store.toAssn, Store.rowOf, Store.closeAt, Assn.all,
    Row.empty]

end RubyCore.Types
