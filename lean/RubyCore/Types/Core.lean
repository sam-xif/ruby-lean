import RubyCore.Types.Decls

/-!
# P0 of the static-soundness POC — the type language and the checker

`docs/semantics/static-soundness-poc.md` §8. This is deliberately the smallest
type layer that exercises the whole architecture: three ground types, no
subtyping, no user classes, no `send`. Its purpose is not coverage — it is to
measure the cost of typing the machine's **continuation stack** before P1 fixes
a larger scope.

The checker is an **executable inference function**, and the typing judgment is
*defined by it* (`infer Γ e = some (τ, Γ')`). That is the certifying-checker
shape of the POC doc §2: no separate `Prop` to keep in sync, and no completeness
proof owed — `none` simply means `unknown`.

Inference is **flow-sensitive** in the environment (Ruby locals are assigned,
not declared), so every judgment threads an input and an output environment.

**F1a threads a second thing: the declaration table `D`** (`Types/Decls.lean`).
Where P0 consulted a `builtinSig` *function*, every rule now consults `sigOf D`,
and `check` supplies `declsOf p`. Today that is `baseDecls` for every program, so
no verdict moves; what the threading buys is that the invariant has a table to be
a refinement *of* (`Proof/Static/Decls.lean`), and that F1b's program-supplied
declarations are a change to `declsOf` rather than to the rules. `Ty`/`Env` moved
to `Types/Ty.lean` in the same commit, unchanged.
-/

namespace RubyCore.Types

/-! ## The refutation pass

`static-soundness-poc.md` §2.2 deferred a `reject` verdict; this supplies it, as
a **second pass independent of `infer`**. The separation is deliberate: `infer`'s
`none` conflates "outside the fragment" with "ill-typed", and threading a third
value through it would touch every `KontOk` constructor and every case of the
preservation proof for no gain. `check_sound` is about `accept` and is untouched
by anything here.

**What `reject` claims.** Only that *our rules refute the program* — not that it
will fail at runtime. `if false then 1 + nil else 0 end` is rejected and is
perfectly safe. That asymmetry is inherent (`typed-portion-safety.md` §8.1) and
is why the guard on `reject` is a difftest direction — `reject ⇒ srb rejects` —
rather than a Lean theorem. Verified for the cases below [V].

**Bias toward `unknown`.** Every source of doubt resolves to `unknown`:
a receiver or argument whose type is not *unconditional*, a method absent from
the declaration table, or any expression outside the fragment's spine.
-/

/-- The type of an expression when it is **unconditional** — literals, and sends
    whose operands are themselves unconditional. Deliberately takes no
    environment, so a local variable is always `none`: `q = 1; q + nil` is
    `unknown` here though `srb` rejects it [V]. That is incompleteness, which
    the ratchet is allowed to have; it is also the obvious next widening. -/
def defTy (D : Decls) (e : Expr) : Option Ty :=
  match e with
  | .int _ => some .int
  | .tru => some .bool
  | .fls => some .bool
  | .nil => some .nilT
  | .send (some r) mname [a] none =>
    match defTy D r with
    | some τr =>
      match sigOf D τr mname with
      | some ([τp], τret) =>
        match defTy D a with
        | some τa => if τa = τp then some τret else none
        | none => none
      | _ => none
    | none => none
  | _ => none
termination_by sizeOf e

/-- Does the table *definitely* refute this call? Requires the receiver and the
    argument to have unconditional types **and** the method to be in the table.

    A method the table does not carry is `false`, not `true`: the table is
    narrow on purpose (`/` is absent but perfectly valid), so absence means "no
    opinion". `1.foo(2)` is therefore `unknown` here even though `srb` rejects it
    with 7003 [V] — again incompleteness, never unsoundness. -/
def tableRefutes (D : Decls) (r : Expr) (mname : String) (a : Expr) : Bool :=
  match defTy D r, defTy D a with
  | some τr, some τa =>
    match sigOf D τr mname with
    | some ([τp], _) => τa != τp
    | _ => false
  | _, _ => false

mutual

/-- Refutation: is there a call anywhere on the fragment's spine that the table
    refutes? Recursion stops at any construct outside the fragment, so an
    unsupported node hides everything below it — the conservative direction. -/
def illTyped (D : Decls) (e : Expr) : Bool :=
  match e with
  | .seq es => illTypedAny D es
  | .if' c t els =>
    illTyped D c || illTyped D t || (match els with | some e' => illTyped D e' | none => false)
  | .while' c b => illTyped D c || illTyped D b
  | .vasgn _ _ rhs => illTyped D rhs
  | .send (some r) mname [a] none =>
    illTyped D r || illTyped D a || tableRefutes D r mname a
  | _ => false
termination_by sizeOf e

def illTypedAny (D : Decls) (es : List Expr) : Bool :=
  match es with
  | [] => false
  | e :: rest => illTyped D e || illTypedAny D rest
termination_by sizeOf es

end

mutual

/-- `infer Γ e = some (τ, Γ')` — `e` has type `τ` and leaves the environment
    `Γ'`. `none` is `unknown`: outside the P0 fragment, or ill-typed. -/
def infer (D : Decls) (Γ : Env) (e : Expr) : Option (Ty × Env) :=
  match e with
  | .int _ => some (.int, Γ)
  | .tru => some (.bool, Γ)
  | .fls => some (.bool, Γ)
  | .nil => some (.nilT, Γ)
  -- **The first producer of a class-typed value** (F1b.3, L151). A string
  -- literal allocates a fresh plain `String` (`Builtins.allocStr`), so this is
  -- the one construct that inhabits `Ty.cls` in a *single* step, with no
  -- constant read, no send and no dispatch — which is why it is the producer
  -- that landed rather than `C.new` (`homebrew/HANDOFF.md` §The next commit
  -- costed that one and it needs four further rungs; see L151's note).
  --
  -- The name is the literal `"String"` rather than anything read from the heap
  -- because `infer` is a pure function of the program. Tying it to the object
  -- the step really allocates is `Inv`'s job, and the clause that does it is
  -- `StrClsOk` — *the boot `String` id is a class named `"String"`* — which is
  -- the same put-the-condition-in-the-judgement move as `NoHook`'s bound (L149).
  | .str _ => some (.cls "String", Γ)
  | .var .lvar x => (envGet? Γ x).map (fun τ => (τ, Γ))
  | .vasgn .lvar x rhs =>
    match infer D Γ rhs with
    | some (τ, Γ₁) => some (τ, envSet Γ₁ x τ)
    | none => none
  -- Binary send to a builtin, explicit receiver, no block. Every other send
  -- shape — implicit self, wrong arity, a block, `vcall` — is `unknown`, which
  -- is also what keeps `.self'` out of receiver position (see `KontOk.recvK`:
  -- `evalExpr` picks the `.selfRecv` site *syntactically* for a literal `self`).
  | .send (some recv) mname [arg] none =>
    match infer D Γ recv with
    | some (τr, Γ₁) =>
      match sigOf D τr mname with
      | some ([τp], τret) =>
        match infer D Γ₁ arg with
        | some (τa, Γ₂) => if τa = τp then some (τret, Γ₂) else none
        | none => none
      | _ => none
    | none => none
  -- **A zero-argument send** (L152). Split from the unary rule rather than folded
  -- into it, because the two are *different machine shapes*: with an argument the
  -- receiver's `recvK` pushes an `argsK` and dispatch happens a step later, while
  -- with none `applyKont` runs `startArgs … [] []`, which is `finishSend` — so the
  -- send completes in the `recvK` step itself and needs its own `KontOk`
  -- constructor and its own consecution case (`KontOk.recvK0`).
  --
  -- Every send in the fragment is now zero- or one-argument; two or more is still
  -- `unknown`, and stays so until `ValuesTy` is threaded through a list of argument
  -- continuations rather than a single one.
  | .send (some recv) mname [] none =>
    match infer D Γ recv with
    | some (τr, Γ₁) =>
      match sigOf D τr mname with
      | some ([], τret) => some (τret, Γ₁)
      | _ => none
    | none => none
  -- A **zero-parameter** definition. Parameters wait for call-site types (the
  -- next step); until then there is no environment to check the body in.
  --
  -- Two exclusions, and each discharges a clause of the machine invariant rather
  -- than being a matter of taste.
  --
  -- **`declaresName D name` is F1a's generalization of P0's `≠ "+"/"-"/"*"`.** A
  -- `def` of a name the declarations do not mention is an *addition*, which D10
  -- admits unconditionally, and the invariant survives it because `lookup` for
  -- every declared name is untouched (`Proof/Static/Decls.lean`
  -- `DeclsOk_defineMethod`). A `def` of a name they *do* mention is a
  -- **redefinition**, admissible iff the new body conforms to the displaced
  -- declaration — checkable, and F1c's job, so `unknown` until then. With
  -- `baseDecls` this excludes exactly `+`, `-`, `*`.
  --
  -- `method_added` would install the `def` hook (`Interp.lean:2625`) whose body
  -- we cannot type, so it stays excluded by name.
  | .def' name params body =>
    if params.isEmpty ∧ declaresName D name = false ∧ name ≠ "method_added" then
      -- The body is checked even though nothing can call it yet. Skipping the
      -- check would accept more programs *now* and fewer once calls arrive,
      -- which is a ratchet regression; the fragment only ever grows.
      match infer D [] body with
      | some _ => some (.sym, Γ)
      | none => none
    else none
  | .seq es => inferSeq D Γ es
  | .if' c t els =>
    match infer D Γ c with
    | some (_, Γ₁) => inferIf D Γ₁ t els
    | none => none
  | .while' c body =>
    -- The loop re-enters the condition with the environment the body leaves, so
    -- both must be *stable* at `Γ`. This is the P0 stand-in for a fixpoint.
    match infer D Γ c with
    | some (_, Γ₁) =>
      if Γ₁ = Γ then
        match infer D Γ body with
        | some (_, Γ₂) => if Γ₂ = Γ then some (.nilT, Γ) else none
        | none => none
      else none
    | none => none
  | _ => none
termination_by sizeOf e

/-- Statement sequence: thread the environment, take the last type. Mirrors
    `evalExpr`'s three-way split on `.seq` (`Interp.lean:2732`) exactly — in
    particular `[e]` steps straight to `e` with no `seqK` pushed. -/
def inferSeq (D : Decls) (Γ : Env) (es : List Expr) : Option (Ty × Env) :=
  match es with
  | [] => some (.nilT, Γ)
  | [e] => infer D Γ e
  | e :: rest =>
    match infer D Γ e with
    | some (_, Γ₁) => inferSeq D Γ₁ rest
    | none => none
termination_by sizeOf es

/-- The `if` join, factored out because `KontOk.ifK` must agree with it
    branch-for-branch. No union type in P0, so the two arms must agree on both
    the type and the environment; a missing `else` contributes `nil` and no
    environment change (`applyKont`'s fall-through, `Interp.lean:2096`). -/
def inferIf (D : Decls) (Γ : Env) (t : Expr) (els : Option Expr) : Option (Ty × Env) :=
  match els with
  | some e =>
    match infer D Γ t, infer D Γ e with
    | some (τt, Γt), some (τe, Γe) =>
      if τt = τe ∧ Γt = Γe then some (τt, Γt) else none
    | _, _ => none
  | none =>
    match infer D Γ t with
    | some (τt, Γt) => if τt = Ty.nilT ∧ Γt = Γ then some (.nilT, Γ) else none
    | none => none
termination_by sizeOf t + sizeOf els

end

/-- The verdict lattice. `accept` is backed by `check_sound`; `reject` is backed
    by the difftest direction `reject ⇒ srb rejects` (not by a theorem — see the
    refutation-pass header); `unknown` claims nothing and is the default. -/
inductive Verdict where
  | accept
  | reject
  | unknown
deriving DecidableEq, Repr, Inhabited

/-- **The checker.** Total and executable, and still a pure function of the
    program: the declaration table it runs against is `declsOf p`, computed from
    `p` (constant today — `Types/Decls.lean` says why). `infer` is consulted
    first, so a program the type rules accept is never refuted; `illTyped` only
    ever upgrades an `unknown` to a `reject`. -/
def check (p : Expr) : Verdict :=
  match infer (declsOf p) [] p with
  | some _ => .accept
  | none => if illTyped (declsOf p) p then .reject else .unknown

/-! ## Worked verdicts

Each `unknown` below is *incompleteness* — `srb` rejects and we abstain — which
the ratchet permits and the pinned zero does not count. Each `reject` agrees
with `srb` [V, 0.6.13405].
-/

/-- `1 + nil` — srb 7002. The motivating case. -/
example : check (.send (some (.int 1)) "+" [.nil] none) = .reject := by
  simp [check, infer, illTyped, tableRefutes, defTy, sigOf, declFor, declOf?, declsFor, baseDecls, tyClassNames, declsOf]

/-- `1 + true` — srb 7002. -/
example : check (.send (some (.int 1)) "+" [.tru] none) = .reject := by
  simp [check, infer, illTyped, tableRefutes, defTy, sigOf, declFor, declOf?, declsFor, baseDecls, tyClassNames, declsOf]

/-- **Rejected, and perfectly safe.** `if false then 1 + nil else 0 end` runs to
    `0`. `reject` claims our rules refute the program, *not* that it fails —
    the asymmetry of `typed-portion-safety.md` §8.1. srb rejects this too, but
    for a different reason (7006 unreachable, not 7002), which is worth
    remembering when the difftest starts comparing diagnostics [V]. -/
example :
    check (.if' .fls (.send (some (.int 1)) "+" [.nil] none) (some (.int 0)))
      = .reject := by
  simp [check, infer, inferIf, illTyped, tableRefutes, defTy, sigOf, declFor, declOf?, declsFor, baseDecls, tyClassNames, declsOf]

/-- `1 / 2` — srb *accepts*; `/` is absent from the table, so we abstain. This
    is the case that makes "absent ⇒ no opinion" mandatory rather than merely
    conservative: rejecting here would break `reject ⇒ srb rejects`. -/
example : check (.send (some (.int 1)) "/" [.int 2] none) = .unknown := by
  simp [check, infer, illTyped, tableRefutes, defTy, sigOf, declFor, declOf?, declsFor, baseDecls, tyClassNames, declsOf]

/-- `1.foo(2)` — srb 7003. We abstain: the table cannot distinguish "no such
    method" from "method we have not tabulated". Incompleteness. -/
example : check (.send (some (.int 1)) "foo" [.int 2] none) = .unknown := by
  simp [check, infer, illTyped, tableRefutes, defTy, sigOf, declFor, declOf?, declsFor, baseDecls, tyClassNames, declsOf]

/-- `q = 1; q + nil` — srb 7002. We abstain because `defTy` has no environment,
    so a local has no unconditional type. The obvious next widening. -/
example :
    check (.seq [ .vasgn .lvar "q" (.int 1),
                  .send (some (.var .lvar "q")) "+" [.nil] none ]) = .unknown := by
  simp [check, infer, inferSeq, illTyped, illTypedAny, tableRefutes, defTy,
    sigOf, declFor, declOf?, declsFor, baseDecls, tyClassNames, declsOf, envSet, envGet?]

end RubyCore.Types
