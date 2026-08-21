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

**D12 renames the parts of that sentence without changing any of them.** The
reported decision is total — `accept` or `reject` — and `reject` means *the
checker did not certify this program*, which claims nothing at all. The verdict
above is retained as the decision's **basis**: `refuted` is the paragraph you have
just read (our rules refute, guarded by `reject ⇒ srb rejects`), `uncertified` is
the abstention below. Only the first has ever had an obligation, which is why the
two are not collapsed. See `decisionOf` and the §D12 note at the file's end.

**Bias toward `uncertified`** (called `unknown` above and everywhere before D12).
**Every source of doubt resolves to it**:
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

/-! ## Declaration-free expressions

The side condition monotonicity needs, and the reason it is syntactic rather
than semantic.

`infer` is **not** monotone in the declaration table, and there is exactly one
rule that makes it so: `def`'s guard is `declaresName D name = false`, which a
larger table can falsify. Every other rule reads the table only through
`sigOf`, and `sigOf` *is* monotone under `SubDecls` — so an expression with no
`def` in it infers the same way at any larger table.

That matters because the invariant has to survive its own program's later
declarations. A method body is checked where the `def` appears and *called*
later, by which time more rows are in force, and `UserConforms` — the checker's
own verdict on the body, carried inside the soundness invariant — has to still
hold. `infer_mono` (`Proof/Static/Mono.lean`) is that step, and this predicate
is its hypothesis.

`class'` is excluded along with `def`, and not because a class body is a
declaration: it is excluded because a class body *contains* them, so admitting
it here would make the predicate a lie about the rows in force after it. Both
exclusions are what the `def` rule and `UserConforms` will require of a body,
which is a genuine narrowing of the fragment — a method may not define a method
— and a narrowing real Ruby rarely needs.
-/

/-- Is this expression the literal `self`? A `Bool` rather than `DecidableEq` on
    `Expr`, which the type does not have and which would be a large derivation for
    one guard. -/
def isSelf : Expr → Bool
  | .self' => true
  | _ => false

mutual

/-- No `def` (and no `class`) anywhere in the expression. -/
def defFree (e : Expr) : Bool :=
  match e with
  | .def' _ _ _ => false
  | .class' _ _ _ => false
  | .seq es => defFreeAll es
  | .if' c t els =>
    defFree c && defFree t && (match els with | some e' => defFree e' | none => true)
  | .while' c b => defFree c && defFree b
  | .vasgn _ _ rhs => defFree rhs
  | .send r _ args _ =>
    (match r with | some r' => defFree r' | none => true) && defFreeAll args
  -- **L174.** Not optional: `infer`'s `.array` arm threads the table through the
  -- elements via `inferSeq`, so an element `def` really does change it, and
  -- `infer_mono`'s `D₀ = D` conclusion would be false with this arm left in the
  -- catchall's vacuous `true`. A predicate that is vacuous *because* the head is
  -- out of the fragment stops being vacuous the moment the head is admitted.
  | .array es => defFreeAll es
  -- **L200.** Same reason as `.array`'s, one rung later: `infer`'s `.ret` arm threads
  -- the table through the returned expression, so a `def` in there really does change
  -- it and `infer_mono`'s `D₀ = D` half would be false with the catch-all's vacuous
  -- `true` left in place. Third time this exact trap has been walked into
  -- (`.array` at L174, `.vasgn .ivar` at L191), which is why it is a comment.
  | .ret e => match e with | some e' => defFree e' | none => true
  -- **L205.** Fourth time (`.array` L174, `.vasgn .ivar` L191, `.ret` L200): `infer`'s
  -- `.cpath (some base)` arm threads the table through the base, so a `def` in there
  -- really does change it and `infer_mono`'s `D₀ = D` half would be **false** with the
  -- catch-all's vacuous `true` left in place. `infer_mono_all`'s new case is what found
  -- it, one minute after the arm was written.
  | .cpath base _ => match base with | some b => defFree b | none => true
  -- **L212.** Fifth time (`.array` L174, `.vasgn .ivar` L191, `.ret` L200, `.cpath`
  -- L205): `infer`'s `.super'` arm threads the table through the arguments via
  -- `inferArgs`, so a `def` in one really does change it and `infer_mono`'s `D₀ = D`
  -- half would be **false** with the catch-all's vacuous `true` left in place. Written
  -- with the arm rather than after `infer_mono_all` complained, which is the first time
  -- that has happened.
  | .super' args blk =>
    defFreeAll args && (match blk with | some b => defFree b | none => true)
  -- **L214.** `.zsuper`'s arm reads the *context*, not a subexpression, so this one is
  -- vacuous on its own — but the catch-all's `true` is only *right* by accident, and the
  -- sixth walk into that trap is one comment too many. Stated for the block slot, which
  -- is the only subexpression the head has.
  | .zsuper blk => match blk with | some b => defFree b | none => true
  -- Every other head is either a leaf or outside `infer`'s domain, where the
  -- predicate is vacuous: `infer` answers `none`, so no hypothesis mentioning it
  -- can be satisfied.
  | _ => true
termination_by sizeOf e

def defFreeAll (es : List Expr) : Bool :=
  match es with
  | [] => true
  | e :: rest => defFree e && defFreeAll rest
termination_by sizeOf es

end

/-! `defFree`'s own equation lemmas carry the *earlier patterns did not match*
side conditions that a catch-all arm forces, so `simp [defFree]` cannot fire on
any of the compound shapes. These are the unconditional forms, and they are what
`Proof/Static/Mono.lean`'s induction rewrites with. -/

@[simp] theorem defFree_seq (es : List Expr) : defFree (.seq es) = defFreeAll es := by
  rw [defFree.eq_def]

@[simp] theorem defFree_if (c t : Expr) (els : Option Expr) :
    defFree (.if' c t els)
      = (defFree c && defFree t && (match els with | some e' => defFree e' | none => true)) := by
  rw [defFree.eq_def]

@[simp] theorem defFree_while (c b : Expr) :
    defFree (.while' c b) = (defFree c && defFree b) := by rw [defFree.eq_def]

@[simp] theorem defFree_vasgn (k : VarKind) (x : String) (rhs : Expr) :
    defFree (.vasgn k x rhs) = defFree rhs := by rw [defFree.eq_def]

@[simp] theorem defFree_send (r : Option Expr) (m : String) (args : List Expr)
    (blk : Option Expr) :
    defFree (.send r m args blk)
      = ((match r with | some r' => defFree r' | none => true) && defFreeAll args) := by
  rw [defFree.eq_def]

@[simp] theorem defFreeAll_nil : defFreeAll [] = true := by rw [defFreeAll.eq_def]

@[simp] theorem defFreeAll_cons (e : Expr) (rest : List Expr) :
    defFreeAll (e :: rest) = (defFree e && defFreeAll rest) := by rw [defFreeAll.eq_def]

mutual

/-- `infer D Γ e = some (τ, Γ', D')` — `e` has type `τ`, leaves the environment
    `Γ'` and leaves the declarations `D'` in force. `none` is `unknown`: outside
    the P0 fragment, or ill-typed.

    **The declaration table is threaded exactly as the environment is** (F1b.8),
    and the reason is the same one the header gives for `Γ`: Ruby methods are
    *installed*, not declared, so the set of signatures a call site may rely on
    is a function of where in the program the call site is. `declsOf` has been a
    constant function since F1a with a program-supplied row named as later work
    in two documents; it is not later work but a soundness condition, because
    `initiation` obliges `DeclsOk` at the **boot** heap and a row synthesized
    from the program's own `class C; def foo; …` cannot resolve there. Threading
    is what lets the row come into force *at the step that installs the method*.

    Today no rule grows the table — every arm returns the `D` it was handed — so
    this commit changes no verdict, which is the same argument L137 makes for
    heap-indexing a judgement whose arms do not yet read the heap.

    **`top` is the toplevel-position flag** (L155), and it exists for exactly one
    future rule: `class C … end` reopens a constant looked up in the *current
    definee's* own constant table (`enterClassBody`'s `constOwn m.currentFrame.defmod`,
    `Interp/Dispatch.lean:236`), and the only definee whose table an invariant can
    describe is `Object`. So the rule is admissible in a toplevel position and
    nowhere else, and `infer` has to be able to tell the two apart.

    **The flag is redundant with something the judgement already carries, which is
    why it costs one parameter rather than an index.** `CtlOk` reads it off the
    *environment stack* — `Γs.isEmpty`, i.e. no enclosing activation — and
    `KontOk.frameK` is already the constructor at which that stack pops, so the
    mode flips exactly where the definee does. The alternative considered and
    rejected was a genuine `Bool` index on `KontOk`: it needs the caller's definee
    at the `frameK` *pop*, which `KontOk` cannot see, and recovering it costs a
    stack-depth index that `Γs.length` already is.

    **Threaded through every subexpression evaluated in the *same activation*,
    and blocked at exactly the two that are not** — a `def` body and (F1b.6) a
    class body, both of which run in a frame `enterUserMethod`/`enterClassBody`
    pushes. That split is forced rather than chosen: `CtlOk` reads the mode off
    the environment stack, so a subexpression the machine evaluates without
    pushing a frame is read at the *enclosing* mode, and checking it at any other
    would leave `KontOk` unable to state its own hypothesis. -/
def infer (D : Decls) (Γ : Env) (e : Expr) (top : Bool := false)
    (ctx : FrameCtx := { cls := "Object" }) : Option (Ty × Env × Decls) :=
  match e with
  | .int _ => some (.int, Γ, D)
  | .tru => some (.bool, Γ, D)
  | .fls => some (.bool, Γ, D)
  | .nil => some (.nilT, Γ, D)
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
  -- `LitClsOk` — *the boot `String` id is a class named `"String"`* — which is
  -- the same put-the-condition-in-the-judgement move as `NoHook`'s bound (L149).
  | .str _ => some (.cls "String", Γ, D)
  -- **A symbol literal** (L159). `Ty.sym` has existed since P0 — a `def`
  -- evaluates to one — and this is the rule for *writing* one, which nothing had
  -- needed until the slice was measured: `homebrew/fragment-gap.py` ranks `sym`
  -- third by nodes (**281**) and joint-first by files (**all 8**), against a rule
  -- that is one line and a consecution case that is four. Immediate, like the
  -- other literals: `evalExpr` answers `.value (.sym s)` with no heap write
  -- (`Interp.lean:127`), so nothing is owed beyond `ValueTy … .sym`, which is
  -- `rfl`.
  --
  -- Not added to `defTy`, following L151's precedent for `.str`: widening the
  -- *refutation* pass is a separate decision with a separate guard
  -- (`reject ⇒ srb rejects` is a difftest direction, not a theorem).
  | .sym _ => some (.sym, Γ, D)
  | .var .lvar x => (envGet? Γ x).map (fun τ => (τ, Γ, D))
  -- **`self`, in a method body** (F1b.11). `evalExpr` answers the current frame's
  -- `self` with no heap write (`Interp.lean:131`), so the rule is as cheap as a
  -- literal's — what it costs is the *invariant* clause that says the frame's self
  -- really has that type, which `StackCtx` now carries.
  --
  -- `selfCls` is `none` in a class body and at toplevel, and that is a refusal
  -- rather than an omission: in a class body `self` is the **class object**, which
  -- `plainRecv` excludes and `valueTy?` gives no type at all.
  | .self' =>
    match ctx.selfCls with
    | some c => some (.cls c, Γ, D)
    | none => none
  -- **An implicit-self zero-argument send** (F1b.11) — the `vcall`, and the
  -- construct the slice's *verdict* ratchet ranks first: 14 of its 92 method
  -- bodies are blocked by this alone, every one of them a call to a user-defined
  -- accessor, which is exactly what a program-supplied row is (F1b.10).
  --
  -- One step, like `.self'` and unlike `recvK0`: the receiver is already a value,
  -- so `evalExpr` goes straight to `startArgs … [] []`, which is `finishSend`
  -- (`Interp.lean:210`). There is no continuation to push and therefore no `KontOk`
  -- constructor — the dispatch happens *in this step*, which makes it the shortest
  -- send rule in the fragment and the only one with no kont at all.
  --
  -- The send **site** is `.vcall`, not `.explicit`, and that is visible to the
  -- machine: `visError?` lets an implicit-self send reach a *private* method. The
  -- fragment does not exploit that — `ResolvesUser` still demands `.pub` — but the
  -- dispatch lemmas had to be generalized over the site to state the case at all.
  | .vcall mname =>
    match ctx.selfCls with
    | some c =>
      match sigOf D (.cls c) mname with
      | some ([], τret) => some (τret, Γ, D)
      | _ => none
    | none => none
  | .vasgn .lvar x rhs =>
    match infer D Γ rhs top ctx with
    | some (τ, Γ₁, D₁) => some (τ, envSet Γ₁ x τ, D₁)
    | none => none
  -- **`@x = e`** (L191). The rule is a *guard* plus the right-hand side's own
  -- answer, and the guard is `selfCls`.
  --
  -- Why that guard and not something about `x`: `applyKont`'s ivar arm raises
  -- `FrozenError` when the frame's `self` is frozen — and when it is an *immediate*,
  -- since those are frozen (`Interp/Kont.lean:35`) — and a raise is a `.jump`, which
  -- `CtlOk` refuses outright. So admitting the write means knowing `self` is a plain
  -- unfrozen reference. `selfCls = some c` is exactly that, via `StackCtx`'s F1b.11
  -- clause and `plainRecv`'s L191 one: a class body or the toplevel answers `none`
  -- here, and both are frames where `self` is a class object rather than an instance.
  --
  -- **The environment does not move.** The invariant tracks locals, not instance
  -- variables, so there is nothing to record — and that asymmetry is also why the
  -- matching *read* `@x` stays out of the fragment: a write needs only that it does
  -- not raise, while a read needs a type to answer with, which would take a
  -- per-class ivar table this judgement does not have.
  | .vasgn .ivar x rhs =>
    match ctx.selfCls with
    | some c =>
      match infer D Γ rhs top ctx with
      | some (τ, Γ₁, D₁) =>
        -- **L196: a declared ivar constrains the write.** L191 admitted `@x = e`
        -- freely, and could, because nothing claimed anything about instance
        -- variables. `D.ivars` is exactly such a claim — quantified over *every*
        -- object of the class, since an ivar read has no receiver to constrain — so
        -- the write owes conformance to it. An **undeclared** ivar is still free:
        -- there is no row to break.
        match ivarTy? D₁ c x with
        | some σ => if subTy τ σ then some (τ, Γ₁, D₁) else none
        | none => some (τ, Γ₁, D₁)
      | none => none
    | none => none
  -- **An instance-variable read** (L196), and the two halves of the answer are both
  -- forced by the machine.
  --
  -- `selfCls` because `evalExpr` reads the frame's `self` (`Interp.lean:139`), and
  -- the invariant knows that object only by its class — which is why `IvarOk` is
  -- quantified over every instance rather than over a receiver.
  --
  -- **`mkNilable`**, because an *unset* ivar reads as `nil`: `evalExpr` ends
  -- `.getD .nil`, so the type has to admit it. Answering `σ` would be unsound and
  -- answering it *soundly* needs definite-assignment tracking through `initialize`,
  -- which is Wall 2's rung. This is where L193's `nilable` pays for itself a second
  -- time, in a rule that has nothing to do with `if`.
  | .var .ivar x =>
    match ctx.selfCls with
    | some c =>
      match ivarTy? D c x with
      | some σ => some (mkNilable σ, Γ, D)
      | none => none
    | none => none
  -- Binary send to a builtin, any receiver expression, no block. Wrong arity, a
  -- block, or two or more arguments is still `unknown`.
  | .send (some recv) mname (arg :: args) none =>
    -- **The signature is read after the arguments, not before** (F1b.8). The three
    -- tests are independent — each failure is `none` — so the order is free, and
    -- what fixes it is the *continuation*: an `argsK` exists once the receiver and
    -- some prefix of the arguments have run, so the table it is indexed by is the
    -- one that prefix left, and `KontOk.argsK`'s signature premise has to be
    -- readable at the table the **last** argument leaves.
    --
    -- **A literal `self` receiver is admitted** (L172). F1b.11 excluded it, and the
    -- reason was a fact about the machine rather than about types: `evalExpr` picks
    -- the send *site* syntactically, so `self.foo` is a `.selfRecv` send and takes a
    -- different path through `visError?` than `.explicit`.
    --
    -- **Any positive arity** (L175). `startArgs` walks the argument list one at a
    -- time, pushing one `argsK` per argument, so the rule's shape is `inferArgs` —
    -- the list of argument *types*, in order, matched against the whole parameter
    -- list. The zero-argument case is a separate arm because it is a different
    -- number of steps: `startArgs … [] []` is `finishSend`, so no `argsK` is pushed
    -- at all (`KontOk.recvK0`).
    match infer D Γ recv top ctx with
    | some (τr, Γ₁, D₁) =>
      match inferArgs D₁ Γ₁ (arg :: args) top ctx with
      | some (τs, Γ₂, D₂) =>
        match sigOf D₂ τr mname with
        | some (ps, τret) => if subTys τs ps then some (τret, Γ₂, D₂) else none
        | none => none
      | none => none
    | none => none
  -- **A zero-argument send** (L152). Split from the positive-arity rule rather than
  -- folded into it, because the two are *different machine shapes*: with arguments
  -- the receiver's `recvK` pushes an `argsK` and dispatch happens a step later,
  -- while with none `applyKont` runs `startArgs … [] []`, which is `finishSend` — so
  -- the send completes in the `recvK` step itself and needs its own `KontOk`
  -- constructor and its own consecution case (`KontOk.recvK0`).
  | .send (some recv) mname [] none =>
    match infer D Γ recv top ctx with
    | some (τr, Γ₁, D₁) =>
      match sigOf D₁ τr mname with
      | some ([], τret) => some (τret, Γ₁, D₁)
      | _ => none
    | none => none
  -- **A written receiverless call** (L170/L171/L175): `foo`, `foo()`, `foo(x, y)`.
  -- The *typing* is the `vcall` rule with an argument list — same receiver (the
  -- frame's `self`), same table read — and the *machine* difference is one
  -- `SendSite` constructor: `evalExpr` answers both with
  -- `startArgs m self site mname [] args`, and `visError?` is `none` for every site
  -- but `.explicit`.
  --
  -- Kept as its own arm rather than folded into `.vcall`'s because the two are
  -- different `Expr` constructors and `step_ok`'s case analysis splits on the
  -- constructor: folding them would mean an `infer` arm no case of the
  -- preservation proof is indexed by.
  | .send none mname [] none =>
    match ctx.selfCls with
    | some c =>
      match sigOf D (.cls c) mname with
      | some ([], τret) => some (τret, Γ, D)
      | _ => none
    | none => none
  -- The same, with arguments. **There is no `recvK` in this chain** — the receiver
  -- is already a value — so the arguments run starting in *this* step and the
  -- answer's environment and table are the ones the last argument leaves, which is
  -- exactly what `CtlOk` then hands `KontOk.argsK`.
  | .send none mname (arg :: args) none =>
    match ctx.selfCls with
    | some c =>
      match inferArgs D Γ (arg :: args) top ctx with
      | some (τs, Γ₁, D₁) =>
        match sigOf D₁ (.cls c) mname with
        | some (ps, τret) => if subTys τs ps then some (τret, Γ₁, D₁) else none
        | none => none
      | none => none
    | none => none
  -- **A constant read** (L189), and it is the first `Expr` head to *produce* a
  -- class-object type — the arm L184/L185 built with no producer.
  --
  -- **Keyed on the *table* since L195**, not on a global list, and that is what lets
  -- `T` in: a global list cannot name a constant that exists only at the
  -- prelude-booted heap, because `check_sound` establishes `Inv` at the bare boot one
  -- (L194 measured the failure). A declaration has no such problem — `Inv` already
  -- ∃-quantifies the table and `DeclsOk` ties it to the heap — so the boot-safe and
  -- prelude-aware tables are two *tables*, each sound at the heap it describes.
  --
  -- It also generalizes for free: the type comes from the row rather than from the
  -- name, so `HEAD_VERSION_REGEX : Regexp` is this same rule at a different `Ty`.
  --
  -- `DeclsOk`'s constant clause is three conjuncts, not the seven `ClassOk` carried,
  -- because `ValueTy h v (.clsOf n)` *already* means "a class-object receiver named
  -- `n`". What it needs is —
  -- `constOwn Object n` answers a class object, that object is named `n`, it is not
  -- one of the two ids `invoke` dispatches singleton families from, and **`Object`
  -- is its sole owner** (L189's clause). The last is what makes the rule need no
  -- frame clause at all: `evalExpr`'s `.const` walks the frame's `cref` *before* the
  -- ancestors, and sole ownership means any `cref` hit is `Object`'s whatever the
  -- `cref` is (`constRead_sole`).
  --
  -- One step and no continuation: `evalExpr` answers `.value` directly, so this arm
  -- adds **no `KontOk` constructor** — the third rule in the fragment with that
  -- property, after `.self'` and `.vcall`.
  | .const n =>
    match constTy? D n with
    | some τ => some (τ, Γ, D)
    | none => none
  -- **An array literal** (L174), and it is L151's string-literal producer with a
  -- list in front of it: `continueArray` evaluates the elements left to right and
  -- then `Builtins.allocArr`s one fresh plain `Array` — the *same* `Heap.alloc` of
  -- a non-class object, at `Boot.arrayId` instead of `Boot.stringId`. So the value
  -- half is `valueTy_alloc_fresh` again and the invariant clause is the second
  -- conjunct of `LitClsOk` (which is what `StrClsOk` was renamed to when it stopped
  -- being about one literal).
  --
  -- **The element types are erased**, which is what makes the rule this cheap:
  -- `Ty` has no `Array τ`, so nothing has to be joined across the elements and the
  -- only thing the traversal owes is the *threading* — the environment and table
  -- the elements leave. That is exactly `inferSeq`, evaluated in the same
  -- left-to-right order by `continueArray` as by `evalExpr`'s `.seq`, so this arm
  -- reuses the existing third motive rather than adding a fourth mutual function.
  --
  -- A `splat`, `kwargs` or `fwd` element needs no guard: `infer` has no arm for
  -- any of them, so `inferSeq` answers `none` and the consecution case recovers
  -- *not a splat* from the element's own accepting judgement (the `recvK` case's
  -- `hsp` move).
  | .array es =>
    match inferSeq D Γ es top ctx with
    | some (_, Γ', D') => some (.cls "Array", Γ', D')
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
  --
  -- **F1b.10: the rule now *declares*.** A `def` the four conditions below admit
  -- adds a row `ctx#name : [] → <the body's type>` to the table in force for the
  -- rest of the program, which is what a call to it reads. Everything about the
  -- shape of that row is forced by what `ResolvesUser` requires of the `MethodDef`
  -- `evalExpr` builds, and each of the four is one of those requirements:
  --
  -- * **`¬ top`** — a *toplevel* `def` installs a **private** method
  --   (`Interp.lean:225`: `if currentFrame.kind == .toplevel then .priv`), and
  --   `ResolvesUser` requires `.pub`. So a toplevel row is unwitnessable, not
  --   merely weak. The `def` is still admitted, it just declares nothing.
  -- * **`name ≠ "initialize"`** — private for the same rule, one line earlier.
  -- * **`reopenableClasses.contains ctx`** — the row obliges *every* class object
  --   named `ctx`, and `ClassOk`'s uniqueness clause is stated at the names in that
  --   table (F1b.9). Not a restriction on where a `def` may appear: `class C … end`
  --   is admitted for exactly those names anyway.
  -- * **`defFree body`** — the body's typing is carried in the invariant and has to
  --   survive the program's *later* declarations, which is `infer_mono`, whose
  --   hypothesis this is (L161). A declared method may not itself declare one.
  --
  -- The body must also leave the table as it found it, for the same reason the
  -- class-body rule's stability condition existed: `KontOk.frameK` carries one
  -- table. That is implied by `defFree` and checked anyway, because the rule reads
  -- the body's output.
  | .def' name params body =>
    if params.isEmpty ∧ declaresName D name = false ∧ name ≠ "method_added" then
      -- The body is checked even though nothing can call it yet. Skipping the
      -- check would accept more programs *now* and fewer once calls arrive,
      -- which is a ratchet regression; the fragment only ever grows.
      -- **`ret := none` explicitly** (L198), not inherited: a `def` computes its
      -- return type *from* the body, so it cannot name one for the body to check a
      -- `return` against. Inheriting `ctx.ret` would be worse than wrong — it would
      -- check the inner body's returns against the *enclosing* method's type.
      -- L207 set this to `none` **explicitly**, because `{ ctx with … }` would inherit
      -- the *enclosing* method's name, which is not this body's. **L210 sets it to
      -- `some name`** — the body is this method's, so the context that types it names
      -- this method, and that is the channel `super` reads. The obligation it creates
      -- is on the machine side, where `userFrame` builds `meth := md.superName.getD
      -- mname`: `ResolvesUser` now carries `md.superName = none`, which is true of
      -- every `def` (only `alias` sets the field) and is what makes the two agree.
      -- **L214: `params := []` explicitly**, and the explicitness is L207's point again —
      -- `{ ctx with … }` would inherit the *enclosing* method's parameter types, which are
      -- not this body's. The rule requires `params.isEmpty` anyway, so `[]` is the truth
      -- and not an approximation.
      match infer D [] body false
          { ctx with selfCls := some ctx.cls, ret := none, meth := some name,
                     params := some [] } with
      | some (τb, _, Db) =>
        if Db = D then
          -- **`groundClassNames` is excluded** (L189). `reopenableClasses` grew to
          -- eight names, five of which are the classes the *ground* arms of `Ty`
          -- denote — and `tyClassNames` subtracts those from the class arm's range,
          -- so a row keyed on one would owe `EntryOk` over receivers the row was
          -- never about (`Types/Decls.lean`'s note on that subtraction).
          -- `DeclsOk_addRow` says so in its hypotheses; this is the rule keeping
          -- them true.
          -- **`ctx.ret.isNone`** (L200), and it costs nothing while buying the last
          -- fact the `return` rule needs. A `def` is the *only* arm that grows the
          -- table at `top = false` (`class'` needs `top = true`), so refusing the row
          -- when the enclosing method declares a return type makes the table
          -- **constant along every continuation chain inside such a body** — which is
          -- what `KontOk.retOk` needs and could not get from `defFree`, because
          -- `KontOk`'s constructors carry the `infer` equations without it.
          --
          -- Free: no shipped table declares a return type (L198 — `def` supplies
          -- `r = none`, and `some d.ret` waits for W8's `sig`). And it *refuses the
          -- row*, not the program: the `else` branch below still types the `def`, it
          -- just declares nothing — which `UserConforms`' `defFree` was already doing
          -- to such a body anyway.
          if top = false ∧ name ≠ "initialize" ∧ reopenableClasses.contains ctx.cls ∧
              groundClassNames.contains ctx.cls = false ∧ defFree body = true ∧
              ctx.ret.isNone then
            some (.sym, Γ, addRow D ctx.cls name { params := [], ret := τb })
          else some (.sym, Γ, D)
        else none
      | none => none
    else none
  -- **Reopening a class** (F1b.6, L156). Three restrictions, and each one names a
  -- branch of `enterClassBody` the invariant cannot survive rather than a matter of
  -- taste:
  --
  -- * `top` — the reopen lookup is `constOwn m.currentFrame.defmod name`, the
  --   definee's *own* constant table, and `Object`'s is the only one `Inv`
  --   describes (`BottomObj`, L155).
  -- * `sup.isNone` — an explicit superclass evaluates first (`classDefK`) and then
  --   has to *match*, and a mismatch is `raiseErr`.
  -- * `reopenableClasses.contains name` — the promise that the constant is there
  --   and is a non-module class, so the step is neither an allocation nor a
  --   `TypeError`. `Types/Decls.lean` says why that is a table.
  --
  -- The body is checked in the **empty** environment at `top := false`, because
  -- `enterClassBody` pushes a frame with no locals and a definee that is the class.
  -- The value is the body's: the frame pops through `frameK` and the body's value
  -- is what the caller sees, so the type is the body's and the environment is the
  -- caller's, untouched.
  | .class' name sup body =>
    if top ∧ sup.isNone ∧ reopenableClasses.contains name then
      -- **The body must leave the table as it found it** (F1b.8), which is the
      -- same stability condition `LoopOk` and `UserConforms` carry and is here
      -- for the same reason: `KontOk.frameK` resumes the caller at a table fixed
      -- when the frame was pushed, so a class body whose `def`s changed it would
      -- pop into a continuation typed against the wrong one. Inert today, since
      -- no rule grows the table — and it is precisely what the *next* rung has to
      -- revisit, because a class body's `def`s are the rows that are supposed to
      -- escape. Recorded as a refusal rather than left implicit so that widening
      -- `def` breaks the build here (constraint 4) instead of silently.
      -- **F1b.10: the body's declarations escape.** A class body's `def`s are
      -- exactly the rows that are supposed to outlive it, and the stability
      -- condition F1b.8 put here was the placeholder for deciding how. The answer
      -- is that they escape and `frameK` still carries **one** table: the caller's
      -- continuation is typed at `Db` because that is what this rule returns, so
      -- the table the frame pops into is the one the body ended at. No antitone
      -- step, and no second index.
      match infer D [] body false { cls := name } with
      | some (τ, _, Db) => some (τ, Γ, Db)
      | none => none
    else none
  | .seq es => inferSeq D Γ es top ctx
  | .if' c t els =>
    match infer D Γ c top ctx with
    | some (_, Γ₁, D₁) => inferIf D₁ Γ₁ t els top ctx
    | none => none
  | .while' c body =>
    -- The loop re-enters the condition with the environment the body leaves, so
    -- both must be *stable* at `Γ`. This is the P0 stand-in for a fixpoint.
    --
    -- **Stability is now about the declaration table too** (F1b.8): a loop whose
    -- body declares a method would put a different table in force on the second
    -- iteration than the one the first was checked at, and there is no single `D`
    -- to index the two loop konts by. Same argument as `Γ`, and the same shape.
    match infer D Γ c top ctx with
    | some (_, Γ₁, D₁) =>
      if Γ₁ = Γ ∧ D₁ = D then
        match infer D Γ body top ctx with
        | some (_, Γ₂, D₂) => if Γ₂ = Γ ∧ D₂ = D then some (.nilT, Γ, D) else none
        | none => none
      else none
    | none => none
  -- **`return e`** (L200), and it is a *guard* plus a conformance check.
  --
  -- The guard is `ctx.ret`: a `return` has a target only inside a method activation
  -- that declares a return type, and a class body or the toplevel declares none — the
  -- desugarer gates a toplevel `return` for the same reason. `StackCtx`'s L198/L200
  -- clause is what turns `ret.isSome` into *this frame is a `.method` with a caller*,
  -- which is what `returnTarget` (`Interp/Support.lean:349`) needs.
  --
  -- The check is `subTy τ σ` against the **declared** type, which is what makes the
  -- rule local: it never needs to know what the rest of the body will answer.
  --
  -- **The answer is `.nilT`, and it is free**: the value never reaches this
  -- continuation — the machine jumps — so any answer is sound, and `KontOk.retValK`'s
  -- conclusion index is the *returned* type rather than this one. `.nilT` is the
  -- honest reading (*nothing comes back here*) and it composes well: `return X if c`
  -- joins with the missing `else`'s `nil` to `nilT` rather than to a nilable.
  | .ret e =>
    match ctx.ret with
    | some σ =>
      match e with
      | some e' =>
        match infer D Γ e' top ctx with
        | some (τ, Γ₁, D₁) => if subTy τ σ then some (.nilT, Γ₁, D₁) else none
        | none => none
      -- A bare `return` yields `nil`, so the declared type has to admit it.
      | none => if subTy .nilT σ then some (.nilT, Γ, D) else none
    | none => none
  -- **`::n`, an absolute constant read** (L203) — and it is the *same table read* as
  -- `.const n`, one lookup shorter.
  --
  -- `evalExpr`'s `.cpath none` arm is `constLookup m.heap n`, which is `Object`'s own
  -- constant table and nothing else: no cref walk, no ancestors. So this arm needs
  -- neither a new table (`Decls.consts` is keyed on the name, which is what an
  -- absolute path *is*) nor `ConstOk`'s third conjunct — sole ownership is what makes
  -- a *relative* read land on `Object`, and an absolute one starts there.
  --
  -- Nothing is admitted with a **scope** (`A::B`). That is a second rule and a second
  -- table — a scoped constant is keyed on the *pair*, like `Decls.ivars` — plus a
  -- `KontOk` arm for the base's evaluation. The slice's census says which one pays:
  -- 86 of its 99 `cpath` nodes are `::Regexp` from a regex literal, absolute.
  | .cpath none n =>
    match constTy? D n with
    | some τ => some (τ, Γ, D)
    | none => none
  -- **`C::n`, a scoped constant read** (L205), and it is the *other* lookup: where
  -- `::n` is `Object`'s own table, this is `constLookupFrom` — the ancestors walk from
  -- the class object the base evaluates to (`Interp/Kont.lean`'s `.cpathK`).
  --
  -- The base must type at a **class object**, which is the only `Ty` a namespace can
  -- have, and `.clsOf`'s name is the table key. Everything else about the delivery —
  -- that the container is a class, that the constant is not `private_constant`, that
  -- the walk finds a value of the declared type — is `ScopedConstOk`, carried on the
  -- `cpathK` continuation rather than re-derived at the delivery.
  | .cpath (some base) n =>
    match infer D Γ base top ctx with
    | some (.clsOf cname, Γ₁, D₁) =>
      match scopedConstTy? D₁ cname n with
      | some τ => some (τ, Γ₁, D₁)
      | none => none
    | _ => none
  -- **A float literal** (L202), placed here rather than beside `.int` on purpose:
  -- inserting an arm shifts every later case number in `infer.induct`, and the only
  -- case after this one is the catch-all. The rule itself is `.int`'s verbatim, and
  -- what it buys is measured in `implementation-notes.md`: three slice bodies stop
  -- being out of fragment and start naming a declaration they need.
  -- **A float literal** (L202), placed here rather than beside `.int` on purpose:
  -- inserting an arm shifts every later case number in `infer.induct`.
  | .flt _ => some (.float, Γ, D)
  -- **`super(args)`** (L212), placed *last* for `.flt`'s reason (L202): inserting an
  -- arm shifts every later case number in `infer.induct`, and `Proof/Static/Mono.lean`
  -- addresses its cases by number. Measured — the arms were written beside `.send`
  -- first, and `Mono.lean` broke at nine places.
  --
  -- The whole rule is *which table to read*. The name
  -- comes off the context (`ctx.meth`, L210's channel) rather than out of the
  -- expression, because `super` does not name its target: `doSuper` re-dispatches the
  -- **running** method starting after the frame's definee. So the key is the pair
  -- `(ctx.cls, mn)` and the table is `supers`, which is why that table exists.
  --
  -- Three guards, each paying for one thing `doSuper` can do that is not a value:
  --
  -- * `ctx.meth = some mn` — outside a method body there is no name to re-dispatch,
  --   and `doSuper` answers `.unsupported`.
  -- * `mn ≠ ""` — the empty name is `doSuper`'s own *"super outside a method"* test
  --   (`Interp/Send.lean:263`), and `StepOk` refuses `.unsupported`, so the rule has
  --   to rule it out rather than hope no row is keyed there.
  -- * `subTys τs d.params` — the arity and the argument types, exactly as a send's.
  --
  -- **Bare `super` (`.zsuper`) is *not* this rule**, and the reason is not laziness:
  -- it forwards the enclosing method's *parameter values*, so its argument types are
  -- the parameters' declared types, and neither `FrameCtx` nor `Γ` says which locals
  -- are parameters (L207, finding 2). That needs a second channel.
  | .super' [] none =>
    match ctx.meth with
    | some mn =>
      if mn ≠ "" then
        match superDecl? D ctx.cls mn with
        | some d => if d.params.isEmpty then some (d.ret, Γ, D) else none
        | none => none
      else none
    | none => none
  -- The positive-arity form. **The table is read after the arguments** for the
  -- `.send`-arm reason (F1b.8): a `superArgK` exists once some prefix of the arguments
  -- has run, so `KontOk.superArgsK`'s signature premise has to be readable at the
  -- table the *last* argument leaves. `SubDecls` pins `supers` equal, so the two
  -- readings agree — but the rule is written at the one the continuation can state.
  | .super' (arg :: args) none =>
    match ctx.meth with
    | some mn =>
      if mn ≠ "" then
        match inferArgs D Γ (arg :: args) top ctx with
        | some (τs, Γ₁, D₁) =>
          match superDecl? D₁ ctx.cls mn with
          | some d => if subTys τs d.params then some (d.ret, Γ₁, D₁) else none
          | none => none
        | none => none
      else none
    | none => none
  -- **Bare `super`** (L214), and it is `super(args)`'s rule with the argument list read
  -- off the *context* instead of out of the expression. `zsuperArgs` forwards the
  -- enclosing method's parameter **values**, so the argument types are the parameters'
  -- declared types — `ctx.params`, L214's channel — and there is no `inferArgs` and no
  -- continuation: `evalExpr` reconstructs the arguments and dispatches in one step.
  --
  -- The fourth guard is new and it is `zsuperArgs`' own refusals: it answers `none` for a
  -- `define_method` body (`runFromDM`) and for destructuring parameters, both of which
  -- are `.unsupported` and therefore stuck. `StackCtx`'s L214 clause is what rules them
  -- out, so the *rule* does not test them — which is the one place this rule is cheaper
  -- than `super(args)` rather than the same.
  | .zsuper none =>
    match ctx.meth, ctx.params with
    | some mn, some ps =>
      if mn ≠ "" then
        match superDecl? D ctx.cls mn with
        | some d => if subTys ps d.params then some (d.ret, Γ, D) else none
        | none => none
      else none
    | _, _ => none
  | _ => none
termination_by sizeOf e

/-- Statement sequence: thread the environment, take the last type. Mirrors
    `evalExpr`'s three-way split on `.seq` (`Interp.lean:2732`) exactly — in
    particular `[e]` steps straight to `e` with no `seqK` pushed. -/
def inferSeq (D : Decls) (Γ : Env) (es : List Expr) (top : Bool := false)
    (ctx : FrameCtx := { cls := "Object" }) : Option (Ty × Env × Decls) :=
  match es with
  | [] => some (.nilT, Γ, D)
  | [e] => infer D Γ e top ctx
  | e :: rest =>
    match infer D Γ e top ctx with
    | some (_, Γ₁, D₁) => inferSeq D₁ Γ₁ rest top ctx
    | none => none
termination_by sizeOf es

/-- **The argument list of a send** (L175), and the reason it is a *fourth*
    mutual function rather than a use of `inferSeq`: a send needs the arguments'
    **types**, in order, to match against the signature's parameter list, where an
    array literal and a statement sequence each need only the threading.

    Mirrors `startArgs`' own loop (`Interp/Send.lean:455`) arm for arm — one
    argument at a time, left to right, threading both the environment and the
    table — and refuses nothing by name: `.splat`, `.kwargs` and `.fwd` have no
    `infer` arm, so they answer `none` here and the consecution cases recover *not
    a splat* from the argument's own accepting judgement. -/
def inferArgs (D : Decls) (Γ : Env) (es : List Expr) (top : Bool := false)
    (ctx : FrameCtx := { cls := "Object" }) : Option (List Ty × Env × Decls) :=
  match es with
  | [] => some ([], Γ, D)
  | e :: rest =>
    match infer D Γ e top ctx with
    | some (τ, Γ₁, D₁) =>
      match inferArgs D₁ Γ₁ rest top ctx with
      | some (τs, Γ₂, D₂) => some (τ :: τs, Γ₂, D₂)
      | none => none
    | none => none
termination_by sizeOf es

/-- The `if` join, factored out because `KontOk.ifK` must agree with it
    branch-for-branch. No union type in P0, so the two arms must agree on both
    the type and the environment; a missing `else` contributes `nil` and no
    environment change (`applyKont`'s fall-through, `Interp.lean:2096`). -/
def inferIf (D : Decls) (Γ : Env) (t : Expr) (els : Option Expr) (top : Bool := false)
    (ctx : FrameCtx := { cls := "Object" }) : Option (Ty × Env × Decls) :=
  match els with
  | some e =>
    match infer D Γ t top ctx, infer D Γ e top ctx with
    | some (τt, Γt, Dt), some (τe, Γe, De) =>
      -- **The types are *joined*, the environments are still compared** (L193).
      -- Before this rung both were equalities, and the type one is what refused a
      -- quarter of the slice's method bodies: `raise … if c`, `x&.foo`, `a || b` all
      -- desugar to an `if` whose branches have different types. `joinTy` answers only
      -- where it can justify an answer, so this stays a *refusal* wherever the two
      -- sides are unrelated — what changed is that `nil` on one side is no longer one
      -- of those places.
      --
      -- The environment join is a **separate** rung and deliberately not here:
      -- `namespace = nil if c` binds a local in one branch only, and merging that
      -- needs `Env` to become a lattice, which `KontOk`'s environment *equality*
      -- (read by every `frameK`) does not yet tolerate.
      -- `Option.map` rather than a `match` on purpose (L193b): the factoring proof
      -- has to rewrite `joinTy`'s *result* under this binder, and a rewrite inside a
      -- `match` scrutinee is exactly the shape `rw` refuses ("motive is not type
      -- correct"). One combinator instead of one match, and the open side's
      -- `joinATy_subst` goes straight in.
      if Γt = Γe ∧ Dt = De then (joinTy τt τe).map (fun τj => (τj, Γt, Dt)) else none
    | _, _ => none
  | none =>
    match infer D Γ t top ctx with
    | some (τt, Γt, Dt) =>
      -- No `else` means the missing branch yields `nil`, so this is the same join
      -- against `.nilT` — and it is the shape that pays for the rung, since
      -- `raise … if c` is a one-armed `if` whose arm is not `nil`.
      if Γt = Γ ∧ Dt = D then (joinTy τt .nilT).map (fun τj => (τj, Γ, D)) else none
    | none => none
termination_by sizeOf t + sizeOf els

end

/-- The **epistemic** verdict — what the checker knows, in three values.

    `accept` is backed by `check_sound`. `reject` says *our rules refute this
    program*; the difftest direction `reject ⇒ srb rejects` is the guard on it
    (not a theorem — see the refutation-pass header). `unknown` claims nothing.

    **This is no longer what the tool reports** (D12). It is the *basis* of the
    reported decision, and it is kept in exactly this shape because "our rules
    refute this" and "the fragment escaped" are different facts, only the first
    has ever been compared against `srb`, and collapsing them would retire that
    comparison silently. `Decision`/`basisOf` below are the reported reading. -/
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
  -- `top := true`: the program body *is* the toplevel position (L155). Inert
  -- until a rule reads the flag, and the verdict diff proves it.
  match infer (declsOf p) [] p true { cls := "Object" } with
  | some _ => .accept
  | none => if illTyped (declsOf p) p then .reject else .unknown

/-! ## D12 — the decision is total, and what `reject` does and does not claim

`PLAN.md` §1 criterion 2 asks for *`accept` or `reject`, never `unknown`*, and D5
says *either verdict is a result; `unknown` is not*. Both are satisfiable today,
and the reason is the **asymmetry of the guarantee**:

* `accept` is a claim about the *program* — `check_sound` and its prelude-booted
  instances conclude that no reachable outcome is type-stuck.
* `reject` is a claim about the *checker*: **we did not certify this program.** It
  does **not** say the program type-sticks, and no theorem or difftest direction
  needs it to. A rejected program may run perfectly.

So the decision is total by construction, with soundness untouched: `accept` iff
`check p = .accept`, the same predicate every theorem is stated over
(`decision_accept_iff`). What the three-valued `Verdict` becomes is the
**basis** — *why* this is a reject — and it is retained rather than collapsed:

| basis | reading | who consumes it |
|---|---|---|
| `certified` | `check_sound` applies | the theorem |
| `refuted` | our rules positively refute the program | the `srb` comparison's pinned zero (`difftest/checker_relation.py`) |
| `uncertified` | the fragment escaped; no claim either way | the false-negative metric — the thing to minimize |

**The quality metric is therefore false negatives, not `unknown`s.** A checker
that rejects everything is total and useless, so the number that matters is how
much of the target it *certifies* — `homebrew/slice-verdict.md` is where that is
tracked, per method body, with the assertion language as the triage of each
`uncertified`.
-/

/-- D12's reported verdict: total, two-valued. -/
inductive Decision where
  | accept
  | reject
deriving DecidableEq, Repr, Inhabited

/-- Why a decision is what it is. See the table above. -/
inductive Basis where
  | certified
  | refuted
  | uncertified
deriving DecidableEq, Repr, Inhabited

/-- **The decision, and its basis.** Total: every program gets `accept` or
    `reject`. Defined *over* `check` rather than replacing it, so that no theorem
    changes and the epistemic reading stays available to the consumers that need
    it (the `srb` relation, the tier-4 declared verdicts). -/
def decisionOf (p : Expr) : Decision × Basis :=
  match check p with
  | .accept => (.accept, .certified)
  | .reject => (.reject, .refuted)
  | .unknown => (.reject, .uncertified)

/-- The bridge every soundness statement is read through: the total verdict's
    `accept` is *the same predicate* `check_sound` is stated over. Proved rather
    than asserted, because it is the one place where making the verdict total
    could have quietly weakened the theorem. -/
theorem decision_accept_iff (p : Expr) :
    (decisionOf p).1 = .accept ↔ check p = .accept := by
  unfold decisionOf
  cases h : check p <;> simp [h]

/-- …and the corresponding fact about the basis, which is what makes the table
    above a definition rather than a comment: an accepting decision is always
    `certified`, so a reader cannot see `accept` paired with anything else. -/
theorem decision_accept_certified {p : Expr} (h : (decisionOf p).1 = .accept) :
    (decisionOf p).2 = .certified := by
  unfold decisionOf at h ⊢
  cases hc : check p <;> simp [hc] at h ⊢

/-! ## Worked verdicts

Each `unknown` below is *incompleteness* — `srb` rejects and we abstain — which
the ratchet permits and the pinned zero does not count. Each `reject` agrees
with `srb` [V, 0.6.13405].
-/

/-- `1 + nil` — srb 7002. The motivating case. -/
example : check (.send (some (.int 1)) "+" [.nil] none) = .reject := by
  simp [check, infer, inferArgs, subTys, subTy, illTyped, tableRefutes, defTy, sigOf, declFor, declOf?, declsFor, baseDecls, tyClassNames, declsOf]

/-- `1 + true` — srb 7002. -/
example : check (.send (some (.int 1)) "+" [.tru] none) = .reject := by
  simp [check, infer, inferArgs, subTys, subTy, illTyped, tableRefutes, defTy, sigOf, declFor, declOf?, declsFor, baseDecls, tyClassNames, declsOf]

/-- **Rejected, and perfectly safe.** `if false then 1 + nil else 0 end` runs to
    `0`. `reject` claims our rules refute the program, *not* that it fails —
    the asymmetry of `typed-portion-safety.md` §8.1. srb rejects this too, but
    for a different reason (7006 unreachable, not 7002), which is worth
    remembering when the difftest starts comparing diagnostics [V]. -/
example :
    check (.if' .fls (.send (some (.int 1)) "+" [.nil] none) (some (.int 0)))
      = .reject := by
  simp [check, infer, inferArgs, subTys, subTy, inferIf, illTyped, tableRefutes, defTy, sigOf, declFor, declOf?, declsFor, baseDecls, tyClassNames, declsOf]

/-- `1 / 2` — srb *accepts*; `/` is absent from the table, so we abstain. This
    is the case that makes "absent ⇒ no opinion" mandatory rather than merely
    conservative: rejecting here would break `reject ⇒ srb rejects`. -/
example : check (.send (some (.int 1)) "/" [.int 2] none) = .unknown := by
  simp [check, infer, inferArgs, subTys, subTy, illTyped, tableRefutes, defTy, sigOf, declFor, declOf?, declsFor, baseDecls, tyClassNames, declsOf]

/-- `1.foo(2)` — srb 7003. We abstain: the table cannot distinguish "no such
    method" from "method we have not tabulated". Incompleteness. -/
example : check (.send (some (.int 1)) "foo" [.int 2] none) = .unknown := by
  simp [check, infer, inferArgs, subTys, subTy, illTyped, tableRefutes, defTy, sigOf, declFor, declOf?, declsFor, baseDecls, tyClassNames, declsOf]

/-- `q = 1; q + nil` — srb 7002. We abstain because `defTy` has no environment,
    so a local has no unconditional type. The obvious next widening. -/
example :
    check (.seq [ .vasgn .lvar "q" (.int 1),
                  .send (some (.var .lvar "q")) "+" [.nil] none ]) = .unknown := by
  simp [check, infer, inferArgs, subTys, subTy, inferSeq, illTyped, illTypedAny, tableRefutes, defTy,
    sigOf, declFor, declOf?, declsFor, baseDecls, tyClassNames, declsOf, envSet, envGet?]

end RubyCore.Types
