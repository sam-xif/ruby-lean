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
  -- `StrClsOk` — *the boot `String` id is a class named `"String"`* — which is
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
  -- Binary send to a builtin, explicit receiver, no block. Every other send
  -- shape — implicit self, wrong arity, a block, `vcall` — is `unknown`, which
  -- is also what keeps `.self'` out of receiver position (see `KontOk.recvK`:
  -- `evalExpr` picks the `.selfRecv` site *syntactically* for a literal `self`).
  | .send (some recv) mname [arg] none =>
    -- **The signature is read after the argument, not before** (F1b.8). The three
    -- tests are independent — each failure is `none` — so the order is free, and
    -- what fixes it is the *continuation*: an `argsK` exists once both receiver and
    -- argument have run, so the table it is indexed by is the one the argument
    -- left, and `KontOk.argsK`'s signature premise has to be readable there.
    -- Reading `sigOf` at the earlier table would make the kont carry a fact about
    -- a table nothing in the machine is at.
    -- **A literal `self` receiver is excluded** (F1b.11), and it is a fact about
    -- the machine rather than about types: `evalExpr` picks the send *site*
    -- syntactically, so `self.foo` is a `.selfRecv` send and takes a different path
    -- through `visError?` than `.explicit`. `KontOk.recvK` is stated at
    -- `.explicit`, and `site_explicit` — which used to hold because `infer` refused
    -- `self` outright — is what this guard keeps true. The zero-argument case is
    -- covered by `vcall`, which is the same dispatch without the receiver.
    if isSelf recv then none else
    match infer D Γ recv top ctx with
    | some (τr, Γ₁, D₁) =>
      match infer D₁ Γ₁ arg top ctx with
      | some (τa, Γ₂, D₂) =>
        match sigOf D₂ τr mname with
        | some ([τp], τret) => if τa = τp then some (τret, Γ₂, D₂) else none
        | _ => none
      | none => none
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
    if isSelf recv then none else
    match infer D Γ recv top ctx with
    | some (τr, Γ₁, D₁) =>
      match sigOf D₁ τr mname with
      | some ([], τret) => some (τret, Γ₁, D₁)
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
      match infer D [] body false { ctx with selfCls := some ctx.cls } with
      | some (τb, _, Db) =>
        if Db = D then
          if top = false ∧ name ≠ "initialize" ∧ reopenableClasses.contains ctx.cls ∧
              defFree body = true then
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
      if τt = τe ∧ Γt = Γe ∧ Dt = De then some (τt, Γt, Dt) else none
    | _, _ => none
  | none =>
    match infer D Γ t top ctx with
    | some (τt, Γt, Dt) =>
      if τt = Ty.nilT ∧ Γt = Γ ∧ Dt = D then some (.nilT, Γ, D) else none
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
  -- `top := true`: the program body *is* the toplevel position (L155). Inert
  -- until a rule reads the flag, and the verdict diff proves it.
  match infer (declsOf p) [] p true { cls := "Object" } with
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
