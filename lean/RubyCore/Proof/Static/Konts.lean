import RubyCore.Proof.Static.Decls

/-!
# P0 static soundness, part 2 — typing the machine

§2 of `Proof/StaticSoundness.lean` before the L136 split: `KontOk` (one
constructor per admitted continuation, and the *absence* of the other 39 is what
collapses preservation's case analysis), `CtlOk`, the two heap conditions
`TableOk`/`NoHook`, the invariant `Inv` itself, and the inversion lemmas the send
and `def` cases need.
-/

namespace RubyCore
namespace Proof
namespace Static

open Interp
open RubyCore.Types

set_option maxRecDepth 100000

/-! ## 2. Typing the machine

`KontOk h Γ τ k` reads: *the in-flight value has type `τ`, the environment is
`Γ`, and `k` is a well-typed continuation.* There is one constructor per
admitted `Kont` — five out of the machine's 48 (`Machine.lean:140`) — and the
absence of the other 43 is what makes preservation's case analysis collapse.
-/

/-- A `while` whose condition and body are both **environment-stable** at `Γ`.
    The loop re-enters the condition with whatever the body leaves, so without
    stability there is no single `Γ` to index the two loop konts by. -/
def LoopOk (D : Decls) (Γ : Env) (c body : Expr) (top : Bool := false)
    (ctx : FrameCtx := { cls := "Object" }) : Prop :=
  (∃ τc, infer D Γ c top ctx = some (τc, Γ, D)) ∧
    (∃ τb, infer D Γ body top ctx = some (τb, Γ, D))

/-- `KontOk h Γs τ k` reads: *in heap `h`, the in-flight value has type `τ`, the
    environment **stack** is `Γs` (innermost first), and `k` is a well-typed
    continuation.*

    The heap index arrived with L137 and is carried for one constructor only —
    `argsK`, which stores an already-evaluated **receiver** and therefore a
    `ValueTy` fact about a value the heap describes. It is the reason a
    heap-writing step now owes `KontOk.heap_congr`.

    The stack replaces P0's single environment because a method activation has
    its own locals: `frameK` — the kont `enterUserMethod` pushes
    (`Interp.lean:573`) and `applyKont` pops (`Interp.lean:2206`) — is exactly
    the marker at which one environment goes out of scope. Every other
    constructor operates on the head and passes the tail through untouched.

    **The declarations are an *index*, not a parameter** (F1b.8). A continuation
    is resumed at whatever table is in force when control comes back to it, and
    that is not the table the continuation was created under: a `seqK` holding
    `def foo; …; end; foo` runs its tail with a row the head installed. So the
    three constructors that store *unevaluated program* — `seqCons`, `ifK`, and
    the argument half of `recvK` — relate an incoming table to an outgoing one,
    and `frameK` relates the callee's to the caller's resumption. Every other
    constructor passes one table through, because no step between it and its
    premise can install a method.

    Today no rule grows the table, so every one of those pairs is instantiated
    equal and the index is inert. It is here now because widening `infer` later
    without it would mean re-indexing the inductive with eleven consecution cases
    already written against it.

    **The environment stack carries the definee's class name beside the
    environment** (F1b.9). A declaration row is keyed on a class name, so `infer`
    needs one, and the only thing that says which class is the frame's `defmod` —
    which changes at exactly the constructor the environment changes at. Pairing
    it into the stack rather than adding a parallel index is what makes `frameK`
    restore *both* at once: the caller's context is the second component of the
    stack, not a fact the constructor has to be handed. `FramesOk` and
    `StackCtx` read the two projections and are otherwise untouched. -/
inductive KontOk : Decls → Heap → List (FrameCtx × Env) → Ty → List Kont → Prop where
  /-- Empty stack: the in-flight value is the program's result. -/
  | nil {D h Γs τ} :
      -- **L198: an empty continuation means no enclosing method.** There is nowhere
      -- for a `return` to land, so the current activation cannot declare a return
      -- type — and stating it here is what lets `KontOk.retOk` be an induction with no
      -- side conditions instead of a carried invariant conjunct. Established by one
      -- `simp` at both `initiation`s: the toplevel context has `ret := none`.
      (∀ cΓ Γs', Γs = cΓ :: Γs' → cΓ.1.ret = none) →
      -- **L227: and no enclosing loop either**, for the same reason at the other jump
      -- channel: `unwind` at `[]` answers `.stuck "jump escaped the program"` for a
      -- `.nxtJ`, so `KontOk.nxtOk` has to be able to *refute* the empty-continuation
      -- position, and `ret = none` says nothing about loops. Established by the same
      -- `simp` at both `initiation`s — the toplevel context has `inLoop := none`.
      (∀ cΓ Γs', Γs = cΓ :: Γs' → cΓ.1.inLoop = none) →
      KontOk D h Γs τ []
  /-- `seqK []` yields the in-flight value unchanged (`Interp.lean:1957`). -/
  | seqNil {D h c Γ Γs τ τw k Γk} :
      subTy τ τw = true → KontOk D h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γ := by first | exact SubEnv.refl _ | assumption) →
      KontOk D h ((c, Γ) :: Γs) τ (.seqK [] :: k)
  /-- `seqK (e :: es)` discards the in-flight value and runs the rest.

      **`Γs.isEmpty` is the toplevel mode** (L155), and this is the only
      constructor that has to name it: `seqK` is the one kont that stores
      *unevaluated statements*, so it is the one whose contents may be a `class`.
      The mode is read off the environment stack rather than carried as an index
      because `frameK` — the constructor at which an activation's environment goes
      out of scope — is already exactly where the definee changes. -/
  | seqCons {D D' h c Γ Γs τ e es τ' τw Γ' k Γk} :
      inferSeq D Γ (e :: es) Γs.isEmpty c = some (τ', Γ', D') →
      subTy τ' τw = true →
      KontOk D' h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γ' := by first | exact SubEnv.refl _ | assumption) →
      KontOk D h ((c, Γ) :: Γs) τ (.seqK (e :: es) :: k)
  /-- Assignment binds `x` at the in-flight type and re-yields the value. -/
  | asgn {D h c Γ Γs τ τw x k Γk} :
      -- **L252: the activation is not a block.** `applyKont`'s delivery runs
      -- `Machine.setLocal`, which walks the `captured` chain and may write an
      -- **enclosing** frame; `StackCtx`'s empty-chain clause is guarded on the same flag
      -- and is what the delivery reads it through. Free at the one construction site,
      -- because `infer`'s `.vasgn .lvar` arm now refuses inside a block, so the eval
      -- case's split hands the fact over.
      c.inBlock = false → subTy τ τw = true →
      KontOk D h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk (envSet Γ x τ) := by first | exact SubEnv.refl _ | assumption) →
      KontOk D h ((c, Γ) :: Γs) τ (.asgnK .lvar x :: k)
  /-- **`@x = e`, with the value in flight** (L191). One premise beyond the tail, and
      it is the *frame context's* rather than the heap's: `selfCls` being inhabited is
      what the consecution case turns — through `StackCtx` and `plainRecv` — into
      "the write does not raise `FrozenError`". No binding moves, so the tail is
      typed in the same environment. -/
  | asgnIvar {D h c Γ Γs τ τw x k Γk} :
      c.selfCls.isSome = true → subTy τ τw = true →
      -- **L196: the write conforms to whatever the table declares.** Carried on the
      -- continuation rather than re-derived at the delivery, because the delivery is
      -- where `DeclsOk`'s ivar half has to be re-established and this is the only
      -- fact that can do it.
      (∀ cn σ, c.selfCls = some cn → ivarTy? D cn x = some σ → subTy τ σ = true) →
      KontOk D h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk (Γ) := by first | exact SubEnv.refl _ | assumption) →
      KontOk D h ((c, Γ) :: Γs) τ (.asgnK .ivar x :: k)
  /-- **`$x = e`, with the value in flight** (L228) — `asgnIvar`'s shape at the sixth
      table, and simpler in exactly one way: a global has no receiver, so there is no
      `selfCls` premise and no quantification over the class. The declared type is carried
      here rather than re-read at the delivery for `asgnIvar`'s reason: the delivery is
      where `GlobalsOk` has to be re-established, and this is the fact that does it. -/
  | asgnGvar {D h c Γ Γs τ τw x σ k Γk} :
      plainGlobal x = true →
      globalTy? D x = some σ →
      subTy τ σ = true →
      subTy τ τw = true →
      KontOk D h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk (Γ) := by first | exact SubEnv.refl _ | assumption) →
      KontOk D h ((c, Γ) :: Γs) τ (.asgnK .gvar x :: k)
  /-- The in-flight value is the condition; either branch may run next, so the
      join must be the one `inferIf` computed. -/
  | ifK {D D' h c Γ Γs τ t els τ' τw Γ' k Γk} :
      inferIf D Γ t els Γs.isEmpty c = some (τ', Γ', D') →
      subTy τ' τw = true →
      KontOk D' h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk (Γ') := by first | exact SubEnv.refl _ | assumption) →
      KontOk D h ((c, Γ) :: Γs) τ (.ifK t els :: k)
  -- **L222: the loop konts clear the flag on the way down.** Above them the context is the
  -- one `infer`'s `.while'` arm types the loop at; below them the enclosing one. That plus
  -- `frameK`'s new premise makes *"the flag is on ⇒ a loop kont sits above the `frameK`"* a
  -- property of the derivation — what a `next` rule needs to *refute* the frameK position,
  -- where `unwind` answers `.unsupported`.
  | whileCond {D h ctx Γ Γs τ τw c body k Γk} :
      LoopOk D Γ c body Γs.isEmpty { ctx with inLoop := some Γ } → subTy .nilT τw = true →
      KontOk D h ((ctx, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk (Γ) := by first | exact SubEnv.refl _ | assumption) →
      KontOk D h (({ ctx with inLoop := some Γ }, Γ) :: Γs) τ (.whileCondK c body :: k)
  | whileBody {D h ctx Γ Γs τ τw c body k Γk} :
      LoopOk D Γ c body Γs.isEmpty { ctx with inLoop := some Γ } → subTy .nilT τw = true →
      KontOk D h ((ctx, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk (Γ) := by first | exact SubEnv.refl _ | assumption) →
      KontOk D h (({ ctx with inLoop := some Γ }, Γ) :: Γs) τ (.whileBodyK c body :: k)
  /-- The in-flight value is the **receiver** of a binary builtin send; the
      argument expression runs next.

      **The site is a parameter** (L172), as `argsK`'s is (L171). `evalExpr` picks
      it syntactically — `.selfRecv` for a literal `self` receiver and `.explicit`
      for everything else — and the difference is *permissive*: `visError?` raises
      only at `.explicit`, while `ResolvesAt`/`ResolvesUser` demand `.pub`
      regardless. So a public method dispatches identically at both, the dispatch
      lemmas have been site-polymorphic since L164, and `infer`'s `isSelf` guard —
      which existed only to keep this constructor's `.explicit` true — is gone. -/
  | recvK {D D₂ h c Γ Γs τ mname arg args τs ps τret τw Γ₂ k Γk} {site : SendSite} :
      inferArgs D Γ (arg :: args) Γs.isEmpty c = some (τs, Γ₂, D₂) →
      sigOf D₂ τ mname = some (ps, τret) →
      subTys τs ps = true →
      subTy τret τw = true →
      KontOk D₂ h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk (Γ₂) := by first | exact SubEnv.refl _ | assumption) →
      KontOk D h ((c, Γ) :: Γs) τ (.recvK mname (arg :: args) .none site :: k)
  /-- **A zero-argument send** (L152), and it is a separate constructor rather than
      `recvK` with an empty list because the two describe *different numbers of
      steps*. With an argument, `applyKont` pushes an `argsK` and the dispatch is a
      step away; with none, `startArgs … [] []` is `finishSend`, so the send completes
      **in this step** and the continuation `k` must already be typed at the return
      type. There is no `argsK` in the chain at all, and therefore no `ValueTy` stored
      in the kont — which is why this constructor, unlike `argsK`, does not read the
      heap. -/
  | recvK0 {D h c Γ Γs τ mname τret τw k Γk} {site : SendSite} :
      sigOf D τ mname = some ([], τret) →
      subTy τret τw = true →
      KontOk D h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk (Γ) := by first | exact SubEnv.refl _ | assumption) →
      KontOk D h ((c, Γ) :: Γs) τ (.recvK mname [] .none site :: k)
  /-- The in-flight value is the **argument**; the receiver is already a value
      carried by the kont, so its type is pinned by `ValueTy` rather than by
      `infer`.

      **The site is a parameter** (L171). `startArgs` stores whatever site it was
      called at, and nothing between here and the dispatch reads it: `visError?`
      matches `.explicit` alone and both dispatch lemmas have been quantified over
      the site since L164. So the *written receiverless* unary send — which pushes
      this kont at `.implicit`, with the frame's `self` as the stored receiver —
      is the same constructor rather than a second one. -/
  | argsK {D D' h c Γ Γs τ mname recv τr psacc τp τrest psrest τret τw acc rest Γ' k Γk}
      {site : SendSite} :
      ValueTy h recv τr →
      ValuesTy h acc psacc →
      subTy τ τp = true →
      inferArgs D Γ rest Γs.isEmpty c = some (τrest, Γ', D') →
      subTys τrest psrest = true →
      sigOf D' τr mname = some (psacc ++ τp :: psrest, τret) →
      subTy τret τw = true →
      KontOk D' h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk (Γ') := by first | exact SubEnv.refl _ | assumption) →
      KontOk D h ((c, Γ) :: Γs) τ (.argsK recv site mname acc rest .none :: k)
  /-- **A `super` argument in flight** (L212), and it is `argsK` with the receiver
      taken out. `doSuper` re-dispatches the *frame's* method on the *frame's* `self`,
      so there is no stored receiver and no `sigOf`: the signature comes out of the
      `supers` table at the pair `(c.cls, mname)`, which is why the context's own
      `meth` is a premise rather than the kont's payload.

      `blk` is stored by the machine and mentioned nowhere here, for `arrK`'s reason at
      a different field: the builtin arm of `SuperOk` ignores it (`Builtins.run` takes
      no block), and the user arm — which would not — is not in the fragment.

      The two `super`-specific premises are the guards the eval rule checks and the
      dispatch lemma spends: `c.meth = some mname` ties the kont's signature to the
      activation `doSuper` will read, and `mname ≠ ""` refuses `doSuper`'s
      *"super outside a method"* answer, which is `.unsupported` and therefore stuck. -/
  | superArgsK {D D' h c Γ Γs τ mname psacc τp τrest psrest τret τw acc rest Γ' k blk dd Γk} :
      ValuesTy h acc psacc →
      subTy τ τp = true →
      inferArgs D Γ rest Γs.isEmpty c = some (τrest, Γ', D') →
      subTys τrest psrest = true →
      c.meth = some mname →
      mname ≠ "" →
      superDecl? D' c.cls mname = some dd →
      dd.params = psacc ++ τp :: psrest →
      dd.ret = τret →
      subTy τret τw = true →
      KontOk D' h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk (Γ') := by first | exact SubEnv.refl _ | assumption) →
      KontOk D h ((c, Γ) :: Γs) τ (.superArgK acc rest blk :: k)
  /-- **An array literal's element** (L174). The in-flight value is one element;
      the remaining elements run next, and when they are gone `continueArray`
      allocates — so the continuation `k` is typed at `.cls "Array"` and the
      accumulated values are **not mentioned at all**.

      That absence is the rule's whole economy: `Ty` has no `Array τ`, so the
      element types are erased and this constructor owes only the *threading* the
      unevaluated tail needs. It is `seqCons`'s shape — `inferSeq` over the stored
      program, an incoming table related to an outgoing one — with a fixed answer
      type instead of the sequence's last. -/
  | arrK {D D' h c Γ Γs τ τ' τw acc rest Γ' k Γk} :
      -- **L230: `inferElems`, not `inferSeq`.** The remaining elements are typed by the
      -- traversal that admits a splat, which is the whole of the rung on this side.
      inferElems D Γ rest Γs.isEmpty c = some (τ', Γ', D') →
      subTy (.cls "Array") τw = true →
      KontOk D' h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk (Γ') := by first | exact SubEnv.refl _ | assumption) →
      KontOk D h ((c, Γ) :: Γs) τ (.arrK acc rest :: k)
  /-- **A splatted array element, with the operand in flight** (L230) — `arrK`'s twin at
      `continueArray`'s splat arm, and it carries exactly one premise more: the in-flight
      value's type is `Array`.

      That premise is what makes the step **total**. `applyKont`'s `arrSplatK` arm calls
      `spreadA`, which answers `.error` — hence `.unsupported`, which `StepOk` refuses —
      for every payload but `.arr`, `.mdata` and a `Range`; and the bridge from "its class
      is `Array`" to "its payload is an `.arr`" is `plainRecv`'s sixth clause (L230),
      landed as a clause of the judgement rather than as a sixth heap conjunct of `Inv`. -/
  | arrSplatK {D D' h c Γ Γs τ τ' τw acc rest Γ' k Γk} :
      subTy τ (.cls "Array") = true →
      inferElems D Γ rest Γs.isEmpty c = some (τ', Γ', D') →
      subTy (.cls "Array") τw = true →
      KontOk D' h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk (Γ') := by first | exact SubEnv.refl _ | assumption) →
      KontOk D h ((c, Γ) :: Γs) τ (.arrSplatK acc rest :: k)
  /-- **Method return.** The in-flight value is the body's value; popping the
      activation (`Interp.lean:2206`) discards the callee's environment and
      resumes the caller's.

      Note the **two-deep** env stack `Γ :: Γ' :: Γs`. A one-deep version would
      be provable-looking and wrong: `KontOk.nil` accepts *any* stack including
      `[]`, so `KontOk h (Γ :: []) τ (frameK :: [])` would be derivable, and
      popping it leaves a machine with no current environment for `CtlOk` to use.
      Requiring a caller environment to exist is what makes the pop total.

      **One table, and this is the constructor where that is a restriction**
      (F1b.8). The callee's body runs under the same declarations the caller
      resumes at, which is why both the class-body rule and `UserConforms` carry
      a *stability* side condition saying the body leaves the table alone. Two
      tables would be the honest shape — a class body's `def`s are exactly the
      rows meant to escape — but the pop then owes `DeclsOk` at the caller's
      table from `DeclsOk` at the callee's, and `DeclsOk` is neither monotone nor
      antitone in the table (`UserConforms` reads it through `infer`). That is
      the next rung's problem, and it is loud rather than latent because the
      stability conditions refuse the programs it would admit. -/
  | frameK {D h cΓ cΓ' Γs τ fid k} :
      -- **L198: the callee's declared return type *is* the type the caller's
      -- continuation expects** — when it declares one at all, which a class-body
      -- frame does not. That single agreement is the whole reason `RetOk` can be
      -- *derived* from a `KontOk` derivation (`KontOk.retOk`) rather than carried as a
      -- separate conjunct of `Inv` and re-established at forty push sites.
      -- `subTy` rather than equality, because `CtlOk`'s eval clause already allows the
      -- continuation to sit at a *wider* type than the expression's (L193): the
      -- callee's declared return is below the index, not equal to it.
      (∀ σ, cΓ.1.ret = some σ → subTy σ τ = true) →
      -- **L222: the callee is not inside a loop** — free at every push, and the other half
      -- of the guarantee above.
      cΓ.1.inLoop = none →
      KontOk D h (cΓ' :: Γs) τ k → KontOk D h (cΓ :: cΓ' :: Γs) τ (.frameK fid :: k)
  /-- **A block body's value, delivered** (L245) — the block frame pops and the value
      goes on to whatever pushed the block call (an `iterK`, for a native iterator).

      `frameK`'s shape at a different constructor: `applyKont`'s two arms are the same
      `stack.tail` + `.value v`, and only the label's kind differs. What is *not*
      `frameK`'s are the two context premises, and they are the reason the case analyses
      over `KontOk` close rather than a tidiness:

      * `ret = none` — a `return` inside a block targets the **home method**
        (`returnTarget` walks past a block frame), not this activation, so the block's
        context opens no return channel and `KontOk.retOk`'s new case is `absurd`;
      * `inLoop = none` — a `next` inside a block ends the *block invocation*
        (`blkFrameK`'s own `.nxtJ` arm), not the enclosing loop, so the same for
        `KontOk.nxtOk`.

      Both are what `infer`'s block rule will supply, and both are §10's "first cut"
      stated on the invariant side: a block body containing `return` or `next` is out of
      the fragment, and this is where that shows up as a *derivation* that does not
      exist rather than as a rule that refuses. -/
  | blkFrameK {D h cΓ cΓ' Γs τ τ' fid lam brk cl args k} :
      cΓ.1.ret = none → cΓ.1.inLoop = none → subTy τ τ' = true →
      KontOk D h (cΓ' :: Γs) τ' k →
      KontOk D h (cΓ :: cΓ' :: Γs) τ (.blkFrameK fid lam brk cl args :: k)
  /-- **`return e`, with the value in flight** (L200). Three premises, each spent in a
      different place: `c.ret = some σ` is what the target is read through, `subTy τ σ`
      is the rule's own conformance check, and the tail's `KontOk` is what
      `KontOk.retOk` turns into the `RetOk` the unwinding consumes.

      It carries a **`KontOk`** and not a `RetOk`, and that is not an accident: `RetOk`
      is defined *over* `KontOk` derivations, so a `RetOk` premise here would make the
      two mutually inductive. Deriving it at the delivery costs one lemma application. -/
  | retValK {D h c Γ Γs τ τ' σ k Γk} :
      c.ret = some σ → subTy τ σ = true →
      KontOk D h ((c, Γk) :: Γs) τ' k →
      (hsu : SubEnv Γk (Γ) := by first | exact SubEnv.refl _ | assumption) →
      KontOk D h ((c, Γ) :: Γs) τ (.jumpValK .retK :: k)
  /-- **`C::n`, with the namespace in flight** (L205).

      The in-flight value is the *base*, and the premise that matters is that its type
      is a **class object**: `.clsOf cname` is the only `Ty` a namespace can have, and
      the name is the table key. `subTy τ (.clsOf cname)` rather than `τ = .clsOf cname`
      for L193's reason — every constructor's index is decoupled from what it stores, so
      a value delivered at a weakened type still lands.

      Nothing about the container's *heap* is carried here: that is `ScopedConstOk`,
      which `DeclsOk` supplies at the delivery. The difference from `asgnIvar` — which
      does carry a conformance premise — is that this rule reads the table where that
      one writes the heap, so the delivery re-establishes nothing. -/
  | cpathK {D h c Γ Γs τ τw cname n σ k Γk} :
      subTy τ (.clsOf cname) = true → scopedConstTy? D cname n = some σ →
      subTy σ τw = true →
      KontOk D h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk (Γ) := by first | exact SubEnv.refl _ | assumption) →
      KontOk D h ((c, Γ) :: Γs) τ (.cpathK n :: k)
  /-- **The receiver of a *block* send, in flight** (L257) — the `recvK` a literal block
      rides on, and the constructor `infer`'s block-send rule registers.

      Its premises are `KontOk.iterK`'s (L253) read one step earlier: the block
      environment is built from the **send site's** environment rather than from the
      iterator activation's, and the row is still a row rather than the loop's residue.
      What the delivery adds is everything `DeclsOk` supplies — the miss, the payload
      shape and the answer's type — which is why none of that is here. -/
  | recvKBlk {D : Decls} {h : Heap} {c : FrameCtx} {Γ Γk : Env}
      {Γs : List (FrameCtx × Env)} {τr τw τb τret σp βret : Ty} {Γb' : Env}
      {mname x : String} {ps : List Param} {ls : List String} {body : Expr}
      {k : List Kont} {site : SendSite} :
      blockSend? D τr mname ps ls = some (x, σp, βret, τret) →
      infer D ((x, σp) :: anyEnv Γ) body false (blockCtx c) = some (τb, Γb', D) →
      SubEnv ((x, σp) :: anyEnv Γ) Γb' →
      subTy τb βret = true →
      subTy τret τw = true →
      -- L257: the send site is not itself inside a block, so the frame the closure
      -- captures is self-contained — `ShallowChain`'s second conjunct at the fresh
      -- block frame, and the reason a nested block is out of the fragment.
      c.inBlock = false →
      KontOk D h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γ := by first | exact SubEnv.refl _ | assumption) →
      KontOk D h ((c, Γ) :: Γs) τr (.recvK mname [] (.lit ps ls body) site :: k)
  /-- **A native iterator between two block calls** (L253) — the loop marker, and the
      one constructor that has to carry *everything the next call needs*, because
      `iterStep` either calls the block again (a fresh block frame **and** a fresh
      `iterK`) or delivers the iterator's own answer.

      The conclusion sits at the **iterator activation's** entry: the block frame has
      already popped (`blkFrameK`'s delivery is `stack.tail`), so the current frame is
      the one `startIter` pushed.

      What each group of premises is for:

      * **the closure's shape** — `[.req x]`, no block-locals, not a lambda — is exactly
        `callClosure_req1`'s hypothesis set (L244), and all three are syntactic, so
        `infer`'s rule can check them;
      * **`Γb = (x, σp) :: outer` with every `outer` entry `.any`** is the block
        environment, and the `.any` is doing real work: `FrameConforms` at the fresh
        block frame then owes `ValueTy h _ .any` at every enclosing name, which holds for
        every value (L232), so the constructor needs to say **nothing** about the frame
        the closure captured. That is what `ClosuresOk` carries instead (L248/L251);
      * **the block context's five `none`/`true` fields** discharge four of `StackCtx`'s
        seven clauses at the block frame outright (L250) and are what `retOk`/`nxtOk`
        close their new cases with;
      * **`∀ a ∈ rest, ValuesTy h a bs.params`** is the loop's remaining work, heap-indexed
        so it rides `heap_congr'` like every other `ValueTy` premise;
      * **`retVal`'s type** is the iterator's answer, delivered to the `frameK` below once
        `rest` runs out.

      `kind = .ignore` restricts this to the `each`-shaped iterators. `.collect` accumulates
      the block's values into a fresh array and would need the element claim `Ty` cannot
      yet write (`arrayOf`, L238); `.fold`/`.maxBy` change the block's *argument* types
      between iterations. One `IterKind` at a time, and the census says `each` is the
      one to have (L244's table). -/
  | iterK {D : Decls} {h : Heap} {cΓ : FrameCtx × Env} {Γs : List (FrameCtx × Env)}
      {τ τ' τr τbody σp : Ty} {bs : BlockSig} {cb : FrameCtx} {Γb Γb' outer : Env}
      {x : String} {cl : Closure} {brk : FrameId} {rest : List (List Value)}
      {acc : List Value} {retVal cur : Value} {k : List Kont} :
      cl.params = [.req x] → cl.locals = [] → cl.lam = false →
      bs.params = [σp] → Γb = (x, σp) :: outer → (∀ e ∈ outer, e.2 = Ty.any) →
      cb.ret = none → cb.inLoop = none → cb.selfCls = none → cb.meth = none →
      cb.inBlock = true →
      infer D Γb cl.body false cb = some (τbody, Γb', D) →
      SubEnv Γb Γb' →
      subTy τbody bs.ret = true →
      (∀ a ∈ rest, ValuesTy h a bs.params) →
      subTy τ bs.ret = true →
      ValueTy h retVal τr → subTy τr τ' = true →
      cΓ.1.ret = none → cΓ.1.inLoop = none →
      KontOk D h (cΓ :: Γs) τ' k →
      KontOk D h (cΓ :: Γs) τ (.iterK cl brk rest .ignore acc retVal cur :: k)

/-- **The labels of the `frameK`s in the continuation, in order** (L199). One frame
    push writes both a stack entry and a `frameK`, and one pop removes both, so the
    two lists move together — this is that fact, made checkable.

    It is the *one* thing the `return` rule needed that nothing carried (L198 §What is
    still missing). `doReturn` targets `returnTarget m`, which is the frame stack's
    head; `unwind`'s `frameK fid` case compares that against the **kont's** label. With
    no relation between the two, a matching `frameK` cannot be produced and the
    consecution has no case to be in. -/
def frameKLabels : List Kont → List FrameId
  | [] => []
  | .frameK fid :: k => fid :: frameKLabels k
  | _ :: k => frameKLabels k

/-- **Every kont that pops a frame** (L245) — `frameK` *and* `blkFrameK` — and it is
    this, not `frameKLabels`, that `Inv` states the stack correspondence over.

    `callClosure` pushes a block activation with a **`blkFrameK`**, not a `frameK`
    (`Interp/Kont.lean`: both deliveries are `stack.tail` + `.value v`, and only the
    label's constructor differs). So the moment a block frame exists, `frameKLabels
    m.kont = m.stack.dropLast` is **false** — the stack has an entry the labels do not.

    > **And the naive fix — teaching `frameKLabels` to count `blkFrameK` — is wrong**,
    > which is worth writing down because it is the obvious move. `frameKLabels` and
    > `firstFrameK` are the *return-target* correspondence: `doReturn` targets
    > `returnTarget m`, which walks **past** a block frame to the closure's `home`, and
    > `unwind`'s `frameK fid` case compares that against the kont's label. A
    > `firstFrameK` that answered a block frame's id would make that comparison wrong.
    > The two notions are genuinely different and both are needed.

    The bridge between them is `firstFrameK_of_retOk` below, and it goes through
    `RetOk` rather than through the labels — which is *why* the split costs nothing. -/
def framePopLabels : List Kont → List FrameId
  | [] => []
  | .frameK fid :: k => fid :: framePopLabels k
  | .blkFrameK fid _ _ _ _ :: k => fid :: framePopLabels k
  | _ :: k => framePopLabels k

/-- **The konts a `.retJ` passes straight through** (L199). Not a judgement: it is a
    read-off of `unwind` (`Interp/Kont.lean`), whose **catch-all** propagates a jump
    unchanged and whose two loop markers propagate a `.retJ` explicitly. All nine kont
    shapes the fragment stacks are in here; `frameK` is the one that is not, and it is
    the one that consumes the jump. -/
def RetTransparent : Kont → Prop
  | .seqK _ => True
  | .asgnK _ _ => True
  | .ifK _ _ => True
  | .whileCondK _ _ => True
  | .whileBodyK _ _ => True
  | .recvK .. => True
  | .argsK .. => True
  -- L212: `unwind`'s catch-all again — a pending `super` argument has no opinion
  -- about a jump.
  | .superArgK .. => True
  | .arrK .. => True
  -- L230: and the splat arm of the same literal — `unwind`'s catch-all a further time.
  | .arrSplatK .. => True
  | .jumpValK _ => True
  -- L205: `unwind`'s catch-all, like the nine above — a `.cpathK` on the stack has no
  -- opinion about a jump, so a `.retJ` passes straight through it.
  | .cpathK _ => True
  -- **L253: the native iterator's loop marker.** `unwind` has *no arm* for `.iterK` — it
  -- falls to the catch-all, which passes the jump on with the kont popped — so it is
  -- transparent for the same one line of the interpreter the ten above it are. Note the
  -- asymmetry with `blkFrameK`, which is right there beside it in the continuation and is
  -- **not** transparent: the block frame consumes a `next` and a lambda's `break`.
  | .iterK .. => True
  | _ => False

/-- The label of the innermost activation's `frameK`. With L199's clause this is the
    frame stack's head, which is what `doReturn` targets. -/
def firstFrameK : List Kont → Option FrameId
  | [] => none
  | .frameK fid :: _ => some fid
  | _ :: k => firstFrameK k

/-- **A transparent kont pops nothing** (L245) — `RetTransparent`'s list and
    `framePopLabels`' two arms are disjoint by inspection, which is the fact the bridge
    below runs on. -/
@[simp] theorem framePopLabels_transparent {κ : Kont} {k : List Kont} (h : RetTransparent κ) :
    framePopLabels (κ :: k) = framePopLabels k := by
  cases κ <;> simp_all [RetTransparent, framePopLabels]

/-- The first label of `frameKLabels` *is* `firstFrameK` — the bridge between L199's
    list-shaped clause and the single id `unwind` compares against.

    **Superseded at L245 and kept**, with the withdrawal visible rather than deleted:
    `Inv`'s clause is now over `framePopLabels`, so this lemma's hypothesis is no longer
    something the invariant supplies, and both of its callers moved to
    `firstFrameK_of_retOk`. It remains *true*, and it remains the statement to reach for
    if a future clause is ever phrased over `frameKLabels` again. -/
theorem firstFrameK_of_labels : ∀ (k : List Kont) (fid : FrameId) (rest : List FrameId),
    frameKLabels k = fid :: rest → firstFrameK k = some fid := by
  intro k
  induction k with
  | nil => intro fid rest h; simp [frameKLabels] at h
  | cons κ k ih =>
    intro fid rest h
    cases κ with
    | frameK f =>
      simp only [frameKLabels, List.cons.injEq] at h
      simp [firstFrameK, h.1]
    | _ => exact (by simpa [firstFrameK] using ih fid rest (by simpa [frameKLabels] using h))

/-- **A `.retJ` in flight is well-typed for where it will land** (L200): every kont
    above the innermost `frameK` is transparent to it, and that `frameK` resumes a
    caller whose continuation accepts the declared return type.

    The table is **fixed** across `skip`, which is what makes the popped machine's
    `Inv` usable: `DeclsOk` is neither monotone nor antitone in the table, so arriving
    at the `frameK` with a *different* table would leave nothing to build `Inv` from.
    `infer_table_ret` is what pays for it, and L200's `def`-row guard is what makes
    that lemma true. -/
inductive RetOk : Decls → Heap → List (FrameCtx × Env) → Ty → List Kont → Prop where
  | here {D h Γs σ τ fid k} :
      subTy σ τ = true → KontOk D h Γs τ k → RetOk D h Γs σ (.frameK fid :: k)
  | skip {D h Γs σ κ k} :
      RetTransparent κ → RetOk D h Γs σ k → RetOk D h Γs σ (κ :: k)

/-- **`RetOk`, derived** (L200) — the lemma L198's two `KontOk` premises and L200's
    `def`-row guard exist for.

    Recursion on the *kont list* rather than on the derivation, because the derivation's
    shape is determined by the list's head and `frameK`'s premise sits at a shorter
    environment stack. Two hypotheses, each spent once: `KontOk.nil`'s `ret = none`
    refutes the empty continuation, and `Γs ≠ []` makes `infer_table_ret` applicable —
    every constructor's `infer` equation is at `top = Γs.isEmpty`, and the lemma needs
    `top = false`. `StackCtx`'s L200 clause is where that non-emptiness comes from. -/
theorem KontOk.retOk : ∀ {k : List Kont} {D : Decls} {h : Heap} {c : FrameCtx} {Γ : Env}
    {Γs : List (FrameCtx × Env)} {τ : Ty}, KontOk D h ((c, Γ) :: Γs) τ k →
    Γs ≠ [] → ∀ σ, c.ret = some σ → RetOk D h Γs σ k
  | [], _, _, c, Γ, Γs, _, hk, _, σ, hσ => by
      cases hk with
      | nil hr hl => exact absurd (hr (c, Γ) Γs rfl) (by rw [hσ]; simp)
  | κ :: k, D, h, c, Γ, Γs, τ, hk, hne, σ, hσ => by
      have htop : Γs.isEmpty = false := by simpa using hne
      cases hk with
      | seqNil hw hk' _ => exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      | seqCons hs hw hk' _ =>
          have hq : _ = D := inferSeq_table_ret (ctx := c) (by rw [hσ]; simp) htop hs
          subst hq
          exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      | asgn hib hw hk' _ => exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      | asgnIvar hsc hw hcf hk' _ => exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      | asgnGvar hpg hgt hcf hw hk' _ =>
          exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      | ifK hi hw hk' _ =>
          have hq : _ = D := inferIf_table_ret (ctx := c) (by rw [hσ]; simp) htop hi
          subst hq
          exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      | whileCond hl hw hk' _ => exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      | whileBody hl hw hk' _ => exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      | recvK ha hsg hsub hw hk' _ =>
          have hq : _ = D := inferArgs_table_ret (ctx := c) (by rw [hσ]; simp) htop ha
          subst hq
          exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      | recvK0 hsg hw hk' _ => exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      | argsK hv hva hst hia hsr hsg hw hk' _ =>
          have hq : _ = D := inferArgs_table_ret (ctx := c) (by rw [hσ]; simp) htop hia
          subst hq
          exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      | superArgsK hva hst hia hsr hmt hmn hrow hps hrt hw hk' _ =>
          have hq : _ = D := inferArgs_table_ret (ctx := c) (by rw [hσ]; simp) htop hia
          subst hq
          exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      | arrK hs hw hk' _ =>
          have hq : _ = D := inferElems_table_ret (ctx := c) (by rw [hσ]; simp) htop hs
          subst hq
          exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      | arrSplatK ha hs hw hk' _ =>
          have hq : _ = D := inferElems_table_ret (ctx := c) (by rw [hσ]; simp) htop hs
          subst hq
          exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      | retValK hr hs hk' _ => exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      -- L205: the table is untouched (the arm *reads* `scopedConsts`), so this is the
      -- plain transparent case — no `_table_ret` composition needed.
      | cpathK hb hsc hw hk' _ => exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      | frameK hrt hil hk' => exact RetOk.here (hrt σ hσ) hk'
      -- L245: the block's context opens no return channel, so this case does not exist.
      | blkFrameK hr _ _ _ => exact absurd hσ (by rw [hr]; simp)
      -- L257: `recvK` is transparent to a `.retJ`, block or no block.
      | recvKBlk _ _ _ _ _ _ hk' _ => exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      -- L253: the iterator activation declares no return type either.
      | iterK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr _ hk' =>
          exact absurd hσ (by rw [hr] at hσ ⊢; simp)

@[simp] theorem frameKLabels_transparent {κ : Kont} {k : List Kont} (h : RetTransparent κ) :
    frameKLabels (κ :: k) = frameKLabels k := by
  cases κ <;> simp_all [RetTransparent, frameKLabels]

@[simp] theorem firstFrameK_transparent {κ : Kont} {k : List Kont} (h : RetTransparent κ) :
    firstFrameK (κ :: k) = firstFrameK k := by
  cases κ <;> simp_all [RetTransparent, firstFrameK]

/-- **The bridge, and it goes through `RetOk` rather than through the labels** (L245).

    L199's clause used to *be* the bridge: `frameKLabels m.kont = m.stack.dropLast` and
    `firstFrameK_of_labels` together said *the innermost `frameK`'s label is the stack's
    head*, which is what `unwind` compares `returnTarget` against. With the clause moved
    to `framePopLabels` (L245) that reading is gone — the innermost *popping* kont may be
    a `blkFrameK`, whose frame `returnTarget` walks past.

    What replaces it is free, because `RetOk` already says the missing thing: it is built
    from `skip` at **transparent** konts and `here` at a `frameK`, and no transparent kont
    pops. So along a chain that carries a `.retJ` at all, the first popping kont *is* the
    `frameK` the jump lands at — and its label is `framePopLabels`' head. -/
theorem firstFrameK_of_retOk {D : Decls} {h : Heap} {Γs : List (FrameCtx × Env)} {σ : Ty} :
    ∀ {k : List Kont}, RetOk D h Γs σ k → ∀ {fid rest},
      framePopLabels k = fid :: rest → firstFrameK k = some fid := by
  intro k hr
  induction hr with
  | here _ _ =>
    intro fid rest hl
    simp only [framePopLabels, List.cons.injEq] at hl
    simp [firstFrameK, hl.1]
  | skip ht _ ih =>
    intro fid rest hl
    rw [framePopLabels_transparent ht] at hl
    rw [firstFrameK_transparent ht]
    exact ih hl


/-- **`unwind` propagates a `.retJ` through every transparent kont** (L200), which is
    a computation rather than an argument: `unwind`'s catch-all passes a jump on
    unchanged and the two loop markers pass a `.retJ` on explicitly. Nine cases, each a
    `simp` — this is the measurement `RetTransparent` records, cashed. -/
theorem unwind_ret_transparent {m : Machine} {κ : Kont} {k : List Kont} {v : Value}
    {t : FrameId} (hκ : RetTransparent κ) (hkm : m.kont = κ :: k) :
    Interp.unwind m (.retJ v t)
      = .next (Interp.withCtl { m with kont := k } (.jump (.retJ v t))) := by
  unfold Interp.unwind
  rw [hkm]
  cases κ <;> simp_all [RetTransparent, Interp.withCtl]

/-- **The konts a `next` passes through unchanged** (L225), and it is the *second* such
    list. The difference from `RetTransparent` is one fact about `unwind`: its `while` arm
    handles `.brkJ`/`.nxtJ`/`.redoJ` **specially** and passes everything else to the
    catch-all. So a loop kont is transparent to a `.retJ` and is a `next`'s **terminator**,
    which is the whole point of `NxtOk` below. `frameK` is in neither list. -/
def NxtTransparent : Kont → Prop
  | .seqK _ => True
  | .asgnK _ _ => True
  | .ifK _ _ => True
  | .recvK .. => True
  | .argsK .. => True
  | .superArgK .. => True
  | .arrK .. => True
  -- L230: and the splat arm of the same literal — `unwind`'s catch-all a further time.
  | .arrSplatK .. => True
  | .jumpValK _ => True
  | .cpathK _ => True
  -- L253, for `RetTransparent`'s reason at the other channel.
  | .iterK .. => True
  | _ => False

theorem unwind_nxt_transparent {m : Machine} {κ : Kont} {k : List Kont} {v : Value}
    (hκ : NxtTransparent κ) (hkm : m.kont = κ :: k) :
    Interp.unwind m (.nxtJ v)
      = .next (Interp.withCtl { m with kont := k } (.jump (.nxtJ v))) := by
  unfold Interp.unwind
  rw [hkm]
  cases κ <;> simp_all [NxtTransparent, Interp.withCtl]

@[simp] theorem frameKLabels_nxt_transparent {κ : Kont} {k : List Kont}
    (h : NxtTransparent κ) : frameKLabels (κ :: k) = frameKLabels k := by
  cases κ <;> simp_all [NxtTransparent, frameKLabels]

/-- L245's twin, at the `next` channel. -/
@[simp] theorem framePopLabels_nxt_transparent {κ : Kont} {k : List Kont}
    (h : NxtTransparent κ) : framePopLabels (κ :: k) = framePopLabels k := by
  cases κ <;> simp_all [NxtTransparent, framePopLabels]

/-- **`unwind` restarts the loop at its condition** (L225) — `unwind`'s `whileCondK`/
    `whileBodyK` arm at `.nxtJ`, which is one line of the interpreter: pop the loop kont,
    push a fresh `whileCondK`, and evaluate the condition. -/
theorem unwind_nxt_loopCond {m : Machine} {c body : Expr} {k : List Kont} {v : Value}
    (hkm : m.kont = .whileCondK c body :: k) :
    Interp.unwind m (.nxtJ v)
      = .next (Interp.withKont { m with kont := k } (.eval c) (.whileCondK c body)) := by
  unfold Interp.unwind
  rw [hkm]

theorem unwind_nxt_loopBody {m : Machine} {c body : Expr} {k : List Kont} {v : Value}
    (hkm : m.kont = .whileBodyK c body :: k) :
    Interp.unwind m (.nxtJ v)
      = .next (Interp.withKont { m with kont := k } (.eval c) (.whileCondK c body)) := by
  unfold Interp.unwind
  rw [hkm]

/-- **And the same for a `.raiseJ`** (L217) — the *same* nine cases and the same `simp`,
    because `unwind`'s catch-all does not look at the jump. Stated as a twin rather than
    by generalizing over the jump, because the `while` arms *do* look: `.brkJ`/`.nxtJ`/
    `.redoJ` are special there and a generalized lemma would need a side condition
    excluding exactly them, which is longer than the twin. -/
theorem unwind_raise_transparent {m : Machine} {κ : Kont} {k : List Kont} {exc : Value}
    (hκ : RetTransparent κ) (hkm : m.kont = κ :: k) :
    Interp.unwind m (.raiseJ exc)
      = .next (Interp.withCtl { m with kont := k } (.jump (.raiseJ exc))) := by
  unfold Interp.unwind
  rw [hkm]
  cases κ <;> simp_all [RetTransparent, Interp.withCtl]

/-- **A raise crosses a `frameK` by popping the activation** (L217) — `unwind`'s
    `frameK` arm at `.raiseJ`, which is one line of the interpreter and needs no
    agreement between the jump and the frame (contrast `.retJ`, whose arm compares the
    target against the label). -/
theorem unwind_raise_frameK {m : Machine} {fid : FrameId} {k : List Kont} {exc : Value}
    (hkm : m.kont = .frameK fid :: k) :
    Interp.unwind m (.raiseJ exc)
      = .next (Interp.withCtl { m with kont := k, stack := m.stack.tail }
          (.jump (.raiseJ exc))) := by
  unfold Interp.unwind
  rw [hkm]

/-- **L245: the same, at a block frame.** `unwind`'s `blkFrameK` arm sends a `.raiseJ`
    on with `stack := m.stack.tail`, which is `frameK`'s arm at a different label — one
    `rw` and one `simp` for the arm's own `match` on the jump. -/
theorem unwind_raise_blkFrameK {m : Machine} {fid : FrameId} {lam : Bool}
    {brk : Option FrameId} {cl : Closure} {args : List Value} {k : List Kont} {exc : Value}
    (hkm : m.kont = .blkFrameK fid lam brk cl args :: k) :
    Interp.unwind m (.raiseJ exc)
      = .next (Interp.withCtl { m with kont := k, stack := m.stack.tail }
          (.jump (.raiseJ exc))) := by
  unfold Interp.unwind
  rw [hkm]

/-- **The konts a propagating raise walks, and how the frame stack shrinks under it**
    (L217). `RetOk`'s shape with the type removed.

    `RetTransparent` is reused rather than duplicated, and that reuse is a fact about
    `unwind` rather than a convenience: the konts it lists are exactly the ones that hit
    `unwind`'s **catch-all** (or the `while` arm's `_`), and that catch-all does not look
    at the jump — so a kont transparent to a `.retJ` is transparent to a `.raiseJ` for
    the same one line of the interpreter. `frameK` is the one that is not, and it is the
    `pop` constructor. -/
inductive RaiseOk : List (FrameCtx × Env) → List Kont → Prop where
  | nil {Γs} : RaiseOk Γs []
  | skip {Γs κ k} : RetTransparent κ → RaiseOk Γs k → RaiseOk Γs (κ :: k)
  | pop {cΓ Γs k fid} : RaiseOk Γs k → RaiseOk (cΓ :: Γs) (.frameK fid :: k)
  /-- **L245: a block frame pops on a raise too**, and it is `pop`'s shape at the other
      popping kont — `unwind`'s `blkFrameK` arm sends a `.raiseJ` on with
      `stack := m.stack.tail`, exactly as its `frameK` arm does. A separate constructor
      rather than a generalization of `pop` because the two are different `Kont`
      constructors and the raise consecution case splits on the head. -/
  | popBlk {cΓ Γs k fid lam brk cl args} :
      RaiseOk Γs k → RaiseOk (cΓ :: Γs) (.blkFrameK fid lam brk cl args :: k)

/-- **`RaiseOk`, derived from `KontOk`** — the counterpart of `KontOk.retOk` (L200), and
    cheaper for the reason `RaiseOk` is cheaper: no `top = false`, no `c.ret`, no
    `infer_table_ret` composition, because there is no type to line up. Every `KontOk`
    constructor is either a `RetTransparent` kont or `frameK`, which is why the induction
    is one line per constructor. -/
theorem KontOk.raiseOk : ∀ {k : List Kont} {D : Decls} {h : Heap} {c : FrameCtx} {Γ : Env}
    {Γs : List (FrameCtx × Env)} {τ : Ty}, KontOk D h ((c, Γ) :: Γs) τ k → RaiseOk Γs k
  | [], _, _, _, _, _, _, _ => RaiseOk.nil
  | κ :: k, D, h, c, Γ, Γs, τ, hk => by
      cases hk with
      -- L245: a block frame pops on a raise, exactly as an activation does.
      | blkFrameK _ _ _ hk' => exact .popBlk (KontOk.raiseOk hk')
      | recvKBlk _ _ _ _ _ _ hk' _ => exact .skip trivial (KontOk.raiseOk hk')
      -- L253: `unwind` has no arm for `iterK`, so a raise passes straight through.
      | iterK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk' =>
          exact .skip trivial (KontOk.raiseOk hk')
      | seqNil hw hk' _ => exact .skip trivial (KontOk.raiseOk hk')
      | seqCons hs hw hk' _ => exact .skip trivial (KontOk.raiseOk hk')
      | asgn hib hw hk' _ => exact .skip trivial (KontOk.raiseOk hk')
      | asgnIvar hsc hw hcf hk' _ => exact .skip trivial (KontOk.raiseOk hk')
      | asgnGvar hpg hgt hcf hw hk' _ => exact .skip trivial (KontOk.raiseOk hk')
      | ifK hi hw hk' _ => exact .skip trivial (KontOk.raiseOk hk')
      | whileCond hl hw hk' _ => exact .skip trivial (KontOk.raiseOk hk')
      | whileBody hl hw hk' _ => exact .skip trivial (KontOk.raiseOk hk')
      | recvK ha hsg hsub hw hk' _ => exact .skip trivial (KontOk.raiseOk hk')
      | recvK0 hsg hw hk' _ => exact .skip trivial (KontOk.raiseOk hk')
      | argsK hv hva hst hia hsr hsg hw hk' _ => exact .skip trivial (KontOk.raiseOk hk')
      | superArgsK hva hst hia hsr hmt hmn hrow hps hrt hw hk' _ =>
          exact .skip trivial (KontOk.raiseOk hk')
      | arrK hs hw hk' _ => exact .skip trivial (KontOk.raiseOk hk')
      | arrSplatK ha hs hw hk' _ => exact .skip trivial (KontOk.raiseOk hk')
      | cpathK hb hsc hw hk' _ => exact .skip trivial (KontOk.raiseOk hk')
      | retValK hr hs hk' _ => exact .skip trivial (KontOk.raiseOk hk')
      | frameK hrt hil hk' => exact .pop (KontOk.raiseOk hk')

/-- **The kont shape a `next` walks** (L227), `RetOk`'s third sibling — and the one that
    does **not cross a frame**: a `next` restarts the enclosing loop in the *same*
    activation. So it has no `pop` and no `nil`. Both of those positions are **refuted**
    rather than handled: `unwind` at `[]` answers `.stuck` and at a `frameK` answers
    `.unsupported`, and `KontOk.nil`'s and `KontOk.frameK`'s `inLoop = none` premises
    (L224/L227) are what refute them.

    The two `loop` constructors carry exactly `KontOk.whileCond`'s premises, which is what
    the restart needs. The *environment* obligation lives in `CtlOk`, because the rule is
    what can check it (L224). -/
inductive NxtOk (D : Decls) (h : Heap) :
    FrameCtx → List (FrameCtx × Env) → List Kont → Prop where
  | loopCond {ctx Γl Γs τw c body k Γk} :
      LoopOk D Γl c body Γs.isEmpty { ctx with inLoop := some Γl } →
      subTy .nilT τw = true →
      KontOk D h ((ctx, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γl := by first | exact SubEnv.refl _ | assumption) →
      NxtOk D h { ctx with inLoop := some Γl } Γs (.whileCondK c body :: k)
  | loopBody {ctx Γl Γs τw c body k Γk} :
      LoopOk D Γl c body Γs.isEmpty { ctx with inLoop := some Γl } →
      subTy .nilT τw = true →
      KontOk D h ((ctx, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γl := by first | exact SubEnv.refl _ | assumption) →
      NxtOk D h { ctx with inLoop := some Γl } Γs (.whileBodyK c body :: k)
  | skip {c Γs κ k} :
      NxtTransparent κ → NxtOk D h c Γs k → NxtOk D h c Γs (κ :: k)

/-- **`NxtOk`, derived from `KontOk`** (L227) — `KontOk.retOk`'s sibling, and it needs the
    same two hypotheses for the same two reasons.

    `c.inLoop = some Γl` is what refutes the `nil` and `frameK` positions. `Γs.isEmpty =
    false` is what makes **`infer_table_loop`** (L226) applicable: every threading
    constructor hands the continuation a table the chain computed, and without that lemma the
    derived relation would sit at the chain's deepest table while `CtlOk` needs the
    invariant's. That was L225's blocker and it is now one `subst` per threading case. -/
theorem KontOk.nxtOk : ∀ {k : List Kont} {D : Decls} {h : Heap} {c : FrameCtx} {Γ : Env}
    {Γs : List (FrameCtx × Env)} {τ : Ty} {Γl : Env},
    KontOk D h ((c, Γ) :: Γs) τ k → c.inLoop = some Γl → Γs.isEmpty = false →
    NxtOk D h c Γs k
  | [], _, _, c, Γ, Γs, _, _, hk, hil, _ => by
      cases hk with
      | nil hr hl => exact absurd (hl (c, Γ) Γs rfl) (by rw [hil]; simp)
  | κ :: k, D, h, c, Γ, Γs, τ, Γl, hk, hil, htop => by
      have hls : c.inLoop.isSome = true := by rw [hil]; simp
      cases hk with
      -- L245: the block's context opens no loop channel, so this case does not exist.
      | blkFrameK _ hl _ _ => exact absurd hil (by rw [hl]; simp)
      | recvKBlk _ _ _ _ _ _ hk' _ => exact .skip trivial (KontOk.nxtOk hk' hil htop)
      | iterK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hl _ =>
          exact absurd hil (by rw [hl] at hil ⊢; simp)
      | seqNil hw hk' _ => exact .skip trivial (KontOk.nxtOk hk' hil htop)
      | seqCons hs hw hk' _ =>
          have hq : _ = D := inferSeq_table_loop (ctx := c) hls htop hs
          subst hq
          exact .skip trivial (KontOk.nxtOk hk' hil htop)
      | asgn hib hw hk' _ => exact .skip trivial (KontOk.nxtOk hk' hil htop)
      | asgnIvar hsc hw hcf hk' _ => exact .skip trivial (KontOk.nxtOk hk' hil htop)
      | asgnGvar hpg hgt hcf hw hk' _ => exact .skip trivial (KontOk.nxtOk hk' hil htop)
      | ifK hi hw hk' _ =>
          have hq : _ = D := inferIf_table_loop (ctx := c) hls htop hi
          subst hq
          exact .skip trivial (KontOk.nxtOk hk' hil htop)
      | recvK ha hsg hsub hw hk' _ =>
          have hq : _ = D := inferArgs_table_loop (ctx := c) hls htop ha
          subst hq
          exact .skip trivial (KontOk.nxtOk hk' hil htop)
      | recvK0 hsg hw hk' _ => exact .skip trivial (KontOk.nxtOk hk' hil htop)
      | argsK hv hva hst hia hsr hsg hw hk' _ =>
          have hq : _ = D := inferArgs_table_loop (ctx := c) hls htop hia
          subst hq
          exact .skip trivial (KontOk.nxtOk hk' hil htop)
      | superArgsK hva hst hia hsr hmt hmn hrow hps hrt hw hk' _ =>
          have hq : _ = D := inferArgs_table_loop (ctx := c) hls htop hia
          subst hq
          exact .skip trivial (KontOk.nxtOk hk' hil htop)
      | arrK hs hw hk' _ =>
          have hq : _ = D := inferElems_table_loop (ctx := c) hls htop hs
          subst hq
          exact .skip trivial (KontOk.nxtOk hk' hil htop)
      | arrSplatK ha hs hw hk' _ =>
          have hq : _ = D := inferElems_table_loop (ctx := c) hls htop hs
          subst hq
          exact .skip trivial (KontOk.nxtOk hk' hil htop)
      | cpathK hb hsc hw hk' _ => exact .skip trivial (KontOk.nxtOk hk' hil htop)
      | retValK hr hs hk' _ => exact .skip trivial (KontOk.nxtOk hk' hil htop)
      -- **The two terminators.**
      | whileCond hl hw hsu hk' => exact .loopCond hl hw hsu hk'
      | whileBody hl hw hsu hk' => exact .loopBody hl hw hsu hk'
      -- **The refuted position** (L224).
      | frameK hrt hnl hk' => exact absurd hil (by rw [hnl]; simp)

def CtlOk (D : Decls) (c : FrameCtx) (Γ : Env) (Γs : List (FrameCtx × Env))
    (m : Machine) : Prop :=
  match m.ctl with
  | .eval e =>
    -- **The subsumption is here and only here** (L193). `infer` answers the
    -- expression's *own* type, the continuation is typed at whatever the enclosing
    -- rule registered, and a join is exactly the place those two differ: an `if`
    -- whose branches are `String` and `nil` registers `.nilable (.cls "String")`,
    -- and each branch then runs at its own type. One `subTy` between the two is all
    -- that needs saying, because `ValueTy` is already a relation — so the *value*
    -- clause below needs nothing.
    ∃ τ τ' Γ' D' Γk, infer D Γ e Γs.isEmpty c = some (τ, Γ', D') ∧ subTy τ τ' = true ∧
      SubEnv Γk Γ' ∧ KontOk D' m.heap ((c, Γk) :: Γs) τ' m.kont
  -- **The environment slack** (L236) is the second half of the same story, and it is
  -- what an `if` whose branches *bind* needs: the continuation was registered at the
  -- join's environment, and each branch then runs at its own — which is *wider*, since
  -- a branch may add bindings the join dropped. `SubEnv Γk Γ'` says the registered one
  -- is contained in the one the expression answers, and `SubEnv.refl` is what every
  -- other rule passes. Kept as a separate conjunct rather than folded into `KontOk`
  -- because the *constructors* carry the matching premise (defaulted to `refl`), so the
  -- two compose by `SubEnv.trans` at the one delivery case that needs it.
  | .value v => ∃ τ Γk, ValueTy m.heap v τ ∧ SubEnv Γk Γ ∧
      KontOk D m.heap ((c, Γk) :: Γs) τ m.kont
  -- **A `return` in flight** (L200), and the arm has exactly the three things `unwind`
  -- reads: the value's type, that every kont above the innermost `frameK` is
  -- transparent to a `.retJ` and that `frameK` accepts the type (`RetOk`), and that the
  -- jump's *target* is that `frameK`'s label — which L199's clause is what supplies.
  | .jump (.retJ v target) =>
    -- `RetOk` is indexed by the **callers'** environment stack, not by this
    -- activation's: the head is the frame the jump is about to leave, and nothing about
    -- it survives the pop. That indexing is what lets `skip` keep the index fixed while
    -- `KontOk`'s own head changes at every transparent constructor.
    ∃ σ, ValueTy m.heap v σ ∧ RetOk D m.heap Γs σ m.kont ∧
      firstFrameK m.kont = some target
  -- **A raise in flight** (L217), and the arm is *one conjunct* — which is the
  -- surprise, so read why before adding to it.
  --
  -- `typeStuck` fires only on an uncaught **type** error (`Proof/TypeSafety.lean`), and
  -- L216 made `StepOk` agree. So a propagating user exception owes nothing about a
  -- *type*: `unwind` carries it through every transparent kont unchanged, pops one frame
  -- at each `frameK`, and turns it into `.uncaught` at `[]`, which `StepOk` now admits
  -- exactly when this conjunct holds. The heap never moves along that path, so the
  -- conjunct is preserved by every one of those steps for free.
  --
  -- **`RaiseOk` is the second conjunct, and the first draft did without it and was
  -- wrong.** The tempting argument is that a raise owes nothing about the continuation,
  -- so `frameKLabels` and `StackCtx` alone should carry the pops. What that misses is
  -- that `CtlOk`'s jump arm has **no `KontOk`**, so nothing bounds which konts are on
  -- the stack — and `unwind` does not propagate a raise through all of them.
  -- `definedGuardK` turns it into `.next (withCtl m (.value .nil))`, at which point
  -- `CtlOk` wants a `KontOk` for the continuation and there is none to be had. So the
  -- stack has to be *known* to be raise-propagating, which is what this relation says.
  --
  -- Unlike `RetOk` it carries no type — a propagating raise has no value the receiving
  -- kont must accept — so it is indexed by the environment stack and the konts alone.
  --
  -- What this arm does not yet support is a raise being **caught**: a handler resumes
  -- with `.value v` and would need a `KontOk` below it. That is the `begin`/`rescue`
  -- rung, and it is where `RaiseOk` grows a third constructor
  -- (*a handler typed at τ*). Stated so the next commit does not read the absence as an
  -- oversight.
  | .jump (.raiseJ exc) => ¬ isTypeError m.heap exc ∧ RaiseOk Γs m.kont
  -- **A `next` in flight** (L227). Three things, and the third is the one `return` did not
  -- need: `NxtOk` says the kont stack reaches a loop kont without crossing a frame, and
  -- `SubEnv Γl Γ` says the loop's *entry* environment — which its condition was typed at —
  -- is weaker than the one the `next` fires in. A `next` restarts the loop in the **same
  -- frame**, so the environment survives the jump and has to be reconciled; `RetOk` and
  -- `RaiseOk` both pop a frame and owe nothing here (L224). `SubEnv` is L218's relation,
  -- getting its first consumer.
  | .jump (.nxtJ _) =>
      ∃ Γl, c.inLoop = some Γl ∧ SubEnv Γl Γ ∧ Γs.isEmpty = false ∧
        NxtOk D m.heap c Γs m.kont
  -- The other jumps stay excluded: `break`/`retry`/`redo`/`throw` are not in the fragment,
  -- so no step can produce one.
  | .jump _ => False

/-- **Transport of the continuation judgement.** The other half of L137's cost:
    a heap-writing step must carry every `ValueTy` fact already stored in the
    continuation stack into the new heap. Only `argsK` stores one, so this is a
    one-case induction today — and it is the case that stops being trivial the
    moment `Ty` gains a nominal arm, which is the point of writing it now. -/
theorem KontOk.heap_congr' {h' : Heap} :
    ∀ {D : Decls} {h : Heap} {Γs : List (FrameCtx × Env)} {τ : Ty} {k : List Kont},
      KontOk D h Γs τ k → TypeAgree h h' → KontOk D h' Γs τ k := by
  intro D h Γs τ k hk
  induction hk with
  | nil hr hl => intro _; exact .nil hr hl
  | blkFrameK hr hl hw _ ih => intro ha; exact .blkFrameK hr hl hw (ih ha)
  | recvKBlk hbs hbody hsu2 hsb hsw hib _ hsu ih =>
    intro ha; exact .recvKBlk hbs hbody hsu2 hsb hsw hib (ih ha) hsu
  | iterK hp hlo hlam hbp hgb hany hr hil hsc hmt hib hbody hsu hsb hvs hsr hrv hrt
      hcr hci _ ih =>
    intro ha
    exact .iterK hp hlo hlam hbp hgb hany hr hil hsc hmt hib hbody hsu hsb
      (fun a hm => ValuesTy.congr ha (hvs a hm)) hsr (ValueTy.congr ha hrv) hrt hcr hci
      (ih ha)
  | seqNil hw _ hsu ih => intro ha; exact .seqNil hw (ih ha) hsu
  | seqCons hs hw _ hsu ih => intro ha; exact .seqCons hs hw (ih ha) hsu
  | asgn hib hw _ hsu ih => intro ha; exact .asgn hib hw (ih ha) hsu
  | asgnIvar hsc hw hcf _ hsu ih => intro ha; exact .asgnIvar hsc hw hcf (ih ha) hsu
  | asgnGvar hpg hgt hcf hw _ hsu ih => intro ha; exact .asgnGvar hpg hgt hcf hw (ih ha) hsu
  | ifK hi hw _ hsu ih => intro ha; exact .ifK hi hw (ih ha) hsu
  | whileCond hl hw _ hsu ih => intro ha; exact .whileCond hl hw (ih ha) hsu
  | whileBody hl hw _ hsu ih => intro ha; exact .whileBody hl hw (ih ha) hsu
  | recvK hsg ha' hsub hw _ hsu ih => intro ha; exact .recvK hsg ha' hsub hw (ih ha) hsu
  | recvK0 hsg hw _ hsu ih => intro ha; exact .recvK0 hsg hw (ih ha) hsu
  | cpathK hb hsc hw _ hsu ih => intro ha; exact .cpathK hb hsc hw (ih ha) hsu
  | superArgsK hva hst hia hsr hmt hmn hrow hps hrt hw _ hsu ih =>
      intro ha
      exact .superArgsK (ValuesTy.congr ha hva) hst hia hsr hmt hmn hrow hps hrt hw (ih ha) hsu
  | argsK hv hva hst hia hsr hsg hw _ hsu ih =>
      intro ha
      exact .argsK (ValueTy.congr ha hv) (ValuesTy.congr ha hva) hst hia hsr hsg hw (ih ha) hsu
  | arrK hs hw _ hsu ih => intro ha; exact .arrK hs hw (ih ha) hsu
  | arrSplatK hv hs hw _ hsu ih => intro ha; exact .arrSplatK hv hs hw (ih ha) hsu
  | frameK hr hil _ ih => intro ha; exact .frameK hr hil (ih ha)
  | retValK hr hs _ hsu ih => intro ha; exact .retValK hr hs (ih ha) hsu

/-- The shape every call site reads. `heap_congr'` takes the heap agreement
    *after* the derivation because the induction generalizes the heap index, and
    with the declarations now an index too there is no instantiation at which the
    hypothesis can stay fixed outside. -/
theorem KontOk.heap_congr {h h' : Heap} (ha : TypeAgree h h')
    {D : Decls} {Γs : List (FrameCtx × Env)} {τ : Ty} {k : List Kont}
    (hk : KontOk D h Γs τ k) : KontOk D h' Γs τ k :=
  KontOk.heap_congr' hk ha

/-- `dropLast` past a cons, which needs the tail non-empty — the bottom activation is
    the one entry with no `frameK`, so this is where that asymmetry is paid. -/
theorem dropLast_cons_ne {α : Type} {a : α} {l : List α} (h : l ≠ []) :
    (a :: l).dropLast = a :: l.dropLast := by
  cases l with
  | nil => exact absurd rfl h
  | cons b t => simp

/-- **The globals conjunct** (L228), and it is the first `Inv` clause about machine
    state that is neither the heap nor the frames.

    Indexed by the *heap* and the *association list* rather than by the machine, which is
    `FramesOk`'s shape and is here for `FramesOk`'s reason: every step that changes only
    the control or the continuation leaves both projections `rfl`-equal, so the conjunct
    transports by handing the hypothesis over untouched at all but a handful of cases.

    **Only plain globals are constrained.** `$!`, `$~` and the match views are not in
    `m.globals` at all — `getGlobal` routes them to `currentExc`, the frame's `lastMatch`
    and `matchGlobal`'s computation — so a claim about them here would be a claim about the
    wrong storage. `plainGlobal` is the hypothesis, and it is the reason the read rule
    carries the same test. -/
def GlobalsOk (D : Decls) (h : Heap) (gs : List (String × Value)) : Prop :=
  ∀ x p σ, plainGlobal x = true → gs.find? (·.1 == x) = some p →
    globalTy? D x = some σ → ValueTy h p.2 σ

/-- **A plain global is not a match view** (L228), which is what makes the read step a
    plain `getGlobal`: `evalExpr`'s gvar arm consults `matchGlobal` first, and that answers
    `none` for every name outside `isMatchView`. The rule's guard is what supplies it —
    `Step.varGvar`'s old claim that a gvar read *is* a `getGlobal` becomes true again,
    conditionally, for exactly the names the table may declare. -/
theorem matchGlobal_none_of_plain {m : Machine} {x : String} (h : plainGlobal x = true) :
    Interp.matchGlobal m x = none := by
  have hv : Interp.isMatchView x = false := by
    unfold plainGlobal at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact h.2
  unfold Interp.matchGlobal
  simp [hv]

/-- **And `setGlobal` writes the association list** (L228), for the same reason: the `$~`
    branch is the only other one and `plainGlobal` excludes it. -/
theorem setGlobal_of_plain {m : Machine} {x : String} {v : Value} (h : plainGlobal x = true) :
    m.setGlobal x v = { m with globals := (x, v) :: m.globals.filter (·.1 != x) } := by
  have ht : (x == "$~") = false := by
    unfold plainGlobal at h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simpa using h.1.2
  unfold Machine.setGlobal
  rw [if_neg (by simpa using ht)]

/-- **The read**, which is the only shape the rule consumes: `getGlobal` answers the stored
    value or `.nil`, and `mkNilable σ` is what admits both. The `nil` half is why the rule
    answers a *nilable* type and not `σ` — an unset global reads `nil` in Ruby, with no
    error and no declaration consulted. -/
theorem GlobalsOk.read {D : Decls} {m : Machine} {x : String} {σ : Ty}
    (hg : GlobalsOk D m.heap m.globals) (hp : plainGlobal x = true)
    (hd : globalTy? D x = some σ) : ValueTy m.heap (m.getGlobal x) (mkNilable σ) := by
  -- The two machine-backed names, read off `plainGlobal` as **`Bool` facts**: `simp` on
  -- `x = "$!"` unfolds `isMatchView` and times out, and `hp` itself is still needed below.
  have hb : (x == "$!") = false := by
    have := hp; unfold plainGlobal at this
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    simpa using this.1.1
  have ht : (x == "$~") = false := by
    have := hp; unfold plainGlobal at this
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    simpa using this.1.2
  unfold Machine.getGlobal
  rw [if_neg (by simpa using hb), if_neg (by simpa using ht)]
  cases hf : m.globals.find? (·.1 == x) with
  | none => exact ValueTy.weaken (ValueTy.exact rfl) (subTy_nilT_mkNilable _)
  | some pr => exact ValueTy.weaken (hg x pr σ hp hf hd) (subTy_mkNilable _)

/-- **The write**, and the one thing it has to check is what the rule checks: the value's
    type is the declared one. The list `setGlobal` builds is `(x, v) :: filter`, so a
    lookup either finds the new head — the `ValueTy` the rule supplies — or an old entry,
    which the incoming conjunct covers. -/
theorem GlobalsOk.set {D : Decls} {h : Heap} {gs : List (String × Value)} {x : String}
    {v : Value} {σ : Ty} (hg : GlobalsOk D h gs) (hd : globalTy? D x = some σ)
    (hv : ValueTy h v σ) :
    GlobalsOk D h ((x, v) :: gs.filter (·.1 != x)) := by
  intro y p τ hpl hf hdy
  by_cases hxy : (x == y) = true
  · have hyx : x = y := by simpa using hxy
    subst hyx
    rw [List.find?_cons_of_pos (p := fun (e : String × Value) => e.1 == x) (by simp)] at hf
    simp only [Option.some.injEq] at hf
    subst hf
    rw [hdy] at hd
    simp only [Option.some.injEq] at hd
    subst hd
    exact hv
  · rw [List.find?_cons_of_neg (p := fun (e : String × Value) => e.1 == y) (by simpa using hxy)] at hf
    -- The list fact is `HeapFacts`' `find?_filter_ne`, which is already stated over any
    -- `List (String × α)` and was written for the *method*-table filter at L142 — the
    -- association list `setGlobal` builds has the same shape, which is why this case
    -- needed no new lemma once I looked.
    have hne : ¬ (y = x) := fun hq => hxy (by rw [hq]; simp)
    rw [find?_filter_ne _ hne] at hf
    exact hg y p τ hpl hf hdy

/-- **And the table is irrelevant up to `SubDecls`** (L228) — a `def` grows `rows` and
    nothing else, so `globalTy?` is unmoved and the conjunct transports by rewriting the
    lookup. Needed because the `def` case re-establishes `Inv` at the *grown* table. -/
theorem GlobalsOk.table {D D' : Decls} {h : Heap} {gs : List (String × Value)}
    (hs : SubDecls D D') (hg : GlobalsOk D h gs) : GlobalsOk D' h gs :=
  fun x p σ hp hf hd => hg x p σ hp hf (by rw [← hs.globalTy_eq x]; exact hd)

/-- **And the heap transport**, one `ValueTy.congr` under a binder. Every allocating step
    owes exactly this, and it is why the conjunct costs an allocating case one term. -/
theorem GlobalsOk.congr {D : Decls} {h h' : Heap} {gs : List (String × Value)}
    (ha : TypeAgree h h') (hg : GlobalsOk D h gs) : GlobalsOk D h' gs :=
  fun x p σ hp hf hd => ValueTy.congr ha (hg x p σ hp hf hd)

/-- **The closure a continuation carries, if it carries one** (L247). Two constructors
    do: `iterK` remembers the block a native iterator is driving, and `blkFrameK`
    remembers it so that `redo` can re-enter the same invocation. -/
def KontClosure : Kont → Option Closure
  | .iterK cl _ _ _ _ _ _ => some cl
  | .blkFrameK _ _ _ cl _ => some cl
  | _ => none

/-- **Every closure the continuation mentions captures a live, non-block frame** (L247).

    This is the *whole* frame-side fact a block call needs, and it is small because the
    captured frame's **environment** is not among the things it has to supply: the block
    body is typed with the enclosing locals at `.any` (L232's clause, written for exactly
    this), so the block frame's `FrameConforms` obligation at an outer name is
    `ValueTy h _ .any`, which holds for every value. What is left is `ShallowChain`'s two
    conjuncts, and they are these.

    A **list-wide** predicate over the kont rather than a positional pairing of kont
    against stack — which is what L246 priced and L247 withdrew. Preserving it is three
    observations: frames only grow, `setLocal` writes `locals` and not `captured`, and
    the one step that pushes such a kont pushes it with `cl.captured = m.stack.headD 0`,
    whose non-blockness is `StackCtx`'s L243 clause. -/
def ClosuresOk (m : Machine) : Prop :=
  ∀ κ ∈ m.kont, ∀ cl, KontClosure κ = some cl →
    cl.captured < m.frames.size ∧ (m.frames.getD cl.captured default).captured = none ∧
    -- **L250: and the three *name-free* `StackCtx` clauses of that frame** — the ones a
    -- block activation's own entry will owe, since `callClosure` copies `defmod`, `cref`
    -- and `defVis` from here. Name-free is the whole point: `className … = c.cls` is the
    -- clause that needs the pairing, and it is guarded on `c.inBlock` instead (L250).
    (m.heap.classPayload? (m.frames.getD cl.captured default).defmod).isSome ∧
    Boot.objectId ∈ (m.frames.getD cl.captured default).cref

theorem ClosuresOk.cons {m : Machine} {κ : Kont} {ctl : Ctl}
    (hκ : KontClosure κ = none) (h : ClosuresOk m) :
    ClosuresOk (Interp.withKont m ctl κ) := by
  intro κ' hmem cl hcl
  rcases List.mem_cons.mp hmem with rfl | hmem'
  · exact absurd hcl (by rw [hκ]; simp)
  · exact h κ' hmem' cl hcl

theorem ClosuresOk.ctl {m : Machine} {ctl : Ctl} (h : ClosuresOk m) :
    ClosuresOk (Interp.withCtl m ctl) := h

theorem ClosuresOk.cons' {m : Machine} {κ : Kont} {ctl : Ctl}
    (hκ : KontClosure κ = none) (h : ClosuresOk m) :
    ClosuresOk (Interp.withKont m ctl κ) := h.cons hκ

/-- The four fields `ClosuresOk` reads off the captured frame. Stated as a predicate so
    the transport takes one hypothesis rather than four, and so `setLocal` — which writes
    `locals` and none of these — discharges it in one lemma. -/
def FrameShape (f g : Frame) : Prop :=
  f.captured = g.captured ∧ f.defmod = g.defmod ∧ f.cref = g.cref ∧
  defVisOfDef f = defVisOfDef g

theorem FrameShape.rfl' (f : Frame) : FrameShape f f := ⟨rfl, rfl, rfl, rfl⟩

/-- **The one shape every consecution case needs** (L247): the frames may have grown
    (or had a `locals` rewritten), and the continuation may have gained konts that carry
    no closure or lost some from the front. Every step in the fragment is an instance,
    which is why the sites take one lemma rather than one argument each. -/
theorem ClosuresOk.transport {m m' : Machine} (h : ClosuresOk m)
    -- **Every closure the new continuation mentions, the old one mentioned** (L253) —
    -- which is weaker than *every new kont was already there*, and the weakening is what
    -- the block call needs: it pushes two konts that are **new** and carry the closure
    -- the `iterK` it replaces already carried.
    (hk : ∀ κ ∈ m'.kont, ∀ cl, KontClosure κ = some cl →
      ∃ κ₀ ∈ m.kont, KontClosure κ₀ = some cl)
    (hsz : m.frames.size ≤ m'.frames.size)
    (hget : ∀ p, p < m.frames.size → FrameShape (m'.frames.getD p default)
      (m.frames.getD p default))
    (hh : ∀ o, (m.heap.classPayload? o).isSome → (m'.heap.classPayload? o).isSome) :
    ClosuresOk m' := by
  intro κ hmem cl hcl
  obtain ⟨κ₀, hin, hcl₀⟩ := hk κ hmem cl hcl
  obtain ⟨hlt, hcap, hpay, hcref⟩ := h κ₀ hin cl hcl₀
  obtain ⟨e1, e2, e3, e4⟩ := hget _ hlt
  exact ⟨Nat.lt_of_lt_of_le hlt hsz, by rw [e1]; exact hcap,
    by rw [e2]; exact hh _ hpay, by rw [e3]; exact hcref⟩

/-- The activation push: one `frameK` (which carries no closure) and one frame. -/
theorem ClosuresOk.pushFrame {m m' : Machine} {fid : FrameId} {f : Frame}
    (h : ClosuresOk m) (hk : m'.kont = .frameK fid :: m.kont)
    (hf : m'.frames = m.frames.push f) (hhp : m'.heap = m.heap) : ClosuresOk m' :=
  h.transport
    (by
      intro κ hmem cl hcl
      rw [hk] at hmem
      rcases List.mem_cons.mp hmem with rfl | hin
      · exact absurd hcl (by simp [KontClosure])
      · exact ⟨κ, hin, hcl⟩)
    (by rw [hf, Array.size_push]; omega)
    (by intro p hp; rw [hf, getD_push_lt _ _ _ hp]; exact FrameShape.rfl' _)
    (by intro o ho; rw [hhp]; exact ho)

/-- `setLocal` writes a frame's `locals`; every frame's `captured` is where it was. -/
theorem setLocal_captured (m : Machine) (x : String) (v : Value) (p : ObjId) :
    ((m.setLocal x v).frames.getD p default).captured
      = (m.frames.getD p default).captured := by
  show ((m.frames.set! _ _).getD p default).captured = _
  by_cases hq : p = Machine.setLocal.owner m x (m.stack.headD 0) (m.stack.headD 0)
      (m.frames.size + 1)
  · by_cases hlt : p < m.frames.size
    · rw [hq, getD_set!_self _ _ _ (hq ▸ hlt)]
    · simp only [Array.getD, Array.set!]
      rw [dif_neg (by simpa using hlt), dif_neg hlt]
  · rw [getD_set!_ne _ _ _ _ hq]

theorem setLocal_shape (m : Machine) (x : String) (v : Value) (p : ObjId) :
    FrameShape ((m.setLocal x v).frames.getD p default) (m.frames.getD p default) := by
  show FrameShape ((m.frames.set! _ _).getD p default) _
  by_cases hq : p = Machine.setLocal.owner m x (m.stack.headD 0) (m.stack.headD 0)
      (m.frames.size + 1)
  · by_cases hlt : p < m.frames.size
    · rw [hq, getD_set!_self _ _ _ (hq ▸ hlt)]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · simp only [Array.getD, Array.set!]
      rw [dif_neg (by simpa using hlt), dif_neg hlt]
      exact FrameShape.rfl' _
  · rw [getD_set!_ne _ _ _ _ hq]
    exact FrameShape.rfl' _

theorem setLocal_frames_size (m : Machine) (x : String) (v : Value) :
    (m.setLocal x v).frames.size = m.frames.size := by
  show (m.frames.set! _ _).size = _
  simp [Array.set!]

/-- The common instance: nothing about the frames moved. -/
theorem ClosuresOk.konts {m m' : Machine} (h : ClosuresOk m)
    (hf : m'.frames = m.frames) (hhp : m'.heap = m.heap)
    (hk : ∀ κ ∈ m'.kont, κ ∈ m.kont ∨ KontClosure κ = none) : ClosuresOk m' :=
  h.transport (fun κ hm cl hcl => by
      rcases hk κ hm with hin | hnone
      · exact ⟨κ, hin, hcl⟩
      · exact absurd hcl (by rw [hnone]; simp))
    (by rw [hf]; exact Nat.le_refl _)
    (by intro p _; rw [hf]; exact FrameShape.rfl' _)
    (by intro o ho; rw [hhp]; exact ho)

/-- **The invariant** handed to `invariant_sound_from`.

    **`Saturated` is the third heap conjunct since L148**, and it is here for one
    reason: `DeclsOk_grow` — the invariant's own preservation across an allocating
    step — needs the ancestor walk to be fuel-saturated *at the heap the step starts
    from*, and only the invariant can carry a fact there. It is a heap clause of the
    same kind as `NoHook`: true at the boot heap by `decide`, true at the
    prelude-booted heap by the certificate `heapOkB` (L148 folded `saturatedB` into
    it), and preserved by every step that writes the heap
    (`Saturated_defineMethod`, `Saturated_grow`).

    It is *not* a fragment restriction. A program cannot make it false — nothing in
    the object model builds a cyclic `include` — but nothing in the `Heap` **type**
    forbids one either, which is why it cannot be a theorem.

    **`LitClsOk` is the fourth heap conjunct** (L151), and it is here for the
    producer: `infer` gives a string literal the type `.cls "String"`, which is a
    claim about a name, while the step allocates an object whose class is the id
    `Boot.stringId`. See its own docstring for why the join belongs in the
    invariant rather than at the use site.

    **`BottomObj` is the sixth conjunct** (L155), and it is the only one that is
    not about the heap: *the outermost activation's definee is `Object`.* It is
    what turns `infer`'s `top` flag from a decoration into a fact — `CtlOk` reads
    the mode as `Γs.isEmpty`, `FramesOk` makes that a singleton frame stack, and
    this names that frame's definee. Carried rather than derived because nothing
    in the `Machine` *type* says the bottom frame is the toplevel one; `initFrom`
    establishes it and every step preserves it.

    **The declaration table is existential** (F1b.8), where it used to be a
    parameter. It has to be: the whole content of the threading is that the table
    *changes along a run*, and `invariant_sound_from` quantifies its invariant
    over every reachable machine, so no single table can index the statement.
    What pins it down is `initiation`, which supplies `declsOf p` at the start,
    and `CtlOk`, which ties it to the program by `infer`.

    One table, not two: `DeclsOk` and `CtlOk` read the same `F`, because the
    `def` step moves both together — the row enters the table exactly when the
    method enters the heap. A *smaller* control table related by `SubDecls` is
    what the user-method arm will want later, and it is left out here for the
    reason `crubySingletonShadow` was (L145): a clause that looks necessary is a
    measurement, not a judgement. -/
def Inv (m : Machine) : Prop :=
  NoHook m.heap ∧ Saturated m.heap ∧ LitClsOk m.heap ∧
    ClassOk m.heap ∧ BottomObj m.frames m.stack ∧
    -- **L199: the frame stack and the continuation's `frameK`s are the same list**,
    -- modulo the bottom activation, which is pushed by `Machine.init` and has no
    -- `frameK`. A machine fact rather than a typing one — it mentions no `Decls` and
    -- no `Ty` — which is why it sits out here beside `BottomObj` rather than inside
    -- the existential.
    framePopLabels m.kont = m.stack.dropLast ∧
    -- **L247: every closure on the continuation captures a live, non-block frame.** A
    -- machine fact like the two above it, and the *whole* frame-side price of a block
    -- call — see `ClosuresOk` for why the captured frame's environment is not part of it.
    ClosuresOk m ∧
    ∃ (F : Decls) (c : FrameCtx) (Γ : Env) (Γs : List (FrameCtx × Env)), DeclsOk F m.heap ∧
      FramesOk m.heap m.frames m.stack (Γ :: Γs.map Prod.snd) ∧
      StackCtx m.heap m.frames m.stack (c :: Γs.map Prod.fst) ∧
      -- **L228: the globals**, and it is inside the existential because it reads the
      -- table — the sixth one, and the first whose obligation is not about the heap.
      GlobalsOk F m.heap m.globals ∧
      CtlOk F c Γ Γs m

/-! ### Inversions used by the send cases -/

/-- **A signature exists only at a type dispatch can start from** (L193). `sigOf`
    reads `declFor`, which reads `tyClassNames`, which is `[]` at `.any` and at every
    nilable — so the existence of a row *is* the side condition `entry_dispatch` and
    `valueTy_tyClass` now ask for, and no rule has to carry it. That is the whole
    reason the two arms were given `[]` rather than a name. -/
theorem sigOf_atomic {D : Decls} {τr : Ty} {mname : String} {ps : List Ty} {τret : Ty}
    -- **L260 adds the hypothesis the conclusion used to *derive*.** `sigOf` now answers at
    -- a nilable receiver (union dispatch), so a row's existence no longer refutes that
    -- arm — the caller has to have ruled it out, and the two dispatch sites that cannot
    -- do so by `simp` split on it instead.
    (hnil : ∀ τ', τr ≠ .nilable τ')
    (h : sigOf D τr mname = some (ps, τret)) :
    -- **L239 adds the third**, from the same fact: `tyClassNames` is `[]` at the
    -- parameterised arm too, so a row's *existence* refutes it exactly as it refutes
    -- `.any` and a nilable. Every dispatch lemma's new side condition is therefore free at
    -- every caller — and the day `arrayOf` starts dispatching, this conjunct is where the
    -- bill lands, which is the honest place for it.
    τr ≠ .any ∧ (∀ τ', τr ≠ .nilable τ') ∧ ∀ σ, τr ≠ .arrayOf σ := by
  cases τr <;>
    simp_all [sigOf, declFor, tyClassNames]

/-- **A declaration's key is atomic** (L260) — `tyClassNames` is `[]` at `.any`, at a
    nilable and at an `arrayOf`, so `declFor` answering `some` refutes all three. This is
    `sigOf_atomic`'s old proof, moved one level down: `sigOf` itself is no longer atomic
    (it answers at a nilable now), but the rows it is *made of* still are. -/
theorem declFor_atomic {D : Decls} {τ : Ty} {mname : String} {d : MethodDecl}
    (h : declFor D τ mname = some d) :
    τ ≠ .any ∧ (∀ τ', τ ≠ .nilable τ') ∧ ∀ σ, τ ≠ .arrayOf σ := by
  cases τ <;> simp_all [declFor, tyClassNames]

/-- `valueTy?`'s range, at the two arms the nilable inversion needs to read back. -/
theorem valueTy_nilT {h : Heap} {v : Value} (hσ : valueTy? h v = some .nilT) :
    v = .nil := by
  cases v with
  | nil => rfl
  | ref o =>
    simp only [valueTy?] at hσ
    split at hσ
    · exact absurd hσ (by simp)
    · split at hσ
      · exact absurd hσ (by simp)
      · exact absurd hσ (by simp)
  | _ => exact absurd hσ (by simp [valueTy?])

theorem valueTy_not_nilable {h : Heap} {v : Value} {σ : Ty}
    (hσ : valueTy? h v = some (.nilable σ)) : False := by
  cases v with
  | ref o =>
    simp only [valueTy?] at hσ
    split at hσ
    · exact absurd hσ (by simp)
    · split at hσ
      · exact absurd hσ (by simp)
      · exact absurd hσ (by simp)
  | _ => exact absurd hσ (by simp [valueTy?])

/-- **A nilable is either `nil` or the thing under it** (L260). The three disjuncts of
    `ValueTy` all reduce: `.any` is below a nilable only when it is below what is under
    it (`subTy_any_false`), an array likewise, and the exact arm's `subTy σ' (.nilable σ)`
    is `σ' = .nilT ∨ σ' = .nilable σ ∨ subTy σ' σ` — of which the middle is refuted
    because `valueTy?` never answers a nilable. -/
theorem valueTy_nilable_inv {h : Heap} {v : Value} {σ : Ty} (ha : σ ≠ .any)
    (hn : ∀ τ', σ ≠ .nilable τ') (hnar : ∀ τ', σ ≠ .arrayOf τ')
    (hv : ValueTy h v (.nilable σ)) : v = .nil ∨ ValueTy h v σ := by
  rcases hv with hany | ⟨σ', o, xs, hup, rfl, hb, hex, hpay, hall⟩ | ⟨σ', hσ, hsub⟩
  · simp only [subTy, Bool.or_eq_true, beq_iff_eq] at hany
    rcases hany with (h1 | h1) | h1
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
    · exact absurd h1.symm ha
  · simp only [subTy, Bool.or_eq_true, beq_iff_eq] at hup
    rcases hup with (h1 | h1) | h1
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
    · exact Or.inr (Or.inr (Or.inl ⟨σ', o, xs, by rw [← h1]; simp, rfl, hb, hex, hpay, hall⟩))
  · simp only [subTy, Bool.or_eq_true, beq_iff_eq] at hsub
    rcases hsub with (rfl | rfl) | h1
    · exact Or.inl (valueTy_nilT hσ)
    · exact absurd hσ (fun hq => (valueTy_not_nilable hq).elim)
    · exact Or.inr (Or.inr (Or.inr ⟨σ', hσ, by rw [h1]; simp⟩))

/-- The signature in the shape `EntryOk` reads it. Trivial, and it exists because
    `sigOf` is `declFor` composed with a projection while `DeclsOk` is stated over
    `declFor` — so the `argsK` case has to move between the two.

    **Generalized from `[τp]` to any `params` in L152**, because the zero-argument
    case needs it at `[]` and the two would otherwise be the same proof twice.

    **The recovered row takes no block** (L242), and that conjunct is not decoration:
    `sigOf` now refuses a block-taking row, so a rule that reads a signature has
    *shown* the row is blockless, and this is where that fact is handed to `DeclsOk`.
    The day a block-send rule exists it will read `declFor` directly rather than come
    through here, for exactly this reason. -/
theorem sigOf_declFor {D : Decls} {τr : Ty} {mname : String} {params : List Ty}
    {τret : Ty} (hnil : ∀ τ', τr ≠ .nilable τ')
    (h : sigOf D τr mname = some (params, τret)) :
    declFor D τr mname = some { params := params, ret := τret, blk := none } := by
  cases τr with
  | nilable σ => exact absurd rfl (hnil σ)
  | _ =>
    all_goals (
      unfold sigOf at h
      simp only [] at h
      cases hd : declFor D _ mname with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some d =>
        obtain ⟨ps, r, b⟩ := d
        rw [hd] at h
        cases b with
        | none =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rfl
        | some _ => exact absurd h (by simp))

/-- **L260's whole cost at a dispatch site, in one lemma.** A send whose receiver type
    is a nilable is *reduced* to the atomic arm the receiver value actually is: the union
    rule's two rows are ordinary rows at ordinary keys, so each dispatches by the
    machinery that was already there and neither needs a new `EntryOk` arm.

    Stated as a re-binding of the same three facts (`sigOf`, `ValueTy`, and now the
    atomicity side condition) so that a consecution case spends **one** `obtain` on it and
    its body is unchanged. -/
theorem sigOf_value_atomic {D : Decls} {h : Heap} {v : Value} {τ : Ty} {mname : String}
    {ps : List Ty} {τret : Ty}
    (hsg : sigOf D τ mname = some (ps, τret)) (hv : ValueTy h v τ) :
    ∃ τ₀, sigOf D τ₀ mname = some (ps, τret) ∧ ValueTy h v τ₀ ∧
      (∀ τ', τ₀ ≠ .nilable τ') := by
  cases hτ : τ with
  | nilable σ =>
    subst hτ
    obtain ⟨h1, h2⟩ := sigOf_nilable hsg
    obtain ⟨haσ, hnσ, hnarσ⟩ := declFor_atomic h2
    rcases valueTy_nilable_inv haσ hnσ hnarσ hv with rfl | hvσ
    · exact ⟨.nilT, by simp [sigOf, h1], ValueTy.exact rfl, by simp⟩
    · refine ⟨σ, ?_, hvσ, hnσ⟩
      cases σ with
      | nilable _ => exact absurd rfl (hnσ _)
      | _ => all_goals (simp only [sigOf]; rw [h2])
  | _ => exact ⟨τ, hτ ▸ hsg, hτ ▸ hv, by subst hτ; simp⟩

-- ~~`site_explicit`~~ — **withdrawn at L172**, together with the hypothesis it
-- needed. It said: *`evalExpr` chooses the send site syntactically, `infer`
-- rejects `self`, so the site is always `.explicit` in the fragment.* The second
-- clause stopped being true when `KontOk.recvK`/`recvK0` took the site as a
-- **parameter** and the `isSelf` guard came out of the rule. It was propping up
-- those constructors' `.explicit` index and nothing else, so it is unnecessary
-- rather than false — the same shape as `TypeAgree.symm` (L147) and
-- `ResolvesTo_grow` (L147): correct when written, and made pointless by a sharper
-- later statement.

/-- `Machine.currentFrame` and `curFrame` agree once the stack is non-empty. -/
theorem currentFrame_eq {m : Machine} (hne : m.stack ≠ []) :
    m.currentFrame = curFrame m := by
  cases hst : m.stack with
  | nil => exact absurd hst hne
  | cons fid _ => simp [Machine.currentFrame, curFrame, curFid, hst]

/-- Inversion for the two `super` rules (L212). Split by arity for the reason the rules
    are: `startSuperArgs … []` is `doSuper` outright (one step, no continuation) while
    the positive-arity form pushes a `superArgK`. -/
theorem infer_super0_inv {D D' : Decls} {Γ Γ' : Env} {τ : Ty} {top : Bool} {ctx : FrameCtx}
    (h : infer D Γ (.super' [] none) top ctx = some (τ, Γ', D')) :
    Γ' = Γ ∧ D' = D ∧ ∃ mn dd, ctx.meth = some mn ∧ mn ≠ "" ∧
      superDecl? D ctx.cls mn = some dd ∧ dd.params = [] ∧ τ = dd.ret := by
  simp only [infer] at h
  split at h
  · next mn hmn =>
    split at h
    · next hne =>
      split at h
      · next dd hrow =>
        split at h
        · next hemp =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨rfl, rfl, mn, dd, hmn, hne, hrow, List.isEmpty_iff.mp hemp, rfl⟩
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem infer_super_inv {D D' : Decls} {Γ Γ' : Env} {τ : Ty} {top : Bool} {ctx : FrameCtx}
    {arg : Expr} {args : List Expr}
    (h : infer D Γ (.super' (arg :: args) none) top ctx = some (τ, Γ', D')) :
    ∃ mn τs dd, ctx.meth = some mn ∧ mn ≠ "" ∧
      inferArgs D Γ (arg :: args) top ctx = some (τs, Γ', D') ∧
      superDecl? D' ctx.cls mn = some dd ∧ subTys τs dd.params = true ∧ τ = dd.ret := by
  simp only [infer] at h
  split at h
  · next mn hmn =>
    split at h
    · next hne =>
      split at h
      · next τs Γ₁ D₁ hargs =>
        split at h
        · next dd hrow =>
          split at h
          · next hsub =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact ⟨mn, τs, dd, hmn, hne, hargs, hrow, hsub, rfl⟩
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Inversion for bare `super` (L214). No argument list, so no `inferArgs` premise —
    the types come off the context. -/
theorem infer_zsuper_inv {D D' : Decls} {Γ Γ' : Env} {τ : Ty} {top : Bool} {ctx : FrameCtx}
    (h : infer D Γ (.zsuper none) top ctx = some (τ, Γ', D')) :
    Γ' = Γ ∧ D' = D ∧ ∃ mn ps dd, ctx.meth = some mn ∧ ctx.params = some ps ∧ mn ≠ "" ∧
      superDecl? D ctx.cls mn = some dd ∧ subTys ps dd.params = true ∧ τ = dd.ret := by
  simp only [infer] at h
  split at h
  · next mn ps hmn hpar =>
    split at h
    · next hne =>
      split at h
      · next dd hrow =>
        split at h
        · next hsub =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨rfl, rfl, mn, ps, dd, hmn, hpar, hne, hrow, hsub, rfl⟩
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Inversion for the `def` rule. -/
theorem infer_def_inv {D D' : Decls} {Γ : Env} {name : String} {params : List Param}
    {body : Expr} {τ : Ty} {Γ' : Env} {top : Bool} {ctx : FrameCtx}
    (h : infer D Γ (.def' name params body) top ctx = some (τ, Γ', D')) :
    τ = .sym ∧ Γ' = Γ ∧ params = [] ∧ declaresName D name = false
      ∧ name ≠ "method_added"
      ∧ ∃ τb Γb, infer D [] body false
          { ctx with selfCls := some ctx.cls, ret := none, meth := some name, params := some [], inLoop := none, inBlock := false }
          = some (τb, Γb, D)
      ∧ (D' = D ∨
          (D' = addRow D ctx.cls name { params := [], ret := τb } ∧
            top = false ∧ name ≠ "initialize" ∧
            reopenableClasses.contains ctx.cls = true ∧
            groundClassNames.contains ctx.cls = false ∧ defFree body = true ∧
            ctx.inBlock = false)) := by
  simp only [infer] at h
  split at h
  · next hc =>
    obtain ⟨hp, h1, h2⟩ := hc
    split at h
    · next τb Γb Db hb =>
      split at h
      · next hDb =>
        subst hDb
        split at h
        · next hrow =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨rfl, rfl, List.isEmpty_iff.mp hp, h1, h2, τb, Γb, hb,
            Or.inr ⟨rfl, hrow.1, hrow.2.1, hrow.2.2.1, hrow.2.2.2.1, hrow.2.2.2.2.1,
              hrow.2.2.2.2.2.2.2⟩⟩
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨rfl, rfl, List.isEmpty_iff.mp hp, h1, h2, τb, Γb, hb, Or.inl rfl⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Inversion for the **class-reopen** rule (L156). The three side conditions come
    back out as separate facts because the consecution case spends them in three
    different places: `top` against `BottomObj`, `sup = none` against `evalExpr`'s
    own match, and membership against `ClassOk`. -/
theorem infer_class_inv {D D' : Decls} {Γ : Env} {name : String} {sup : Option Expr}
    {body : Expr} {τ : Ty} {Γ' : Env} {top : Bool} {ctx : FrameCtx}
    (h : infer D Γ (.class' name sup body) top ctx = some (τ, Γ', D')) :
    top = true ∧ sup = none ∧ reopenableClasses.contains name = true ∧ Γ' = Γ ∧
      ∃ Γ'', infer D [] body false { cls := name } = some (τ, Γ'', D') := by
  simp only [infer] at h
  split at h
  · next hc =>
    obtain ⟨ht, hs, hm⟩ := hc
    split at h
    · next τb Γb Db hb =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨ht, Option.isNone_iff_eq_none.mp hs, hm, rfl, Γb, hb⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Inversion for the **zero-argument** send rule (L152). One `split` shallower than
    its unary sibling, because there is no argument to infer and therefore no
    parameter-type equality to check — the output environment is the receiver's. -/
theorem infer_send0_inv {D D' : Decls} {Γ : Env} {r : Expr} {mname : String} {τ : Ty}
    {Γ' : Env} {top : Bool} {ctx : FrameCtx}
    (h : infer D Γ (.send (some r) mname [] none) top ctx = some (τ, Γ', D')) :
    ∃ τr, infer D Γ r top ctx = some (τr, Γ', D') ∧ sigOf D' τr mname = some ([], τ) := by
  simp only [infer] at h
  split at h
  · next τr Γ₁ D₁ hr =>
    split at h
    · next τret hsg =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨τr, hr, hsg⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The argument traversal on a non-empty list answers a non-empty list of types. -/
theorem inferArgs_cons_ne {D D' : Decls} {Γ Γ' : Env} {e : Expr} {es : List Expr}
    {top : Bool} {ctx : FrameCtx} {τs : List Ty}
    (h : inferArgs D Γ (e :: es) top ctx = some (τs, Γ', D')) : τs ≠ [] := by
  simp only [inferArgs] at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; simp
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **L259: an arity-`n` block send names a block-taking row *with parameters*.**

    That pair of facts is exactly what `EntryOk` cannot grant: both resolving arms pin
    `blk = none` (`EntryOk.iter`), and the one arm that admits a block — `IterEntryOk` —
    pins the parameter list to `[]`. So the *rule* is real and the **table** is what
    refuses it, which is where the refusal belongs: a future `EntryOk` arm for a
    block-taking row with parameters turns this refutation back into work. -/
theorem infer_sendBlkN_decl {D D' : Decls} {Γ Γ' : Env} {recv arg blk : Expr}
    {extra : List Expr} {mname : String} {τ : Ty} {top : Bool} {ctx : FrameCtx}
    (h : infer D Γ (.send (some recv) mname (arg :: extra) (some blk)) top ctx
      = some (τ, Γ', D')) :
    ∃ τr d σp βret, declFor D τr mname = some d ∧ d.params ≠ [] ∧
      d.blk = some { params := [σp], ret := βret } := by
  cases blk
  case block ps ls body =>
    simp only [infer] at h
    cases hr : infer D Γ recv top ctx with
    | none => rw [hr] at h; exact absurd h (by simp)
    | some p =>
      obtain ⟨τr, Γ₁, D₁⟩ := p
      rw [hr] at h
      simp only [] at h
      cases ha : inferArgs D₁ Γ₁ (arg :: extra) top ctx with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some q =>
        obtain ⟨τs, Γ₂, D₂⟩ := q
        rw [ha] at h
        simp only [] at h
        cases hbs : blockSendA? D₂ τr mname ps ls with
        | none => rw [hbs] at h; exact absurd h (by simp)
        | some rr =>
          obtain ⟨x, σp, βret, dps, τret⟩ := rr
          rw [hbs] at h
          simp only [] at h
          cases hbody : infer D₂ ((x, σp) :: anyEnv Γ₂) body false (blockCtx ctx) with
          | none => rw [hbody] at h; exact absurd h (by simp)
          | some z =>
            obtain ⟨τb, Γb', D₃⟩ := z
            rw [hbody] at h
            simp only [] at h
            split at h
            · next hif =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨-, -, -⟩ := h
              obtain ⟨h1, h2, h3, hd21, hd1, h5, h6⟩ := hif
              subst hd21
              subst hd1
              obtain ⟨d, hd, hdps, -, hdb⟩ := blockSendA?_declFor hbs
              refine ⟨τr, d, σp, βret, hd, ?_, hdb⟩
              rw [hdps]
              intro hnil
              rw [hnil] at h1
              cases hts : τs with
              | nil => exact inferArgs_cons_ne ha hts
              | cons t ts => rw [hts] at h1; exact absurd h1 (by simp [subTys])
            · exact absurd h (by simp)
  all_goals exact absurd h (by simp [infer])

/-- **Inversion for the block-send rule** (L257). Four nested splits, and the last is
    the three-way conjunction the rule checks. -/
theorem infer_sendBlk_inv {D D' : Decls} {Γ Γ' : Env} {recv body : Expr}
    {mname : String} {ps : List Param} {ls : List String} {τ : Ty} {top : Bool}
    {ctx : FrameCtx}
    (h : infer D Γ (.send (some recv) mname [] (some (.block ps ls body))) top ctx
      = some (τ, Γ', D')) :
    ∃ τr x σp βret τb Γb',
      infer D Γ recv top ctx = some (τr, Γ', D') ∧
      blockSend? D' τr mname ps ls = some (x, σp, βret, τ) ∧
      infer D' ((x, σp) :: anyEnv Γ') body false (blockCtx ctx) = some (τb, Γb', D') ∧
      subTy τb βret = true ∧ subEnvB ((x, σp) :: anyEnv Γ') Γb' = true ∧
      ctx.inBlock = false := by
  simp only [infer] at h
  cases hr : infer D Γ recv top ctx with
  | none => rw [hr] at h; exact absurd h (by simp)
  | some p =>
    obtain ⟨τr, Γ₁, D₁⟩ := p
    rw [hr] at h
    simp only [] at h
    cases hbs : blockSend? D₁ τr mname ps ls with
    | none => rw [hbs] at h; exact absurd h (by simp)
    | some r =>
      obtain ⟨x, σp, βret, τret⟩ := r
      rw [hbs] at h
      simp only [] at h
      cases hbody : infer D₁ ((x, σp) :: anyEnv Γ₁) body false (blockCtx ctx) with
      | none => rw [hbody] at h; exact absurd h (by simp)
      | some q =>
        obtain ⟨τb, Γb', D₂⟩ := q
        rw [hbody] at h
        simp only [] at h
        split at h
        · next hif =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨hsb, rfl, hse, hib⟩ := hif
          exact ⟨τr, x, σp, βret, τb, Γb', rfl, hbs, hbody, hsb, hse, hib⟩
        · exact absurd h (by simp)

/-- Inversion for the send rule, **at any positive arity** (L175). Factored out of
    `step_ok` because the nested `split at` needs `next`-bound names that are
    unreadable inline. -/
theorem infer_send_inv {D D' : Decls} {Γ : Env} {r arg : Expr} {args : List Expr}
    {mname : String} {τ : Ty} {Γ' : Env} {top : Bool} {ctx : FrameCtx}
    (h : infer D Γ (.send (some r) mname (arg :: args) none) top ctx
      = some (τ, Γ', D')) :
    ∃ τr Γ₁ D₁ τs ps, infer D Γ r top ctx = some (τr, Γ₁, D₁) ∧
      inferArgs D₁ Γ₁ (arg :: args) top ctx = some (τs, Γ', D') ∧
      sigOf D' τr mname = some (ps, τ) ∧ subTys τs ps = true := by
  simp only [infer] at h
  split at h
  · next τr Γ₁ D₁ hr =>
    split at h
    · next τs Γ₂ D₂ ha =>
      split at h
      · next ps τret hsg =>
        split at h
        · next hτ =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨τr, Γ₁, D₁, τs, ps, hr, ha, hsg, hτ⟩
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)


/-- Inversion for the **written receiverless call at positive arity** (L171/L175).
    No receiver run: the receiver is the frame's `self`, supplied by the context, so
    the rule's three tests are the arguments, the signature at the table the last
    argument leaves, and the parameter match. -/
theorem infer_implicit_send1_inv {D D' : Decls} {Γ : Env} {arg : Expr}
    {args : List Expr} {mname : String} {τ : Ty} {Γ' : Env} {top : Bool}
    {ctx : FrameCtx}
    (h : infer D Γ (.send none mname (arg :: args) none) top ctx = some (τ, Γ', D')) :
    ∃ c τs ps, ctx.selfCls = some c ∧
      inferArgs D Γ (arg :: args) top ctx = some (τs, Γ', D') ∧
      sigOf D' (.cls c) mname = some (ps, τ) ∧ subTys τs ps = true := by
  simp only [infer] at h
  split at h
  · next c hsome =>
    split at h
    · next τs Γ₁ D₁ ha =>
      split at h
      · next ps τret hsg =>
        split at h
        · next hτ =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨c, τs, ps, hsome, ha, hsg, hτ⟩
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Inversion for `inferArgs` at a non-empty list: the head's type is the head of
    the answer, and the tail is inferred at the table and environment the head
    leaves. The shape both send consecution cases need, because each `argsK` step
    peels exactly one argument. -/
theorem inferArgs_cons_inv {D D' : Decls} {Γ Γ' : Env} {e : Expr} {rest : List Expr}
    {τs : List Ty} {top : Bool} {ctx : FrameCtx}
    (h : inferArgs D Γ (e :: rest) top ctx = some (τs, Γ', D')) :
    ∃ τe Γ₁ D₁ τrest, τs = τe :: τrest ∧
      infer D Γ e top ctx = some (τe, Γ₁, D₁) ∧
      inferArgs D₁ Γ₁ rest top ctx = some (τrest, Γ', D') := by
  simp only [inferArgs] at h
  split at h
  · next τe Γ₁ D₁ he =>
    split at h
    · next τrest Γ₂ D₂ hr =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨τe, Γ₁, D₁, τrest, rfl, he, hr⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- `ValuesTy` respects a snoc on both sides — the shape the argument loop needs:
    each `argsK` step moves one value from the unevaluated tail to the accumulated
    prefix, and the signature's parameter list is split at the same point. -/
theorem ValuesTy_snoc {h : Heap} : ∀ {vs : List Value} {τs : List Ty} {v : Value}
    {σ τ : Ty}, ValuesTy h vs τs → ValueTy h v σ → subTy σ τ = true →
      ValuesTy h (vs ++ [v]) (τs ++ [τ])
  | [], [], _, _, _, _, hv, hs => ⟨⟨_, hv, hs⟩, trivial⟩
  | _ :: _, _ :: _, _, _, _, hvs, hv, hs => ⟨hvs.1, ValuesTy_snoc hvs.2 hv hs⟩

/-- `continueArray` on a non-`splat` head pushes an `arrK` and evaluates it.
    `startArgs_plain`'s twin, and the reason `infer`'s `.array` arm needs no splat
    guard: the element's own accepting judgement refutes the splat arm. -/
theorem continueArray_plain {m : Machine} {acc : List Value} {e : Expr}
    {rest : List Expr} (hsplat : ∀ x, e ≠ .splat x) :
    continueArray m acc (e :: rest)
      = .next (withKont m (.eval e) (.arrK acc rest)) := by
  cases e <;> simp_all [continueArray]

/-- **An `Array`-typed value is a reference to an `.arr` payload** (L255) — `plainRecv`'s
    sixth clause (L230) read back out, factored from `spreadA_of_array` because the block
    send needs the same fact for a different consumer (`tryIterator`'s payload match). -/
theorem arrayPayload_of_valueTy {h : Heap} {v : Value} (hv : ValueTy h v (.cls "Array")) :
    ∃ o xs, v = .ref o ∧ (h.get o).payload = .arr xs ∧ o < h.objs.size := by
  obtain ⟨o, rfl⟩ : ∃ o, v = .ref o := by
    cases hsv : v with
    | ref o' => exact ⟨o', rfl⟩
    | _ => rw [hsv] at hv; simp_all [ValueTy, valueTy?, subTy]
  have hpl : plainRecv h o = true := valueTy_ref_plain hv
  have hcn : className h (h.get o).klass = "Array" := by
    rcases valueTy_ref_inv (by simp [subTy]) (by simp [subTy]) hv with ⟨-, hs⟩ | ⟨hc, hs⟩
    · have hq := (subTy_atomic (τ := Ty.cls "Array") (by simp) (by simp)).mp hs
      rw [plainRecv_classOf hpl] at hq
      simpa using hq
    · exact absurd hs (by simp [subTy])
  have hlt : o < h.objs.size := by
    unfold plainRecv at hpl; simp only [Bool.and_eq_true] at hpl
    exact of_decide_eq_true hpl.1.1.1.1.1
  have harr : ∃ xs, (h.get o).payload = .arr xs := by
    unfold plainRecv at hpl
    simp only [Bool.and_eq_true] at hpl
    have h6 := hpl.2
    rw [hcn] at h6
    simp only [beq_self_eq_true, if_true] at h6
    cases hp : (h.get o).payload with
    | arr xs => exact ⟨xs, rfl⟩
    | _ => rw [hp] at h6; exact absurd h6 (by simp)
  obtain ⟨xs, hp⟩ := harr
  exact ⟨o, xs, rfl, hp, hlt⟩


/-- **An `Array`-typed value spreads, and the machine does not move** (L230) — the whole
    soundness content of the splat rule, and the reason `plainRecv` gained a sixth clause.

    `spreadA` is total on an `.arr` payload (it hands back the elements) and answers
    `.error` — hence `.unsupported`, which `StepOk` refuses — on a `.str`, an `.int` or a
    `.hsh`. `valueTy?` reads the *class*, so nothing but `plainRecv`'s clause connects the
    two, and this lemma is where the connection is spent. -/
theorem spreadA_of_array {m : Machine} {v : Value}
    (hv : ValueTy m.heap v (.cls "Array")) :
    ∃ vs, Interp.spreadA m v = .ok (vs, m) := by
  -- The value is a reference: no immediate has a class type (`valueTy?`'s arms answer
  -- `.int`/`.bool`/… and `subTy` at a concrete type is an equality).
  obtain ⟨o, rfl⟩ : ∃ o, v = .ref o := by
    cases hsv : v with
    | ref o' => exact ⟨o', rfl⟩
    | _ => rw [hsv] at hv; simp_all [ValueTy, valueTy?, subTy]
  have hpl : plainRecv m.heap o = true := valueTy_ref_plain hv
  have hcn : className m.heap (m.heap.get o).klass = "Array" := by
    rcases valueTy_ref_inv (by simp [subTy]) (by simp [subTy]) hv with ⟨-, hs⟩ | ⟨hc, hs⟩
    · have hq := (subTy_atomic (τ := Ty.cls "Array") (by simp) (by simp)).mp hs
      rw [plainRecv_classOf hpl] at hq
      simpa using hq
    · exact absurd hs (by simp [subTy])
  -- And now the sixth clause, read back out.
  have harr : ∃ xs, (m.heap.get o).payload = .arr xs := by
    unfold plainRecv at hpl
    simp only [Bool.and_eq_true] at hpl
    have h6 := hpl.2
    rw [hcn] at h6
    simp only [beq_self_eq_true, if_true] at h6
    cases hp : (m.heap.get o).payload with
    | arr xs => exact ⟨xs, rfl⟩
    | _ => rw [hp] at h6; exact absurd h6 (by simp)
  obtain ⟨xs, hp⟩ := harr
  exact ⟨xs.toList, by simp [Interp.spreadA, Interp.spread, hp, Except.map]⟩

/-- **And the splat arm** (L230), which is one line of `continueArray` and needs no
    hypothesis: a `.splat (some o)` element evaluates `o` under an `arrSplatK`. -/
theorem continueArray_splat {m : Machine} {acc : List Value} {o : Expr}
    {rest : List Expr} :
    continueArray m acc (.splat (some o) :: rest)
      = .next (withKont m (.eval o) (.arrSplatK acc rest)) := by
  simp [continueArray]

/-! ### 2.2 `FramesOk` survives the fragment's frame-preserving updates

`ctl` and `kont` updates leave `frames` and `stack` alone, and `FramesOk` reads
nothing else — so it transports by `rfl` rather than by a congruence lemma. That
is the payoff of phrasing conformance over the array and the stack instead of
over the machine: P0a needed `FrameOk_congr` *and* `LocalsOk_congr`, and both are
now gone.
-/

/-! ### 2.3 Building `Inv` for the machines the fragment steps to -/

theorem inv_eval {F : Decls} {m : Machine} {c : FrameCtx} {Γ : Env}
    {Γs : List (FrameCtx × Env)} {Γk : Env} {e : Expr} {τ : Ty} {Γ' : Env} {F' : Decls}
    (hfs : FramesOk m.heap m.frames m.stack (Γ :: Γs.map Prod.snd)) (ht : DeclsOk F m.heap)
    (hsc : StackCtx m.heap m.frames m.stack (c :: Γs.map Prod.fst))
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : LitClsOk m.heap) (hcls : ClassOk m.heap)
    (hbot : BottomObj m.frames m.stack)
    (hks : framePopLabels m.kont = m.stack.dropLast)
    (hinf : infer F Γ e Γs.isEmpty c = some (τ, Γ', F'))
    (hk : KontOk F' m.heap ((c, Γk) :: Γs) τ m.kont)
    -- **L228's conjunct, defaulted.** It is last and `by assumption` because every caller
    -- has it under the same name: `Inv`'s own destructuring binds `hglob`, and a positional
    -- insertion into nine call sites of five lemmas is the kind of edit that silently
    -- reorders a `by simp` argument. The default is elaborated in the *caller's* context,
    -- so a caller that lacks the fact still fails here rather than being papered over.
    (hgl : GlobalsOk F m.heap m.globals := by assumption)
    (hsuE : SubEnv Γk Γ' := by first | exact SubEnv.refl _ | assumption)
    -- **L247's conjunct, and it is placed *last*** — after every other defaulted
    -- parameter — because a defaulted parameter still consumes a positional argument,
    -- and the callers of these five pass `hglob`/`hgv` positionally. L228's note says
    -- the same thing about `hgl`; this is the second time it has been load-bearing.
    (hclo : ClosuresOk m := by assumption) :
    Inv (withCtl m (.eval e)) :=
  ⟨hh, hsat, hstr, hcls, hbot, hks, hclo.ctl, F, c, Γ, Γs, ht, hfs, hsc, hgl,
   ⟨τ, τ, Γ', F', Γk, hinf, by simp, hsuE, hk⟩⟩

/-- **The same, at a *wider* continuation** (L193) — `inv_eval` with the identity
    `subTy` made a parameter. The one caller is the `ifK` delivery case, where the
    branch's own type sits below the join `inferIf` registered. -/
theorem inv_eval_sub {F : Decls} {m : Machine} {c : FrameCtx} {Γ : Env}
    {Γs : List (FrameCtx × Env)} {Γk : Env} {e : Expr} {τ τ' : Ty} {Γ' : Env} {F' : Decls}
    (hfs : FramesOk m.heap m.frames m.stack (Γ :: Γs.map Prod.snd)) (ht : DeclsOk F m.heap)
    (hsc : StackCtx m.heap m.frames m.stack (c :: Γs.map Prod.fst))
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : LitClsOk m.heap) (hcls : ClassOk m.heap)
    (hbot : BottomObj m.frames m.stack)
    (hks : framePopLabels m.kont = m.stack.dropLast)
    (hinf : infer F Γ e Γs.isEmpty c = some (τ, Γ', F'))
    (hsub : subTy τ τ' = true)
    (hk : KontOk F' m.heap ((c, Γk) :: Γs) τ' m.kont)
    -- **L228's conjunct, defaulted.** It is last and `by assumption` because every caller
    -- has it under the same name: `Inv`'s own destructuring binds `hglob`, and a positional
    -- insertion into nine call sites of five lemmas is the kind of edit that silently
    -- reorders a `by simp` argument. The default is elaborated in the *caller's* context,
    -- so a caller that lacks the fact still fails here rather than being papered over.
    (hgl : GlobalsOk F m.heap m.globals := by assumption)
    (hsuE : SubEnv Γk Γ' := by first | exact SubEnv.refl _ | assumption)
    -- **L247's conjunct, and it is placed *last*** — after every other defaulted
    -- parameter — because a defaulted parameter still consumes a positional argument,
    -- and the callers of these five pass `hglob`/`hgv` positionally. L228's note says
    -- the same thing about `hgl`; this is the second time it has been load-bearing.
    (hclo : ClosuresOk m := by assumption) :
    Inv (withCtl m (.eval e)) :=
  ⟨hh, hsat, hstr, hcls, hbot, hks, hclo.ctl, F, c, Γ, Γs, ht, hfs, hsc, hgl,
   ⟨τ, τ', Γ', F', Γk, hinf, hsub, hsuE, hk⟩⟩

theorem inv_value {F : Decls} {m : Machine} {c : FrameCtx} {Γ : Env}
    {Γs : List (FrameCtx × Env)} {Γk : Env} {v : Value} {τ : Ty}
    (hfs : FramesOk m.heap m.frames m.stack (Γ :: Γs.map Prod.snd)) (ht : DeclsOk F m.heap)
    (hsc : StackCtx m.heap m.frames m.stack (c :: Γs.map Prod.fst))
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : LitClsOk m.heap) (hcls : ClassOk m.heap)
    (hbot : BottomObj m.frames m.stack)
    (hks : framePopLabels m.kont = m.stack.dropLast)
    (hv : ValueTy m.heap v τ) (hk : KontOk F m.heap ((c, Γk) :: Γs) τ m.kont)
    -- **L228's conjunct, defaulted.** It is last and `by assumption` because every caller
    -- has it under the same name: `Inv`'s own destructuring binds `hglob`, and a positional
    -- insertion into nine call sites of five lemmas is the kind of edit that silently
    -- reorders a `by simp` argument. The default is elaborated in the *caller's* context,
    -- so a caller that lacks the fact still fails here rather than being papered over.
    (hgl : GlobalsOk F m.heap m.globals := by assumption)
    (hsuE : SubEnv Γk Γ := by first | exact SubEnv.refl _ | assumption)
    (hclo : ClosuresOk m := by assumption) :
    Inv (withCtl m (.value v)) :=
  ⟨hh, hsat, hstr, hcls, hbot, hks, hclo.ctl, F, c, Γ, Γs, ht, hfs, hsc, hgl, ⟨τ, Γk, hv, hsuE, hk⟩⟩

theorem inv_push {F : Decls} {m : Machine} {c : FrameCtx} {Γ : Env}
    {Γs : List (FrameCtx × Env)} {Γk : Env} {e : Expr} {τ : Ty} {Γ' : Env} {F' : Decls} {k : Kont}
    (hfs : FramesOk m.heap m.frames m.stack (Γ :: Γs.map Prod.snd)) (ht : DeclsOk F m.heap)
    (hsc : StackCtx m.heap m.frames m.stack (c :: Γs.map Prod.fst))
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : LitClsOk m.heap) (hcls : ClassOk m.heap)
    (hbot : BottomObj m.frames m.stack)
    (hks : framePopLabels (k :: m.kont) = m.stack.dropLast)
    (hinf : infer F Γ e Γs.isEmpty c = some (τ, Γ', F'))
    (hk : KontOk F' m.heap ((c, Γk) :: Γs) τ (k :: m.kont))
    -- **L228's conjunct, defaulted.** It is last and `by assumption` because every caller
    -- has it under the same name: `Inv`'s own destructuring binds `hglob`, and a positional
    -- insertion into nine call sites of five lemmas is the kind of edit that silently
    -- reorders a `by simp` argument. The default is elaborated in the *caller's* context,
    -- so a caller that lacks the fact still fails here rather than being papered over.
    (hgl : GlobalsOk F m.heap m.globals := by assumption)
    (hsuE : SubEnv Γk Γ' := by first | exact SubEnv.refl _ | assumption)
    -- **L247's conjunct, and it is placed *last*** — after every other defaulted
    -- parameter — because a defaulted parameter still consumes a positional argument,
    -- and the callers of these five pass `hglob`/`hgv` positionally. L228's note says
    -- the same thing about `hgl`; this is the second time it has been load-bearing.
    (hkc : KontClosure k = none := by simp [KontClosure])
    (hclo : ClosuresOk m := by assumption) :
    Inv (withKont m (.eval e) k) :=
  ⟨hh, hsat, hstr, hcls, hbot, hks, hclo.cons hkc, F, c, Γ, Γs, ht, hfs, hsc, hgl,
   ⟨τ, τ, Γ', F', Γk, hinf, by simp, hsuE, hk⟩⟩

/-- **`inv_push` at a wider continuation** (L193), the `inv_eval_sub` of the
    push form. Same one caller shape: a delivery case whose stored continuation was
    registered at a join. -/
theorem inv_push_sub {F : Decls} {m : Machine} {c : FrameCtx} {Γ : Env}
    {Γs : List (FrameCtx × Env)} {Γk : Env} {e : Expr} {τ τ' : Ty} {Γ' : Env} {F' : Decls} {k : Kont}
    (hfs : FramesOk m.heap m.frames m.stack (Γ :: Γs.map Prod.snd)) (ht : DeclsOk F m.heap)
    (hsc : StackCtx m.heap m.frames m.stack (c :: Γs.map Prod.fst))
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : LitClsOk m.heap) (hcls : ClassOk m.heap)
    (hbot : BottomObj m.frames m.stack)
    (hks : framePopLabels (k :: m.kont) = m.stack.dropLast)
    (hinf : infer F Γ e Γs.isEmpty c = some (τ, Γ', F'))
    (hsub : subTy τ τ' = true)
    (hk : KontOk F' m.heap ((c, Γk) :: Γs) τ' (k :: m.kont))
    -- **L228's conjunct, defaulted.** It is last and `by assumption` because every caller
    -- has it under the same name: `Inv`'s own destructuring binds `hglob`, and a positional
    -- insertion into nine call sites of five lemmas is the kind of edit that silently
    -- reorders a `by simp` argument. The default is elaborated in the *caller's* context,
    -- so a caller that lacks the fact still fails here rather than being papered over.
    (hgl : GlobalsOk F m.heap m.globals := by assumption)
    (hsuE : SubEnv Γk Γ' := by first | exact SubEnv.refl _ | assumption)
    -- **L247's conjunct, and it is placed *last*** — after every other defaulted
    -- parameter — because a defaulted parameter still consumes a positional argument,
    -- and the callers of these five pass `hglob`/`hgv` positionally. L228's note says
    -- the same thing about `hgl`; this is the second time it has been load-bearing.
    (hkc : KontClosure k = none := by simp [KontClosure])
    (hclo : ClosuresOk m := by assumption) :
    Inv (withKont m (.eval e) k) :=
  ⟨hh, hsat, hstr, hcls, hbot, hks, hclo.cons hkc, F, c, Γ, Γs, ht, hfs, hsc, hgl,
   ⟨τ, τ', Γ', F', Γk, hinf, hsub, hsuE, hk⟩⟩

/-- **A freshly allocated non-class object has the class type its `klass` names**
    (L151). This is the *value* half of a producer's obligation — the half
    `inv_grow_value` deliberately left to the rule (`hv`, read in the **new** heap) —
    and it is stated once here because every producer owes exactly it: a string
    literal today, `.array` and `C.new` later, each differing only in which `klass`
    and which payload it pushes.

    The four hypotheses are `plainRecv`'s four conjuncts at the fresh id, each
    discharged from the object literal or from the invariant:
    the bound is free (the id is the one being pushed), `hpl` is a computation on the
    payload, `hk`/`hn` are the heap facts — which for `String` is exactly what the
    `LitClsOk` conjunct carries.

    `hpl` is three refutations rather than `plainRecv`'s own `match` because a `match`
    written in a *statement* elaborates to a fresh matcher constant, which then will
    not `rw` against the one `plainRecv` was compiled with. Case-splitting the payload
    is the shape that composes; `entry_dispatch` discharges the same three shapes the
    same way. -/
theorem valueTy_alloc_fresh {h : Heap} {obj : Object} {n : String}
    (hpl : (∀ c, obj.payload ≠ .proc c) ∧ (∀ xs, obj.payload ≠ .hsh xs) ∧
           (∀ c, obj.payload ≠ .cls c))
    (he : obj.eigen = none)
    -- L191: `plainRecv` refuses a frozen object, and every literal producer
    -- allocates an unfrozen one (`allocStr`/`allocArr` leave the field at its
    -- default). A hypothesis rather than a derivation, because the lemma is stated
    -- at an abstract `obj`.
    (hfz : obj.frozen = false)
    -- L196: and no instance variables, for `PlainGrow`'s new clause — same shape and
    -- the same reason (`allocStr`/`allocArr` leave the field at its default).
    (hiv : obj.ivars = [])
    (hk : (h.classPayload? obj.klass).isSome)
    (hn : className h obj.klass = n)
    -- **L230: and if it is an `Array`, it holds one** — `plainRecv`'s sixth clause,
    -- stated at the *name* the producer already has. Free at both call sites: the array
    -- literal's payload *is* an `.arr`, and the string literal's name is `"String"`.
    (harr : n = "Array" → ∃ xs, obj.payload = .arr xs) :
    ValueTy ⟨h.objs.push obj⟩ (.ref h.objs.size) (.cls n) := by
  obtain ⟨hproc, hhsh, hnc⟩ := hpl
  have hg : PlainGrow h ⟨h.objs.push obj⟩ := plainGrow_alloc h obj hnc hiv
  -- The fresh id reads back as the object that was pushed; everything else is a
  -- rewrite through `PlainGrow`, which pins `classPayload?` at *every* id.
  have hget : (Heap.get ⟨h.objs.push obj⟩ h.objs.size) = obj := by
    simp [Heap.get, Array.getD_eq_getD_getElem?]
  have hlt : h.objs.size < (Heap.mk (h.objs.push obj)).objs.size := by simp
  have hplain : plainRecv ⟨h.objs.push obj⟩ h.objs.size = true := by
    unfold plainRecv
    rw [hget, he, hg.payload obj.klass]
    rw [hg.className_eq obj.klass, hn]
    cases hp : obj.payload
    case proc c => exact absurd hp (hproc c)
    case hsh xs => exact absurd hp (hhsh xs)
    case cls c => exact absurd hp (hnc c)
    -- The `.arr` payload satisfies the sixth clause outright; every other payload
    -- **refutes** `n = "Array"` through `harr`, which is the direction that makes the
    -- hypothesis free at the string producer.
    case arr xs => simp [hlt, hk, hfz]
    all_goals
      (have hna : ¬ n = "Array" := by
         intro hq
         obtain ⟨ys, hys⟩ := harr hq
         rw [hp] at hys
         exact absurd hys (by simp)
       simp [hlt, hk, hfz, hna])
  refine ValueTy.exact ?_
  simp only [valueTy?, hplain, if_true]
  rw [plainRecv_classOf hplain, hget, hg.className_eq obj.klass, hn]

/-- **The invariant survives a step that allocates a plain object** (L149) — which
    is the producer's consecution case with the rule removed, and therefore the
    statement that says how much of the producer is *not* about the producer.

    Every conjunct is discharged by a lemma of its own rung, and it is worth reading
    the list as a summary of what items 2–5 of the bill bought:

    | conjunct | discharged by | rung |
    |---|---|---|
    | `DeclsOk`   | `DeclsOk_grow`          | L147 (class-indexed resolution) |
    | `NoHook`    | `NoHook_grow`           | L149 |
    | `Saturated` | `Saturated_grow`        | L148 |
    | `FramesOk`  | `FramesOk.heap_congr` ∘ `typeAgree_of_plainGrow` | L143/L145 |
    | `CtlOk`     | `KontOk.heap_congr` ∘ the same | L143/L145 |

    What the *rule* still owes is only what a rule can owe: that the step really
    lands in a machine related to this one by `PlainGrow` with frames, stack and
    `kont` untouched, and that the value it produces has the type the rule assigns.
    `plainGrow_alloc` supplies the first for a non-class `Heap.alloc`.

    The produced value's type is read in the **new** heap (`hv`), which is the whole
    reason the transport had to be relativized rather than proved unrelativized
    (L143): the fresh object has no type in the old one. -/
theorem inv_grow_value {F : Decls} {m m' : Machine} {c : FrameCtx} {Γ : Env}
    {Γs : List (FrameCtx × Env)} {Γk : Env} {v : Value} {τ : Ty}
    (hfs : FramesOk m.heap m.frames m.stack (Γ :: Γs.map Prod.snd)) (ht : DeclsOk F m.heap)
    (hsc : StackCtx m.heap m.frames m.stack (c :: Γs.map Prod.fst))
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : LitClsOk m.heap) (hcls : ClassOk m.heap)
    (hbot : BottomObj m.frames m.stack)
    (hks : framePopLabels m.kont = m.stack.dropLast)
    (hg : PlainGrow m.heap m'.heap)
    (hfr : m'.frames = m.frames) (hst : m'.stack = m.stack) (hko : m'.kont = m.kont)
    (hv : ValueTy m'.heap v τ) (hk : KontOk F m.heap ((c, Γk) :: Γs) τ m.kont)
    -- **L228's conjunct, defaulted.** It is last and `by assumption` because every caller
    -- has it under the same name: `Inv`'s own destructuring binds `hglob`, and a positional
    -- insertion into nine call sites of five lemmas is the kind of edit that silently
    -- reorders a `by simp` argument. The default is elaborated in the *caller's* context,
    -- so a caller that lacks the fact still fails here rather than being papered over.
    (hgl : GlobalsOk F m.heap m.globals := by assumption)
    -- And that the allocation left the globals alone, which is `rfl` at every caller.
    (hgv : m'.globals = m.globals := by rfl)
    (hsuE : SubEnv Γk Γ := by first | exact SubEnv.refl _ | assumption)
    (hclo : ClosuresOk m := by assumption) :
    Inv (withCtl m' (.value v)) := by
  have hag : TypeAgree m.heap m'.heap := typeAgree_of_plainGrow hg hsat
  refine ⟨NoHook_grow hg hsat hh,
    Saturated_grow hg.shapeAgree hg.size hsat, LitClsOk_grow hg hstr,
    ClassOk_grow hg hsat hcls,
    show BottomObj m'.frames m'.stack by rw [hfr, hst]; exact hbot,
    show framePopLabels m'.kont = m'.stack.dropLast by rw [hko, hst]; exact hks,
    -- L247: an allocating step moves neither the kont nor the frames.
    show ClosuresOk (withCtl m' (.value v)) from
      hclo.transport
        (by
          intro κ hmem cl hcl
          exact ⟨κ, by rw [show (withCtl m' (.value v)).kont = m.kont from by
            simp [withCtl, hko]] at hmem; exact hmem, hcl⟩)
        (by rw [show (withCtl m' (.value v)).frames = m.frames from by
              simp [withCtl, hfr]]; exact Nat.le_refl _)
        (by intro p _; rw [show (withCtl m' (.value v)).frames = m.frames from by
              simp [withCtl, hfr]]; exact FrameShape.rfl' _)
        (by
          intro o ho
          show (m'.heap.classPayload? o).isSome = true
          rw [hag.2.2.1 o (classPayload?_isSome_lt ho)]; exact ho),
    F, c, Γ, Γs, DeclsOk_grow hg hsat ht, ?_, ?_, ?_, ?_⟩
  · show FramesOk m'.heap m'.frames m'.stack (Γ :: Γs.map Prod.snd)
    rw [hfr, hst]
    exact FramesOk.heap_congr hag hfs
  · show StackCtx m'.heap m'.frames m'.stack (c :: Γs.map Prod.fst)
    rw [hfr, hst]
    exact StackCtx.heap_congr hag hsc
  · show GlobalsOk F m'.heap m'.globals
    rw [hgv]
    exact GlobalsOk.congr hag hgl
  · show ∃ σ Γk, ValueTy m'.heap v σ ∧ SubEnv Γk Γ ∧
        KontOk F m'.heap ((c, Γk) :: Γs) σ m'.kont
    exact ⟨τ, _, hv, hsuE, by rw [hko]; exact KontOk.heap_congr hag hk⟩
end Static
end Proof
end RubyCore
