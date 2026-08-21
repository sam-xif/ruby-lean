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
      KontOk D h Γs τ []
  /-- `seqK []` yields the in-flight value unchanged (`Interp.lean:1957`). -/
  | seqNil {D h c Γ Γs τ τw k} :
      subTy τ τw = true → KontOk D h ((c, Γ) :: Γs) τw k →
      KontOk D h ((c, Γ) :: Γs) τ (.seqK [] :: k)
  /-- `seqK (e :: es)` discards the in-flight value and runs the rest.

      **`Γs.isEmpty` is the toplevel mode** (L155), and this is the only
      constructor that has to name it: `seqK` is the one kont that stores
      *unevaluated statements*, so it is the one whose contents may be a `class`.
      The mode is read off the environment stack rather than carried as an index
      because `frameK` — the constructor at which an activation's environment goes
      out of scope — is already exactly where the definee changes. -/
  | seqCons {D D' h c Γ Γs τ e es τ' τw Γ' k} :
      inferSeq D Γ (e :: es) Γs.isEmpty c = some (τ', Γ', D') →
      subTy τ' τw = true →
      KontOk D' h ((c, Γ') :: Γs) τw k →
      KontOk D h ((c, Γ) :: Γs) τ (.seqK (e :: es) :: k)
  /-- Assignment binds `x` at the in-flight type and re-yields the value. -/
  | asgn {D h c Γ Γs τ τw x k} :
      subTy τ τw = true →
      KontOk D h ((c, envSet Γ x τ) :: Γs) τw k →
      KontOk D h ((c, Γ) :: Γs) τ (.asgnK .lvar x :: k)
  /-- **`@x = e`, with the value in flight** (L191). One premise beyond the tail, and
      it is the *frame context's* rather than the heap's: `selfCls` being inhabited is
      what the consecution case turns — through `StackCtx` and `plainRecv` — into
      "the write does not raise `FrozenError`". No binding moves, so the tail is
      typed in the same environment. -/
  | asgnIvar {D h c Γ Γs τ τw x k} :
      c.selfCls.isSome = true → subTy τ τw = true →
      -- **L196: the write conforms to whatever the table declares.** Carried on the
      -- continuation rather than re-derived at the delivery, because the delivery is
      -- where `DeclsOk`'s ivar half has to be re-established and this is the only
      -- fact that can do it.
      (∀ cn σ, c.selfCls = some cn → ivarTy? D cn x = some σ → subTy τ σ = true) →
      KontOk D h ((c, Γ) :: Γs) τw k →
      KontOk D h ((c, Γ) :: Γs) τ (.asgnK .ivar x :: k)
  /-- The in-flight value is the condition; either branch may run next, so the
      join must be the one `inferIf` computed. -/
  | ifK {D D' h c Γ Γs τ t els τ' τw Γ' k} :
      inferIf D Γ t els Γs.isEmpty c = some (τ', Γ', D') →
      subTy τ' τw = true →
      KontOk D' h ((c, Γ') :: Γs) τw k →
      KontOk D h ((c, Γ) :: Γs) τ (.ifK t els :: k)
  | whileCond {D h ctx Γ Γs τ τw c body k} :
      LoopOk D Γ c body Γs.isEmpty ctx → subTy .nilT τw = true →
      KontOk D h ((ctx, Γ) :: Γs) τw k →
      KontOk D h ((ctx, Γ) :: Γs) τ (.whileCondK c body :: k)
  | whileBody {D h ctx Γ Γs τ τw c body k} :
      LoopOk D Γ c body Γs.isEmpty ctx → subTy .nilT τw = true →
      KontOk D h ((ctx, Γ) :: Γs) τw k →
      KontOk D h ((ctx, Γ) :: Γs) τ (.whileBodyK c body :: k)
  /-- The in-flight value is the **receiver** of a binary builtin send; the
      argument expression runs next.

      **The site is a parameter** (L172), as `argsK`'s is (L171). `evalExpr` picks
      it syntactically — `.selfRecv` for a literal `self` receiver and `.explicit`
      for everything else — and the difference is *permissive*: `visError?` raises
      only at `.explicit`, while `ResolvesAt`/`ResolvesUser` demand `.pub`
      regardless. So a public method dispatches identically at both, the dispatch
      lemmas have been site-polymorphic since L164, and `infer`'s `isSelf` guard —
      which existed only to keep this constructor's `.explicit` true — is gone. -/
  | recvK {D D₂ h c Γ Γs τ mname arg args τs ps τret τw Γ₂ k} {site : SendSite} :
      inferArgs D Γ (arg :: args) Γs.isEmpty c = some (τs, Γ₂, D₂) →
      sigOf D₂ τ mname = some (ps, τret) →
      subTys τs ps = true →
      subTy τret τw = true →
      KontOk D₂ h ((c, Γ₂) :: Γs) τw k →
      KontOk D h ((c, Γ) :: Γs) τ (.recvK mname (arg :: args) .none site :: k)
  /-- **A zero-argument send** (L152), and it is a separate constructor rather than
      `recvK` with an empty list because the two describe *different numbers of
      steps*. With an argument, `applyKont` pushes an `argsK` and the dispatch is a
      step away; with none, `startArgs … [] []` is `finishSend`, so the send completes
      **in this step** and the continuation `k` must already be typed at the return
      type. There is no `argsK` in the chain at all, and therefore no `ValueTy` stored
      in the kont — which is why this constructor, unlike `argsK`, does not read the
      heap. -/
  | recvK0 {D h c Γ Γs τ mname τret τw k} {site : SendSite} :
      sigOf D τ mname = some ([], τret) →
      subTy τret τw = true →
      KontOk D h ((c, Γ) :: Γs) τw k →
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
  | argsK {D D' h c Γ Γs τ mname recv τr psacc τp τrest psrest τret τw acc rest Γ' k}
      {site : SendSite} :
      ValueTy h recv τr →
      ValuesTy h acc psacc →
      subTy τ τp = true →
      inferArgs D Γ rest Γs.isEmpty c = some (τrest, Γ', D') →
      subTys τrest psrest = true →
      sigOf D' τr mname = some (psacc ++ τp :: psrest, τret) →
      subTy τret τw = true →
      KontOk D' h ((c, Γ') :: Γs) τw k →
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
  | superArgsK {D D' h c Γ Γs τ mname psacc τp τrest psrest τret τw acc rest Γ' k blk dd} :
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
      KontOk D' h ((c, Γ') :: Γs) τw k →
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
  | arrK {D D' h c Γ Γs τ τ' τw acc rest Γ' k} :
      inferSeq D Γ rest Γs.isEmpty c = some (τ', Γ', D') →
      subTy (.cls "Array") τw = true →
      KontOk D' h ((c, Γ') :: Γs) τw k →
      KontOk D h ((c, Γ) :: Γs) τ (.arrK acc rest :: k)
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
      KontOk D h (cΓ' :: Γs) τ k → KontOk D h (cΓ :: cΓ' :: Γs) τ (.frameK fid :: k)
  /-- **`return e`, with the value in flight** (L200). Three premises, each spent in a
      different place: `c.ret = some σ` is what the target is read through, `subTy τ σ`
      is the rule's own conformance check, and the tail's `KontOk` is what
      `KontOk.retOk` turns into the `RetOk` the unwinding consumes.

      It carries a **`KontOk`** and not a `RetOk`, and that is not an accident: `RetOk`
      is defined *over* `KontOk` derivations, so a `RetOk` premise here would make the
      two mutually inductive. Deriving it at the delivery costs one lemma application. -/
  | retValK {D h c Γ Γs τ τ' σ k} :
      c.ret = some σ → subTy τ σ = true →
      KontOk D h ((c, Γ) :: Γs) τ' k →
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
  | cpathK {D h c Γ Γs τ τw cname n σ k} :
      subTy τ (.clsOf cname) = true → scopedConstTy? D cname n = some σ →
      subTy σ τw = true →
      KontOk D h ((c, Γ) :: Γs) τw k →
      KontOk D h ((c, Γ) :: Γs) τ (.cpathK n :: k)

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
  | .jumpValK _ => True
  -- L205: `unwind`'s catch-all, like the nine above — a `.cpathK` on the stack has no
  -- opinion about a jump, so a `.retJ` passes straight through it.
  | .cpathK _ => True
  | _ => False

/-- The label of the innermost activation's `frameK`. With L199's clause this is the
    frame stack's head, which is what `doReturn` targets. -/
def firstFrameK : List Kont → Option FrameId
  | [] => none
  | .frameK fid :: _ => some fid
  | _ :: k => firstFrameK k

/-- The first label of `frameKLabels` *is* `firstFrameK` — the bridge between L199's
    list-shaped clause and the single id `unwind` compares against. -/
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
      | nil hr => exact absurd (hr (c, Γ) Γs rfl) (by rw [hσ]; simp)
  | κ :: k, D, h, c, Γ, Γs, τ, hk, hne, σ, hσ => by
      have htop : Γs.isEmpty = false := by simpa using hne
      cases hk with
      | seqNil hw hk' => exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      | seqCons hs hw hk' =>
          have hq : _ = D := inferSeq_table_ret (ctx := c) (by rw [hσ]; simp) htop hs
          subst hq
          exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      | asgn hw hk' => exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      | asgnIvar hsc hw hcf hk' => exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      | ifK hi hw hk' =>
          have hq : _ = D := inferIf_table_ret (ctx := c) (by rw [hσ]; simp) htop hi
          subst hq
          exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      | whileCond hl hw hk' => exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      | whileBody hl hw hk' => exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      | recvK ha hsg hsub hw hk' =>
          have hq : _ = D := inferArgs_table_ret (ctx := c) (by rw [hσ]; simp) htop ha
          subst hq
          exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      | recvK0 hsg hw hk' => exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      | argsK hv hva hst hia hsr hsg hw hk' =>
          have hq : _ = D := inferArgs_table_ret (ctx := c) (by rw [hσ]; simp) htop hia
          subst hq
          exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      | superArgsK hva hst hia hsr hmt hmn hrow hps hrt hw hk' =>
          have hq : _ = D := inferArgs_table_ret (ctx := c) (by rw [hσ]; simp) htop hia
          subst hq
          exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      | arrK hs hw hk' =>
          have hq : _ = D := inferSeq_table_ret (ctx := c) (by rw [hσ]; simp) htop hs
          subst hq
          exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      | retValK hr hs hk' => exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      -- L205: the table is untouched (the arm *reads* `scopedConsts`), so this is the
      -- plain transparent case — no `_table_ret` composition needed.
      | cpathK hb hsc hw hk' => exact RetOk.skip trivial (KontOk.retOk hk' hne σ hσ)
      | frameK hrt hk' => exact RetOk.here (hrt σ hσ) hk'

@[simp] theorem frameKLabels_transparent {κ : Kont} {k : List Kont} (h : RetTransparent κ) :
    frameKLabels (κ :: k) = frameKLabels k := by
  cases κ <;> simp_all [RetTransparent, frameKLabels]

@[simp] theorem firstFrameK_transparent {κ : Kont} {k : List Kont} (h : RetTransparent κ) :
    firstFrameK (κ :: k) = firstFrameK k := by
  cases κ <;> simp_all [RetTransparent, firstFrameK]

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
      | seqNil hw hk' => exact .skip trivial (KontOk.raiseOk hk')
      | seqCons hs hw hk' => exact .skip trivial (KontOk.raiseOk hk')
      | asgn hw hk' => exact .skip trivial (KontOk.raiseOk hk')
      | asgnIvar hsc hw hcf hk' => exact .skip trivial (KontOk.raiseOk hk')
      | ifK hi hw hk' => exact .skip trivial (KontOk.raiseOk hk')
      | whileCond hl hw hk' => exact .skip trivial (KontOk.raiseOk hk')
      | whileBody hl hw hk' => exact .skip trivial (KontOk.raiseOk hk')
      | recvK ha hsg hsub hw hk' => exact .skip trivial (KontOk.raiseOk hk')
      | recvK0 hsg hw hk' => exact .skip trivial (KontOk.raiseOk hk')
      | argsK hv hva hst hia hsr hsg hw hk' => exact .skip trivial (KontOk.raiseOk hk')
      | superArgsK hva hst hia hsr hmt hmn hrow hps hrt hw hk' =>
          exact .skip trivial (KontOk.raiseOk hk')
      | arrK hs hw hk' => exact .skip trivial (KontOk.raiseOk hk')
      | cpathK hb hsc hw hk' => exact .skip trivial (KontOk.raiseOk hk')
      | retValK hr hs hk' => exact .skip trivial (KontOk.raiseOk hk')
      | frameK hrt hk' => exact .pop (KontOk.raiseOk hk')

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
    ∃ τ τ' Γ' D', infer D Γ e Γs.isEmpty c = some (τ, Γ', D') ∧ subTy τ τ' = true ∧
      KontOk D' m.heap ((c, Γ') :: Γs) τ' m.kont
  | .value v => ∃ τ, ValueTy m.heap v τ ∧ KontOk D m.heap ((c, Γ) :: Γs) τ m.kont
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
  -- The other jumps stay excluded: `break`/`next`/`retry`/`redo`/`throw` are not in the
  -- fragment, so no step can produce one.
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
  | nil hr => intro _; exact .nil hr
  | seqNil hw _ ih => intro ha; exact .seqNil hw (ih ha)
  | seqCons hs hw _ ih => intro ha; exact .seqCons hs hw (ih ha)
  | asgn hw _ ih => intro ha; exact .asgn hw (ih ha)
  | asgnIvar hsc hw hcf _ ih => intro ha; exact .asgnIvar hsc hw hcf (ih ha)
  | ifK hi hw _ ih => intro ha; exact .ifK hi hw (ih ha)
  | whileCond hl hw _ ih => intro ha; exact .whileCond hl hw (ih ha)
  | whileBody hl hw _ ih => intro ha; exact .whileBody hl hw (ih ha)
  | recvK hsg ha' hsub hw _ ih => intro ha; exact .recvK hsg ha' hsub hw (ih ha)
  | recvK0 hsg hw _ ih => intro ha; exact .recvK0 hsg hw (ih ha)
  | cpathK hb hsc hw _ ih => intro ha; exact .cpathK hb hsc hw (ih ha)
  | superArgsK hva hst hia hsr hmt hmn hrow hps hrt hw _ ih =>
      intro ha
      exact .superArgsK (ValuesTy.congr ha hva) hst hia hsr hmt hmn hrow hps hrt hw (ih ha)
  | argsK hv hva hst hia hsr hsg hw _ ih =>
      intro ha
      exact .argsK (ValueTy.congr ha hv) (ValuesTy.congr ha hva) hst hia hsr hsg hw (ih ha)
  | arrK hs hw _ ih => intro ha; exact .arrK hs hw (ih ha)
  | frameK hr _ ih => intro ha; exact .frameK hr (ih ha)
  | retValK hr hs _ ih => intro ha; exact .retValK hr hs (ih ha)

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
    frameKLabels m.kont = m.stack.dropLast ∧
    ∃ (F : Decls) (c : FrameCtx) (Γ : Env) (Γs : List (FrameCtx × Env)), DeclsOk F m.heap ∧
      FramesOk m.heap m.frames m.stack (Γ :: Γs.map Prod.snd) ∧
      StackCtx m.heap m.frames m.stack (c :: Γs.map Prod.fst) ∧
      CtlOk F c Γ Γs m

/-! ### Inversions used by the send cases -/

/-- **A signature exists only at a type dispatch can start from** (L193). `sigOf`
    reads `declFor`, which reads `tyClassNames`, which is `[]` at `.any` and at every
    nilable — so the existence of a row *is* the side condition `entry_dispatch` and
    `valueTy_tyClass` now ask for, and no rule has to carry it. That is the whole
    reason the two arms were given `[]` rather than a name. -/
theorem sigOf_atomic {D : Decls} {τr : Ty} {mname : String} {ps : List Ty} {τret : Ty}
    (h : sigOf D τr mname = some (ps, τret)) :
    τr ≠ .any ∧ ∀ τ', τr ≠ .nilable τ' := by
  cases τr <;>
    simp_all [sigOf, declFor, tyClassNames]

/-- The signature in the shape `EntryOk` reads it. Trivial, and it exists because
    `sigOf` is `declFor` composed with a projection while `DeclsOk` is stated over
    `declFor` — so the `argsK` case has to move between the two.

    **Generalized from `[τp]` to any `params` in L152**, because the zero-argument
    case needs it at `[]` and the two would otherwise be the same proof twice. -/
theorem sigOf_declFor {D : Decls} {τr : Ty} {mname : String} {params : List Ty}
    {τret : Ty} (h : sigOf D τr mname = some (params, τret)) :
    declFor D τr mname = some { params := params, ret := τret } := by
  unfold sigOf at h
  cases hd : declFor D τr mname with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some d =>
    obtain ⟨ps, r⟩ := d
    rw [hd] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

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
          { ctx with selfCls := some ctx.cls, ret := none, meth := some name, params := some [] }
          = some (τb, Γb, D)
      ∧ (D' = D ∨
          (D' = addRow D ctx.cls name { params := [], ret := τb } ∧
            top = false ∧ name ≠ "initialize" ∧
            reopenableClasses.contains ctx.cls = true ∧
            groundClassNames.contains ctx.cls = false ∧ defFree body = true)) := by
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
            Or.inr ⟨rfl, hrow.1, hrow.2.1, hrow.2.2.1, hrow.2.2.2.1, hrow.2.2.2.2.1⟩⟩
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

/-! ### 2.2 `FramesOk` survives the fragment's frame-preserving updates

`ctl` and `kont` updates leave `frames` and `stack` alone, and `FramesOk` reads
nothing else — so it transports by `rfl` rather than by a congruence lemma. That
is the payoff of phrasing conformance over the array and the stack instead of
over the machine: P0a needed `FrameOk_congr` *and* `LocalsOk_congr`, and both are
now gone.
-/

/-! ### 2.3 Building `Inv` for the machines the fragment steps to -/

theorem inv_eval {F : Decls} {m : Machine} {c : FrameCtx} {Γ : Env}
    {Γs : List (FrameCtx × Env)} {e : Expr} {τ : Ty} {Γ' : Env} {F' : Decls}
    (hfs : FramesOk m.heap m.frames m.stack (Γ :: Γs.map Prod.snd)) (ht : DeclsOk F m.heap)
    (hsc : StackCtx m.heap m.frames m.stack (c :: Γs.map Prod.fst))
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : LitClsOk m.heap) (hcls : ClassOk m.heap)
    (hbot : BottomObj m.frames m.stack)
    (hks : frameKLabels m.kont = m.stack.dropLast)
    (hinf : infer F Γ e Γs.isEmpty c = some (τ, Γ', F'))
    (hk : KontOk F' m.heap ((c, Γ') :: Γs) τ m.kont) :
    Inv (withCtl m (.eval e)) :=
  ⟨hh, hsat, hstr, hcls, hbot, hks, F, c, Γ, Γs, ht, hfs, hsc,
   ⟨τ, τ, Γ', F', hinf, by simp, hk⟩⟩

/-- **The same, at a *wider* continuation** (L193) — `inv_eval` with the identity
    `subTy` made a parameter. The one caller is the `ifK` delivery case, where the
    branch's own type sits below the join `inferIf` registered. -/
theorem inv_eval_sub {F : Decls} {m : Machine} {c : FrameCtx} {Γ : Env}
    {Γs : List (FrameCtx × Env)} {e : Expr} {τ τ' : Ty} {Γ' : Env} {F' : Decls}
    (hfs : FramesOk m.heap m.frames m.stack (Γ :: Γs.map Prod.snd)) (ht : DeclsOk F m.heap)
    (hsc : StackCtx m.heap m.frames m.stack (c :: Γs.map Prod.fst))
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : LitClsOk m.heap) (hcls : ClassOk m.heap)
    (hbot : BottomObj m.frames m.stack)
    (hks : frameKLabels m.kont = m.stack.dropLast)
    (hinf : infer F Γ e Γs.isEmpty c = some (τ, Γ', F'))
    (hsub : subTy τ τ' = true)
    (hk : KontOk F' m.heap ((c, Γ') :: Γs) τ' m.kont) :
    Inv (withCtl m (.eval e)) :=
  ⟨hh, hsat, hstr, hcls, hbot, hks, F, c, Γ, Γs, ht, hfs, hsc,
   ⟨τ, τ', Γ', F', hinf, hsub, hk⟩⟩

theorem inv_value {F : Decls} {m : Machine} {c : FrameCtx} {Γ : Env}
    {Γs : List (FrameCtx × Env)} {v : Value} {τ : Ty}
    (hfs : FramesOk m.heap m.frames m.stack (Γ :: Γs.map Prod.snd)) (ht : DeclsOk F m.heap)
    (hsc : StackCtx m.heap m.frames m.stack (c :: Γs.map Prod.fst))
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : LitClsOk m.heap) (hcls : ClassOk m.heap)
    (hbot : BottomObj m.frames m.stack)
    (hks : frameKLabels m.kont = m.stack.dropLast)
    (hv : ValueTy m.heap v τ) (hk : KontOk F m.heap ((c, Γ) :: Γs) τ m.kont) :
    Inv (withCtl m (.value v)) :=
  ⟨hh, hsat, hstr, hcls, hbot, hks, F, c, Γ, Γs, ht, hfs, hsc, ⟨τ, hv, hk⟩⟩

theorem inv_push {F : Decls} {m : Machine} {c : FrameCtx} {Γ : Env}
    {Γs : List (FrameCtx × Env)} {e : Expr} {τ : Ty} {Γ' : Env} {F' : Decls} {k : Kont}
    (hfs : FramesOk m.heap m.frames m.stack (Γ :: Γs.map Prod.snd)) (ht : DeclsOk F m.heap)
    (hsc : StackCtx m.heap m.frames m.stack (c :: Γs.map Prod.fst))
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : LitClsOk m.heap) (hcls : ClassOk m.heap)
    (hbot : BottomObj m.frames m.stack)
    (hks : frameKLabels (k :: m.kont) = m.stack.dropLast)
    (hinf : infer F Γ e Γs.isEmpty c = some (τ, Γ', F'))
    (hk : KontOk F' m.heap ((c, Γ') :: Γs) τ (k :: m.kont)) :
    Inv (withKont m (.eval e) k) :=
  ⟨hh, hsat, hstr, hcls, hbot, hks, F, c, Γ, Γs, ht, hfs, hsc,
   ⟨τ, τ, Γ', F', hinf, by simp, hk⟩⟩

/-- **`inv_push` at a wider continuation** (L193), the `inv_eval_sub` of the
    push form. Same one caller shape: a delivery case whose stored continuation was
    registered at a join. -/
theorem inv_push_sub {F : Decls} {m : Machine} {c : FrameCtx} {Γ : Env}
    {Γs : List (FrameCtx × Env)} {e : Expr} {τ τ' : Ty} {Γ' : Env} {F' : Decls} {k : Kont}
    (hfs : FramesOk m.heap m.frames m.stack (Γ :: Γs.map Prod.snd)) (ht : DeclsOk F m.heap)
    (hsc : StackCtx m.heap m.frames m.stack (c :: Γs.map Prod.fst))
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : LitClsOk m.heap) (hcls : ClassOk m.heap)
    (hbot : BottomObj m.frames m.stack)
    (hks : frameKLabels (k :: m.kont) = m.stack.dropLast)
    (hinf : infer F Γ e Γs.isEmpty c = some (τ, Γ', F'))
    (hsub : subTy τ τ' = true)
    (hk : KontOk F' m.heap ((c, Γ') :: Γs) τ' (k :: m.kont)) :
    Inv (withKont m (.eval e) k) :=
  ⟨hh, hsat, hstr, hcls, hbot, hks, F, c, Γ, Γs, ht, hfs, hsc,
   ⟨τ, τ', Γ', F', hinf, hsub, hk⟩⟩

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
    (hn : className h obj.klass = n) :
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
    cases hp : obj.payload
    case proc c => exact absurd hp (hproc c)
    case hsh xs => exact absurd hp (hhsh xs)
    case cls c => exact absurd hp (hnc c)
    all_goals simp [hlt, hk, hfz]
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
    {Γs : List (FrameCtx × Env)} {v : Value} {τ : Ty}
    (hfs : FramesOk m.heap m.frames m.stack (Γ :: Γs.map Prod.snd)) (ht : DeclsOk F m.heap)
    (hsc : StackCtx m.heap m.frames m.stack (c :: Γs.map Prod.fst))
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : LitClsOk m.heap) (hcls : ClassOk m.heap)
    (hbot : BottomObj m.frames m.stack)
    (hks : frameKLabels m.kont = m.stack.dropLast)
    (hg : PlainGrow m.heap m'.heap)
    (hfr : m'.frames = m.frames) (hst : m'.stack = m.stack) (hko : m'.kont = m.kont)
    (hv : ValueTy m'.heap v τ) (hk : KontOk F m.heap ((c, Γ) :: Γs) τ m.kont) :
    Inv (withCtl m' (.value v)) := by
  have hag : TypeAgree m.heap m'.heap := typeAgree_of_plainGrow hg hsat
  refine ⟨NoHook_grow hg hsat hh,
    Saturated_grow hg.shapeAgree hg.size hsat, LitClsOk_grow hg hstr,
    ClassOk_grow hg hsat hcls,
    show BottomObj m'.frames m'.stack by rw [hfr, hst]; exact hbot,
    show frameKLabels m'.kont = m'.stack.dropLast by rw [hko, hst]; exact hks,
    F, c, Γ, Γs, DeclsOk_grow hg hsat ht, ?_, ?_, ?_⟩
  · show FramesOk m'.heap m'.frames m'.stack (Γ :: Γs.map Prod.snd)
    rw [hfr, hst]
    exact FramesOk.heap_congr hag hfs
  · show StackCtx m'.heap m'.frames m'.stack (c :: Γs.map Prod.fst)
    rw [hfr, hst]
    exact StackCtx.heap_congr hag hsc
  · show ∃ σ, ValueTy m'.heap v σ ∧ KontOk F m'.heap ((c, Γ) :: Γs) σ m'.kont
    exact ⟨τ, hv, by rw [hko]; exact KontOk.heap_congr hag hk⟩
end Static
end Proof
end RubyCore
