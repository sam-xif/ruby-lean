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
  | nil {D h Γs τ} : KontOk D h Γs τ []
  /-- `seqK []` yields the in-flight value unchanged (`Interp.lean:1957`). -/
  | seqNil {D h c Γ Γs τ k} :
      KontOk D h ((c, Γ) :: Γs) τ k → KontOk D h ((c, Γ) :: Γs) τ (.seqK [] :: k)
  /-- `seqK (e :: es)` discards the in-flight value and runs the rest.

      **`Γs.isEmpty` is the toplevel mode** (L155), and this is the only
      constructor that has to name it: `seqK` is the one kont that stores
      *unevaluated statements*, so it is the one whose contents may be a `class`.
      The mode is read off the environment stack rather than carried as an index
      because `frameK` — the constructor at which an activation's environment goes
      out of scope — is already exactly where the definee changes. -/
  | seqCons {D D' h c Γ Γs τ e es τ' Γ' k} :
      inferSeq D Γ (e :: es) Γs.isEmpty c = some (τ', Γ', D') →
      KontOk D' h ((c, Γ') :: Γs) τ' k →
      KontOk D h ((c, Γ) :: Γs) τ (.seqK (e :: es) :: k)
  /-- Assignment binds `x` at the in-flight type and re-yields the value. -/
  | asgn {D h c Γ Γs τ x k} :
      KontOk D h ((c, envSet Γ x τ) :: Γs) τ k →
      KontOk D h ((c, Γ) :: Γs) τ (.asgnK .lvar x :: k)
  /-- The in-flight value is the condition; either branch may run next, so the
      join must be the one `inferIf` computed. -/
  | ifK {D D' h c Γ Γs τ t els τ' Γ' k} :
      inferIf D Γ t els Γs.isEmpty c = some (τ', Γ', D') →
      KontOk D' h ((c, Γ') :: Γs) τ' k →
      KontOk D h ((c, Γ) :: Γs) τ (.ifK t els :: k)
  | whileCond {D h ctx Γ Γs τ c body k} :
      LoopOk D Γ c body Γs.isEmpty ctx → KontOk D h ((ctx, Γ) :: Γs) .nilT k →
      KontOk D h ((ctx, Γ) :: Γs) τ (.whileCondK c body :: k)
  | whileBody {D h ctx Γ Γs τ c body k} :
      LoopOk D Γ c body Γs.isEmpty ctx → KontOk D h ((ctx, Γ) :: Γs) .nilT k →
      KontOk D h ((ctx, Γ) :: Γs) τ (.whileBodyK c body :: k)
  /-- The in-flight value is the **receiver** of a binary builtin send; the
      argument expression runs next. The site is `.explicit` because `evalExpr`
      picks it syntactically and `infer` rejects `self` in receiver position. -/
  | recvK {D D₂ h c Γ Γs τ mname arg τp τret Γ₂ k} :
      infer D Γ arg Γs.isEmpty c = some (τp, Γ₂, D₂) →
      sigOf D₂ τ mname = some ([τp], τret) →
      KontOk D₂ h ((c, Γ₂) :: Γs) τret k →
      KontOk D h ((c, Γ) :: Γs) τ (.recvK mname [arg] .none .explicit :: k)
  /-- **A zero-argument send** (L152), and it is a separate constructor rather than
      `recvK` with an empty list because the two describe *different numbers of
      steps*. With an argument, `applyKont` pushes an `argsK` and the dispatch is a
      step away; with none, `startArgs … [] []` is `finishSend`, so the send completes
      **in this step** and the continuation `k` must already be typed at the return
      type. There is no `argsK` in the chain at all, and therefore no `ValueTy` stored
      in the kont — which is why this constructor, unlike `argsK`, does not read the
      heap. -/
  | recvK0 {D h c Γ Γs τ mname τret k} :
      sigOf D τ mname = some ([], τret) →
      KontOk D h ((c, Γ) :: Γs) τret k →
      KontOk D h ((c, Γ) :: Γs) τ (.recvK mname [] .none .explicit :: k)
  /-- The in-flight value is the **argument**; the receiver is already a value
      carried by the kont, so its type is pinned by `ValueTy` rather than by
      `infer`.

      **The site is a parameter** (L171). `startArgs` stores whatever site it was
      called at, and nothing between here and the dispatch reads it: `visError?`
      matches `.explicit` alone and both dispatch lemmas have been quantified over
      the site since L164. So the *written receiverless* unary send — which pushes
      this kont at `.implicit`, with the frame's `self` as the stored receiver —
      is the same constructor rather than a second one. -/
  | argsK {D h c Γ Γs τ mname recv τr τret k} {site : SendSite} :
      ValueTy h recv τr →
      sigOf D τr mname = some ([τ], τret) →
      KontOk D h ((c, Γ) :: Γs) τret k →
      KontOk D h ((c, Γ) :: Γs) τ (.argsK recv site mname [] [] .none :: k)
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
      KontOk D h (cΓ' :: Γs) τ k → KontOk D h (cΓ :: cΓ' :: Γs) τ (.frameK fid :: k)

/-- The control component. `.jump` is excluded outright: `break`/`next`/`return`
    are not in the fragment, so no step can produce one. -/
def CtlOk (D : Decls) (c : FrameCtx) (Γ : Env) (Γs : List (FrameCtx × Env))
    (m : Machine) : Prop :=
  match m.ctl with
  | .eval e =>
    ∃ τ Γ' D', infer D Γ e Γs.isEmpty c = some (τ, Γ', D') ∧
      KontOk D' m.heap ((c, Γ') :: Γs) τ m.kont
  | .value v => ∃ τ, ValueTy m.heap v τ ∧ KontOk D m.heap ((c, Γ) :: Γs) τ m.kont
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
  | nil => intro _; exact .nil
  | seqNil _ ih => intro ha; exact .seqNil (ih ha)
  | seqCons hs _ ih => intro ha; exact .seqCons hs (ih ha)
  | asgn _ ih => intro ha; exact .asgn (ih ha)
  | ifK hi _ ih => intro ha; exact .ifK hi (ih ha)
  | whileCond hl _ ih => intro ha; exact .whileCond hl (ih ha)
  | whileBody hl _ ih => intro ha; exact .whileBody hl (ih ha)
  | recvK hsg ha' _ ih => intro ha; exact .recvK hsg ha' (ih ha)
  | recvK0 hsg _ ih => intro ha; exact .recvK0 hsg (ih ha)
  | argsK hv hsg _ ih => intro ha; exact .argsK (ValueTy.congr ha hv) hsg (ih ha)
  | frameK _ ih => intro ha; exact .frameK (ih ha)

/-- The shape every call site reads. `heap_congr'` takes the heap agreement
    *after* the derivation because the induction generalizes the heap index, and
    with the declarations now an index too there is no instantiation at which the
    hypothesis can stay fixed outside. -/
theorem KontOk.heap_congr {h h' : Heap} (ha : TypeAgree h h')
    {D : Decls} {Γs : List (FrameCtx × Env)} {τ : Ty} {k : List Kont}
    (hk : KontOk D h Γs τ k) : KontOk D h' Γs τ k :=
  KontOk.heap_congr' hk ha

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

    **`StrClsOk` is the fourth heap conjunct** (L151), and it is here for the
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
  NoHook m.heap ∧ Saturated m.heap ∧ StrClsOk m.heap ∧
    ClassOk m.heap ∧ BottomObj m.frames m.stack ∧
    ∃ (F : Decls) (c : FrameCtx) (Γ : Env) (Γs : List (FrameCtx × Env)), DeclsOk F m.heap ∧
      FramesOk m.heap m.frames m.stack (Γ :: Γs.map Prod.snd) ∧
      StackCtx m.heap m.frames m.stack (c :: Γs.map Prod.fst) ∧
      CtlOk F c Γ Γs m

/-! ### Inversions used by the send cases -/

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

/-- `evalExpr` chooses the send site *syntactically* from the receiver
    expression (`Interp.lean:2582`); `infer` rejects `self`, so the site is
    always `.explicit` in the fragment. -/
theorem site_explicit {r : Expr} (h : isSelf r = false) :
    (match r with | .self' => SendSite.selfRecv | _ => SendSite.explicit) = .explicit := by
  cases r <;> try rfl
  exact absurd h (by simp [isSelf])

/-- `Machine.currentFrame` and `curFrame` agree once the stack is non-empty. -/
theorem currentFrame_eq {m : Machine} (hne : m.stack ≠ []) :
    m.currentFrame = curFrame m := by
  cases hst : m.stack with
  | nil => exact absurd hst hne
  | cons fid _ => simp [Machine.currentFrame, curFrame, curFid, hst]

/-- Inversion for the `def` rule. -/
theorem infer_def_inv {D D' : Decls} {Γ : Env} {name : String} {params : List Param}
    {body : Expr} {τ : Ty} {Γ' : Env} {top : Bool} {ctx : FrameCtx}
    (h : infer D Γ (.def' name params body) top ctx = some (τ, Γ', D')) :
    τ = .sym ∧ Γ' = Γ ∧ params = [] ∧ declaresName D name = false
      ∧ name ≠ "method_added"
      ∧ ∃ τb Γb, infer D [] body false { ctx with selfCls := some ctx.cls }
          = some (τb, Γb, D)
      ∧ (D' = D ∨
          (D' = addRow D ctx.cls name { params := [], ret := τb } ∧
            top = false ∧ name ≠ "initialize" ∧
            reopenableClasses.contains ctx.cls = true ∧ defFree body = true)) := by
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
            Or.inr ⟨rfl, hrow.1, hrow.2.1, hrow.2.2.1, hrow.2.2.2⟩⟩
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
    isSelf r = false ∧
      ∃ τr, infer D Γ r top ctx = some (τr, Γ', D') ∧ sigOf D' τr mname = some ([], τ) := by
  simp only [infer] at h
  split at h
  case isTrue hns => exact absurd h (by simp)
  rename_i hns
  have hns' : isSelf r = false := by simpa using hns
  split at h
  · next τr Γ₁ D₁ hr =>
    split at h
    · next τret hsg =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨hns', τr, hr, hsg⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Inversion for the send rule. Factored out of `step_ok` because the nested
    `split at` needs `next`-bound names that are unreadable inline. -/
theorem infer_send_inv {D D' : Decls} {Γ : Env} {r arg : Expr} {mname : String} {τ : Ty}
    {Γ' : Env} {top : Bool} {ctx : FrameCtx}
    (h : infer D Γ (.send (some r) mname [arg] none) top ctx = some (τ, Γ', D')) :
    isSelf r = false ∧
      ∃ τr Γ₁ D₁ τp, infer D Γ r top ctx = some (τr, Γ₁, D₁) ∧
      infer D₁ Γ₁ arg top ctx = some (τp, Γ', D') ∧
      sigOf D' τr mname = some ([τp], τ) := by
  simp only [infer] at h
  split at h
  case isTrue hns => exact absurd h (by simp)
  rename_i hns
  have hns' : isSelf r = false := by simpa using hns
  split at h
  · next τr Γ₁ D₁ hr =>
    split at h
    · next τa Γ₂ D₂ ha =>
      split at h
      · next τp τret hsg =>
        split at h
        · next hτ =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨hns', τr, Γ₁, D₁, τp, hr, hτ ▸ ha, hτ ▸ hsg⟩
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)


/-- Inversion for the **unary written receiverless call** (L171). No `isSelf`
    guard and no receiver run: the receiver is the frame's `self`, supplied by the
    context, so the rule's three tests are the argument, the signature at the table
    the argument leaves, and the parameter match. -/
theorem infer_implicit_send1_inv {D D' : Decls} {Γ : Env} {arg : Expr}
    {mname : String} {τ : Ty} {Γ' : Env} {top : Bool} {ctx : FrameCtx}
    (h : infer D Γ (.send none mname [arg] none) top ctx = some (τ, Γ', D')) :
    ∃ c τp, ctx.selfCls = some c ∧
      infer D Γ arg top ctx = some (τp, Γ', D') ∧
      sigOf D' (.cls c) mname = some ([τp], τ) := by
  simp only [infer] at h
  split at h
  · next c hsome =>
    split at h
    · next τa Γ₁ D₁ ha =>
      split at h
      · next τp τret hsg =>
        split at h
        · next hτ =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨c, τp, hsome, hτ ▸ ha, hsg⟩
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

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
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : StrClsOk m.heap) (hcls : ClassOk m.heap)
    (hbot : BottomObj m.frames m.stack)
    (hinf : infer F Γ e Γs.isEmpty c = some (τ, Γ', F'))
    (hk : KontOk F' m.heap ((c, Γ') :: Γs) τ m.kont) :
    Inv (withCtl m (.eval e)) :=
  ⟨hh, hsat, hstr, hcls, hbot, F, c, Γ, Γs, ht, hfs, hsc, ⟨τ, Γ', F', hinf, hk⟩⟩

theorem inv_value {F : Decls} {m : Machine} {c : FrameCtx} {Γ : Env}
    {Γs : List (FrameCtx × Env)} {v : Value} {τ : Ty}
    (hfs : FramesOk m.heap m.frames m.stack (Γ :: Γs.map Prod.snd)) (ht : DeclsOk F m.heap)
    (hsc : StackCtx m.heap m.frames m.stack (c :: Γs.map Prod.fst))
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : StrClsOk m.heap) (hcls : ClassOk m.heap)
    (hbot : BottomObj m.frames m.stack)
    (hv : ValueTy m.heap v τ) (hk : KontOk F m.heap ((c, Γ) :: Γs) τ m.kont) :
    Inv (withCtl m (.value v)) :=
  ⟨hh, hsat, hstr, hcls, hbot, F, c, Γ, Γs, ht, hfs, hsc, ⟨τ, hv, hk⟩⟩

theorem inv_push {F : Decls} {m : Machine} {c : FrameCtx} {Γ : Env}
    {Γs : List (FrameCtx × Env)} {e : Expr} {τ : Ty} {Γ' : Env} {F' : Decls} {k : Kont}
    (hfs : FramesOk m.heap m.frames m.stack (Γ :: Γs.map Prod.snd)) (ht : DeclsOk F m.heap)
    (hsc : StackCtx m.heap m.frames m.stack (c :: Γs.map Prod.fst))
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : StrClsOk m.heap) (hcls : ClassOk m.heap)
    (hbot : BottomObj m.frames m.stack)
    (hinf : infer F Γ e Γs.isEmpty c = some (τ, Γ', F'))
    (hk : KontOk F' m.heap ((c, Γ') :: Γs) τ (k :: m.kont)) :
    Inv (withKont m (.eval e) k) :=
  ⟨hh, hsat, hstr, hcls, hbot, F, c, Γ, Γs, ht, hfs, hsc, ⟨τ, Γ', F', hinf, hk⟩⟩

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
    `StrClsOk` conjunct carries.

    `hpl` is three refutations rather than `plainRecv`'s own `match` because a `match`
    written in a *statement* elaborates to a fresh matcher constant, which then will
    not `rw` against the one `plainRecv` was compiled with. Case-splitting the payload
    is the shape that composes; `entry_dispatch` discharges the same three shapes the
    same way. -/
theorem valueTy_alloc_fresh {h : Heap} {obj : Object} {n : String}
    (hpl : (∀ c, obj.payload ≠ .proc c) ∧ (∀ xs, obj.payload ≠ .hsh xs) ∧
           (∀ c, obj.payload ≠ .cls c))
    (he : obj.eigen = none)
    (hk : (h.classPayload? obj.klass).isSome)
    (hn : className h obj.klass = n) :
    ValueTy ⟨h.objs.push obj⟩ (.ref h.objs.size) (.cls n) := by
  obtain ⟨hproc, hhsh, hnc⟩ := hpl
  have hg : PlainGrow h ⟨h.objs.push obj⟩ := plainGrow_alloc h obj hnc
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
    all_goals simp [hlt, hk]
  show valueTy? _ _ = _
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
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : StrClsOk m.heap) (hcls : ClassOk m.heap)
    (hbot : BottomObj m.frames m.stack)
    (hg : PlainGrow m.heap m'.heap)
    (hfr : m'.frames = m.frames) (hst : m'.stack = m.stack) (hko : m'.kont = m.kont)
    (hv : ValueTy m'.heap v τ) (hk : KontOk F m.heap ((c, Γ) :: Γs) τ m.kont) :
    Inv (withCtl m' (.value v)) := by
  have hag : TypeAgree m.heap m'.heap := typeAgree_of_plainGrow hg
  refine ⟨NoHook_grow hg hsat hh,
    Saturated_grow hg.shapeAgree hg.size hsat, StrClsOk_grow hg hstr,
    ClassOk_grow hg hsat hcls,
    show BottomObj m'.frames m'.stack by rw [hfr, hst]; exact hbot,
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
