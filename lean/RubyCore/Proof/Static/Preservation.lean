import RubyCore.Proof.Static.Konts
import RubyCore.Proof.Static.Iter

/-!
# P0 static soundness, part 3 — progress and preservation in one case analysis

§3 of `Proof/StaticSoundness.lean` before the L136 split. `StepOk` bundles both
obligations so the 48-way `Kont` split and the ~40-way `Expr` split are each
walked **once**: `.next` carries preservation, `.done` is a legitimate halt, and
every remaining `StepResult` — crucially `.uncaught` — is `False`, which is
exactly progress.
-/

namespace RubyCore
namespace Proof
namespace Static

open Interp
open RubyCore.Types

set_option maxRecDepth 100000

/-! ## 3. Progress and preservation, in one case analysis

`StepOk` bundles both obligations so the 48-way `Kont` split and the ~40-way
`Expr` split are each walked **once**: `.next` carries preservation, `.done` is
a legitimate halt, and every remaining `StepResult` — crucially `.uncaught` —
is `False`, which is exactly progress.
-/

def StepOk : StepResult → Prop
  | .next m' => Inv m'
  | .done _ _ => True
  -- **L216: an uncaught exception is admitted when it is not a *type* error.**
  --
  -- `typeStuck` has always been `.uncaught exc m => isTypeError m.heap exc`
  -- (`Proof/TypeSafety.lean`) — an uncaught `ArgumentError` from user code is a
  -- perfectly good Ruby outcome and the metatheorem never claimed otherwise. `StepOk`
  -- was nevertheless refusing `.uncaught` outright, which is *stronger than the
  -- theorem needs* and is exactly what makes `raise` unstateable: no rule can produce a
  -- jump the bundle forbids.
  --
  -- So this clause is a weakening, and the headline theorem does not move: `Inv` is
  -- unchanged, `consecution` is unchanged, and `safety`'s obligation
  -- (`¬ aboutToTypeStick`) is *this clause* at the `.uncaught` branch rather than a
  -- vacuous one. What it buys is that `CtlOk` can admit `.raiseJ`, which `begin`/`rescue`
  -- and `raise` both need.
  | .uncaught exc m => ¬ isTypeError m.heap exc
  | _ => False

/-! ### The implicit-self dispatch, shared by every receiverless send

`evalExpr` sends `foo` and `foo()` to the **same** place — `startArgs m self site
mname [] []`, which is `finishSend` (`Interp/Send.lean:455`) — differing only in
the `SendSite`: `.vcall` for the bare identifier, `.implicit` for the written
call. `visError?` answers `none` for every site but `.explicit`
(`Interp/Dispatch.lean:325`), and both dispatch lemmas were generalized over the
site at L164, so the two rules share **one** consecution argument. This is L164's
`vcall` case lifted out of `step_ok` verbatim and quantified over `site`; L170's
`.send none mname [] none` rule is the second caller and adds no proof.
-/

/-- The zero-argument implicit-self send preserves `Inv`, whatever the site. The
    dispatch happens *in this step* — there is no continuation and no `argsK` —
    so the caller's `KontOk` must already be typed at the return type. -/
theorem inv_implicit_send0 {F : Decls} {m : Machine} {ctx : FrameCtx} {Γ Γk : Env}
    {Γs : List (FrameCtx × Env)} {c mname : String} {τret : Ty} {site : SendSite}
    (hfs : FramesOk m.heap m.frames m.stack (Γ :: Γs.map Prod.snd))
    (htab : DeclsOk F m.heap)
    (hsc : StackCtx m.heap m.frames m.stack (ctx :: Γs.map Prod.fst))
    (hhook : NoHook m.heap) (hsat : Saturated m.heap) (hstr : LitClsOk m.heap)
    (hcls : ClassOk m.heap) (hbot : BottomObj m.frames m.stack)
    (hks : framePopLabels m.kont = m.stack.dropLast)
    (hne : m.stack ≠ []) (hsome : ctx.selfCls = some c)
    (hsg : sigOf F (.cls c) mname = some ([], τret))
    -- L193: the continuation may have been registered at a *wider* type than the
    -- signature's return, and this is the only hypothesis that changes.
    {τw : Ty} (hsubw : subTy τret τw = true)
    (hk : KontOk F m.heap ((ctx, Γk) :: Γs) τw m.kont)
    -- L228's conjunct, defaulted for the `inv_*` family's reason (`Konts.lean`).
    (hglob : GlobalsOk F m.heap m.globals := by assumption)
    (hsuE : SubEnv Γk Γ := by first | exact SubEnv.refl _ | assumption)
    -- L247, last for `Konts.lean`'s reason: a defaulted parameter still eats a
    -- positional argument, and this lemma's callers pass `hglob` positionally.
    (hclo : ClosuresOk m := by assumption) :
    StepOk (startArgs m m.currentFrame.self site mname [] [] .none) := by
  -- L236: the slack is consumed at the top, once — every obligation below is then at
  -- the environment the continuation was registered at.
  have hfs := FramesOk.narrowHead hsuE hfs
  have hself : ValueTy m.heap m.currentFrame.self (.cls c) := by
    cases hst : m.stack with
    | nil => exact absurd hst hne
    | cons fid fids =>
      rw [hst] at hsc
      have := hsc.2.2.2.1 c hsome
      rw [show m.currentFrame = m.frames.getD fid default by
        simp [Machine.currentFrame, hst]]
      exact this.1
  -- L254: `EntryOk.blockless` is what refutes the iterator arm at a rule that read the
  -- row through `sigOf`, which refuses a block-taking one.
  rcases (htab.1 _ mname _ (sigOf_declFor (by simp) hsg)).blockless with hbi |
    ⟨mdu, cu, htys, hresu, hnmu, hconfu⟩
  · obtain ⟨w, m', hw, hg', hfr', hst', hko', hgv', hstep⟩ :=
      entry_dispatch (m := m) (recv := m.currentFrame.self) (args := [])
        (site := site) (by simp) (by simp) (by simp) hbi hself trivial
    rw [hstep]
    -- **L215**: `inv_grow_value` where this was `inv_value`, and the four extra
    -- arguments are `entry_dispatch`'s new conclusion verbatim. Inert for a
    -- non-allocating row (`m' = m` and `PlainGrow` is reflexive); the point is that the
    -- case no longer *forbids* one.
    exact inv_grow_value hfs htab hsc hhook hsat hstr hcls hbot hks hg' hfr' hst' hko'
      (ValueTy.weaken hw hsubw) hk hglob hgv'
  · have hru := hresu _ (valueTy_tyClass (by simp) (by simp) (by simp) hself)
    have hown : (m.heap.classPayload? mdu.owner).isSome := by
      obtain ⟨_, _, _, _, _, _, _, _, h9, _⟩ := hru; exact h9
    rw [user_dispatch (m := m) (site := site) hru hself]
    have hlt : ∀ g ∈ m.stack, g < m.frames.size := hfs.mem_lt
    obtain ⟨hdp, hdblk, hdfu, Γb, r, τb, hbu, hsb, hag⟩ := hconfu
    refine ⟨hhook, hsat, hstr, hcls,
      BottomObj_cons hne (BottomObj_push hlt hbot),
      -- L199: the push writes a `frameK` and a stack entry at the same id, so both
      -- lists grow by the same head — which is the whole content of the clause.
      (by simp [framePopLabels, hks, dropLast_cons_ne hne]),
      -- L247: one `frameK` (no closure) and one frame.
      (ClosuresOk.pushFrame hclo rfl rfl rfl), _,
      -- L198: the callee's context carries the `ret` its body was checked at, which
      -- is what `KontOk.frameK`'s agreement premise reads.
      { cls := cu, selfCls := some cu, ret := r, meth := some mname,
        params := some [] }, [],
      -- L236: the caller's environment on the new stack is the *narrowed* one, which
      -- `hfs` was moved to at the top of the proof.
      (ctx, Γk) :: Γs, htab, ?_, ?_, ?_, ?_⟩
    · refine ⟨by rw [Array.size_push]; exact Nat.lt_succ_self _, hlt,
        ⟨ShallowChain.of_none (by rw [getD_push_lt_self]; try rfl), ?_, ?_⟩, FramesOk.push hfs⟩
      · rw [getD_push_lt_self]; exact hown
      · intro y σ hy; exact absurd hy (by simp [envGet?])
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, (fun hcb _ => nomatch hcb), StackCtx.push hlt hsc⟩
      · rw [getD_push_lt_self]; exact hown
      · rw [getD_push_lt_self]; exact fun _ => hnmu
      · rw [getD_push_lt_self]; exact fun _ => rfl
      -- The callee's `self` **is** the receiver, and the receiver's type is
      -- what the row was read at — so this clause is the send's own
      -- `ValueTy` carried one frame in, not a new obligation.
      · intro sc hsc'
        simp only [Option.some.injEq] at hsc'
        subst hsc'
        rw [getD_push_lt_self]
        show ValueTy m.heap m.currentFrame.self (.cls cu) ∧
          (userFrame m.currentFrame.self mdu mname).defmod ∈
            ancestors m.heap (classOf m.heap m.currentFrame.self)
        have hcu : c = cu := UserKey.cls_inv htys
        -- **L209: and the chain half is `ResolvesUser`'s eleventh clause, spent
        -- here.** `userFrame` sets `defmod := md.owner`, and the row's resolution says
        -- that owner is on the receiver's chain — which is the fact `doSuper`'s
        -- `dropWhile` needs and the one thing the walk cannot recover for itself.
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hch, _⟩ := hru
        exact ⟨hcu ▸ hself, hch⟩
      -- **L189: the callee's lexical scope**, which `ResolvesUser` carries — the
      -- ninth clause it grew for exactly this push.
      · rw [getD_push_lt_self]
        obtain ⟨_, _, _, _, _, _, _, _, _, _, hcr, _, _⟩ := hru
        exact hcr
      -- L198/L200: `userFrame` builds a `.method` frame, and the caller's context is
      -- right there on the list — so the callee's context may declare a return type.
      · exact Or.inl ⟨by rw [getD_push_lt_self]; rfl, by simp⟩
      -- **L210: the callee's context names the method**, and `userFrame` builds the
      -- activation with `meth := md.superName.getD mname` — so the clause is
      -- `ResolvesUser`'s twelfth, `md.superName = none`, and nothing else.
      · intro mn hmn
        simp only [Option.some.injEq] at hmn
        subst hmn
        rw [getD_push_lt_self]
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hsn⟩ := hru
        exact ⟨by simp [userFrame, hsn], rfl, rfl, rfl, rfl, rfl, rfl⟩
      -- L243: `userFrame` leaves `captured` at its default, which is the same fact
      -- `FrameConforms`'s first clause used to carry here.
      · rw [getD_push_lt_self]; exact fun _ => rfl
    -- **L228: the push leaves the globals alone**, and the heap too, so the conjunct is
    -- the incoming one at a machine that differs in `frames`/`stack`/`kont`/`ctl`.
    · exact hglob
    -- **L229: the body's type is `τb`, below the declared `τret`** — and the eval clause's
    -- subsumption is where that difference is spent, exactly as `CtlOk` has allowed since
    -- L193. One `subTy_trans` is the whole cost of the join.
    · exact ⟨τb, τw, Γb, _, _, hbu, subTy_trans hsb hsubw, SubEnv.refl _,
        KontOk.frameK (fun σ h => by rw [hag σ (by simpa using h)]; exact hsubw) rfl hk⟩

/-- **The array literal's loop, once** (L230) — and it is a *lemma* rather than three
    copies of a case because L230 gave the loop a second entry point.

    `continueArray` is reached from three places: `evalExpr`'s `.array` arm, the `arrK`
    delivery, and now the `arrSplatK` delivery (after the spread). All three are the same
    two shapes — nothing left, so allocate; a head to run, so push the next kont — and the
    only difference is which kont the head gets, which is a function of the head itself.
    Stating it once is what keeps the splat's arrival from duplicating fifteen lines.

    The accumulated values are never inspected, which is the erasure of element types
    showing up as an *absence* in the statement rather than as a weakening of it. -/
theorem inv_continueArray {D D' : Decls} {m : Machine} {c : FrameCtx} {Γ Γ' : Env}
    {Γs : List (FrameCtx × Env)} {τ' τw : Ty} {acc : List Value} {rest : List Expr}
    (hfs : FramesOk m.heap m.frames m.stack (Γ :: Γs.map Prod.snd))
    (htab : DeclsOk D m.heap)
    (hsc : StackCtx m.heap m.frames m.stack (c :: Γs.map Prod.fst))
    (hhook : NoHook m.heap) (hsat : Saturated m.heap) (hstr : LitClsOk m.heap)
    (hcls : ClassOk m.heap) (hbot : BottomObj m.frames m.stack)
    (hks : framePopLabels m.kont = m.stack.dropLast)
    (hglob : GlobalsOk D m.heap m.globals)
    (hs : inferElems D Γ rest Γs.isEmpty c = some (τ', Γ', D'))
    (hsw : subTy (.cls "Array") τw = true)
    (hk : KontOk D' m.heap ((c, Γk) :: Γs) τw m.kont)
    (hsuE : SubEnv Γk Γ' := by first | exact SubEnv.refl _ | assumption)
    (hclo : ClosuresOk m := by assumption) :
    StepOk (Interp.continueArray m acc rest) := by
  cases rest with
  | nil =>
    -- Nothing left: the literal allocates *in this step*, at `Boot.arrayId`, and the case
    -- is L151's string literal with the class swapped. `inferElems _ _ [] = some (.nilT,
    -- Γ, D)` pins the environment and the table to the incoming ones.
    simp only [inferElems, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, rfl, rfl⟩ := hs
    simp only [Interp.continueArray, Builtins.allocArr]
    exact inv_grow_value hfs htab hsc hhook hsat hstr hcls hbot hks
      (plainGrow_alloc m.heap _ (by simp) rfl) rfl rfl rfl
      (ValueTy.weaken (valueTy_alloc_fresh (by simp) rfl rfl rfl hstr.2.1 hstr.2.2
        (fun _ => ⟨_, rfl⟩)) hsw) hk
  | cons e rest' =>
    -- A head to run, and **which kont it gets is the head's own shape**: a splat element
    -- evaluates its *operand* under an `arrSplatK`, anything else evaluates itself under
    -- an `arrK`. `inferElems`' two arms line up with `continueArray`'s two.
    cases e
    case splat oe =>
      cases oe with
      | none => exact absurd hs (by simp [inferElems, infer])
      | some o =>
        simp only [inferElems] at hs
        cases ho : infer D Γ o Γs.isEmpty c with
        | none => rw [ho] at hs; exact absurd hs (by simp)
        | some r =>
          obtain ⟨τo, Γ₁, D₁⟩ := r
          rw [ho] at hs
          cases τo with
          | cls nm =>
            by_cases hnm : nm = "Array"
            · subst hnm
              rw [continueArray_splat]
              exact inv_push hfs htab hsc hhook hsat hstr hcls hbot
                (by simp [framePopLabels, hks]) ho
                (KontOk.arrSplatK (subTy_refl _) hs hsw hk)
            · simp_all
          | _ => simp_all
    all_goals
      (rename_i _
       simp only [inferElems] at hs
       cases he : infer D Γ _ Γs.isEmpty c with
       | none => rw [he] at hs; exact absurd hs (by simp)
       | some r =>
         obtain ⟨τe, Γ₁, D₁⟩ := r
         rw [he] at hs
         rw [continueArray_plain (by intro x hq; exact absurd hq (by simp))]
         exact inv_push hfs htab hsc hhook hsat hstr hcls hbot
           (by simp [framePopLabels, hks]) he (KontOk.arrK hs hsw hk))

set_option maxHeartbeats 2000000 in
theorem step_ok {m : Machine} (h : Inv m) : StepOk (stepFn m) := by
  obtain ⟨hhook, hsat, hstr, hcls, hbot, hks, hclo, D, ctx, Γ, Γs, htab, hfs, hsc, hglob, hc⟩ := h
  -- **L252: `FrameOk` is no longer free.** `StackCtx`'s empty-chain clause is guarded on
  -- the context's block flag, so what the whole proof can have unconditionally is
  -- `FrameShallow` — enough for every *read* of a local and for `m.stack ≠ []`. The one
  -- case that needs the write, the `asgnK` delivery, gets the flag off `KontOk.asgn`.
  have hfsh : FrameShallow m := hfs.frameShallow
  have hl : LocalsOk Γ m := hfs.localsOk
  -- **L247, once for the whole proof.** Almost every case steps at
  -- `{ m with kont := k }` for the tail `k` the kont's head was peeled off, so the
  -- defaulted `by assumption` cannot find `ClosuresOk m`; this is the one-line bridge,
  -- and the equation naming the head is what each case already has under `hK`.
  have hcloTail : ∀ {κ₀ : Kont} {k' : List Kont}, m.kont = κ₀ :: k' →
      ClosuresOk { m with kont := k' } := fun hkq =>
    ClosuresOk.konts hclo rfl rfl
      (by intro κ hm; exact Or.inl (by rw [hkq]; exact List.mem_cons_of_mem _ hm))
  unfold CtlOk at hc
  rcases hctl : m.ctl with e | v | j
  · -- ## control = eval e
    rw [hctl] at hc
    obtain ⟨τ, τw, Γ', D', Γk, hinf, hsubw, hsuE, hk⟩ := hc
    simp only [stepFn, hctl]
    cases e <;> try (simp only [infer] at hinf; contradiction)
    case int n =>
      simp only [infer, Option.some.injEq, Prod.mk.injEq] at hinf
      obtain ⟨rfl, rfl, rfl⟩ := hinf
      exact inv_value hfs htab hsc hhook hsat hstr hcls hbot hks (ValueTy.weaken (ValueTy.exact rfl) hsubw) hk
    -- L202: `.int`'s twin, and the copy is exact — `valueTy? (.flt x) = some .float`
    -- holds by `rfl` for the same reason (`.flt` is an immediate, so the arm reads no
    -- heap), so `ValueTy.exact` closes it and no new transport is involved.
    case flt x =>
      simp only [infer, Option.some.injEq, Prod.mk.injEq] at hinf
      obtain ⟨rfl, rfl, rfl⟩ := hinf
      exact inv_value hfs htab hsc hhook hsat hstr hcls hbot hks (ValueTy.weaken (ValueTy.exact rfl) hsubw) hk
    case tru =>
      simp only [infer, Option.some.injEq, Prod.mk.injEq] at hinf
      obtain ⟨rfl, rfl, rfl⟩ := hinf
      exact inv_value hfs htab hsc hhook hsat hstr hcls hbot hks (ValueTy.weaken (ValueTy.exact rfl) hsubw) hk
    case fls =>
      simp only [infer, Option.some.injEq, Prod.mk.injEq] at hinf
      obtain ⟨rfl, rfl, rfl⟩ := hinf
      exact inv_value hfs htab hsc hhook hsat hstr hcls hbot hks (ValueTy.weaken (ValueTy.exact rfl) hsubw) hk
    case nil =>
      simp only [infer, Option.some.injEq, Prod.mk.injEq] at hinf
      obtain ⟨rfl, rfl, rfl⟩ := hinf
      exact inv_value hfs htab hsc hhook hsat hstr hcls hbot hks (ValueTy.weaken (ValueTy.exact rfl) hsubw) hk
    -- **The producer** (L151). One allocation, no continuation, no dispatch: the
    -- whole case is `plainGrow_alloc` for the step, `valueTy_alloc_fresh` for the
    -- value, and `inv_grow_value` — proved a rung earlier — for everything else.
    -- That the case is this short is the measurement L149 was for.
    case str s =>
      simp only [infer, Option.some.injEq, Prod.mk.injEq] at hinf
      obtain ⟨rfl, rfl, rfl⟩ := hinf
      exact inv_grow_value hfs htab hsc hhook hsat hstr hcls hbot hks
        (plainGrow_alloc m.heap _ (by simp) rfl)
        rfl rfl rfl
        (ValueTy.weaken (valueTy_alloc_fresh (by simp) rfl rfl rfl hstr.1.1 hstr.1.2 (by simp)) hsubw) hk
    -- **The symbol literal** (L159). Identical to the four immediate cases above,
    -- which is the point: the slice's third-largest blocker by node count cost a
    -- rule of one line and a case of three, because `Ty.sym` was already there and
    -- `evalExpr` writes no heap.
    case sym s =>
      simp only [infer, Option.some.injEq, Prod.mk.injEq] at hinf
      obtain ⟨rfl, rfl, rfl⟩ := hinf
      exact inv_value hfs htab hsc hhook hsat hstr hcls hbot hks (ValueTy.weaken (ValueTy.exact rfl) hsubw) hk
    -- **`self`** (F1b.11). `evalExpr` answers the frame's `self` with no heap
    -- write, so this is the shortest case in the file — one `inv_value` — and the
    -- whole content is the `StackCtx` clause that says the frame's `self` has the
    -- type the context claims.
    case self' =>
      simp only [infer] at hinf
      split at hinf
      · next c hsome =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hinf
        obtain ⟨rfl, rfl, rfl⟩ := hinf
        refine inv_value hfs htab hsc hhook hsat hstr hcls hbot hks
          (ValueTy.weaken ?_ hsubw) hk
        cases hst : m.stack with
        | nil => exact absurd hst hfsh.1
        | cons fid fids =>
          rw [hst] at hsc
          have := hsc.2.2.2.1 c hsome
          rw [show m.currentFrame = m.frames.getD fid default by
            simp [Machine.currentFrame, hst]]
          exact this.1
      · exact absurd hinf (by simp)
    -- **The implicit-self send** (F1b.11), and it is the only send case with no
    -- continuation: `evalExpr` goes straight to `startArgs … [] []`, which is
    -- `finishSend`, so the dispatch happens *in this step*. That makes it
    -- `recvK0`'s consecution case with the receiver already in hand — the same two
    -- dispatch lemmas, at site `.vcall` rather than `.explicit`.
    case vcall mname =>
      simp only [infer] at hinf
      split at hinf
      · next c hsome =>
        split at hinf
        · next τret hsg =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hinf
          obtain ⟨rfl, rfl, rfl⟩ := hinf
          simp only [evalExpr]
          exact inv_implicit_send0 hfs htab hsc hhook hsat hstr hcls hbot hks hfsh.1
            hsome hsg hsubw hk
        · exact absurd hinf (by simp)
      · exact absurd hinf (by simp)
    -- **A constant read** (L189), and the case is short because the two `ClassOk`
    -- clauses do the work: `constRead_sole` collapses `evalExpr`'s two-phase lookup
    -- to `Object`'s own table (the lexical phase can only hit `Object`, and if it
    -- misses, the ancestor walk gets there), and the value's type is the class
    -- object's own name — which is what `ClassOk` says it is.
    case const n =>
      simp only [infer] at hinf
      split at hinf
      · next τc hre =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hinf
        obtain ⟨rfl, rfl, rfl⟩ := hinf
        -- **L195: the whole case is now the table's own clause.** It used to read six
        -- of `ClassOk`'s promises and rebuild `ValueTy` from them; `DeclsOk`'s
        -- constant half *is* that value judgement, so what is left is the frame's
        -- `cref` membership and one `constRead_sole`.
        obtain ⟨v, hconst, hty, hsole⟩ := htab.2.1 n _ hre
        -- `Object` is on the frame's cref (`StackCtx`, L189), so the *lexical* phase
        -- cannot miss — and sole ownership makes whatever it hits `Object`'s. The
        -- ancestor walk is never reached.
        cases hst : m.stack with
        | nil => exact absurd hst hfsh.1
        | cons fid fids =>
          have hsc' := hsc
          rw [hst] at hsc'
          have hcur : m.currentFrame = m.frames.getD fid default := by
            simp [Machine.currentFrame, hst]
          have hcref : Boot.objectId ∈ m.currentFrame.cref := by
            rw [hcur]; exact hsc'.2.2.2.2.1
          simp only [evalExpr]
          rw [constRead_sole hcref hconst hsole]
          exact inv_value hfs htab hsc hhook hsat hstr hcls hbot hks
            (ValueTy.weaken hty hsubw) hk
      · exact absurd hinf (by simp)
    -- **`::n`** (L203), and it is `.const`'s case with the two hard steps deleted.
    -- `evalExpr`'s absolute arm is `constLookup m.heap n`, which is `Object`'s own
    -- constant table — literally `constOwn h Boot.objectId n` (`Heap.lean:576/599`
    -- are the same lookup) — so neither the frame's `cref` nor `constRead_sole` is
    -- needed here. `DeclsOk`'s constant half supplies the value and its type outright.
    case cpath base n =>
      cases base with
      | none =>
        simp only [infer] at hinf
        split at hinf
        · next τc hre =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hinf
          obtain ⟨rfl, rfl, rfl⟩ := hinf
          obtain ⟨v, hconst, hty, -⟩ := htab.2.1 n _ hre
          have hcl : constLookup m.heap n = some v := by
            unfold constLookup
            unfold constOwn at hconst
            cases hp : m.heap.classPayload? Boot.objectId with
            | none => rw [hp] at hconst; simp at hconst
            | some c => rw [hp] at hconst; simpa using hconst
          simp only [evalExpr, hcl]
          exact inv_value hfs htab hsc hhook hsat hstr hcls hbot hks
            (ValueTy.weaken hty hsubw) hk
        · exact absurd hinf (by simp)
      -- **`C::n`** (L205): `evalExpr` pushes `.cpathK n` on the base, and the rule's
      -- two reads — the base's class-object type and the table's row — are exactly
      -- `KontOk.cpathK`'s two premises. Nothing about the container's heap is settled
      -- here; `ScopedConstOk` is what the delivery consumes.
      | some b =>
        simp only [infer] at hinf
        split at hinf
        · next cname Γ₁ D₁ hbase =>
          split at hinf
          · next σ hsco =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hinf
            obtain ⟨rfl, rfl, rfl⟩ := hinf
            exact inv_push hfs htab hsc hhook hsat hstr hcls hbot
              (by simp [framePopLabels, hks]) hbase
              (KontOk.cpathK (by simp) hsco hsubw hk)
          · exact absurd hinf (by simp)
        · exact absurd hinf (by simp)
    case var k x =>
      cases k
      case lvar =>
        simp only [infer, Option.map_eq_some_iff] at hinf
        obtain ⟨σ, hg, heq⟩ := hinf
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        exact inv_value hfs htab hsc hhook hsat hstr hcls hbot hks
          (ValueTy.weaken (hl x _ hg) hsubw) hk
      -- **`@x`** (L196), and the case is two branches of `evalExpr` against the two
      -- disjuncts `mkNilable` was chosen for: the ivar is set, and `IvarOk` types what
      -- is there; or it is unset and `evalExpr` answers `nil`, which `mkNilable`
      -- admits. `StackCtx`'s `selfCls` clause is what turns the frame's `self` into a
      -- `.ref` whose class the table can be read at.
      case ivar =>
        simp only [infer] at hinf
        split at hinf
        · next sc hsome =>
          split at hinf
          · next σ hiv =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hinf
            obtain ⟨rfl, rfl, rfl⟩ := hinf
            have hself : ValueTy m.heap m.currentFrame.self (.cls sc) := by
              cases hst : m.stack with
              | nil => exact absurd hst hfsh.1
              | cons fid fids =>
                have hsc2 := hsc
                rw [hst] at hsc2
                have := hsc2.2.2.2.1 sc hsome
                rw [show m.currentFrame = m.frames.getD fid default by
                  simp [Machine.currentFrame, hst]]
                exact this.1
            obtain ⟨o, hsf⟩ : ∃ o, m.currentFrame.self = .ref o := by
              cases hsv : m.currentFrame.self with
              | ref o' => exact ⟨o', rfl⟩
              | _ => rw [hsv] at hself; simp_all [ValueTy, valueTy?, subTy]
            have hpl : plainRecv m.heap o = true := valueTy_ref_plain (hsf ▸ hself)
            -- The class the table is keyed at: `plainRecv` says dispatch goes through
            -- `klass`, and `hself` names that class.
            have hcn : className m.heap (m.heap.get o).klass = sc := by
              have := valueTy_ref_inv (by simp [subTy]) (by simp [subTy]) (hsf ▸ hself)
              rcases this with ⟨-, hs⟩ | ⟨hc, hs⟩
              · have := (subTy_atomic (τ := Ty.cls sc) (by simp) (by simp)).mp hs
                rw [plainRecv_classOf hpl] at this
                simpa using this
              · exact absurd hs (by simp [subTy])
            have hlt : o < m.heap.objs.size := by
              unfold plainRecv at hpl; simp only [Bool.and_eq_true] at hpl
              simpa using hpl.1.1.1.1.1
            simp only [evalExpr, hsf]
            refine inv_value hfs htab hsc hhook hsat hstr hcls hbot hks
              (ValueTy.weaken ?_ hsubw) hk
            cases hfind : ((m.heap.get o).ivars.find? (·.1 == x)).map Prod.snd with
            | none => simpa [hfind] using ValueTy.weaken (ValueTy.exact rfl) (by simp)
            | some v =>
              have := htab.2.2.1 sc x σ hiv o hlt hcn v hfind
              simpa [hfind] using ValueTy.weaken this (by simp)
          · exact absurd hinf (by simp)
        · exact absurd hinf (by simp)
      -- **`$x`** (L228), and it is the shortest read case in the file: `matchGlobal`
      -- answers `none` for a plain name, so the step *is* `getGlobal`, and `GlobalsOk.read`
      -- is the whole obligation — the conjunct was designed to be exactly this.
      case gvar =>
        simp only [infer] at hinf
        split at hinf
        · next σ hpg hgt =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hinf
          obtain ⟨rfl, rfl, rfl⟩ := hinf
          simp only [evalExpr, matchGlobal_none_of_plain hpg]
          exact inv_value hfs htab hsc hhook hsat hstr hcls hbot hks
            (ValueTy.weaken (GlobalsOk.read hglob hpg hgt) hsubw) hk
        · exact absurd hinf (by simp)
      all_goals (simp only [infer] at hinf; contradiction)
    case vasgn k x rhs =>
      cases k
      case lvar =>
        -- L252: the block guard is the outer split; inside a block the rule answers
        -- `none`, so that branch is the contradiction and the `false` branch is L191's.
        simp only [infer] at hinf
        split at hinf
        · exact absurd hinf (by simp)
        · split at hinf
          · rename_i σ Γ₁ hrhs
            simp only [Option.some.injEq, Prod.mk.injEq] at hinf
            obtain ⟨rfl, rfl, rfl⟩ := hinf
            exact inv_push hfs htab hsc hhook hsat hstr hcls hbot
              (by simp [framePopLabels, hks]) hrhs (KontOk.asgn (by assumption) hsubw hk)
          · exact absurd hinf (by simp)
      -- **`@x = e`** (L191). `evalExpr` pushes the same shape as the local-variable
      -- write and the rule answers the rhs's own type, so the case is `lvar`'s minus
      -- the `envSet` — the guard is carried into `KontOk.asgnIvar`, which is where
      -- the *delivery* case will spend it.
      case ivar =>
        simp only [infer] at hinf
        split at hinf
        · next sc hsome =>
          split at hinf
          · next τr Γ₁ D₁ hrhs =>
            split at hinf
            · next σ hiv =>
              split at hinf
              · next hsub =>
                simp only [Option.some.injEq, Prod.mk.injEq] at hinf
                obtain ⟨rfl, rfl, rfl⟩ := hinf
                exact inv_push hfs htab hsc hhook hsat hstr hcls hbot (by simp [framePopLabels, hks]) hrhs
                  (KontOk.asgnIvar (by rw [hsome]; rfl) hsubw
                    (fun cn σ' hcn hiv' => by
                      rw [hsome, Option.some.injEq] at hcn
                      subst hcn
                      rw [hiv] at hiv'
                      simp only [Option.some.injEq] at hiv'
                      subst hiv'
                      exact hsub) hk)
              · exact absurd hinf (by simp)
            · next hiv =>
              simp only [Option.some.injEq, Prod.mk.injEq] at hinf
              obtain ⟨rfl, rfl, rfl⟩ := hinf
              exact inv_push hfs htab hsc hhook hsat hstr hcls hbot (by simp [framePopLabels, hks]) hrhs
                (KontOk.asgnIvar (by rw [hsome]; rfl) hsubw
                  (fun cn σ' hcn hiv' => by
                    rw [hsome, Option.some.injEq] at hcn
                    subst hcn
                    rw [hiv] at hiv'
                    exact absurd hiv' (by simp)) hk)
          · exact absurd hinf (by simp)
        · exact absurd hinf (by simp)
      -- **`$x = e`** (L228). `evalExpr` pushes the same `asgnK` the other two writes do,
      -- so the case is `ivar`'s with the guard replaced: the declared type rides on
      -- `KontOk.asgnGvar` and the *delivery* is where `GlobalsOk.set` spends it.
      case gvar =>
        simp only [infer] at hinf
        split at hinf
        · next hpg =>
          split at hinf
          · next τr Γ₁ D₁ hrhs =>
            split at hinf
            · next σ hgt =>
             split at hinf
             · next hsub =>
               simp only [Option.some.injEq, Prod.mk.injEq] at hinf
               obtain ⟨rfl, rfl, rfl⟩ := hinf
               exact inv_push hfs htab hsc hhook hsat hstr hcls hbot
                 (by simp [framePopLabels, hks]) hrhs
                 (KontOk.asgnGvar hpg hgt hsub hsubw hk)
             · exact absurd hinf (by simp)
            · exact absurd hinf (by simp)
          · exact absurd hinf (by simp)
        · exact absurd hinf (by simp)
      all_goals (simp only [infer] at hinf; contradiction)
    -- **`return e`** (L200), and the two arms are two different machines: with an
    -- expression the step pushes `jumpValK .retK` and the jump happens at the
    -- delivery; bare, `evalExpr` calls `doReturn` outright and the *jump* is the new
    -- control. Both spend `StackCtx`'s L198/L200 clause — a declared return type means
    -- a `.method` frame with a caller — which is what `returnTarget` reads.
    case ret e =>
      simp only [infer] at hinf
      split at hinf
      · next σ hret =>
        cases hst : m.stack with
        | nil => exact absurd hst hfsh.1
        | cons fid fids =>
          have hsc2 := hsc
          rw [hst] at hsc2
          rcases hsc2.2.2.2.2.2.1 with ⟨hkind, hcs⟩ | hnone
          · -- `Γs ≠ []`, and `fids ≠ []` with it: `StackCtx` pairs the two lists, so a
            -- non-empty context tail forces a non-empty frame tail.
            have hne : Γs ≠ [] := by
              intro hq; rw [hq] at hcs; simp at hcs
            have hfne : fids ≠ [] := by
              intro hq
              rw [hq] at hsc2
              have htl := hsc2.2.2.2.2.2.2
              cases hΓ : Γs.map Prod.fst with
              | nil => exact absurd hΓ hcs
              | cons a b => rw [hΓ] at htl; exact absurd htl (by simp [StackCtx])
            have hrt : Interp.returnTarget m = fid := by
              have hh : m.stack.headD 0 = fid := by rw [hst]; rfl
              simp only [Interp.returnTarget, hh, hkind]
            have hff : firstFrameK m.kont = some fid := by
              -- L245: the bridge runs through `RetOk`, not through the labels — a
              -- `blkFrameK` pops a frame `returnTarget` walks past, so the innermost
              -- *popping* kont is only the `frameK` when a `.retJ` can reach it.
              refine firstFrameK_of_retOk (KontOk.retOk hk hne σ hret)
                (rest := fids.dropLast) ?_
              rw [hks, hst, dropLast_cons_ne hfne]
            cases e with
            | some e' =>
              dsimp only at hinf
              cases he : infer D Γ e' Γs.isEmpty ctx with
              | none => rw [he] at hinf; exact absurd hinf (by simp)
              | some r =>
                obtain ⟨τe, Γ₁, D₁⟩ := r
                rw [he] at hinf
                dsimp only at hinf
                by_cases hsub : subTy τe σ = true
                · rw [if_pos hsub] at hinf
                  simp only [Option.some.injEq, Prod.mk.injEq] at hinf
                  obtain ⟨rfl, rfl, rfl⟩ := hinf
                  exact inv_push hfs htab hsc hhook hsat hstr hcls hbot
                    (by simpa [framePopLabels] using hks) he
                    (KontOk.retValK hret hsub hk)
                · rw [if_neg hsub] at hinf; exact absurd hinf (by simp)
            | none =>
              dsimp only at hinf
              by_cases hsub : subTy Ty.nilT σ = true
              · rw [if_pos hsub] at hinf
                simp only [Option.some.injEq, Prod.mk.injEq] at hinf
                obtain ⟨rfl, rfl, rfl⟩ := hinf
                simp only [evalExpr, Interp.doReturn, hrt,
                  show m.stack.contains fid = true from by simp [hst]]
                exact ⟨hhook, hsat, hstr, hcls, hbot, hks, hclo,
                  D, ctx, Γ, Γs, htab, hfs, hsc, hglob,
                  ⟨σ, Or.inr (Or.inr ⟨.nilT, rfl, hsub⟩), KontOk.retOk hk hne σ hret, hff⟩⟩
              · rw [if_neg hsub] at hinf; exact absurd hinf (by simp)
          · rw [hnone] at hret; exact absurd hret (by simp)
      · exact absurd hinf (by simp)
    -- **A bare `next`** (L227). `evalExpr` is one line — the control becomes the jump and
    -- nothing else moves — so the case is entirely about handing `CtlOk`'s new arm its
    -- four components, and three of them are the rule's own guards read back off `hinf`.
    -- The fourth is `KontOk.nxtOk`, which needs exactly the other two: the `inLoop`
    -- witness and `Γs ≠ []`, which is `top = false` (L226).
    case nxt e =>
      -- The value-carrying `next e` has no rule, so it is refuted by *computing* — and
      -- the `cases` has to come first, because the arm's pattern is `.nxt none` and
      -- `simp only [infer]` cannot fire on an unresolved `Option`.
      cases e with
      | some e' => exact absurd hinf (by simp [infer])
      | none =>
        simp only [infer] at hinf
        split at hinf
        · next htop =>
          split at hinf
          · next Γl hil =>
            split at hinf
            · next hse =>
              simp only [Option.some.injEq, Prod.mk.injEq] at hinf
              obtain ⟨rfl, rfl, rfl⟩ := hinf
              simp only [evalExpr]
              exact ⟨hhook, hsat, hstr, hcls, hbot, by simpa [withCtl] using hks, hclo,
                D, ctx, Γ, Γs, htab, hfs, hsc, hglob,
                ⟨Γl, hil, subEnvB_sound hse, by simpa using htop,
                  KontOk.nxtOk hk hil (by simpa using htop)⟩⟩
            · exact absurd hinf (by simp)
          · exact absurd hinf (by simp)
        · exact absurd hinf (by simp)
    case seq es =>
      simp only [infer] at hinf
      cases es with
      | nil =>
        simp only [inferSeq, Option.some.injEq, Prod.mk.injEq] at hinf
        obtain ⟨rfl, rfl, rfl⟩ := hinf
        exact inv_value hfs htab hsc hhook hsat hstr hcls hbot hks (ValueTy.weaken (ValueTy.exact rfl) hsubw) hk
      | cons e₁ rest =>
        cases rest with
        | nil =>
          simp only [inferSeq] at hinf
          exact inv_eval_sub hfs htab hsc hhook hsat hstr hcls hbot hks hinf hsubw hk
        | cons e₂ rest' =>
          simp only [inferSeq] at hinf
          split at hinf
          · rename_i σ Γ₁ h₁
            exact inv_push hfs htab hsc hhook hsat hstr hcls hbot (by simp [framePopLabels, hks]) h₁ (KontOk.seqCons hinf hsubw hk)
          · exact absurd hinf (by simp)
    case if' c t els =>
      simp only [infer] at hinf
      split at hinf
      · rename_i σ Γ₁ hcnd
        exact inv_push hfs htab hsc hhook hsat hstr hcls hbot (by simp [framePopLabels, hks]) hcnd (KontOk.ifK hinf hsubw hk)
      · exact absurd hinf (by simp)
    case while' c body =>
      simp only [infer] at hinf
      split at hinf
      · rename_i σ Γ₁ D₁ hcnd
        split at hinf
        · rename_i hΓ₁
          obtain ⟨rfl, rfl⟩ := hΓ₁
          split at hinf
          · rename_i σb Γ₂ D₂ hbody
            split at hinf
            · rename_i hΓ₂
              obtain ⟨rfl, rfl⟩ := hΓ₂
              simp only [Option.some.injEq, Prod.mk.injEq] at hinf
              obtain ⟨rfl, rfl, rfl⟩ := hinf
              -- L224: `c` is determined by `hcnd`'s own type (`infer`'s `.while'` arm names
              -- the loop's environment in the context it types the condition at), so it is
              -- left to unification rather than written out.
              exact inv_push hfs htab
                (stackCtx_inLoop hsc) hhook hsat hstr hcls hbot
                (by simp [framePopLabels, hks]) hcnd
                (KontOk.whileCond ⟨⟨σ, hcnd⟩, ⟨σb, hbody⟩⟩ hsubw hk)
            · exact absurd hinf (by simp)
          · exact absurd hinf (by simp)
        · exact absurd hinf (by simp)
      · exact absurd hinf (by simp)
    -- **Reopening a class** (F1b.6, L156). The step writes **no heap at all** —
    -- `enterClassBody`'s reopen branch is `pushFrame` and nothing else — which is
    -- the whole reason this rung comes before the allocating one: all six heap
    -- conjuncts carry across by `rfl`, and what is left is the frame push.
    case class' name sup body =>
      obtain ⟨htop, rfl, hmem, rfl, Γb, hbody⟩ := infer_class_inv hinf
      -- `Γs.isEmpty = true` is the mode `infer` was run at; `FramesOk` turns it into
      -- a singleton frame stack and `BottomObj` names that frame's definee. This is
      -- the composite L155 exists for.
      have hΓs : Γs = [] := List.isEmpty_iff.mp htop
      subst hΓs
      -- L236: the slack, consumed before the push — the caller's environment on the
      -- new stack is the one the continuation was registered at.
      have hfs := FramesOk.narrowHead hsuE hfs
      obtain ⟨fid₀, hst⟩ := hfs.stack_singleton
      have hdefmod : m.currentFrame.defmod = Boot.objectId := by
        rw [currentFrame_eq hfsh.1]; exact BottomObj_curFrame hst hbot
      -- `ClassOk` at this name: the constant is there, it is a class, and it is not
      -- a module — the three tests `enterClassBody` applies before `pushFrame`.
      obtain ⟨k, cp, hconst, hpay, hnm, huniq, -, -, -, hreop⟩ :=
        hcls.2.2 name (readable_of_reopenable (List.mem_of_elem_eq_true hmem))
      obtain ⟨hmod, -, -⟩ := hreop (List.mem_of_elem_eq_true hmem)
      -- **L189: the enclosing frame's lexical scope**, which the pushed frame
      -- inherits because `enterClassBody` *prepends*.
      have hcrefCur : Boot.objectId ∈ m.currentFrame.cref := by
        rw [show m.currentFrame = m.frames.getD fid₀ default by
          simp [Machine.currentFrame, hst]]
        rw [hst] at hsc
        exact hsc.2.2.2.2.1
      simp only [evalExpr, enterClassBody, hdefmod, hconst, hpay, hmod, withKont]
      -- What is left is `pushFrame`, and it is a frame push on an untouched heap.
      have hlt : ∀ g ∈ m.stack, g < m.frames.size := hfs.mem_lt
      refine ⟨hhook, hsat, hstr, hcls,
        BottomObj_cons hfsh.1 (BottomObj_push hlt hbot),
        (by simp [framePopLabels, hks, dropLast_cons_ne hfsh.1]),
        (ClosuresOk.pushFrame hclo rfl rfl rfl),
        D, { cls := name }, [], [(ctx, Γk)],
        htab, ?_, ?_, hglob, ?_⟩
      · -- `FrameConforms` at the class-body frame: no captured chain (the literal
        -- leaves the field at its default), the definee is a class — which is
        -- exactly `ClassOk`'s second conjunct, and is what L154 generalized this
        -- clause to admit — and the empty environment types nothing.
        refine ⟨by rw [Array.size_push]; exact Nat.lt_succ_self _, hlt,
          ⟨ShallowChain.of_none (by rw [getD_push_lt_self]; try rfl), ?_, ?_⟩, FramesOk.push hfs⟩
        · rw [getD_push_lt_self]; simp [hpay]
        · intro y σ hy; exact absurd hy (by simp [envGet?])
      -- **The class-body frame's static context is the class's own name** (F1b.9),
      -- and this is where `ClassOk`'s new clause is spent: the definee is the object
      -- the constant names, and that object is named `name`. `defVis` comes out of
      -- the frame literal's default, which is what makes a `def` in this body public
      -- where a toplevel one is private.
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, (fun hcb _ => nomatch hcb), StackCtx.push hlt hsc⟩
        · rw [getD_push_lt_self]; simp [hpay]
        · rw [getD_push_lt_self]; exact fun _ => hnm
        · rw [getD_push_lt_self]; exact fun _ => rfl
        -- A class body's `self` is the **class object**, which `plainRecv`
        -- excludes, so the context claims no self type and the clause is vacuous.
        · exact fun sc hsc' => absurd hsc' (by simp)
        -- **L189: `enterClassBody` *prepends* the class to the enclosing cref**
        -- (`Interp/Dispatch.lean:224`), so `Object`'s membership is inherited from
        -- the frame this one was pushed from — which is the whole reason the clause
        -- is a membership rather than a shape.
        · rw [getD_push_lt_self]
          exact List.mem_cons_of_mem _ hcrefCur
        -- L198: a class body declares no return type, so the clause is vacuous on the
        -- right — the honest reading, since `return` there has no target.
        · exact Or.inr rfl
        -- L207: and it names no method, for the same reason.
        · exact fun mn h => absurd h (by simp)
        -- L243: the class-body frame literal leaves `captured` at its default.
        · rw [getD_push_lt_self]; exact fun _ => rfl
      -- The class body's own table `Db` is the index the *callee's* continuation
      -- carries; `frameK` carries one table, which the rule's stability condition
      -- is what pays for.
      · exact ⟨τ, τw, Γb, D', _, hbody, hsubw, SubEnv.refl _,
          KontOk.frameK (fun _ h => by simp at h) rfl hk⟩
    case def' name params body =>
      obtain ⟨rfl, rfl, rfl, hfresh, hha, τb, Γb, hbody, hrow⟩ := infer_def_inv hinf
      have hdm : m.currentFrame = curFrame m := currentFrame_eq hfsh.1
      -- L154: the definee is *a class* rather than *`Object`*, which is what makes a
      -- class-body frame expressible. Every `defineMethod` lemma below is already
      -- stated `∀ cls`, so the generalization costs nothing here — the equation was
      -- only ever used to instantiate `NoHook` at the definee, and `NoHook` is now
      -- quantified over exactly the class objects this predicate names.
      have hdo : (m.heap.classPayload? (curFrame m).defmod).isSome := by
        cases hst : m.stack with
        | nil => exact absurd hst hfsh.1
        | cons fid _ =>
          have hfc : FrameConforms m.heap m.frames Γ' fid := by
            rw [hst] at hfs; exact hfs.2.2.1
          simpa [curFrame, curFid, hst] using hfc.2.1

      -- `hlk` is the raw lookup equation, because `simp` needs it to collapse
      -- `evalExpr`'s hook `match`; `hlkNH` is the invariant's clause, which since L149
      -- also carries `Boot.objectId < objs.size` — preserved because `set!` does not
      -- resize.
      have hlkNH : ∀ md : MethodDef,
          NoHook (defineMethod m.heap (curFrame m).defmod name md) :=
        fun _ => NoHook_defineMethod hhook hha
      -- L153/L154: one *instance* of the generalized clause, at the definee the frame
      -- names. That the definee is a class is `hdo`, and `classPayload?` is unmoved by
      -- a method-table write.
      have hlk : ∀ md : MethodDef,
          lookup (defineMethod m.heap (curFrame m).defmod name md)
            (.ref (curFrame m).defmod) "method_added" = none := fun md =>
        (hlkNH md).2 (curFrame m).defmod
          (by rw [classPayload?_isSome_defineMethod]; exact hdo)
          "method_added" (by simp [hookFreeNames])
      -- Quantified over `md` so the `MethodDef` literal `evalExpr` builds never
      -- has to be written out, and over `m₀` so the `preludeMode` branch — which
      -- differs only in fields `Inv` does not mention — is discharged by the same
      -- argument. (There used to be a `reprSensitive` branch here too; L103
      -- retired the global `reprPure` flag for a per-class test, so `def` no longer
      -- touches it. This proof kept case-splitting on a constant that no longer
      -- exists, and `Proof/` being off the default build target is why that went
      -- unnoticed from L103 until now — L119.)
      -- Phrased over the *facts* about `m₀.heap` rather than over the
      -- `MethodDef` that produced it: `m₀` is then fixed by unifying the
      -- conclusion with the goal, and each remaining hypothesis is a concrete
      -- goal whose `md` unification is forced. Quantifying over `md` instead
      -- leaves it an unsolvable metavariable.
      -- L137 added the fourth hypothesis, `TypeAgree`: with the judgement
      -- heap-indexed, the `ValueTy` facts stored in the frames and in the
      -- continuation stack have to be *transported* into the post-`def` heap
      -- rather than reused. `defineMethod` supplies it
      -- (`typeAgree_defineMethod`), which is the whole reason `TypeAgree` is
      -- phrased over `classOf`/`className`/`classPayload?` and not over the
      -- method table.
      have hres : ∀ (m₀ : Machine),
          m₀.frames = m.frames → m₀.stack = m.stack → m₀.kont = m.kont →
          TypeAgree m.heap m₀.heap → DeclsOk D' m₀.heap → NoHook m₀.heap →
          Saturated m₀.heap → LitClsOk m₀.heap → ClassOk m₀.heap →
          -- **L228: and the globals**, at the *grown* table — which is free, because
          -- `addRow` writes `rows` and `defineMethod` writes the method table, so both
          -- the lookup and the association list are the ones this step started with.
          GlobalsOk D' m₀.heap m₀.globals →
          Inv (withCtl m₀ (.value (.sym name))) := by
        intro m₀ hfr hst hko hag ht' hh' hsat' hstr' hcls' hgl'
        refine ⟨hh', hsat', hstr', hcls',
          show BottomObj m₀.frames m₀.stack by rw [hfr, hst]; exact hbot,
          show framePopLabels m₀.kont = m₀.stack.dropLast by rw [hko, hst]; exact hks,
          ClosuresOk.transport hclo
            (by intro κ hm cl hcl; simp only [withCtl, hko] at hm; exact ⟨κ, hm, hcl⟩)
            (by simp only [withCtl]; rw [hfr]; exact Nat.le_refl _)
            (by intro p _; simp only [withCtl]; rw [hfr]; exact FrameShape.rfl' _)
            (by
              intro o ho
              show (m₀.heap.classPayload? o).isSome = true
              exact (hag.2.2.1 o (classPayload?_isSome_lt ho)) ▸ ho),
          D', ctx, Γ', Γs, ht', ?_, ?_, hgl', ?_⟩
        · show FramesOk m₀.heap m₀.frames m₀.stack (Γ' :: Γs.map Prod.snd)
          rw [hfr, hst]; exact FramesOk.heap_congr hag hfs
        · show StackCtx m₀.heap m₀.frames m₀.stack (ctx :: Γs.map Prod.fst)
          rw [hfr, hst]; exact StackCtx.heap_congr hag hsc
        · show ∃ σ Γk', ValueTy m₀.heap (Value.sym name) σ ∧ SubEnv Γk' Γ' ∧
              KontOk D' m₀.heap ((ctx, Γk') :: Γs) σ m₀.kont
          exact ⟨_, _, ValueTy.weaken (ValueTy.exact rfl) hsubw, hsuE,
            by rw [hko]; exact KontOk.heap_congr hag hk⟩
      -- `hlk` collapses the hook lookup to `none`, after which only the
      -- `preludeMode` `if` remains.
      simp only [evalExpr, hdm]
      -- `split` would dive into the `visibility` `if`s *inside* the `MethodDef`
      -- literal, which `hres` deliberately abstracts over; case on the one
      -- condition that matters instead.
      -- **The declaration obligation** (F1b.10), and it is the only conjunct that
      -- distinguishes the two branches of the rule. Without a row `DeclsOk` is
      -- `DeclsOk_defineMethod` exactly as before; with one it is `DeclsOk_addRow`,
      -- whose single new obligation is the row's own `EntryOk` — discharged by the
      -- **user** arm, which makes this the first commit in which that arm is
      -- inhabited (L157 built it and left it empty).
      rcases hrow with rfl | ⟨rfl, htopf, hinit, hmemctx, hdf⟩
      · by_cases hp : m.preludeMode = true <;>
          simp only [hp, if_true, if_false, Bool.false_eq_true, hlk] <;>
          refine hres _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
            first
              | rfl
              | exact typeAgree_defineMethod _ _ _ _
              | exact DeclsOk_defineMethod htab hfresh
              | exact hlkNH _
              | exact Saturated_defineMethod hsat _ _ _
              | exact LitClsOk_defineMethod hstr
              | exact ClassOk_defineMethod hcls
              -- L228: the globals conjunct, and the *same* term in both branches —
              -- `addRow`'s table has the same `globals` field by `rfl`.
              | exact GlobalsOk.congr (typeAgree_defineMethod _ _ _ _) hglob
      -- The row branch. Three facts about the *current frame* are wanted, and all
      -- three come from `StackCtx` — which is what that predicate was added for.
      · obtain ⟨fid₀, fids₀, hst⟩ : ∃ fid fids, m.stack = fid :: fids := by
          cases hst : m.stack with
          | nil => exact absurd hst hfsh.1
          | cons a r => exact ⟨a, r, rfl⟩
        have hΓs : Γs ≠ [] := by
          intro hz; rw [hz] at htopf; exact absurd htopf (by simp)
        have hfidsne : fids₀ ≠ [] := by
          intro hz
          rw [hst, hz] at hfs
          cases hΓ : Γs with
          | nil => exact absurd hΓ hΓs
          | cons a r => rw [hΓ] at hfs; exact absurd hfs.2.2.2 (by simp [FramesOk])
        have hscc : StackCtx m.heap m.frames (fid₀ :: fids₀) (ctx :: Γs.map Prod.fst) := by
          rw [hst] at hsc; exact hsc
        -- L249: the name clause is guarded on the block flag, and the `def` rule's row
        -- carries the matching guard — so `hctx` is a function of it, applied where the
        -- row is built.
        have hctx : ctx.inBlock = false → className m.heap (curFrame m).defmod = ctx.cls := by
          intro hnb
          rw [show curFrame m = m.frames.getD fid₀ default by
            simp [curFrame, curFid, hst]]
          exact hscc.2.1 hnb
        have hvis : defVisOfDef (curFrame m) = .pub := by
          rw [show curFrame m = m.frames.getD fid₀ default by
            simp [curFrame, curFid, hst]]
          exact hscc.2.2.1 hfidsne
        -- **L189: the defining frame's lexical scope contains `Object`**, which is
        -- what the row's `ResolvesUser` has to carry across a later call, since
        -- `evalExpr` copies `cref` into the `MethodDef` it installs.
        have hcrefCur : Boot.objectId ∈ m.currentFrame.cref := by
          rw [show m.currentFrame = m.frames.getD fid₀ default by
            simp [Machine.currentFrame, hst]]
          exact hscc.2.2.2.2.1
        -- The chain from the definee starts at the definee, which is what makes the
        -- entry the step just wrote the one `lookup` finds.
        have hchain : ∀ md : MethodDef, ∃ rest,
            ancestors (defineMethod m.heap (curFrame m).defmod name md)
              (curFrame m).defmod = (curFrame m).defmod :: rest := by
          intro md
          obtain ⟨k₀, cp, _, _, hnm₀, huniq₀, _, _, _, hreop₀⟩ :=
            (ClassOk_defineMethod (name := name) (md := md)
              (cls := (curFrame m).defmod) hcls).2.2 ctx.cls
              (readable_of_reopenable (List.mem_of_elem_eq_true hmemctx))
          obtain ⟨-, hhead₀, -⟩ := hreop₀ (List.mem_of_elem_eq_true hmemctx)
          have hdefk : (curFrame m).defmod = k₀ :=
            huniq₀ _ (by rw [classPayload?_isSome_defineMethod]; exact hdo)
              (by rw [className_defineMethod]; exact hctx hdf.2.2)
          rw [hdefk] at hdo hhead₀ ⊢
          cases hanc : ancestors (defineMethod m.heap k₀ name md) k₀ with
          | nil => rw [hanc] at hhead₀; exact absurd hhead₀ (by simp)
          | cons a rest =>
            rw [hanc] at hhead₀
            simp only [List.head?_cons, Option.some.injEq] at hhead₀
            exact ⟨rest, by rw [hhead₀]⟩
        have hdecls : ∀ (md : MethodDef), md.owner = (curFrame m).defmod →
            md.builtin = none → md.undefined = false → md.visibility = .pub →
            md.params = [] → md.declared = [] → md.capturedFrame = none →
            md.body = body → Boot.objectId ∈ md.cref → md.superName = none →
            DeclsOk (addRow D ctx.cls name { params := [], ret := τb })
              (defineMethod m.heap (curFrame m).defmod name md) := by
          intro md hown hb hu hvs hpar hdec hcap hbd hcref hsn
          refine DeclsOk_addRow htab hfresh ?_ ?_
          · -- **The row is not at a ground type**, and since L189 that is a *rule*
            -- guard rather than a consequence of `reopenableClasses` membership:
            -- the table grew to eight names, five of which are exactly the ground
            -- classes. `tyClassNames` subtracts those from the class arm's range, so
            -- a row on one would owe `EntryOk` over immediates — which is why the
            -- `def` rule now tests it and this is a hypothesis rather than a
            -- computation.
            exact hdf.1
          obtain ⟨k₀, cp, _, _, hnm₀, huniq₀, _, _, _, _⟩ :=
            (ClassOk_defineMethod (name := name) (md := md)
              (cls := (curFrame m).defmod) hcls).2.2 ctx.cls
              (readable_of_reopenable (List.mem_of_elem_eq_true hmemctx))
          have hctx' : className (defineMethod m.heap (curFrame m).defmod name md)
              (curFrame m).defmod = ctx.cls := by rw [className_defineMethod]; exact hctx hdf.2.2
          have hdefk : (curFrame m).defmod = k₀ :=
            huniq₀ _ (by rw [classPayload?_isSome_defineMethod]; exact hdo) hctx'
          obtain ⟨rest, hrest⟩ := hchain md
          refine Or.inr (Or.inl ⟨md, ctx.cls, UserKey.cls, fun k htc => ?_,
            by rw [hown]; exact hctx', rfl,
            rfl, by rw [hbd]; exact hdf.2.1, ?_⟩)
          -- L241: the row's key is `UserKey.cls` — the type names exactly its class, which
          -- is what lets a *call* recover the class the body was checked in (F1b.11). It
          -- used to be `rfl` at an equation; the relation's first shape is that equation.
          · have hk : k = (curFrame m).defmod := by
              rw [hdefk]; exact huniq₀ k htc.1 htc.2
            subst hk
            refine ⟨(curFrame m).defmod, ?_, hb, hu, hvs, hpar, hdec, hcap,
              by rw [hown, classPayload?_isSome_defineMethod]; exact hdo, ?_, hcref,
              -- L209: the definee is the head of its own chain (`ClassOk`'s reopen
              -- clause, already destructured as `hrest`), and `md.owner` *is* the
              -- definee at the step that installs it — so `super`'s chain clause is
              -- free here and needs no new fact about `lookup`.
              by rw [hown, hrest]; exact List.mem_cons_self ..,
              -- L210: the literal `evalExpr` installs leaves `superName` at its default
              -- — only `alias` sets it — so the activation's `meth` is the plain name,
              -- which is the one the body's context was checked at.
              hsn⟩
            · show lookup.go _ name (ancestors _ _) = _
              rw [hrest]
              exact lookup_go_defineMethod_self m.heap _ name md hdo rest
            · split
              · rfl
              · rw [hrest]
                simp only [List.takeWhile, bne_self_eq_false, decide_false,
                  Bool.false_eq_true, if_false]
                rfl
          · -- L198: the `def` rule supplies `r = none`, which is exactly *this body
            -- contains no `return`* — see `UserConforms`.
            -- L229: the `def` rule's row carries the body's *own* type, so the new
            -- `subTy` conjunct is reflexivity — a `def` declares exactly what it infers,
            -- and it is the *declared* signature (W8's `sig`) that can be wider.
            exact ⟨Γb, none, τb,
              by rw [hbd]; exact infer_mono (subDecls_addRow hfresh) hdf.2.1 hbody,
              subTy_refl _, fun σ h => absurd h (by simp)⟩
        by_cases hp : m.preludeMode = true <;>
          simp only [hp, if_true, if_false, Bool.false_eq_true, hlk] <;>
          refine hres _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
            first
              | rfl
              | exact typeAgree_defineMethod _ _ _ _
              -- The literal's `visibility` is `defVisOfDef` once the name is not
              -- `initialize`, and `StackCtx` says that is `.pub` on any frame that
              -- is not the outermost — which `top = false` is exactly.
              | exact hdecls _ rfl rfl rfl
                  (by simpa [defVisOfDef, hinit] using hvis) rfl rfl rfl rfl
                  (by simpa [hdm] using hcrefCur) rfl
              | exact hlkNH _
              | exact Saturated_defineMethod hsat _ _ _
              | exact LitClsOk_defineMethod hstr
              | exact ClassOk_defineMethod hcls
              -- L228: the globals conjunct, and the *same* term in both branches —
              -- `addRow`'s table has the same `globals` field by `rfl`.
              | exact GlobalsOk.congr (typeAgree_defineMethod _ _ _ _) hglob
    -- **An array literal** (L174). Two shapes, and they are the two `continueArray`
    -- has: an empty literal allocates *in this step* (so the case is L151's string
    -- literal verbatim, at `Boot.arrayId`), and a non-empty one pushes an `arrK`
    -- and evaluates its head.
    case array es =>
      simp only [infer] at hinf
      split at hinf
      · next τ0 Γ0 D0 hseq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hinf
        obtain ⟨rfl, rfl, rfl⟩ := hinf
        simp only [evalExpr]
        exact inv_continueArray hfs htab hsc hhook hsat hstr hcls hbot hks hglob
          hseq hsubw hk
      · exact absurd hinf (by simp)
    -- **`super(args)`** (L212). Two shapes, and they are the *receiverless send*'s two
    -- shapes with the receiver replaced by the frame's own `self`: with no arguments
    -- `startSuperArgs` is `doSuper` outright, and with one the machine pushes a
    -- `superArgK` and runs the argument.
    --
    -- Everything `super_dispatch` wants about the frame is a `StackCtx` clause, and the
    -- clause that does the work is L209's: without `defmod ∈ ancestors (classOf self)`
    -- the `dropWhile` empties the list and `doSuper` raises `NoMethodError`.
    case super' args blk =>
      cases blk with
      | some b => exact absurd hinf (by simp [infer])
      | none =>
        -- The frame facts, read off `StackCtx` once and shared by both shapes.
        cases hst : m.stack with
        | nil => exact absurd hst hfsh.1
        | cons fid fids =>
          have hsc' := hsc
          rw [hst] at hsc'
          have hcur : m.frames.getD fid default = m.frames.getD (methodFrameOf m) default := by
            have hkd : (m.frames.getD fid default).kind = .method := by
              cases hmn : ctx.meth with
              | none =>
                -- Both rules require `ctx.meth = some mn`, so this branch is refuted by
                -- the rule rather than by the machine.
                exfalso
                cases args with
                | nil => obtain ⟨-, -, mn, dd, hm, -, -, -, -⟩ := infer_super0_inv hinf
                         rw [hmn] at hm; exact absurd hm (by simp)
                | cons a r => obtain ⟨mn, -, -, hm, -, -, -, -, -⟩ := infer_super_inv hinf
                              rw [hmn] at hm; exact absurd hm (by simp)
              | some mn => exact (hsc'.2.2.2.2.2.2.1 mn hmn).2.1
            simp only [methodFrameOf, hst, List.headD_cons, hkd]
          have hcls' : ∀ mn, ctx.meth = some mn →
              (m.frames.getD (methodFrameOf m) default).meth = mn ∧
              (m.heap.classPayload?
                (m.frames.getD (methodFrameOf m) default).defmod).isSome ∧
              className m.heap (m.frames.getD (methodFrameOf m) default).defmod = ctx.cls ∧
              (m.frames.getD (methodFrameOf m) default).defmod ∈
                ancestors m.heap
                  (classOf m.heap (m.frames.getD (methodFrameOf m) default).self) ∧
              ValueTy m.heap (m.frames.getD (methodFrameOf m) default).self
                (.cls ctx.cls) := by
            intro mn hmn
            obtain ⟨hm, -, hself, -, -, -, hnb⟩ := hsc'.2.2.2.2.2.2.1 mn hmn
            obtain ⟨hty, hch⟩ := hsc'.2.2.2.1 ctx.cls hself
            rw [← hcur]
            exact ⟨hm, hsc'.1, hsc'.2.1 hnb, hch, hty⟩
          cases args with
          | nil =>
            obtain ⟨rfl, rfl, mn, dd, hmn, hne, hrow, hps, rfl⟩ := infer_super0_inv hinf
            obtain ⟨hm, hdp, hdn, hch, hty⟩ := hcls' mn hmn
            obtain ⟨w, m', hw, hg', hfr', hst', hko', hgv', hstep⟩ :=
              super_dispatch (m := m) (args := []) (blk := methodBlk m) hne
                (htab.2.2.2.2 _ _ _ hrow) hm hdp hdn hch hty (by rw [hps]; trivial)
            simp only [evalExpr, startSuperArgs]
            rw [hstep]
            exact inv_grow_value hfs htab hsc hhook hsat hstr hcls hbot hks
              hg' hfr' hst' hko' (ValueTy.weaken hw hsubw) hk hglob hgv'
          | cons arg extra =>
            obtain ⟨mn, τs, dd, hmn, hne, hargs, hrow, hsub, rfl⟩ := infer_super_inv hinf
            obtain ⟨τe, Γ₁, D₁, τrest, rfl, he, hrest⟩ := inferArgs_cons_inv hargs
            obtain ⟨τp, psrest, hpeq, hs1, hs2⟩ := subTys_cons_inv hsub
            have hsp : ∀ e, arg ≠ .splat e := by
              rintro e rfl; exact absurd he (by simp [infer])
            have hkw : ∀ es, arg ≠ .kwargs es := by
              rintro es rfl; exact absurd he (by simp [infer])
            have hfw : arg ≠ .fwd := by
              rintro rfl; exact absurd he (by simp [infer])
            simp only [evalExpr]
            rw [startSuperArgs_plain hsp hkw hfw]
            exact inv_push hfs htab hsc hhook hsat hstr hcls hbot
              (by simp [framePopLabels, hks]) he
              (KontOk.superArgsK (psacc := []) trivial hs1 hrest hs2 hmn hne hrow
                hpeq rfl hsubw hk)
    -- **Bare `super`** (L214), and it is the *cheapest* of the three dispatch cases:
    -- `evalExpr` reconstructs the arguments from the frame and calls `doSuper` in this
    -- step, so there is no continuation, no `inferArgs` and no argument to run.
    --
    -- The whole case is `StackCtx`'s L214 clause spent twice: once to compute
    -- `zsuperArgs` (`runParams = []` and `runFromDM = false` make `zsuperArgsOf` answer
    -- `some ([], [])` by computation, so the interpreter's own `none` branches — a
    -- `define_method` body, destructuring parameters — are refuted rather than handled),
    -- and once to know the declared parameter list is `[]`, which is what makes
    -- `ValuesTy` of the reconstructed arguments hold.
    case zsuper blk =>
      cases blk with
      | some b => exact absurd hinf (by simp [infer])
      | none =>
        obtain ⟨rfl, rfl, mn, ps, dd, hmn, hpar', hne, hrow, hsub, rfl⟩ := infer_zsuper_inv hinf
        cases hst : m.stack with
        | nil => exact absurd hst hfsh.1
        | cons fid fids =>
          have hsc' := hsc
          rw [hst] at hsc'
          obtain ⟨hm, hkd, hself, hrp, hdm, hpar, hnb⟩ := hsc'.2.2.2.2.2.2.1 mn hmn
          obtain ⟨hty, hch⟩ := hsc'.2.2.2.1 ctx.cls hself
          have hcur : m.frames.getD fid default
              = m.frames.getD (methodFrameOf m) default := by
            simp only [methodFrameOf, hst, List.headD_cons, hkd]
          rw [hcur] at hm hrp hdm
          -- `zsuperArgs` answers `some ([], [])`: the name is non-empty, the body is not
          -- a `define_method` one, and an empty parameter list has no shape to fail on.
          have hza : zsuperArgs m = some ([], []) := by
            simp only [zsuperArgs, zsuperArgsOf, hm, hrp, hdm, classifyFull]
            simp [hne]
          obtain ⟨w, m', hw, hg', hfr', hst', hko', hgv', hstep⟩ :=
            super_dispatch (m := m) (args := []) (blk := methodBlk m) hne
              (htab.2.2.2.2 _ _ _ hrow) hm (hcur ▸ hsc'.1) (hcur ▸ hsc'.2.1 hnb) (hcur ▸ hch)
              (hcur ▸ hty)
              -- `StackCtx` pins the activation's parameter list to `some []`, so the
              -- rule's `ps` is `[]` and `subTys [] dd.params` forces the row's to be too.
              (by
                have : ps = [] := by rw [hpar] at hpar'; simpa using hpar'.symm
                rw [show dd.params = [] from subTys_nil_inv (this ▸ hsub)]; trivial)
          simp only [evalExpr, hza]
          rw [hstep]
          exact inv_grow_value hfs htab hsc hhook hsat hstr hcls hbot hks
            hg' hfr' hst' hko' (ValueTy.weaken hw hsubw) hk hglob hgv'
    case send recv mname args blk =>
      cases recv with
      -- **The written receiverless call** (L170). `evalExpr` answers
      -- `startArgs m self .implicit mname [] args` with no continuation pushed, so
      -- for `args = []` this is `finishSend` and `inv_implicit_send0` — L164's
      -- `vcall` argument, quantified over the site — closes it at `.implicit`.
      -- Every other receiverless shape is still refused by the rule.
      | none =>
        cases args with
        -- **The unary written receiverless call** (L171). `startArgs` pushes
        -- `.argsK self .implicit mname [] []` and evaluates the argument — the same
        -- continuation the explicit unary send reaches one step later, at a
        -- different site, which is why `KontOk.argsK` gained a site *parameter*
        -- rather than a sibling constructor. There is no `recvK` in this chain: the
        -- receiver is already a value, so the argument's environment and table are
        -- the rule's answer and `CtlOk` hands `argsK` exactly the indices it wants.
        | cons arg extra =>
          cases blk with
          | some b => exact absurd hinf (by simp [infer])
          | none =>
            obtain ⟨c, τs, ps, hsome, hargs, hsg, hsub⟩ := infer_implicit_send1_inv hinf
            obtain ⟨τe, Γ₁, D₁, τrest, rfl, he, hrest⟩ := inferArgs_cons_inv hargs
            obtain ⟨τp, psrest, rfl, hs1, hs2⟩ := subTys_cons_inv hsub
            have hself : ValueTy m.heap m.currentFrame.self (.cls c) := by
              cases hst : m.stack with
              | nil => exact absurd hst hfsh.1
              | cons fid fids =>
                rw [hst] at hsc
                have := hsc.2.2.2.1 c hsome
                rw [show m.currentFrame = m.frames.getD fid default by
                  simp [Machine.currentFrame, hst]]
                exact this.1
            have hsp : ∀ e, arg ≠ .splat e := by
              rintro e rfl; exact absurd he (by simp [infer])
            have hkw : ∀ es, arg ≠ .kwargs es := by
              rintro es rfl; exact absurd he (by simp [infer])
            have hfw : arg ≠ .fwd := by
              rintro rfl; exact absurd he (by simp [infer])
            simp only [evalExpr]
            rw [startArgs_plain hsp hkw hfw]
            exact inv_push hfs htab hsc hhook hsat hstr hcls hbot (by simp [framePopLabels, hks]) he
              (KontOk.argsK (psacc := []) hself trivial hs1 hrest hs2
                (by simpa using hsg) hsubw hk)
        | nil =>
          cases blk with
          | some b =>
            -- **L261's lambda literal.** The step is `reifyBlock` and nothing else, so the
            -- case is `inv_grow_value` at the allocation L257 already priced — and the
            -- value's type is `.any`, which every value satisfies, so there is nothing to
            -- prove about *what was allocated*. That is the whole content of the rule: the
            -- type language cannot name a `Proc`, and this is what that costs and buys.
            cases b with
            | block ps ls body =>
              simp only [infer] at hinf
              split at hinf
              · next hlam =>
                simp only [beq_iff_eq] at hlam
                subst hlam
                simp only [Option.some.injEq, Prod.mk.injEq] at hinf
                obtain ⟨rfl, rfl, rfl⟩ := hinf
                show StepOk (startArgs m m.currentFrame.self .implicit "lambda" [] []
                  (.lit ps ls body))
                rw [startArgs_lambda, reifyBlock_eq]
                exact inv_grow_value hfs htab hsc hhook hsat hstr hcls hbot hks
                  (plainGrow_alloc m.heap _ (by simp) rfl) rfl rfl rfl
                  (ValueTy.weaken ValueTy.any hsubw) hk
              · exact absurd hinf (by simp)
            | _ => exact absurd hinf (by simp [infer])
          | none =>
            simp only [infer] at hinf
            split at hinf
            · next c hsome =>
              split at hinf
              · next τret hsg =>
                simp only [Option.some.injEq, Prod.mk.injEq] at hinf
                obtain ⟨rfl, rfl, rfl⟩ := hinf
                simp only [evalExpr]
                exact inv_implicit_send0 hfs htab hsc hhook hsat hstr hcls hbot hks hfsh.1
                  hsome hsg hsubw hk
              · exact absurd hinf (by simp)
            · exact absurd hinf (by simp)
      | some r =>
        cases args with
        -- **The zero-argument send** (L152). Same `evalExpr` step as the unary one —
        -- push `recvK` and evaluate the receiver — and the whole difference lands one
        -- step later, in `applyKont`.
        | nil =>
          cases blk with
          | some b =>
            -- **L257: a *literal block*, and the receiver still runs first.** The step is
            -- the blockless one — `evalExpr` pushes a `recvK` — and the whole difference
            -- is the `PendingBlk` it carries, which `KontOk.recvKBlk` is indexed by.
            cases b with
            | block bps bls bbody =>
              obtain ⟨τr, x, σp, βret, τb, Γb', hr, hbs, hbody, hsb, hse, hib⟩ :=
                infer_sendBlk_inv hinf
              simp only [evalExpr]
              cases r <;>
                exact inv_push hfs htab hsc hhook hsat hstr hcls hbot
                  (by simp [framePopLabels, hks]) hr
                  (KontOk.recvKBlk hbs hbody (subEnvB_sound hse) hsb hsubw hib hk)
            | _ => exact absurd hinf (by simp [infer])
          | none =>
            obtain ⟨τr, hr, hsg⟩ := infer_send0_inv hinf
            simp only [evalExpr]
            -- **The receiver is still case-split, and the site is no longer**
            -- (L172). `evalExpr` picks the site by matching on the receiver
            -- *expression*, and that match will not rewrite under `rw` — so the
            -- split stays. What went away is the branch that had to be refuted:
            -- `KontOk.recvK0` takes the site as a parameter, so `self` is one more
            -- uniform branch rather than the rule's excluded case.
            cases r <;>
              exact inv_push hfs htab hsc hhook hsat hstr hcls hbot (by simp [framePopLabels, hks]) hr (KontOk.recvK0 hsg hsubw hk)
        | cons arg extra =>
          cases blk with
          | some b =>
            -- **L259's arity-`n` block send, refuted by the *table*** — and that is the
            -- honest refutation. The rule is real, but a block-taking row is admissible
            -- only through `IterEntryOk` (`EntryOk.iter`), which pins the declaration's
            -- parameter list to `[]`; this send has arguments, so no declaration the
            -- invariant admits can fire it. When a future `EntryOk` arm supplies a
            -- block-taking row *with* parameters, this line becomes work.
            exfalso
            obtain ⟨τr, d, σp, βret, hd, hdps, hdb⟩ := infer_sendBlkN_decl hinf
            exact hdps ((htab.1 τr mname d hd).iter hdb).2.2.1
          | none =>
            obtain ⟨τr, Γ₁, D₁, τs, ps, hr, hargs, hsg, hsub⟩ := infer_send_inv hinf
            -- `evalExpr` picks the send site by matching on the receiver
            -- *expression*, and that match will not rewrite under `rw`, so
            -- force it to compute. Since L172 every branch — `self` included —
            -- is the same `KontOk.recvK`, at whichever site the match produces.
            simp only [evalExpr]
            cases r <;>
              exact inv_push hfs htab hsc hhook hsat hstr hcls hbot (by simp [framePopLabels, hks]) hr
                (KontOk.recvK hargs hsg hsub hsubw hk)
  · -- ## control = value v
    rw [hctl] at hc
    obtain ⟨τ, Γk, hv, hsuE, hk⟩ := hc
    -- **The environment slack, consumed once** (L236). The continuation was registered
    -- at `Γk`, which `SubEnv Γk Γ` says is contained in the environment the machine's
    -- locals conform to — so `FramesOk.narrowHead` moves the *runtime* conformance down
    -- to `Γk`, and every delivery case below then runs at the environment its own kont
    -- was built at. One narrowing at the top of the block is the whole cost of the slack
    -- on the value side; the `if` rung needs it because a branch runs at an environment
    -- *wider* than the join the continuation was registered at.
    have hfs := FramesOk.narrowHead hsuE hfs
    simp only [stepFn, hctl]
    unfold applyKont
    generalize hK : m.kont = K at hk hks ⊢
    cases hk with
    | nil => trivial
    | @seqNil _ _ _ _ _ _ τw k _ hsw hk' hsu =>
      exact inv_value hfs htab hsc hhook hsat hstr hcls hbot (by simpa [framePopLabels] using hks) (ValueTy.weaken hv hsw) hk' (hclo := hcloTail hK)
    | @seqCons _ _ _ _ _ _ _ e₁ es τ' τw Γ' k _ hseq hsw hk' hsu =>
      cases es with
      | nil =>
        simp only [inferSeq] at hseq
        exact inv_push_sub hfs htab hsc hhook hsat hstr hcls hbot (by simpa [framePopLabels] using hks) hseq hsw
          (KontOk.seqNil (by simp) hk') (hclo := hcloTail hK)
      | cons e₂ es' =>
        simp only [inferSeq] at hseq
        split at hseq
        · rename_i σ Γ₁ h₁
          exact inv_push hfs htab hsc hhook hsat hstr hcls hbot (by simpa [framePopLabels] using hks) h₁
            (KontOk.seqCons hseq hsw hk') (hclo := hcloTail hK)
        · exact absurd hseq (by simp)
    | @asgn _ _ _ _ _ _ τw x k _ hib hsw hk' hsu =>
      -- The machine `applyKont` steps to is `{ m with kont := k }.setLocal x v`, and
      -- `hfs` is phrased over `m`. The two agree definitionally, but since L137 made
      -- `FramesOk` heap-indexed the elaborator resolves `?m` from `hfs` rather than
      -- from the goal, so the instance has to be named.
      refine ⟨hhook, hsat, hstr, hcls, ?_,
        -- L199: `setLocal` moves neither the stack nor the continuation's frames.
        (by
          show framePopLabels (Machine.setLocal { m with kont := k } x v).kont
            = (Machine.setLocal { m with kont := k } x v).stack.dropLast
          rw [setLocal_stack]
          simpa [framePopLabels, Machine.setLocal] using hks),
        -- L247: `setLocal` writes `locals`, so every frame's `captured` is where it
        -- was, and the kont lost its head.
        ClosuresOk.transport (hcloTail hK)
          (by
            intro κ hm cl hcl
            exact ⟨κ, by simpa [Machine.setLocal, withCtl] using hm, hcl⟩)
          (Nat.le_of_eq (setLocal_frames_size { m with kont := k } x v).symm)
          (by intro p _; exact setLocal_shape { m with kont := k } x v p)
          (by intro o ho; exact ho),
        _, ctx, envSet Γk x τ, Γs, htab, ?_, ?_, hglob,
        ⟨τw, _, ValueTy.weaken hv hsw, hsu, hk'⟩⟩
      · -- `setLocal` rewrites one frame's `locals` and nothing else, so every
        -- stacked frame's `defmod` — all `BottomObj` reads — is unmoved.
        show BottomObj (Machine.setLocal { m with kont := k } x v).frames
          (Machine.setLocal { m with kont := k } x v).stack
        have hf' : FrameOk { m with kont := k } :=
          FramesOk.frameOk (m := { m with kont := k }) hfs
            (by simpa [curFrame, curFid] using hsc.curCaptured hib)
        rw [setLocal_stack, setLocal_frames (m := { m with kont := k }) hf']
        refine BottomObj_congr (fun fid _ => ?_) hbot
        by_cases hfx : fid = curFid { m with kont := k }
        · subst hfx
          rw [getD_set!_self _ _ _ (by simpa using hf'.2.1)]
          rfl
        · rw [getD_set!_ne _ _ _ _ hfx]
      · exact FramesOk.setLocal (m := { m with kont := k }) hfs
          (by simpa [curFrame, curFid] using hsc.curCaptured hib) hv
      · -- The same argument for the context stack: `setLocal` moves neither
        -- `defmod` nor `defVis`, which is all this predicate reads.
        show StackCtx (Machine.setLocal { m with kont := k } x v).heap
          (Machine.setLocal { m with kont := k } x v).frames
          (Machine.setLocal { m with kont := k } x v).stack (ctx :: Γs.map Prod.fst)
        have hf' : FrameOk { m with kont := k } :=
          FramesOk.frameOk (m := { m with kont := k }) hfs
            (by simpa [curFrame, curFid] using hsc.curCaptured hib)
        rw [setLocal_stack, setLocal_frames (m := { m with kont := k }) hf']
        -- L189 adds a fourth agreement, and it is the same one-liner: `setLocal`
        -- writes `locals` and moves neither `defmod`, `defVis`, `self` nor `cref`.
        refine StackCtx_congr (fun fid _ => ?_) (fun fid _ => ?_) (fun fid _ => ?_)
          (fun fid _ => ?_) (fun fid _ => ?_) (fun fid _ => ?_) (fun fid _ => ?_)
          (fun fid _ => ?_) (fun fid _ => ?_) hsc <;>
          by_cases hfx : fid = curFid { m with kont := k }
        · subst hfx; rw [getD_set!_self _ _ _ (by simpa using hf'.2.1)]; rfl
        · rw [getD_set!_ne _ _ _ _ hfx]
        · subst hfx
          rw [getD_set!_self _ _ _ (by simpa using hf'.2.1)]
          rfl
        · rw [getD_set!_ne _ _ _ _ hfx]
        · subst hfx
          rw [getD_set!_self _ _ _ (by simpa using hf'.2.1)]
          rfl
        · rw [getD_set!_ne _ _ _ _ hfx]
        · subst hfx
          rw [getD_set!_self _ _ _ (by simpa using hf'.2.1)]
          rfl
        · rw [getD_set!_ne _ _ _ _ hfx]
        -- L198's fifth agreement, and it is the same one-liner a fifth time.
        · subst hfx
          rw [getD_set!_self _ _ _ (by simpa using hf'.2.1)]
          rfl
        · rw [getD_set!_ne _ _ _ _ hfx]
        -- L207's sixth, a sixth time.
        · subst hfx
          rw [getD_set!_self _ _ _ (by simpa using hf'.2.1)]
          rfl
        · rw [getD_set!_ne _ _ _ _ hfx]
        -- **L214's seventh and eighth**, and they are the same one-liner again — which
        -- is exactly the reason L214's `StackCtx` clause is the locals-independent form:
        -- `runParams` and `runFromDM` are fields `setLocal` does not write, and the
        -- general clause (which reads `locals`) would have had no one-liner here at all.
        · subst hfx
          rw [getD_set!_self _ _ _ (by simpa using hf'.2.1)]
          rfl
        · rw [getD_set!_ne _ _ _ _ hfx]
        · subst hfx
          rw [getD_set!_self _ _ _ (by simpa using hf'.2.1)]
          rfl
        · rw [getD_set!_ne _ _ _ _ hfx]
        -- L243's ninth: `captured` is a field `setLocal` does not write either.
        · subst hfx
          rw [getD_set!_self _ _ _ (by simpa using hf'.2.1)]
          rfl
        · rw [getD_set!_ne _ _ _ _ hfx]
    -- **`@x = e`, delivered** (L191), and the whole case is one refutation plus one
    -- transport.
    --
    -- *The refutation.* `applyKont`'s ivar arm has two raising branches — an
    -- immediate `self` and a frozen one — and a raise is a `.jump`, which `CtlOk`
    -- refuses. `KontOk.asgnIvar`'s premise closes both at once: `selfCls = some sc`
    -- gives the frame's `self` a *class* type (`StackCtx`'s F1b.11 clause), a class
    -- type is only inhabited by a `.ref` at a `plainRecv` id
    -- (`valueTy_ref_plain`), and `plainRecv`'s L191 clause is `¬ frozen`.
    --
    -- *The transport.* The step writes `ivars` and nothing else, and no predicate in
    -- `Inv` reads `ivars` — so every conjunct crosses by `IvarOnly`
    -- (`Proof/Static/Decls.lean` §8) with no case analysis at all. That is the
    -- cheapest heap-writing rule in the fragment, and it is cheap for a reason worth
    -- stating: the invariant is about *dispatch and names*, and an instance-variable
    -- table is neither.
    -- **`C::n`, at the delivery** (L205). Three steps and each is one hypothesis read
    -- out: the in-flight value is a class object (so `cpathContainer` succeeds and the
    -- container's name is the table key), the constant is not `private_constant`, and
    -- the walk finds a value of the declared type. All three live in `ScopedConstOk`,
    -- which is why this case establishes nothing about the heap — it only reads.
    | @cpathK _ _ _ _ _ _ τw cname n σ k _ hb hsco hsw hk' hsu =>
      -- The value is a class object, and its *own* name is the key (`valueTy?`'s class
      -- arm, L185) — so the container the machine resolves and the class the table was
      -- read at are the same object, with no uniqueness clause needed.
      have hvc : ValueTy m.heap v (.clsOf cname) := ValueTy.weaken hv hb
      obtain ⟨o, rfl⟩ : ∃ o, v = .ref o := by
        cases hsv : v with
        | ref o' => exact ⟨o', rfl⟩
        | _ => rw [hsv] at hvc; simp_all [ValueTy, valueTy?, subTy]
      have hcr : classRecv m.heap o = true := valueTy_ref_class hvc
      have hpay : (m.heap.classPayload? o).isSome := by
        unfold classRecv at hcr
        simp only [Bool.and_eq_true] at hcr
        exact hcr.2
      have hcn : className m.heap o = cname := by
        rcases valueTy_ref_inv (by simp [subTy]) (by simp [subTy]) hvc with ⟨-, hs⟩ | ⟨-, hs⟩
        · exact absurd hs (by simp [subTy])
        · simpa using (subTy_atomic (τ := Ty.clsOf cname) (by simp) (by simp)).mp hs
      obtain ⟨hpriv, cv, hcv, hcty⟩ := htab.2.2.2.1 cname n σ hsco o hpay hcn
      have hcont : Interp.cpathContainer { m with kont := k } (.ref o) = .ok o := by
        unfold Interp.cpathContainer
        simp [hpay]
      simp only [hcont, hcv]
      -- The `private_constant` gate is `ScopedConstOk`'s first conjunct, and it is what
      -- makes the *miss* path unreachable rather than something to reason about.
      -- **The `private_constant` gate** (L104), and it is refuted rather than computed.
      -- `split` on the machine's own `if` keeps the goal's term — restating it here as
      -- an equation does *not* work, because a `match` in a fresh syntactic position
      -- compiles to its own auxiliary and the two are not the same function even
      -- though they print alike. So the hit branch is closed by its own equation and
      -- the miss branch by `ScopedConstOk`'s first conjunct.
      split
      · rename_i _x cv' heq
        split at heq
        · exact absurd heq (by simp)
        · simp only [Option.some.injEq] at heq
          subst heq
          exact inv_value hfs htab hsc hhook hsat hstr hcls hbot
            (by simpa [framePopLabels] using hks) (ValueTy.weaken hcty hsw) hk' (hclo := hcloTail hK)
      · rename_i _x heq
        exfalso
        split at heq
        · rename_i hcond
          simp only [List.any_eq_true] at hcond
          obtain ⟨a, ha, hcon⟩ := hcond
          have hpa := List.all_eq_true.mp hpriv a ha
          revert hcon hpa
          cases m.heap.classPayload? a <;> simp
        · exact absurd heq (by simp)
    -- **`$x = e`'s delivery** (L228), and it is the shortest write case in the file:
    -- `setGlobal` on a plain name is one `cons` onto a filtered list, the heap does not
    -- move, and `GlobalsOk.set` is exactly the lemma for that shape. Compare `asgnIvar`
    -- below, which needs `StackCtx`, `plainRecv`, the frozen check and a heap transport —
    -- the difference is the whole reason the sixth table got its own `Inv` conjunct
    -- instead of a `DeclsOk` clause.
    | @asgnGvar _ _ _ _ _ _ τw x σ k _ hpg hgt hcf hsw hk' hsu =>
      -- The `show` is load-bearing: `Machine.setGlobal` is an `if` on the *name*, so no
      -- projection of it reduces until the rewrite fires, and the rewrite cannot fire
      -- until `applyKont`'s match is reduced. Stating the stepped machine does both.
      show StepOk (.next (Interp.withCtl (({ m with kont := k }).setGlobal x v) (.value v)))
      rw [setGlobal_of_plain (m := { m with kont := k }) hpg]
      simp only [Interp.withCtl]
      exact ⟨hhook, hsat, hstr, hcls, hbot, (by simpa [framePopLabels] using hks),
        -- L247: a global write moves neither frames nor the closures on the kont.
        ClosuresOk.konts (hcloTail hK) rfl rfl
          (by intro κ hm; exact Or.inl (by simpa using hm)),
        D, ctx, Γk, Γs, htab, hfs, hsc,
        GlobalsOk.set hglob hgt (ValueTy.weaken hv hcf),
        ⟨τw, _, ValueTy.weaken hv hsw, hsu, hk'⟩⟩
    | @asgnIvar _ _ _ _ _ _ τw x k _ hsome hsw hcf hk' hsu =>
      obtain ⟨sc, hsc'⟩ := Option.isSome_iff_exists.mp hsome
      have hself : ValueTy m.heap m.currentFrame.self (.cls sc) := by
        cases hst : m.stack with
        | nil => exact absurd hst hfsh.1
        | cons fid fids =>
          have hsc2 := hsc
          rw [hst] at hsc2
          have := hsc2.2.2.2.1 sc hsc'
          rw [show m.currentFrame = m.frames.getD fid default by
            simp [Machine.currentFrame, hst]]
          exact this.1
      obtain ⟨o, hsf⟩ : ∃ o, m.currentFrame.self = .ref o := by
        cases hsv : m.currentFrame.self with
        | ref o' => exact ⟨o', rfl⟩
        | _ => rw [hsv] at hself; simp_all [ValueTy, valueTy?, subTy]
      have hpl : plainRecv m.heap o = true := valueTy_ref_plain (hsf ▸ hself)
      have hfz : (m.heap.get o).frozen = false := by
        unfold plainRecv at hpl
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hpl
        exact hpl.1.1.2
      -- L196: the class the ivar table is keyed at, and the bound the scan needs.
      have hcnO : className m.heap (m.heap.get o).klass = sc := by
        rcases valueTy_ref_inv (by simp [subTy]) (by simp [subTy]) (hsf ▸ hself) with ⟨-, hs⟩ | ⟨hc, hs⟩
        · have hq := (subTy_atomic (τ := Ty.cls sc) (by simp) (by simp)).mp hs
          rw [plainRecv_classOf hpl] at hq
          simpa using hq
        · exact absurd hs (by simp [subTy])
      have hltO : o < m.heap.objs.size := by
        unfold plainRecv at hpl; simp only [Bool.and_eq_true] at hpl
        simpa using hpl.1.1.1.1.1
      show StepOk (match m.currentFrame.self with
        | .ref o' =>
          if (m.heap.get o').frozen then _ else
            .next (withCtl (bindIvar { m with kont := k } x v) (.value v))
        | selfV => _)
      rw [hsf]
      simp only [hfz, if_false]
      have hi : IvarOnly m.heap (bindIvar { m with kont := k } x v).heap :=
        bindIvar_fields (m := { m with kont := k })
      have hag := hi.typeAgree
      have hfr : (bindIvar { m with kont := k } x v).frames = m.frames := by
        unfold bindIvar; rw [show ({ m with kont := k } : Machine).currentFrame
          = m.currentFrame from rfl, hsf]
      have hstk : (bindIvar { m with kont := k } x v).stack = m.stack := by
        unfold bindIvar; rw [show ({ m with kont := k } : Machine).currentFrame
          = m.currentFrame from rfl, hsf]
      have hkt : (bindIvar { m with kont := k } x v).kont = k := by
        unfold bindIvar; rw [show ({ m with kont := k } : Machine).currentFrame
          = m.currentFrame from rfl, hsf]
      -- L228: and the globals, the same three lines a fourth time.
      have hgb : (bindIvar { m with kont := k } x v).globals = m.globals := by
        unfold bindIvar; rw [show ({ m with kont := k } : Machine).currentFrame
          = m.currentFrame from rfl, hsf]
      refine ⟨hi.noHook hhook, hi.saturated hsat, hi.litClsOk hstr, hi.classOk hcls,
        by rw [show (withCtl (bindIvar { m with kont := k } x v) (.value v)).frames
                 = m.frames from hfr,
              show (withCtl (bindIvar { m with kont := k } x v) (.value v)).stack
                 = m.stack from hstk]
           exact hbot,
        by rw [show (withCtl (bindIvar { m with kont := k } x v) (.value v)).kont
                 = k from hkt,
              show (withCtl (bindIvar { m with kont := k } x v) (.value v)).stack
                 = m.stack from hstk]
           simpa [framePopLabels] using hks,
        -- L247: `bindIvar` writes a heap object; frames and konts are untouched.
        ClosuresOk.transport (hcloTail hK)
          (by
            intro κ hm cl hcl
            refine ⟨κ, ?_, hcl⟩
            rw [show (withCtl (bindIvar { m with kont := k } x v) (.value v)).kont
              = k from hkt] at hm
            exact hm)
          (by
            rw [show (withCtl (bindIvar { m with kont := k } x v) (.value v)).frames
              = (bindIvar { m with kont := k } x v).frames from rfl, hfr]
            exact Nat.le_refl _)
          (by
            intro p _
            rw [show (withCtl (bindIvar { m with kont := k } x v) (.value v)).frames
              = (bindIvar { m with kont := k } x v).frames from rfl, hfr]
            exact FrameShape.rfl' _)
          (by
            intro o ho
            show ((bindIvar { m with kont := k } x v).heap.classPayload? o).isSome = true
            rw [hi.classPayload]; exact ho),
        D, ctx, Γk, Γs, ⟨(hi.rowsAndConsts htab).1, (hi.rowsAndConsts htab).2.1, ?_,
          (hi.rowsAndConsts htab).2.2⟩,
        ?_, ?_, ?_, ?_⟩
      · -- **L196: the one half `IvarOnly` cannot carry**, because it is the half that
        -- is *about* ivars. What re-establishes it is the rule's own conformance
        -- check, and the case splits three ways: a different object (the write missed
        -- it), the same object at a different name (the `filter`/`cons` missed it), or
        -- the written slot itself, where the row's type is the one the rule checked
        -- against — the classes agree because both name `sc`.
        intro c' x' σ' hiv' o' ho0 hcn' v' hv'
        have hsz : (withCtl (bindIvar { m with kont := k } x v) (.value v)).heap.objs.size
            = m.heap.objs.size := hi.size
        have ho' : o' < m.heap.objs.size := by omega
        -- `withCtl` is a structure update, so its `.heap` is the written one — but only
        -- definitionally, and `rw` needs it syntactically.
        simp only [withCtl] at hcn' hv'
        by_cases hoo : o' = o
        · -- The written object. Its class is `sc` on both sides, so `c' = sc` — and
          -- then the row's type is the one the rule checked against.
          have hcls' : c' = sc := by
            rw [← hcn', hoo,
              show ((bindIvar { m with kont := k } x v).heap.get o).klass
                = (m.heap.get o).klass from hi.klass o, hi.className_eq]
            exact hcnO
          subst hcls'
          rw [hoo] at hv' ho'
          by_cases hxx : x' = x
          · subst hxx
            have hvv : v' = v := by
              rw [bindIvar_ivars_self (m := { m with kont := k }) hsf hltO] at hv'
              simpa using hv'.symm
            subst hvv
            exact ValueTy.congr hag (ValueTy.weaken hv (hcf _ σ' hsc' hiv'))
          · -- A different name: the head is `x` and the tail is the old list with `x`
            -- filtered out, so the lookup reads the old value.
            rw [bindIvar_ivars_self (m := { m with kont := k }) hsf hltO,
              List.find?_cons_of_neg (by simpa using fun hq => hxx hq.symm),
              find?_filter_ne _ hxx] at hv'
            exact ValueTy.congr hag (htab.2.2.1 _ x' σ' hiv' o ho' hcnO v' hv')
        · rw [bindIvar_get_ne (m := { m with kont := k }) hsf hoo] at hcn' hv'
          rw [hi.className_eq] at hcn'
          exact ValueTy.congr hag (htab.2.2.1 c' x' σ' hiv' o' ho' hcn' v' hv')
      · show FramesOk _ (bindIvar { m with kont := k } x v).frames
          (bindIvar { m with kont := k } x v).stack (Γk :: Γs.map Prod.snd)
        rw [hfr, hstk]; exact FramesOk.heap_congr hag hfs
      · show StackCtx _ (bindIvar { m with kont := k } x v).frames
          (bindIvar { m with kont := k } x v).stack (ctx :: Γs.map Prod.fst)
        rw [hfr, hstk]; exact StackCtx.heap_congr hag hsc
      -- **L228: an ivar write is a heap write**, so the conjunct needs its transport —
      -- one `GlobalsOk.congr` at the `TypeAgree` the case already has, plus the
      -- association list being untouched.
      · rw [show (withCtl (bindIvar { m with kont := k } x v) (.value v)).globals
                 = m.globals from hgb]
        exact GlobalsOk.congr
          (h' := (withCtl (bindIvar { m with kont := k } x v) (.value v)).heap) hag hglob
      · exact ⟨τw, _, ValueTy.congr hag (ValueTy.weaken hv hsw), hsu,
          by rw [show (withCtl (bindIvar { m with kont := k } x v) (.value v)).kont
                    = k from hkt]
             exact KontOk.heap_congr hag hk'⟩
    -- **`return e`'s value has arrived** (L200). `applyKont`'s `jumpValK .retK` arm is
    -- `doReturn`, so this case *creates* the jump — and everything it needs is already
    -- in hand: `StackCtx`'s L198/L200 clause makes `returnTarget` the stack's head,
    -- L199's clause makes that head the innermost `frameK`'s label, and
    -- `KontOk.retOk` turns the tail's `KontOk` into the `RetOk` the unwinding wants.
    | @retValK _ _ _ _ _ _ τ'' σ k _ hret hsub hk' hsu =>
      cases hst : m.stack with
      | nil => exact absurd hst hfsh.1
      | cons fid fids =>
        rw [hst] at hbot hfs hsc hks
        rcases hsc.2.2.2.2.2.1 with ⟨hkind, hcs⟩ | hnone
        · have hne : Γs ≠ [] := by intro hq; rw [hq] at hcs; simp at hcs
          have hfne : fids ≠ [] := by
            intro hq
            rw [hq] at hsc
            have htl := hsc.2.2.2.2.2.2
            cases hΓ : Γs.map Prod.fst with
            | nil => exact absurd hΓ hcs
            | cons a b => rw [hΓ] at htl; exact absurd htl (by simp [StackCtx])
          have hpl : framePopLabels k = fid :: fids.dropLast := by
            rw [show framePopLabels k = (fid :: fids).dropLast from by
              simpa [framePopLabels] using hks, dropLast_cons_ne hfne]
          -- L245: the bridge runs through `RetOk`.
          have hff : firstFrameK k = some fid :=
            firstFrameK_of_retOk (KontOk.retOk hk' hne σ hret) hpl
          simp only [Interp.doReturn, Interp.returnTarget, List.headD_cons, hkind]
          rw [if_pos (show ((fid :: fids).contains fid) = true from by simp)]
          refine ⟨hhook, hsat, hstr, hcls, hbot, ?_,
            ClosuresOk.konts (hcloTail hK) rfl rfl (by intro κ hm; exact Or.inl hm),
            D, ctx, Γk, Γs, htab, hfs, hsc, hglob,
            ⟨σ, ValueTy.weaken hv hsub, KontOk.retOk hk' hne σ hret, hff⟩⟩
          show framePopLabels k = (fid :: fids).dropLast
          simpa [framePopLabels] using hks
        · rw [hnone] at hret; exact absurd hret (by simp)
    | @ifK _ _ _ _ _ _ _ t els τ' τw Γ' k _ hif hsw hk' hsu =>
      cases els with
      -- **L193: the branch's own type is *below* the join, so each side goes through
      -- `inv_eval_sub` with one `subTy_trans`** — the branch below the join, the join
      -- below whatever the enclosing rule registered. `joinTy_sub` supplies the first
      -- half; before this rung the two were equal and the composition was invisible.
      | some e₂ =>
        simp only [inferIf] at hif
        split at hif
        · rename_i τt Γt Dt τe Γe De ht he
          split at hif
          · rename_i hagree
            -- **L236: the environment half is two containments, not an equality**, and
            -- this is the case the whole slack machinery was built for. The branch runs
            -- at *its own* environment while the continuation was registered at the
            -- `if`'s answer — the entry one; `subEnvB_sound` turns the rule's own guard
            -- into the missing `SubEnv`, `hsu` is the kont's slack against the answer,
            -- and one `SubEnv.trans` reconciles them. Every other construction site in
            -- this file passes `refl`.
            obtain ⟨hsub1, hsub2, rfl⟩ := hagree
            simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hif
            obtain ⟨τj, hjoin, rfl, rfl, rfl⟩ := hif
            by_cases hb : v.truthy
            · simp only [hb, if_true]
              exact inv_eval_sub hfs htab hsc hhook hsat hstr hcls hbot hks ht
                (subTy_trans (joinTy_sub hjoin).1 hsw) hk'
                (hsuE := SubEnv.trans hsu (subEnvB_sound hsub1)) (hclo := hcloTail hK)
            · simp only [hb]
              exact inv_eval_sub hfs htab hsc hhook hsat hstr hcls hbot hks he
                (subTy_trans (joinTy_sub hjoin).2 hsw) hk'
                (hsuE := SubEnv.trans hsu (subEnvB_sound hsub2)) (hclo := hcloTail hK)
          · exact absurd hif (by simp)
        · exact absurd hif (by simp)
      | none =>
        simp only [inferIf] at hif
        split at hif
        · rename_i τt Γt ht
          split at hif
          · rename_i hnil
            -- L236: `subEnvB` where this was an equality, so the arm's environment is a
            -- *widening* of the `if`'s and the kont's slack composes with it.
            obtain ⟨hsub1, rfl⟩ := hnil
            simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hif
            obtain ⟨τj, hjoin, rfl, rfl, rfl⟩ := hif
            by_cases hb : v.truthy
            · simp only [hb, if_true]
              exact inv_eval_sub hfs htab hsc hhook hsat hstr hcls hbot hks ht
                (subTy_trans (joinTy_sub hjoin).1 hsw) hk'
                (hsuE := SubEnv.trans hsu (subEnvB_sound hsub1)) (hclo := hcloTail hK)
            · simp only [hb]
              exact inv_value hfs htab hsc hhook hsat hstr hcls hbot (by simpa [framePopLabels] using hks)
                (ValueTy.weaken (ValueTy.exact rfl)
                  (subTy_trans (joinTy_sub hjoin).2 hsw)) hk' (hclo := hcloTail hK)
          · exact absurd hif (by simp)
        · exact absurd hif (by simp)
    | @whileCond _ _ _ _ _ _ τw c body k _ hloop hsw hk' hsu =>
      obtain ⟨⟨σc, hcnd⟩, ⟨σb, hbody⟩⟩ := hloop
      by_cases hb : v.truthy
      · simp only [hb, if_true]
        exact inv_push hfs htab hsc hhook hsat hstr hcls hbot (by simpa [framePopLabels] using hks) hbody
          (KontOk.whileBody ⟨⟨σc, hcnd⟩, ⟨σb, hbody⟩⟩ hsw hk') (hclo := hcloTail hK)
      · simp only [hb]
        -- The loop *exits*: the value goes to a continuation indexed at the enclosing
        -- context, so this is where the flag comes back off.
        exact inv_value hfs htab (stackCtx_inLoop' hsc) hhook hsat hstr hcls hbot
          (by simpa [framePopLabels] using hks)
          (ValueTy.weaken (ValueTy.exact rfl) hsw) hk' (hclo := hcloTail hK)
    | @whileBody _ _ _ _ _ _ τw c body k _ hloop hsw hk' hsu =>
      obtain ⟨⟨σc, hcnd⟩, ⟨σb, hbody⟩⟩ := hloop
      exact inv_push hfs htab hsc hhook hsat hstr hcls hbot (by simpa [framePopLabels] using hks) hcnd
        (KontOk.whileCond ⟨⟨σc, hcnd⟩, ⟨σb, hbody⟩⟩ hsw hk') (hclo := hcloTail hK)
    -- **A block body's value** (L245) — `applyKont`'s two popping arms are the same
    -- `stack.tail` + `.value v`, so this is `frameK`'s case with the type agreement
    -- spelled as the constructor's own `subTy` rather than read off the caller's
    -- context. Nothing about the block is used here: the block frame is described by
    -- `FramesOk`, and popping it is `hfs.tail`.
    | @blkFrameK _ _ _ cΓ' Γs _ _ fid lam brk cl args k _ _ hsw hk' =>
      obtain ⟨c', Γ'⟩ := cΓ'
      have hst2 : ∃ f0 f1 rest, m.stack = f0 :: f1 :: rest := by
        cases hst : m.stack with
        | nil => rw [hst] at hfs; exact absurd hfs (by simp [FramesOk])
        | cons f0 t =>
          cases ht : t with
          | nil => rw [hst, ht] at hfs; exact absurd hfs (by simp [FramesOk])
          | cons f1 rest => exact ⟨f0, f1, rest, rfl⟩
      obtain ⟨f0, f1, rest, hst⟩ := hst2
      have hlab : framePopLabels k = m.stack.tail.dropLast := by
        have hq := hks
        simp only [framePopLabels] at hq
        rw [hst] at hq ⊢
        simp only [List.dropLast_cons_cons, List.cons.injEq] at hq
        simpa using hq.2
      refine ⟨hhook, hsat, hstr, hcls, BottomObj_tail hbot, hlab,
        ClosuresOk.konts (hcloTail hK) rfl rfl (by intro κ hm; exact Or.inl hm),
        _, c', Γ', Γs, htab,
        hfs.tail, StackCtx.tail hsc, hglob,
        ⟨_, _, ValueTy.weaken hv hsw, SubEnv.refl _, hk'⟩⟩
    -- **A block send dispatches** (L257) — the step `Proof/Static/Iter.lean`'s five
    -- reductions describe, with `Inv` at the far end.
    | @recvKBlk _ _ _ _ Γk2 Γs2 τr2 τw2 τb2 τret2 σp2 βret2 Γb'2 mname2 x2 ps2 ls2 body2
        k2 site2 hbs hbody hsu2 hsb hsw hib2 hk'2 hsuE2 =>
      obtain ⟨d, hd, hdp, hdr, hdb⟩ := blockSend?_declFor hbs
      obtain ⟨hτ, hmn, -, hdr2, ⟨br, hdb2⟩, hmiss⟩ := (htab.1 _ mname2 d hd).iter hdb
      obtain ⟨hps, hls⟩ := blockSend?_shape hbs
      subst hps; subst hls; subst hmn; subst hτ
      have hσany : σp2 = Ty.any := by
        rw [hdb] at hdb2
        simp only [Option.some.injEq, BlockSig.mk.injEq, List.cons.injEq,
          and_true, List.nil_eq] at hdb2
        exact hdb2.1
      have hret : τret2 = Ty.cls "Array" := by rw [← hdr, hdr2]
      subst hσany; subst hret
      obtain ⟨o, xs, rfl, hpay, holt⟩ := arrayPayload_of_valueTy hv
      have htc : TyClass m.heap (Ty.cls "Array") (classOf m.heap (.ref o)) :=
        valueTy_tyClass (by simp) (by simp) (by simp) hv
      have hne : m.stack ≠ [] := hfsh.1
      have hlt : ∀ g ∈ m.stack, g < m.frames.size := hfs.mem_lt
      have hg : PlainGrow m.heap
          (reifyBlock { m with kont := k2 } [.req x2] [] body2 false).2.heap := by
        rw [reifyBlock_eq]; exact plainGrow_alloc m.heap _ (by simp) rfl
      have hag : TypeAgree m.heap
          (reifyBlock { m with kont := k2 } [.req x2] [] body2 false).2.heap :=
        typeAgree_of_plainGrow hg hsat
      have hpay1 : ((reifyBlock { m with kont := k2 } [.req x2] [] body2 false).2.heap.get
          o).payload = .arr xs := by rw [hg.get o holt]; exact hpay
      have hlk1 : lookup (reifyBlock { m with kont := k2 } [.req x2] [] body2 false).2.heap
          (.ref o) "each" = none := by
        have hm0 := hmiss (classOf m.heap (.ref o)) htc
        unfold MissesAt lookupIn at hm0
        show lookup.go _ "each" (ancestors _ (classOf _ (.ref o))) = none
        rw [hg.classOf_value_eq (.ref o) (fun o' he => by
            simp only [Value.ref.injEq] at he; exact he ▸ holt),
          hg.ancestors_eq hsat, lookup_go_grow hg]
        exact hm0
      have hproc1 : ((reifyBlock { m with kont := k2 } [.req x2] [] body2 false).2.heap.get
          m.heap.objs.size).payload
            = .proc (blockClosure { m with kont := k2 } [.req x2] [] body2 false) := by
        rw [reifyBlock_eq]
        exact congrArg Object.payload (get_push_self m.heap.objs _)
      show StepOk (Interp.finishSend { m with kont := k2 } (.ref o) site2 "each" []
        (.lit [.req x2] [] body2))
      rw [finishSend_lit (by simp) (by simp) (by simp)]
      rw [reifyBlock_eq] at hpay1 hlk1 hproc1 hg hag ⊢
      rw [invoke_iter_each (cl := blockClosure { m with kont := k2 } [.req x2] [] body2 false)
        hpay1 hproc1 hlk1, startIter_eq]
      cases hxs : xs.toList with
      | nil =>
        -- **An empty array**: the loop never runs, and the iterator's own answer — the
        -- receiver — goes to the `frameK` that pops its activation.
        simp only [hxs, List.map_nil]
        rw [iterStep_nil]
        refine ⟨NoHook_grow hg hsat hhook, Saturated_grow hg.shapeAgree hg.size hsat,
          LitClsOk_grow hg hstr, ClassOk_grow hg hsat hcls,
          BottomObj_cons hne (BottomObj_push hlt hbot),
          (by simpa [withCtl, framePopLabels, dropLast_cons_ne hne] using hks),
          ?_, D, { cls := "Array" }, [], (ctx, Γk2) :: Γs,
          DeclsOk_grow hg hsat htab, ?_, ?_, ?_, ?_⟩
        · -- `ClosuresOk`: the pushed `frameK` carries no closure, the rest was there.
          refine ClosuresOk.transport hclo (fun κ hm cl hcl => ?_)
            (by simp only [withCtl]; simp [Array.size_push]) (by
              intro p hp'
              simp only [withCtl]
              show FrameShape ((m.frames.push _).getD p default) _
              rw [getD_push_lt _ _ _ hp']; exact FrameShape.rfl' _)
            (fun ob hob => by
              simp only [withCtl]
              show (Heap.classPayload? _ ob).isSome = true
              rw [hg.payload]; exact hob)
          rcases List.mem_cons.mp hm with rfl | hm₁
          · exact absurd hcl (by simp [KontClosure])
          · exact ⟨κ, by rw [hK]; exact List.mem_cons_of_mem _ hm₁, hcl⟩
        · -- `FramesOk`: the iterator activation has no locals, so its environment is `[]`.
          simp only [withCtl]
          refine ⟨by rw [Array.size_push]; exact Nat.lt_succ_self _, hlt,
            ⟨ShallowChain.of_none (by rw [getD_push_lt_self]), ?_, ?_⟩,
            FramesOk.push (FramesOk.narrowHead hsuE2 (FramesOk.heap_congr hag hfs))⟩
          · rw [getD_push_lt_self]
            show (Heap.classPayload? _ (classOf _ (.ref o))).isSome = true
            rw [hg.payload, hg.classOf_eq holt]; exact htc.1
          · intro y σ hy; exact absurd hy (by simp [envGet?])
        · -- `StackCtx`: the activation's definee **is** the receiver's class, and its
          -- `cref` is the caller's (L256) — the clause an empty one refused.
          simp only [withCtl]
          refine ⟨?_, ?_, ?_, ?_, ?_, Or.inr rfl, fun mn hmn => absurd hmn (by simp), ?_,
            (fun hcb _ => nomatch hcb),
            StackCtx.push hlt (StackCtx.heap_congr hag hsc)⟩
          · rw [getD_push_lt_self]
            show (Heap.classPayload? _ (classOf _ (.ref o))).isSome = true
            rw [hg.payload, hg.classOf_eq holt]; exact htc.1
          · intro _
            rw [getD_push_lt_self]
            show className _ (classOf _ (.ref o)) = "Array"
            rw [hg.classOf_eq holt, hg.className_eq]; exact htc.2
          · intro _; rw [getD_push_lt_self]; simp [defVisOfDef]
          · exact fun sc hsc' => absurd hsc' (by simp)
          · rw [getD_push_lt_self]
            show Boot.objectId ∈ m.currentFrame.cref
            rw [currentFrame_eq hne]
            cases hst : m.stack with
            | nil => exact absurd hst hne
            | cons fid fids =>
              rw [hst] at hsc
              simpa [curFrame, curFid, hst] using hsc.2.2.2.2.1
          · intro _; rw [getD_push_lt_self]
        · simp only [withCtl]; exact GlobalsOk.congr hag hglob
        · exact ⟨τw2, [], ValueTy.weaken (ValueTy.congr hag hv) hsw, SubEnv.refl _,
            KontOk.frameK (fun σ hq => absurd hq (by simp)) rfl
              (KontOk.heap_congr hag hk'2)⟩
      | cons a0 rest' =>
        simp only [hxs, List.map_cons]
        rw [iterStep_cons,
          callClosure_req1 (cl := blockClosure { m with kont := k2 } [.req x2] [] body2 false)
            rfl rfl rfl]
        -- **The closure's captured frame is the send site's**, and every fact the block
        -- frame needs about it is one of `StackCtx`'s clauses at the caller.
        have hcapn : (m.frames.getD (m.stack.headD 0) default).captured = none := by
          simpa [curFrame, curFid] using hsc.curCaptured hib2
        have hcap3 : (m.heap.classPayload? (m.frames.getD (m.stack.headD 0)
              default).defmod).isSome = true ∧
            Boot.objectId ∈ (m.frames.getD (m.stack.headD 0) default).cref := by
          cases hst : m.stack with
          | nil => exact absurd hst hne
          | cons fid0 fids0 =>
            rw [hst] at hsc
            exact ⟨by simpa [hst] using hsc.1, by simpa [hst] using hsc.2.2.2.2.1⟩
        have hclt : m.stack.headD 0 < m.frames.size := by
          simpa [curFid] using hfsh.2.1
        -- The closure's captured id *is* the send site's frame, but only by `rfl`.
        have hbc : (blockClosure { m with kont := k2 } [.req x2] [] body2 false).captured
            = m.stack.headD 0 := rfl
        -- Everything the block frame's environment claims is `.any`, so its conformance
        -- is `ValueTy.any` at every name and needs no lookup (L247).
        have hany : ∀ y σ, envGet? ((x2, Ty.any) :: anyEnv Γk) y = some σ → σ = Ty.any := by
          intro y σ hy
          by_cases hyx : (x2 == y) = true
          · simpa [envGet?, List.find?, hyx] using hy.symm
          · have hy' : envGet? (anyEnv Γk) y = some σ := by
              simpa [envGet?, List.find?, hyx] using hy
            rw [anyEnv_get] at hy'
            cases hgk : envGet? Γk y with
            | none => rw [hgk] at hy'; exact absurd hy' (by simp)
            | some _ => rw [hgk] at hy'; simpa using hy'.symm
        -- The two pushes are opaque giants; every index fact below is one of these five
        -- (L257 — `omega` will not fire under a context this large, so each is explicit).
        have hpop : ∀ (f1 f2 : Frame) (q : FrameId), q < m.frames.size →
            ((m.frames.push f1).push f2).getD q default = m.frames.getD q default := by
          intro f1 f2 q hq
          rw [getD_push_lt _ _ _ (by
              simp only [Array.size_push]; exact Nat.lt_succ_of_lt hq),
            getD_push_lt _ _ _ hq]
        have hlt2 : ∀ (f1 f2 : Frame) (q : FrameId), q < m.frames.size →
            q < ((m.frames.push f1).push f2).size := by
          intro f1 f2 q hq
          simp only [Array.size_push]
          exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hq)
        have hltI : ∀ (f1 f2 : Frame), m.frames.size < ((m.frames.push f1).push f2).size := by
          intro f1 f2; simp only [Array.size_push]
          exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)
        have hltB : ∀ (f1 f2 : Frame),
            (m.frames.push f1).size < ((m.frames.push f1).push f2).size := by
          intro f1 f2; simp only [Array.size_push]; exact Nat.lt_succ_self _
        have hgetI : ∀ (f1 f2 : Frame),
            ((m.frames.push f1).push f2).getD m.frames.size default = f1 := by
          intro f1 f2
          rw [getD_push_lt _ _ _ (by
              simp only [Array.size_push]; exact Nat.lt_succ_self _), getD_push_lt_self]
        refine ⟨NoHook_grow hg hsat hhook, Saturated_grow hg.shapeAgree hg.size hsat,
          LitClsOk_grow hg hstr, ClassOk_grow hg hsat hcls,
          BottomObj_cons (by simp) (BottomObj_cons hne
            (BottomObj_push (fun g hgm => by
                have h0 := hlt g hgm; simp only [Array.size_push]; exact Nat.lt_succ_of_lt h0)
              (BottomObj_push hlt hbot))),
          (by
            simpa [withKont, framePopLabels, dropLast_cons_ne hne] using hks),
          ?_, D, blockCtx ctx, (x2, Ty.any) :: anyEnv Γk,
          ({ cls := "Array" }, []) :: (ctx, Γk2) :: Γs,
          DeclsOk_grow hg hsat htab, ?_, ?_, ?_, ?_⟩
        · -- `ClosuresOk`: the two konts the call pushes carry the **fresh** closure, whose
          -- captured frame is the send site's.
          simp only [withKont]
          intro κ hm cl' hcl'
          have hfacts : ∀ (f1 f2 : Frame) (h' : Heap),
              (∀ kk, h'.classPayload? kk = m.heap.classPayload? kk) →
              ∀ cl0 : Closure, cl0.captured = m.stack.headD 0 →
              cl0.captured < ((m.frames.push f1).push f2).size ∧
              (((m.frames.push f1).push f2).getD cl0.captured default).captured = none ∧
              (h'.classPayload? (((m.frames.push f1).push f2).getD cl0.captured
                default).defmod).isSome = true ∧
              Boot.objectId ∈ (((m.frames.push f1).push f2).getD cl0.captured default).cref := by
            intro f1 f2 h' hpp cl0 hc0
            have h1 : cl0.captured < m.frames.size := hc0 ▸ hclt
            have h2 : ((m.frames.push f1).push f2).getD cl0.captured default
                = m.frames.getD cl0.captured default := by
              rw [getD_push_lt _ _ _ (by
                  simp only [Array.size_push]; exact Nat.lt_succ_of_lt h1),
                getD_push_lt _ _ _ h1]
            refine ⟨by
                simp only [Array.size_push]
                exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt h1),
              by rw [h2, hc0]; exact hcapn,
              by rw [h2, hc0, hpp]; exact hcap3.1,
              by rw [h2, hc0]; exact hcap3.2⟩
          rcases List.mem_cons.mp hm with rfl | hm₁
          · exact hfacts _ _ _ (fun kk => hg.payload kk) cl' (by
              simp only [KontClosure, Option.some.injEq] at hcl'; rw [← hcl']; rfl)
          · rcases List.mem_cons.mp hm₁ with rfl | hm₂
            · exact hfacts _ _ _ (fun kk => hg.payload kk) cl' (by
                simp only [KontClosure, Option.some.injEq] at hcl'; rw [← hcl']; rfl)
            · rcases List.mem_cons.mp hm₂ with rfl | hm₃
              · exact absurd hcl' (by simp [KontClosure])
              · obtain ⟨hlt0, hcapn0, hpay0, hcref0⟩ :=
                  hclo κ (by rw [hK]; exact List.mem_cons_of_mem _ hm₃) cl' hcl'
                exact ⟨hlt2 _ _ _ hlt0,
                  by rw [hpop _ _ _ hlt0]; exact hcapn0,
                  by rw [hpop _ _ _ hlt0, hg.payload]; exact hpay0,
                  by rw [hpop _ _ _ hlt0]; exact hcref0⟩
        · -- `FramesOk` at the fresh block frame, then the iterator's, then the caller's.
          simp only [withKont]
          refine FramesOk.cons (hltB _ _) ?_
            (FrameConforms.mk' ?_ ?_ ?_)
            (FramesOk.cons (hltI _ _) hlt
              (FrameConforms.mk' (ShallowChain.of_none (by rw [hgetI]))
                ?_ (fun y σ hy => absurd hy (by simp [envGet?])))
              (FramesOk.push (FramesOk.push
                (FramesOk.narrowHead hsuE2 (FramesOk.heap_congr hag hfs)))))
          · intro g hgm
            rcases List.mem_cons.mp hgm with rfl | hgm'
            · simp only [Array.size_push]; exact Nat.lt_succ_self _
            · simp only [Array.size_push]; exact Nat.lt_succ_of_lt (hlt g hgm')
          · intro q hq
            rw [getD_push_lt_self] at hq
            simp only [Option.some.injEq] at hq
            subst hq
            refine ⟨by simp only [Array.size_push]; exact Nat.lt_succ_of_lt hclt, ?_⟩
            rw [hbc, hpop _ _ _ hclt]
            exact hcapn
          · rw [getD_push_lt_self, hbc, getD_push_lt _ _ _ hclt, hg.payload]
            exact hcap3.1
          · intro y σ hy
            rw [hany y σ hy]
            exact ValueTy.any
          · rw [hgetI]
            show (Heap.classPayload? _ (classOf _ (.ref o))).isSome = true
            rw [hg.payload, hg.classOf_eq holt]; exact htc.1
        · -- `StackCtx` at the block frame, then at the iterator activation.
          simp only [withKont]
          refine StackCtx.cons ?_ (fun hq => absurd hq (by simp [blockCtx])) ?_
            (fun sc hsc' => absurd hsc' (by simp [blockCtx])) ?_ (Or.inr rfl)
            (fun mn hmn => absurd hmn (by simp [blockCtx]))
            (fun hq => absurd hq (by simp [blockCtx]))
            (fun hcb _ => by simp [blockCtx] at hcb)
            (StackCtx.cons ?_ ?_ ?_ (fun sc hsc' => absurd hsc' (by simp)) ?_ (Or.inr rfl)
              (fun mn hmn => absurd hmn (by simp)) (fun _ => ?_)
              (fun hcb _ => nomatch hcb)
              (StackCtx.push
                (fun g hgm => by
                  simp only [Array.size_push]; exact Nat.lt_succ_of_lt (hlt g hgm))
                (StackCtx.push hlt (StackCtx.heap_congr hag hsc))))
          · rw [getD_push_lt_self, hbc, getD_push_lt _ _ _ hclt, hg.payload]; exact hcap3.1
          · intro _; rw [getD_push_lt_self]; simp [defVisOfDef]
          · rw [getD_push_lt_self, hbc, getD_push_lt _ _ _ hclt]; exact hcap3.2
          · rw [hgetI]
            show (Heap.classPayload? _ (classOf _ (.ref o))).isSome = true
            rw [hg.payload, hg.classOf_eq holt]; exact htc.1
          · intro _
            rw [hgetI]
            show className _ (classOf _ (.ref o)) = "Array"
            rw [hg.classOf_eq holt, hg.className_eq]; exact htc.2
          · intro _
            rw [hgetI]; simp [defVisOfDef]
          · rw [hgetI]
            show Boot.objectId ∈ m.currentFrame.cref
            rw [currentFrame_eq hne]
            cases hst : m.stack with
            | nil => exact absurd hst hne
            | cons fid0 fids0 =>
              rw [hst] at hsc
              simpa [curFrame, curFid, hst] using hsc.2.2.2.2.1
          · rw [hgetI]
        · simp only [withKont]; exact GlobalsOk.congr hag hglob
        · -- The block body runs, under the `blkFrameK` that pops its frame and the fresh
          -- `iterK` that remembers the rest of the loop.
          refine ⟨τb2, βret2, Γb'2, D, (x2, Ty.any) :: anyEnv Γk, hbody, hsb, hsu2,
            KontOk.blkFrameK rfl rfl (subTy_refl _)
              (KontOk.iterK (bs := { params := [Ty.any], ret := βret2 })
                rfl rfl rfl rfl rfl ?_ rfl rfl rfl rfl rfl
                hbody hsu2 hsb ?_ (subTy_refl _)
                (ValueTy.congr hag hv) hsw rfl rfl
                (KontOk.frameK (fun σ hq => absurd hq (by simp)) rfl
                  (KontOk.heap_congr hag hk'2)))⟩
          · intro e he
            obtain ⟨e0, -, rfl⟩ := List.mem_map.mp he
            rfl
          · intro a ha
            obtain ⟨e0, -, rfl⟩ := List.mem_map.mp ha
            exact ⟨⟨Ty.any, ValueTy.any, by simp [subTy]⟩, trivial⟩
    -- **The native iterator's loop, one turn** (L253).
    | @iterK _ _ cΓ Γs _ τ' τr τbody σp bs cb Γb Γb' outer x cl brk rest acc retVal cur k
        hp hlo hlam hbp hgb hany hcbr hcbl hcbs hcbm hcbi hbody hsub hsb hvs hsr hrv hrt
        hcr hci hk' =>
      cases rest with
      | nil =>
        -- The loop is done: `iterStep` delivers the iterator's own answer, and the
        -- `frameK` below is what pops its activation.
        exact inv_value hfs htab hsc hhook hsat hstr hcls hbot
          (by simpa [framePopLabels] using hks) (ValueTy.weaken hrv hrt) hk'
          (hclo := hcloTail hK)
      | cons a rest' =>
        obtain ⟨a₀, rfl⟩ : ∃ a₀, a = [a₀] := by
          have hva := hvs a (by simp)
          rw [hbp] at hva
          match a, hva with
          | [a₀], _ => exact ⟨a₀, rfl⟩
        show StepOk (Interp.iterStep { m with kont := k } cl brk ([a₀] :: rest')
          .ignore acc retVal)
        rw [iterStep_cons, callClosure_req1 (cl := cl) hp hlo hlam]
        -- `ClosuresOk` is what says the captured frame exists and is self-contained —
        -- the *whole* frame-side price of the call (L248/L251).
        obtain ⟨hcaplt, hcapn, hcappay, hcapcref⟩ :=
          hclo _ (by rw [hK]; exact List.mem_cons_self ..) cl (by simp [KontClosure])
        have hne : m.stack ≠ [] := hfsh.1
        have hlt : ∀ g ∈ m.stack, g < m.frames.size := hfs.mem_lt
        obtain ⟨ca₀, hva₀, hsa₀⟩ : ∃ σ, ValueTy m.heap a₀ σ ∧ subTy σ σp = true := by
          have hva := hvs [a₀] (by simp)
          rw [hbp] at hva
          exact hva.1
        refine ⟨hhook, hsat, hstr, hcls,
          BottomObj_cons hne (BottomObj_push hlt hbot),
          -- L245: the block push writes a `blkFrameK` and a stack entry at the same id,
          -- and the `iterK` between them pops nothing.
          (by simpa [withKont, framePopLabels, dropLast_cons_ne hne] using hks),
          -- L248: the two new konts carry the closure the old one did.
          (ClosuresOk.transport hclo
            (by
              intro κ hm cl' hcl'
              -- The two konts the call pushes carry the closure the old `iterK` did;
              -- everything below them was already there.
              rcases List.mem_cons.mp hm with rfl | hm₁
              · exact ⟨Kont.iterK cl brk ([a₀] :: rest') .ignore acc retVal cur,
                  by rw [hK]; exact List.mem_cons_self .., by simpa [KontClosure] using hcl'⟩
              · rcases List.mem_cons.mp hm₁ with rfl | hm₂
                · exact ⟨Kont.iterK cl brk ([a₀] :: rest') .ignore acc retVal cur,
                    by rw [hK]; exact List.mem_cons_self .., by simpa [KontClosure] using hcl'⟩
                · exact ⟨κ, by rw [hK]; exact List.mem_cons_of_mem _ hm₂, hcl'⟩)
            (by simp [withKont, Array.size_push])
            (by
              intro p hp'
              show FrameShape ((m.frames.push _).getD p default) _
              rw [getD_push_lt _ _ _ hp']; exact FrameShape.rfl' _)
            (by intro o ho; exact ho)),
          _, cb, Γb, (ctx, Γk) :: Γs, htab, ?_, ?_, hglob, ?_⟩
        · -- `FrameConforms` at the fresh block frame.
          simp only [withKont]
          refine ⟨by rw [Array.size_push]; exact Nat.lt_succ_self _, hlt,
            ⟨?_, ?_, ?_⟩, FramesOk.push hfs⟩
          · -- `ShallowChain`: one hop, and it lands on a self-contained frame.
            intro q hq
            rw [getD_push_lt_self] at hq
            simp only [Option.some.injEq] at hq
            subst hq
            exact ⟨hcaplt, by rw [getD_push_lt _ _ _ hcaplt]; exact hcapn⟩
          · rw [getD_push_lt_self]; exact hcappay
          · -- The parameter is in the frame's **own** locals, so its read is one lookup;
            -- every other name is `.any`, and `ValueTy _ _ .any` holds of every value
            -- (L232) — which is why the captured frame's environment is not needed here.
            intro y σ hy
            rw [hgb] at hy
            by_cases hyx : y = x
            · subst hyx
              have hσ : σ = σp := by
                simpa [envGet?, List.find?] using hy.symm
              subst hσ
              rw [show localOfIn (m.frames.push _) ((m.frames.push _).getD m.frames.size default) y
                  = a₀ from by rw [getD_push_lt_self]; simp [localOfIn, List.find?]]
              exact ValueTy.weaken hva₀ hsa₀
            · have hmem : ∃ e ∈ outer, e.2 = σ := by
                have hy' : envGet? outer y = some σ := by
                  have hxy : (x == y) = false := by simpa using fun hq => hyx hq.symm
                  simpa [envGet?, List.find?, hxy] using hy
                unfold envGet? at hy'
                cases hf : outer.find? (fun p => p.1 == y) with
                | none => rw [hf] at hy'; exact absurd hy' (by simp)
                | some e =>
                  rw [hf] at hy'
                  exact ⟨e, List.mem_of_find?_eq_some hf, by simpa using hy'⟩
              obtain ⟨e, hem, he⟩ := hmem
              rw [← he, hany e hem]
              exact ValueTy.any
        · -- `StackCtx` at the block frame: four of the seven clauses are vacuous because
          -- the block's context claims no name, no self and no method (L250), and the
          -- three that are not are `ClosuresOk`'s (L251) read through
          -- `callClosure`'s copy.
          simp only [withKont]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, (fun _ hb => absurd (hcbi ▸ hb) (by simp)),
            StackCtx.push hlt hsc⟩
          · rw [getD_push_lt_self]; exact hcappay
          · intro hb; exact absurd (hcbi ▸ hb) (by simp)
          · intro _; rw [getD_push_lt_self]; simp [defVisOfDef]
          · exact fun sc hsc' => absurd (hcbs ▸ hsc') (by simp)
          · rw [getD_push_lt_self]; exact hcapcref
          · exact Or.inr hcbr
          · exact fun mn hmn => absurd (hcbm ▸ hmn) (by simp)
          · intro hb; exact absurd (hcbi ▸ hb) (by simp)
        · -- The block body is what runs, under the `blkFrameK` that pops its frame and
          -- the fresh `iterK` that remembers the rest of the loop.
          exact ⟨τbody, bs.ret, Γb', D, Γb, hbody, hsb, hsub,
            KontOk.blkFrameK hcbr hcbl (subTy_refl _)
              (KontOk.iterK hp hlo hlam hbp hgb hany hcbr hcbl hcbs hcbm hcbi hbody hsub
                hsb (fun a hm => hvs a (List.mem_cons_of_mem _ hm)) (subTy_refl _)
                hrv hrt hcr hci hk')⟩
    | @frameK _ _ _ cΓ' Γs _ fid k hrt hil hk' =>
      -- The activation pops: `frames` is untouched, `stack` loses its head, and
      -- the caller's environment — carried all along by `FramesOk` — becomes
      -- current again. This is the case L91 could not close.
      obtain ⟨c', Γ'⟩ := cΓ'
      -- **L199: the pop moves both lists** — and reading the clause backwards is also
      -- what says `fid` *is* the stack's head, which is the fact the `return` rule
      -- needs and the reason this conjunct exists at all.
      have hst2 : ∃ f0 f1 rest, m.stack = f0 :: f1 :: rest := by
        cases hst : m.stack with
        | nil => rw [hst] at hfs; exact absurd hfs (by simp [FramesOk])
        | cons f0 t =>
          cases ht : t with
          | nil => rw [hst, ht] at hfs; exact absurd hfs (by simp [FramesOk])
          | cons f1 rest => exact ⟨f0, f1, rest, rfl⟩
      obtain ⟨f0, f1, rest, hst⟩ := hst2
      have hlab : framePopLabels k = m.stack.tail.dropLast := by
        have hq := hks
        simp only [framePopLabels] at hq
        rw [hst] at hq ⊢
        simp only [List.dropLast_cons_cons, List.cons.injEq] at hq
        simpa using hq.2
      refine ⟨hhook, hsat, hstr, hcls, BottomObj_tail hbot, hlab,
        ClosuresOk.konts (hcloTail hK) rfl rfl (by intro κ hm; exact Or.inl hm),
        _, c', Γ', Γs, htab,
        hfs.tail, ?_, hglob, ⟨τ, _, hv, SubEnv.refl _, hk'⟩⟩
      -- `StackCtx` pops with the environment stack, which is the whole point of
      -- pairing the two: the caller's context is the second component of the list
      -- rather than a fact `frameK` has to be handed.
      exact StackCtx.tail hsc
    -- **The receiver has arrived** (L175). `startArgs` peels the *first* argument
    -- and pushes one `argsK` for it; the remaining arguments ride in the kont as
    -- unevaluated program, exactly as `seqK`'s do. So this case is one
    -- `inferArgs_cons_inv` and one `KontOk.argsK` at the empty accumulator.
    | @recvK _ _ _ _ _ _ _ mname arg args τs ps τret τw Γ₂ k _ _ hargs hsg hsub hsw hk' hsu =>
      obtain ⟨τe, Γ₁, D₁, τrest, rfl, he, hrest⟩ := inferArgs_cons_inv hargs
      obtain ⟨τp, psrest, rfl, hs1, hs2⟩ := subTys_cons_inv hsub
      have hsp : ∀ e, arg ≠ .splat e := by
        rintro e rfl; exact absurd he (by simp [infer])
      have hkw : ∀ es, arg ≠ .kwargs es := by
        rintro es rfl; exact absurd he (by simp [infer])
      have hfw : arg ≠ .fwd := by
        rintro rfl; exact absurd he (by simp [infer])
      dsimp only
      rw [startArgs_plain hsp hkw hfw]
      exact inv_push hfs htab hsc hhook hsat hstr hcls hbot (by simpa [framePopLabels] using hks) he
        (KontOk.argsK (psacc := []) hv trivial hs1 hrest hs2
          (by simpa using hsg) hsw hk') (hclo := hcloTail hK)
    -- **The zero-argument dispatch** (L152). `applyKont` runs `startArgs … [] []`,
    -- which is `finishSend` with no argument continuation in between — so this case
    -- ends where `argsK`'s does, one step earlier, and it is `entry_dispatch` at
    -- `args = []` rather than a second dispatch lemma. `ValuesTy _ [] []` is
    -- `trivial`, which is the whole of what the empty parameter list costs.
    | @recvK0 _ _ _ _ _ _ mname τret τw k Γj _ hsg hsw hk' hsu =>
      have hfs := FramesOk.narrowHead hsu hfs
      dsimp only
      -- **L260: a nilable receiver is reduced to the arm the value actually is**, and
      -- that is the whole of the union rule at a dispatch site. The three facts are
      -- re-bound at the atomic type, so everything below is the case as it was.
      obtain ⟨τ, hsg, hv, hnilτ⟩ := sigOf_value_atomic hsg hv
      -- **The two witness kinds land different steps** (L157), which is why
      -- `EntryOk` is a disjunction and why this case is the first to case on it.
      rcases (htab.1 τ mname _ (sigOf_declFor hnilτ hsg)).blockless with hbi |
        ⟨mdu, cu, htys, hresu, hnmu, hconfu⟩
      · obtain ⟨w, m', hw, hg', hfr', hst', hko', hgv', hstep⟩ :=
          entry_dispatch (m := { m with kont := k }) (recv := v) (args := [])
            (sigOf_atomic hnilτ hsg).1 (sigOf_atomic hnilτ hsg).2.1
            (sigOf_atomic hnilτ hsg).2.2 hbi hv trivial
        rw [hstep]
        exact inv_grow_value (m := { m with kont := k })
          hfs htab hsc hhook hsat hstr hcls hbot
          (by simpa [framePopLabels] using hks) hg' hfr' hst' hko'
          (ValueTy.weaken hw hsw) hk' hglob hgv' (hclo := hcloTail hK)
      · -- The user branch: no value, a **frame**. `user_dispatch` supplies the step;
        -- the heap is untouched, so all five heap conjuncts pass straight through and
        -- what is left is the push and the callee's `CtlOk`.
        -- L185: `user_dispatch` pins the receiver's type to the class arm, and
        -- `UserEntryOk` supplies exactly that — so the substitution is the whole
        -- adjustment.
        --
        -- **L241 made the key a relation**, so there are two shapes to case on, and the
        -- second is refuted *here* rather than by the witness: `tyClassNames` is `[]` at
        -- `arrayOf`, so a row cannot be read at it. This is the case that becomes real the
        -- day dispatch lands, and it is the honest place for that bill to show up.
        rcases htys with rfl | ⟨⟨e, rfl⟩, rfl⟩
        case inr =>
          simp only [sigOf, declFor, tyClassNames] at hsg
          exact absurd hsg (by simp)
        have hru := hresu _ (valueTy_tyClass (by simp) (by simp) (by simp) hv)
        have hown : (m.heap.classPayload? mdu.owner).isSome := by
          obtain ⟨_, _, _, _, _, _, _, _, h9, _⟩ := hru; exact h9
        rw [user_dispatch (m := { m with kont := k }) hru hv]
        have hlt : ∀ g ∈ m.stack, g < m.frames.size := hfs.mem_lt
        obtain ⟨hdp, hdblk, hdfu, Γb, r, τb, hbu, hsb, hag⟩ := hconfu
        refine ⟨hhook, hsat, hstr, hcls,
          BottomObj_cons hfsh.1 (BottomObj_push hlt hbot),
          (by rw [dropLast_cons_ne hfsh.1]; simpa [framePopLabels] using hks),
          ClosuresOk.pushFrame (hcloTail hK) rfl rfl rfl, _,
          { cls := cu, selfCls := some cu, ret := r, meth := some mname,
            params := some [] }, [],
          (ctx, Γj) :: Γs, htab, ?_, ?_, hglob, ?_⟩
        · -- `FrameConforms` at the activation: `userFrame` leaves `captured` at its
          -- default, its definee **is** `md.owner`, and `ResolvesUser` carries that
          -- that id is a class — the clause the user arm has and `ResolvesAt` does
          -- not need.
          refine ⟨by rw [Array.size_push]; exact Nat.lt_succ_self _, hlt,
            ⟨ShallowChain.of_none (by rw [getD_push_lt_self]; rfl), ?_, ?_⟩,
            FramesOk.push hfs⟩
          · rw [getD_push_lt_self]; exact hown
          · intro y σ hy; exact absurd hy (by simp [envGet?])
        · -- **The activation's static context is the owner's class name** (F1b.9),
          -- which is the clause `UserEntryOk` carries beside the body's typing: the
          -- body was checked in the class it is defined on, and `userFrame`'s definee
          -- **is** `md.owner`. `defVis` is the frame literal's default, which is what
          -- makes a `def` in a method body public — and it is `UserConforms`'s
          -- `defFree` restriction, not this, that keeps one out of the fragment.
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, (fun hcb _ => nomatch hcb),
            StackCtx.push hlt hsc⟩
          · rw [getD_push_lt_self]; exact hown
          · rw [getD_push_lt_self]; exact fun _ => hnmu
          · rw [getD_push_lt_self]; exact fun _ => rfl
          · intro sc hsc'
            simp only [Option.some.injEq] at hsc'
            subst hsc'
            rw [getD_push_lt_self]
            -- L209: as at the self-send push — `userFrame`'s definee is `md.owner`
            -- and the row's resolution puts it on the receiver's chain.
            obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hch, _⟩ := hru
            exact ⟨hv, hch⟩
          -- L189: `ResolvesUser`'s tenth clause, spent here.
          · rw [getD_push_lt_self]
            obtain ⟨_, _, _, _, _, _, _, _, _, _, hcr, _, _⟩ := hru
            exact hcr
          -- L198/L200: `userFrame`'s kind, and the caller is on the list.
          · exact Or.inl ⟨by rw [getD_push_lt_self]; rfl, by simp⟩
          -- L210: as at the self-send push — `ResolvesUser`'s `superName` clause.
          · intro mn hmn
            simp only [Option.some.injEq] at hmn
            subst hmn
            rw [getD_push_lt_self]
            obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hsn⟩ := hru
            exact ⟨by simp [userFrame, hsn], rfl, rfl, rfl, rfl, rfl, rfl⟩
          -- L243: `userFrame` leaves `captured` at its default.
          · rw [getD_push_lt_self]; exact fun _ => rfl
        · -- The callee's body, typed at the **declared return type**: that is what
          -- makes `frameK` — which has always resumed the caller at the in-flight
          -- type — line the activation's answer up with the send's continuation.
          exact ⟨τb, τw, Γb, _, _, hbu, subTy_trans hsb hsw, SubEnv.refl _,
            KontOk.frameK (fun σ h => by rw [hag σ (by simpa using h)]; exact hsw) rfl hk'⟩
    -- **An array element has arrived** (L174/L230), and since L230 the whole case is one
    -- lemma application: `inv_continueArray` is the loop, and this is one of its three
    -- entry points.
    | @arrK _ _ _ _ _ _ _ τ' τw acc rest Γ' k _ hs hsw hk' hsu =>
      exact inv_continueArray (m := { m with kont := k })
        hfs htab hsc hhook hsat hstr hcls hbot (by simpa [framePopLabels] using hks) hglob
        hs hsw hk' (hclo := hcloTail hK)
    -- **A splatted element's operand has arrived** (L230), and the *spread* is the step:
    -- `spreadA` answers the array's elements and leaves the machine alone, which is what
    -- `arrSplatK`'s type premise buys through `plainRecv`'s sixth clause. After it, the
    -- literal continues at a longer accumulator — the same loop, so the same lemma.
    | @arrSplatK _ _ _ _ _ _ _ τ' τw acc rest Γ' k _ hva hs hsw hk' hsu =>
      obtain ⟨vs, hsp⟩ := spreadA_of_array (m := { m with kont := k })
        (ValueTy.weaken hv hva)
      simp only [hsp]
      exact inv_continueArray (m := { m with kont := k })
        hfs htab hsc hhook hsat hstr hcls hbot (by simpa [framePopLabels] using hks) hglob
        hs hsw hk' (hclo := hcloTail hK)
    -- **A `super` argument has arrived** (L212), and it is `argsK`'s case with the
    -- receiver read out of the frame instead of out of the kont. The frame facts are
    -- re-derived here rather than threaded through the continuation, because `StackCtx`
    -- is indexed by the machine and this step changes neither `frames` nor `stack`.
    | @superArgsK _ _ _ _ _ _ _ mname psacc τp τrest psrest τret τw acc rest Γ' k blk dd _
        hva hst hrest hsr hmn hne hrow hpeq hret hsw hk' hsu =>
      have hfacts : (m.frames.getD (methodFrameOf m) default).meth = mname ∧
          (m.heap.classPayload?
            (m.frames.getD (methodFrameOf m) default).defmod).isSome ∧
          className m.heap (m.frames.getD (methodFrameOf m) default).defmod = ctx.cls ∧
          (m.frames.getD (methodFrameOf m) default).defmod ∈
            ancestors m.heap
              (classOf m.heap (m.frames.getD (methodFrameOf m) default).self) ∧
          ValueTy m.heap (m.frames.getD (methodFrameOf m) default).self (.cls ctx.cls) := by
        cases hst' : m.stack with
        | nil => exact absurd hst' hfsh.1
        | cons fid fids =>
          have hsc' := hsc
          rw [hst'] at hsc'
          obtain ⟨hm, hkd, hself, -, -, -, hnb⟩ := hsc'.2.2.2.2.2.2.1 mname hmn
          obtain ⟨hty, hch⟩ := hsc'.2.2.2.1 ctx.cls hself
          have hcur : m.frames.getD fid default
              = m.frames.getD (methodFrameOf m) default := by
            simp only [methodFrameOf, hst', List.headD_cons, hkd]
          rw [← hcur]
          exact ⟨hm, hsc'.1, hsc'.2.1 hnb, hch, hty⟩
      obtain ⟨hm, hdp, hdn, hch, hty⟩ := hfacts
      cases rest with
      | nil =>
        simp only [inferArgs, Option.some.injEq, Prod.mk.injEq] at hrest
        obtain ⟨rfl, rfl, rfl⟩ := hrest
        have hpr : psrest = [] := subTys_nil_inv hsr
        subst hpr
        dsimp only
        obtain ⟨w, m', hw, hg', hfr', hst', hko', hgv', hstep⟩ :=
          super_dispatch (m := { m with kont := k }) (args := acc ++ [v]) (blk := blk)
            hne (htab.2.2.2.2 _ _ _ hrow) hm hdp hdn hch hty
            (by rw [hpeq]; exact ValuesTy_snoc hva hv hst)
        rw [show startSuperArgs { m with kont := k } (acc ++ [v]) [] blk
            = doSuper { m with kont := k } (acc ++ [v]) blk from rfl, hstep]
        exact inv_grow_value (m := { m with kont := k })
          hfs htab hsc hhook hsat hstr hcls hbot
          (by simpa [framePopLabels] using hks) hg' hfr' hst' hko'
          (ValueTy.weaken (hret ▸ hw) hsw) hk' hglob hgv' (hclo := hcloTail hK)
      | cons e rest' =>
        obtain ⟨τe, Γ₁, D₁, τrest', rfl, he, hrest'⟩ := inferArgs_cons_inv hrest
        obtain ⟨τp', psrest', rfl, hs1, hs2⟩ := subTys_cons_inv hsr
        have hsp : ∀ x, e ≠ .splat x := by
          rintro x rfl; exact absurd he (by simp [infer])
        have hkw : ∀ es, e ≠ .kwargs es := by
          rintro es rfl; exact absurd he (by simp [infer])
        have hfw : e ≠ .fwd := by
          rintro rfl; exact absurd he (by simp [infer])
        dsimp only
        rw [startSuperArgs_plain hsp hkw hfw]
        exact inv_push (m := { m with kont := k })
          hfs htab hsc hhook hsat hstr hcls hbot (by simpa [framePopLabels] using hks) he
          (KontOk.superArgsK (psacc := psacc ++ [τp]) (ValuesTy_snoc hva hv hst) hs1
            hrest' hs2 hmn hne hrow (by rw [hpeq]; simp) hret hsw hk') (hclo := hcloTail hK)
    | @argsK _ _ _ _ _ _ _ mname recv τr psacc τp τrest psrest τret τw acc rest Γ' k _ _
        hrv hva hst hrest hsr hsg hsw hk' hsu =>
      cases rest with
      -- **The last argument** (L175). `startArgs … (acc ++ [v]) []` is
      -- `finishSend`, so the send completes in this step, and the arguments'
      -- `ValuesTy` is the accumulated one snoc'd with the in-flight value —
      -- `ValuesTy_snoc`, matched against the signature's parameter list split at
      -- exactly the same point. Since L183 the match is `subTy`, so what is snoc'd
      -- is the *declared* parameter `τp` and the in-flight type only has to be
      -- below it.
      --
      -- **F1a: one dispatch step for every declared method**, where P0 had a
      -- three-way `rcases` over the tabulated names and a rewrite per name. The
      -- invariant supplies the entry, `entry_dispatch` supplies the step, and the
      -- ~128 conformance lemmas of F6 become witnesses of the same clause rather
      -- than a parallel obligation (`typing-a-mutable-method-table.md` §7).
      | nil =>
        simp only [inferArgs, Option.some.injEq, Prod.mk.injEq] at hrest
        obtain ⟨rfl, rfl, rfl⟩ := hrest
        have hpr : psrest = [] := subTys_nil_inv hsr
        subst hpr
        dsimp only
        -- L260, as in the `recvK0` case: the nilable receiver is reduced to the arm the
        -- value is, and the three facts are re-bound at the atomic type.
        obtain ⟨τr, hsgA, hrv, hnilτ⟩ := sigOf_value_atomic (by simpa using hsg) hrv
        -- **The user arm is refuted rather than handled**, and by arithmetic rather
        -- than by anything about dispatch: `UserConforms` requires `d.params = []`
        -- (a zero-parameter method is all `enterUserMethod` binds today) while this
        -- declaration's is `psacc ++ [τp]`, which a snoc can never be. So a send
        -- with arguments is a builtin send, necessarily — at every arity.
        have hbi : BuiltinEntryOk m.heap τr mname
            { params := psacc ++ [τp], ret := τret } := by
          rcases (htab.1 τr mname _ (sigOf_declFor hnilτ hsgA)).blockless with
            hb | ⟨_, _, _, _, _, hdp, _, _⟩
          · exact hb
          · exact absurd hdp (by simp)
        obtain ⟨w, m', hw, hg', hfr', hst', hko', hgv', hstep⟩ :=
          entry_dispatch (m := { m with kont := k }) (recv := recv) (args := acc ++ [v])
            (sigOf_atomic hnilτ hsgA).1 (sigOf_atomic hnilτ hsgA).2.1
            (sigOf_atomic hnilτ hsgA).2.2
            hbi hrv (ValuesTy_snoc hva hv hst)
        rw [hstep]
        exact inv_grow_value (m := { m with kont := k })
          hfs htab hsc hhook hsat hstr hcls hbot
          (by simpa [framePopLabels] using hks) hg' hfr' hst' hko'
          (ValueTy.weaken hw hsw) hk' hglob hgv' (hclo := hcloTail hK)
      -- **Another argument to run.** One value moves from the unevaluated tail to
      -- the accumulated prefix, and the signature's split point moves with it —
      -- which is the `List.append_assoc` the `simpa` below discharges.
      | cons e rest' =>
        obtain ⟨τe, Γ₁, D₁, τrest', rfl, he, hrest'⟩ := inferArgs_cons_inv hrest
        obtain ⟨τp', psrest', rfl, hs1, hs2⟩ := subTys_cons_inv hsr
        have hsp : ∀ x, e ≠ .splat x := by
          rintro x rfl; exact absurd he (by simp [infer])
        have hkw : ∀ es, e ≠ .kwargs es := by
          rintro es rfl; exact absurd he (by simp [infer])
        have hfw : e ≠ .fwd := by
          rintro rfl; exact absurd he (by simp [infer])
        dsimp only
        rw [startArgs_plain hsp hkw hfw]
        exact inv_push (m := { m with kont := k })
          hfs htab hsc hhook hsat hstr hcls hbot (by simpa [framePopLabels] using hks) he
          (KontOk.argsK (psacc := psacc ++ [τp]) hrv (ValuesTy_snoc hva hv hst) hs1
            hrest' hs2 (by simpa using hsg) hsw hk') (hclo := hcloTail hK)
  · -- ## control = jump — **inhabited since L200, and only by `.retJ`**
    --
    -- The unwinding is two cases and both are read off `RetOk`. Every kont the fragment
    -- stacks except `frameK` is *transparent* to a `.retJ` — `unwind`'s catch-all
    -- passes a jump on unchanged and the two loop markers pass a `.retJ` on explicitly
    -- — so `skip` is one lemma application; and at the `frameK` the target matches,
    -- because L199's clause says the label *is* the stack's head and `firstFrameK`
    -- carries that through the transparent prefix.
    rw [hctl] at hc
    cases j with
    | retJ v target =>
      obtain ⟨σ, hv, hro, hff⟩ := hc
      simp only [stepFn, hctl]
      generalize hK : m.kont = K at hro hff hks ⊢
      cases hro with
      | skip hκ hro' =>
        rw [unwind_ret_transparent (m := m) hκ hK]
        refine ⟨hhook, hsat, hstr, hcls, hbot, ?_,
          ClosuresOk.konts (hcloTail hK) rfl rfl (by intro κ hm; exact Or.inl hm),
          D, ctx, Γ, Γs, htab, hfs, hsc, hglob,
          ⟨σ, hv, hro', ?_⟩⟩
        · simp only [withCtl]
          rw [← hks, framePopLabels_transparent hκ]
        · simp only [withCtl]
          rw [← hff, firstFrameK_transparent hκ]
      | here hsubf hkf =>
        rename_i τf fid kf
        -- The target *is* this frame: `firstFrameK (frameK fid :: kf) = some fid`.
        have htg : target = fid := by simpa [firstFrameK] using hff.symm
        subst htg
        rw [show Interp.unwind m (.retJ v target)
              = .next (Interp.withCtl
                  { m with kont := kf, stack := m.stack.tail } (.value v)) from by
          unfold Interp.unwind
          rw [hK]
          simp only [beq_self_eq_true, if_true, Interp.withCtl]]
        -- **The stack has at least two entries**, and `hks` is what says so: the
        -- continuation has a `frameK`, so `m.stack.dropLast` is a cons.
        cases hst : m.stack with
        | nil => rw [hst] at hks; simp [framePopLabels] at hks
        | cons f0 t =>
          cases ht : t with
          | nil => rw [hst, ht] at hks; simp [framePopLabels] at hks
          | cons f1 rest =>
            have hlab : framePopLabels kf = m.stack.tail.dropLast := by
              have hq := hks
              simp only [framePopLabels] at hq
              rw [hst, ht] at hq ⊢
              simp only [List.dropLast_cons_cons, List.cons.injEq] at hq
              simpa using hq.2
            rw [hst, ht] at hbot hfs hsc hlab
            cases hΓ : Γs with
            | nil =>
              rw [hΓ] at hfs
              exact absurd hfs.2.2.2 (by simp [FramesOk])
            | cons cΓb Γsb =>
              obtain ⟨c', Γ'⟩ := cΓb
              rw [hΓ] at hfs hsc hkf
              exact ⟨hhook, hsat, hstr, hcls, BottomObj_tail hbot, hlab,
                ClosuresOk.konts (hcloTail hK) rfl rfl (by intro κ hm; exact Or.inl hm),
                D, c', Γ', Γsb, htab, hfs.tail, StackCtx.tail hsc, hglob,
                ⟨τf, _, ValueTy.weaken hv hsubf, SubEnv.refl _, hkf⟩⟩
    -- **A raise in flight** (L217), and it is the shortest jump case in the file:
    -- `unwind` never inspects the *value*, so there is no type to line up and no
    -- `frameK` agreement to spend. `RaiseOk` was destructured before the `stepFn`
    -- unfold for `RetOk`'s reason — the relation's shape is what picks the kont.
    | raiseJ exc =>
      obtain ⟨hne, hro⟩ := hc
      simp only [stepFn, hctl]
      generalize hK : m.kont = K at hro hks ⊢
      cases hro with
      | nil =>
        -- `[]`: the raise escapes to `.uncaught`, and `StepOk`'s L216 clause *is* the
        -- hypothesis — which is the whole content of that commit, cashed here.
        rw [show Interp.unwind m (.raiseJ exc) = .uncaught exc m from by
          unfold Interp.unwind; rw [hK]]
        exact hne
      | skip hκ hro' =>
        -- A transparent kont: pop it, keep the jump, and every conjunct is at the same
        -- heap, frames and stack — so only `frameKLabels` moves.
        rw [unwind_raise_transparent (m := m) hκ hK]
        refine ⟨hhook, hsat, hstr, hcls, hbot, ?_,
          ClosuresOk.konts (hcloTail hK) rfl rfl (by intro κ hm; exact Or.inl hm),
          D, ctx, Γ, Γs, htab, hfs, hsc, hglob,
          ⟨hne, hro'⟩⟩
        simp only [withCtl]
        rw [← hks, framePopLabels_transparent hκ]
      -- L245: the block frame's twin of `pop`, and the only difference is which
      -- `unwind` lemma names the arm.
      | popBlk hro' =>
        rename_i cΓ Γs' kf fid lam brk cl args
        rw [unwind_raise_blkFrameK (m := m) hK]
        cases hst : m.stack with
        | nil => rw [hst] at hks; simp [framePopLabels] at hks
        | cons f0 t =>
          cases ht : t with
          | nil => rw [hst, ht] at hks; simp [framePopLabels] at hks
          | cons f1 rest =>
            have hlab : framePopLabels kf = m.stack.tail.dropLast := by
              have hq := hks
              simp only [framePopLabels] at hq
              rw [hst, ht] at hq ⊢
              simp only [List.dropLast_cons_cons, List.cons.injEq] at hq
              simpa using hq.2
            rw [hst, ht] at hbot hfs hsc hlab
            obtain ⟨c', Γ'⟩ := cΓ
            exact ⟨hhook, hsat, hstr, hcls, BottomObj_tail hbot, hlab,
              ClosuresOk.konts (hcloTail hK) rfl rfl (by intro κ hm; exact Or.inl hm),
              D, c', Γ', Γs', htab, hfs.tail, StackCtx.tail hsc, hglob, ⟨hne, hro'⟩⟩
      | pop hro' =>
        -- A `frameK`: the activation goes with it, and `RaiseOk.pop` handed over the
        -- caller's environment — so this case is `RetOk.here`'s bookkeeping without the
        -- type agreement, and without the `firstFrameK` target match.
        rename_i cΓ Γs' kf fid
        rw [unwind_raise_frameK (m := m) hK]
        -- **The stack has at least two entries**, and `hks` is what says so, exactly as
        -- in the `.retJ` case: the continuation has a `frameK`, so `m.stack.dropLast` is
        -- a cons.
        cases hst : m.stack with
        | nil => rw [hst] at hks; simp [framePopLabels] at hks
        | cons f0 t =>
          cases ht : t with
          | nil => rw [hst, ht] at hks; simp [framePopLabels] at hks
          | cons f1 rest =>
            have hlab : framePopLabels kf = m.stack.tail.dropLast := by
              have hq := hks
              simp only [framePopLabels] at hq
              rw [hst, ht] at hq ⊢
              simp only [List.dropLast_cons_cons, List.cons.injEq] at hq
              simpa using hq.2
            rw [hst, ht] at hbot hfs hsc hlab
            obtain ⟨c', Γ'⟩ := cΓ
            exact ⟨hhook, hsat, hstr, hcls, BottomObj_tail hbot, hlab,
              ClosuresOk.konts (hcloTail hK) rfl rfl (by intro κ hm; exact Or.inl hm),
              D, c', Γ', Γs', htab, hfs.tail, StackCtx.tail hsc, hglob, ⟨hne, hro'⟩⟩
    -- **A `next` in flight** (L227), and it is the only jump that *lands back in the
    -- program*: the two `RetOk`-shaped cases pop frames, this one restarts a loop in the
    -- same activation. So the two terminating cases have to re-establish the **`.eval`**
    -- arm, and that is where L224's `SubEnv` is spent: the loop's condition was typed at
    -- the entry environment `Γl`, the `next` fires at whatever the body had reached, and
    -- `FramesOk.narrowHead` (L218) is what turns the runtime conformance at the wider
    -- environment into conformance at `Γl`. `StackCtx` needs nothing — it reads no
    -- environment at all.
    | nxtJ v =>
      obtain ⟨Γl, hil, hsub, htop, hro⟩ := hc
      simp only [stepFn, hctl]
      generalize hK : m.kont = K at hro hks ⊢
      cases hro with
      | skip hκ hro' =>
        rw [unwind_nxt_transparent (m := m) hκ hK]
        refine ⟨hhook, hsat, hstr, hcls, hbot, ?_,
          ClosuresOk.konts (hcloTail hK) rfl rfl (by intro κ hm; exact Or.inl hm),
          D, ctx, Γ, Γs, htab, hfs, hsc, hglob,
          ⟨Γl, hil, hsub, htop, hro'⟩⟩
        simp only [withCtl]
        rw [← hks, framePopLabels_nxt_transparent hκ]
      | loopCond hl hw hk' =>
        rename_i Γl' _ _ _ _ _ _
        -- `cases` unified the relation's context index with the constructor's record, so
        -- the loop environment `CtlOk` named and the one `NxtOk` carries are the same one
        -- — `hil` is the proof, and it is one `simp`.
        have hΓl : Γl' = Γl := by simpa using hil
        subst hΓl
        rw [unwind_nxt_loopCond (m := m) hK]
        obtain ⟨τc, hc'⟩ := hl.1
        refine ⟨hhook, hsat, hstr, hcls, hbot, by simpa [withKont, framePopLabels] using hks,
          ClosuresOk.konts hclo rfl rfl
            (by
              intro κ hm
              rcases List.mem_cons.mp hm with rfl | hin
              · exact Or.inr (by simp [KontClosure])
              · exact Or.inl (by rw [hK]; exact List.mem_cons_of_mem _ hin)),
          D, _, Γl', Γs, htab, FramesOk.narrowHead hsub hfs, hsc, hglob,
          ⟨τc, τc, Γl', D, Γl', ?_, subTy_refl _, SubEnv.refl _, ?_⟩⟩
        · simpa [withKont] using hc'
        · simpa [withKont] using KontOk.whileCond hl hw hk'
      | loopBody hl hw hk' =>
        rename_i Γl' _ _ _ _ _ _
        -- `cases` unified the relation's context index with the constructor's record, so
        -- the loop environment `CtlOk` named and the one `NxtOk` carries are the same one
        -- — `hil` is the proof, and it is one `simp`.
        have hΓl : Γl' = Γl := by simpa using hil
        subst hΓl
        rw [unwind_nxt_loopBody (m := m) hK]
        obtain ⟨τc, hc'⟩ := hl.1
        refine ⟨hhook, hsat, hstr, hcls, hbot, by simpa [withKont, framePopLabels] using hks,
          ClosuresOk.konts hclo rfl rfl
            (by
              intro κ hm
              rcases List.mem_cons.mp hm with rfl | hin
              · exact Or.inr (by simp [KontClosure])
              · exact Or.inl (by rw [hK]; exact List.mem_cons_of_mem _ hin)),
          D, _, Γl', Γs, htab, FramesOk.narrowHead hsub hfs, hsc, hglob,
          ⟨τc, τc, Γl', D, Γl', ?_, subTy_refl _, SubEnv.refl _, ?_⟩⟩
        · simpa [withKont] using hc'
        · simpa [withKont] using KontOk.whileCond hl hw hk'
    | _ => exact hc.elim
end Static
end Proof
end RubyCore
