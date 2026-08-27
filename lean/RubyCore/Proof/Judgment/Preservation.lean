import RubyCore.Proof.Judgment.Mono

/-!
# Progress and preservation over `Judge` (J21) — the rung-1 fragment

`step_okJ` is `step_ok` (Proof/Static/Preservation.lean:263) re-proved against
`InvJ`. Two structural differences from the old proof, both consequences of stating
the metatheory over a relation:

* **The eval branch is one induction over the derivation** (`judge_eval_ok`), driven
  by `Judge.rec` with the ten auxiliary motives trivial. The old proof unfolded
  `infer` at each head; here each constructor case *is* the head's preservation
  argument, and the `sub` case — the one non-syntax-directed rule — composes the
  invariant's slack by `SubJ.trans`/`SubEnv.trans` once, for every head at a stroke.
  This is §2's "inversion is `cases`" cashed: no motive maps, no `.induct`
  derivability, and a new rule is a new case that perturbs nothing.
* **Out-of-fragment heads are refuted by `MFrag`**, not by a checker's `none` — the
  eval arm's gate (J20), doing the job `infer`'s partiality did.

The delivery branch is a `cases` over `KontOkJ`, one case per constructor,
transliterated from the old file's value branch.
-/

namespace RubyCore
namespace Proof
namespace Judgment

open Interp
open RubyCore.Types
open RubyCore.Judgment
open RubyCore.Proof.Static

set_option maxRecDepth 100000

/-- `StepOk` with the invariant swapped: `.next` carries `InvJ`, `.done` is a halt,
    `.uncaught` is admitted when the exception is not a type error (progress is
    exactly this clause), everything else refused. -/
def StepOkJ : StepResult → Prop
  | .next m' => InvJ m'
  | .done _ _ => True
  | .uncaught exc m => ¬ isTypeError m.heap exc
  | _ => False

/-- The eval branch's motive: everything `step_okJ` knows at an eval state, with the
    conclusion over `evalExpr`. Universally quantified over the machine so the
    `Judge.rec` induction can thread it through `sub`. -/
def EvalOkAt (D : Decls) (Γ : Env) (e : Expr) (top : Bool) (ctx : JCtx)
    (τ : Ty) (Γ' : Env) (D' : Decls) : Prop :=
  ∀ (m : Machine) (Γs : List (JCtx × Env)) (τw : Ty) (Γk : Env),
    top = Γs.isEmpty →
    FramesOkJ m.heap m.frames m.stack (Γ :: Γs.map Prod.snd) →
    DeclsOkJ D m.heap →
    StackCtx m.heap m.frames m.stack (jctxs ctx Γs) →
    NoHook m.heap → Saturated m.heap → LitClsOk m.heap → ClassOk m.heap →
    BottomObj m.frames m.stack →
    framePopLabels m.kont = m.stack.dropLast →
    GlobalsOk D m.heap m.globals →
    ClosuresOk m →
    MFrag e →
    SubJ τ τw → SubEnv Γk Γ' →
    KontOkJ D' m.heap ((ctx, Γk) :: Γs) τw m.kont →
    StepOkJ (evalExpr m e)


@[simp] theorem jctxs_eq (c : JCtx) (Γs : List (JCtx × Env)) :
    jctxs c Γs = c.toFrameCtx :: (Γs.map Prod.fst).map JCtx.toFrameCtx := rfl

set_option maxHeartbeats 1000000 in
/-- The zero-argument implicit-self send preserves `InvJ`, whatever the site —
    `inv_implicit_send0` (Proof/Static/Preservation.lean:66) over the judgment.
    The dispatch happens *in this step*; the builtin arm ends in
    `inv_grow_valueJ`, the user arm pushes the activation whose body's `Judge`
    derivation `UserConformsJ` carries. -/
theorem inv_implicit_send0J {F : Decls} {m : Machine} {ctx : JCtx} {Γ Γk : Env}
    {Γs : List (JCtx × Env)} {c mname : String} {τret : Ty} {site : SendSite}
    (hfs : FramesOkJ m.heap m.frames m.stack (Γ :: Γs.map Prod.snd))
    (htab : DeclsOkJ F m.heap)
    (hsc : StackCtx m.heap m.frames m.stack (jctxs ctx Γs))
    (hhook : NoHook m.heap) (hsat : Saturated m.heap) (hstr : LitClsOk m.heap)
    (hcls : ClassOk m.heap) (hbot : BottomObj m.frames m.stack)
    (hks : framePopLabels m.kont = m.stack.dropLast)
    (hne : m.stack ≠ []) (hsome : ctx.selfCls = some c)
    (hsg : sigOf F (.cls c) mname = some ([], τret))
    {τw : Ty} (hsubw : SubJ τret τw)
    (hk : KontOkJ F m.heap ((ctx, Γk) :: Γs) τw m.kont)
    (hglob : GlobalsOk F m.heap m.globals := by assumption)
    (hsuE : SubEnv Γk Γ := by first | exact SubEnv.refl _ | assumption)
    (hclo : ClosuresOk m := by assumption) :
    StepOkJ (startArgs m m.currentFrame.self site mname [] [] .none) := by
  have hfs := FramesOkJ.narrowHead hsuE hfs
  have hself : ValueTy m.heap m.currentFrame.self (.cls c) := by
    cases hst : m.stack with
    | nil => exact absurd hst hne
    | cons fid fids =>
      rw [hst] at hsc
      have := hsc.2.2.2.1 c hsome
      rw [show m.currentFrame = m.frames.getD fid default by
        simp [Machine.currentFrame, hst]]
      exact this.1
  rcases (htab.1 _ mname _ (sigOf_declFor (by simp) hsg)).blockless with hbi |
    ⟨mdu, cu, htys, hresu, hnmu, hconfu⟩
  · obtain ⟨w, m', hw, hg', hfr', hst', hko', hgv', hstep⟩ :=
      entry_dispatch (m := m) (recv := m.currentFrame.self) (args := [])
        (site := site) (by simp) (by simp) (by simp) hbi hself trivial
    rw [hstep]
    exact inv_grow_valueJ hfs htab hsc hhook hsat hstr hcls hbot hks hg' hfr' hst' hko'
      (VTy.weaken (VTy.ofValueTy hw) hsubw) hk hglob hgv'
  · have hru := hresu _ (valueTy_tyClass (by simp) (by simp) (by simp) hself)
    have hown : (m.heap.classPayload? mdu.owner).isSome := by
      obtain ⟨_, _, _, _, _, _, _, _, h9, _⟩ := hru; exact h9
    rw [user_dispatch (m := m) (site := site) hru hself]
    have hlt : ∀ g ∈ m.stack, g < m.frames.size := hfs.mem_lt
    obtain ⟨hdp, hdblk, hdfu, hmfb, Γb, r, τb, hbu, hsb, hag⟩ := hconfu
    refine ⟨hhook, hsat, hstr, hcls,
      BottomObj_cons hne (BottomObj_push hlt hbot),
      (by simp [framePopLabels, hks, dropLast_cons_ne hne]),
      (ClosuresOk.pushFrame hclo rfl rfl rfl), _,
      { cls := cu, selfCls := some cu, ret := r, meth := some mname,
        params := some [] }, [],
      (ctx, Γk) :: Γs, htab, ?_, ?_, ?_⟩
    · refine ⟨by rw [Array.size_push]; exact Nat.lt_succ_self _, hlt,
        ⟨ShallowChain.of_none (by rw [getD_push_lt_self]; try rfl), ?_, ?_⟩,
        FramesOkJ.push hfs⟩
      · rw [getD_push_lt_self]; exact hown
      · intro y σ hy; exact absurd hy (by simp [envGet?])
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [getD_push_lt_self]; exact hown
      · rw [getD_push_lt_self]; exact fun _ => hnmu
      · rw [getD_push_lt_self]; exact fun _ => rfl
      · intro sc hsc'
        simp only [Option.some.injEq] at hsc'
        subst hsc'
        rw [getD_push_lt_self]
        show ValueTy m.heap m.currentFrame.self (.cls cu) ∧
          (userFrame m.currentFrame.self mdu mname).defmod ∈
            ancestors m.heap (classOf m.heap m.currentFrame.self)
        have hcu : c = cu := UserKey.cls_inv htys
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hch, _⟩ := hru
        exact ⟨hcu ▸ hself, hch⟩
      · rw [getD_push_lt_self]
        obtain ⟨_, _, _, _, _, _, _, _, _, _, hcr, _, _⟩ := hru
        exact hcr
      · exact Or.inl ⟨by rw [getD_push_lt_self]; rfl, by simp⟩
      · intro mn hmn
        simp only [Option.some.injEq] at hmn
        subst hmn
        rw [getD_push_lt_self]
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hsn⟩ := hru
        exact ⟨by simp [userFrame, hsn], rfl, rfl, rfl, rfl, rfl, rfl⟩
      · rw [getD_push_lt_self]; exact fun _ => rfl
      · show StackCtx m.heap (m.frames.push _) m.stack (jctxs ctx Γs)
        exact StackCtx.push hlt hsc
    · refine ⟨hglob, ?_⟩
      show CtlOkJ F _ [] ((ctx, Γk) :: Γs) _
      exact ⟨hmfb, τb, τw, Γb, F, Γb,
        hbu, hsb.trans hsubw, SubEnv.refl _,
        KontOkJ.frameK (fun σ h => by rw [hag σ (by simpa using h)]; exact hsubw) rfl hk⟩

set_option maxHeartbeats 2000000 in
/-- **The eval branch**, by induction over the derivation. -/
theorem judge_eval_ok {D : Decls} {Γ : Env} {e : Expr} {top : Bool} {ctx : JCtx}
    {τ : Ty} {Γ' : Env} {D' : Decls} (hj : Judge D Γ e top ctx τ Γ' D') :
    EvalOkAt D Γ e top ctx τ Γ' D' := by
  refine Judge.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ _ _ _ _ => True)
    (motive_8 := fun _ _ _ _ _ _ _ => True)
    (motive_9 := fun _ _ _ _ _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ _ _ => True)
    (motive_11 := fun D Γ e top ctx τ Γ' D' _ => EvalOkAt D Γ e top ctx τ Γ' D')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?hint ?hflt ?hstr ?hsym ?htru ?hfls ?hnil ?hself
    ?hvarLvar ?hvarIvar ?hvarGvar ?hvarCvar
    ?hvasgnLvar ?hvasgnIvarDecl ?hvasgnIvarFresh ?hvasgnGvar ?hvasgnCvar
    ?hconst ?hcpathAbs ?hcpathScoped ?hcasgn ?hcpathAsgn
    ?hsend ?hsendIter0 ?hsendIterA ?hsendLambda ?hsendLambdaArrow ?hsendCall
    ?hsendBlockpass ?hvcall ?hkwargs ?hfwd ?hsplatAnon ?hsplatArray ?hsplatArrayOf
    ?hyield ?hifElse ?hifNone ?hifNarrowElse ?hifNarrowNone
    ?hwhile ?hdowhile ?hfor
    ?hretSome ?hretNil ?hnxtNil ?hnxtSome ?hbrkNil ?hbrkSome ?hretry ?hredo
    ?hdefDecl ?hdefPromote ?hdefs ?hclassTop ?hclassSup ?hmodule
    ?hscopedClass ?hscopedModule ?hsclass ?hbegin ?hsuper ?hzsuper ?halias
    ?hdefined ?harray ?hhash ?hseq ?hsub
    hj
  -- The ten auxiliary relations' constructors: their motives are `True`.
  all_goals try (intros; trivial)
  -- ## Literals: one step to a value of the exact type.
  case hint =>
    intro D Γ n top ctx
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    exact inv_valueJ hfs htab hsc hh hsat hstr hcls hbot hks
      (VTy.weaken (VTy.exact rfl) hsubw) hk
  case hflt =>
    intro D Γ x top ctx
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    exact inv_valueJ hfs htab hsc hh hsat hstr hcls hbot hks
      (VTy.weaken (VTy.exact rfl) hsubw) hk
  case hsym =>
    intro D Γ s top ctx
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    exact inv_valueJ hfs htab hsc hh hsat hstr hcls hbot hks
      (VTy.weaken (VTy.exact rfl) hsubw) hk
  case htru =>
    intro D Γ top ctx
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    exact inv_valueJ hfs htab hsc hh hsat hstr hcls hbot hks
      (VTy.weaken (VTy.exact rfl) hsubw) hk
  case hfls =>
    intro D Γ top ctx
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    exact inv_valueJ hfs htab hsc hh hsat hstr hcls hbot hks
      (VTy.weaken (VTy.exact rfl) hsubw) hk
  case hnil =>
    intro D Γ top ctx
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    exact inv_valueJ hfs htab hsc hh hsat hstr hcls hbot hks
      (VTy.weaken (VTy.exact rfl) hsubw) hk
  -- ## The string literal: the producer — one allocation, `inv_grow_valueJ`.
  case hstr =>
    intro D Γ s top ctx
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    exact inv_grow_valueJ hfs htab hsc hh hsat hstr hcls hbot hks
      (plainGrow_alloc m.heap _ (by simp) rfl) rfl rfl rfl
      (VTy.weaken (VTy.ofValueTy
        (valueTy_alloc_fresh (by simp) rfl rfl rfl hstr.1.1 hstr.1.2 (by simp))) hsubw) hk
  -- ## Local read: `LocalsOkJ`, off the head frame's conformance.
  case hvarLvar =>
    intro D Γ x top ctx τ0 hget
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    exact inv_valueJ hfs htab hsc hh hsat hstr hcls hbot hks
      (VTy.weaken (hfs.localsOk x τ0 hget) hsubw) hk
  -- ## Local write: push the assignment kont on the rhs.
  case hvasgnLvar =>
    intro D Γ x rhs top ctx τ0 Γ₁ D₁ hib hrhs ih
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    cases hmf with
    | vasgnLvar hmrhs =>
      subst htop
      exact inv_pushJ hfs htab hsc hh hsat hstr hcls hbot
        (by simp [framePopLabels, hks]) hmrhs hrhs (SubJ.refl _)
        (KontOkJ.asgn hib hsubw hk)
  -- ## Sequencing: the three-way split `evalExpr` makes.
  case hseq =>
    intro D Γ es top ctx τ0 Γ' D'0 hseq ihseq
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    subst htop
    have hall : ∀ e' ∈ es, MFrag e' := by cases hmf; assumption
    cases hseq with
    | nil =>
      exact inv_valueJ hfs htab hsc hh hsat hstr hcls hbot hks
        (VTy.weaken (VTy.exact rfl) hsubw) hk
    | single hj1 =>
      exact inv_evalJ hfs htab hsc hh hsat hstr hcls hbot hks
        (hall _ (by simp)) hj1 hsubw hk
    | cons hj1 hrest =>
      exact inv_pushJ hfs htab hsc hh hsat hstr hcls hbot
        (by simp [framePopLabels, hks]) (hall _ (by simp)) hj1 (SubJ.refl _)
        (KontOkJ.seqCons (fun e' he' => hall e' (List.mem_cons_of_mem _ he'))
          hrest hsubw hk)
  -- ## `if`: push the branch kont on the condition.
  case hifElse =>
    intro D Γ cond t els top ctx τc Γ₁ D₁ τt Γt Dt τe Γe τj Γc
    intro hcnd ht he hjt hje hct hce ihc iht ihe
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    subst htop
    cases hmf with
    | ifElse hshape hmc hmt hme =>
      exact inv_pushJ hfs htab hsc hh hsat hstr hcls hbot
        (by simp [framePopLabels, hks]) hmc hcnd (SubJ.refl _)
        (KontOkJ.ifElseK hmt hme ht he hjt hje hct hce hsubw hk)
  case hifNone =>
    intro D Γ cond t top ctx τc Γ₁ D₁ τt Γt τj Γc
    intro hcnd ht hjt hjn hct hcΓ ihc iht
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    subst htop
    cases hmf with
    | ifNone hshape hmc hmt =>
      exact inv_pushJ hfs htab hsc hh hsat hstr hcls hbot
        (by simp [framePopLabels, hks]) hmc hcnd (SubJ.refl _)
        (KontOkJ.ifNoneK hmt ht hjt hjn hct hcΓ hsubw hk)
  -- ## Narrowing derivations at a bare-local condition: out of the rung-1 fragment
  -- (`MFrag`'s shape condition; the narrowing rung's delivery needs the value↔store
  -- correlation — see DESIGN-NOTES).
  case hifNarrowElse =>
    intro D Γ x t els top ctx τ0 τt Γt Dt τe Γe τj Γc
    intro hget ht he hjt hje hct hce iht ihe
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    cases hmf with
    | ifElse hshape _ _ _ => exact absurd rfl (hshape x)
  case hifNarrowNone =>
    intro D Γ x t top ctx τ0 τt Γt τj Γc
    intro hget ht hjt hjn hct hcΓ iht
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    cases hmf with
    | ifNone hshape _ _ => exact absurd rfl (hshape x)
  -- ## `while`: enter the loop at the chosen head environment.
  case hwhile =>
    intro D Γ Γl cond body top ctx τc Γ₁ τb Γ₂
    intro hentry hcnd hs1 hbody hs2 ihc ihb
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    subst htop
    cases hmf with
    | while' hmc hmb =>
      have hfs' := FramesOkJ.narrowHead hentry hfs
      have hloop : LoopOkJ D Γl cond body Γs.isEmpty (loopCtx ctx Γl) :=
        ⟨hmc, hmb, ⟨τc, Γ₁, hcnd, hs1⟩, ⟨τb, Γ₂, hbody, hs2⟩⟩
      refine inv_pushJ (c := loopCtx ctx Γl) hfs' htab ?_ hh hsat hstr hcls hbot
        (by simp [framePopLabels, hks]) hmc hcnd (SubJ.refl _)
        (KontOkJ.whileCond hloop hsubw hk (hsu := hsuE)) (hsuE := hs1)
      show StackCtx m.heap m.frames m.stack (jctxs (loopCtx ctx Γl) Γs)
      have : jctxs (loopCtx ctx Γl) Γs
          = { ctx.toFrameCtx with inLoop := some Γl } :: (Γs.map Prod.fst).map JCtx.toFrameCtx := by
        simp [jctxs, loopCtx]
      rw [this]
      exact stackCtx_inLoop (by simpa [jctxs] using hsc)
  -- ## `self`: the frame's own value, typed by `StackCtx`'s clause.
  case hself =>
    intro D Γ top ctx cc hsome
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    refine inv_valueJ hfs htab hsc hh hsat hstr hcls hbot hks
      (VTy.weaken (VTy.ofValueTy ?_) hsubw) hk
    have hne : m.stack ≠ [] := (hfs.frameShallow).1
    cases hst : m.stack with
    | nil => exact absurd hst hne
    | cons fid fids =>
      rw [hst] at hsc
      have := hsc.2.2.2.1 cc hsome
      rw [show m.currentFrame = m.frames.getD fid default by
        simp [Machine.currentFrame, hst]]
      exact this.1
  -- ## `vcall`: the implicit-self zero-argument send, dispatched in this step.
  case hvcall =>
    intro D Γ mname top ctx cc τret hsome hsg
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    simp only [evalExpr]
    exact inv_implicit_send0J hfs htab hsc hh hsat hstr hcls hbot hks
      (hfs.frameShallow).1 hsome hsg hsubw hk
  -- ## The block-less send.
  case hsend =>
    intro D Γ recvO mname args top ctx τr Γ₁ D₁ τs Γ₂ D₂ ps τret
    intro hrecv hargs hsg hsub ihr iha
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    subst htop
    cases hrecv with
    | expl hr =>
      -- Explicit receiver: push the receiver kont; which constructor depends on
      -- the argument count, exactly as `applyKont` behaves one step later.
      cases hmf with
      | send hne hmr hma =>
      cases args with
      | nil =>
        cases hargs
        have hps : ps = [] := hsub.nil_inv
        subst hps
        simp only [evalExpr]
        rename_i r
        cases r <;>
          exact inv_pushJ hfs htab hsc hh hsat hstr hcls hbot
            (by simp [framePopLabels, hks]) hmr hr (SubJ.refl _)
            (KontOkJ.recvK0 hsg hsubw hk)
      | cons a as =>
        simp only [evalExpr]
        rename_i r
        cases r <;>
          exact inv_pushJ hfs htab hsc hh hsat hstr hcls hbot
            (by simp [framePopLabels, hks]) hmr hr (SubJ.refl _)
            (KontOkJ.recvK (fun a' ha' => hma a' ha') hargs hsg hsub hsubw hk)
    | @self _ _ _ _ cc hsome =>
      -- Implicit receiver: `startArgs` on the frame's `self`, with no receiver kont.
      cases hmf with
      | sendImplicit hma =>
      cases args with
      | nil =>
        cases hargs
        have hps : ps = [] := hsub.nil_inv
        subst hps
        simp only [evalExpr]
        exact inv_implicit_send0J hfs htab hsc hh hsat hstr hcls hbot hks
          (hfs.frameShallow).1 hsome hsg hsubw hk
      | cons a as =>
        cases hargs with
        | cons ha1 harest =>
          rename_i τe Γm Dm τs'
          obtain ⟨τp, psrest, rfl, hs1, hs2⟩ := hsub.cons_inv
          have hself : ValueTy m.heap m.currentFrame.self (.cls cc) := by
            cases hst : m.stack with
            | nil => exact absurd hst (hfs.frameShallow).1
            | cons fid fids =>
              rw [hst] at hsc
              have := hsc.2.2.2.1 cc hsome
              rw [show m.currentFrame = m.frames.getD fid default by
                simp [Machine.currentFrame, hst]]
              exact this.1
          have hsp : ∀ e, a ≠ Expr.splat e := by
            rintro e rfl
            exact nomatch hma (Expr.splat e) (by simp)
          have hkw : ∀ es, a ≠ Expr.kwargs es := by
            rintro es rfl
            exact nomatch hma (Expr.kwargs es) (by simp)
          have hfw : a ≠ Expr.fwd := by
            rintro rfl
            exact nomatch hma Expr.fwd (by simp)
          simp only [evalExpr]
          rw [startArgs_plain hsp hkw hfw]
          exact inv_pushJ hfs htab hsc hh hsat hstr hcls hbot
            (by simp [framePopLabels, hks]) (hma _ (by simp)) ha1 (SubJ.refl _)
            (KontOkJ.argsK (psacc := []) (VTy.ofValueTy hself) trivial hs1
              (fun a' ha' => hma a' (by simp [ha'])) harest hs2
              (by simpa using hsg) hsubw hk)
  -- ## `class C … end` — the reopen: a frame push on an untouched heap.
  case hclassTop =>
    intro D Γ name body ctx τ0 Γb' Db hmem hbody ihb
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    cases hmf with
    | classTop hmb =>
      have hΓs : Γs = [] := List.isEmpty_iff.mp htop.symm
      subst hΓs
      have hfsh1 : m.stack ≠ [] := (hfs.frameShallow).1
      have hfs := FramesOkJ.narrowHead hsuE hfs
      obtain ⟨fid₀, hst⟩ := hfs.stack_singleton
      have hdefmod : m.currentFrame.defmod = Boot.objectId := by
        rw [currentFrame_eq hfsh1]; exact BottomObj_curFrame hst hbot
      obtain ⟨k, cp, hconst, hpay, hnm, huniq, -, -, -, hreop⟩ :=
        hcls.2.2 name (readable_of_reopenable (List.mem_of_elem_eq_true hmem))
      obtain ⟨hmod, -, -⟩ := hreop (List.mem_of_elem_eq_true hmem)
      have hcrefCur : Boot.objectId ∈ m.currentFrame.cref := by
        rw [show m.currentFrame = m.frames.getD fid₀ default by
          simp [Machine.currentFrame, hst]]
        rw [hst] at hsc
        exact hsc.2.2.2.2.1
      simp only [evalExpr, enterClassBody, hdefmod, hconst, hpay, hmod, withKont]
      have hlt : ∀ g ∈ m.stack, g < m.frames.size := hfs.mem_lt
      refine ⟨hh, hsat, hstr, hcls,
        BottomObj_cons hfsh1 (BottomObj_push hlt hbot),
        (by simp [framePopLabels, hks, dropLast_cons_ne hfsh1]),
        (ClosuresOk.pushFrame hclo rfl rfl rfl),
        D, ({ cls := name } : JCtx), [], [(ctx, Γk)],
        htab, ?_, ?_, hgl, ?_⟩
      · refine ⟨by rw [Array.size_push]; exact Nat.lt_succ_self _, hlt,
          ⟨ShallowChain.of_none (by rw [getD_push_lt_self]; try rfl), ?_, ?_⟩,
          FramesOkJ.push hfs⟩
        · rw [getD_push_lt_self]; simp [hpay]
        · intro y σ hy; exact absurd hy (by simp [envGet?])
      · refine ⟨?_, ?_, ?_, ?_, ?_, Or.inr rfl, fun mn h' => absurd h' (by simp), ?_,
          StackCtx.push hlt hsc⟩
        · rw [getD_push_lt_self]; simp [hpay]
        · rw [getD_push_lt_self]; exact fun _ => hnm
        · rw [getD_push_lt_self]; exact fun _ => rfl
        · exact fun sc hsc' => absurd hsc' (by simp)
        · rw [getD_push_lt_self]
          exact List.mem_cons_of_mem _ hcrefCur
        · rw [getD_push_lt_self]; exact fun _ => rfl
      · exact ⟨hmb, τ0, τw, Γb', Db, Γb', hbody, hsubw, SubEnv.refl _,
          KontOkJ.frameK (fun _ h' => by simp at h') rfl hk⟩
  -- ## `def` — the two derivations of the same step: install-only (`defDecl`) and
  -- row-threading promotion (`defPromote`). The heap write and the value are
  -- identical; the difference is the table the invariant is re-established at.
  case hdefDecl =>
    intro D Γ name ps body top ctx τs σb bs τb Γb'
    intro hfresh hha hlen hbody hsbb ihb
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    have hfsh1 : m.stack ≠ [] := (hfs.frameShallow).1
    have hdm : m.currentFrame = curFrame m := currentFrame_eq hfsh1
    have hfs := FramesOkJ.narrowHead hsuE hfs
    have hdo : (m.heap.classPayload? (curFrame m).defmod).isSome := by
      cases hst : m.stack with
      | nil => exact absurd hst hfsh1
      | cons fid _ =>
        have hfc : FrameConformsJ m.heap m.frames Γk fid := by
          rw [hst] at hfs; exact hfs.2.2.1
        simpa [curFrame, curFid, hst] using hfc.2.1
    have hha' : ¬ ("method_added" = name) := fun hh' => hha hh'.symm
    have hlkNH : ∀ md : MethodDef,
        NoHook (defineMethod m.heap (curFrame m).defmod name md) :=
      fun _ => NoHook_defineMethod hh hha'
    have hlk : ∀ md : MethodDef,
        lookup (defineMethod m.heap (curFrame m).defmod name md)
          (.ref (curFrame m).defmod) "method_added" = none := fun md =>
      (hlkNH md).2 (curFrame m).defmod
        (by rw [classPayload?_isSome_defineMethod]; exact hdo)
    have hres : ∀ (m₀ : Machine),
        m₀.frames = m.frames → m₀.stack = m.stack → m₀.kont = m.kont →
        TypeAgree m.heap m₀.heap → DeclsOkJ D m₀.heap → NoHook m₀.heap →
        Saturated m₀.heap → LitClsOk m₀.heap → ClassOk m₀.heap →
        GlobalsOk D m₀.heap m₀.globals →
        InvJ (withCtl m₀ (.value (.sym name))) := by
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
        D, ctx, Γk, Γs, ht', ?_, ?_, hgl', ?_⟩
      · show FramesOkJ m₀.heap m₀.frames m₀.stack (Γk :: Γs.map Prod.snd)
        rw [hfr, hst]; exact FramesOkJ.heap_congr hag hfs
      · show StackCtx m₀.heap m₀.frames m₀.stack (jctxs ctx Γs)
        rw [hfr, hst]; exact StackCtx.heap_congr hag hsc
      · show ∃ σ' Γk', VTy m₀.heap (Value.sym name) σ' ∧ SubEnv Γk' Γk ∧
            KontOkJ D m₀.heap ((ctx, Γk') :: Γs) σ' m₀.kont
        exact ⟨_, _, VTy.weaken (VTy.exact rfl) hsubw, SubEnv.refl _,
          by rw [hko]; exact KontOkJ.heap_congr hag hk⟩
    simp only [evalExpr, hdm]
    by_cases hp : m.preludeMode = true <;>
      simp only [hp, if_true, if_false, Bool.false_eq_true, hlk] <;>
      refine hres _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        first
          | rfl
          | exact typeAgree_defineMethod _ _ _ _
          | exact DeclsOkJ_defineMethod htab hfresh
          | exact hlkNH _
          | exact Saturated_defineMethod hsat _ _ _
          | exact LitClsOk_defineMethod hstr
          | exact ClassOk_defineMethod hcls
          | exact GlobalsOk.congr (typeAgree_defineMethod _ _ _ _) hgl
  case hdefPromote =>
    intro D Γ name body top ctx τb Γb'
    intro hfresh hha hbody htopf hinit hmemctx hgroundc hdfree hretn hloopn hblkn ihb
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    have hmfb : MFrag body := by cases hmf; assumption
    have hfsh1 : m.stack ≠ [] := (hfs.frameShallow).1
    have hdm : m.currentFrame = curFrame m := currentFrame_eq hfsh1
    have hfs := FramesOkJ.narrowHead hsuE hfs
    have hdo : (m.heap.classPayload? (curFrame m).defmod).isSome := by
      cases hst : m.stack with
      | nil => exact absurd hst hfsh1
      | cons fid _ =>
        have hfc : FrameConformsJ m.heap m.frames Γk fid := by
          rw [hst] at hfs; exact hfs.2.2.1
        simpa [curFrame, curFid, hst] using hfc.2.1
    have hha' : ¬ ("method_added" = name) := fun hh' => hha hh'.symm
    have hlkNH : ∀ md : MethodDef,
        NoHook (defineMethod m.heap (curFrame m).defmod name md) :=
      fun _ => NoHook_defineMethod hh hha'
    have hlk : ∀ md : MethodDef,
        lookup (defineMethod m.heap (curFrame m).defmod name md)
          (.ref (curFrame m).defmod) "method_added" = none := fun md =>
      (hlkNH md).2 (curFrame m).defmod
        (by rw [classPayload?_isSome_defineMethod]; exact hdo)
    have hres : ∀ (m₀ : Machine),
        m₀.frames = m.frames → m₀.stack = m.stack → m₀.kont = m.kont →
        TypeAgree m.heap m₀.heap →
        DeclsOkJ (addRow D ctx.cls name { params := [], ret := τb }) m₀.heap →
        NoHook m₀.heap → Saturated m₀.heap → LitClsOk m₀.heap → ClassOk m₀.heap →
        GlobalsOk (addRow D ctx.cls name { params := [], ret := τb }) m₀.heap
          m₀.globals →
        InvJ (withCtl m₀ (.value (.sym name))) := by
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
        addRow D ctx.cls name { params := [], ret := τb }, ctx, Γk, Γs,
        ht', ?_, ?_, hgl', ?_⟩
      · show FramesOkJ m₀.heap m₀.frames m₀.stack (Γk :: Γs.map Prod.snd)
        rw [hfr, hst]; exact FramesOkJ.heap_congr hag hfs
      · show StackCtx m₀.heap m₀.frames m₀.stack (jctxs ctx Γs)
        rw [hfr, hst]; exact StackCtx.heap_congr hag hsc
      · show ∃ σ' Γk', VTy m₀.heap (Value.sym name) σ' ∧ SubEnv Γk' Γk ∧
            KontOkJ (addRow D ctx.cls name { params := [], ret := τb }) m₀.heap
              ((ctx, Γk') :: Γs) σ' m₀.kont
        exact ⟨_, _, VTy.weaken (VTy.exact rfl) hsubw, SubEnv.refl _,
          by rw [hko]; exact KontOkJ.heap_congr hag hk⟩
    obtain ⟨fid₀, fids₀, hst⟩ : ∃ fid fids, m.stack = fid :: fids := by
      cases hst : m.stack with
      | nil => exact absurd hst hfsh1
      | cons a r => exact ⟨a, r, rfl⟩
    have hΓs : Γs ≠ [] := by
      intro hz
      rw [hz] at htop
      rw [htopf] at htop
      exact absurd htop.symm (by simp)
    have hfidsne : fids₀ ≠ [] := by
      intro hz
      rw [hst, hz] at hfs
      cases hΓ : Γs with
      | nil => exact absurd hΓ hΓs
      | cons a r => rw [hΓ] at hfs; exact absurd hfs.2.2.2 (by simp [FramesOkJ])
    have hscc : StackCtx m.heap m.frames (fid₀ :: fids₀)
        (ctx.toFrameCtx :: (Γs.map Prod.fst).map JCtx.toFrameCtx) := by
      rw [hst] at hsc; exact hsc
    have hctx : className m.heap (curFrame m).defmod = ctx.cls := by
      rw [show curFrame m = m.frames.getD fid₀ default by
        simp [curFrame, curFid, hst]]
      exact hscc.2.1 hblkn
    have hvis : defVisOfDef (curFrame m) = .pub := by
      rw [show curFrame m = m.frames.getD fid₀ default by
        simp [curFrame, curFid, hst]]
      exact hscc.2.2.1 hfidsne
    have hcrefCur : Boot.objectId ∈ m.currentFrame.cref := by
      rw [show m.currentFrame = m.frames.getD fid₀ default by
        simp [Machine.currentFrame, hst]]
      exact hscc.2.2.2.2.1
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
          (by rw [className_defineMethod]; exact hctx)
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
        DeclsOkJ (addRow D ctx.cls name { params := [], ret := τb })
          (defineMethod m.heap (curFrame m).defmod name md) := by
      intro md hown hb hu hvs hpar hdec hcap hbd hcref hsn
      refine DeclsOkJ_addRow_here (DeclsOkJ_defineMethod htab hfresh) hfresh rfl ?_
      intro τ0 hk0
      have hτ0 : τ0 = .cls ctx.cls := by
        cases τ0 <;> simp only [tyClassNames] at hk0
        case cls n =>
          split at hk0
          · exact absurd hk0 (by simp)
          · simp only [List.cons.injEq, and_true] at hk0
            rw [hk0]
        case int =>
          simp only [List.cons.injEq, and_true] at hk0
          rw [← hk0] at hgroundc
          exact absurd hgroundc (by decide)
        case float =>
          simp only [List.cons.injEq, and_true] at hk0
          rw [← hk0] at hgroundc
          exact absurd hgroundc (by decide)
        case nilT =>
          simp only [List.cons.injEq, and_true] at hk0
          rw [← hk0] at hgroundc
          exact absurd hgroundc (by decide)
        case sym =>
          simp only [List.cons.injEq, and_true] at hk0
          rw [← hk0] at hgroundc
          exact absurd hgroundc (by decide)
        all_goals exact absurd hk0 (by simp)
      subst hτ0
      obtain ⟨k₀, cp, _, _, hnm₀, huniq₀, _, _, _, _⟩ :=
        (ClassOk_defineMethod (name := name) (md := md)
          (cls := (curFrame m).defmod) hcls).2.2 ctx.cls
          (readable_of_reopenable (List.mem_of_elem_eq_true hmemctx))
      have hctx' : className (defineMethod m.heap (curFrame m).defmod name md)
          (curFrame m).defmod = ctx.cls := by
        rw [className_defineMethod]; exact hctx
      have hdefk : (curFrame m).defmod = k₀ :=
        huniq₀ _ (by rw [classPayload?_isSome_defineMethod]; exact hdo) hctx'
      obtain ⟨rest, hrest⟩ := hchain md
      refine Or.inr (Or.inl ⟨md, ctx.cls, UserKey.cls, fun k htc => ?_,
        by rw [hown]; exact hctx', rfl,
        rfl, by rw [hbd]; exact hdfree, by rw [hbd]; exact hmfb, ?_⟩)
      · have hkk : k = (curFrame m).defmod := by
          rw [hdefk]; exact huniq₀ k htc.1 htc.2
        subst hkk
        refine ⟨(curFrame m).defmod, ?_, hb, hu, hvs, hpar, hdec, hcap,
          by rw [hown, classPayload?_isSome_defineMethod]; exact hdo, ?_, hcref,
          by rw [hown, hrest]; exact List.mem_cons_self ..,
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
      · obtain ⟨-, hbo'⟩ := judge_mono hbody hmfb hdfree (subDecls_addRow hfresh)
        exact ⟨Γb', none, τb, by rw [hbd]; exact hbo', SubJ.refl _,
          fun σ' h' => absurd h' (by simp)⟩
    simp only [evalExpr, hdm]
    by_cases hp : m.preludeMode = true <;>
      simp only [hp, if_true, if_false, Bool.false_eq_true, hlk] <;>
      (refine hres _ rfl rfl rfl (typeAgree_defineMethod _ _ _ _) ?_ (hlkNH _)
        (Saturated_defineMethod hsat _ _ _) (LitClsOk_defineMethod hstr)
        (ClassOk_defineMethod hcls)
        (GlobalsOk.congr (typeAgree_defineMethod _ _ _ _) hgl)
       refine hdecls _ rfl rfl rfl ?_ rfl rfl rfl rfl ?_ rfl
       · simpa [defVisOfDef, hinit] using hvis
       · exact hdm ▸ hcrefCur)
  -- ## `sendCall`'s conclusion is a send head, so the fragment gate's shape
  -- condition (no `call`-named explicit sends) is what refutes it.
  case hsendCall =>
    intro D Γ r args top ctx τr Γ₁ D₁ τs Γ₂ D₂ ps ret hr hparts hargs hsub ihr iha
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    cases hmf with
    | send hne _ _ => exact absurd rfl hne
  -- ## The subsumption rule: compose the invariant's slack, once for all heads.
  case hsub =>
    intro D Γ e top ctx τ0 Γ'0 D'0 σ Γ'' hj0 hs hse ih
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    exact ih m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf
      (hs.trans hsubw) (SubEnv.trans hsuE hse) hk
  -- ## Everything else is out of the rung-1 fragment: refuted by `MFrag`.
  all_goals
    (intros
     refine fun m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo
       hmf hsubw hsuE hk => ?_
     cases hmf)

/-- **Progress and preservation in one case analysis** — `step_ok`, over `InvJ`. -/
theorem step_okJ {m : Machine} (h : InvJ m) : StepOkJ (stepFn m) := by
  obtain ⟨hh, hsat, hstr, hcls, hbot, hks, hclo, F, ctx, Γ, Γs, htab, hfs, hsc, hgl, hc⟩ := h
  have hcloTail : ∀ {κ₀ : Kont} {k' : List Kont}, m.kont = κ₀ :: k' →
      ClosuresOk { m with kont := k' } := fun hkq =>
    ClosuresOk.konts hclo rfl rfl
      (by intro κ hm; exact Or.inl (by rw [hkq]; exact List.mem_cons_of_mem _ hm))
  unfold CtlOkJ at hc
  rcases hctl : m.ctl with e | v | j
  · -- ## control = eval e
    rw [hctl] at hc
    obtain ⟨hmf, τ, τw, Γ', D', Γk, hj, hsubw, hsuE, hk⟩ := hc
    simp only [stepFn, hctl]
    exact judge_eval_ok hj m Γs τw Γk rfl hfs htab hsc hh hsat hstr hcls hbot hks
      hgl hclo hmf hsubw hsuE hk
  · -- ## control = value v
    rw [hctl] at hc
    obtain ⟨τ, Γk, hv, hsuE, hk⟩ := hc
    have hfs := FramesOkJ.narrowHead hsuE hfs
    simp only [stepFn, hctl]
    unfold applyKont
    generalize hK : m.kont = K at hk hks ⊢
    cases hk with
    | nil => trivial
    | @seqNil _ _ _ _ _ _ τw k _ hsw hk' hsu =>
      exact inv_valueJ hfs htab hsc hh hsat hstr hcls hbot
        (by simpa [framePopLabels] using hks)
        (VTy.weaken hv hsw) hk' (hclo := hcloTail hK)
    | @seqCons _ _ _ _ _ _ _ e₁ es τ' τw Γ' k _ hm hseq hsw hk' hsu =>
      cases hseq with
      | single hj1 =>
        exact inv_pushJ hfs htab hsc hh hsat hstr hcls hbot
          (by simpa [framePopLabels] using hks) (hm _ (by simp)) hj1 hsw
          (KontOkJ.seqNil (SubJ.refl _) hk') (hclo := hcloTail hK)
      | cons hj1 hrest =>
        exact inv_pushJ hfs htab hsc hh hsat hstr hcls hbot
          (by simpa [framePopLabels] using hks) (hm _ (by simp)) hj1 (SubJ.refl _)
          (KontOkJ.seqCons (fun e' he' => hm e' (List.mem_cons_of_mem _ he'))
            hrest hsw hk') (hclo := hcloTail hK)
    | @asgn _ _ _ _ _ _ τw x k _ hib hsw hk' hsu =>
      refine ⟨hh, hsat, hstr, hcls, ?_,
        (by
          show framePopLabels (Machine.setLocal { m with kont := k } x v).kont
            = (Machine.setLocal { m with kont := k } x v).stack.dropLast
          rw [setLocal_stack]
          simpa [framePopLabels, Machine.setLocal] using hks),
        ClosuresOk.transport (hcloTail hK)
          (by
            intro κ hm cl hcl
            exact ⟨κ, by simpa [Machine.setLocal, withCtl] using hm, hcl⟩)
          (Nat.le_of_eq (setLocal_frames_size { m with kont := k } x v).symm)
          (by intro p _; exact setLocal_shape { m with kont := k } x v p)
          (by intro o ho; exact ho),
        _, ctx, envSet Γk x τ, Γs, htab, ?_, ?_, hgl,
        ⟨τw, _, VTy.weaken hv hsw, hsu, hk'⟩⟩
      · show BottomObj (Machine.setLocal { m with kont := k } x v).frames
          (Machine.setLocal { m with kont := k } x v).stack
        have hf' : FrameOk { m with kont := k } :=
          FramesOkJ.frameOk (m := { m with kont := k }) hfs
            (by simpa [curFrame, curFid] using hsc.curCaptured hib)
        rw [setLocal_stack, setLocal_frames (m := { m with kont := k }) hf']
        refine BottomObj_congr (fun fid _ => ?_) hbot
        by_cases hfx : fid = curFid { m with kont := k }
        · subst hfx
          rw [getD_set!_self _ _ _ (by simpa using hf'.2.1)]
          rfl
        · rw [getD_set!_ne _ _ _ _ hfx]
      · exact FramesOkJ.setLocal (m := { m with kont := k }) hfs
          (by simpa [curFrame, curFid] using hsc.curCaptured hib) hv
      · show StackCtx (Machine.setLocal { m with kont := k } x v).heap
          (Machine.setLocal { m with kont := k } x v).frames
          (Machine.setLocal { m with kont := k } x v).stack (jctxs ctx Γs)
        have hf' : FrameOk { m with kont := k } :=
          FramesOkJ.frameOk (m := { m with kont := k }) hfs
            (by simpa [curFrame, curFid] using hsc.curCaptured hib)
        rw [setLocal_stack, setLocal_frames (m := { m with kont := k }) hf']
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
        · subst hfx
          rw [getD_set!_self _ _ _ (by simpa using hf'.2.1)]
          rfl
        · rw [getD_set!_ne _ _ _ _ hfx]
        · subst hfx
          rw [getD_set!_self _ _ _ (by simpa using hf'.2.1)]
          rfl
        · rw [getD_set!_ne _ _ _ _ hfx]
    | @ifElseK _ Dt _ _ _ _ _ t els τt Γt τe Γe τj Γc τw k _
        hmt hme ht he hjt hje hct hce hjw hk' hsu =>
      by_cases hb : v.truthy
      · simp only [hb, if_true]
        exact inv_evalJ hfs htab hsc hh hsat hstr hcls hbot
          (by simpa [framePopLabels] using hks) hmt ht (hjt.trans hjw) hk'
          (hsuE := SubEnv.trans hsu hct) (hclo := hcloTail hK)
      · simp only [hb]
        exact inv_evalJ hfs htab hsc hh hsat hstr hcls hbot
          (by simpa [framePopLabels] using hks) hme he (hje.trans hjw) hk'
          (hsuE := SubEnv.trans hsu hce) (hclo := hcloTail hK)
    | @ifNoneK _ _ _ _ _ _ t τt Γt τj Γc τw k _
        hmt ht hjt hjn hct hcΓ hjw hk' hsu =>
      by_cases hb : v.truthy
      · simp only [hb, if_true]
        exact inv_evalJ hfs htab hsc hh hsat hstr hcls hbot
          (by simpa [framePopLabels] using hks) hmt ht (hjt.trans hjw) hk'
          (hsuE := SubEnv.trans hsu hct) (hclo := hcloTail hK)
      · simp only [hb]
        exact inv_valueJ hfs htab hsc hh hsat hstr hcls hbot
          (by simpa [framePopLabels] using hks)
          (VTy.weaken (VTy.exact rfl) (hjn.trans hjw)) hk'
          (hsuE := SubEnv.trans hsu hcΓ) (hclo := hcloTail hK)
    | @whileCond _ _ ctx' Γl _ _ τw c body k _ hloop hsw hk' hsu =>
      obtain ⟨hmc, hmb, ⟨τc, Γ₁, hcnd, hs1⟩, ⟨τb, Γ₂, hbody, hs2⟩⟩ := hloop
      by_cases hb : v.truthy
      · simp only [hb, if_true]
        exact inv_pushJ hfs htab hsc hh hsat hstr hcls hbot
          (by simpa [framePopLabels] using hks) hmb hbody (SubJ.refl _)
          (KontOkJ.whileBody ⟨hmc, hmb, ⟨τc, Γ₁, hcnd, hs1⟩, ⟨τb, Γ₂, hbody, hs2⟩⟩
            hsw hk' (hsu := hsu))
          (hsuE := hs2) (hclo := hcloTail hK)
      · simp only [hb]
        refine inv_valueJ (c := ctx') hfs htab ?_ hh hsat hstr hcls hbot
          (by simpa [framePopLabels] using hks)
          (VTy.weaken (VTy.exact rfl) hsw) hk'
          (hsuE := hsu) (hclo := hcloTail hK)
        have heq : jctxs (loopCtx ctx' Γk) Γs
            = { ctx'.toFrameCtx with inLoop := some Γk }
              :: (Γs.map Prod.fst).map JCtx.toFrameCtx := by
          simp [jctxs, loopCtx]
        rw [heq] at hsc
        simpa [jctxs] using stackCtx_inLoop' hsc
    | @whileBody _ _ ctx' Γl _ _ τw c body k _ hloop hsw hk' hsu =>
      obtain ⟨hmc, hmb, ⟨τc, Γ₁, hcnd, hs1⟩, ⟨τb, Γ₂, hbody, hs2⟩⟩ := hloop
      exact inv_pushJ hfs htab hsc hh hsat hstr hcls hbot
        (by simpa [framePopLabels] using hks) hmc hcnd (SubJ.refl _)
        (KontOkJ.whileCond ⟨hmc, hmb, ⟨τc, Γ₁, hcnd, hs1⟩, ⟨τb, Γ₂, hbody, hs2⟩⟩
          hsw hk' (hsu := hsu))
        (hsuE := hs1) (hclo := hcloTail hK)
    | @recvK _ D₂ _ _ _ _ _ mname arg args τs ps τret τw Γ₂ k _ _ hm hargs hsg hsub hsw hk' hsu =>
      cases hargs with
      | cons ha1 harest =>
        rename_i τe Γm Dm τs'
        obtain ⟨τp, psrest, rfl, hs1, hs2⟩ := hsub.cons_inv
        have hsp : ∀ e, arg ≠ Expr.splat e := by
          rintro e rfl
          exact nomatch hm (Expr.splat e) (by simp)
        have hkw : ∀ es, arg ≠ Expr.kwargs es := by
          rintro es rfl
          exact nomatch hm (Expr.kwargs es) (by simp)
        have hfw : arg ≠ Expr.fwd := by
          rintro rfl
          exact nomatch hm Expr.fwd (by simp)
        dsimp only
        rw [startArgs_plain hsp hkw hfw]
        exact inv_pushJ hfs htab hsc hh hsat hstr hcls hbot
          (by simpa [framePopLabels] using hks) (hm _ (by simp)) ha1 (SubJ.refl _)
          (KontOkJ.argsK (psacc := []) hv trivial hs1
            (fun a' ha' => hm a' (by simp [ha'])) harest hs2
            (by simpa using hsg) hsw hk') (hclo := hcloTail hK)
    | @recvK0 _ _ _ _ _ _ mname τret τw k Γj _ hsg hsw hk' hsu =>
      have hfs := FramesOkJ.narrowHead hsu hfs
      dsimp only
      obtain ⟨τ0, hsg, hv0, hnilτ⟩ := sigOf_vty_atomic hsg hv
      rcases (htab.1 τ0 mname _ (sigOf_declFor hnilτ hsg)).blockless with hbi |
        ⟨mdu, cu, htys, hresu, hnmu, hconfu⟩
      · obtain ⟨w, m', hw, hg', hfr', hst', hko', hgv', hstep⟩ :=
          entry_dispatch (m := { m with kont := k }) (recv := v) (args := [])
            (sigOf_atomic hnilτ hsg).1 (sigOf_atomic hnilτ hsg).2.1
            (sigOf_atomic hnilτ hsg).2.2 hbi hv0 trivial
        rw [hstep]
        exact inv_grow_valueJ (m := { m with kont := k })
          hfs htab hsc hh hsat hstr hcls hbot
          (by simpa [framePopLabels] using hks) hg' hfr' hst' hko'
          (VTy.weaken (VTy.ofValueTy hw) hsw) hk' hgl hgv' (hclo := hcloTail hK)
      · rcases htys with rfl | ⟨⟨e, rfl⟩, rfl⟩
        case inr =>
          simp only [sigOf, declFor, tyClassNames] at hsg
          exact absurd hsg (by simp)
        have hru := hresu _ (valueTy_tyClass (by simp) (by simp) (by simp) hv0)
        have hown : (m.heap.classPayload? mdu.owner).isSome := by
          obtain ⟨_, _, _, _, _, _, _, _, h9, _⟩ := hru; exact h9
        rw [user_dispatch (m := { m with kont := k }) hru hv0]
        have hlt : ∀ g ∈ m.stack, g < m.frames.size := hfs.mem_lt
        obtain ⟨hdp, hdblk, hdfu, hmfb, Γb, r, τb, hbu, hsb, hag⟩ := hconfu
        refine ⟨hh, hsat, hstr, hcls,
          BottomObj_cons (hfs.frameShallow).1 (BottomObj_push hlt hbot),
          (by rw [dropLast_cons_ne (hfs.frameShallow).1]
              simpa [framePopLabels] using hks),
          ClosuresOk.pushFrame (hcloTail hK) rfl rfl rfl, _,
          { cls := cu, selfCls := some cu, ret := r, meth := some mname,
            params := some [] }, [],
          (ctx, Γj) :: Γs, htab, ?_, ?_, ?_⟩
        · refine ⟨by rw [Array.size_push]; exact Nat.lt_succ_self _, hlt,
            ⟨ShallowChain.of_none (by rw [getD_push_lt_self]; rfl), ?_, ?_⟩,
            FramesOkJ.push hfs⟩
          · rw [getD_push_lt_self]; exact hown
          · intro y σ hy; exact absurd hy (by simp [envGet?])
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [getD_push_lt_self]; exact hown
          · rw [getD_push_lt_self]; exact fun _ => hnmu
          · rw [getD_push_lt_self]; exact fun _ => rfl
          · intro sc hsc'
            simp only [Option.some.injEq] at hsc'
            subst hsc'
            rw [getD_push_lt_self]
            obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hch, _⟩ := hru
            exact ⟨hv0, hch⟩
          · rw [getD_push_lt_self]
            obtain ⟨_, _, _, _, _, _, _, _, _, _, hcr, _, _⟩ := hru
            exact hcr
          · exact Or.inl ⟨by rw [getD_push_lt_self]; rfl, by simp⟩
          · intro mn hmn
            simp only [Option.some.injEq] at hmn
            subst hmn
            rw [getD_push_lt_self]
            obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hsn⟩ := hru
            exact ⟨by simp [userFrame, hsn], rfl, rfl, rfl, rfl, rfl, rfl⟩
          · rw [getD_push_lt_self]; exact fun _ => rfl
          · show StackCtx m.heap (m.frames.push _) m.stack (jctxs ctx Γs)
            exact StackCtx.push hlt hsc
        · refine ⟨hgl, ?_⟩
          show CtlOkJ _ _ [] ((ctx, Γj) :: Γs) _
          exact ⟨hmfb, τb, τw, Γb, _, Γb,
            hbu, hsb.trans hsw, SubEnv.refl _,
            KontOkJ.frameK (fun σ hσ => by rw [hag σ (by simpa using hσ)]; exact hsw)
              rfl hk'⟩
    | @argsK _ D' _ _ _ _ _ mname recv τr psacc τp τrest psrest τret τw acc rest Γ' k _ _
        hrv hva hst hm hrest hsr hsg hsw hk' hsu =>
      cases rest with
      | nil =>
        cases hrest
        have hpr : psrest = [] := hsr.nil_inv
        subst hpr
        dsimp only
        obtain ⟨τr0, hsgA, hrv0, hnilτ⟩ :=
          sigOf_vty_atomic (by simpa using hsg) hrv
        have hground : ∀ p ∈ psacc ++ [τp], groundTy p = true := by
          intro p hp
          refine htab.2.2.2.2.2 τr0 mname _ (sigOf_declFor hnilτ hsgA) p ?_
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
          simp only [List.mem_append, List.mem_cons]
          rcases hp with hp | rfl
          · exact Or.inl hp
          · exact Or.inr (Or.inl rfl)
        have hbi : BuiltinEntryOk m.heap τr0 mname
            { params := psacc ++ [τp], ret := τret } := by
          rcases (htab.1 τr0 mname _ (sigOf_declFor hnilτ hsgA)).blockless with
            hb | ⟨_, _, _, _, _, hdp, _, _⟩
          · exact hb
          · exact absurd hdp (by simp)
        obtain ⟨w, m', hw, hg', hfr', hst', hko', hgv', hstep⟩ :=
          entry_dispatch (m := { m with kont := k }) (recv := recv) (args := acc ++ [v])
            (sigOf_atomic hnilτ hsgA).1 (sigOf_atomic hnilτ hsgA).2.1
            (sigOf_atomic hnilτ hsgA).2.2
            hbi (hrv0)
            ((VTys.snoc hva (hv.weaken hst)).toValuesTy hground)
        rw [hstep]
        exact inv_grow_valueJ (m := { m with kont := k })
          hfs htab hsc hh hsat hstr hcls hbot
          (by simpa [framePopLabels] using hks) hg' hfr' hst' hko'
          (VTy.weaken (VTy.ofValueTy hw) hsw) hk' hgl hgv' (hclo := hcloTail hK)
      | cons e rest' =>
        cases hrest with
        | cons he1 hrest' =>
          rename_i τe Γm Dm τrest'
          obtain ⟨τp', psrest', rfl, hs1, hs2⟩ := hsr.cons_inv
          have hsp : ∀ x, e ≠ Expr.splat x := by
            rintro x rfl
            exact nomatch hm (Expr.splat x) (by simp)
          have hkw : ∀ es, e ≠ Expr.kwargs es := by
            rintro es rfl
            exact nomatch hm (Expr.kwargs es) (by simp)
          have hfw : e ≠ Expr.fwd := by
            rintro rfl
            exact nomatch hm Expr.fwd (by simp)
          dsimp only
          rw [startArgs_plain hsp hkw hfw]
          exact inv_pushJ (m := { m with kont := k })
            hfs htab hsc hh hsat hstr hcls hbot
            (by simpa [framePopLabels] using hks) (hm _ (by simp)) he1 (SubJ.refl _)
            (KontOkJ.argsK (psacc := psacc ++ [τp]) hrv
              (VTys.snoc hva (hv.weaken hst)) hs1
              (fun a' ha' => hm a' (by simp [ha'])) hrest' hs2
              (by simpa using hsg) hsw hk') (hclo := hcloTail hK)
    | @frameK _ _ _ cΓ' Γs' _ fid k hrt hil hk' =>
      obtain ⟨c', Γ'⟩ := cΓ'
      have hst2 : ∃ f0 f1 rest, m.stack = f0 :: f1 :: rest := by
        cases hst : m.stack with
        | nil => rw [hst] at hfs; exact absurd hfs (by simp [FramesOkJ])
        | cons f0 t =>
          cases ht : t with
          | nil => rw [hst, ht] at hfs; exact absurd hfs (by simp [FramesOkJ])
          | cons f1 rest => exact ⟨f0, f1, rest, rfl⟩
      obtain ⟨f0, f1, rest, hst⟩ := hst2
      have hlab : framePopLabels k = m.stack.tail.dropLast := by
        have hq := hks
        simp only [framePopLabels] at hq
        rw [hst] at hq ⊢
        simp only [List.dropLast_cons_cons, List.cons.injEq] at hq
        simpa using hq.2
      refine ⟨hh, hsat, hstr, hcls, BottomObj_tail hbot, hlab,
        ClosuresOk.konts (hcloTail hK) rfl rfl (by intro κ hm; exact Or.inl hm),
        _, c', Γ', Γs', htab,
        hfs.tail, ?_, hgl, ⟨τ, _, hv, SubEnv.refl _, hk'⟩⟩
      exact StackCtx.tail hsc
  · -- ## control = jump — empty in the rung-1 fragment.
    rw [hctl] at hc
    exact absurd hc (by simp)

end Judgment
end Proof
end RubyCore
