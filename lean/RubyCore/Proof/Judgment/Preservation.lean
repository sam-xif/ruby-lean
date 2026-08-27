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

/-- `StepOk` with the invariant swapped: `.next` carries `InvJ`, `.uncaught` is
    admitted when the exception is not a type error (progress is exactly this
    clause), everything else refused. **J29:** the `done` arm is no longer a mere
    halt — the delivered value inhabits the answer type. This is the single point
    where the `ans` parameter pays out: it is what `SemJudge`'s result clause and
    `judge_result_vty` consume, and its bill is one `VTy.weaken` at the
    `KontOkJ.nil` inversion in `step_okJ`'s delivery branch. -/
def StepOkJ (ans : Ty) (A : SemAxioms) : StepResult → Prop
  | .next m' => InvJ ans A m'
  | .done v mf => VTy mf.heap v ans
  | .uncaught exc m => ¬ isTypeError m.heap exc
  | _ => False

/-- The eval branch's motive: everything `step_okJ` knows at an eval state, with the
    conclusion over `evalExpr`. Universally quantified over the machine so the
    `Judge.rec` induction can thread it through `sub`. -/
def EvalOkAt (ans : Ty) (A : SemAxioms) (D : Decls) (Γ : Env) (e : Expr) (top : Bool) (ctx : JCtx)
    (τ : Ty) (Γ' : Env) (D' : Decls) : Prop :=
  ∀ (m : Machine) (Γs : List (JCtx × Env)) (τw : Ty) (Γk : Env),
    top = Γs.isEmpty →
    FramesOkJ m.heap m.frames m.stack (Γ :: Γs.map Prod.snd) →
    DeclsOkJ A D m.heap →
    StackCtx m.heap m.frames m.stack (jctxs ctx Γs) →
    NoHook m.heap → Saturated m.heap → LitClsOk m.heap → ClassOk m.heap →
    BottomObj m.frames m.stack →
    framePopLabels m.kont = m.stack.dropLast →
    GlobalsOk D m.heap m.globals →
    ClosuresOk m →
    MFrag A e →
    SubJ τ τw → SubEnv Γk Γ' →
    KontOkJ ans A D' m.heap ((ctx, Γk) :: Γs) τw m.kont →
    StepOkJ ans A (evalExpr m e)

/-- **J31 — the semantic obligation.** One claim's meaning: `EvalOkAt` at the
    canonical judgment (`.any`, environment- and table-preserving), at *every*
    table, environment, context, position, and answer type. This is exactly the
    statement `step_okJ`'s eval branch needs of a claimed expression, so the
    preservation case for a semantic leaf is an application, not a proof. A user
    extension = one lemma of this shape per claimed expression. -/
def SemAxiomsOk (A : SemAxioms) : Prop :=
  ∀ cl ∈ A, ∀ (ans : Ty) (D : Decls) (Γ : Env) (top : Bool) (c : JCtx),
    (∀ cn, cl.reqCls = some cn →
      c.cls = cn ∧ c.inClassBody = true ∧ c.inBlock = false) →
    (∀ r ∈ cl.rows, declaresName D r.2.1 = false) →
    EvalOkAt ans A D Γ cl.e top c cl.τ Γ (addRows D cl.rows)

/-- The empty axiom set is vacuously discharged — every pre-J31 theorem is the
    `A := []` instance. -/
theorem semAxiomsOk_nil : SemAxiomsOk [] := by
  intro cl hcl; exact absurd hcl (by simp)


@[simp] theorem jctxs_eq (c : JCtx) (Γs : List (JCtx × Env)) :
    jctxs c Γs = c.toFrameCtx :: (Γs.map Prod.fst).map JCtx.toFrameCtx := rfl

set_option maxHeartbeats 1000000 in
/-- The zero-argument implicit-self send preserves `InvJ`, whatever the site —
    `inv_implicit_send0` (Proof/Static/Preservation.lean:66) over the judgment.
    The dispatch happens *in this step*; the builtin arm ends in
    `inv_grow_valueJ`, the user arm pushes the activation whose body's `Judge`
    derivation `UserConformsJ` carries. -/
theorem inv_implicit_send0J {ans : Ty} {F : Decls} {m : Machine} {ctx : JCtx} {Γ Γk : Env}
    {Γs : List (JCtx × Env)} {c mname : String} {τret : Ty} {site : SendSite}
    (hfs : FramesOkJ m.heap m.frames m.stack (Γ :: Γs.map Prod.snd))
    (htab : DeclsOkJ A F m.heap)
    (hsc : StackCtx m.heap m.frames m.stack (jctxs ctx Γs))
    (hhook : NoHook m.heap) (hsat : Saturated m.heap) (hstr : LitClsOk m.heap)
    (hcls : ClassOk m.heap) (hbot : BottomObj m.frames m.stack)
    (hks : framePopLabels m.kont = m.stack.dropLast)
    (hne : m.stack ≠ []) (hsome : ctx.selfCls = some c)
    (hsg : sigOf F (.cls c) mname = some ([], τret))
    {τw : Ty} (hsubw : SubJ τret τw)
    (hk : KontOkJ ans A F m.heap ((ctx, Γk) :: Γs) τw m.kont)
    (hglob : GlobalsOk F m.heap m.globals := by assumption)
    (hsuE : SubEnv Γk Γ := by first | exact SubEnv.refl _ | assumption)
    (hclo : ClosuresOk m := by assumption) :
    StepOkJ ans A (startArgs m m.currentFrame.self site mname [] [] .none) := by
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
    obtain ⟨hdp, hdblk, hdfu, hmfb, hfb, Γb, r, τb, hbu, hsb, hag⟩ := hconfu
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
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      · exact fun hcb _ => nomatch hcb
      · show StackCtx m.heap (m.frames.push _) m.stack (jctxs ctx Γs)
        exact StackCtx.push hlt hsc
    · refine ⟨hglob, ?_⟩
      show CtlOkJ F _ [] ((ctx, Γk) :: Γs) _ _ _
      exact Or.inl ⟨hfb, hmfb, τb, τw, Γb, F, Γb,
        hbu, hsb.trans hsubw, SubEnv.refl _,
        KontOkJ.frameK (fun σ h => by rw [hag σ (by simpa using h)]; exact hsubw) rfl hk⟩


/-- **The array literal's loop** (J26, mirroring `inv_continueArray`): nothing left
    → allocate; a head to run → push `arrK`. Fragment elements are never splats
    (`MFrag` has no constructor at that shape), so the loop stays on the plain
    branch. -/
theorem inv_continueArrayJ {ans : Ty} {D D' : Decls} {m : Machine} {c : JCtx} {Γ Γ' : Env}
    {Γs : List (JCtx × Env)} {Γk : Env} {τw : Ty} {acc : List Value} {rest : List Expr}
    (hfs : FramesOkJ m.heap m.frames m.stack (Γ :: Γs.map Prod.snd))
    (htab : DeclsOkJ A D m.heap)
    (hsc : StackCtx m.heap m.frames m.stack (jctxs c Γs))
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : LitClsOk m.heap)
    (hcls : ClassOk m.heap) (hbot : BottomObj m.frames m.stack)
    (hks : framePopLabels m.kont = m.stack.dropLast)
    (hgl : GlobalsOk D m.heap m.globals)
    (hfa : ∀ e ∈ rest, fragHead e = true)
    (hm : ∀ e ∈ rest, MFrag A e)
    (hje : JudgeElems A D Γ rest Γs.isEmpty c Γ' D')
    (hsw : SubJ (.cls "Array") τw)
    (hk : KontOkJ ans A D' m.heap ((c, Γk) :: Γs) τw m.kont)
    (hsuE : SubEnv Γk Γ' := by first | exact SubEnv.refl _ | assumption)
    (hclo : ClosuresOk m := by assumption) :
    StepOkJ ans A (Interp.continueArray m acc rest) := by
  cases hje with
  | nil =>
    simp only [Interp.continueArray, Builtins.allocArr]
    exact inv_grow_valueJ hfs htab hsc hh hsat hstr hcls hbot hks
      (plainGrow_alloc m.heap _ (by simp) rfl) rfl rfl rfl
      (VTy.weaken (VTy.ofValueTy
        (valueTy_alloc_fresh (by simp) rfl rfl rfl hstr.2.1 hstr.2.2
          (fun _ => ⟨_, rfl⟩))) hsw) hk
  | @cons _ _ e rest' _ _ τe Γ₁ D₁ _ _ he hrest =>
    have hnsp : ∀ x, e ≠ Expr.splat x := by
      rintro x rfl
      exact nomatch hm (Expr.splat x) (by simp)
    rw [continueArray_plain (by intro x hq; exact absurd hq (hnsp x))]
    exact inv_pushJ hfs htab hsc hh hsat hstr hcls hbot
      (by simp [framePopLabels, hks]) (hm e (by simp)) (hfa e (by simp)) he (SubJ.refl _)
      (KontOkJ.arrK (fun e' he' => hfa e' (by simp [he']))
        (fun e' he' => hm e' (by simp [he'])) hrest hsw hk)

set_option maxHeartbeats 2000000 in
/-- **The eval branch**, by induction over the derivation. -/
theorem judge_eval_ok {ans : Ty} {A : SemAxioms} {D : Decls} {Γ : Env} {e : Expr}
    {top : Bool} {ctx : JCtx}
    {τ : Ty} {Γ' : Env} {D' : Decls} (hj : Judge A D Γ e top ctx τ Γ' D')
    (hfh : fragHead e = true) :
    EvalOkAt ans A D Γ e top ctx τ Γ' D' := by
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
    (motive_11 := fun D Γ e top ctx τ Γ' D' _ =>
      fragHead e = true → EvalOkAt ans A D Γ e top ctx τ Γ' D')
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
    ?hdefined ?harray ?hhash ?hseq ?hsub ?hsemantic
    hj hfh
  case hsemantic =>
    intro D Γ top ctx cl hmem hff hreq hfr hdisc hfh
    rw [hff] at hfh
    exact Bool.noConfusion hfh
  -- The ten auxiliary relations' constructors: their motives are `True`.
  all_goals try (intros; trivial)
  -- ## Literals: one step to a value of the exact type.
  case hint =>
    intro D Γ n top ctx
    intro _hfh
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    exact inv_valueJ hfs htab hsc hh hsat hstr hcls hbot hks
      (VTy.weaken (VTy.exact rfl) hsubw) hk
  case hflt =>
    intro D Γ x top ctx
    intro _hfh
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    exact inv_valueJ hfs htab hsc hh hsat hstr hcls hbot hks
      (VTy.weaken (VTy.exact rfl) hsubw) hk
  case hsym =>
    intro D Γ s top ctx
    intro _hfh
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    exact inv_valueJ hfs htab hsc hh hsat hstr hcls hbot hks
      (VTy.weaken (VTy.exact rfl) hsubw) hk
  case htru =>
    intro D Γ top ctx
    intro _hfh
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    exact inv_valueJ hfs htab hsc hh hsat hstr hcls hbot hks
      (VTy.weaken (VTy.exact rfl) hsubw) hk
  case hfls =>
    intro D Γ top ctx
    intro _hfh
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    exact inv_valueJ hfs htab hsc hh hsat hstr hcls hbot hks
      (VTy.weaken (VTy.exact rfl) hsubw) hk
  case hnil =>
    intro D Γ top ctx
    intro _hfh
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    exact inv_valueJ hfs htab hsc hh hsat hstr hcls hbot hks
      (VTy.weaken (VTy.exact rfl) hsubw) hk
  -- ## The string literal: the producer — one allocation, `inv_grow_valueJ`.
  case hstr =>
    intro D Γ s top ctx
    intro _hfh
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    exact inv_grow_valueJ hfs htab hsc hh hsat hstr hcls hbot hks
      (plainGrow_alloc m.heap _ (by simp) rfl) rfl rfl rfl
      (VTy.weaken (VTy.ofValueTy
        (valueTy_alloc_fresh (by simp) rfl rfl rfl hstr.1.1 hstr.1.2 (by simp))) hsubw) hk
  -- ## Local read: `LocalsOkJ`, off the head frame's conformance.
  case hvarLvar =>
    intro D Γ x top ctx τ0 hget
    intro _hfh
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    exact inv_valueJ hfs htab hsc hh hsat hstr hcls hbot hks
      (VTy.weaken (hfs.localsOk x τ0 hget) hsubw) hk
  -- ## Local write: push the assignment kont on the rhs.
  case hvasgnLvar =>
    intro D Γ x rhs top ctx τ0 Γ₁ D₁ hib hrhs ih
    intro _hfh
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    cases hmf with
    | semantic hmem hff => simp [fragHead] at hff
    | vasgnLvar hfrhs hmrhs =>
      subst htop
      exact inv_pushJ hfs htab hsc hh hsat hstr hcls hbot
        (by simp [framePopLabels, hks]) hmrhs hfrhs hrhs (SubJ.refl _)
        (KontOkJ.asgn hib hsubw hk)
  -- ## Sequencing: the three-way split `evalExpr` makes.
  case hseq =>
    intro D Γ es top ctx τ0 Γ' D'0 hseq ihseq
    intro _hfh
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    subst htop
    have hall : ∀ e' ∈ es, MFrag A e' := by
      cases hmf with
      | semantic hmem hff => simp [fragHead] at hff
      | seq h => exact h
    cases hseq with
    | nil =>
      exact inv_valueJ hfs htab hsc hh hsat hstr hcls hbot hks
        (VTy.weaken (VTy.exact rfl) hsubw) hk
    | @single _ _ e1 _ _ _ _ _ hj1 hcpl =>
      by_cases hfe : fragHead e1 = true
      · exact inv_evalJ hfs htab hsc hh hsat hstr hcls hbot hks
          (hall _ (by simp)) hfe hj1 hsubw hk
      · -- claimed statement in final position: the coupling pins the claim's
        -- judgment, so the continuation's expectation matches the claimed type
        replace hfe : fragHead e1 = false := by simpa using hfe
        obtain ⟨cl, hclA, rfl, rfl, rfl, rfl, hdisc, hreq, hfr⟩ := hcpl hfe
        exact inv_evalSemJ hfs htab hsc hh hsat hstr hcls hbot hks
          hclA rfl hfe hdisc hreq hfr hsubw hk
    | @cons _ _ e1 e₂ rest _ _ τ₁ Γ₁ D₁ _ _ _ hj1 hrest hcpl =>
      by_cases hfe : fragHead e1 = true
      · exact inv_pushJ hfs htab hsc hh hsat hstr hcls hbot
          (by simp [framePopLabels, hks]) (hall _ (by simp)) hfe hj1 (SubJ.refl _)
          (KontOkJ.seqCons (fun e' he' => hall e' (List.mem_cons_of_mem _ he'))
            hrest hsubw hk)
      · -- claimed statement mid-sequence: the value is discarded, the rest was
        -- judged at the (coupling-pinned) environment and effected table
        replace hfe : fragHead e1 = false := by simpa using hfe
        obtain ⟨cl, hclA, rfl, rfl, rfl, hD₁, hdisc, hreq, hfr⟩ := hcpl hfe
        subst hD₁
        exact inv_pushSemJ hfs htab hsc hh hsat hstr hcls hbot
          (by simp [framePopLabels, hks])
          hclA rfl hfe hdisc hreq hfr (SubJ.refl cl.τ)
          (KontOkJ.seqCons (fun e' he' => hall e' (List.mem_cons_of_mem _ he'))
            hrest hsubw hk)
  -- ## `if`: push the branch kont on the condition.
  case hifElse =>
    intro D Γ cond t els top ctx τc Γ₁ D₁ τt Γt Dt τe Γe τj Γc
    intro hcnd ht he hjt hje hct hce ihc iht ihe
    intro _hfh
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    subst htop
    cases hmf with
    | semantic hmem hff => simp [fragHead] at hff
    | ifElse hfc hft hfe hmc hmt hme =>
      exact inv_pushJ hfs htab hsc hh hsat hstr hcls hbot
        (by simp [framePopLabels, hks]) hmc hfc hcnd (SubJ.refl _)
        (KontOkJ.ifElseK hft hfe hmt hme ht he hjt hje hct hce hsubw hk)
  case hifNone =>
    intro D Γ cond t top ctx τc Γ₁ D₁ τt Γt τj Γc
    intro hcnd ht hjt hjn hct hcΓ ihc iht
    intro _hfh
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    subst htop
    cases hmf with
    | semantic hmem hff => simp [fragHead] at hff
    | ifNone hfc hft hmc hmt =>
      exact inv_pushJ hfs htab hsc hh hsat hstr hcls hbot
        (by simp [framePopLabels, hks]) hmc hfc hcnd (SubJ.refl _)
        (KontOkJ.ifNoneK hft hmt ht hjt hjn hct hcΓ hsubw hk)
  -- ## The narrowing `if` (J27): the push chooses the stored value's atom by
  -- `vty_narrow_kit`, sharpens the binding (no write — `FramesOkJ.setHead`), and
  -- registers the narrowing kont; the machine's own truthiness test at the
  -- delivery is the narrowing evidence.
  case hifNarrowElse =>
    intro D Γ x t els top ctx τ0 τt Γt Dt τe Γe τj Γc
    intro hget ht he hjt hje hct hce iht ihe
    intro _hfh
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    subst htop
    cases hmf with
    | semantic hmem hff => simp [fragHead] at hff
    | ifElse hfc hft hfe hmc hmt hme =>
      have hv0 : VTy m.heap (m.getLocal x) τ0 := hfs.localsOk x τ0 hget
      obtain ⟨a, hva, hs0, hT, hFn, hFf⟩ := vty_narrow_kit hv0
      have hfs' := FramesOkJ.setHead hfs hva
      simp only [evalExpr]
      exact inv_pushJ (Γ := envSet Γ x a) hfs' htab hsc hh hsat hstr hcls hbot
        (by simp [framePopLabels, hks]) MFrag.varLvar rfl
        (Judge.varLvar (by rw [envGet?_set]; simp))
        (SubJ.refl _)
        (KontOkJ.ifNarrowElseK hft hfe hmt hme hget ht he hjt hje hct hce hs0 hT hFn hFf
          hsubw hk)
  case hifNarrowNone =>
    intro D Γ x t top ctx τ0 τt Γt τj Γc
    intro hget ht hjt hjn hct hcΓ iht
    intro _hfh
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    subst htop
    cases hmf with
    | semantic hmem hff => simp [fragHead] at hff
    | ifNone hfc hft hmc hmt =>
      have hv0 : VTy m.heap (m.getLocal x) τ0 := hfs.localsOk x τ0 hget
      obtain ⟨a, hva, hs0, hT, hFn, hFf⟩ := vty_narrow_kit hv0
      have hfs' := FramesOkJ.setHead hfs hva
      simp only [evalExpr]
      exact inv_pushJ (Γ := envSet Γ x a) hfs' htab hsc hh hsat hstr hcls hbot
        (by simp [framePopLabels, hks]) MFrag.varLvar rfl
        (Judge.varLvar (by rw [envGet?_set]; simp))
        (SubJ.refl _)
        (KontOkJ.ifNarrowNoneK hft hmt hget ht hjt hjn hct hcΓ hs0 hT hsubw hk)
  -- ## `while`: enter the loop at the chosen head environment.
  case hwhile =>
    intro D Γ Γl cond body top ctx τc Γ₁ τb Γ₂
    intro hentry hcnd hs1 hbody hs2 ihc ihb
    intro _hfh
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    subst htop
    cases hmf with
    | semantic hmem hff => simp [fragHead] at hff
    | while' hfc hfb hmc hmb =>
      have hfs' := FramesOkJ.narrowHead hentry hfs
      have hloop : LoopOkJ A D Γl cond body Γs.isEmpty (loopCtx ctx Γl) :=
        ⟨hfc, hfb, hmc, hmb, ⟨τc, Γ₁, hcnd, hs1⟩, ⟨τb, Γ₂, hbody, hs2⟩⟩
      refine inv_pushJ (c := loopCtx ctx Γl) hfs' htab ?_ hh hsat hstr hcls hbot
        (by simp [framePopLabels, hks]) hmc hfc hcnd (SubJ.refl _)
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
    intro _hfh
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
    intro _hfh
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    simp only [evalExpr]
    exact inv_implicit_send0J hfs htab hsc hh hsat hstr hcls hbot hks
      (hfs.frameShallow).1 hsome hsg hsubw hk
  -- ## The block-less send.
  case hsend =>
    intro D Γ recvO mname args top ctx τr Γ₁ D₁ τs Γ₂ D₂ ps τret
    intro hrecv hargs hsg hsub ihr iha
    intro _hfh
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    subst htop
    cases hrecv with
    | expl hr =>
      -- Explicit receiver: push the receiver kont; which constructor depends on
      -- the argument count, exactly as `applyKont` behaves one step later.
      cases hmf with
      | semantic hmem hff => simp [fragHead] at hff
      | send hne hfr hfa hmr hma =>
      cases args with
      | nil =>
        cases hargs
        have hps : ps = [] := hsub.nil_inv
        subst hps
        simp only [evalExpr]
        rename_i r
        cases r <;>
          exact inv_pushJ hfs htab hsc hh hsat hstr hcls hbot
            (by simp [framePopLabels, hks]) hmr hfr hr (SubJ.refl _)
            (KontOkJ.recvK0 hsg hsubw hk)
      | cons a as =>
        simp only [evalExpr]
        rename_i r
        cases r <;>
          exact inv_pushJ hfs htab hsc hh hsat hstr hcls hbot
            (by simp [framePopLabels, hks]) hmr hfr hr (SubJ.refl _)
            (KontOkJ.recvK (fun a' ha' => hfa a' ha') (fun a' ha' => hma a' ha')
              hargs hsg hsub hsubw hk)
    | @self _ _ _ _ cc hsome =>
      -- Implicit receiver: `startArgs` on the frame's `self`, with no receiver kont.
      cases hmf with
      | semantic hmem hff => simp [fragHead] at hff
      | sendImplicit hfa hma =>
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
            (by simp [framePopLabels, hks]) (hma _ (by simp)) (hfa _ (by simp)) ha1
            (SubJ.refl _)
            (KontOkJ.argsK (psacc := []) (VTy.ofValueTy hself) trivial hs1
              (fun a' ha' => hfa a' (by simp [ha']))
              (fun a' ha' => hma a' (by simp [ha'])) harest hs2
              (by simpa using hsg) hsubw hk)
  -- ## `class C … end` — the reopen: a frame push on an untouched heap.
  case hclassTop =>
    intro D Γ name body ctx τ0 Γb' Db hmem hbody ihb
    intro _hfh
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    cases hmf with
    | semantic hmem hff => simp [fragHead] at hff
    | classTop hfb hmb =>
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
        D, ({ cls := name, inClassBody := true } : JCtx), [], [(ctx, Γk)],
        htab, ?_, ?_, hgl, ?_⟩
      · refine ⟨by rw [Array.size_push]; exact Nat.lt_succ_self _, hlt,
          ⟨ShallowChain.of_none (by rw [getD_push_lt_self]; try rfl), ?_, ?_⟩,
          FramesOkJ.push hfs⟩
        · rw [getD_push_lt_self]; simp [hpay]
        · intro y σ hy; exact absurd hy (by simp [envGet?])
      · refine ⟨?_, ?_, ?_, ?_, ?_, Or.inr rfl, fun mn h' => absurd h' (by simp), ?_,
          (fun _ _ => by rw [getD_push_lt_self]), StackCtx.push hlt hsc⟩
        · rw [getD_push_lt_self]; simp [hpay]
        · rw [getD_push_lt_self]; exact fun _ => hnm
        · rw [getD_push_lt_self]; exact fun _ => rfl
        · exact fun sc hsc' => absurd hsc' (by simp)
        · rw [getD_push_lt_self]
          exact List.mem_cons_of_mem _ hcrefCur
        · rw [getD_push_lt_self]; exact fun _ => rfl
      · exact Or.inl ⟨hfb, hmb, τ0, τw, Γb', Db, Γb', hbody, hsubw, SubEnv.refl _,
          KontOkJ.frameK (fun _ h' => by simp at h') rfl hk⟩
  -- ## `def` — the two derivations of the same step: install-only (`defDecl`) and
  -- row-threading promotion (`defPromote`). The heap write and the value are
  -- identical; the difference is the table the invariant is re-established at.
  case hdefDecl =>
    intro D Γ name ps body top ctx τs σb bs τb Γb'
    intro hfresh hha hlen hbody hsbb ihb
    intro _hfh
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
    have hlkNH : ∀ md : MethodDef,
        NoHook (defineMethod m.heap (curFrame m).defmod name md) :=
      fun _ => NoHook_defineMethod hh hha
    have hlk : ∀ md : MethodDef,
        lookup (defineMethod m.heap (curFrame m).defmod name md)
          (.ref (curFrame m).defmod) "method_added" = none := fun md =>
      (hlkNH md).2 (curFrame m).defmod
        (by rw [classPayload?_isSome_defineMethod]; exact hdo)
        "method_added" (by simp [hookFreeNames])
    have hres : ∀ (m₀ : Machine),
        m₀.frames = m.frames → m₀.stack = m.stack → m₀.kont = m.kont →
        TypeAgree m.heap m₀.heap → DeclsOkJ A D m₀.heap → NoHook m₀.heap →
        Saturated m₀.heap → LitClsOk m₀.heap → ClassOk m₀.heap →
        GlobalsOk D m₀.heap m₀.globals →
        InvJ ans A (withCtl m₀ (.value (.sym name))) := by
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
            KontOkJ ans A D m₀.heap ((ctx, Γk') :: Γs) σ' m₀.kont
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
    intro _hfh
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    obtain ⟨hffb, hmfb⟩ : fragHead body = true ∧ MFrag A body := by
      cases hmf with
      | semantic hmem hff => simp [fragHead] at hff
      | def' hfb hmb => exact ⟨hfb, hmb⟩
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
    have hlkNH : ∀ md : MethodDef,
        NoHook (defineMethod m.heap (curFrame m).defmod name md) :=
      fun _ => NoHook_defineMethod hh hha
    have hlk : ∀ md : MethodDef,
        lookup (defineMethod m.heap (curFrame m).defmod name md)
          (.ref (curFrame m).defmod) "method_added" = none := fun md =>
      (hlkNH md).2 (curFrame m).defmod
        (by rw [classPayload?_isSome_defineMethod]; exact hdo)
        "method_added" (by simp [hookFreeNames])
    have hres : ∀ (m₀ : Machine),
        m₀.frames = m.frames → m₀.stack = m.stack → m₀.kont = m.kont →
        TypeAgree m.heap m₀.heap →
        DeclsOkJ A (addRow D ctx.cls name { params := [], ret := τb }) m₀.heap →
        NoHook m₀.heap → Saturated m₀.heap → LitClsOk m₀.heap → ClassOk m₀.heap →
        GlobalsOk (addRow D ctx.cls name { params := [], ret := τb }) m₀.heap
          m₀.globals →
        InvJ ans A (withCtl m₀ (.value (.sym name))) := by
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
            KontOkJ ans A (addRow D ctx.cls name { params := [], ret := τb }) m₀.heap
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
        DeclsOkJ A (addRow D ctx.cls name { params := [], ret := τb })
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
        rfl, by rw [hbd]; exact hdfree, by rw [hbd]; exact hmfb,
        by rw [hbd]; exact hffb, ?_⟩)
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
      · obtain ⟨-, hbo'⟩ := judge_mono hbody (by simp [methodCtx]) hffb hmfb hdfree (subDecls_addRow hfresh)
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
  -- ## The table-read heads (J26): const, ivar, gvar — reads off `DeclsOkJ`.
  case hconst =>
    intro D Γ nm top ctx τ0 hre
    intro _hfh
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    obtain ⟨v, hconst, hty, hsole⟩ := htab.2.1 nm _ hre
    have hne : m.stack ≠ [] := (hfs.frameShallow).1
    cases hst : m.stack with
    | nil => exact absurd hst hne
    | cons fid fids =>
      have hsc' := hsc
      rw [hst] at hsc'
      have hcur : m.currentFrame = m.frames.getD fid default := by
        simp [Machine.currentFrame, hst]
      have hcref : Boot.objectId ∈ m.currentFrame.cref := by
        rw [hcur]; exact hsc'.2.2.2.2.1
      simp only [evalExpr]
      rw [constRead_sole hcref hconst hsole]
      exact inv_valueJ hfs htab hsc hh hsat hstr hcls hbot hks
        (VTy.weaken (VTy.ofValueTy hty) hsubw) hk
  case hvarIvar =>
    intro D Γ x top ctx sc σ hsome hiv
    intro _hfh
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    have hne : m.stack ≠ [] := (hfs.frameShallow).1
    have hself : ValueTy m.heap m.currentFrame.self (.cls sc) := by
      cases hst : m.stack with
      | nil => exact absurd hst hne
      | cons fid fids =>
        rw [hst] at hsc
        have := hsc.2.2.2.1 sc hsome
        rw [show m.currentFrame = m.frames.getD fid default by
          simp [Machine.currentFrame, hst]]
        exact this.1
    obtain ⟨o, hsf⟩ : ∃ o, m.currentFrame.self = .ref o := by
      cases hsv : m.currentFrame.self with
      | ref o' => exact ⟨o', rfl⟩
      | _ => rw [hsv] at hself; simp_all [ValueTy, valueTy?, subTy]
    have hpl : plainRecv m.heap o = true := valueTy_ref_plain (hsf ▸ hself)
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
    refine inv_valueJ hfs htab hsc hh hsat hstr hcls hbot hks
      (VTy.weaken (VTy.ofValueTy ?_) hsubw) hk
    cases hfind : ((m.heap.get o).ivars.find? (·.1 == x)).map Prod.snd with
    | none => simpa [hfind] using ValueTy.weaken (ValueTy.exact rfl) (by simp)
    | some v =>
      have := htab.2.2.1 sc x σ hiv o hlt hcn v hfind
      simpa [hfind] using ValueTy.weaken this (by simp)
  case hvarGvar =>
    intro D Γ x top ctx σ hpg hgt
    intro _hfh
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    simp only [evalExpr, matchGlobal_none_of_plain hpg]
    exact inv_valueJ hfs htab hsc hh hsat hstr hcls hbot hks
      (VTy.weaken (VTy.ofValueTy (GlobalsOk.read hgl hpg hgt)) hsubw) hk
  case hvasgnIvarDecl =>
    intro D Γ x rhs top ctx sc τ0 Γ₁ D₁ σ hsome hrhs hiv hsj ih
    intro _hfh
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    cases hmf with
    | semantic hmem hff => simp [fragHead] at hff
    | vasgnIvar hfr hmr =>
      subst htop
      exact inv_pushJ hfs htab hsc hh hsat hstr hcls hbot
        (by simp [framePopLabels, hks]) hmr hfr hrhs (SubJ.refl _)
        (KontOkJ.asgnIvar (by rw [hsome]; rfl) hsubw
          (fun cn σ' hcn hiv' => by
            rw [hsome, Option.some.injEq] at hcn
            subst hcn
            rw [hiv] at hiv'
            simp only [Option.some.injEq] at hiv'
            subst hiv'
            exact hsj) hk)
  case hvasgnIvarFresh =>
    intro D Γ x rhs top ctx sc τ0 Γ₁ D₁ hsome hrhs hiv ih
    intro _hfh
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    cases hmf with
    | semantic hmem hff => simp [fragHead] at hff
    | vasgnIvar hfr hmr =>
      subst htop
      exact inv_pushJ hfs htab hsc hh hsat hstr hcls hbot
        (by simp [framePopLabels, hks]) hmr hfr hrhs (SubJ.refl _)
        (KontOkJ.asgnIvar (by rw [hsome]; rfl) hsubw
          (fun cn σ' hcn hiv' => by
            rw [hsome, Option.some.injEq] at hcn
            subst hcn
            rw [hiv] at hiv'
            exact absurd hiv' (by simp)) hk)
  case hvasgnGvar =>
    intro D Γ x rhs top ctx τ0 Γ₁ D₁ σ hpg hrhs hgt hsj ih
    intro _hfh
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    cases hmf with
    | semantic hmem hff => simp [fragHead] at hff
    | vasgnGvar hfr hmr =>
      subst htop
      exact inv_pushJ hfs htab hsc hh hsat hstr hcls hbot
        (by simp [framePopLabels, hks]) hmr hfr hrhs (SubJ.refl _)
        (KontOkJ.asgnGvar hpg hgt hsj hsubw hk)
  case harray =>
    intro D Γ es top ctx Γ'0 D'0 hje ih
    intro _hfh
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    subst htop
    obtain ⟨hfa, hall⟩ : (∀ e' ∈ es, fragHead e' = true) ∧ (∀ e' ∈ es, MFrag A e') := by
      cases hmf with
      | semantic hmem hff => simp [fragHead] at hff
      | array hf h => exact ⟨hf, h⟩
    simp only [evalExpr]
    exact inv_continueArrayJ hfs htab hsc hh hsat hstr hcls hbot hks hgl hfa hall hje
      hsubw hk
  -- ## `sendCall`'s conclusion is a send head, so the fragment gate's shape
  -- condition (no `call`-named explicit sends) is what refutes it.
  case hsendCall =>
    intro D Γ r args top ctx τr Γ₁ D₁ τs Γ₂ D₂ ps ret hr hparts hargs hsub ihr iha
    intro _hfh
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    cases hmf with
    | semantic hmem hff => simp [fragHead] at hff
    | send hne _ _ _ _ => exact absurd rfl hne
  -- ## The subsumption rule: compose the invariant's slack, once for all heads.
  case hsub =>
    intro D Γ e top ctx τ0 Γ'0 D'0 σ Γ'' hj0 hs hse ih
    intro _hfh
    intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw hsuE hk
    exact ih _hfh m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf
      (hs.trans hsubw) (SubEnv.trans hsuE hse) hk
  -- ## Everything else is out of the rung-1 fragment: refuted by `MFrag`.
  -- ## Everything else is out of the rung-1 fragment: refuted by the `fragHead`
  -- gate (post-J31 — `MFrag`'s semantic arm makes the old empty-`cases` refutation
  -- insufficient, but a claimed head is out of the *syntactic* universe, which is
  -- exactly what the gated motive says cannot be here).
  all_goals
    (intros
     first
      | exact Bool.noConfusion ‹fragHead _ = true›
      | (refine fun m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo
           hmf hsubw hsuE hk => ?_
         cases hmf <;> simp_all [fragHead]))

/-- **Progress and preservation in one case analysis** — `step_ok`, over `InvJ`. -/
theorem step_okJ {ans : Ty} {A : SemAxioms} {m : Machine} (hax : SemAxiomsOk A)
    (h : InvJ ans A m) : StepOkJ ans A (stepFn m) := by
  obtain ⟨hh, hsat, hstr, hcls, hbot, hks, hclo, F, ctx, Γ, Γs, htab, hfs, hsc, hgl, hc⟩ := h
  have hcloTail : ∀ {κ₀ : Kont} {k' : List Kont}, m.kont = κ₀ :: k' →
      ClosuresOk { m with kont := k' } := fun hkq =>
    ClosuresOk.konts hclo rfl rfl
      (by intro κ hm; exact Or.inl (by rw [hkq]; exact List.mem_cons_of_mem _ hm))
  unfold CtlOkJ at hc
  rcases hctl : m.ctl with e | v | j
  · -- ## control = eval e — dispatch on the J31 mode
    rw [hctl] at hc
    rcases hc with ⟨hfh, hmf, τ, τw, Γ', D', Γk, hj, hsubw, hsuE, hk⟩ |
      ⟨cl, hmem, hcle, hfh, hdisc, hreq, hfr, τw, Γk, hs', hsuE, hk⟩
    · simp only [stepFn, hctl]
      exact judge_eval_ok hj hfh m Γs τw Γk rfl hfs htab hsc hh hsat hstr hcls hbot hks
        hgl hclo hmf hsubw hsuE hk
    · -- the semantic leaf: the claim's obligation, applied
      simp only [stepFn, hctl]
      subst hcle
      exact hax cl hmem ans F Γ Γs.isEmpty ctx hreq hfr m Γs τw Γk rfl hfs htab hsc hh
        hsat hstr hcls hbot hks hgl hclo (.semantic ⟨cl, hmem, rfl⟩ hfh) hs' hsuE hk
  · -- ## control = value v
    rw [hctl] at hc
    obtain ⟨τ, Γk, hv, hsuE, hk⟩ := hc
    have hfs := FramesOkJ.narrowHead hsuE hfs
    simp only [stepFn, hctl]
    unfold applyKont
    generalize hK : m.kont = K at hk hks ⊢
    cases hk with
    | nil hsub _ _ => exact VTy.weaken hv hsub
    | @seqNil _ _ _ _ _ _ τw k _ hsw hk' hsu =>
      exact inv_valueJ hfs htab hsc hh hsat hstr hcls hbot
        (by simpa [framePopLabels] using hks)
        (VTy.weaken hv hsw) hk' (hclo := hcloTail hK)
    | @seqCons _ _ _ _ _ _ _ e₁ es τ' τw Γ' k _ hm hseq hsw hk' hsu =>
      cases hseq with
      | single hj1 hcpl =>
        by_cases hfe : fragHead e₁ = true
        · exact inv_pushJ hfs htab hsc hh hsat hstr hcls hbot
            (by simpa [framePopLabels] using hks) (hm _ (by simp)) hfe hj1 hsw
            (KontOkJ.seqNil (SubJ.refl _) hk') (hclo := hcloTail hK)
        · -- claimed final statement: the coupling pins the claim's judgment
          replace hfe : fragHead e₁ = false := by simpa using hfe
          obtain ⟨cl, hclA, rfl, rfl, rfl, rfl, hdisc, hreq, hfr⟩ := hcpl hfe
          exact inv_pushSemJ hfs htab hsc hh hsat hstr hcls hbot
            (by simpa [framePopLabels] using hks)
            hclA rfl hfe hdisc hreq hfr hsw
            (KontOkJ.seqNil (SubJ.refl _) hk') (hclo := hcloTail hK)
      | cons hj1 hrest hcpl =>
        by_cases hfe : fragHead e₁ = true
        · exact inv_pushJ hfs htab hsc hh hsat hstr hcls hbot
            (by simpa [framePopLabels] using hks) (hm _ (by simp)) hfe hj1 (SubJ.refl _)
            (KontOkJ.seqCons (fun e' he' => hm e' (List.mem_cons_of_mem _ he'))
              hrest hsw hk') (hclo := hcloTail hK)
        · -- claimed mid-sequence statement: value discarded, threading pinned
          replace hfe : fragHead e₁ = false := by simpa using hfe
          obtain ⟨cl, hclA, rfl, rfl, rfl, hD₁, hdisc, hreq, hfr⟩ := hcpl hfe
          subst hD₁
          exact inv_pushSemJ hfs htab hsc hh hsat hstr hcls hbot
            (by simpa [framePopLabels] using hks)
            hclA rfl hfe hdisc hreq hfr (SubJ.refl cl.τ)
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
        hft hfe hmt hme ht he hjt hje hct hce hjw hk' hsu =>
      by_cases hb : v.truthy
      · simp only [hb, if_true]
        exact inv_evalJ hfs htab hsc hh hsat hstr hcls hbot
          (by simpa [framePopLabels] using hks) hmt hft ht (hjt.trans hjw) hk'
          (hsuE := SubEnv.trans hsu hct) (hclo := hcloTail hK)
      · simp only [hb]
        exact inv_evalJ hfs htab hsc hh hsat hstr hcls hbot
          (by simpa [framePopLabels] using hks) hme hfe he (hje.trans hjw) hk'
          (hsuE := SubEnv.trans hsu hce) (hclo := hcloTail hK)
    | @ifNoneK _ _ _ _ _ _ t τt Γt τj Γc τw k _
        hft hmt ht hjt hjn hct hcΓ hjw hk' hsu =>
      by_cases hb : v.truthy
      · simp only [hb, if_true]
        exact inv_evalJ hfs htab hsc hh hsat hstr hcls hbot
          (by simpa [framePopLabels] using hks) hmt hft ht (hjt.trans hjw) hk'
          (hsuE := SubEnv.trans hsu hct) (hclo := hcloTail hK)
      · simp only [hb]
        exact inv_valueJ hfs htab hsc hh hsat hstr hcls hbot
          (by simpa [framePopLabels] using hks)
          (VTy.weaken (VTy.exact rfl) (hjn.trans hjw)) hk'
          (hsuE := SubEnv.trans hsu hcΓ) (hclo := hcloTail hK)
    | ifNarrowElseK hft hfe hmt hme hget ht he hjt hje2 hct hce hs0 hT hFn hFf hjw hk' hsu =>
      by_cases hb : v.truthy
      · rcases hT with rfl | hdrop
        · exact absurd hb (by rw [vty_nilT_eq hv]; simp [Value.truthy])
        · have hfs' := FramesOkJ.narrowHeadJ (subEnvJ_set hdrop) hfs
          simp only [hb, if_true]
          exact inv_evalJ hfs' htab hsc hh hsat hstr hcls hbot
            (by simpa [framePopLabels] using hks) hmt hft ht (hjt.trans hjw) hk'
            (hsuE := SubEnv.trans hsu hct) (hclo := hcloTail hK)
      · simp only [hb]
        rcases truthy_false_cases (by simpa using hb) with rfl | rfl
        · have hfs' := FramesOkJ.narrowHeadJ (subEnvJ_set (hFn (vty_nil_subJ hv))) hfs
          exact inv_evalJ hfs' htab hsc hh hsat hstr hcls hbot
            (by simpa [framePopLabels] using hks) hme hfe he (hje2.trans hjw) hk'
            (hsuE := SubEnv.trans hsu hce) (hclo := hcloTail hK)
        · have hfs' := FramesOkJ.narrowHeadJ (subEnvJ_set (hFf (vty_false_subJ hv))) hfs
          exact inv_evalJ hfs' htab hsc hh hsat hstr hcls hbot
            (by simpa [framePopLabels] using hks) hme hfe he (hje2.trans hjw) hk'
            (hsuE := SubEnv.trans hsu hce) (hclo := hcloTail hK)
    | ifNarrowNoneK hft hmt hget ht hjt hjn hct hcb hs0 hT hjw hk' hsu =>
      by_cases hb : v.truthy
      · rcases hT with rfl | hdrop
        · exact absurd hb (by rw [vty_nilT_eq hv]; simp [Value.truthy])
        · have hfs' := FramesOkJ.narrowHeadJ (subEnvJ_set hdrop) hfs
          simp only [hb, if_true]
          exact inv_evalJ hfs' htab hsc hh hsat hstr hcls hbot
            (by simpa [framePopLabels] using hks) hmt hft ht (hjt.trans hjw) hk'
            (hsuE := SubEnv.trans hsu hct) (hclo := hcloTail hK)
      · simp only [hb]
        have hfs' := FramesOkJ.narrowHeadJ (subEnvJ_unset hget hs0) hfs
        exact inv_valueJ hfs' htab hsc hh hsat hstr hcls hbot
          (by simpa [framePopLabels] using hks)
          (VTy.weaken (VTy.exact rfl) (hjn.trans hjw)) hk'
          (hsuE := SubEnv.trans hsu hcb) (hclo := hcloTail hK)
    | @whileCond _ _ ctx' Γl _ _ τw c body k _ hloop hsw hk' hsu =>
      obtain ⟨hfc, hfb, hmc, hmb, ⟨τc, Γ₁, hcnd, hs1⟩, ⟨τb, Γ₂, hbody, hs2⟩⟩ := hloop
      by_cases hb : v.truthy
      · simp only [hb, if_true]
        exact inv_pushJ hfs htab hsc hh hsat hstr hcls hbot
          (by simpa [framePopLabels] using hks) hmb hfb hbody (SubJ.refl _)
          (KontOkJ.whileBody ⟨hfc, hfb, hmc, hmb, ⟨τc, Γ₁, hcnd, hs1⟩, ⟨τb, Γ₂, hbody, hs2⟩⟩
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
      obtain ⟨hfc, hfb, hmc, hmb, ⟨τc, Γ₁, hcnd, hs1⟩, ⟨τb, Γ₂, hbody, hs2⟩⟩ := hloop
      exact inv_pushJ hfs htab hsc hh hsat hstr hcls hbot
        (by simpa [framePopLabels] using hks) hmc hfc hcnd (SubJ.refl _)
        (KontOkJ.whileCond ⟨hfc, hfb, hmc, hmb, ⟨τc, Γ₁, hcnd, hs1⟩, ⟨τb, Γ₂, hbody, hs2⟩⟩
          hsw hk' (hsu := hsu))
        (hsuE := hs1) (hclo := hcloTail hK)
    | @recvK _ D₂ _ _ _ _ _ mname arg args τs ps τret τw Γ₂ k _ _ hfm hm hargs hsg hsub hsw hk' hsu =>
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
          (by simpa [framePopLabels] using hks) (hm _ (by simp)) (hfm _ (by simp)) ha1
          (SubJ.refl _)
          (KontOkJ.argsK (psacc := []) hv trivial hs1
            (fun a' ha' => hfm a' (by simp [ha']))
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
        obtain ⟨hdp, hdblk, hdfu, hmfb, hfb, Γb, r, τb, hbu, hsb, hag⟩ := hconfu
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
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
          · exact fun hcb _ => nomatch hcb
          · show StackCtx m.heap (m.frames.push _) m.stack (jctxs ctx Γs)
            exact StackCtx.push hlt hsc
        · refine ⟨hgl, ?_⟩
          show CtlOkJ _ _ [] ((ctx, Γj) :: Γs) _ _ _
          exact Or.inl ⟨hfb, hmfb, τb, τw, Γb, _, Γb,
            hbu, hsb.trans hsw, SubEnv.refl _,
            KontOkJ.frameK (fun σ hσ => by rw [hag σ (by simpa using hσ)]; exact hsw)
              rfl hk'⟩
    | @argsK _ D' _ _ _ _ _ mname recv τr psacc τp τrest psrest τret τw acc rest Γ' k _ _
        hrv hva hst hfm hm hrest hsr hsg hsw hk' hsu =>
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
          refine htab.2.2.2.2.2.1 τr0 mname _ (sigOf_declFor hnilτ hsgA) p ?_
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
            (by simpa [framePopLabels] using hks) (hm _ (by simp)) (hfm _ (by simp)) he1
            (SubJ.refl _)
            (KontOkJ.argsK (psacc := psacc ++ [τp]) hrv
              (VTys.snoc hva (hv.weaken hst)) hs1
              (fun a' ha' => hfm a' (by simp [ha']))
              (fun a' ha' => hm a' (by simp [ha'])) hrest' hs2
              (by simpa using hsg) hsw hk') (hclo := hcloTail hK)
    | @asgnIvar _ _ _ _ _ _ τw x k _ hsome hsw hcf hk' hsu =>
      obtain ⟨sc, hsc'⟩ := Option.isSome_iff_exists.mp hsome
      have hself : ValueTy m.heap m.currentFrame.self (.cls sc) := by
        cases hst : m.stack with
        | nil => exact absurd hst (hfs.frameShallow).1
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
      have hcnO : className m.heap (m.heap.get o).klass = sc := by
        rcases valueTy_ref_inv (by simp [subTy]) (by simp [subTy]) (hsf ▸ hself)
          with ⟨-, hs⟩ | ⟨hc, hs⟩
        · have hq := (subTy_atomic (τ := Ty.cls sc) (by simp) (by simp)).mp hs
          rw [plainRecv_classOf hpl] at hq
          simpa using hq
        · exact absurd hs (by simp [subTy])
      have hltO : o < m.heap.objs.size := by
        unfold plainRecv at hpl; simp only [Bool.and_eq_true] at hpl
        simpa using hpl.1.1.1.1.1
      show StepOkJ ans A (match m.currentFrame.self with
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
      have hgb : (bindIvar { m with kont := k } x v).globals = m.globals := by
        unfold bindIvar; rw [show ({ m with kont := k } : Machine).currentFrame
          = m.currentFrame from rfl, hsf]
      refine ⟨hi.noHook hh, hi.saturated hsat, hi.litClsOk hstr, hi.classOk hcls,
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
        F, ctx, Γk, Γs,
        ⟨(ivarOnly_rowsAndConstsJ hi htab).1, (ivarOnly_rowsAndConstsJ hi htab).2.1, ?_,
          (ivarOnly_rowsAndConstsJ hi htab).2.2.1, (ivarOnly_rowsAndConstsJ hi htab).2.2.2,
          htab.2.2.2.2.2.1, htab.2.2.2.2.2.2.1, htab.2.2.2.2.2.2.2⟩,
        ?_, ?_, ?_, ?_⟩
      · intro c' x' σ' hiv' o' ho0 hcn' v' hv'
        have hsz : (withCtl (bindIvar { m with kont := k } x v) (.value v)).heap.objs.size
            = m.heap.objs.size := hi.size
        have ho' : o' < m.heap.objs.size := by omega
        simp only [withCtl] at hcn' hv'
        by_cases hoo : o' = o
        · have hcls' : c' = sc := by
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
            -- The written slot: the value's `VTy` at the declared type, collapsed to
            -- `ValueTy` — the row's type is ground (`DeclsOkJ` has no groundness for
            -- ivar rows, so go through `ivarTy?`'s… the declared σ' is what `hcf`
            -- answers at, as a `SubJ`; `IvarOk` is `ValueTy`-based, so collapse.
            exact ValueTy.congr hag
              ((VTy.weaken hv (hcf _ σ' hsc' hiv')).toValueTy (htab.2.2.2.2.2.2.1 _ _ _ hiv'))
          · rw [bindIvar_ivars_self (m := { m with kont := k }) hsf hltO,
              List.find?_cons_of_neg (by simpa using fun hq => hxx hq.symm),
              find?_filter_ne _ hxx] at hv'
            exact ValueTy.congr hag (htab.2.2.1 _ x' σ' hiv' o ho' hcnO v' hv')
        · rw [bindIvar_get_ne (m := { m with kont := k }) hsf hoo] at hcn' hv'
          rw [hi.className_eq] at hcn'
          exact ValueTy.congr hag (htab.2.2.1 c' x' σ' hiv' o' ho' hcn' v' hv')
      · show FramesOkJ _ (bindIvar { m with kont := k } x v).frames
          (bindIvar { m with kont := k } x v).stack (Γk :: Γs.map Prod.snd)
        rw [hfr, hstk]; exact FramesOkJ.heap_congr hag hfs
      · show StackCtx _ (bindIvar { m with kont := k } x v).frames
          (bindIvar { m with kont := k } x v).stack (jctxs ctx Γs)
        rw [hfr, hstk]; exact StackCtx.heap_congr hag hsc
      · rw [show (withCtl (bindIvar { m with kont := k } x v) (.value v)).globals
                 = m.globals from hgb]
        exact GlobalsOk.congr
          (h' := (withCtl (bindIvar { m with kont := k } x v) (.value v)).heap) hag hgl
      · exact ⟨τw, _, VTy.congr hag (VTy.weaken hv hsw), hsu,
          by rw [show (withCtl (bindIvar { m with kont := k } x v) (.value v)).kont
                    = k from hkt]
             exact KontOkJ.heap_congr hag hk'⟩
    | @asgnGvar _ _ _ _ _ _ τw x σ k _ hpg hgt hcf hsw hk' hsu =>
      show StepOkJ ans A (.next (Interp.withCtl (({ m with kont := k }).setGlobal x v) (.value v)))
      rw [setGlobal_of_plain (m := { m with kont := k }) hpg]
      simp only [Interp.withCtl]
      refine ⟨hh, hsat, hstr, hcls, hbot, (by simpa [framePopLabels] using hks),
        ClosuresOk.konts (hcloTail hK) rfl rfl
          (by intro κ hm; exact Or.inl (by simpa using hm)),
        F, ctx, Γk, Γs, htab, hfs, hsc,
        GlobalsOk.set hgl hgt ((hv.weaken hcf).toValueTy (htab.2.2.2.2.2.2.2 _ _ hgt)),
        ⟨τw, _, VTy.weaken hv hsw, hsu, hk'⟩⟩
    | @arrK _ D' _ _ _ _ _ τw acc rest Γ' k _ hfm hm hje hsw hk' hsu =>
      exact inv_continueArrayJ (m := { m with kont := k })
        hfs htab hsc hh hsat hstr hcls hbot (by simpa [framePopLabels] using hks) hgl
        hfm hm hje hsw hk' (hclo := hcloTail hK)
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
