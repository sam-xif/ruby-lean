import RubyCore.Proof.Judgment.Konts

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
  · -- ## control = jump — empty in the rung-1 fragment.
    rw [hctl] at hc
    exact absurd hc (by simp)

end Judgment
end Proof
end RubyCore
