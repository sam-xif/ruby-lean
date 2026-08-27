import RubyCore.Proof.Judgment.Frames
import RubyCore.Proof.Judgment.Decls

/-!
# Machine typing over `Judge` (J20) — `KontOkJ`, `CtlOkJ`, `InvJ`

`judgment-layer.md` §3, built: `CtlOk`/`KontOk`/`Inv` (Proof/Static/Konts.lean)
transliterated onto the declarative judgment. The shape is the old spine's shape —
one constructor per admitted continuation, subsumption slack (`SubJ` + `SubEnv`)
outside the stored judgment, the invariant existential over the table, context, and
environment stack — with three systematic changes:

* `infer*` premises become `Judge`/`JudgeSeq` derivations, plus the `MFrag` facts
  the eval arm will need when the stored program resumes;
* `subTy`/`ValueTy` become `SubJ`/`VTy` (J18/J19);
* the context is `JCtx` (the judgment's, with the `blk`/`inRescue` channels);
  `StackCtx` reads it through `.toFrameCtx`, unchanged.

The heap conjuncts of `Inv` (`NoHook`, `Saturated`, `LitClsOk`, `ClassOk`,
`BottomObj`, the `framePopLabels` correspondence, `ClosuresOk`) are reused verbatim —
they mention no typing. `GlobalsOk` is reused because declared global rows are ground
types, where `ValueTy` and `VTy` coincide (J19).

The constructor set grows with the fragment (`MFrag`, J20); this file holds the
rung-1 set — the T1 control core: value delivery, sequencing, local assignment,
branching, loops.
-/

namespace RubyCore
namespace Proof
namespace Judgment

open Interp
open RubyCore.Types
open RubyCore.Judgment
open RubyCore.Proof.Static

set_option maxRecDepth 100000

/-- A loop whose condition and body are judged at the loop-head environment `Γl`,
    each exit re-guaranteeing it — `LoopOk` with `chk`'s environment equality
    relaxed to the containment `Judge.while'` carries (J6). -/
def LoopOkJ (D : Decls) (Γl : Env) (c body : Expr) (top : Bool) (ctx : JCtx) : Prop :=
  MFrag c ∧ MFrag body ∧
  (∃ τc Γ₁, Judge D Γl c top ctx τc Γ₁ D ∧ SubEnv Γl Γ₁) ∧
  (∃ τb Γ₂, Judge D Γl body top ctx τb Γ₂ D ∧ SubEnv Γl Γ₂)

/-- `KontOk` over the judgment: *the in-flight value has type `τ` (as a `VTy`), the
    environment stack is `Γs`, and `k` is a well-typed continuation.* One
    constructor per admitted `Kont`; the absence of the rest is what collapses
    preservation's 48-way split. See `Proof/Static/Konts.lean:76` for the design
    commentary each constructor inherits. -/
inductive KontOkJ : Decls → Heap → List (JCtx × Env) → Ty → List Kont → Prop where
  /-- Empty stack: the in-flight value is the program's result. The two `none`
      channels are what let `RetOkJ`/`NxtOkJ` refute the empty position. -/
  | nil {D h Γs τ} :
      (∀ cΓ Γs', Γs = cΓ :: Γs' → cΓ.1.ret = none) →
      (∀ cΓ Γs', Γs = cΓ :: Γs' → cΓ.1.inLoop = none) →
      KontOkJ D h Γs τ []
  /-- `seqK []` yields the in-flight value unchanged. -/
  | seqNil {D h c Γ Γs τ τw k Γk} :
      SubJ τ τw → KontOkJ D h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γ := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ D h ((c, Γ) :: Γs) τ (.seqK [] :: k)
  /-- `seqK (e :: es)` discards the in-flight value and runs the rest. -/
  | seqCons {D D' h c Γ Γs τ e es τ' τw Γ' k Γk} :
      (∀ e' ∈ e :: es, MFrag e') →
      JudgeSeq D Γ (e :: es) Γs.isEmpty c τ' Γ' D' →
      SubJ τ' τw →
      KontOkJ D' h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γ' := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ D h ((c, Γ) :: Γs) τ (.seqK (e :: es) :: k)
  /-- Assignment binds `x` at the in-flight type and re-yields the value. -/
  | asgn {D h c Γ Γs τ τw x k Γk} :
      c.inBlock = false → SubJ τ τw →
      KontOkJ D h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk (envSet Γ x τ) := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ D h ((c, Γ) :: Γs) τ (.asgnK .lvar x :: k)
  /-- `@x = e`, with the value in flight: the conformance to whatever the table
      declares rides the kont (J26, mirroring L191/L196). -/
  | asgnIvar {D h c Γ Γs τ τw x k Γk} :
      c.selfCls.isSome = true → SubJ τ τw →
      (∀ cn σ, c.selfCls = some cn → ivarTy? D cn x = some σ → SubJ τ σ) →
      KontOkJ D h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γ := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ D h ((c, Γ) :: Γs) τ (.asgnK .ivar x :: k)
  /-- `$x = e`, with the value in flight (J26, mirroring L228). -/
  | asgnGvar {D h c Γ Γs τ τw x σ k Γk} :
      plainGlobal x = true →
      globalTy? D x = some σ →
      SubJ τ σ →
      SubJ τ τw →
      KontOkJ D h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γ := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ D h ((c, Γ) :: Γs) τ (.asgnK .gvar x :: k)
  /-- An array literal's element (J26, mirroring L174): the remaining elements ride
      as program, the answer is a fresh `Array`, the accumulated values are not
      mentioned (element types are erased at `.cls "Array"`). -/
  | arrK {D D' h c Γ Γs τ τw acc rest Γ' k Γk} :
      (∀ e ∈ rest, MFrag e) →
      JudgeElems D Γ rest Γs.isEmpty c Γ' D' →
      SubJ (.cls "Array") τw →
      KontOkJ D' h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γ' := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ D h ((c, Γ) :: Γs) τ (.arrK acc rest :: k)
  /-- The in-flight value is the condition; either branch may run next, judged at
      this constructor's own environment (the condition's exit), below the chosen
      join `τj` with the chosen continuation environment `Γc` — `Judge.ifElse`'s
      premises carried onto the continuation. -/
  | ifElseK {D Dt h c Γ Γs τ t els τt Γt τe Γe τj Γc τw k Γk} :
      MFrag t → MFrag els →
      Judge D Γ t Γs.isEmpty c τt Γt Dt →
      Judge D Γ els Γs.isEmpty c τe Γe Dt →
      SubJ τt τj → SubJ τe τj →
      SubEnv Γc Γt → SubEnv Γc Γe →
      SubJ τj τw →
      KontOkJ Dt h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γc := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ D h ((c, Γ) :: Γs) τ (.ifK t (some els) :: k)
  /-- The elseless `if`: a falsy condition delivers `nil`, so `nil` sits below the
      join (`Judge.ifNone`'s premise). -/
  | ifNoneK {D h c Γ Γs τ t τt Γt τj Γc τw k Γk} :
      MFrag t →
      Judge D Γ t Γs.isEmpty c τt Γt D →
      SubJ τt τj → SubJ .nilT τj →
      SubEnv Γc Γt → SubEnv Γc Γ →
      SubJ τj τw →
      KontOkJ D h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γc := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ D h ((c, Γ) :: Γs) τ (.ifK t none :: k)
  /-- The loop konts: condition in flight (`whileCond`) or body's value in flight
      (`whileBody`); the loop's own answer is `nil`, delivered to the enclosing
      continuation. The environment index is the loop head `Γl`, which every
      subcomputation exit re-guarantees (`LoopOkJ`). -/
  | whileCond {D h ctx Γl Γs τ τw c body k Γk} :
      LoopOkJ D Γl c body Γs.isEmpty (loopCtx ctx Γl) →
      SubJ .nilT τw →
      KontOkJ D h ((ctx, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γl := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ D h ((loopCtx ctx Γl, Γl) :: Γs) τ (.whileCondK c body :: k)
  | whileBody {D h ctx Γl Γs τ τw c body k Γk} :
      LoopOkJ D Γl c body Γs.isEmpty (loopCtx ctx Γl) →
      SubJ .nilT τw →
      KontOkJ D h ((ctx, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γl := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ D h ((loopCtx ctx Γl, Γl) :: Γs) τ (.whileBodyK c body :: k)
  /-- The in-flight value is the **receiver** of an argument-bearing send; the
      first argument runs next. -/
  | recvK {D D₂ h c Γ Γs τ mname arg args τs ps τret τw Γ₂ k Γk} {site : SendSite} :
      (∀ a ∈ arg :: args, MFrag a) →
      JudgeArgs D Γ (arg :: args) Γs.isEmpty c τs Γ₂ D₂ →
      sigOf D₂ τ mname = some (ps, τret) →
      SubJs τs ps →
      SubJ τret τw →
      KontOkJ D₂ h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γ₂ := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ D h ((c, Γ) :: Γs) τ (.recvK mname (arg :: args) .none site :: k)
  /-- A zero-argument send: the dispatch happens at the delivery itself, so the
      continuation is already at the return type. -/
  | recvK0 {D h c Γ Γs τ mname τret τw k Γk} {site : SendSite} :
      sigOf D τ mname = some ([], τret) →
      SubJ τret τw →
      KontOkJ D h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γ := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ D h ((c, Γ) :: Γs) τ (.recvK mname [] .none site :: k)
  /-- The in-flight value is an **argument**; the receiver and the evaluated prefix
      ride the kont as values, so their types are `VTy` facts against the heap —
      the constructor `heap_congr'` gains content at. -/
  | argsK {D D' h c Γ Γs τ mname recv τr psacc τp τrest psrest τret τw acc rest Γ' k Γk}
      {site : SendSite} :
      VTy h recv τr →
      VTys h acc psacc →
      SubJ τ τp →
      (∀ a ∈ rest, MFrag a) →
      JudgeArgs D Γ rest Γs.isEmpty c τrest Γ' D' →
      SubJs τrest psrest →
      sigOf D' τr mname = some (psacc ++ τp :: psrest, τret) →
      SubJ τret τw →
      KontOkJ D' h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γ' := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ D h ((c, Γ) :: Γs) τ (.argsK recv site mname acc rest .none :: k)
  /-- **Method return** — the callee's declared return type is what the caller's
      continuation expects; the two-deep stack is what makes the pop total. -/
  | frameK {D h cΓ cΓ' Γs τ fid k} :
      (∀ σ, cΓ.1.ret = some σ → SubJ σ τ) →
      cΓ.1.inLoop = none →
      KontOkJ D h (cΓ' :: Γs) τ k → KontOkJ D h (cΓ :: cΓ' :: Γs) τ (.frameK fid :: k)

/-- Transport of the continuation judgment across a heap the step grew — no rung-1
    constructor stores a `VTy` fact, so this is currently structural; the `argsK`
    rung is where it gains content (as `KontOk.heap_congr'` did at L137). -/
theorem KontOkJ.heap_congr' {h' : Heap} :
    ∀ {D : Decls} {h : Heap} {Γs : List (JCtx × Env)} {τ : Ty} {k : List Kont},
      KontOkJ D h Γs τ k → TypeAgree h h' → KontOkJ D h' Γs τ k := by
  intro D h Γs τ k hk
  induction hk with
  | nil hr hl => intro _; exact .nil hr hl
  | seqNil hw _ hsu ih => intro ha; exact .seqNil hw (ih ha) hsu
  | seqCons hm hs hw _ hsu ih => intro ha; exact .seqCons hm hs hw (ih ha) hsu
  | asgn hib hw _ hsu ih => intro ha; exact .asgn hib hw (ih ha) hsu
  | ifElseK hmt hme ht he hjt hje hct hce hw _ hsu ih =>
      intro ha; exact .ifElseK hmt hme ht he hjt hje hct hce hw (ih ha) hsu
  | ifNoneK hmt ht hjt hjn hct hce hw _ hsu ih =>
      intro ha; exact .ifNoneK hmt ht hjt hjn hct hce hw (ih ha) hsu
  | whileCond hl hw _ hsu ih => intro ha; exact .whileCond hl hw (ih ha) hsu
  | whileBody hl hw _ hsu ih => intro ha; exact .whileBody hl hw (ih ha) hsu
  | recvK hm hargs hsg hsub hw _ hsu ih =>
      intro ha; exact .recvK hm hargs hsg hsub hw (ih ha) hsu
  | recvK0 hsg hw _ hsu ih => intro ha; exact .recvK0 hsg hw (ih ha) hsu
  | argsK hrv hva hst hm hrest hsr hsg hw _ hsu ih =>
      intro ha
      exact .argsK (hrv.congr ha) (VTys.congr ha hva) hst hm hrest hsr hsg hw (ih ha) hsu
  | frameK hrt hil _ ih => intro ha; exact .frameK hrt hil (ih ha)
  | asgnIvar hsc hw hcf _ hsu ih => intro ha; exact .asgnIvar hsc hw hcf (ih ha) hsu
  | asgnGvar hpg hgt hcf hw _ hsu ih =>
      intro ha; exact .asgnGvar hpg hgt hcf hw (ih ha) hsu
  | arrK hm hje hw _ hsu ih => intro ha; exact .arrK hm hje hw (ih ha) hsu

theorem KontOkJ.heap_congr {h h' : Heap} (ha : TypeAgree h h')
    {D : Decls} {Γs : List (JCtx × Env)} {τ : Ty} {k : List Kont}
    (hk : KontOkJ D h Γs τ k) : KontOkJ D h' Γs τ k :=
  KontOkJ.heap_congr' hk ha

/-- The control clause over the judgment (`CtlOk`, Proof/Static/Konts.lean:925).
    The eval arm adds the fragment gate; the jump arms are `False` until the rungs
    that produce jumps (`return`/`next`/`raise`) enter the fragment. -/
def CtlOkJ (D : Decls) (c : JCtx) (Γ : Env) (Γs : List (JCtx × Env))
    (m : Machine) : Prop :=
  match m.ctl with
  | .eval e =>
    MFrag e ∧
    ∃ τ τ' Γ' D' Γk, Judge D Γ e Γs.isEmpty c τ Γ' D' ∧ SubJ τ τ' ∧
      SubEnv Γk Γ' ∧ KontOkJ D' m.heap ((c, Γk) :: Γs) τ' m.kont
  | .value v => ∃ τ Γk, VTy m.heap v τ ∧ SubEnv Γk Γ ∧
      KontOkJ D m.heap ((c, Γk) :: Γs) τ m.kont
  | .jump _ => False

/-- The `JCtx`-shaped context stack, projected for `StackCtx`. -/
def jctxs (c : JCtx) (Γs : List (JCtx × Env)) : List FrameCtx :=
  (c :: Γs.map Prod.fst).map JCtx.toFrameCtx

/-- **The invariant** handed to `invariant_sound_from` — `Inv` (Proof/Static/
    Konts.lean:1346) with the typed existential in the judgment vocabulary. -/
def InvJ (m : Machine) : Prop :=
  NoHook m.heap ∧ Saturated m.heap ∧ LitClsOk m.heap ∧
    ClassOk m.heap ∧ BottomObj m.frames m.stack ∧
    framePopLabels m.kont = m.stack.dropLast ∧
    ClosuresOk m ∧
    ∃ (F : Decls) (c : JCtx) (Γ : Env) (Γs : List (JCtx × Env)),
      DeclsOkJ F m.heap ∧
      FramesOkJ m.heap m.frames m.stack (Γ :: Γs.map Prod.snd) ∧
      StackCtx m.heap m.frames m.stack (jctxs c Γs) ∧
      GlobalsOk F m.heap m.globals ∧
      CtlOkJ F c Γ Γs m

/-! ## The five re-establishment helpers (Proof/Static/Konts.lean:1969–2245) -/

theorem inv_evalJ {F : Decls} {m : Machine} {c : JCtx} {Γ : Env}
    {Γs : List (JCtx × Env)} {Γk : Env} {e : Expr} {τ τ' : Ty} {Γ' : Env} {F' : Decls}
    (hfs : FramesOkJ m.heap m.frames m.stack (Γ :: Γs.map Prod.snd))
    (ht : DeclsOkJ F m.heap)
    (hsc : StackCtx m.heap m.frames m.stack (jctxs c Γs))
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : LitClsOk m.heap)
    (hcls : ClassOk m.heap) (hbot : BottomObj m.frames m.stack)
    (hks : framePopLabels m.kont = m.stack.dropLast)
    (hmf : MFrag e)
    (hj : Judge F Γ e Γs.isEmpty c τ Γ' F')
    (hsub : SubJ τ τ')
    (hk : KontOkJ F' m.heap ((c, Γk) :: Γs) τ' m.kont)
    (hgl : GlobalsOk F m.heap m.globals := by assumption)
    (hsuE : SubEnv Γk Γ' := by first | exact SubEnv.refl _ | assumption)
    (hclo : ClosuresOk m := by assumption) :
    InvJ (withCtl m (.eval e)) :=
  ⟨hh, hsat, hstr, hcls, hbot, hks, hclo.ctl, F, c, Γ, Γs, ht, hfs, hsc, hgl,
   hmf, ⟨τ, τ', Γ', F', Γk, hj, hsub, hsuE, hk⟩⟩

theorem inv_valueJ {F : Decls} {m : Machine} {c : JCtx} {Γ : Env}
    {Γs : List (JCtx × Env)} {Γk : Env} {v : Value} {τ : Ty}
    (hfs : FramesOkJ m.heap m.frames m.stack (Γ :: Γs.map Prod.snd))
    (ht : DeclsOkJ F m.heap)
    (hsc : StackCtx m.heap m.frames m.stack (jctxs c Γs))
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : LitClsOk m.heap)
    (hcls : ClassOk m.heap) (hbot : BottomObj m.frames m.stack)
    (hks : framePopLabels m.kont = m.stack.dropLast)
    (hv : VTy m.heap v τ) (hk : KontOkJ F m.heap ((c, Γk) :: Γs) τ m.kont)
    (hgl : GlobalsOk F m.heap m.globals := by assumption)
    (hsuE : SubEnv Γk Γ := by first | exact SubEnv.refl _ | assumption)
    (hclo : ClosuresOk m := by assumption) :
    InvJ (withCtl m (.value v)) :=
  ⟨hh, hsat, hstr, hcls, hbot, hks, hclo.ctl, F, c, Γ, Γs, ht, hfs, hsc, hgl,
   ⟨τ, Γk, hv, hsuE, hk⟩⟩

theorem inv_pushJ {F : Decls} {m : Machine} {c : JCtx} {Γ : Env}
    {Γs : List (JCtx × Env)} {Γk : Env} {e : Expr} {τ τ' : Ty} {Γ' : Env} {F' : Decls}
    {k : Kont}
    (hfs : FramesOkJ m.heap m.frames m.stack (Γ :: Γs.map Prod.snd))
    (ht : DeclsOkJ F m.heap)
    (hsc : StackCtx m.heap m.frames m.stack (jctxs c Γs))
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : LitClsOk m.heap)
    (hcls : ClassOk m.heap) (hbot : BottomObj m.frames m.stack)
    (hks : framePopLabels (k :: m.kont) = m.stack.dropLast)
    (hmf : MFrag e)
    (hj : Judge F Γ e Γs.isEmpty c τ Γ' F')
    (hsub : SubJ τ τ')
    (hk : KontOkJ F' m.heap ((c, Γk) :: Γs) τ' (k :: m.kont))
    (hgl : GlobalsOk F m.heap m.globals := by assumption)
    (hsuE : SubEnv Γk Γ' := by first | exact SubEnv.refl _ | assumption)
    (hkc : KontClosure k = none := by simp [KontClosure])
    (hclo : ClosuresOk m := by assumption) :
    InvJ (withKont m (.eval e) k) :=
  ⟨hh, hsat, hstr, hcls, hbot, hks, hclo.cons hkc, F, c, Γ, Γs, ht, hfs, hsc, hgl,
   hmf, ⟨τ, τ', Γ', F', Γk, hj, hsub, hsuE, hk⟩⟩

theorem inv_grow_valueJ {F : Decls} {m m' : Machine} {c : JCtx} {Γ : Env}
    {Γs : List (JCtx × Env)} {Γk : Env} {v : Value} {τ : Ty}
    (hfs : FramesOkJ m.heap m.frames m.stack (Γ :: Γs.map Prod.snd))
    (ht : DeclsOkJ F m.heap)
    (hsc : StackCtx m.heap m.frames m.stack (jctxs c Γs))
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : LitClsOk m.heap)
    (hcls : ClassOk m.heap) (hbot : BottomObj m.frames m.stack)
    (hks : framePopLabels m.kont = m.stack.dropLast)
    (hg : PlainGrow m.heap m'.heap)
    (hfr : m'.frames = m.frames) (hst : m'.stack = m.stack) (hko : m'.kont = m.kont)
    (hv : VTy m'.heap v τ) (hk : KontOkJ F m.heap ((c, Γk) :: Γs) τ m.kont)
    (hgl : GlobalsOk F m.heap m.globals := by assumption)
    (hgv : m'.globals = m.globals := by rfl)
    (hsuE : SubEnv Γk Γ := by first | exact SubEnv.refl _ | assumption)
    (hclo : ClosuresOk m := by assumption) :
    InvJ (withCtl m' (.value v)) := by
  have hag : TypeAgree m.heap m'.heap := typeAgree_of_plainGrow hg hsat
  refine ⟨NoHook_grow hg hsat hh,
    Saturated_grow hg.shapeAgree hg.size hsat, LitClsOk_grow hg hstr,
    ClassOk_grow hg hsat hcls,
    show BottomObj m'.frames m'.stack by rw [hfr, hst]; exact hbot,
    show framePopLabels m'.kont = m'.stack.dropLast by rw [hko, hst]; exact hks,
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
    F, c, Γ, Γs, DeclsOkJ_grow hg hsat ht, ?_, ?_, ?_, ?_⟩
  · show FramesOkJ m'.heap m'.frames m'.stack (Γ :: Γs.map Prod.snd)
    rw [hfr, hst]
    exact FramesOkJ.heap_congr hag hfs
  · show StackCtx m'.heap m'.frames m'.stack (jctxs c Γs)
    rw [hfr, hst]
    exact StackCtx.heap_congr hag hsc
  · show GlobalsOk F m'.heap m'.globals
    rw [hgv]
    exact GlobalsOk.congr hag hgl
  · show ∃ σ Γk, VTy m'.heap v σ ∧ SubEnv Γk Γ ∧
        KontOkJ F m'.heap ((c, Γk) :: Γs) σ m'.kont
    exact ⟨τ, _, hv, hsuE, by rw [hko]; exact KontOkJ.heap_congr hag hk⟩

/-! ## The dispatch boundary: `sigOf` answers only at ground receiver types -/

/-- A row is only readable at a type that names classes, and those are ground. -/
theorem declFor_ground {D : Decls} {σ : Ty} {mname : String} {d : MethodDecl}
    (h : declFor D σ mname = some d) : groundTy σ = true := by
  cases σ <;> first
    | rfl
    | (exact absurd h (by simp [declFor, tyClassNames]))

theorem sigOf_ground {D : Decls} {τ : Ty} {mname : String} {ps : List Ty} {τret : Ty}
    (h : sigOf D τ mname = some (ps, τret)) : groundTy τ = true := by
  cases τ
  case nilable σ =>
    obtain ⟨-, h2⟩ := sigOf_nilable h
    simpa [groundTy] using declFor_ground h2
  all_goals first
    | rfl
    | (exact absurd h (by simp [sigOf, declFor, tyClassNames]))

/-- `sigOf_value_atomic`, lifted to `VTy`: the receiver's widened judgment collapses
    back to the old `ValueTy` at the (ground) dispatch type, and a nilable receiver
    reduces to the arm the value actually is. -/
theorem sigOf_vty_atomic {D : Decls} {h : Heap} {v : Value} {τ : Ty} {mname : String}
    {ps : List Ty} {τret : Ty}
    (hsg : sigOf D τ mname = some (ps, τret)) (hv : VTy h v τ) :
    ∃ τ₀, sigOf D τ₀ mname = some (ps, τret) ∧ ValueTy h v τ₀ ∧
      (∀ τ', τ₀ ≠ .nilable τ') :=
  sigOf_value_atomic hsg (hv.toValueTy (sigOf_ground hsg))

end Judgment
end Proof
end RubyCore
