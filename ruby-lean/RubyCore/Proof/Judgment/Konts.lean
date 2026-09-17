import RubyCore.Proof.Judgment.Frames
import RubyCore.Proof.Judgment.Decls
import RubyCore.Proof.Judgment.TableRet

/-!
# Machine typing over `Judge` (J20) — `KontOkJ`, `CtlOkJ`, `InvJ`

the judgment-layer note §3, built: `CtlOk`/`KontOk`/`Inv` (Proof/Static/Konts.lean)
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
def LoopOkJ (A : SemAxioms) (D : Decls) (Γl : Env) (c body : Expr) (top : Bool) (ctx : JCtx) : Prop :=
  fragHead c = true ∧ fragHead body = true ∧ MFrag A c ∧ MFrag A body ∧
  (∃ τc Γ₁, Judge A D Γl c top ctx τc Γ₁ D ∧ SubEnv Γl Γ₁) ∧
  (∃ τb Γ₂, Judge A D Γl body top ctx τb Γ₂ D ∧ SubEnv Γl Γ₂)

/-- `KontOk` over the judgment: *the in-flight value has type `τ` (as a `VTy`), the
    environment stack is `Γs`, and `k` is a well-typed continuation.* One
    constructor per admitted `Kont`; the absence of the rest is what collapses
    preservation's 48-way split. See `Proof/Static/Konts.lean:76` for the design
    commentary each constructor inherits.

    **J29: the answer type.** `ans` is a *parameter*, not an index — it is the type
    the whole continuation stack eventually answers at, constant along the spine
    (every constructor threads it to its tail untouched), and pinned only at `nil`:
    an empty continuation's in-flight value *is* the answer, so `nil` demands
    `SubJ τ ans`. Before J29 the `nil` constructor accepted any in-flight type,
    which made the invariant forget the program's judged type by the time the
    machine reached `done` — true safety, vacuous result typing. With the
    parameter, `StepOkJ`'s `done` arm can (and now does) conclude
    `VTy mf.heap v ans`, which is what `SemJudge`'s result clause consumes. -/
inductive KontOkJ (ans : Ty) (A : SemAxioms) : Decls → Heap → List (JCtx × Env) → Ty → List Kont → Prop where
  /-- Empty stack: the in-flight value is the program's result — so it must sit
      below the answer type. The two `none` channels are what let
      `RetOkJ`/`NxtOkJ` refute the empty position. -/
  | nil {D h Γs τ} :
      SubJ τ ans →
      (∀ cΓ Γs', Γs = cΓ :: Γs' → cΓ.1.ret = none) →
      (∀ cΓ Γs', Γs = cΓ :: Γs' → cΓ.1.inLoop = none) →
      KontOkJ ans A D h Γs τ []
  /-- `seqK []` yields the in-flight value unchanged. -/
  | seqNil {D h c Γ Γs τ τw k Γk} :
      SubJ τ τw → KontOkJ ans A D h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γ := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ ans A D h ((c, Γ) :: Γs) τ (.seqK [] :: k)
  /-- `seqK (e :: es)` discards the in-flight value and runs the rest. -/
  | seqCons {D D' h c Γ Γs τ e es τ' τw Γ' k Γk} :
      (∀ e' ∈ e :: es, MFrag A e') →
      JudgeSeq A D Γ (e :: es) Γs.isEmpty c τ' Γ' D' →
      SubJ τ' τw →
      KontOkJ ans A D' h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γ' := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ ans A D h ((c, Γ) :: Γs) τ (.seqK (e :: es) :: k)
  /-- Assignment binds `x` at the in-flight type and re-yields the value. -/
  | asgn {D h c Γ Γs τ τw x k Γk} :
      c.inBlock = false → SubJ τ τw →
      KontOkJ ans A D h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk (envSet Γ x τ) := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ ans A D h ((c, Γ) :: Γs) τ (.asgnK .lvar x :: k)
  /-- `@x = e`, with the value in flight: the conformance to whatever the table
      declares rides the kont (J26, mirroring L191/L196). -/
  | asgnIvar {D h c Γ Γs τ τw x k Γk} :
      c.selfCls.isSome = true → SubJ τ τw →
      (∀ cn σ, c.selfCls = some cn → ivarTy? D cn x = some σ → SubJ τ σ) →
      KontOkJ ans A D h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γ := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ ans A D h ((c, Γ) :: Γs) τ (.asgnK .ivar x :: k)
  /-- `$x = e`, with the value in flight (J26, mirroring L228). -/
  | asgnGvar {D h c Γ Γs τ τw x σ k Γk} :
      plainGlobal x = true →
      globalTy? D x = some σ →
      SubJ τ σ →
      SubJ τ τw →
      KontOkJ ans A D h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γ := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ ans A D h ((c, Γ) :: Γs) τ (.asgnK .gvar x :: k)
  /-- `C::n`, with the base in flight (J38, mirroring L205's `KontOk.cpathK`): the
      table is read here (`scopedConstTy?`), the container's heap at the delivery
      (`ScopedConstOk`, `DeclsOkJ`'s conjunct) — so the delivery re-establishes
      nothing. -/
  | cpathK {D h c Γ Γs τ τw cname n σ k Γk} :
      SubJ τ (.clsOf cname) →
      scopedConstTy? D cname n = some σ →
      SubJ σ τw →
      KontOkJ ans A D h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γ := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ ans A D h ((c, Γ) :: Γs) τ (.cpathK n :: k)
  /-- An array literal's element (J26, mirroring L174): the remaining elements ride
      as program, the answer is a fresh `Array`, the accumulated values are not
      mentioned (element types are erased at `.cls "Array"`). -/
  | arrK {D D' h c Γ Γs τ τw acc rest Γ' k Γk} :
      (∀ e ∈ rest, fragHead e = true) →
      (∀ e ∈ rest, MFrag A e) →
      JudgeElems A D Γ rest Γs.isEmpty c Γ' D' →
      SubJ (.cls "Array") τw →
      KontOkJ ans A D' h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γ' := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ ans A D h ((c, Γ) :: Γs) τ (.arrK acc rest :: k)
  /-- The in-flight value is the condition; either branch may run next, judged at
      this constructor's own environment (the condition's exit), below the chosen
      join `τj` with the chosen continuation environment `Γc` — `Judge.ifElse`'s
      premises carried onto the continuation. -/
  | ifElseK {D Dt h c Γ Γs τ t els τt Γt τe Γe τj Γc τw k Γk} :
      fragHead t = true → fragHead els = true →
      MFrag A t → MFrag A els →
      Judge A D Γ t Γs.isEmpty c τt Γt Dt →
      Judge A D Γ els Γs.isEmpty c τe Γe Dt →
      SubJ τt τj → SubJ τe τj →
      SubEnv Γc Γt → SubEnv Γc Γe →
      SubJ τj τw →
      KontOkJ ans A Dt h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γc := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ ans A D h ((c, Γ) :: Γs) τ (.ifK t (some els) :: k)
  /-- The elseless `if`: a falsy condition delivers `nil`, so `nil` sits below the
      join (`Judge.ifNone`'s premise). -/
  | ifNoneK {D h c Γ Γs τ t τt Γt τj Γc τw k Γk} :
      fragHead t = true →
      MFrag A t →
      Judge A D Γ t Γs.isEmpty c τt Γt D →
      SubJ τt τj → SubJ .nilT τj →
      SubEnv Γc Γt → SubEnv Γc Γ →
      SubJ τj τw →
      KontOkJ ans A D h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γc := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ ans A D h ((c, Γ) :: Γs) τ (.ifK t none :: k)
  /-- **The narrowing `if`** (J27): the condition was a bare read of `x : τ₀`, and
      the machine's own truthiness test is the narrowing evidence. The conclusion's
      environment binds `x` at the *stored value's atom* `a` (chosen at the push by
      `vty_narrow_kit`), the in-flight index is that same atom, and the three
      `SubJ` premises are exactly what each delivery direction spends: `hT` for the
      then-branch (or `a = nilT`, whose values are `nil` and refute truthiness),
      `hFn`/`hFf` for the two falsy shapes. No value↔store correlation is carried —
      the atom's sharpness *is* the correlation, established once at the push. -/
  | ifNarrowElseK {D Dt h c Γb x τ₀ a t els τt Γt τe Γe τj Γc τw k Γk} :
      fragHead t = true → fragHead els = true →
      MFrag A t → MFrag A els →
      envGet? Γb x = some τ₀ →
      Judge A D (envSet Γb x (dropNil τ₀)) t Γs.isEmpty c τt Γt Dt →
      Judge A D (envSet Γb x (elseNarrow τ₀)) els Γs.isEmpty c τe Γe Dt →
      SubJ τt τj → SubJ τe τj →
      SubEnv Γc Γt → SubEnv Γc Γe →
      SubJ a τ₀ →
      (a = .nilT ∨ SubJ a (dropNil τ₀)) →
      (SubJ .nilT a → SubJ a (elseNarrow τ₀)) →
      (SubJ .bool a → SubJ a (elseNarrow τ₀)) →
      SubJ τj τw →
      KontOkJ ans A Dt h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γc := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ ans A D h ((c, envSet Γb x a) :: Γs) a (.ifK t (some els) :: k)
  | ifNarrowNoneK {D h c Γb x τ₀ a t τt Γt τj Γc τw k Γk} :
      fragHead t = true →
      MFrag A t →
      envGet? Γb x = some τ₀ →
      Judge A D (envSet Γb x (dropNil τ₀)) t Γs.isEmpty c τt Γt D →
      SubJ τt τj → SubJ .nilT τj →
      SubEnv Γc Γt → SubEnv Γc Γb →
      SubJ a τ₀ →
      (a = .nilT ∨ SubJ a (dropNil τ₀)) →
      SubJ τj τw →
      KontOkJ ans A D h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γc := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ ans A D h ((c, envSet Γb x a) :: Γs) a (.ifK t none :: k)
  /-- The loop konts: condition in flight (`whileCond`) or body's value in flight
      (`whileBody`); the loop's own answer is `nil`, delivered to the enclosing
      continuation. The environment index is the loop head `Γl`, which every
      subcomputation exit re-guarantees (`LoopOkJ`). -/
  | whileCond {D h ctx Γl Γs τ τw c body k Γk} :
      LoopOkJ A D Γl c body Γs.isEmpty (loopCtx ctx Γl) →
      SubJ .nilT τw →
      KontOkJ ans A D h ((ctx, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γl := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ ans A D h ((loopCtx ctx Γl, Γl) :: Γs) τ (.whileCondK c body :: k)
  | whileBody {D h ctx Γl Γs τ τw c body k Γk} :
      LoopOkJ A D Γl c body Γs.isEmpty (loopCtx ctx Γl) →
      SubJ .nilT τw →
      KontOkJ ans A D h ((ctx, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γl := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ ans A D h ((loopCtx ctx Γl, Γl) :: Γs) τ (.whileBodyK c body :: k)
  /-- The in-flight value is the **receiver** of an argument-bearing send; the
      first argument runs next. -/
  | recvK {D D₂ h c Γ Γs τ mname arg args τs ps τret τw Γ₂ k Γk} {site : SendSite} :
      (∀ a ∈ arg :: args, fragHead a = true) →
      (∀ a ∈ arg :: args, MFrag A a) →
      JudgeArgs A D Γ (arg :: args) Γs.isEmpty c τs Γ₂ D₂ →
      sigOf D₂ τ mname = some (ps, τret) →
      SubJs τs ps →
      SubJ τret τw →
      KontOkJ ans A D₂ h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γ₂ := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ ans A D h ((c, Γ) :: Γs) τ (.recvK mname (arg :: args) .none site :: k)
  /-- A zero-argument send: the dispatch happens at the delivery itself, so the
      continuation is already at the return type. -/
  | recvK0 {D h c Γ Γs τ mname τret τw k Γk} {site : SendSite} :
      sigOf D τ mname = some ([], τret) →
      SubJ τret τw →
      KontOkJ ans A D h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γ := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ ans A D h ((c, Γ) :: Γs) τ (.recvK mname [] .none site :: k)
  /-- The in-flight value is an **argument**; the receiver and the evaluated prefix
      ride the kont as values, so their types are `VTy` facts against the heap —
      the constructor `heap_congr'` gains content at. -/
  | argsK {D D' h c Γ Γs τ mname recv τr psacc τp τrest psrest τret τw acc rest Γ' k Γk}
      {site : SendSite} :
      VTy h recv τr →
      VTys h acc psacc →
      SubJ τ τp →
      (∀ a ∈ rest, fragHead a = true) →
      (∀ a ∈ rest, MFrag A a) →
      JudgeArgs A D Γ rest Γs.isEmpty c τrest Γ' D' →
      SubJs τrest psrest →
      sigOf D' τr mname = some (psacc ++ τp :: psrest, τret) →
      SubJ τret τw →
      KontOkJ ans A D' h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γ' := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ ans A D h ((c, Γ) :: Γs) τ (.argsK recv site mname acc rest .none :: k)
  /-- The hash literal's **key** in flight (J40): the pending value expression
      and remaining pairs ride as program, the answer is `.any` (the rule's own
      conclusion — a hash value inhabits no narrower type), and the accumulator
      is erased exactly as `arrK`'s is. -/
  | hshKeyK {D D₂ D' h c Γ Γs τ vE rest τv Γ₂ Γ' τw acc k Γk} :
      fragHead vE = true → MFrag A vE →
      (∀ p ∈ rest, fragHead (Prod.fst p) = true ∧ fragHead (Prod.snd p) = true) →
      (∀ p ∈ rest, MFrag A (Prod.fst p)) →
      (∀ p ∈ rest, MFrag A (Prod.snd p)) →
      Judge A D Γ vE Γs.isEmpty c τv Γ₂ D₂ →
      JudgePairs A D₂ Γ₂ rest Γs.isEmpty c Γ' D' →
      SubJ .any τw →
      KontOkJ ans A D' h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γ' := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ ans A D h ((c, Γ) :: Γs) τ (.hshKeyK acc vE rest :: k)
  /-- The hash literal's **value** in flight (J40). -/
  | hshValK {D D' h c Γ Γs τ rest Γ' τw acc key k Γk} :
      (∀ p ∈ rest, fragHead (Prod.fst p) = true ∧ fragHead (Prod.snd p) = true) →
      (∀ p ∈ rest, MFrag A (Prod.fst p)) →
      (∀ p ∈ rest, MFrag A (Prod.snd p)) →
      JudgePairs A D Γ rest Γs.isEmpty c Γ' D' →
      SubJ .any τw →
      KontOkJ ans A D' h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γ' := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ ans A D h ((c, Γ) :: Γs) τ (.hshValK acc key rest :: k)
  /-- **A toplevel constant write's value in flight** (J41). The three freshness
      guards ride the kont (read at the delivery by the `constSetIn` transports),
      and the environment stack is pinned to the singleton — the write lands on
      the bottom frame's definee, which `BottomObj` says is `Object`. -/
  | casgnK {D h c Γ τ τw nm k Γk} :
      constTy? D nm = none →
      (∀ cn, scopedConstTy? D cn nm = none) →
      readableClasses.contains nm = false →
      (∀ pr ∈ D.modules, pr.2 ≠ nm) →
      (∀ pr ∈ D.classes, pr.2 ≠ nm) →
      ':' ∉ nm.data → nm ∉ bootConstNames →
      SubJ τ τw →
      KontOkJ ans A D h [(c, Γk)] τw k →
      (hsu : SubEnv Γk Γ := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ ans A D h [(c, Γ)] τ (.casgnK nm :: k)
  /-- **J49: the module-body constant write, in flight.** `casgnK`'s guards at
      the module-body position (J34/J44c supply the definee's identity at the
      delivery); the ret/meth pins close the jump channels. -/
  | casgnMK {D h c Γ Γs τ τw nm k Γk} :
      c.inClassBody = true → c.inModuleBody = true → c.inBlock = false →
      c.ret = none → c.meth = none →
      constTy? D nm = none →
      (∀ cn, scopedConstTy? D cn nm = none) →
      readableClasses.contains nm = false →
      (∀ pr ∈ D.modules, pr.2 ≠ nm) →
      (∀ pr ∈ D.classes, pr.2 ≠ nm) →
      ':' ∉ nm.data → nm ∉ bootConstNames →
      SubJ τ τw →
      KontOkJ ans A D h ((c, Γk) :: Γs) τw k →
      (hsu : SubEnv Γk Γ := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ ans A D h ((c, Γ) :: Γs) τ (.casgnK nm :: k)
  /-- **`return e`'s value in flight** (J39, mirroring L200's `KontOk.retValK`):
      the delivery is `doReturn`, so the constructor carries what that needs —
      the open return channel below the in-flight type, plus the method channel
      (`judge_table_ret`'s second hypothesis). The tail is at an *unrelated* type
      `τ'`: nothing about the popped-to continuation is knowable here; the
      `RetOkJ` derived at the delivery is what lands the value. -/
  | retValK {D h c Γ Γs τ τ' σ k Γk} :
      c.ret = some σ → c.meth.isSome = true → SubJ τ σ →
      KontOkJ ans A D h ((c, Γk) :: Γs) τ' k →
      (hsu : SubEnv Γk Γ := by first | exact SubEnv.refl _ | assumption) →
      KontOkJ ans A D h ((c, Γ) :: Γs) τ (.jumpValK .retK :: k)
  /-- **Method return** — the callee's declared return type is what the caller's
      continuation expects; the two-deep stack is what makes the pop total. -/
  | frameK {D h cΓ cΓ' Γs τ fid k} :
      (∀ σ, cΓ.1.ret = some σ → SubJ σ τ) →
      cΓ.1.inLoop = none →
      KontOkJ ans A D h (cΓ' :: Γs) τ k → KontOkJ ans A D h (cΓ :: cΓ' :: Γs) τ (.frameK fid :: k)

/-- Transport of the continuation judgment across a heap the step grew — no rung-1
    constructor stores a `VTy` fact, so this is currently structural; the `argsK`
    rung is where it gains content (as `KontOk.heap_congr'` did at L137). -/
theorem KontOkJ.heap_congr' {ans : Ty} {A : SemAxioms} {h' : Heap} :
    ∀ {D : Decls} {h : Heap} {Γs : List (JCtx × Env)} {τ : Ty} {k : List Kont},
      KontOkJ ans A D h Γs τ k → TypeAgree h h' → KontOkJ ans A D h' Γs τ k := by
  intro D h Γs τ k hk
  induction hk with
  | nil hsub hr hl => intro _; exact .nil hsub hr hl
  | seqNil hw _ hsu ih => intro ha; exact .seqNil hw (ih ha) hsu
  | seqCons hm hs hw _ hsu ih => intro ha; exact .seqCons hm hs hw (ih ha) hsu
  | asgn hib hw _ hsu ih => intro ha; exact .asgn hib hw (ih ha) hsu
  | cpathK hb hsco hsw _ hsu ih => intro ha; exact .cpathK hb hsco hsw (ih ha) hsu
  | retValK hσ hms hsub _ hsu ih => intro ha; exact .retValK hσ hms hsub (ih ha) hsu
  | casgnK hct hsct hrd hmods hclss hnc hbn hsub _ hsu ih =>
      intro ha; exact .casgnK hct hsct hrd hmods hclss hnc hbn hsub (ih ha) hsu
  | casgnMK hicb himb hnbk hret hmeth hct hsct hrd hmods hclss hnc hbn hsub _ hsu ih =>
      intro ha
      exact .casgnMK hicb himb hnbk hret hmeth hct hsct hrd hmods hclss hnc hbn hsub (ih ha) hsu
  | hshKeyK hfv hmv hfp hmk hmvs hjv hpr hw _ hsu ih =>
      intro ha; exact .hshKeyK hfv hmv hfp hmk hmvs hjv hpr hw (ih ha) hsu
  | hshValK hfp hmk hmvs hpr hw _ hsu ih =>
      intro ha; exact .hshValK hfp hmk hmvs hpr hw (ih ha) hsu
  | ifElseK hft hfe hmt hme ht he hjt hje hct hce hw _ hsu ih =>
      intro ha; exact .ifElseK hft hfe hmt hme ht he hjt hje hct hce hw (ih ha) hsu
  | ifNoneK hft hmt ht hjt hjn hct hce hw _ hsu ih =>
      intro ha; exact .ifNoneK hft hmt ht hjt hjn hct hce hw (ih ha) hsu
  | whileCond hl hw _ hsu ih => intro ha; exact .whileCond hl hw (ih ha) hsu
  | whileBody hl hw _ hsu ih => intro ha; exact .whileBody hl hw (ih ha) hsu
  | recvK hfm hm hargs hsg hsub hw _ hsu ih =>
      intro ha; exact .recvK hfm hm hargs hsg hsub hw (ih ha) hsu
  | recvK0 hsg hw _ hsu ih => intro ha; exact .recvK0 hsg hw (ih ha) hsu
  | argsK hrv hva hst hfm hm hrest hsr hsg hw _ hsu ih =>
      intro ha
      exact .argsK (hrv.congr ha) (VTys.congr ha hva) hst hfm hm hrest hsr hsg hw (ih ha) hsu
  | frameK hrt hil _ ih => intro ha; exact .frameK hrt hil (ih ha)
  | asgnIvar hsc hw hcf _ hsu ih => intro ha; exact .asgnIvar hsc hw hcf (ih ha) hsu
  | asgnGvar hpg hgt hcf hw _ hsu ih =>
      intro ha; exact .asgnGvar hpg hgt hcf hw (ih ha) hsu
  | arrK hfm hm hje hw _ hsu ih => intro ha; exact .arrK hfm hm hje hw (ih ha) hsu
  | ifNarrowElseK hft hfe hmt hme hget ht he hjt hje2 hct hce hs0 hT hFn hFf hjw _ hsu ih =>
      intro ha
      exact .ifNarrowElseK hft hfe hmt hme hget ht he hjt hje2 hct hce hs0 hT hFn hFf hjw
        (ih ha) hsu
  | ifNarrowNoneK hft hmt hget ht hjt hjn hct hcb hs0 hT hjw _ hsu ih =>
      intro ha
      exact .ifNarrowNoneK hft hmt hget ht hjt hjn hct hcb hs0 hT hjw (ih ha) hsu

theorem KontOkJ.heap_congr {ans : Ty} {A : SemAxioms} {h h' : Heap} (ha : TypeAgree h h')
    {D : Decls} {Γs : List (JCtx × Env)} {τ : Ty} {k : List Kont}
    (hk : KontOkJ ans A D h Γs τ k) : KontOkJ ans A D h' Γs τ k :=
  KontOkJ.heap_congr' hk ha

/-- **A `.retJ` in flight is well-typed for where it will land** (J39, mirroring
    L200's `RetOk`): every kont above the innermost `frameK` is transparent to a
    `.retJ`, and that `frameK` resumes a caller whose continuation accepts the
    value's type. Indexed by the **callers'** stack — the head activation is what
    the jump is leaving. -/
inductive RetOkJ (ans : Ty) (A : SemAxioms) :
    Decls → Heap → List (JCtx × Env) → Ty → List Kont → Prop where
  | here {D h Γs σ τ fid k} :
      SubJ σ τ → KontOkJ ans A D h Γs τ k → RetOkJ ans A D h Γs σ (.frameK fid :: k)
  | skip {D h Γs σ κ k} :
      RetTransparent κ → RetOkJ ans A D h Γs σ k → RetOkJ ans A D h Γs σ (κ :: k)

/-- `KontOk.retOk` over the judgment (J39): a continuation whose head context has
    the return **and** method channels open unwinds to a `RetOkJ`. Table-threading
    konts hold the table still by `judge_*_table_ret` — the J-side twin of L200's
    `infer_table_ret` composition. -/
theorem KontOkJ.retOkJ {ans : Ty} {A : SemAxioms} :
    ∀ {k : List Kont} {D : Decls} {h : Heap} {c : JCtx} {Γ : Env}
    {Γs : List (JCtx × Env)} {τ : Ty}, KontOkJ ans A D h ((c, Γ) :: Γs) τ k →
    Γs ≠ [] → ∀ σ, c.ret = some σ → c.meth.isSome = true →
    RetOkJ ans A D h Γs σ k
  | [], _, _, c, Γ, Γs, _, hk, _, σ, hσ, _ => by
      cases hk with
      | nil _ hr _ => exact absurd (hr (c, Γ) Γs rfl) (by rw [hσ]; simp)
  | κ :: k, D, h, c, Γ, Γs, τ, hk, hne, σ, hσ, hms => by
      have htop : Γs.isEmpty = false := by simpa using hne
      cases hk with
      | seqNil hw hk' hsu => exact RetOkJ.skip trivial (KontOkJ.retOkJ hk' hne σ hσ hms)
      | seqCons hm hseq hw hk' hsu =>
          have hq : _ = D := judge_seq_table_ret hseq (by rw [hσ]; simp) hms htop
          subst hq
          exact RetOkJ.skip trivial (KontOkJ.retOkJ hk' hne σ hσ hms)
      | asgn hib hw hk' hsu => exact RetOkJ.skip trivial (KontOkJ.retOkJ hk' hne σ hσ hms)
      | asgnIvar hsc hw hcf hk' hsu =>
          exact RetOkJ.skip trivial (KontOkJ.retOkJ hk' hne σ hσ hms)
      | asgnGvar hpg hgt hcf hw hk' hsu =>
          exact RetOkJ.skip trivial (KontOkJ.retOkJ hk' hne σ hσ hms)
      | cpathK hb hsco hw hk' hsu =>
          exact RetOkJ.skip trivial (KontOkJ.retOkJ hk' hne σ hσ hms)
      | retValK hσ' hms' hsub hk' hsu =>
          exact RetOkJ.skip trivial (KontOkJ.retOkJ hk' hne σ hσ hms)
      | arrK hfm hm helems hje hk' hsu =>
          have hq : _ = D := judge_elems_table_ret helems (by rw [hσ]; simp) hms htop
          subst hq
          exact RetOkJ.skip trivial (KontOkJ.retOkJ hk' hne σ hσ hms)
      | ifElseK hft hfe hmt hme ht he hjt hje hct hce hw hk' hsu =>
          have hq : _ = D := judge_table_ret ht (by rw [hσ]; simp) hms htop
          subst hq
          exact RetOkJ.skip trivial (KontOkJ.retOkJ hk' hne σ hσ hms)
      | ifNoneK hft hmt ht hjt hjn hct hce hw hk' hsu =>
          exact RetOkJ.skip trivial (KontOkJ.retOkJ hk' hne σ hσ hms)
      | ifNarrowElseK hft hfe hmt hme hget ht he hjt hje2 hct hce hs0 hT hFn hFf hjw hk' hsu =>
          have hq : _ = D := judge_table_ret ht (by rw [hσ]; simp) hms htop
          subst hq
          exact RetOkJ.skip trivial (KontOkJ.retOkJ hk' hne σ hσ hms)
      | ifNarrowNoneK hft hmt hget ht hjt hjn hct hcb hs0 hT hjw hk' hsu =>
          exact RetOkJ.skip trivial (KontOkJ.retOkJ hk' hne σ hσ hms)
      | whileCond hl hw hk' hsu =>
          exact RetOkJ.skip trivial
            (KontOkJ.retOkJ hk' hne σ (by simpa [loopCtx] using hσ)
              (by simpa [loopCtx] using hms))
      | whileBody hl hw hk' hsu =>
          exact RetOkJ.skip trivial
            (KontOkJ.retOkJ hk' hne σ (by simpa [loopCtx] using hσ)
              (by simpa [loopCtx] using hms))
      | recvK hfm hm hargs hsg hsub hw hk' hsu =>
          have hq : _ = D := judge_args_table_ret hargs (by rw [hσ]; simp) hms htop
          subst hq
          exact RetOkJ.skip trivial (KontOkJ.retOkJ hk' hne σ hσ hms)
      | recvK0 hsg hw hk' hsu => exact RetOkJ.skip trivial (KontOkJ.retOkJ hk' hne σ hσ hms)
      | argsK hrv hva hst hfm hm hrest hsr hsg hw hk' hsu =>
          have hq : _ = D := judge_args_table_ret hrest (by rw [hσ]; simp) hms htop
          subst hq
          exact RetOkJ.skip trivial (KontOkJ.retOkJ hk' hne σ hσ hms)
      | hshKeyK hfv hmv hfp hmk hmvs hjv hpr hw hk' hsu =>
          have hq := (judge_pairs_table_ret hpr (by rw [hσ]; simp) hms htop).trans
            (judge_table_ret hjv (by rw [hσ]; simp) hms htop)
          exact RetOkJ.skip trivial (KontOkJ.retOkJ (hq ▸ hk') hne σ hσ hms)
      | hshValK hfp hmk hmvs hpr hw hk' hsu =>
          have hq : _ = D := judge_pairs_table_ret hpr (by rw [hσ]; simp) hms htop
          subst hq
          exact RetOkJ.skip trivial (KontOkJ.retOkJ hk' hne σ hσ hms)
      | casgnK hct hsct hrd hmods hclss hnc hbn hsub hk' hsu => exact absurd rfl hne
      | casgnMK hicb himb hnbk hret hmeth hct hsct hrd hmods hclss hnc hbn hsub hk' hsu =>
          exact absurd hσ (by rw [hret]; simp)
      | frameK hrt hil hk' => exact RetOkJ.here (hrt σ hσ) hk'

/-- `firstFrameK_of_retOk`, J-flavored: along a chain that carries a `.retJ`, the
    first popping kont is the `frameK` the jump lands at. -/
theorem firstFrameK_of_retOkJ {ans : Ty} {A : SemAxioms} {D : Decls} {h : Heap}
    {Γs : List (JCtx × Env)} {σ : Ty} :
    ∀ {k : List Kont}, RetOkJ ans A D h Γs σ k → ∀ {fid rest},
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

/-- The control clause over the judgment (`CtlOk`, Proof/Static/Konts.lean:925).
    The eval arm adds the fragment gate; the jump arms are `False` until the rungs
    that produce jumps (`return`/`next`/`raise`) enter the fragment. `ans` (J29) is
    the answer type the continuation's spine bottoms out at. -/
def CtlOkJ (D : Decls) (c : JCtx) (Γ : Env) (Γs : List (JCtx × Env))
    (ans : Ty) (A : SemAxioms) (m : Machine) : Prop :=
  match m.ctl with
  | .eval e =>
    -- **J31: two modes.** The syntactic mode is the pre-J31 clause plus the
    -- `fragHead` routing bit; the semantic mode holds a claimed expression at the
    -- canonical judgment — no derivation, the continuation expecting (at least)
    -- `.any` at the current environment. `step_okJ`'s eval branch dispatches on
    -- the disjunction: syntactic → `judge_eval_ok`, semantic → the claim's
    -- `SemAxiomsOk` obligation, applied.
    (fragHead e = true ∧ MFrag A e ∧
      ∃ τ τ' Γ' D' Γk, Judge A D Γ e Γs.isEmpty c τ Γ' D' ∧ SubJ τ τ' ∧
        SubEnv Γk Γ' ∧ KontOkJ ans A D' m.heap ((c, Γk) :: Γs) τ' m.kont)
    ∨ (∃ cl ∈ A, cl.e = e ∧ fragHead e = false ∧
        (cl.rows = [] ∧ cl.freshNames = [] ∨ c.meth = none) ∧
        (∀ cn, cl.reqCls = some cn →
          c.cls = cn ∧ c.inClassBody = true ∧ c.inBlock = false) ∧
        cl.reqModOk c ∧
        (∀ r ∈ cl.rows, declaresName D r.2.1 = false) ∧
        (∀ n ∈ cl.freshNames, declaresName D n = false) ∧
        ∃ τ' Γk, SubJ cl.τ τ' ∧ SubEnv Γk Γ ∧
          KontOkJ ans A (addRows D cl.rows) m.heap ((c, Γk) :: Γs) τ' m.kont)
  | .value v => ∃ τ Γk, VTy m.heap v τ ∧ SubEnv Γk Γ ∧
      KontOkJ ans A D m.heap ((c, Γk) :: Γs) τ m.kont
  -- **A `return` in flight** (J39, mirroring L200's arm): the value's type, the
  -- transparent unwinding (`RetOkJ`), and the jump's target — the innermost
  -- `frameK`'s label, which L199's clause pins to the stack's head.
  | .jump (.retJ v target) =>
    ∃ σ, VTy m.heap v σ ∧ RetOkJ ans A D m.heap Γs σ m.kont ∧
      firstFrameK m.kont = some target
  | .jump _ => False

/-- The `JCtx`-shaped context stack, projected for `StackCtx`. -/
def jctxs (c : JCtx) (Γs : List (JCtx × Env)) : List FrameCtx :=
  (c :: Γs.map Prod.fst).map JCtx.toFrameCtx

/-- **The invariant** handed to `invariant_sound_from` — `Inv` (Proof/Static/
    Konts.lean:1346) with the typed existential in the judgment vocabulary.

    **J29:** the invariant is now a *family* indexed by the answer type `ans` —
    the type the whole run's continuation discipline promises the final value
    below. `ans` is a parameter rather than a member of the existential tuple
    precisely so it survives to the `done` step: existentials are re-chosen at
    every consecution, and an existential answer type is what made the pre-J29
    invariant forget the judged type (any value re-closes `KontOkJ.nil` at its
    own type). Safety-only clients instantiate `ans := .any`. -/
def InvJ (ans : Ty) (A : SemAxioms) (m : Machine) : Prop :=
  NoHook m.heap ∧ Saturated m.heap ∧ ChainsIn m.heap ∧ LitClsOk m.heap ∧
    ClassOk m.heap ∧ BottomObj m.frames m.stack ∧
    framePopLabels m.kont = m.stack.dropLast ∧
    ClosuresOk m ∧
    ∃ (F : Decls) (c : JCtx) (Γ : Env) (Γs : List (JCtx × Env)),
      DeclsOkJ A F m.heap ∧
      FramesOkJ m.heap m.frames m.stack (Γ :: Γs.map Prod.snd) ∧
      StackCtx m.heap m.frames m.stack (jctxs c Γs) ∧
      GlobalsOk F m.heap m.globals ∧
      CtlOkJ F c Γ Γs ans A m

/-! ## The five re-establishment helpers (Proof/Static/Konts.lean:1969–2245) -/

theorem inv_evalJ {ans : Ty} {A : SemAxioms} {F : Decls} {m : Machine} {c : JCtx} {Γ : Env}
    {Γs : List (JCtx × Env)} {Γk : Env} {e : Expr} {τ τ' : Ty} {Γ' : Env} {F' : Decls}
    (hfs : FramesOkJ m.heap m.frames m.stack (Γ :: Γs.map Prod.snd))
    (ht : DeclsOkJ A F m.heap)
    (hsc : StackCtx m.heap m.frames m.stack (jctxs c Γs))
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : LitClsOk m.heap)
    (hcls : ClassOk m.heap) (hbot : BottomObj m.frames m.stack)
    (hchn : ChainsIn m.heap := by assumption)
    (hks : framePopLabels m.kont = m.stack.dropLast)
    (hmf : MFrag A e)
    (hfh : fragHead e = true)
    (hj : Judge A F Γ e Γs.isEmpty c τ Γ' F')
    (hsub : SubJ τ τ')
    (hk : KontOkJ ans A F' m.heap ((c, Γk) :: Γs) τ' m.kont)
    (hgl : GlobalsOk F m.heap m.globals := by assumption)
    (hsuE : SubEnv Γk Γ' := by first | exact SubEnv.refl _ | assumption)
    (hclo : ClosuresOk m := by assumption) :
    InvJ ans A (withCtl m (.eval e)) :=
  ⟨hh, hsat, hchn, hstr, hcls, hbot, hks, hclo.ctl, F, c, Γ, Γs, ht, hfs, hsc, hgl,
   Or.inl ⟨hfh, hmf, τ, τ', Γ', F', Γk, hj, hsub, hsuE, hk⟩⟩

theorem inv_valueJ {ans : Ty} {A : SemAxioms} {F : Decls} {m : Machine} {c : JCtx} {Γ : Env}
    {Γs : List (JCtx × Env)} {Γk : Env} {v : Value} {τ : Ty}
    (hfs : FramesOkJ m.heap m.frames m.stack (Γ :: Γs.map Prod.snd))
    (ht : DeclsOkJ A F m.heap)
    (hsc : StackCtx m.heap m.frames m.stack (jctxs c Γs))
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : LitClsOk m.heap)
    (hcls : ClassOk m.heap) (hbot : BottomObj m.frames m.stack)
    (hchn : ChainsIn m.heap := by assumption)
    (hks : framePopLabels m.kont = m.stack.dropLast)
    (hv : VTy m.heap v τ) (hk : KontOkJ ans A F m.heap ((c, Γk) :: Γs) τ m.kont)
    (hgl : GlobalsOk F m.heap m.globals := by assumption)
    (hsuE : SubEnv Γk Γ := by first | exact SubEnv.refl _ | assumption)
    (hclo : ClosuresOk m := by assumption) :
    InvJ ans A (withCtl m (.value v)) :=
  ⟨hh, hsat, hchn, hstr, hcls, hbot, hks, hclo.ctl, F, c, Γ, Γs, ht, hfs, hsc, hgl,
   ⟨τ, Γk, hv, hsuE, hk⟩⟩

theorem inv_pushJ {ans : Ty} {A : SemAxioms} {F : Decls} {m : Machine} {c : JCtx} {Γ : Env}
    {Γs : List (JCtx × Env)} {Γk : Env} {e : Expr} {τ τ' : Ty} {Γ' : Env} {F' : Decls}
    {k : Kont}
    (hfs : FramesOkJ m.heap m.frames m.stack (Γ :: Γs.map Prod.snd))
    (ht : DeclsOkJ A F m.heap)
    (hsc : StackCtx m.heap m.frames m.stack (jctxs c Γs))
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : LitClsOk m.heap)
    (hcls : ClassOk m.heap) (hbot : BottomObj m.frames m.stack)
    (hchn : ChainsIn m.heap := by assumption)
    (hks : framePopLabels (k :: m.kont) = m.stack.dropLast)
    (hmf : MFrag A e)
    (hfh : fragHead e = true)
    (hj : Judge A F Γ e Γs.isEmpty c τ Γ' F')
    (hsub : SubJ τ τ')
    (hk : KontOkJ ans A F' m.heap ((c, Γk) :: Γs) τ' (k :: m.kont))
    (hgl : GlobalsOk F m.heap m.globals := by assumption)
    (hsuE : SubEnv Γk Γ' := by first | exact SubEnv.refl _ | assumption)
    (hkc : KontClosure k = none := by simp [KontClosure])
    (hclo : ClosuresOk m := by assumption) :
    InvJ ans A (withKont m (.eval e) k) :=
  ⟨hh, hsat, hchn, hstr, hcls, hbot, hks, hclo.cons hkc, F, c, Γ, Γs, ht, hfs, hsc, hgl,
   Or.inl ⟨hfh, hmf, τ, τ', Γ', F', Γk, hj, hsub, hsuE, hk⟩⟩

/-- **Semantic-mode re-establishment (J31)** — the eval arm's `Or.inr`, for a
    claimed expression becoming `ctl` with the current continuation. -/
theorem inv_evalSemJ {ans : Ty} {A : SemAxioms} {F : Decls} {m : Machine} {c : JCtx}
    {Γ : Env} {Γs : List (JCtx × Env)} {Γk : Env} {e : Expr} {τ' : Ty}
    (hfs : FramesOkJ m.heap m.frames m.stack (Γ :: Γs.map Prod.snd))
    (ht : DeclsOkJ A F m.heap)
    (hsc : StackCtx m.heap m.frames m.stack (jctxs c Γs))
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : LitClsOk m.heap)
    (hcls : ClassOk m.heap) (hbot : BottomObj m.frames m.stack)
    (hchn : ChainsIn m.heap := by assumption)
    (hks : framePopLabels m.kont = m.stack.dropLast)
    {cl : SemClaim}
    (hmem : cl ∈ A) (hcle : cl.e = e) (hfh : fragHead e = false)
    (hdisc : cl.rows = [] ∧ cl.freshNames = [] ∨ c.meth = none)
    (hreq : ∀ cn, cl.reqCls = some cn →
      c.cls = cn ∧ c.inClassBody = true ∧ c.inBlock = false)
    (hqm : cl.reqModOk c)
    (hfr : ∀ r ∈ cl.rows, declaresName F r.2.1 = false)
    (hfn : ∀ n ∈ cl.freshNames, declaresName F n = false)
    (hs' : SubJ cl.τ τ')
    (hk : KontOkJ ans A (addRows F cl.rows) m.heap ((c, Γk) :: Γs) τ' m.kont)
    (hgl : GlobalsOk F m.heap m.globals := by assumption)
    (hsuE : SubEnv Γk Γ := by first | exact SubEnv.refl _ | assumption)
    (hclo : ClosuresOk m := by assumption) :
    InvJ ans A (withCtl m (.eval e)) :=
  ⟨hh, hsat, hchn, hstr, hcls, hbot, hks, hclo.ctl, F, c, Γ, Γs, ht, hfs, hsc, hgl,
   Or.inr ⟨cl, hmem, hcle, hfh, hdisc, hreq, hqm, hfr, hfn, τ', Γk, hs', hsuE, hk⟩⟩

/-- Semantic-mode push: a claimed expression becoming `ctl` under a freshly pushed
    continuation frame. -/
theorem inv_pushSemJ {ans : Ty} {A : SemAxioms} {F : Decls} {m : Machine} {c : JCtx}
    {Γ : Env} {Γs : List (JCtx × Env)} {Γk : Env} {e : Expr} {τ' : Ty} {k : Kont}
    (hfs : FramesOkJ m.heap m.frames m.stack (Γ :: Γs.map Prod.snd))
    (ht : DeclsOkJ A F m.heap)
    (hsc : StackCtx m.heap m.frames m.stack (jctxs c Γs))
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : LitClsOk m.heap)
    (hcls : ClassOk m.heap) (hbot : BottomObj m.frames m.stack)
    (hchn : ChainsIn m.heap := by assumption)
    (hks : framePopLabels (k :: m.kont) = m.stack.dropLast)
    {cl : SemClaim}
    (hmem : cl ∈ A) (hcle : cl.e = e) (hfh : fragHead e = false)
    (hdisc : cl.rows = [] ∧ cl.freshNames = [] ∨ c.meth = none)
    (hreq : ∀ cn, cl.reqCls = some cn →
      c.cls = cn ∧ c.inClassBody = true ∧ c.inBlock = false)
    (hqm : cl.reqModOk c)
    (hfr : ∀ r ∈ cl.rows, declaresName F r.2.1 = false)
    (hfn : ∀ n ∈ cl.freshNames, declaresName F n = false)
    (hs' : SubJ cl.τ τ')
    (hk : KontOkJ ans A (addRows F cl.rows) m.heap ((c, Γk) :: Γs) τ' (k :: m.kont))
    (hgl : GlobalsOk F m.heap m.globals := by assumption)
    (hsuE : SubEnv Γk Γ := by first | exact SubEnv.refl _ | assumption)
    (hkc : KontClosure k = none := by simp [KontClosure])
    (hclo : ClosuresOk m := by assumption) :
    InvJ ans A (withKont m (.eval e) k) :=
  ⟨hh, hsat, hchn, hstr, hcls, hbot, hks, hclo.cons hkc, F, c, Γ, Γs, ht, hfs, hsc, hgl,
   Or.inr ⟨cl, hmem, hcle, hfh, hdisc, hreq, hqm, hfr, hfn, τ', Γk, hs', hsuE, hk⟩⟩

theorem inv_grow_valueJ {ans : Ty} {A : SemAxioms} {F : Decls} {m m' : Machine} {c : JCtx} {Γ : Env}
    {Γs : List (JCtx × Env)} {Γk : Env} {v : Value} {τ : Ty}
    (hfs : FramesOkJ m.heap m.frames m.stack (Γ :: Γs.map Prod.snd))
    (ht : DeclsOkJ A F m.heap)
    (hsc : StackCtx m.heap m.frames m.stack (jctxs c Γs))
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : LitClsOk m.heap)
    (hcls : ClassOk m.heap) (hbot : BottomObj m.frames m.stack)
    (hchn : ChainsIn m.heap := by assumption)
    (hks : framePopLabels m.kont = m.stack.dropLast)
    (hg : PlainGrow m.heap m'.heap)
    (hfr : m'.frames = m.frames) (hst : m'.stack = m.stack) (hko : m'.kont = m.kont)
    (hv : VTy m'.heap v τ) (hk : KontOkJ ans A F m.heap ((c, Γk) :: Γs) τ m.kont)
    -- J43: `PlainGrow` cannot say the fresh object's fields are bounded, so the
    -- grown heap's `ChainsIn` arrives from the call site (`chainsIn_alloc`).
    (hchn' : ChainsIn m'.heap := by assumption)
    (hgl : GlobalsOk F m.heap m.globals := by assumption)
    (hgv : m'.globals = m.globals := by rfl)
    (hsuE : SubEnv Γk Γ := by first | exact SubEnv.refl _ | assumption)
    (hclo : ClosuresOk m := by assumption) :
    InvJ ans A (withCtl m' (.value v)) := by
  have hag : TypeAgree m.heap m'.heap := typeAgree_of_plainGrow hg hsat
  refine ⟨NoHook_grow hg hsat hh,
    Saturated_grow hg.shapeAgree hg.size hsat, hchn', LitClsOk_grow hg hstr,
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
    F, c, Γ, Γs, DeclsOkJ_grow hg hsat hchn.boot.2.2.2.2 ht, ?_, ?_, ?_, ?_⟩
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
        KontOkJ ans A F m'.heap ((c, Γk) :: Γs) σ m'.kont
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
