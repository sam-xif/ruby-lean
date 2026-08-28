import RubyCore.Proof.Judgment.Sem

/-!
# J45 — the segment layer: `RunSafe`, the S-grade invariant, and `SegOkAt`

The pivot recorded in `implementation-notes.md` J45: extend the semantic-judgment
system from *whole-run* facts (`SemJudge`, conformant start states with an empty
continuation) to *segment* facts — statements about a machine mid-run, mid-kont —
so that out-of-fragment constructs whose evaluation takes **more than one step**
can be admitted by targeted semantic lemmas (schemas), instead of one machine
rung per head.

The layer's spine is one observation: the semantic ground truth at a mid-machine
state is simply *the rest of the run is safe* —

    RunSafe ans m := no reachable result from m is type-stuck, and every
                     terminating run's value inhabits `ans`

— which is exactly `SemJudge`'s body (`semJudge_runSafe_iff` below), stated at an
arbitrary state instead of a conformant one. `RunSafe` is closed under steps by
construction (`RunSafe.step`: reachability from a successor is reachability), and
the syntactic invariant collapses into it (`invJ_runSafe`: the composed soundness
theorems, re-read as "InvJ anywhere implies RunSafe there"). So the disjunction

    InvS ans A m := InvJ ans A m ∨ RunSafe ans m

is an inductive invariant whose right arm is *absorbing*: once a run leaves the
syntactic fragment through a semantically-claimed segment, `RunSafe` carries it —
including everything after the segment delivers — with no re-entry obligation.

`StepOkS` is `StepOkJ` with the `.next` arm weakened from `InvJ` to `InvS` — the
**S-grade** step conclusion. Grade matters and is deliberate: `StepOkJ` refuses
`.stuck`/`.unsupported` (progress), while the reachability property (`SemJudge`,
`typeStuck`) tolerates them; `StepOkS` matches the *semantic* grade (`True` on
those arms), because a segment discharged "by executing the semantics" over
arbitrary conformant heaps can promise no more than `SemJudge` itself promises.

`SegOkAt` is `EvalOkAt` verbatim with the conclusion weakened to `StepOkS`: the
one step out of a claimed expression may land **mid-segment** (`RunSafe`), not
only back in the syntactic invariant. `evalOkAt_segOkAt` embeds the existing
one-step obligations, so every J31/J32 claim is a degenerate segment claim.

**Deliberately not built here (J46, priced in the note):** threading `StepOkS`
through `step_okJ` itself — the change that lets `Judge.semantic` leaves carry
`SegOkAt` obligations inside derivations. That touches the preservation mountain's
conclusion type (mechanical: every case ends in `stepOkJ_toS ∘ ·`), and it is
where the delivery-side design (re-establishing `InvJ` at the claim's `KontOkJ`
from segment facts, without circularity through `SemAxiomsOkS`) must land first.
-/

namespace RubyCore
namespace Proof
namespace Judgment

open Interp
open RubyCore.Types
open RubyCore.Judgment
open RubyCore.Proof.Static

/-! ## `RunSafe` — the semantic ground truth at a mid-machine state -/

/-- **The rest of the run is safe**: no reachable result is type-stuck, and a
    terminating run's value inhabits `ans`. This is `SemJudge`'s body at an
    arbitrary machine state — the segment layer's atom. -/
def RunSafe (ans : Ty) (m : Machine) : Prop :=
  (∀ r, ReachableResult m r → ¬ typeStuck r) ∧
  (∀ v mf, ReachableResult m (.done v mf) → VTy mf.heap v ans)

/-- `SemJudge` is `RunSafe` quantified over conformant start states — the
    definitional reading that makes `RunSafe` the segment generalization. -/
theorem semJudge_runSafe_iff {A : SemAxioms} {D : Decls} {Γ : Env} {e : Expr}
    {c : JCtx} {τ : Ty} :
    SemJudge A D Γ e c τ ↔
      (∀ m : Machine, Conformant A D c Γ m → m.ctl = .eval e → RunSafe τ m) :=
  Iff.rfl

/-- A machine's own next result is reachable (zero steps, then the step). -/
theorem reachableResult_self {m : Machine} : ReachableResult m (stepFn m) :=
  ⟨m, .refl, rfl⟩

/-- Reachability composes across a front step. -/
theorem reachableResult_of_step {m m' : Machine} {r : StepResult}
    (hs : stepFn m = .next m') (hr : ReachableResult m' r) :
    ReachableResult m r := by
  obtain ⟨mr, hre, hst⟩ := hr
  exact ⟨mr, Reaches.head hs hre, hst⟩

/-- **`RunSafe` is closed under steps** — the segment layer's consecution, free by
    construction: everything reachable from the successor was reachable already. -/
theorem RunSafe.step {ans : Ty} {m m' : Machine}
    (h : RunSafe ans m) (hs : stepFn m = .next m') : RunSafe ans m' :=
  ⟨fun r hr => h.1 r (reachableResult_of_step hs hr),
   fun v mf hr => h.2 v mf (reachableResult_of_step hs hr)⟩

/-- **The collapse**: the syntactic invariant anywhere implies `RunSafe` there.
    The content is the already-proved composed soundness — `invariant_sound_from`
    and `invariant_result_sound` over `consecutionJ`/`safetyJ`/`step_okJ` — read
    at an arbitrary invariant-satisfying state instead of the boot state. -/
theorem invJ_runSafe {ans : Ty} {A : SemAxioms} {m : Machine}
    (hax : SemAxiomsOk A) (hinv : InvJ ans A m) : RunSafe ans m :=
  ⟨invariant_sound_from (InvJ ans A) hinv (consecutionJ hax) (safetyJ hax),
   fun v mf hr =>
     invariant_result_sound (InvJ ans A) hinv (consecutionJ hax)
       (fun m' hm' => stepOkJ_doneVTy (step_okJ hax hm')) (.done v mf) hr⟩

/-! ## The S-grade invariant and step conclusion -/

/-- The segment-extended invariant: syntactically in the fragment, **or** inside
    a semantically-certified remainder. The right arm is absorbing
    (`RunSafe.step`), so a run that leaves the fragment through a claimed
    segment never owes re-entry. -/
def InvS (ans : Ty) (A : SemAxioms) (m : Machine) : Prop :=
  InvJ ans A m ∨ RunSafe ans m

/-- `InvS` collapses to `RunSafe` outright (given the axiom set discharged) —
    the composed safety theorem for the S-grade is this one line. -/
theorem invS_runSafe {ans : Ty} {A : SemAxioms} {m : Machine}
    (hax : SemAxiomsOk A) (h : InvS ans A m) : RunSafe ans m :=
  h.elim (invJ_runSafe hax) id

/-- `StepOkJ` at the S-grade: `.next` lands in `InvS` (possibly mid-segment);
    `.stuck`/`.unsupported` are tolerated — the semantic grade (`typeStuck`
    holds of neither), matching what `SemJudge`-level facts can promise. -/
def StepOkS (ans : Ty) (A : SemAxioms) : StepResult → Prop
  | .next m' => InvS ans A m'
  | .done v mf => VTy mf.heap v ans
  | .uncaught exc m => ¬ isTypeError m.heap exc
  | _ => True

/-- The J-grade conclusion embeds in the S-grade. -/
theorem stepOkJ_toS {ans : Ty} {A : SemAxioms} {r : StepResult}
    (h : StepOkJ ans A r) : StepOkS ans A r := by
  cases r with
  | next _ => exact Or.inl h
  | done v mf => exact h
  | uncaught exc m => exact h
  | unsupported reason => trivial
  | stuck msg => trivial

/-- A `RunSafe` state's own step satisfies the S-grade conclusion — the case
    J46's `step_okS` will use for the absorbing arm. -/
theorem stepOkS_of_runSafe {ans : Ty} {A : SemAxioms} {m : Machine}
    (h : RunSafe ans m) : StepOkS ans A (stepFn m) := by
  cases hs : stepFn m with
  | next m'' => exact Or.inr (h.step hs)
  | done v mf => exact h.2 v mf (hs ▸ reachableResult_self)
  | uncaught exc me =>
      have := h.1 (stepFn m) reachableResult_self
      rw [hs] at this
      exact this
  | unsupported reason => trivial
  | stuck msg => trivial

/-! ## `SegOkAt` — the segment obligation

`EvalOkAt`'s hypotheses verbatim (the full mid-machine conformance `step_okJ`'s
eval branch holds at a claimed expression), with the conclusion weakened from
`StepOkJ` to `StepOkS`: the step out of the claim may land mid-segment. A schema
lemma proves this shape once, quantified over the pattern's subterms. -/

/-- The segment obligation at a claim site: `EvalOkAt` with an S-grade
    conclusion. -/
def SegOkAt (ans : Ty) (A : SemAxioms) (D : Decls) (Γ : Env) (e : Expr)
    (top : Bool) (ctx : JCtx) (τ : Ty) (Γ' : Env) (D' : Decls) : Prop :=
  ∀ (m : Machine) (Γs : List (JCtx × Env)) (τw : Ty) (Γk : Env),
    top = Γs.isEmpty →
    FramesOkJ m.heap m.frames m.stack (Γ :: Γs.map Prod.snd) →
    DeclsOkJ A D m.heap →
    StackCtx m.heap m.frames m.stack (jctxs ctx Γs) →
    NoHook m.heap → Saturated m.heap → LitClsOk m.heap → ClassOk m.heap →
    BottomObj m.frames m.stack →
    ChainsIn m.heap →
    framePopLabels m.kont = m.stack.dropLast →
    GlobalsOk D m.heap m.globals →
    ClosuresOk m →
    MFrag A e →
    SubJ τ τw → SubEnv Γk Γ' →
    KontOkJ ans A D' m.heap ((ctx, Γk) :: Γs) τw m.kont →
    StepOkS ans A (evalExpr m e)

/-- Every one-step obligation is a (degenerate) segment obligation. -/
theorem evalOkAt_segOkAt {ans : Ty} {A : SemAxioms} {D : Decls} {Γ : Env}
    {e : Expr} {top : Bool} {ctx : JCtx} {τ : Ty} {Γ' : Env} {D' : Decls}
    (h : EvalOkAt ans A D Γ e top ctx τ Γ' D') :
    SegOkAt ans A D Γ e top ctx τ Γ' D' :=
  fun m Γs τw Γk h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 =>
    stepOkJ_toS (h m Γs τw Γk h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17)

/-- `SemAxiomsOk` at the S-grade: each claim's obligation is a segment
    obligation. This is the hypothesis shape J46's `step_okS` will consume; by
    `semAxiomsOk_toS` every currently-discharged axiom set already satisfies it. -/
def SemAxiomsOkS (A : SemAxioms) : Prop :=
  ∀ cl ∈ A, ∀ (ans : Ty) (D : Decls) (Γ : Env) (top : Bool) (c : JCtx),
    (∀ cn, cl.reqCls = some cn →
      c.cls = cn ∧ c.inClassBody = true ∧ c.inBlock = false) →
    cl.reqModOk c →
    (∀ r ∈ cl.rows, declaresName D r.2.1 = false) →
    (∀ n ∈ cl.freshNames, declaresName D n = false) →
    SegOkAt ans A D Γ cl.e top c cl.τ Γ (addRows D cl.rows)

/-- One-step axiom sets are segment axiom sets. -/
theorem semAxiomsOk_toS {A : SemAxioms} (h : SemAxiomsOk A) : SemAxiomsOkS A :=
  fun cl hcl ans D Γ top c hreq hqm hrows hfn =>
    evalOkAt_segOkAt (h cl hcl ans D Γ top c hreq hqm hrows hfn)

/-! ## Axiom hygiene -/

/-- info: 'RubyCore.Proof.Judgment.invJ_runSafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms invJ_runSafe

/-- info: 'RubyCore.Proof.Judgment.invS_runSafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms invS_runSafe

end Judgment
end Proof
end RubyCore
