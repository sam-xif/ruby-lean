import RubyCore.Proof.Judgment.Sem
import RubyCore.Proof.Judgment.Adequacy

/-!
# The J31 pilot: a user-specified semantic axiom, end to end

The first **directly-proved semantic fact consumed by the syntactic pipeline** — the
extension pilot J30 named. The claimed expression is a block-bearing send:

    lamE  =  `lambda { 1 }`  =  `.send none "lambda" [] (some (.block [] [] (.int 1)))`

which is **out of the machine-typed fragment** (block-bearing sends have no `MFrag`
constructor — they are the J16/J19 arrow bill), so no `Judge`-derivation route
exists for it. Its semantic obligation (`SemAxiomsOk [lamE]`, one `EvalOkAt` at the
canonical judgment) is discharged **by executing the semantics**: `evalExpr` on a
lambda send is one step — `startArgs` → `finishSend` → `reifyBlock`, a proc
allocation delivering a value — so the proof is `inv_grow_valueJ` at `VTy.any`,
eleven lines, no new machinery.

The composition is then exercised **both ways**:

* `egSem_semantic_safe` — a program with the claimed lambda in statement position,
  certified through `judge_sound` with a hand-built derivation whose leaf is
  `Judge.semantic`;
* `egSem_data_certified` — the same program certified from a **data certificate**:
  `egSemJCert` carries the claim in `semAssumes` and invokes it with the
  field-free `Deriv.semantic` node; `validateJ` accepts by `decide`, and the
  composed theorem is conditional on exactly `SemAxiomsOk [lamE]` — discharged
  here, so the conclusion is unconditional.

This is the whole J31 contract in one file: *a construct the syntactic system
cannot check, admitted by a user-supplied semantic lemma, invoked from the
certificate language, composed into the machine-checked safety property.*
-/

namespace RubyCore
namespace Proof
namespace Judgment

open Interp
open RubyCore.Types
open RubyCore.Judgment
open RubyCore.Proof.Static

set_option maxRecDepth 100000

/-- `lambda { 1 }` — a block-bearing send, out of the fragment (`fragHead` false). -/
def lamE : Expr := .send none "lambda" [] (some (.block [] [] (.int 1)))

/-- The claim, at the J31 canonical indices (`.any`, no rows). -/
def lamClaim : SemClaim := { e := lamE }

/-- **The user-supplied semantic lemma**: the claim's `EvalOkAt` obligation,
    discharged by running the machine — a lambda send is one step to a fresh proc
    value, so the invariant is re-established by the heap-growth helper at `.any`. -/
theorem semAxiomsOk_lam : SemAxiomsOk [lamClaim] := by
  intro cl hcl ans D Γ top c _hreq _hqm _hfr _hfn
  simp only [List.mem_singleton] at hcl
  subst hcl
  intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hchn hks hgl hclo hmf
    hsubw hsuE hk
  simp only [lamClaim, lamE, evalExpr, startArgs, finishSend, reifyBlock]
  exact inv_grow_valueJ hfs htab hsc hh hsat hstr hcls hbot hchn hks
    (plainGrow_alloc m.heap _ (by simp) rfl (classPayload?_isSome_lt hstr.2.2.1) rfl)
    rfl rfl rfl
    (VTy.weaken VTy.any hsubw)
    (hchn' := chainsIn_plainGrow
      (plainGrow_alloc m.heap _ (by simp) rfl (classPayload?_isSome_lt hstr.2.2.1) rfl)
      hchn)
    (hk := hk) (hgl := hgl) (hgv := rfl) (hsuE := hsuE) (hclo := hclo)

/-- `x = 1; lambda { 1 }; x` — the claimed lambda in statement position. -/
def egSem : Expr := .seq [.vasgn .lvar "x" (.int 1), lamE, .var .lvar "x"]

/-- The derivation, its middle leaf `Judge.semantic` — no syntactic rule covers
    `lamE`. The `cons` coupling at the leaf is the canonical triple, by `rfl`. -/
theorem egSem_judged : Judge [lamClaim] (declsOf egSem) [] egSem true topJCtx
    .int [("x", .int)] (declsOf egSem) := by
  refine .seq (.cons (.vasgnLvar rfl .int) (.cons ?_ (.single (.varLvar (by decide)))
    (hcpl := fun _ => ⟨lamClaim, by simp, rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩,
      fun cn hcn => by simp [lamClaim] at hcn,
      SemClaim.reqModOk_false rfl,
      fun r hr => by simp [lamClaim] at hr,
      fun n hn => by simp [lamClaim] at hn⟩)))
  exact .semantic (cl := lamClaim) (by simp) (by decide)
    (fun cn hcn => by simp [lamClaim] at hcn)
    (SemClaim.reqModOk_false rfl)
    (fun r hr => by simp [lamClaim] at hr)
    (fun n hn => by simp [lamClaim] at hn) (Or.inl ⟨rfl, rfl⟩)

theorem egSem_mfrag : MFrag [lamClaim] egSem :=
  mfragB_sound (A := [lamClaim]) (n := 8) (by decide)

/-- **The pilot, hand-derivation route**: safety of a program containing an
    out-of-fragment construct, via the discharged semantic axiom. -/
theorem egSem_semantic_safe :
    ∀ r, ReachableResult (Machine.init egSem) r → ¬ typeStuck r :=
  judge_sound semAxiomsOk_lam declsOkJ_declsOf egSem_mfrag (by decide) egSem_judged

/-- ... and its result typing, for free (J29/J30). -/
theorem egSem_result_int :
    ∀ v mf, ReachableResult (Machine.init egSem) (.done v mf) → VTy mf.heap v .int :=
  judge_result_vty semAxiomsOk_lam declsOkJ_declsOf egSem_mfrag (by decide) egSem_judged

/-! ## The same, from a data certificate -/

/-- The certificate: the claim in `semAssumes`, invoked by the field-free
    `.semantic` node at the statement position. -/
def egSemJCert : JCert :=
  { semAssumes := [lamClaim],
    deriv := .seq (.cons (.vasgnLvar .int) (.cons (.semantic 0) (.single .varLvar))) }

theorem egSemJCert_validates : validateJ egSemJCert egSem 8 = true := by decide

/-- **The pilot, certificate route** — J31's contract end to end: the kernel
    replays the derivation (one `decide`), the claim's obligation is the one
    honest hypothesis, and it is discharged above. -/
theorem egSem_data_certified :
    ∀ r, ReachableResult (Machine.init egSem) r → ¬ typeStuck r :=
  validateJ_certifies semAxiomsOk_lam egSemJCert_validates
    (fun r hm => by simp [egSemJCert] at hm)

/-! ## Axiom hygiene -/

/-- info: 'RubyCore.Proof.Judgment.semAxiomsOk_lam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms semAxiomsOk_lam

/-- info: 'RubyCore.Proof.Judgment.egSem_semantic_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms egSem_semantic_safe

/-- info: 'RubyCore.Proof.Judgment.egSem_result_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms egSem_result_int

/-- info: 'RubyCore.Proof.Judgment.egSem_data_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms egSem_data_certified

end Judgment
end Proof
end RubyCore
