import RubyCore.Proof.Judgment.Seg
import RubyCore.Proof.Judgment.SemAxiom

/-!
# J45 — the schema pilot: one lemma, every `lambda` site

The first **schema judgment**: a semantic lemma quantified over a pattern's
subterms, so that *one* proof discharges the obligation of *every* claim
instantiating the pattern. J31's pilot discharged `lambda { 1 }` — one fixed
expression, one lemma (`semAxiomsOk_lam`). This file generalizes it to

    lambda { |ps| b }        (any params, any locals, any body)

with `semAxiomsOk_lambdas` covering **any list** of such claims at once. The
proof is J31's eleven lines, unchanged in content: a lambda send is one step —
`startArgs → finishSend → reifyBlock` — and `reifyBlock` allocates a proc
*capturing* the body without evaluating it, so the invariant is re-established
by the plain-heap-growth helper at `.any`, for every body uniformly. `ClosuresOk`
demands captured-frame facts only, nothing of the body — which is why the schema
carries **no premise on `b` at all**.

That absence is also the honest fine print: the schema promises exactly what the
machine's one step does — a proc *value* — and nothing about *calling* it. The
demo program below claims `lambda { 1.nope }` (a body that would `NoMethodError`
if run) and is certified safe, because the proc is never called; a send named
`call` is still fragment-excluded (the J19 arrow bill), so a program that *does*
call it cannot be certified by this route. Schema soundness lives or dies on the
side conditions, so schemas are Lean lemmas beside `semAxiomsOk_lam`, never
user-supplied data (`implementation-notes.md` J45).

Demo: a program with **two different** claimed lambdas, certified end to end from
a data certificate (`validateJ` by one kernel `decide`), both obligations
discharged by the single schema lemma.
-/

namespace RubyCore
namespace Proof
namespace Judgment

open Interp
open RubyCore.Types
open RubyCore.Judgment
open RubyCore.Proof.Static

set_option maxRecDepth 100000

/-- The pattern: `lambda { |ps| b }` — a block-bearing send, out of the fragment
    for every `ps`/`ls`/`b` (`fragHead` is `false` at any block-bearing send). -/
def lamES (ps : List Param) (ls : List String) (b : Expr) : Expr :=
  .send none "lambda" [] (some (.block ps ls b))

/-- The schema's claim at an instance, at the J31 canonical indices
    (`.any`, no rows, position-free). J31's `lamClaim` is `lamClaimS [] [] (.int 1)`. -/
def lamClaimS (ps : List Param) (ls : List String) (b : Expr) : SemClaim :=
  { e := lamES ps ls b }

/-- **The schema lemma** — one proof, arbitrarily many `lambda` sites: every list
    of `lambda`-shaped claims is a discharged axiom set. The body `b` is bound by
    a bare `∀`: `reifyBlock` captures it without evaluating it, so no premise on
    `b` is owed (and none is given — see the header's fine print). -/
theorem semAxiomsOk_lambdas (insts : List (List Param × List String × Expr)) :
    SemAxiomsOk (insts.map fun t => lamClaimS t.1 t.2.1 t.2.2) := by
  intro cl hcl ans D Γ top c _hreq _hrows
  obtain ⟨⟨ps, ls, b⟩, -, rfl⟩ := List.mem_map.mp hcl
  intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hchn hks hgl hclo hmf
    hsubw hsuE hk
  simp only [lamClaimS, lamES, evalExpr, startArgs, finishSend, reifyBlock]
  exact inv_grow_valueJ hfs htab hsc hh hsat hstr hcls hbot hchn hks
    (plainGrow_alloc m.heap _ (by simp) rfl (classPayload?_isSome_lt hstr.2.2.1) rfl)
    rfl rfl rfl
    (VTy.weaken VTy.any hsubw)
    (hchn' := chainsIn_plainGrow
      (plainGrow_alloc m.heap _ (by simp) rfl (classPayload?_isSome_lt hstr.2.2.1) rfl)
      hchn)
    (hk := hk) (hgl := hgl) (hgv := rfl) (hsuE := hsuE) (hclo := hclo)

/-! ## The demo: two distinct lambdas, one schema, one certificate -/

/-- A body that would `NoMethodError` if it ever ran. The schema admits it: the
    lambda is a *value*, and this program never calls it. -/
def bodyBad : Expr := .send (some (.int 1)) "nope" [] none

/-- A second, unrelated body — the point is that the two sites share one lemma. -/
def bodyStr : Expr := .str "hi"

/-- `x = 1; lambda { 1.nope }; lambda { "hi" }; x` — two claimed lambdas in
    statement position. -/
def egSchema : Expr :=
  .seq [.vasgn .lvar "x" (.int 1), lamES [] [] bodyBad, lamES [] [] bodyStr,
        .var .lvar "x"]

/-- The demo's axiom set: both claims are instances of the one schema. -/
def egSchemaAxioms : SemAxioms :=
  [lamClaimS [] [] bodyBad, lamClaimS [] [] bodyStr]

/-- Both obligations by the single schema lemma. -/
theorem egSchemaAxioms_ok : SemAxiomsOk egSchemaAxioms :=
  semAxiomsOk_lambdas [([], [], bodyBad), ([], [], bodyStr)]

/-- The data certificate: both claims in `semAssumes`, each invoked by the
    field-free `.semantic` node at its statement position. -/
def egSchemaJCert : JCert :=
  { semAssumes := egSchemaAxioms,
    deriv := .seq (.cons (.vasgnLvar .int)
      (.cons (.semantic 0) (.cons (.semantic 1) (.single .varLvar)))) }

theorem egSchemaJCert_validates : validateJ egSchemaJCert egSchema 32 = true := by
  decide

/-- **The pilot, end to end**: a program with two out-of-fragment block-bearing
    sends, certified from a data certificate replayed by one kernel `decide`,
    with both semantic obligations discharged by one schema lemma. -/
theorem egSchema_certified :
    ∀ r, ReachableResult (Machine.init egSchema) r → ¬ typeStuck r :=
  validateJ_certifies egSchemaAxioms_ok egSchemaJCert_validates
    (fun _r hm => by simp [egSchemaJCert, egSchemaAxioms, lamClaimS] at hm)

/-! ## Axiom hygiene -/

/-- info: 'RubyCore.Proof.Judgment.semAxiomsOk_lambdas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms semAxiomsOk_lambdas

/-- info: 'RubyCore.Proof.Judgment.egSchema_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms egSchema_certified

end Judgment
end Proof
end RubyCore
