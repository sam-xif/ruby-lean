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

/-! ## The second pilot: a schema that delivers a **non-`.any` type**

`defined?(a)` is out of the fragment (`fragHead` false) and, for a class of
argument shapes, is one *unconditional* step to a freshly allocated String —
`evalDefined` answers without evaluating `a` (`defined?(x)` on a parser-known
local is "local-variable" statically, `defined?(nil)` is "nil", …). So the claim
can carry `τ := .cls "String"` and the obligation proves it *exactly*:
`valueTy_alloc_fresh` (the L151 producer-value lemma) types the fresh object off
`LitClsOk`'s String clause. Claimed as the **final** statement of a program, the
type is observable: `judge_result_vty` concludes every terminating run's value
is a String — the first semantic claim whose type does work downstream. -/

/-- The argument shapes whose `defined?` is one unconditional `allocStr` step,
    paired with the string the machine answers. Conditional shapes (ivars,
    gvars — String *or* nil) are a later, nilable-typed schema. -/
def definedStr? : Expr → Option String
  | .nil => some "nil"
  | .tru => some "true"
  | .fls => some "false"
  | .self' => some "self"
  | .var .lvar _ => some "local-variable"
  | _ => none

/-- The schema's claim at an instance: `defined?(a)` **at `.cls "String"`**. -/
def definedClaim (a : Expr) : SemClaim :=
  { e := .defined a, τ := .cls "String" }

/-- The machine's step at a covered shape: one `allocStr`, delivered. -/
theorem evalDefined_str {m : Machine} {a : Expr} {s : String}
    (ha : definedStr? a = some s) :
    evalDefined m a =
      (let vm := Builtins.allocStr m s
       .next (withCtl vm.2 (.value vm.1))) := by
  unfold definedStr? at ha
  split at ha <;> simp_all [evalDefined]

/-- The core obligation: `defined?` at a covered shape re-establishes the
    invariant **at `.cls "String"`** — `VTy.exact` where the lambda schema had
    `VTy.any`, off `valueTy_alloc_fresh` and `LitClsOk`'s String clause. -/
theorem evalOkAt_defined_str {A : SemAxioms} {a : Expr} {s : String}
    (ha : definedStr? a = some s)
    (ans : Ty) (D : Decls) (Γ : Env) (top : Bool) (c : JCtx) :
    EvalOkAt ans A D Γ (.defined a) top c (.cls "String") Γ D := by
  intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hchn hks hgl hclo hmf
    hsubw hsuE hk
  have hg : PlainGrow m.heap ⟨m.heap.objs.push { klass := Boot.stringId, payload := .str s }⟩ :=
    plainGrow_alloc m.heap _ (by simp) rfl (classPayload?_isSome_lt hstr.1.1) rfl
  simp only [evalExpr, evalDefined_str ha, Builtins.allocStr]
  exact inv_grow_valueJ hfs htab hsc hh hsat hstr hcls hbot hchn hks hg
    rfl rfl rfl
    (VTy.weaken (VTy.ofValueTy (valueTy_alloc_fresh
      ⟨by simp, by simp, by simp⟩
      rfl rfl rfl hstr.1.1 hstr.1.2
      (fun hq => absurd hq (by decide)))) hsubw)
    (hchn' := chainsIn_plainGrow hg hchn)
    (hk := hk) (hgl := hgl) (hgv := rfl) (hsuE := hsuE) (hclo := hclo)

/-- **The schema lemma**: every list of covered `defined?` claims is a discharged
    axiom set — at `.cls "String"`, not `.any`. -/
theorem semAxiomsOk_definedStr (args : List Expr)
    (hargs : ∀ a ∈ args, (definedStr? a).isSome) :
    SemAxiomsOk (args.map definedClaim) := by
  intro cl hcl ans D Γ top c _hreq _hrows
  obtain ⟨a, hmem, rfl⟩ := List.mem_map.mp hcl
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (hargs a hmem)
  exact evalOkAt_defined_str hs ans D Γ top c

/-! ### The demo: the claimed type is *observable* -/

/-- `x = 1; defined?(self); defined?(x)` — two claimed `defined?`s, the second in
    **final** position, so the program's judged type is the claim's
    `.cls "String"`. -/
def egDefined : Expr :=
  .seq [.vasgn .lvar "x" (.int 1), .defined .self', .defined (.var .lvar "x")]

def egDefinedAxioms : SemAxioms :=
  [definedClaim .self', definedClaim (.var .lvar "x")]

theorem egDefinedAxioms_ok : SemAxiomsOk egDefinedAxioms :=
  semAxiomsOk_definedStr [.self', .var .lvar "x"]
    (by intro a ha; simp only [List.mem_cons, List.mem_singleton] at ha
        rcases ha with rfl | rfl | h
        · rfl
        · rfl
        · exact absurd h (by simp))

theorem egDefined_mfrag : MFrag egDefinedAxioms egDefined :=
  mfragB_sound (A := egDefinedAxioms) (n := 32) (by decide)

/-- The derivation: both leaves `Judge.semantic`, the second under
    `JudgeSeq.single`, so the sequence's type is the second claim's τ. -/
theorem egDefined_judged : Judge egDefinedAxioms (declsOf egDefined) [] egDefined
    true topJCtx (.cls "String") [("x", .int)] (declsOf egDefined) := by
  refine .seq (.cons (.vasgnLvar rfl .int) (.cons ?_ (.single ?_
      (hcpl := fun _ => ⟨definedClaim (.var .lvar "x"), by simp [egDefinedAxioms],
        rfl, rfl, rfl, rfl, Or.inl rfl,
        fun cn hcn => by simp [definedClaim] at hcn,
        fun r hr => by simp [definedClaim] at hr⟩))
    (hcpl := fun _ => ⟨definedClaim .self', by simp [egDefinedAxioms],
      rfl, rfl, rfl, rfl, Or.inl rfl,
      fun cn hcn => by simp [definedClaim] at hcn,
      fun r hr => by simp [definedClaim] at hr⟩)))
  · exact .semantic (cl := definedClaim .self') (by simp [egDefinedAxioms]) (by decide)
      (fun cn hcn => by simp [definedClaim] at hcn)
      (fun r hr => by simp [definedClaim] at hr) (Or.inl rfl)
  · exact .semantic (cl := definedClaim (.var .lvar "x")) (by simp [egDefinedAxioms])
      (by decide)
      (fun cn hcn => by simp [definedClaim] at hcn)
      (fun r hr => by simp [definedClaim] at hr) (Or.inl rfl)

/-- Safety, hand-derivation route. -/
theorem egDefined_safe :
    ∀ r, ReachableResult (Machine.init egDefined) r → ¬ typeStuck r :=
  judge_sound egDefinedAxioms_ok declsOkJ_declsOf egDefined_mfrag (by decide)
    egDefined_judged

/-- **The headline: result typing through a semantic claim.** Every terminating
    run of the program delivers a String — the claimed non-`.any` type, carried
    from the schema lemma through `judge_result_vty` to the reachable outcome. -/
theorem egDefined_result_string :
    ∀ v mf, ReachableResult (Machine.init egDefined) (.done v mf) →
      VTy mf.heap v (.cls "String") :=
  judge_result_vty egDefinedAxioms_ok declsOkJ_declsOf egDefined_mfrag (by decide)
    egDefined_judged

/-- ... and the same program certified from a data certificate. -/
def egDefinedJCert : JCert :=
  { semAssumes := egDefinedAxioms,
    deriv := .seq (.cons (.vasgnLvar .int)
      (.cons (.semantic 0) (.single (.semantic 1)))) }

theorem egDefinedJCert_validates : validateJ egDefinedJCert egDefined 32 = true := by
  decide

theorem egDefined_data_certified :
    ∀ r, ReachableResult (Machine.init egDefined) r → ¬ typeStuck r :=
  validateJ_certifies egDefinedAxioms_ok egDefinedJCert_validates
    (fun _r hm => by simp [egDefinedJCert, egDefinedAxioms, definedClaim] at hm)

/-! ## Axiom hygiene -/

/-- info: 'RubyCore.Proof.Judgment.semAxiomsOk_lambdas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms semAxiomsOk_lambdas

/-- info: 'RubyCore.Proof.Judgment.egSchema_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms egSchema_certified

/-- info: 'RubyCore.Proof.Judgment.semAxiomsOk_definedStr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms semAxiomsOk_definedStr

/-- info: 'RubyCore.Proof.Judgment.egDefined_result_string' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms egDefined_result_string

/-- info: 'RubyCore.Proof.Judgment.egDefined_data_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms egDefined_data_certified

end Judgment
end Proof
end RubyCore
