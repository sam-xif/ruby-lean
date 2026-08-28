import RubyCore.Proof.Judgment.Schema
import RubyCore.Proof.Judgment.Adequacy

/-!
# J47 — the `defs` schema: one lemma, every `def self.name` site

The third schema (after `semAxiomsOk_lambdas`/`semAxiomsOk_definedStr`), and the
first to consume the parked Wall-2 vocabulary: `def self.name(ps) body end` in a
**machine-typed module body**.

The construct has no syntactic route by design (`self'` in a class body is
untypable — `selfCls` is `none` there), so it is claim territory. The claim is
made one-step by the J47 interpreter composition (the receiver eval is a pure
`currentFrame.self` read), and the obligation is then `defPromote`'s argument
*minus the row*: the step is one `defineMethod` on the **realized eigenclass**
of the definee —

* the receiver's identity comes from `StackCtx`'s J34 class-body clause
  (`self = .ref defmod`), reached through the claim's `reqMod` guard;
* the eigenclass being *already realized* (so `eigenclassOf` is a pure read,
  no allocation, no old-object mutation) is J44c's module-body clause — the
  fact recorded as "later, by `defs`" when it landed;
* the freshness of the installed name against the table rides the claim's
  `freshNames` channel (checker-enforced), which is what `DeclsOkJ_defineMethod`
  consumes — no row is threaded (`Judge.defs` would drop eigenclass rows too),
  so the installed method is *install-and-forget*: nothing in the fragment can
  ever dispatch it, which is why the schema carries **no premise on the body**.

Fine print (the honest contract, as the lambda schema's): the schema certifies
the *installation* — a `.sym` delivered, one method-table write on an object off
every declared resolution path — and nothing about *calling* the method.
-/

namespace RubyCore
namespace Proof
namespace Judgment

open Interp
open RubyCore.Types
open RubyCore.Judgment
open RubyCore.Proof.Static

set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

/-- The pattern: `def self.name(ps) body end`. `fragHead` is `false` at `defs`,
    so every instance is claimable. -/
def defsSelfE (name : String) (ps : List Param) (body : Expr) : Expr :=
  .defs .self' name ps body

/-- The schema's claim at an instance: τ = `.sym` (the machine delivers the
    method name), module-body position (`reqMod`), the installed name declared
    fresh (`freshNames`). -/
def defsClaim (name : String) (ps : List Param) (body : Expr) : SemClaim :=
  { e := defsSelfE name ps body, τ := .sym, reqMod := true, freshNames := [name] }

/-- `eigenclassOf` on an object whose eigenclass is realized is a pure read. -/
theorem eigenclassOf_realized {m : Machine} {o e₀ : ObjId}
    (he : (m.heap.get o).eigen = some e₀) : eigenclassOf m o = (e₀, m) := by
  simp only [eigenclassOf, eigenclassOf.go, he]

/-- The `MethodDef` the composed step installs. -/
def defsMd (m : Machine) (ps : List Param) (body : Expr) (e₀ : ObjId) : MethodDef :=
  { params := ps, body := body, owner := e₀,
    cref := m.currentFrame.cref, fromPrelude := m.preludeMode }

/-- The composed step, reduced: at a realized-eigenclass `self`, `evalExpr` on
    the claim is one `defineMethod`. -/
theorem evalExpr_defsSelf {m : Machine} {name : String} {ps : List Param}
    {body : Expr} {o e₀ : ObjId}
    (hself : m.currentFrame.self = .ref o)
    (he : (m.heap.get o).eigen = some e₀) :
    evalExpr m (defsSelfE name ps body) =
      .next (withCtl { m with heap := defineMethod m.heap e₀ name (defsMd m ps body e₀) }
        (.value (.sym name))) := by
  simp only [defsSelfE, evalExpr, hself, eigenclassOf_realized he, defsMd]

/-- **The schema lemma** — one proof, every `def self.name` site in a module
    body: any axiom set of `defs`-shaped claims (names off the hook list) is
    discharged. Stated shape-wise (J51) so the wire-decoded claim list is
    covered directly, with the mapped-list form (`semAxiomsOk_defsSelf`) a
    corollary. -/
theorem semAxiomsOk_defsAll {A : SemAxioms}
    (h : ∀ cl ∈ A, ∃ n ps b, cl = defsClaim n ps b ∧
      n ≠ "method_added" ∧ n ≠ "define_method") :
    SemAxiomsOk A := by
  intro cl hcl ans D Γ top c _hreq hqm hfr hfn
  obtain ⟨name, ps, body, rfl, hna1, hna2⟩ := h cl hcl
  obtain ⟨hicb, hnbk, hor⟩ := hqm rfl
  have hfresh : declaresName D name = false := hfn name (by simp [defsClaim])
  have hha : name ≠ "method_added" ∧ name ≠ "define_method" := ⟨hna1, hna2⟩
  intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hchn hks hgl hclo hmf
    hsubw hsuE hk
  have hfsh1 : m.stack ≠ [] := (hfs.frameShallow).1
  have hdm : m.currentFrame = curFrame m := currentFrame_eq hfsh1
  have hfs := FramesOkJ.narrowHead hsuE hfs
  obtain ⟨fid₀, fids₀, hst⟩ : ∃ fid fids, m.stack = fid :: fids := by
    cases hst : m.stack with
    | nil => exact absurd hst hfsh1
    | cons a r => exact ⟨a, r, rfl⟩
  have hscc : StackCtx m.heap m.frames (fid₀ :: fids₀)
      (c.toFrameCtx :: (Γs.map Prod.fst).map JCtx.toFrameCtx) := by
    rw [hst] at hsc; exact hsc
  have hcur : curFrame m = m.frames.getD fid₀ default := by
    simp [curFrame, curFid, hst]
  -- J34: the frame's `self` is the definee.
  have hself : (curFrame m).self = .ref (curFrame m).defmod := by
    rw [hcur]
    exact hscc.2.2.2.2.2.2.2.2.1 hicb hnbk
  -- J44c / J53: the definee's eigenclass is realized — the module clause or
  -- the fresh-class clause, whichever the position guard supplies.
  have heig : ((m.heap.get (curFrame m).defmod).eigen).isSome := by
    rw [hcur]
    rcases hor with himb | hifc
    · obtain ⟨cp, hcp, hism, hnm, heig, hoff⟩ :=
        hscc.2.2.2.2.2.2.2.2.2.1 himb hnbk
      exact heig
    · obtain ⟨cp, hcp, hism, hnm, heig⟩ :=
        hscc.2.2.2.2.2.2.2.2.2.2.1 hifc hnbk
      exact heig
  obtain ⟨e₀, he₀⟩ := Option.isSome_iff_exists.mp heig
  -- the step, reduced
  simp only [defsClaim]
  rw [evalExpr_defsSelf (by rw [hdm]; exact hself) he₀]
  -- the invariant, re-established across the one method-table write
  have hag : TypeAgree m.heap (defineMethod m.heap e₀ name (defsMd m ps body e₀)) :=
    typeAgree_defineMethod _ _ _ _
  refine ⟨NoHook_defineMethod hh hha,
    Saturated_defineMethod hsat _ _ _,
    chainsIn_defineMethod hchn,
    LitClsOk_defineMethod hstr,
    ClassOk_defineMethod hcls,
    hbot, hks,
    ClosuresOk.transport hclo
      (by intro κ hm cl hcl; exact ⟨κ, hm, hcl⟩)
      (Nat.le_refl _)
      (by intro p _; exact FrameShape.rfl' _)
      (by
        intro o ho
        show ((defineMethod m.heap e₀ name _).classPayload? o).isSome = true
        exact (hag.2.2.1 o (classPayload?_isSome_lt ho)) ▸ ho),
    D, c, Γk, Γs,
    DeclsOkJ_defineMethod htab hfresh,
    FramesOkJ.heap_congr hag hfs,
    StackCtx.heap_congr hag (hst ▸ hscc),
    GlobalsOk.congr hag hgl,
    ⟨_, _, VTy.weaken (VTy.exact rfl) hsubw, SubEnv.refl _,
      KontOkJ.heap_congr hag hk⟩⟩

/-- The mapped-list form, re-derived. -/
theorem semAxiomsOk_defsSelf (insts : List (String × List Param × Expr))
    (hna : ∀ i ∈ insts, i.1 ≠ "method_added" ∧ i.1 ≠ "define_method") :
    SemAxiomsOk (insts.map fun t => defsClaim t.1 t.2.1 t.2.2) :=
  semAxiomsOk_defsAll (by
    intro cl hcl
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hcl
    exact ⟨t.1, t.2.1, t.2.2, rfl, (hna t ht).1, (hna t ht).2⟩)

/-- `defsShapeB` (the checker-side shape test) names exactly a `defsClaim`. -/
theorem defsShapeB_sound {cl : SemClaim} (h : defsShapeB cl = true) :
    ∃ n ps b, cl = defsClaim n ps b ∧
      n ≠ "method_added" ∧ n ≠ "define_method" := by
  unfold defsShapeB at h
  split at h
  · next name ps body heq =>
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
      List.isEmpty_iff, Option.isNone_iff_eq_none] at h
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
    refine ⟨name, ps, body, ?_, h1, h2⟩
    obtain ⟨e, τ, rows, rc, rm, fn⟩ := cl
    simp only at heq h3 h4 h5 h6 h7
    subst heq h3 h4 h5 h7
    simp only [defsClaim, defsSelfE]
    rw [h6]
  · exact absurd h (by simp)

/-- **The wire-decoded axiom set, discharged by one `Bool`** (J51): every claim
    passes `defsShapeB` ⇒ the set is sound. -/
theorem semAxiomsOk_defsShape {A : SemAxioms}
    (h : A.all defsShapeB = true) : SemAxiomsOk A :=
  semAxiomsOk_defsAll fun cl hcl => defsShapeB_sound (List.all_eq_true.mp h cl hcl)

/-- **The composed accept for `defs`-claim certificates** — `validateJ` accepts
    and the claim list is all-`defsShapeB` ⇒ reachability type safety, with the
    same row/constant residues as `validateJ_certifies` and the semantic residue
    GONE. A certificate with empty `delta_rows`/`delta_consts` and all-shaped
    claims is therefore **unconditional**. -/
theorem validateJ_certifies_defs {c : JCert} {p : Expr} {fuel : Nat}
    (hshape : c.semAssumes.all defsShapeB = true)
    (h : validateJ c p fuel = true)
    (ha : ∀ r ∈ c.deltaRows,
      EntryOkJ c.semAssumes (c.table p) Boot.initHeap (nomTy r.cls) r.name r.sig)
    (hac : ∀ e ∈ c.deltaConsts, ConstOk Boot.initHeap e.1 e.2 := by
      intro e he; exact absurd (show e ∈ [] from he) (by simp))
    (hasc : ∀ e ∈ c.deltaScopedConsts,
      ScopedConstOk Boot.initHeap e.1.1 e.1.2 e.2 := by
      intro e he; exact absurd (show e ∈ [] from he) (by simp)) :
    ∀ r, ReachableResult (Machine.init p) r → ¬ typeStuck r :=
  validateJ_certifies (semAxiomsOk_defsShape hshape) h ha hac hasc

/-! ## The demo: two `def self.` claims inside a hand-built machine state

The end-to-end exercise (a `module` wrapper machine-typed around them) lands
with the module rung; here the schema is exercised as an axiom set alone. -/

/-- Two distinct instances, one lemma. -/
theorem egDefsAxioms_ok : SemAxiomsOk
    [defsClaim "compare" [.req "l", .req "r"] (.int 1),
     defsClaim "parse" [.req "v"] .nil] :=
  semAxiomsOk_defsSelf
    [("compare", [.req "l", .req "r"], .int 1), ("parse", [.req "v"], .nil)]
    (by intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> exact ⟨by decide, by decide⟩)

/-! ## Axiom hygiene -/

/-- info: 'RubyCore.Proof.Judgment.semAxiomsOk_defsSelf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms semAxiomsOk_defsSelf

/-- info: 'RubyCore.Proof.Judgment.validateJ_certifies_defs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms validateJ_certifies_defs

end Judgment
end Proof
end RubyCore
