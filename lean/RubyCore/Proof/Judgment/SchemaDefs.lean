import RubyCore.Proof.Judgment.Schema

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

/-- The composed step, reduced: at a realized-eigenclass `self`, `evalExpr` on
    the claim is one `defineMethod`. -/
theorem evalExpr_defsSelf {m : Machine} {name : String} {ps : List Param}
    {body : Expr} {o e₀ : ObjId}
    (hself : m.currentFrame.self = .ref o)
    (he : (m.heap.get o).eigen = some e₀) :
    evalExpr m (defsSelfE name ps body) =
      .next (withCtl { m with heap := defineMethod m.heap e₀ name
          { params := ps, body := body, owner := e₀,
            cref := m.currentFrame.cref, fromPrelude := m.preludeMode } }
        (.value (.sym name))) := by
  simp only [defsSelfE, evalExpr, hself, eigenclassOf_realized he]

/-- **The schema lemma** — one proof, every `def self.name` site in a module
    body: any list of `defs`-shaped claims (names off the hook list) is a
    discharged axiom set. -/
theorem semAxiomsOk_defsSelf (insts : List (String × List Param × Expr))
    (hna : ∀ i ∈ insts, i.1 ≠ "method_added" ∧ i.1 ≠ "define_method") :
    SemAxiomsOk (insts.map fun t => defsClaim t.1 t.2.1 t.2.2) := by
  intro cl hcl ans D Γ top c _hreq hqm hfr hfn
  obtain ⟨⟨name, ps, body⟩, hmem, rfl⟩ := List.mem_map.mp hcl
  obtain ⟨hicb, himb, hnbk⟩ := hqm rfl
  have hfresh : declaresName D name = false := hfn name (by simp [defsClaim])
  have hha := hna _ hmem
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
  -- J44c: the definee's eigenclass is realized.
  obtain ⟨cp, hcp, hism, hnm, heig, hoff⟩ := by
    rw [hcur] at hscc ⊢
    exact hscc.2.2.2.2.2.2.2.2.2.1 himb hnbk
  obtain ⟨e₀, he₀⟩ := Option.isSome_iff_exists.mp heig
  -- the step, reduced
  rw [evalExpr_defsSelf (by rw [hdm, hcur]; rw [hcur] at hself; exact hself)
    (by rw [hdm, hcur]; exact he₀)]
  -- the invariant, re-established across the one method-table write
  have hag : TypeAgree m.heap (defineMethod m.heap e₀ name
      { params := ps, body := body, owner := e₀,
        cref := m.currentFrame.cref, fromPrelude := m.preludeMode }) :=
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
    ⟨.sym, Γk, VTy.weaken (VTy.exact rfl) hsubw, SubEnv.refl _,
      KontOkJ.heap_congr hag hk⟩⟩

/-! ## The demo: two `def self.` claims inside a hand-built machine state

The end-to-end exercise (a `module` wrapper machine-typed around them) lands
with the module rung; here the schema is exercised as an axiom set alone. -/

/-- Two distinct instances, one lemma. -/
theorem egDefsAxioms_ok : SemAxiomsOk
    [defsClaim "compare" [.req "l", .req "r"] (.int 1),
     defsClaim "parse" [.req "v"] .nil] :=
  semAxiomsOk_defsSelf
    [("compare", [.req "l", .req "r"], .int 1), ("parse", [.req "v"], .nil)]
    (by intro i hi; rcases hi with hi | hi | h
        · subst hi; exact ⟨by decide, by decide⟩
        · rcases hi with rfl | h
          · exact ⟨by decide, by decide⟩
          · exact absurd h (by simp)
        · exact absurd h (by simp))

/-! ## Axiom hygiene -/

/-- info: 'RubyCore.Proof.Judgment.semAxiomsOk_defsSelf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms semAxiomsOk_defsSelf

end Judgment
end Proof
end RubyCore
