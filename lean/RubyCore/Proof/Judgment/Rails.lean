import RubyCore.Proof.Judgment.Sem
import RubyCore.Proof.Judgment.Adequacy

/-!
# J35 — the Rails pilot: `define_method`, claimed, discharged, dispatched

The goal program is the emblem of Rails-style metaprogramming, in its idiomatic
implicit-receiver form:

    class String
      define_method(:shout) { 1 }     -- runtime-generated method: no `def` anywhere
    end
    "a".shout                          -- dispatch on the *generated* row

The `define_method` statement is out of the syntactic fragment twice over (a
block-bearing send; a class-object receiver), so it enters as a **semantic claim**
(`dmClaim`): judged at `.sym` (its value), gated to `class String` bodies
(`reqCls`), and carrying the **claimed row** `String#shout : () → Integer` — the
J32 table effect that makes the second statement's dispatch syntactically typable,
exactly as `defPromote` threads a `def`'s row.

`semAxiomsOk_dm` discharges the claim's obligation **by executing the semantics**:
the J33 one-step composition makes `evalExpr` on the statement a single step —
reify the block (an allocation), walk the dispatch to the reflective installer
(the lookup *miss* is `NoHook`'s J34 clause; the receiver's identity is `StackCtx`'s
J34 class-body-self clause), install the method (`defineMethod`, with the capture
erased for the closed body), deliver the symbol — and the invariant is
re-established at the grown table by the same argument `defPromote`'s preservation
case makes, scavenged: the generated method resolves (`lookup_go_defineMethod_self`)
and conforms (`UserConformsJ`, its body `1` judged by one literal rule).
-/

namespace RubyCore
namespace Proof
namespace Judgment

open Interp
open RubyCore.Types
open RubyCore.Judgment
open RubyCore.Proof.Static

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The generated method's body: `1`. -/
def dmBody : Expr := .int 1

/-- `define_method(:shout) { 1 }`. -/
def dmE : Expr := .send none "define_method" [.sym "shout"] (some (.block [] [] dmBody))

/-- The claimed row: `String#shout : () → Integer`. -/
def shoutSig : MethodDecl := { params := [], ret := .int }

/-- The claim: `dmE`, judged at `.sym`, in `class String` bodies only, installing
    the `shout` row. -/
def dmClaim : SemClaim :=
  { e := dmE, τ := .sym, rows := [("String", "shout", shoutSig)],
    reqCls := some "String" }

/-- The `MethodDef` the step installs (the closure's capture erased — `dmBody` is
    local-free — so it is exactly `def`-shaped for `ResolvesUser`). -/
def dmMd (cref : List ObjId) (owner : ObjId) (fromPrelude : Bool) : MethodDef :=
  { params := [], body := dmBody, owner := owner, cref := cref,
    capturedFrame := none, declared := [], fromPrelude := fromPrelude }

/-- The closure the block reifies to. -/
def dmPcl (m : Machine) : Closure :=
  { params := [], locals := [], body := dmBody, captured := m.stack.headD 0,
    home := returnTarget m, lam := false }

/-- The proc object the reification allocates. -/
def dmPobj (m : Machine) : Object :=
  { klass := Boot.procId, payload := .proc (dmPcl m) }

/-- The machine after the reification's allocation. -/
def dmM₁ (m : Machine) : Machine := { m with heap := (m.heap.alloc (dmPobj m)).2 }

/-- The machine after the whole step: the method installed on the frame's definee. -/
def dmPo (m : Machine) : ObjId := (m.heap.alloc (dmPobj m)).1

def dmM₂ (m : Machine) : Machine :=
  { dmM₁ m with
    heap := defineMethod (dmM₁ m).heap (curFrame m).defmod "shout"
      (dmMd ((dmM₁ m).frames.getD (dmPcl m).captured default).cref
        (curFrame m).defmod m.preludeMode) }

/-- **The step, in one equation**: on a machine whose current frame is a class
    body (`self` = the definee, a class object) where `define_method` is unshadowed,
    the claim's expression is one step — reify, dispatch, install, deliver. -/
theorem evalExpr_dm (m : Machine) {cp : ClassPayload}
    (hself : m.currentFrame.self = .ref (curFrame m).defmod)
    (hdo₁ : ((dmM₁ m).heap.classPayload? (curFrame m).defmod).isSome = true)
    (hcp : ((dmM₁ m).heap.get (curFrame m).defmod).payload = .cls cp)
    (hlk : lookup (dmM₁ m).heap (.ref (curFrame m).defmod) "define_method" = none) :
    evalExpr m dmE = .next (withCtl (dmM₂ m) (.value (.sym "shout"))) := by
  have hgetpo : (dmM₁ m).heap.get (dmPo m) = dmPobj m := by
    simp [dmM₁, dmPo, Heap.alloc, Heap.get, Array.getD]
  -- checkpoint 1: the J33 arm + `finishSend_lit` + the reification
  have h1 : evalExpr m dmE
      = invoke (dmM₁ m) (.ref (curFrame m).defmod) .implicit "define_method"
          [.sym "shout"] (some (.ref (dmPo m))) [] := by
    show finishSend m m.currentFrame.self .implicit "define_method" [.sym "shout"]
        (.lit [] [] dmBody) = _
    rw [hself, finishSend_lit (by decide) (by decide) (by decide)]
    rfl
  -- checkpoint 2: the dispatch walk lands on `invokeDispatch`
  have h2 : invoke (dmM₁ m) (.ref (curFrame m).defmod) .implicit "define_method"
        [.sym "shout"] (some (.ref (dmPo m))) []
      = invoke.invokeDispatch (dmM₁ m) (.ref (curFrame m).defmod) .implicit
          "define_method" [.sym "shout"] (some (.ref (dmPo m))) [] := by
    unfold invoke
    simp only [hlk, hcp, Option.isNone_none, String.reduceBEq, Bool.or_self,
      Bool.false_or, Bool.or_false, Bool.and_true, Bool.false_and, Bool.and_false,
      Bool.false_eq_true, if_false, reduceIte]
    by_cases hmath : ((curFrame m).defmod == Boot.mathId) = true
    · simp only [hmath, if_true, reduceIte]
      rfl
    · simp only [hmath, Bool.false_eq_true, if_false, reduceIte]
      unfold invoke.invokeMaybeNew
      simp only [String.reduceBEq, Bool.false_and, Bool.false_eq_true, if_false,
        reduceIte]
  -- checkpoint 3: the miss, and the reflective installer
  have h3 : invoke.invokeDispatch (dmM₁ m) (.ref (curFrame m).defmod) .implicit
        "define_method" [.sym "shout"] (some (.ref (dmPo m))) []
      = .next (withCtl (dmM₂ m) (.value (.sym "shout"))) := by
    unfold invoke.invokeDispatch
    rw [hlk]
    show dispatchMiss (dmM₁ m) (.ref (curFrame m).defmod) .implicit "define_method"
        [.sym "shout"] (some (.ref (dmPo m))) = _
    unfold dispatchMiss
    rw [show tryIterator (dmM₁ m) (.ref (curFrame m).defmod) "define_method"
        [.sym "shout"] (some (.ref (dmPo m))) = none from by
      unfold tryIterator
      simp only [hgetpo, dmPobj, hcp]]
    rw [show tryMixin (dmM₁ m) (.ref (curFrame m).defmod) "define_method"
        [.sym "shout"] = none from rfl]
    rw [show tryReflect (dmM₁ m) (.ref (curFrame m).defmod) "define_method"
        [.sym "shout"] (some (.ref (dmPo m)))
        = some (.next (withCtl (dmM₂ m) (.value (.sym "shout")))) from by
      have hlf : localFreeB 1000000 dmBody = true := rfl
      unfold tryReflect
      simp only [hgetpo, symOrStr, procClosure?, dmPobj, String.reduceBEq,
        Bool.false_eq_true, if_false, reduceIte, hdo₁, if_true]
      simp only [show (dmPcl m).body = dmBody from rfl, hlf,
        Bool.true_eq_false, if_true, reduceIte]
      simp [dmM₂, dmMd, dmM₁, dmPcl, dmBody, withCtl]]
  rw [h1, h2, h3]

/-- `TypeAgree` composes; local to this file because the two-write step (alloc
    then `defineMethod`) is the first to need it. -/
theorem typeAgree_trans {a b c : Heap} (h1 : TypeAgree a b) (h2 : TypeAgree b c) :
    TypeAgree a c := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := h1
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := h2
  refine ⟨fun o ho => (d1 o (Nat.lt_of_lt_of_le ho c8)).trans (c1 o ho),
    fun k hk => (d2 k (Nat.lt_of_lt_of_le hk c8)).trans (c2 k hk),
    fun k hk => (d3 k (Nat.lt_of_lt_of_le hk c8)).trans (c3 k hk),
    fun o ho hp => d4 o (Nat.lt_of_lt_of_le ho c8) (c4 o ho hp),
    fun o ho hp => d5 o (Nat.lt_of_lt_of_le ho c8) (c5 o ho hp),
    fun k => (d6 k).trans (c6 k),
    fun o ho xs hx => d7 o (Nat.lt_of_lt_of_le ho c8) xs (c7 o ho xs hx),
    Nat.le_trans c8 d8⟩

/-- **The user-supplied semantic lemma** — the Rails claim's obligation. -/
theorem semAxiomsOk_dm : SemAxiomsOk [dmClaim] := by
  intro cl hcl ans D Γ top c hreq hfr
  simp only [List.mem_singleton] at hcl
  subst hcl
  obtain ⟨hccls, hicb, hnbk⟩ := hreq "String" rfl
  have hfresh : declaresName D "shout" = false := by
    simpa [dmClaim, shoutSig] using hfr ("String", "shout", shoutSig) (by simp [dmClaim])
  intro m Γs τw Γk htop hfs htab hsc hh hsat hstr hcls hbot hks hgl hclo hmf hsubw
    hsuE hk
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
  -- **J34's dividends**: the frame's `self` is the class object it names.
  have hself : (curFrame m).self = .ref (curFrame m).defmod := by
    rw [hcur]
    exact hscc.2.2.2.2.2.2.2.2.1 hicb hnbk
  have hctx : className m.heap (curFrame m).defmod = "String" := by
    rw [hcur, ← hccls]
    exact hscc.2.1 hnbk
  have hdo : (m.heap.classPayload? (curFrame m).defmod).isSome := by
    rw [hcur]; exact hscc.1
  have hcrefCur : Boot.objectId ∈ (curFrame m).cref := by
    rw [hcur]; exact hscc.2.2.2.2.1
  -- ## The step, reduced. `reifyBlock` first: one allocation.
  have hreify : reifyBlock m [] [] dmBody false = (.ref (m.heap.alloc (dmPobj m)).1, dmM₁ m) := by
    simp [reifyBlock, dmPcl, dmPobj, dmM₁]
  have hg₁ : PlainGrow m.heap (dmM₁ m).heap :=
    plainGrow_alloc m.heap (dmPobj m) (by simp [dmPobj]) rfl
  have hag₁ : TypeAgree m.heap (dmM₁ m).heap := typeAgree_of_plainGrow hg₁ hsat
  -- the alloc'd object reads back
  have hgetpo : (dmM₁ m).heap.get (m.heap.alloc (dmPobj m)).1 = dmPobj m := by
    simp [dmM₁, Heap.alloc, Heap.get, Array.getD]
  have hdo₁ : ((dmM₁ m).heap.classPayload? (curFrame m).defmod).isSome := by
    rw [hg₁.payload]; exact hdo
  -- the lookup miss, from `NoHook` after the allocation
  have hh₁ : NoHook (dmM₁ m).heap := NoHook_grow hg₁ hsat hh
  have hlkdm : lookup (dmM₁ m).heap (.ref (curFrame m).defmod) "define_method" = none :=
    hh₁.2 (curFrame m).defmod hdo₁ "define_method" (by simp [hookFreeNames])
  -- the class payload, named
  obtain ⟨cp, hcp⟩ : ∃ cp, ((dmM₁ m).heap.get (curFrame m).defmod).payload = .cls cp := by
    have := hdo₁
    unfold Heap.classPayload? at this
    revert this
    cases hpay : ((dmM₁ m).heap.get (curFrame m).defmod).payload <;> simp
  -- ## `evalExpr` on the claim is one step to the installed state.
  have hstep : evalExpr m dmE
      = .next (withCtl (dmM₂ m) (.value (.sym "shout"))) :=
    evalExpr_dm m (by rw [hdm, hself]) hdo₁ hcp hlkdm
  -- ## The invariant, re-established at the grown table — `defPromote`'s argument,
  -- with the reification's `PlainGrow` transport composed in front.
  have hha : ("shout" : String) ≠ "method_added" ∧ ("shout" : String) ≠ "define_method" :=
    ⟨by decide, by decide⟩
  have htab₁ : DeclsOkJ [dmClaim] D (dmM₁ m).heap := DeclsOkJ_grow hg₁ hsat htab
  have hsat₁ : Saturated (dmM₁ m).heap := Saturated_grow hg₁.shapeAgree hg₁.size hsat
  have hstr₁ : LitClsOk (dmM₁ m).heap := LitClsOk_grow hg₁ hstr
  have hcls₁ : ClassOk (dmM₁ m).heap := ClassOk_grow hg₁ hsat hcls
  have hctx₁ : className (dmM₁ m).heap (curFrame m).defmod = "String" := by
    rw [hg₁.className_eq]; exact hctx
  -- the installed MethodDef, named
  have hcrefmd : Boot.objectId ∈ (dmMd ((dmM₁ m).frames.getD (dmPcl m).captured
      default).cref (curFrame m).defmod m.preludeMode).cref := by
    show Boot.objectId ∈ (m.frames.getD (m.stack.headD 0) default).cref
    rw [hst]
    show Boot.objectId ∈ (m.frames.getD fid₀ default).cref
    rw [← hcur]; exact hcrefCur
  -- shorthands for the write
  have hmemS : ("String" : String) ∈ reopenableClasses := by decide
  -- ancestors of the definee still start at the definee, post-write
  have hchain : ∀ md : MethodDef, ∃ rest,
      ancestors (defineMethod (dmM₁ m).heap (curFrame m).defmod "shout" md)
        (curFrame m).defmod = (curFrame m).defmod :: rest := by
    intro md
    obtain ⟨k₀, cp₀, _, _, hnm₀, huniq₀, _, _, _, hreop₀⟩ :=
      (ClassOk_defineMethod (name := "shout") (md := md)
        (cls := (curFrame m).defmod) hcls₁).2.2 "String"
        (readable_of_reopenable hmemS)
    obtain ⟨-, hhead₀, -⟩ := hreop₀ hmemS
    have hdefk : (curFrame m).defmod = k₀ :=
      huniq₀ _ (by rw [classPayload?_isSome_defineMethod]; exact hdo₁)
        (by rw [className_defineMethod]; exact hctx₁)
    rw [hdefk] at hdo₁ hhead₀ ⊢
    cases hanc : ancestors (defineMethod (dmM₁ m).heap k₀ "shout" md) k₀ with
    | nil => rw [hanc] at hhead₀; exact absurd hhead₀ (by simp)
    | cons a rest =>
      rw [hanc] at hhead₀
      simp only [List.head?_cons, Option.some.injEq] at hhead₀
      exact ⟨rest, by rw [hhead₀]⟩
  -- the table, one row richer, still conforms after the write
  have hdecls : ∀ (md : MethodDef), md.owner = (curFrame m).defmod →
      md.builtin = none → md.undefined = false → md.visibility = .pub →
      md.params = [] → md.declared = [] → md.capturedFrame = none →
      md.body = dmBody → Boot.objectId ∈ md.cref → md.superName = none →
      DeclsOkJ [dmClaim] (addRow D "String" "shout" shoutSig)
        (defineMethod (dmM₁ m).heap (curFrame m).defmod "shout" md) := by
    intro md hown hb hu hvs hpar hdec hcap hbd hcref hsn
    refine DeclsOkJ_addRow_here (DeclsOkJ_defineMethod htab₁ hfresh) hfresh rfl ?_
    intro τ0 hk0
    have hτ0 : τ0 = .cls "String" := by
      cases τ0 <;> simp only [tyClassNames] at hk0
      case cls n =>
        split at hk0
        · exact absurd hk0 (by simp)
        · simp only [List.cons.injEq, and_true] at hk0
          rw [hk0]
      all_goals exact absurd hk0 (by decide)
    subst hτ0
    obtain ⟨k₀, cp₀, _, _, hnm₀, huniq₀, _, _, _, _⟩ :=
      (ClassOk_defineMethod (name := "shout") (md := md)
        (cls := (curFrame m).defmod) hcls₁).2.2 "String"
        (readable_of_reopenable hmemS)
    have hctx' : className (defineMethod (dmM₁ m).heap (curFrame m).defmod "shout" md)
        (curFrame m).defmod = "String" := by
      rw [className_defineMethod]; exact hctx₁
    have hdefk : (curFrame m).defmod = k₀ :=
      huniq₀ _ (by rw [classPayload?_isSome_defineMethod]; exact hdo₁) hctx'
    obtain ⟨rest, hrest⟩ := hchain md
    refine Or.inr (Or.inl ⟨md, "String", UserKey.cls, fun k htc => ?_,
      by rw [hown]; exact hctx', rfl,
      rfl, by rw [hbd]; exact defFreeB_sound (n := 2) (by decide),
      by rw [hbd]; exact MFrag.int,
      by rw [hbd]; decide, ?_⟩)
    · have hkk : k = (curFrame m).defmod := by
        rw [hdefk]; exact huniq₀ k htc.1 htc.2
      subst hkk
      refine ⟨(curFrame m).defmod, ?_, hb, hu, hvs, hpar, hdec, hcap,
        by rw [hown, classPayload?_isSome_defineMethod]; exact hdo₁, ?_, hcref,
        by rw [hown, hrest]; exact List.mem_cons_self .., hsn⟩
      · show lookup.go _ "shout" (ancestors _ _) = _
        rw [hrest]
        exact lookup_go_defineMethod_self (dmM₁ m).heap _ "shout" md hdo₁ rest
      · split
        · rfl
        · rw [hrest]
          simp only [List.takeWhile, bne_self_eq_false, decide_false,
            Bool.false_eq_true, if_false]
          rfl
    · exact ⟨[], none, .int, by rw [hbd]; exact .int, SubJ.refl _,
        fun σ' h' => absurd h' (by simp)⟩
  -- assemble
  have hag₂ : TypeAgree m.heap (dmM₂ m).heap :=
    typeAgree_trans hag₁ (typeAgree_defineMethod _ _ _ _)
  show StepOkJ ans [dmClaim] (evalExpr m dmE)
  rw [hstep]
  show InvJ ans [dmClaim] (withCtl (dmM₂ m) (.value (.sym "shout")))
  refine ⟨NoHook_defineMethod hh₁ hha,
    Saturated_defineMethod hsat₁ _ _ _, LitClsOk_defineMethod hstr₁,
    ClassOk_defineMethod hcls₁,
    show BottomObj m.frames m.stack from hbot,
    show framePopLabels m.kont = m.stack.dropLast from hks,
    ClosuresOk.transport hclo
      (by intro κ hm cl' hcl'; simp only [withCtl] at hm; exact ⟨κ, hm, hcl'⟩)
      (by simp only [withCtl]; exact Nat.le_refl _)
      (by intro p _; simp only [withCtl]; exact FrameShape.rfl' _)
      (by
        intro o ho
        show ((dmM₂ m).heap.classPayload? o).isSome = true
        exact (hag₂.2.2.1 o (classPayload?_isSome_lt ho)) ▸ ho),
    addRow D "String" "shout" shoutSig, c, Γk, Γs,
    hdecls _ rfl rfl rfl rfl rfl rfl rfl rfl hcrefmd rfl, ?_, ?_, ?_, ?_⟩
  · show FramesOkJ (dmM₂ m).heap m.frames m.stack (Γk :: Γs.map Prod.snd)
    exact FramesOkJ.heap_congr hag₂ hfs
  · show StackCtx (dmM₂ m).heap m.frames m.stack (jctxs c Γs)
    exact StackCtx.heap_congr hag₂ hsc
  · exact GlobalsOk.congr hag₂ hgl
  · show ∃ σ' Γk', VTy (dmM₂ m).heap (Value.sym "shout") σ' ∧ SubEnv Γk' Γk ∧
        KontOkJ ans [dmClaim] (addRow D "String" "shout" shoutSig) (dmM₂ m).heap
          ((c, Γk') :: Γs) σ' m.kont
    exact ⟨_, _, VTy.weaken (VTy.exact rfl) hsubw, SubEnv.refl _,
      KontOkJ.heap_congr hag₂ hk⟩

end Judgment
end Proof
end RubyCore
