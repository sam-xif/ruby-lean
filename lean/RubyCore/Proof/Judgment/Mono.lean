import RubyCore.Proof.Judgment.Konts

/-!
# Table monotonicity over the fragment (J23)

The `def`-promotion step grows the table, and everything already judged must
survive: the old rows' `UserConformsJ` bodies and the promoted body itself have to
re-judge at `addRow D …`. This is `infer_mono`'s role (Proof/Static/Decls.lean §3c),
restated over the relation — and here the fragment gate earns its keep a second
time: `Judge`'s *own* rule set is not monotone (`alias'`/`defDecl`/`defPromote`
carry negative `declaresName` premises, and the definition heads thread tables), but
every rule reachable at an `MFrag ∧ defFree` expression reads the table only through
`sigOf`, which `SubDecls` preserves. So the hypotheses are exactly the two the
conformance predicate already carries, and the out-of-fragment constructors are
refuted by `cases` on the gate rather than reasoned about.
-/

namespace RubyCore
namespace Proof
namespace Judgment

open Interp
open RubyCore.Types
open RubyCore.Judgment
open RubyCore.Proof.Static

set_option maxRecDepth 100000

/-- `sigOf` is monotone along `SubDecls` — both of a nilable receiver's rows
    transport by the `declFor` clause, everything else is one transported read. -/
theorem SubDecls.sigOf_eq {F F' : Decls} (hs : SubDecls F F') {τ : Ty} {mname : String}
    {ps : List Ty} {τret : Ty}
    (h : sigOf F τ mname = some (ps, τret)) : sigOf F' τ mname = some (ps, τret) := by
  cases τ with
  | nilable σ =>
    obtain ⟨h1, h2⟩ := sigOf_nilable h
    have h1' := hs.1 _ _ _ h1
    have h2' := hs.1 _ _ _ h2
    simp [sigOf, h1', h2']
  | _ =>
    simp only [sigOf] at h ⊢
    cases hdf : declFor F _ mname with
    | none => rw [hdf] at h; exact absurd h (by simp)
    | some d =>
      rw [hdf] at h
      rw [hs.1 _ _ _ hdf]
      exact h

set_option maxHeartbeats 2000000 in
/-- **`Judge` is monotone in the table over the gated fragment** — with the table
    thread pinned (`D' = D`; nothing in the fragment grows it). One `Judge.rec`
    induction; the shape mirrors `judge_eval_ok`'s. -/
theorem judge_mono {D : Decls} {Γ : Env} {e : Expr} {top : Bool} {ctx : JCtx}
    {τ : Ty} {Γ' : Env} {D' : Decls} (hj : Judge D Γ e top ctx τ Γ' D') :
    MFrag e → defFree e = true → ∀ {D2 : Decls}, SubDecls D D2 →
      D' = D ∧ Judge D2 Γ e top ctx τ Γ' D2 := by
  refine Judge.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_2 := fun D Γ ro top ctx τ Γ' D' _ =>
      (∀ r, ro = some r → MFrag r ∧ defFree r = true) → ∀ {D2 : Decls}, SubDecls D D2 →
        D' = D ∧ JudgeRecv D2 Γ ro top ctx τ Γ' D2)
    (motive_3 := fun D Γ es top ctx τ Γ' D' _ =>
      (∀ e' ∈ es, MFrag e') → defFreeAll es = true → ∀ {D2 : Decls}, SubDecls D D2 →
        D' = D ∧ JudgeSeq D2 Γ es top ctx τ Γ' D2)
    (motive_4 := fun D Γ es top ctx τs Γ' D' _ =>
      (∀ e' ∈ es, MFrag e') → defFreeAll es = true → ∀ {D2 : Decls}, SubDecls D D2 →
        D' = D ∧ JudgeArgs D2 Γ es top ctx τs Γ' D2)
    (motive_5 := fun _ _ _ _ _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ _ _ _ _ => True)
    (motive_8 := fun _ _ _ _ _ _ _ => True)
    (motive_9 := fun _ _ _ _ _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ _ _ => True)
    (motive_11 := fun D Γ e top ctx τ Γ' D' _ =>
      MFrag e → defFree e = true → ∀ {D2 : Decls}, SubDecls D D2 →
        D' = D ∧ Judge D2 Γ e top ctx τ Γ' D2)
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
  -- The auxiliary relations whose motives are `True`.
  all_goals try (intros; trivial)
  -- JudgeRecv
  case _ =>  -- self
    intro D Γ top ctx cc hcc _ D2 _
    exact ⟨rfl, .self hcc⟩
  case _ =>  -- expl
    intro D Γ r top ctx τ Γ' D' hr ih hro D2 hs
    obtain ⟨rfl, hr2⟩ := ih (hro r rfl).1 (hro r rfl).2 hs
    exact ⟨rfl, .expl hr2⟩
  -- JudgeSeq
  case _ =>  -- nil
    intro D Γ top ctx _ _ D2 _
    exact ⟨rfl, .nil⟩
  case _ =>  -- single
    intro D Γ e top ctx τ Γ' D' h1 ih hm hdf D2 hs
    obtain ⟨rfl, h2⟩ := ih (hm e (by simp)) (by simpa [defFreeAll] using hdf) hs
    exact ⟨rfl, .single h2⟩
  case _ =>  -- cons
    intro D Γ e e₂ rest top ctx τ₁ Γ₁ D₁ τ Γ' D' h1 hrest ih1 ihr hm hdf D2 hs
    simp only [defFreeAll, Bool.and_eq_true] at hdf
    obtain ⟨rfl, h1'⟩ := ih1 (hm e (by simp)) hdf.1 hs
    obtain ⟨rfl, hr'⟩ := ihr (fun e' he' => hm e' (by simp [he']))
      (by simp only [defFreeAll, Bool.and_eq_true]; exact hdf.2) hs
    exact ⟨rfl, .cons h1' hr'⟩
  -- JudgeArgs
  case _ =>  -- nil
    intro D Γ top ctx _ _ D2 _
    exact ⟨rfl, .nil⟩
  case _ =>  -- cons
    intro D Γ e rest top ctx τ Γ₁ D₁ τs Γ' D' h1 hrest ih1 ihr hm hdf D2 hs
    simp only [defFreeAll, Bool.and_eq_true] at hdf
    obtain ⟨rfl, h1'⟩ := ih1 (hm e (by simp)) hdf.1 hs
    obtain ⟨rfl, hr'⟩ := ihr (fun e' he' => hm e' (by simp [he'])) hdf.2 hs
    exact ⟨rfl, .cons h1' hr'⟩
  -- Judge: the fragment heads.
  case hint => exact fun _ _ _ hs => ⟨rfl, .int⟩
  case hflt => exact fun _ _ _ hs => ⟨rfl, .flt⟩
  case hstr => exact fun _ _ _ hs => ⟨rfl, .str⟩
  case hsym => exact fun _ _ _ hs => ⟨rfl, .sym⟩
  case htru => exact fun _ _ _ hs => ⟨rfl, .tru⟩
  case hfls => exact fun _ _ _ hs => ⟨rfl, .fls⟩
  case hnil => exact fun _ _ _ hs => ⟨rfl, .nil⟩
  case hself =>
    intro D Γ top ctx cc hcc _ _ D2 _
    exact ⟨rfl, .self hcc⟩
  case hvarLvar =>
    intro D Γ x top ctx τ0 hget _ _ D2 _
    exact ⟨rfl, .varLvar hget⟩
  case hvasgnLvar =>
    intro D Γ x rhs top ctx τ0 Γ₁ D₁ hib hrhs ih hmf hdf D2 hs
    cases hmf with
    | vasgnLvar hmr =>
      obtain ⟨rfl, h2⟩ := ih hmr (by simpa [defFree] using hdf) hs
      exact ⟨rfl, .vasgnLvar hib h2⟩
  case hvcall =>
    intro D Γ mname top ctx cc τret hcc hsg _ _ D2 hs
    exact ⟨rfl, .vcall hcc (hs.sigOf_eq hsg)⟩
  case hseq =>
    intro D Γ es top ctx τ0 Γ' D'0 hseq ih hmf hdf D2 hs
    cases hmf with
    | seq hall =>
      obtain ⟨rfl, h2⟩ := ih hall (by simpa [defFree] using hdf) hs
      exact ⟨rfl, .seq h2⟩
  case hifElse =>
    intro D Γ cond t els top ctx τc Γ₁ D₁ τt Γt Dt τe Γe τj Γc
    intro hcnd ht he hjt hje hct hce ihc iht ihe
    intro hmf hdf D2 hs
    cases hmf with
    | ifElse hshape hmc hmt hme =>
      simp only [defFree, Bool.and_eq_true] at hdf
      obtain ⟨rfl, hc'⟩ := ihc hmc hdf.1.1 hs
      obtain ⟨rfl, ht'⟩ := iht hmt hdf.1.2 hs
      obtain ⟨-, he'⟩ := ihe hme hdf.2 hs
      exact ⟨rfl, .ifElse hc' ht' he' hjt hje hct hce⟩
  case hifNone =>
    intro D Γ cond t top ctx τc Γ₁ D₁ τt Γt τj Γc
    intro hcnd ht hjt hjn hct hcΓ ihc iht
    intro hmf hdf D2 hs
    cases hmf with
    | ifNone hshape hmc hmt =>
      simp only [defFree, Bool.and_eq_true] at hdf
      obtain ⟨rfl, hc'⟩ := ihc hmc hdf.1.1 hs
      obtain ⟨-, ht'⟩ := iht hmt hdf.1.2 hs
      exact ⟨rfl, .ifNone hc' ht' hjt hjn hct hcΓ⟩
  case hifNarrowElse =>
    intro D Γ x t els top ctx τ0 τt Γt Dt τe Γe τj Γc
    intro hget ht he hjt hje hct hce iht ihe hmf
    cases hmf with
    | ifElse hshape _ _ _ => exact absurd rfl (hshape x)
  case hifNarrowNone =>
    intro D Γ x t top ctx τ0 τt Γt τj Γc
    intro hget ht hjt hjn hct hcΓ iht hmf
    cases hmf with
    | ifNone hshape _ _ => exact absurd rfl (hshape x)
  case hwhile =>
    intro D Γ Γl cond body top ctx τc Γ₁ τb Γ₂
    intro hentry hcnd hs1 hbody hs2 ihc ihb
    intro hmf hdf D2 hs
    cases hmf with
    | while' hmc hmb =>
      simp only [defFree, Bool.and_eq_true] at hdf
      obtain ⟨-, hc'⟩ := ihc hmc hdf.1 hs
      obtain ⟨-, hb'⟩ := ihb hmb hdf.2 hs
      exact ⟨rfl, .while' hentry hc' hs1 hb' hs2⟩
  case hsend =>
    intro D Γ recvO mname args top ctx τr Γ₁ D₁ τs Γ₂ D₂ ps τret
    intro hrecv hargs hsg hsub ihr iha
    intro hmf hdf D2 hs
    have hro : ∀ r, recvO = some r → MFrag r ∧ defFree r = true := by
      intro r hr
      subst hr
      cases hmf with
      | send hne hmr hma =>
        simp only [defFree, Bool.and_eq_true] at hdf
        exact ⟨hmr, hdf.1.1⟩
    have hma : ∀ a ∈ args, MFrag a := by
      cases hmf with
      | send _ _ hma => exact hma
      | sendImplicit hma => exact hma
    have hdfa : defFreeAll args = true := by
      cases hrecv with
      | expl _ =>
        simp only [defFree, Bool.and_eq_true] at hdf
        exact hdf.1.2
      | self _ =>
        simp only [defFree, Bool.and_eq_true] at hdf
        exact hdf.1.2
    obtain ⟨rfl, hr'⟩ := ihr hro hs
    obtain ⟨rfl, ha'⟩ := iha hma hdfa hs
    exact ⟨rfl, .send hr' ha' (hs.sigOf_eq hsg) hsub⟩
  case hsendCall =>
    intro D Γ r args top ctx τr Γ₁ D₁ τs Γ₂ D₂ ps ret hr hparts hargs hsub ihr iha hmf
    cases hmf with
    | send hne _ _ => exact absurd rfl hne
  case hsub =>
    intro D Γ e top ctx τ0 Γ'0 D'0 σ Γ'' hj0 hsj hse ih hmf hdf D2 hs
    obtain ⟨rfl, h2⟩ := ih hmf hdf hs
    exact ⟨rfl, .sub h2 hsj hse⟩
  -- Everything else is out of the gated fragment — refuted by the `MFrag` gate,
  -- or (for the definition heads, which are in `MFrag` but not `defFree`) by the
  -- `defFree` gate.
  all_goals
    (intros
     first
      | trivial
      | (refine absurd ?_ (fun (hq : MFrag _) => by cases hq)
         assumption)
      | (exact absurd ‹defFree _ = true› (by simp [defFree])))

/-! ## The table transports, J-flavored -/

/-- `EntryOk_mono` over the judgment: the user arm's body re-judges by
    `judge_mono`, whose two hypotheses `UserConformsJ` carries. -/
theorem EntryOkJ_mono {D D' : Decls} {h : Heap} {τ : Ty} {n : String} {d : MethodDecl}
    (hs : SubDecls D D') (he : EntryOkJ D h τ n d) : EntryOkJ D' h τ n d := by
  rcases he with hb | ⟨mdu, cu, htys, hres, hnm, hconf⟩ | hi
  · exact Or.inl hb
  · refine Or.inr (Or.inl ⟨mdu, cu, htys, hres, hnm,
      hconf.1, hconf.2.1, hconf.2.2.1, hconf.2.2.2.1, ?_⟩)
    obtain ⟨Γ', r, τb, hbo, hsb, hag⟩ := hconf.2.2.2.2
    obtain ⟨-, hbo'⟩ := judge_mono hbo hconf.2.2.2.1 hconf.2.2.1 hs
    exact ⟨Γ', r, τb, hbo', hsb, hag⟩
  · exact Or.inr (Or.inr hi)

/-- `DeclsOk_of_subDecls`, J-flavored: old rows by `EntryOkJ_mono`, new rows by
    hypothesis; groundness of the new rows likewise. -/
theorem DeclsOkJ_of_subDecls {D D' : Decls} {h : Heap} (hd : DeclsOkJ D h)
    (hs : SubDecls D D')
    (hnew : ∀ τ n d, declFor D τ n = none → declFor D' τ n = some d →
      EntryOkJ D' h τ n d ∧ ∀ p ∈ d.params, groundTy p = true) :
    DeclsOkJ D' h := by
  refine ⟨fun τ n d hdf => ?_,
    fun n τ hn => hd.2.1 n τ (by rw [← hs.constTy_eq]; exact hn),
    fun c x τ hn => hd.2.2.1 c x τ (by rw [← hs.ivarTy_eq]; exact hn),
    fun c n τ hn => hd.2.2.2.1 c n τ (by rw [← hs.scopedConstTy_eq]; exact hn),
    fun c n dd hn => hd.2.2.2.2.1 c n dd (by rw [← hs.superDecl_eq]; exact hn),
    fun τ n d hdf => ?_⟩
  · cases hold : declFor D τ n with
    | none => exact (hnew τ n d hold hdf).1
    | some d0 =>
      have heq := hs.1 τ n d0 hold
      rw [hdf] at heq
      have : d0 = d := (Option.some.inj heq).symm
      subst this
      exact EntryOkJ_mono hs (hd.1 τ n d0 hold)
  · cases hold : declFor D τ n with
    | none => exact (hnew τ n d hold hdf).2
    | some d0 =>
      have heq := hs.1 τ n d0 hold
      rw [hdf] at heq
      have : d0 = d := (Option.some.inj heq).symm
      subst this
      exact hd.2.2.2.2.2 τ n d0 hold

/-- `DeclsOk_defineMethod`, J-flavored — a method-table write at an *undeclared*
    name moves nothing the table invariant reads; the user arm's conformance is
    heap-free and passes through. -/
theorem DeclsOkJ_defineMethod {D : Decls} {h : Heap} {cls : ObjId} {name : String}
    {md : MethodDef} (hd : DeclsOkJ D h) (hfresh : declaresName D name = false) :
    DeclsOkJ D (defineMethod h cls name md) := by
  refine ⟨?_, fun n τ hn => constOk_defineMethod (hd.2.1 n τ hn),
    fun c x τ hn => ivarOk_defineMethod (hd.2.2.1 c x τ hn),
    fun c nn τ hn => scopedConstOk_defineMethod (hd.2.2.2.1 c nn τ hn),
    fun c nn dd hn => superOk_defineMethod (hd.2.2.2.2.1 c nn dd hn)
      (fun heq => by
        rw [heq] at hn
        exact absurd (superDecl?_declaresName hn) (by simp [hfresh])),
    hd.2.2.2.2.2⟩
  intro τr mname decl hdecl
  have hne : ¬ (mname = name) := by
    intro heq
    rw [heq] at hdecl
    exact absurd (declFor_declaresName hdecl) (by simp [hfresh])
  rcases hd.1 τr mname decl hdecl with ⟨bid, hres, hconf⟩ |
    ⟨mdu, cu, htys, hres, hnm, hconf⟩ | ⟨hτ, hmn, hdp, hdr, hdb, hmiss⟩
  · exact Or.inl ⟨bid,
      fun k ht => ResolvesAt_defineMethod (hres k (TyClass_defineMethod ht)) hne, hconf⟩
  · exact Or.inr (Or.inl ⟨mdu, cu, htys,
      fun k ht => ResolvesUser_defineMethod (hres k (TyClass_defineMethod ht)) hne,
      by rw [className_defineMethod]; exact hnm, hconf⟩)
  · exact Or.inr (Or.inr ⟨hτ, hmn, hdp, hdr, hdb, fun k ht => by
      have := hmiss k (TyClass_defineMethod ht)
      unfold MissesAt lookupIn at this ⊢
      rw [ancestors_defineMethod, lookup_go_defineMethod h cls name mname md hne]
      exact this⟩)

/-- `DeclsOk_addRow_here`, J-flavored: one row added at a fixed heap. -/
theorem DeclsOkJ_addRow_here {D : Decls} {h : Heap} {c name : String} {σ : MethodDecl}
    (hd : DeclsOkJ D h) (hfresh : declaresName D name = false)
    (hσp : σ.params = [])
    (hnew : ∀ τ0, tyClassNames τ0 = [c] → EntryOkJ (addRow D c name σ) h τ0 name σ) :
    DeclsOkJ (addRow D c name σ) h := by
  have hsub : SubDecls D (addRow D c name σ) := subDecls_addRow hfresh
  refine DeclsOkJ_of_subDecls hd hsub ?_
  intro τ n d hold hdf
  by_cases hmn : n = name
  · subst hmn
    obtain ⟨hk, rfl⟩ := declFor_addRow_self_inv hfresh hdf
    exact ⟨hnew τ hk, by rw [hσp]; intro p hp; simp at hp⟩
  · rw [← declFor_addRow_other (D := D) (c := c) (σ := σ) hmn τ] at hold
    rw [hold] at hdf
    exact absurd hdf (by simp)

end Judgment
end Proof
end RubyCore
