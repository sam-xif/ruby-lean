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
theorem judge_mono {A : SemAxioms} {D : Decls} {Γ : Env} {e : Expr} {top : Bool}
    {ctx : JCtx}
    {τ : Ty} {Γ' : Env} {D' : Decls} (hj : Judge A D Γ e top ctx τ Γ' D')
    (hmeth : ctx.meth.isSome = true)
    (hfh : fragHead e = true) :
    MFrag A e → defFree e = true → ∀ {D2 : Decls}, SubDecls D D2 →
      D' = D ∧ Judge A D2 Γ e top ctx τ Γ' D2 := by
  refine Judge.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_2 := fun D Γ ro top ctx τ Γ' D' _ =>
      ctx.meth.isSome = true →
      (∀ r, ro = some r → fragHead r = true ∧ MFrag A r ∧ defFree r = true) →
        ∀ {D2 : Decls}, SubDecls D D2 →
        D' = D ∧ JudgeRecv A D2 Γ ro top ctx τ Γ' D2)
    (motive_3 := fun D Γ es top ctx τ Γ' D' _ =>
      ctx.meth.isSome = true →
      (∀ e' ∈ es, MFrag A e') → defFreeAll es = true → ∀ {D2 : Decls}, SubDecls D D2 →
        D' = D ∧ JudgeSeq A D2 Γ es top ctx τ Γ' D2)
    (motive_4 := fun D Γ es top ctx τs Γ' D' _ =>
      ctx.meth.isSome = true →
      (∀ e' ∈ es, fragHead e' = true) →
      (∀ e' ∈ es, MFrag A e') → defFreeAll es = true → ∀ {D2 : Decls}, SubDecls D D2 →
        D' = D ∧ JudgeArgs A D2 Γ es top ctx τs Γ' D2)
    (motive_5 := fun D Γ es top ctx Γ' D' _ =>
      ctx.meth.isSome = true →
      (∀ e' ∈ es, fragHead e' = true) →
      (∀ e' ∈ es, MFrag A e') → defFreeAll es = true → ∀ {D2 : Decls}, SubDecls D D2 →
        D' = D ∧ JudgeElems A D2 Γ es top ctx Γ' D2)
    (motive_6 := fun _ _ _ _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ _ _ _ _ => True)
    (motive_8 := fun _ _ _ _ _ _ _ => True)
    (motive_9 := fun _ _ _ _ _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ _ _ => True)
    (motive_11 := fun D Γ e top ctx τ Γ' D' _ =>
      ctx.meth.isSome = true →
      fragHead e = true →
      MFrag A e → defFree e = true → ∀ {D2 : Decls}, SubDecls D D2 →
        D' = D ∧ Judge A D2 Γ e top ctx τ Γ' D2)
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
    ?hdefined ?harray ?hhash ?hseq ?hsub ?hsemantic
    hj hmeth hfh
  -- The auxiliary relations whose motives are `True`.
  all_goals try (intros; trivial)
  -- J31: the semantic leaf is table-generic — reapply at the grown table.
  case hsemantic =>
    intro D Γ top ctx cl hmem hff hreq hfr hdisc hmeth2 _ _ _ D2 _
    have hrows : cl.rows = [] := by
      rcases hdisc with h | h
      · exact h
      · rw [h] at hmeth2; exact Bool.noConfusion hmeth2
    refine ⟨by simp [hrows, addRows], ?_⟩
    have hsem : Judge A D2 Γ cl.e top ctx cl.τ Γ (addRows D2 cl.rows) :=
      .semantic hmem hff hreq (by rw [hrows]; simp) (Or.inl hrows)
    simp only [hrows, addRows, List.foldl] at hsem
    exact hsem
  -- JudgeRecv
  case _ =>  -- self
    intro D Γ top ctx cc hcc _ _ D2 _
    exact ⟨rfl, .self hcc⟩
  case _ =>  -- expl
    intro D Γ r top ctx τ Γ' D' hr ih hmeth2 hro D2 hs
    obtain ⟨rfl, hr2⟩ := ih hmeth2 (hro r rfl).1 (hro r rfl).2.1 (hro r rfl).2.2 hs
    exact ⟨rfl, .expl hr2⟩
  -- JudgeSeq
  case _ =>  -- nil
    intro D Γ top ctx _ _ _ D2 _
    exact ⟨rfl, .nil⟩
  case _ =>  -- single
    intro D Γ e top ctx τ Γ' D' h1 hcpl ih hmeth2 hm hdf D2 hs
    by_cases hfe : fragHead e = true
    · obtain ⟨rfl, h2⟩ := ih hmeth2 hfe (hm e (by simp)) (by simpa [defFreeAll] using hdf) hs
      exact ⟨rfl, .single h2 (hcpl := fun hh => Bool.noConfusion (hfe.symm.trans hh))⟩
    · -- a claimed element: rebuild via the semantic leaf, canonical by the coupling
      replace hfe : fragHead e = false := by simpa using hfe
      obtain ⟨cl, hclA, rfl, rfl, rfl, hD', hdisc, hreq, hfr⟩ := hcpl hfe
      have hrows : cl.rows = [] := by
        rcases hdisc with h | h
        · exact h
        · rw [h] at hmeth2; exact Bool.noConfusion hmeth2
      subst hD'
      refine ⟨by simp [hrows, addRows], ?_⟩
      have hsem : Judge A D2 Γ' cl.e top ctx cl.τ Γ' (addRows D2 cl.rows) :=
        .semantic hclA hfe hreq (by rw [hrows]; simp) (Or.inl hrows)
      simp only [hrows, addRows, List.foldl] at hsem
      exact .single hsem
        (hcpl := fun _ => ⟨cl, hclA, rfl, rfl, rfl, by simp [hrows, addRows],
          Or.inl hrows, hreq, by rw [hrows]; simp⟩)
  case _ =>  -- cons
    intro D Γ e e₂ rest top ctx τ₁ Γ₁ D₁ τ Γ' D' h1 hrest hcpl ih1 ihr hmeth2 hm hdf D2 hs
    simp only [defFreeAll, Bool.and_eq_true] at hdf
    by_cases hfe : fragHead e = true
    · obtain ⟨rfl, h1'⟩ := ih1 hmeth2 hfe (hm e (by simp)) hdf.1 hs
      obtain ⟨rfl, hr'⟩ := ihr hmeth2 (fun e' he' => hm e' (by simp [he']))
        (by simp only [defFreeAll, Bool.and_eq_true]; exact hdf.2) hs
      exact ⟨rfl, .cons h1' hr' (hcpl := fun hh => Bool.noConfusion (hfe.symm.trans hh))⟩
    · replace hfe : fragHead e = false := by simpa using hfe
      obtain ⟨cl, hclA, rfl, rfl, rfl, hD₁, hdisc, hreq, hfr⟩ := hcpl hfe
      have hrows : cl.rows = [] := by
        rcases hdisc with h | h
        · exact h
        · rw [h] at hmeth2; exact Bool.noConfusion hmeth2
      simp only [hrows, addRows, List.foldl] at hD₁
      have hD₁' : D₁ = D := hD₁
      subst hD₁'
      obtain ⟨rfl, hr'⟩ := ihr hmeth2 (fun e' he' => hm e' (by simp [he']))
        (by simp only [defFreeAll, Bool.and_eq_true]; exact hdf.2) hs
      have hsem : Judge A D2 Γ₁ cl.e top ctx cl.τ Γ₁ (addRows D2 cl.rows) :=
        .semantic hclA hfe hreq (by rw [hrows]; simp) (Or.inl hrows)
      simp only [hrows, addRows, List.foldl] at hsem
      exact ⟨rfl, .cons hsem hr'
        (hcpl := fun _ => ⟨cl, hclA, rfl, rfl, rfl, by simp [hrows, addRows],
          Or.inl hrows, hreq, by rw [hrows]; simp⟩)⟩
  -- JudgeArgs
  case _ =>  -- nil
    intro D Γ top ctx _ _ _ _ D2 _
    exact ⟨rfl, .nil⟩
  case _ =>  -- cons
    intro D Γ e rest top ctx τ Γ₁ D₁ τs Γ' D' h1 hrest ih1 ihr hmeth2 hfa hm hdf D2 hs
    simp only [defFreeAll, Bool.and_eq_true] at hdf
    obtain ⟨rfl, h1'⟩ := ih1 hmeth2 (hfa e (by simp)) (hm e (by simp)) hdf.1 hs
    obtain ⟨rfl, hr'⟩ := ihr hmeth2 (fun e' he' => hfa e' (by simp [he']))
      (fun e' he' => hm e' (by simp [he'])) hdf.2 hs
    exact ⟨rfl, .cons h1' hr'⟩
  -- JudgeElems
  case _ =>  -- nil
    intro D Γ top ctx _ _ _ _ D2 _
    exact ⟨rfl, .nil⟩
  case _ =>  -- cons
    intro D Γ e rest top ctx τ Γ₁ D₁ Γ' D' h1 hrest ih1 ihr hmeth2 hfa hm hdf D2 hs
    simp only [defFreeAll, Bool.and_eq_true] at hdf
    obtain ⟨rfl, h1'⟩ := ih1 hmeth2 (hfa e (by simp)) (hm e (by simp)) hdf.1 hs
    obtain ⟨rfl, hr'⟩ := ihr hmeth2 (fun e' he' => hfa e' (by simp [he']))
      (fun e' he' => hm e' (by simp [he'])) hdf.2 hs
    exact ⟨rfl, .cons h1' hr'⟩
  -- Judge: the fragment heads.
  case hint => exact fun _ _ _ _ _ hs => ⟨rfl, .int⟩
  case hflt => exact fun _ _ _ _ _ hs => ⟨rfl, .flt⟩
  case hstr => exact fun _ _ _ _ _ hs => ⟨rfl, .str⟩
  case hsym => exact fun _ _ _ _ _ hs => ⟨rfl, .sym⟩
  case htru => exact fun _ _ _ _ _ hs => ⟨rfl, .tru⟩
  case hfls => exact fun _ _ _ _ _ hs => ⟨rfl, .fls⟩
  case hnil => exact fun _ _ _ _ _ hs => ⟨rfl, .nil⟩
  case hself =>
    intro D Γ top ctx cc hcc _ _ _ _ D2 _
    exact ⟨rfl, .self hcc⟩
  case hvarLvar =>
    intro D Γ x top ctx τ0 hget _ _ _ _ D2 _
    exact ⟨rfl, .varLvar hget⟩
  case hvasgnLvar =>
    intro D Γ x rhs top ctx τ0 Γ₁ D₁ hib hrhs ih hmeth2 hfhx hmf hdf D2 hs
    cases hmf with
    | semantic hmem hff => simp [fragHead] at hff
    | vasgnLvar hfr hmr =>
      obtain ⟨rfl, h2⟩ := ih hmeth2 hfr hmr (by simpa [defFree] using hdf) hs
      exact ⟨rfl, .vasgnLvar hib h2⟩
  case hconst =>
    intro D Γ nm top ctx τ0 hre _ _ _ _ D2 hs
    exact ⟨rfl, .const (by rw [hs.constTy_eq]; exact hre)⟩
  case hcpathAbs =>
    intro D Γ nm top ctx τ0 hre _ _ _ _ D2 hs
    exact ⟨rfl, .cpathAbs (by rw [hs.constTy_eq]; exact hre)⟩
  case hcpathScoped =>
    intro D Γ base nm top ctx cname Γ₁ D₁ τ0 hbase hsco ih hmeth2 hfhx hmf hdf D2 hs
    cases hmf with
    | semantic hmem hff => simp [fragHead] at hff
    | cpathScoped hfb hmb =>
      obtain ⟨rfl, h2⟩ := ih hmeth2 hfb hmb (by simpa [defFree] using hdf) hs
      exact ⟨rfl, .cpathScoped h2 (by rw [hs.scopedConstTy_eq]; exact hsco)⟩
  case hvarIvar =>
    intro D Γ x top ctx cc σ hcc hiv _ _ _ _ D2 hs
    exact ⟨rfl, .varIvar hcc (by rw [hs.ivarTy_eq]; exact hiv)⟩
  case hvarGvar =>
    intro D Γ x top ctx σ hpg hgt _ _ _ _ D2 hs
    exact ⟨rfl, .varGvar hpg (by rw [hs.globalTy_eq]; exact hgt)⟩
  case hvasgnIvarDecl =>
    intro D Γ x rhs top ctx cc τ0 Γ₁ D₁ σ hcc hrhs hiv hsj ih hmeth2 hfhx hmf hdf D2 hs
    cases hmf with
    | semantic hmem hff => simp [fragHead] at hff
    | vasgnIvar hfr hmr =>
      obtain ⟨rfl, h2⟩ := ih hmeth2 hfr hmr (by simpa [defFree] using hdf) hs
      exact ⟨rfl, .vasgnIvarDecl hcc h2 (by rw [hs.ivarTy_eq]; exact hiv) hsj⟩
  case hvasgnIvarFresh =>
    intro D Γ x rhs top ctx cc τ0 Γ₁ D₁ hcc hrhs hiv ih hmeth2 hfhx hmf hdf D2 hs
    cases hmf with
    | semantic hmem hff => simp [fragHead] at hff
    | vasgnIvar hfr hmr =>
      obtain ⟨rfl, h2⟩ := ih hmeth2 hfr hmr (by simpa [defFree] using hdf) hs
      exact ⟨rfl, .vasgnIvarFresh hcc h2 (by rw [hs.ivarTy_eq]; exact hiv)⟩
  case hvasgnGvar =>
    intro D Γ x rhs top ctx τ0 Γ₁ D₁ σ hpg hrhs hgt hsj ih hmeth2 hfhx hmf hdf D2 hs
    cases hmf with
    | semantic hmem hff => simp [fragHead] at hff
    | vasgnGvar hfr hmr =>
      obtain ⟨rfl, h2⟩ := ih hmeth2 hfr hmr (by simpa [defFree] using hdf) hs
      exact ⟨rfl, .vasgnGvar hpg h2 (by rw [hs.globalTy_eq]; exact hgt) hsj⟩
  case harray =>
    intro D Γ es top ctx Γ' D'0 hje ih hmeth2 hfhx hmf hdf D2 hs
    cases hmf with
    | semantic hmem hff => simp [fragHead] at hff
    | array hfa hall =>
      obtain ⟨rfl, h2⟩ := ih hmeth2 (fun e' he' => hfa e' he') hall (by simpa [defFree] using hdf) hs
      exact ⟨rfl, .array h2⟩
  case hvcall =>
    intro D Γ mname top ctx cc τret hcc hsg _ _ _ _ D2 hs
    exact ⟨rfl, .vcall hcc (hs.sigOf_eq hsg)⟩
  case hseq =>
    intro D Γ es top ctx τ0 Γ' D'0 hseq ih hmeth2 hfhx hmf hdf D2 hs
    cases hmf with
    | semantic hmem hff => simp [fragHead] at hff
    | seq hall =>
      obtain ⟨rfl, h2⟩ := ih hmeth2 hall (by simpa [defFree] using hdf) hs
      exact ⟨rfl, .seq h2⟩
  case hifElse =>
    intro D Γ cond t els top ctx τc Γ₁ D₁ τt Γt Dt τe Γe τj Γc
    intro hcnd ht he hjt hje hct hce ihc iht ihe
    intro hmeth2 hfhx hmf hdf D2 hs
    cases hmf with
    | semantic hmem hff => simp [fragHead] at hff
    | ifElse hfc hft hfe hmc hmt hme =>
      simp only [defFree, Bool.and_eq_true] at hdf
      obtain ⟨rfl, hc'⟩ := ihc hmeth2 hfc hmc hdf.1.1 hs
      obtain ⟨rfl, ht'⟩ := iht hmeth2 hft hmt hdf.1.2 hs
      obtain ⟨-, he'⟩ := ihe hmeth2 hfe hme hdf.2 hs
      exact ⟨rfl, .ifElse hc' ht' he' hjt hje hct hce⟩
  case hifNone =>
    intro D Γ cond t top ctx τc Γ₁ D₁ τt Γt τj Γc
    intro hcnd ht hjt hjn hct hcΓ ihc iht
    intro hmeth2 hfhx hmf hdf D2 hs
    cases hmf with
    | semantic hmem hff => simp [fragHead] at hff
    | ifNone hfc hft hmc hmt =>
      simp only [defFree, Bool.and_eq_true] at hdf
      obtain ⟨rfl, hc'⟩ := ihc hmeth2 hfc hmc hdf.1.1 hs
      obtain ⟨-, ht'⟩ := iht hmeth2 hft hmt hdf.1.2 hs
      exact ⟨rfl, .ifNone hc' ht' hjt hjn hct hcΓ⟩
  case hifNarrowElse =>
    intro D Γ x t els top ctx τ0 τt Γt Dt τe Γe τj Γc
    intro hget ht he hjt hje hct hce iht ihe
    intro hmeth2 hfhx hmf hdf D2 hs
    cases hmf with
    | semantic hmem hff => simp [fragHead] at hff
    | ifElse hfc hft hfe hmc hmt hme =>
      simp only [defFree, Bool.and_eq_true] at hdf
      obtain ⟨rfl, ht'⟩ := iht hmeth2 hft hmt hdf.1.2 hs
      obtain ⟨-, he'⟩ := ihe hmeth2 hfe hme hdf.2 hs
      exact ⟨rfl, .ifNarrowElse hget ht' he' hjt hje hct hce⟩
  case hifNarrowNone =>
    intro D Γ x t top ctx τ0 τt Γt τj Γc
    intro hget ht hjt hjn hct hcΓ iht
    intro hmeth2 hfhx hmf hdf D2 hs
    cases hmf with
    | semantic hmem hff => simp [fragHead] at hff
    | ifNone hfc hft hmc hmt =>
      simp only [defFree, Bool.and_eq_true] at hdf
      obtain ⟨-, ht'⟩ := iht hmeth2 hft hmt hdf.1.2 hs
      exact ⟨rfl, .ifNarrowNone hget ht' hjt hjn hct hcΓ⟩
  case hwhile =>
    intro D Γ Γl cond body top ctx τc Γ₁ τb Γ₂
    intro hentry hcnd hs1 hbody hs2 ihc ihb
    intro hmeth2 hfhx hmf hdf D2 hs
    cases hmf with
    | semantic hmem hff => simp [fragHead] at hff
    | while' hfc hfb hmc hmb =>
      simp only [defFree, Bool.and_eq_true] at hdf
      obtain ⟨-, hc'⟩ := ihc hmeth2 hfc hmc hdf.1 hs
      obtain ⟨-, hb'⟩ := ihb hmeth2 hfb hmb hdf.2 hs
      exact ⟨rfl, .while' hentry hc' hs1 hb' hs2⟩
  case hsend =>
    intro D Γ recvO mname args top ctx τr Γ₁ D₁ τs Γ₂ D₂ ps τret
    intro hrecv hargs hsg hsub ihr iha
    intro hmeth2 hfhx hmf hdf D2 hs
    have hro : ∀ r, recvO = some r → fragHead r = true ∧ MFrag A r ∧ defFree r = true := by
      intro r hr
      subst hr
      cases hmf with
      | semantic hmem hff => simp [fragHead] at hff
      | send hne hfr _ hmr hma =>
        simp only [defFree, Bool.and_eq_true] at hdf
        exact ⟨hfr, hmr, hdf.1.1⟩
    have hma : ∀ a ∈ args, MFrag A a := by
      cases hmf with
      | semantic hmem hff => simp [fragHead] at hff
      | send _ _ _ _ hma => exact hma
      | sendImplicit _ hma => exact hma
    have hfa : ∀ a ∈ args, fragHead a = true := by
      cases hmf with
      | semantic hmem hff => simp [fragHead] at hff
      | send _ _ hfa _ _ => exact hfa
      | sendImplicit hfa _ => exact hfa
    have hdfa : defFreeAll args = true := by
      cases hrecv with
      | expl _ =>
        simp only [defFree, Bool.and_eq_true] at hdf
        exact hdf.1.2
      | self _ =>
        simp only [defFree, Bool.and_eq_true] at hdf
        exact hdf.1.2
    obtain ⟨rfl, hr'⟩ := ihr hmeth2 hro hs
    obtain ⟨rfl, ha'⟩ := iha hmeth2 hfa hma hdfa hs
    exact ⟨rfl, .send hr' ha' (hs.sigOf_eq hsg) hsub⟩
  case hsendCall =>
    intro D Γ r args top ctx τr Γ₁ D₁ τs Γ₂ D₂ ps ret hr hparts hargs hsub ihr iha hmeth2 hfhx hmf
    cases hmf with
    | semantic hmem hff => simp [fragHead] at hff
    | send hne _ _ _ _ => exact absurd rfl hne
  case hsub =>
    intro D Γ e top ctx τ0 Γ'0 D'0 σ Γ'' hj0 hsj hse ih hmeth2 hfhx hmf hdf D2 hs
    obtain ⟨rfl, h2⟩ := ih hmeth2 hfhx hmf hdf hs
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
    (hs : SubDecls D D') (he : EntryOkJ A D h τ n d) : EntryOkJ A D' h τ n d := by
  rcases he with hb | ⟨mdu, cu, htys, hres, hnm, hconf⟩ | hi
  · exact Or.inl hb
  · refine Or.inr (Or.inl ⟨mdu, cu, htys, hres, hnm,
      hconf.1, hconf.2.1, hconf.2.2.1, hconf.2.2.2.1, hconf.2.2.2.2.1, ?_⟩)
    obtain ⟨Γ', r, τb, hbo, hsb, hag⟩ := hconf.2.2.2.2.2
    obtain ⟨-, hbo'⟩ := judge_mono hbo (by simp [methodCtx]) hconf.2.2.2.2.1 hconf.2.2.2.1 hconf.2.2.1 hs
    exact ⟨Γ', r, τb, hbo', hsb, hag⟩
  · exact Or.inr (Or.inr hi)

/-- `DeclsOk_of_subDecls`, J-flavored: old rows by `EntryOkJ_mono`, new rows by
    hypothesis; groundness of the new rows likewise. -/
theorem DeclsOkJ_of_subDecls {D D' : Decls} {h : Heap} (hd : DeclsOkJ A D h)
    (hs : SubDecls D D')
    (hnew : ∀ τ n d, declFor D τ n = none → declFor D' τ n = some d →
      EntryOkJ A D' h τ n d ∧ ∀ p ∈ d.params, groundTy p = true) :
    DeclsOkJ A D' h := by
  refine ⟨fun τ n d hdf => ?_,
    fun n τ hn => hd.2.1 n τ (by rw [← hs.constTy_eq]; exact hn),
    fun c x τ hn => hd.2.2.1 c x τ (by rw [← hs.ivarTy_eq]; exact hn),
    fun c n τ hn => hd.2.2.2.1 c n τ (by rw [← hs.scopedConstTy_eq]; exact hn),
    fun c n dd hn => hd.2.2.2.2.1 c n dd (by rw [← hs.superDecl_eq]; exact hn),
    fun τ n d hdf => ?_,
    fun c x τ hn => hd.2.2.2.2.2.2.1 c x τ (by rw [← hs.ivarTy_eq]; exact hn),
    fun x τ hn => hd.2.2.2.2.2.2.2 x τ (by rw [← hs.globalTy_eq]; exact hn)⟩
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
      exact hd.2.2.2.2.2.1 τ n d0 hold

/-- `DeclsOk_defineMethod`, J-flavored — a method-table write at an *undeclared*
    name moves nothing the table invariant reads; the user arm's conformance is
    heap-free and passes through. -/
theorem DeclsOkJ_defineMethod {D : Decls} {h : Heap} {cls : ObjId} {name : String}
    {md : MethodDef} (hd : DeclsOkJ A D h) (hfresh : declaresName D name = false) :
    DeclsOkJ A D (defineMethod h cls name md) := by
  refine ⟨?_, fun n τ hn => constOk_defineMethod (hd.2.1 n τ hn),
    fun c x τ hn => ivarOk_defineMethod (hd.2.2.1 c x τ hn),
    fun c nn τ hn => scopedConstOk_defineMethod (hd.2.2.2.1 c nn τ hn),
    fun c nn dd hn => superOk_defineMethod (hd.2.2.2.2.1 c nn dd hn)
      (fun heq => by
        rw [heq] at hn
        exact absurd (superDecl?_declaresName hn) (by simp [hfresh])),
    hd.2.2.2.2.2.1, hd.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2⟩
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
    (hd : DeclsOkJ A D h) (hfresh : declaresName D name = false)
    (hσp : σ.params = [])
    (hnew : ∀ τ0, tyClassNames τ0 = [c] → EntryOkJ A (addRow D c name σ) h τ0 name σ) :
    DeclsOkJ A (addRow D c name σ) h := by
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
