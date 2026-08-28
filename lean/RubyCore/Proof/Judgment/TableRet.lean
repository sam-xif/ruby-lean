import RubyCore.Judgment.Frag

/-!
# `judge_table_ret` (J39) — table stability from the context

L200's `infer_table_ret` over the relation: along a derivation whose context has
the return and method channels open, the table is constant. Its own file because
`KontOkJ.retOkJ` (Konts.lean) consumes it and `Mono.lean` sits above Konts.
The three siblings re-run the same motives through the mutual block's other
recursors — a relation costs one `.rec` application per eliminated family where
`infer.induct` covered all five functions at once; recorded as the price of §2's
trade.
-/

namespace RubyCore
namespace Proof
namespace Judgment

open RubyCore.Types
open RubyCore.Judgment

set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
/-- **Table stability from the context** (J39, mirroring L200's `infer_table_ret`):
    along a derivation whose context has the return channel **and** a method open,
    the table is constant. The two channel hypotheses are exactly what a `return`
    rule fires under (`Judge.retSome`/`retNil` carry both since J39), and they are
    what `KontOkJ.retOkJ`'s walk has in hand. Unlike `judge_mono` this is over the
    **whole relation** — no `MFrag`/`defFree` gate — because the only table-growing
    rules are `defPromote` (refuted by its own `ctx.ret = none` guard), `classTop`
    (refuted by `top = true`), and a row-bearing semantic claim (refuted by the J32
    rows/method disjunct at `meth.isSome`); every block/lambda body is pinned by
    its rule. -/
theorem judge_table_ret {A : SemAxioms} {D : Decls} {Γ : Env} {e : Expr} {top : Bool}
    {ctx : JCtx}
    {τ : Ty} {Γ' : Env} {D' : Decls} (hj : Judge A D Γ e top ctx τ Γ' D')
    (hret : ctx.ret.isSome = true) (hmeth : ctx.meth.isSome = true)
    (htop : top = false) : D' = D := by
  refine Judge.rec
    (motive_1 := fun D Γ ro top ctx τ Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_2 := fun D Γ ro top ctx τ Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_3 := fun D Γ es top ctx τ Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_4 := fun D Γ es top ctx τs Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_5 := fun D Γ es top ctx Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_6 := fun D Γ prs top ctx Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_7 := fun D Γ es top ctx Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_8 := fun _ _ _ _ _ _ _ => True)
    (motive_9 := fun _ _ _ _ _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ _ _ => True)
    (motive_11 := fun D Γ e top ctx τ Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?hint ?hflt ?hstr ?hsym ?htru ?hfls ?hnil ?hregexpLit ?hself
    ?hvarLvar ?hvarIvar ?hvarGvar ?hvarCvar
    ?hvasgnLvar ?hvasgnIvarDecl ?hvasgnIvarFresh ?hvasgnGvar ?hvasgnCvar
    ?hconst ?hcpathAbs ?hcpathScoped ?hcasgn ?hcasgnM ?hcpathAsgn
    ?hsend ?hsendIter0 ?hsendIterA ?hsendLambda ?hsendLambdaArrow ?hsendCall
    ?hsendBlockpass ?hvcall ?hkwargs ?hfwd ?hsplatAnon ?hsplatArray ?hsplatArrayOf
    ?hyield ?hifElse ?hifNone ?hifNarrowElse ?hifNarrowNone
    ?hwhile ?hdowhile ?hfor
    ?hretSome ?hretNil ?hnxtNil ?hnxtSome ?hbrkNil ?hbrkSome ?hretry ?hredo
    ?hdefDecl ?hdefPromote ?hdefs ?hclassTop ?hclassSup ?hmodule
    ?hscopedClass ?hscopedModule ?hsclass ?hbegin ?hsuper ?hzsuper ?halias
    ?hdefined ?harray ?hhash ?hseq ?hsub ?hsemantic
    hj hret hmeth htop
  case hsemantic =>
    intro D Γ top ctx cl hmem hff hreq hqm hfr hfn hdisc hret2 hmeth2 _
    have hrows : cl.rows = [] := by
      rcases hdisc with h | h
      · exact h.1
      · rw [h] at hmeth2; exact Bool.noConfusion hmeth2
    simp [hrows, addRows]
  all_goals
    (intros
     first
      | trivial
      | rfl
      | simp_all [loopCtx, rescueCtx])

set_option maxHeartbeats 4000000 in
/-- `judge_table_ret` at `JudgeSeq` (same motives, `JudgeSeq.rec`). -/
theorem judge_seq_table_ret {A : SemAxioms} {D : Decls} {Γ : Env} {es : List Expr} {top : Bool}
    {ctx : JCtx}
    {τ : Ty} {Γ' : Env} {D' : Decls} (hj : JudgeSeq A D Γ es top ctx τ Γ' D')
    (hret : ctx.ret.isSome = true) (hmeth : ctx.meth.isSome = true)
    (htop : top = false) : D' = D := by
  refine JudgeSeq.rec
    (motive_1 := fun D Γ ro top ctx τ Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_2 := fun D Γ ro top ctx τ Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_3 := fun D Γ es top ctx τ Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_4 := fun D Γ es top ctx τs Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_5 := fun D Γ es top ctx Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_6 := fun D Γ prs top ctx Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_7 := fun D Γ es top ctx Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_8 := fun _ _ _ _ _ _ _ => True)
    (motive_9 := fun _ _ _ _ _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ _ _ => True)
    (motive_11 := fun D Γ e top ctx τ Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?hint ?hflt ?hstr ?hsym ?htru ?hfls ?hnil ?hregexpLit ?hself
    ?hvarLvar ?hvarIvar ?hvarGvar ?hvarCvar
    ?hvasgnLvar ?hvasgnIvarDecl ?hvasgnIvarFresh ?hvasgnGvar ?hvasgnCvar
    ?hconst ?hcpathAbs ?hcpathScoped ?hcasgn ?hcasgnM ?hcpathAsgn
    ?hsend ?hsendIter0 ?hsendIterA ?hsendLambda ?hsendLambdaArrow ?hsendCall
    ?hsendBlockpass ?hvcall ?hkwargs ?hfwd ?hsplatAnon ?hsplatArray ?hsplatArrayOf
    ?hyield ?hifElse ?hifNone ?hifNarrowElse ?hifNarrowNone
    ?hwhile ?hdowhile ?hfor
    ?hretSome ?hretNil ?hnxtNil ?hnxtSome ?hbrkNil ?hbrkSome ?hretry ?hredo
    ?hdefDecl ?hdefPromote ?hdefs ?hclassTop ?hclassSup ?hmodule
    ?hscopedClass ?hscopedModule ?hsclass ?hbegin ?hsuper ?hzsuper ?halias
    ?hdefined ?harray ?hhash ?hseq ?hsub ?hsemantic
    hj hret hmeth htop
  case hsemantic =>
    intro D Γ top ctx cl hmem hff hreq hqm hfr hfn hdisc hret2 hmeth2 _
    have hrows : cl.rows = [] := by
      rcases hdisc with h | h
      · exact h.1
      · rw [h] at hmeth2; exact Bool.noConfusion hmeth2
    simp [hrows, addRows]
  all_goals
    (intros
     first
      | trivial
      | rfl
      | simp_all [loopCtx, rescueCtx])

set_option maxHeartbeats 4000000 in
/-- `judge_table_ret` at `JudgeArgs` (same motives, `JudgeArgs.rec`). -/
theorem judge_args_table_ret {A : SemAxioms} {D : Decls} {Γ : Env} {es : List Expr} {top : Bool}
    {ctx : JCtx}
    {τs : List Ty} {Γ' : Env} {D' : Decls} (hj : JudgeArgs A D Γ es top ctx τs Γ' D')
    (hret : ctx.ret.isSome = true) (hmeth : ctx.meth.isSome = true)
    (htop : top = false) : D' = D := by
  refine JudgeArgs.rec
    (motive_1 := fun D Γ ro top ctx τ Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_2 := fun D Γ ro top ctx τ Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_3 := fun D Γ es top ctx τ Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_4 := fun D Γ es top ctx τs Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_5 := fun D Γ es top ctx Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_6 := fun D Γ prs top ctx Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_7 := fun D Γ es top ctx Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_8 := fun _ _ _ _ _ _ _ => True)
    (motive_9 := fun _ _ _ _ _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ _ _ => True)
    (motive_11 := fun D Γ e top ctx τ Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?hint ?hflt ?hstr ?hsym ?htru ?hfls ?hnil ?hregexpLit ?hself
    ?hvarLvar ?hvarIvar ?hvarGvar ?hvarCvar
    ?hvasgnLvar ?hvasgnIvarDecl ?hvasgnIvarFresh ?hvasgnGvar ?hvasgnCvar
    ?hconst ?hcpathAbs ?hcpathScoped ?hcasgn ?hcasgnM ?hcpathAsgn
    ?hsend ?hsendIter0 ?hsendIterA ?hsendLambda ?hsendLambdaArrow ?hsendCall
    ?hsendBlockpass ?hvcall ?hkwargs ?hfwd ?hsplatAnon ?hsplatArray ?hsplatArrayOf
    ?hyield ?hifElse ?hifNone ?hifNarrowElse ?hifNarrowNone
    ?hwhile ?hdowhile ?hfor
    ?hretSome ?hretNil ?hnxtNil ?hnxtSome ?hbrkNil ?hbrkSome ?hretry ?hredo
    ?hdefDecl ?hdefPromote ?hdefs ?hclassTop ?hclassSup ?hmodule
    ?hscopedClass ?hscopedModule ?hsclass ?hbegin ?hsuper ?hzsuper ?halias
    ?hdefined ?harray ?hhash ?hseq ?hsub ?hsemantic
    hj hret hmeth htop
  case hsemantic =>
    intro D Γ top ctx cl hmem hff hreq hqm hfr hfn hdisc hret2 hmeth2 _
    have hrows : cl.rows = [] := by
      rcases hdisc with h | h
      · exact h.1
      · rw [h] at hmeth2; exact Bool.noConfusion hmeth2
    simp [hrows, addRows]
  all_goals
    (intros
     first
      | trivial
      | rfl
      | simp_all [loopCtx, rescueCtx])

set_option maxHeartbeats 4000000 in
/-- `judge_table_ret` at `JudgeElems` (same motives, `JudgeElems.rec`). -/
theorem judge_elems_table_ret {A : SemAxioms} {D : Decls} {Γ : Env} {es : List Expr} {top : Bool}
    {ctx : JCtx}
    {Γ' : Env} {D' : Decls} (hj : JudgeElems A D Γ es top ctx  Γ' D')
    (hret : ctx.ret.isSome = true) (hmeth : ctx.meth.isSome = true)
    (htop : top = false) : D' = D := by
  refine JudgeElems.rec
    (motive_1 := fun D Γ ro top ctx τ Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_2 := fun D Γ ro top ctx τ Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_3 := fun D Γ es top ctx τ Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_4 := fun D Γ es top ctx τs Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_5 := fun D Γ es top ctx Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_6 := fun D Γ prs top ctx Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_7 := fun D Γ es top ctx Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_8 := fun _ _ _ _ _ _ _ => True)
    (motive_9 := fun _ _ _ _ _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ _ _ => True)
    (motive_11 := fun D Γ e top ctx τ Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?hint ?hflt ?hstr ?hsym ?htru ?hfls ?hnil ?hregexpLit ?hself
    ?hvarLvar ?hvarIvar ?hvarGvar ?hvarCvar
    ?hvasgnLvar ?hvasgnIvarDecl ?hvasgnIvarFresh ?hvasgnGvar ?hvasgnCvar
    ?hconst ?hcpathAbs ?hcpathScoped ?hcasgn ?hcasgnM ?hcpathAsgn
    ?hsend ?hsendIter0 ?hsendIterA ?hsendLambda ?hsendLambdaArrow ?hsendCall
    ?hsendBlockpass ?hvcall ?hkwargs ?hfwd ?hsplatAnon ?hsplatArray ?hsplatArrayOf
    ?hyield ?hifElse ?hifNone ?hifNarrowElse ?hifNarrowNone
    ?hwhile ?hdowhile ?hfor
    ?hretSome ?hretNil ?hnxtNil ?hnxtSome ?hbrkNil ?hbrkSome ?hretry ?hredo
    ?hdefDecl ?hdefPromote ?hdefs ?hclassTop ?hclassSup ?hmodule
    ?hscopedClass ?hscopedModule ?hsclass ?hbegin ?hsuper ?hzsuper ?halias
    ?hdefined ?harray ?hhash ?hseq ?hsub ?hsemantic
    hj hret hmeth htop
  case hsemantic =>
    intro D Γ top ctx cl hmem hff hreq hqm hfr hfn hdisc hret2 hmeth2 _
    have hrows : cl.rows = [] := by
      rcases hdisc with h | h
      · exact h.1
      · rw [h] at hmeth2; exact Bool.noConfusion hmeth2
    simp [hrows, addRows]
  all_goals
    (intros
     first
      | trivial
      | rfl
      | simp_all [loopCtx, rescueCtx])



set_option maxHeartbeats 4000000 in
/-- `judge_table_ret` at `JudgePairs` (same motives, `JudgePairs.rec`). -/
theorem judge_pairs_table_ret {A : SemAxioms} {D : Decls} {Γ : Env}
    {prs : List (Expr × Expr)} {top : Bool}
    {ctx : JCtx}
    {Γ' : Env} {D' : Decls} (hj : JudgePairs A D Γ prs top ctx Γ' D')
    (hret : ctx.ret.isSome = true) (hmeth : ctx.meth.isSome = true)
    (htop : top = false) : D' = D := by
  refine JudgePairs.rec
    (motive_1 := fun D Γ ro top ctx τ Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_2 := fun D Γ ro top ctx τ Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_3 := fun D Γ es top ctx τ Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_4 := fun D Γ es top ctx τs Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_5 := fun D Γ es top ctx Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_6 := fun D Γ prs top ctx Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_7 := fun D Γ es top ctx Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    (motive_8 := fun _ _ _ _ _ _ _ => True)
    (motive_9 := fun _ _ _ _ _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ _ _ => True)
    (motive_11 := fun D Γ e top ctx τ Γ' D' _ =>
      ctx.ret.isSome = true → ctx.meth.isSome = true → top = false → D' = D)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?hint ?hflt ?hstr ?hsym ?htru ?hfls ?hnil ?hregexpLit ?hself
    ?hvarLvar ?hvarIvar ?hvarGvar ?hvarCvar
    ?hvasgnLvar ?hvasgnIvarDecl ?hvasgnIvarFresh ?hvasgnGvar ?hvasgnCvar
    ?hconst ?hcpathAbs ?hcpathScoped ?hcasgn ?hcasgnM ?hcpathAsgn
    ?hsend ?hsendIter0 ?hsendIterA ?hsendLambda ?hsendLambdaArrow ?hsendCall
    ?hsendBlockpass ?hvcall ?hkwargs ?hfwd ?hsplatAnon ?hsplatArray ?hsplatArrayOf
    ?hyield ?hifElse ?hifNone ?hifNarrowElse ?hifNarrowNone
    ?hwhile ?hdowhile ?hfor
    ?hretSome ?hretNil ?hnxtNil ?hnxtSome ?hbrkNil ?hbrkSome ?hretry ?hredo
    ?hdefDecl ?hdefPromote ?hdefs ?hclassTop ?hclassSup ?hmodule
    ?hscopedClass ?hscopedModule ?hsclass ?hbegin ?hsuper ?hzsuper ?halias
    ?hdefined ?harray ?hhash ?hseq ?hsub ?hsemantic
    hj hret hmeth htop
  case hsemantic =>
    intro D Γ top ctx cl hmem hff hreq hqm hfr hfn hdisc hret2 hmeth2 _
    have hrows : cl.rows = [] := by
      rcases hdisc with h | h
      · exact h.1
      · rw [h] at hmeth2; exact Bool.noConfusion hmeth2
    simp [hrows, addRows]
  all_goals
    (intros
     first
      | trivial
      | rfl
      | simp_all [loopCtx, rescueCtx])


end Judgment
end Proof
end RubyCore
