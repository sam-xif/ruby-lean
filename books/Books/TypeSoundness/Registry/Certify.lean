import Books.TypeSoundness.Rules.Init.InitBridge

/-! One recursor proof script for every member of the mutual judgment. Keeping its
constructor cases shared makes the ordinary and callback bridges use identical rules. -/
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

macro "certify_djudgments" rec:ident h:ident F:ident hF:ident : tactic => `(tactic| (
  refine $rec
    (motive_1 := fun Γ e τ Γ' κ I κ' I' _ => ($F).judge Γ e τ Γ' κ I κ' I')
    (motive_2 := fun Γ es tys Γ' κ I κ' I' _ => ($F).all Γ es tys Γ' κ I κ' I')
    (motive_3 := fun Γ es τ Γ' κ I κ' I' _ => ($F).seq Γ es τ Γ' κ I κ' I')
    (motive_4 := fun Γ ps ks vs Γ' κ I κ' I' _ => ($F).pairs Γ ps ks vs Γ' κ I κ' I')
    (motive_5 := fun κ I s Γ e τ Γ' _ => ($F).recBody κ I s Γ e τ Γ')
    (motive_6 := fun κ I s Γ es tys Γ' _ => ($F).recArgs κ I s Γ es tys Γ')
    (motive_7 := fun κ Γ I facts e τ current κ' Γ' I' out _ =>
      ($F).flow κ Γ I facts e τ current κ' Γ' I' out)
    (motive_8 := fun κ Γ I facts es τ current κ' Γ' I' out _ =>
      ($F).flowSeq κ Γ I facts es τ current κ' Γ' I' out)
    (motive_9 := fun κ Γ I facts es tys κ' Γ' I' out _ =>
      ($F).flowAll κ Γ I facts es tys κ' Γ' I' out)
    (motive_10 := fun κ I fr ps ret Γ e τ Γ' _ => ($F).method κ I fr ps ret Γ e τ Γ')
    (motive_11 := fun κ I fr ps ret Γ es tys Γ' _ => ($F).methodAll κ I fr ps ret Γ es tys Γ')
    (motive_12 := fun κ I fr ps ret Γ es τ Γ' _ => ($F).methodSeq κ I fr ps ret Γ es τ Γ')
    (motive_13 := fun κ I fr ps ret Γ facts e τ c Γ' out _ => ($F).methodFlow κ I fr ps ret Γ facts e τ c Γ' out)
    (motive_14 := fun κ I fr ps ret Γ facts es τ c Γ' out _ => ($F).methodFlowSeq κ I fr ps ret Γ facts es τ c Γ' out)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ $h
  all_goals intros
  · apply $hF DClink.intLit (by simp [dclinks]) <;> assumption
  · apply $hF DClink.fltLit (by simp [dclinks]) <;> assumption
  · apply $hF DClink.strLit (by simp [dclinks]) <;> assumption
  · apply $hF DClink.symLit (by simp [dclinks]) <;> assumption
  · apply $hF DClink.truLit (by simp [dclinks]) <;> assumption
  · apply $hF DClink.flsLit (by simp [dclinks]) <;> assumption
  · apply $hF DClink.nilLit (by simp [dclinks]) <;> assumption
  · apply $hF DClink.regexpLit (by simp [dclinks]) <;> assumption
  · apply $hF DClink.var (by simp [dclinks]) <;> assumption
  · apply $hF DClink.vasgn (by simp [dclinks]) <;> assumption
  · apply $hF DClink.vasgnAlias (by simp [dclinks]) <;> assumption
  · apply $hF DClink.seq (by simp [dclinks]) <;> assumption
  · apply $hF DClink.prim (by simp [dclinks]) <;> assumption
  · apply $hF DClink.if' (by simp [dclinks]) <;> assumption
  · apply $hF DClink.ifNoElse (by simp [dclinks]) <;> assumption
  · apply $hF DClink.ifTruthy (by simp [dclinks]) <;> assumption
  · apply $hF DClink.ifTruthyNoElse (by simp [dclinks]) <;> assumption
  · apply $hF DClink.ifNilVar (by simp [dclinks]) <;> assumption
  · apply $hF DClink.ifNilQueryNil (by simp [dclinks]) <;> assumption
  · apply $hF DClink.ifNilQuery (by simp [dclinks]) <;> assumption
  · apply $hF DClink.ifIsA (by simp [dclinks]) <;> assumption
  · apply $hF DClink.ifIsAIvar (by simp [dclinks]) <;> assumption
  · apply $hF DClink.ifCaseEq (by simp [dclinks]) <;> assumption
  · apply $hF DClink.ifCaseEqVar (by simp [dclinks]) <;> assumption
  · apply $hF DClink.ifAndVar (by simp [dclinks]) <;> assumption
  · apply $hF DClink.dead (by simp [dclinks]) <;> assumption
  · apply $hF DClink.widen (by simp [dclinks]) <;> assumption
  · apply $hF DClink.sendUnion (by simp [dclinks]) <;> assumption
  · apply $hF DClink.casgnTop (by simp [dclinks]) <;> assumption
  · apply $hF DClink.constRead (by simp [dclinks]) <;> assumption
  · apply $hF DClink.while' (by simp [dclinks]) <;> assumption
  · apply $hF DClink.bareName (by simp [dclinks]) <;> assumption
  · apply $hF DClink.arrayLit (by simp [dclinks]) <;> assumption
  · apply $hF DClink.hashLit (by simp [dclinks]) <;> assumption
  · rename_i κd Γd Γb Id τd d ps hp hps ht hb hm hc hs hbl hco ha hi hg hf hmiss hquiet ihb
    exact $hF DClink.defDecl (by simp [dclinks]) hp hps ht ihb
      hm hc hs hbl hco ha hi hg hf hmiss hquiet
  · rename_i κd Γd Γm Id τd brd d ps bs hp hps hbs hbr ht hb hm hc hs hbl hco ha hi hg hf hmiss hquiet ihb
    exact $hF DClink.defBlock (by simp [dclinks]) hp hps hbs hbr ht ihb
      hm hc hs hbl hco ha hi hg hf hmiss hquiet
  · rename_i κd Γd Id τd brd d localName bs callback Γm out hp hbs hbr ht hb hm hc hs hbl hco ha hi hg hf hmiss hquiet ihb
    exact $hF DClink.defBoundBlock (by simp [dclinks]) hp hbs hbr ht ihb
      hm hc hs hbl hco ha hi hg hf hmiss hquiet
  · rename_i hp hps ht hd hb hm hc hs hbl hco ha hi hg hf hmiss hquiet ihd ihb
    exact $hF DClink.defDeclOpt (by simp [dclinks]) hp hps ht ihd ihb
      hm hc hs hbl hco ha hi hg hf hmiss hquiet
  · rename_i hp hps ht hb hm hc hs hbl hco ha hi hg hf hmiss hquiet ihb
    exact $hF DClink.defDeclKw (by simp [dclinks]) hp hps ht ihb
      hm hc hs hbl hco ha hi hg hf hmiss hquiet
  · rename_i hp hps ht hd hb hm hc hs hbl hco ha hi hg hf hmiss hquiet ihd ihb
    exact $hF DClink.defDeclKwOpt (by simp [dclinks]) hp hps ht ihd ihb
      hm hc hs hbl hco ha hi hg hf hmiss hquiet
  · rename_i hp hps hσ ht hb hm hc hs hbl hco ha hi hg hf hmiss hquiet ihb
    exact $hF DClink.defDeclRest (by simp [dclinks]) hp hps hσ ht ihb
      hm hc hs hbl hco ha hi hg hf hmiss hquiet
  · apply $hF DClink.callSig (by simp [dclinks]) <;> assumption
  · apply $hF DClink.callSigOpt (by simp [dclinks]) <;> assumption
  · rename_i hp hps hσ ht hb henv hkill hcap hcapc hall htys hmem hm hm' hs hbl hco ha hi hg ihb ihall
    exact $hF DClink.callSigRest (by simp [dclinks]) hp hps hσ ht ihb henv hkill hcap hcapc ihall htys hmem
      hm hm' hs hbl hco ha hi hg
  · apply $hF DClink.callSigKw (by simp [dclinks]) <;> assumption
  · apply $hF DClink.callSigKwOpt (by simp [dclinks]) <;> assumption
  · apply $hF DClink.recursive (by simp [dclinks]) <;> assumption
  · exact $hF DClink.ivarRead (by simp [dclinks])
  · apply $hF DClink.constClass (by simp [dclinks]) <;> assumption
  · apply $hF DClink.classDecl (by simp [dclinks]) <;> assumption
  · apply $hF DClink.classReopen (by simp [dclinks]) <;> assumption
  · apply $hF DClink.moduleDecl (by simp [dclinks]) <;> assumption
  · rename_i κd Γd Γb Id Ib τd c d ps hp hps hret hself hb hn hc hg ihb
    exact $hF DClink.memberDef (by simp [dclinks]) hp hps hret hself ihb hn hc hg
  · rename_i κd Γd Γb Id Ib τd c d ps hn hp hps hret hout hb hc hg
    exact $hF DClink.initDef (by simp [dclinks]) hn hp hps hret hout
      (initJudge_certified hb $F $hF) hc hg
  · rename_i κd κ₁ κ₂ Γd Γ₁ Γ₂ Γb Id I₁ I₂ Ib τd c d ps recv args
      hr ha hs hc hd hn hnew halloc hp hps hret hout hb hg ihr iha
    exact $hF DClink.newInst (by simp [dclinks]) ihr iha hs hc hd hn hnew halloc hp hps
      hret hout (initJudge_certified hb $F $hF) hg
  · apply $hF DClink.callMethodSig (by simp [dclinks]) <;> assumption
  · apply $hF DClink.vcallMethodSig (by simp [dclinks]) <;> assumption
  · apply $hF DClink.subclassDecl (by simp [dclinks]) <;> assumption
  · rename_i κd κ₁ κ₂ Γd Γ₁ Γ₂ Γb Id I₁ I₂ Ib τd c owner d ps recv args
      hr ha hs hc route hn hnew halloc hp hps hret hout hb hg ihr iha
    exact $hF DClink.newInherited (by simp [dclinks]) ihr iha hs hc route hn hnew halloc hp hps
      hret hout (initJudge_certified hb $F $hF) hg
  · apply $hF DClink.callInherited (by simp [dclinks]) <;> assumption
  · apply $hF DClink.newDefault (by simp [dclinks]) <;> assumption
  · apply $hF DClink.singletonDef (by simp [dclinks]) <;> assumption
  · apply $hF DClink.callSingleton (by simp [dclinks]) <;> assumption
  · apply $hF DClink.callSingletonImplicit (by simp [dclinks]) <;> assumption
  · rename_i κd κ' Γd Γ' Γb Id I' Ib τd c d ps args hs ha hc hd hn hnew halloc hp hps hret hout hb hg iha
    exact $hF DClink.newImplicit (by simp [dclinks]) hs iha hc hd hn hnew halloc hp hps
      hret hout (initJudge_certified hb $F $hF) hg
  · apply $hF DClink.instanceType (by simp [dclinks]) <;> assumption
  · apply $hF DClink.scalarIvarAsgn (by simp [dclinks]) <;> assumption
  · apply $hF DClink.selfRead (by simp [dclinks]) <;> assumption
  · apply $hF DClink.flow (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DJudgeAll.nil (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DJudgeAll.cons (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DJudgeSeq.last (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DJudgeSeq.cons (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DJudgePairs.nil (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DJudgePairs.cons (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DJudgeRec.embed (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DJudgeRec.prim (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DJudgeRec.if' (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DJudgeRec.selfCall (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DJudgeRecAll.nil (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DJudgeRecAll.cons (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DFlow.embed (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DFlow.intLit (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DFlow.nilLit (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DFlow.var (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DFlow.closureLiteral (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DFlow.vasgn (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DFlow.sequence (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DFlow.call (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DFlow.requiredCall (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DFlow.each (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DFlow.map (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DFlow.callBlock (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DFlow.callBoundBlock (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DFlow.prim (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DFlowSeq.last (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DFlowSeq.cons (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DFlowAll.nil (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DFlowAll.cons (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DMethod.ordinary (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DMethod.vasgn (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DMethod.sequence (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DMethod.prim (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DMethod.yieldOne (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DMethodAll.nil (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DMethodAll.cons (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DMethodSeq.last (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DMethodSeq.cons (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DMethodFlow.embed (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DMethodFlow.intLit (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DMethodFlow.nilLit (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DMethodFlow.var (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DMethodFlow.vasgn (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DMethodFlow.sequence (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DMethodFlow.call (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DMethodFlowSeq.last (by simp [dclinks]) <;> assumption
  · apply $hF DClink.DMethodFlowSeq.cons (by simp [dclinks]) <;> assumption
))
end Checker.Soundness.Typed
