import Books.Metatheory.Framing.RootFrameStep

/-! Compatibility names for the repaired framing chain.

The old stack-only action was false for block-scope probes and Enumerator
transfers. The action now follows the root execution into saved callers, and
ContextFree excludes every native whole-stack observation. The historical
CatchFree name is retained for clients, with this stronger helper contract.
The implementations and their axiom audits live in RootFrame*.lean.
-/
namespace RubyCore.Proof

abbrev pushK := pushRootK
abbrev frameR := rootFrameR
abbrev bpush := Root.bRootPush
abbrev CatchFree := Root.ContextFree

export Root (
  BFrame allocArr_frame allocExc_frame allocFoldArray_frame allocFold_frame
  allocHsh_frame allocMData_frame allocRegexp_frame allocStrEnc_frame allocStr_frame
  appendKwHash_frame applyKont_frame applyTo_frame binArg_frame bindIvar_frame
  blockOwner_frame blockPassChecked_frame blockPassInvalid_frame blockPassMethod_frame blockPassMissing_frame
  blockPassNoConversion_frame blockPassProc_frame blockPassRespond_frame callArrayMapBuiltin_frame callClosure_frame
  callProcBuiltin_frame capsFoldArray_frame capsFoldListArray_frame capsFoldList_frame capsFold_frame
  charsFold_frame coerceBlockPass_frame coerceFailed_frame continueArray_frame cpathContainer_frame
  cvarScope_frame defineAttr_frame definedMethod?_frame dispatchMiss_frame dmTarget?_frame
  dmTargetM_frame doReturn_frame doSuper_frame doYield_frame dupObj_frame
  eigenclassOf_frame eigenclassOf_go_frame emit_frame enterClassBody_frame enterHandler_frame
  enterScopedClassBody_frame enterUserMethod_frame evalDefined_frame evalExpr_frame finishRegion_frame
  finishSend_frame flattenAll_frame floatToInt_frame foldMachine_frame foldPairArray_frame
  foldPairFst_frame foldPair_frame foldrPair_frame forwardBundle_frame frozenErr_frame
  getGlobal_frame getLocal_frame hasCatcher_frame inspectP_frame intBitRef_frame
  invokeDispatch_frame invokeMethodMissing_frame invoke_frame iterStep_frame joinImpl_frame
  matchFrameId_frame matchFrameId_go_frame matchFrameOwner_frame matchGlobal_frame methodBlk_frame
  methodFrameOf_frame missNoMethod_frame mixinDefines_frame mixinShadow_frame moduleHook_frame
  namesFold_frame newImpl_frame nextClause_frame numBin_frame numCmp_frame
  objectsGo_frame okStrEnc_frame okStrFrom_frame okStr_frame printArm_frame
  printFold_frame putsGo_frame putsImpl_frame raiseClass_frame raiseErr_frame
  raiseImpl_frame reflectAliasMethod_frame reflectAttr_frame reflectCatch_frame reflectConstGet_frame
  reflectDefineMethod_frame reflectEval_frame reflectIvarGet_frame reflectIvarNames_frame reflectIvarSet_frame
  reflectMethodDefined_frame reflectRemoveMethod_frame reflectRespondTo_frame reflectSingletonClass_frame reflectThrow_frame
  reflectVisibility_frame regexApply_frame reifyBlock_frame removeNames_frame removeOk_frame
  removeRun_frame resumeBlockPass_frame returnTarget_frame runCollections_frame runModules_frame
  runNumerics_frame runObjects_frame runRegex_frame runStrings_frame run_frame
  scanAll_frame setCurrentFrame_frame setGlobal_frame setLastMatchValue_frame setLastMatch_frame
  setLocal_frame setMatchGlobals_frame sortImpl_frame splitBy_frame splitOn_frame
  startArgs_frame startIter_frame startKwargs_frame startSuperArgs_frame startYield_frame
  stepFn_frame subst_frame symOrStr_frame toSP_frame tryIterator_frame
  tryMixin_frame tryReflect_frame undefAliasMiss_frame undefNames_frame unwindBlockPass_frame
  unwind_frame visError?_frame visNames_frame visOk_frame visRun_frame
  withCtl_frame withIndex_frame withKont_frame zsuperArgs_frame
)

abbrev pushK_ctl := @Root.pushRootK_ctl
abbrev pushK_currentExc := @Root.pushRootK_currentExc
abbrev pushK_currentFrame := @Root.pushRootK_currentFrame
abbrev pushK_frames := @Root.pushRootK_frames
abbrev pushK_globals := @Root.pushRootK_globals
abbrev pushK_heap := @Root.pushRootK_heap
abbrev pushK_kont := @Root.pushRootK_kont
abbrev pushK_out := @Root.pushRootK_out
abbrev pushK_preludeMode := @Root.pushRootK_preludeMode
abbrev pushK_setHeap := @Root.pushRootK_setHeap
abbrev pushK_setOut := @Root.pushRootK_setOut
abbrev pushK_stack := @Root.pushRootK_stack

#print axioms stepFn_frame
end RubyCore.Proof
