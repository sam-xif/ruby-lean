# books/Unrebuilt/ — proofs not yet rebuilt against the current model

Nothing in this directory is built, and nothing under `Books/` imports it. These are
soundness-proof files that were written against an earlier version of the model and
have not been brought up to date. They were moved here, unedited, so that every file
under `Books/` compiles and the build can say so: `lake build` covers the whole of
`Books/`, and CI fails if a file there stops building.

The theorem `validateD_safe_run` does not depend on any of them. It is proved in
`Books/TypeSoundness/Soundness.lean` for every rule the checker has, using the proofs
that *were* rebuilt (many of them the `…Actual` files beside where these used to be).

## Why they do not build

The model changed underneath them. The recurring causes:

- **Constant lookup gained a module fallback** (`Interp.lexicalConstant`,
  `instanceConstResolve`). The `Conformance/Subclass` and `Conformance/Module`
  constant lemmas are stated and proved for the earlier lookup.
- **Class and module entry was re-modelled.** The older lemmas are about a direct jump
  into the fresh-class machine; the real entry queues `const_added` and `inherited`
  first, and `books/notes/type-soundness/HANDOFF.md` records that the older statement
  was false. The rebuilt proofs are the `Class*Actual` / `Module*Actual` /
  `Subclass*Actual` files in `Books/`.
- **Allocation readiness** (`PlainAllocator`) and **method code** (`OrdinaryMethodCode`)
  gained fields.
- **Closure and callback lemmas were restated**, so controls that applied the old forms
  no longer typecheck.

## Bringing a file back

The files keep their module names and imports (`Books.TypeSoundness.…`), so a file
returns by moving it to the same path under `Books/`:

```bash
git mv Unrebuilt/TypeSoundness/Conformance/Subclass/SubclassConstants.lean \
       Books/TypeSoundness/Conformance/Subclass/SubclassConstants.lean
lake build Books.TypeSoundness.Conformance.Subclass.SubclassConstants
```

A control also needs its line in `Books/TypeSoundness/Controls/All.lean`. Work from the
first table below: those are the files with an error of their own, and the count says
how many others each one is holding back. Three of them hold back half of this
directory, including the audit chain (`RuleAudit`, `RuleCoverage`,
`Examples/CorpusSafety`): `SubclassConstants`, `SubclassGlobals` and `SubclassNewEntry`.

## Also here

| Path | What it is |
|---|---|
| `SemLadder.lean` | The full-profile report executable (`semladder`). It imports `RuleAudit` |
| `scripts/run_full_typed_ratchet.sh` | The historical full-coverage audit, formerly `run_typed_ratchet.sh --full-corpus`. It builds `RuleAudit`, `RuleCoverage`, the complete control list and `semladder` |

## Files with an error of their own (42)

"Blocks" is the number of other files here that import it, directly or not.

| File | Blocks | First error |
|---|---|---|
| `TypeSoundness/Conformance/Subclass/SubclassConstants.lean` | 76 | line 80: Type mismatch: After simplification, term |
| `TypeSoundness/Conformance/Subclass/SubclassGlobals.lean` | 51 | line 17: Application type mismatch: The argument |
| `TypeSoundness/Conformance/Subclass/SubclassNewEntry.lean` | 36 | line 27: Application type mismatch: The argument |
| `TypeSoundness/Conformance/Module/ModuleConstants.lean` | 15 | line 65: Tactic 'rfl' failed: The left-hand side |
| `TypeSoundness/Conformance/Module/ModuleGlobals.lean` | 7 | line 17: Application type mismatch: The argument |
| `TypeSoundness/Conformance/Subclass/SubclassAllocator.lean` | 6 | line 18: Insufficient number of fields for '⟨...⟩' constructor: Constructor 'Checker.Soundness.PlainAllocator.mk' has 11 explicit field, but only 9 we |
| `TypeSoundness/Rules/Method/YieldInt.lean` | 4 | line 47: Application type mismatch: The argument |
| `TypeSoundness/Controls/ClosureStoredControls.lean` | 3 | line 23: Unknown identifier 'reified_den' |
| `TypeSoundness/Rules/Constructor/DefaultAllocation.lean` | 3 | line 44: Type mismatch |
| `TypeSoundness/Controls/BoundCallbackControls.lean` | 2 | line 62: Application type mismatch: The argument |
| `TypeSoundness/Rules/Closure/Symbol.lean` | 2 | line 25: Type mismatch |
| `TypeSoundness/Rules/Closure/StorePrefix.lean` | 1 | line 27: Tactic 'introN' failed: There are no additional binders or 'let' bindings in the goal to introduce |
| `TypeSoundness/Rules/Closure/Write.lean` | 1 | line 24: Tactic 'rewrite' failed: Did not find an occurrence of the pattern |
| `TypeSoundness/Rules/Instance/InstanceSitePublish.lean` | 1 | line 18: Invalid field 'recontext': The environment does not contain 'Function.recontext', so it is not possible to project the field 'recontext' from |
| `TypeSoundness/Rules/Instance/ReceiverCache.lean` | 1 | line 28: Application type mismatch: The argument |
| `TypeSoundness/Controls/CaptureBindingControls.lean` | 0 | line 62: (deterministic) timeout at 'whnf', maximum number of heartbeats (200000) has been reached |
| `TypeSoundness/Controls/CaptureFrameControls.lean` | 0 | line 42: Application type mismatch: The argument |
| `TypeSoundness/Controls/CaptureOwnerControls.lean` | 0 | line 27: Application type mismatch: The argument |
| `TypeSoundness/Controls/ClassBaseControls.lean` | 0 | line 18: Application type mismatch: The argument |
| `TypeSoundness/Controls/ClassControls.lean` | 0 | line 47: Application type mismatch: The argument |
| `TypeSoundness/Controls/ClassNameControls.lean` | 0 | line 17: (deterministic) timeout at 'whnf', maximum number of heartbeats (200000) has been reached |
| `TypeSoundness/Controls/ClassQueryControls.lean` | 0 | line 27: Application type mismatch: The argument |
| `TypeSoundness/Controls/ClosureEntryControls.lean` | 0 | line 53: Application type mismatch: The argument |
| `TypeSoundness/Controls/ClosureLiteralControls.lean` | 0 | line 17: Unknown identifier 'closure_literal_result' |
| `TypeSoundness/Controls/ClosureProjectionControls.lean` | 0 | line 22: unsolved goals |
| `TypeSoundness/Controls/ClosureReturnEnvControls.lean` | 0 | line 23: unsolved goals |
| `TypeSoundness/Controls/ClosureShadowControls.lean` | 0 | line 32: Application type mismatch: The argument |
| `TypeSoundness/Controls/ClosureStateControls.lean` | 0 | line 23: unsolved goals |
| `TypeSoundness/Controls/ClosureValueControls.lean` | 0 | line 16: Unknown constant 'Checker.Soundness.Typed.SemSafeCtxA.closureLiteral' |
| `TypeSoundness/Controls/ConstructorControls.lean` | 0 | line 34: Unknown identifier 'constructor_body_entry' |
| `TypeSoundness/Controls/ConstructorRunControls.lean` | 0 | line 26: Application type mismatch: The argument |
| `TypeSoundness/Controls/EachDispatchControls.lean` | 0 | line 20: Expression |
| `TypeSoundness/Controls/InitControls.lean` | 0 | line 41: Type mismatch |
| `TypeSoundness/Controls/InstanceSpineControls.lean` | 0 | line 47: Expression |
| `TypeSoundness/Controls/IteratorFrameControls.lean` | 0 | line 21: Application type mismatch: The argument |
| `TypeSoundness/Controls/MethodBodyControls.lean` | 0 | line 48: numerals are data in Lean, but the expected type is a proposition |
| `TypeSoundness/Controls/MethodEffectsControls.lean` | 0 | line 43: Application type mismatch: The argument |
| `TypeSoundness/Controls/MethodInstallControls.lean` | 0 | line 48: maximum recursion depth has been reached |
| `TypeSoundness/Controls/SuperLookupControls.lean` | 0 | line 16: Expression |
| `TypeSoundness/Controls/TypedEachControls.lean` | 0 | line 29: Application type mismatch: The argument |
| `TypeSoundness/Controls/TypedMapControls.lean` | 0 | line 31: Application type mismatch: The argument |
| `TypeSoundness/Controls/TypedYieldControls.lean` | 0 | line 37: Application type mismatch: The argument |

Three controls in the second table (`InheritedConstructorControls`, `SubclassRunControls`,
`ReceiverCacheControls`) import `Rules/Subclass/SubclassRule`, a module that no longer
exists anywhere; the checker-side guard of that name is `Checker/Guards/SubclassRule.lean`.

## Files held back only by an import (108)

These have not been compiled against the current model, so they may have errors of
their own once what they import is rebuilt.

| File | Waiting on |
|---|---|
| `TypeSoundness/Conformance/Class/ClassAllocators.lean` | Conformance.Subclass.SubclassGlobals |
| `TypeSoundness/Conformance/Class/ClassConstants.lean` | Conformance.Subclass.SubclassConstants |
| `TypeSoundness/Conformance/Class/ClassCore.lean` | Conformance.Subclass.SubclassCore |
| `TypeSoundness/Conformance/Class/ClassDeclared.lean` | Conformance.Class.ClassCore |
| `TypeSoundness/Conformance/Class/ClassGlobalConsts.lean` | Conformance.Subclass.SubclassGlobals |
| `TypeSoundness/Conformance/Class/ClassHeader.lean` | Conformance.Class.ClassNewEntry |
| `TypeSoundness/Conformance/Class/ClassNewEntry.lean` | Conformance.Subclass.SubclassNewEntry |
| `TypeSoundness/Conformance/Class/ClassScopeEntry.lean` | Conformance.Subclass.SubclassSites |
| `TypeSoundness/Conformance/Class/ClassState.lean` | Conformance.Subclass.SubclassState |
| `TypeSoundness/Conformance/Class/ClassTables.lean` | Conformance.Class.ClassConstants |
| `TypeSoundness/Conformance/Instance/InstanceSiteClass.lean` | Conformance.Subclass.SubclassSites |
| `TypeSoundness/Conformance/Instance/InstanceSiteEntry.lean` | Conformance.Subclass.SubclassSites |
| `TypeSoundness/Conformance/Instance/MainSiteClass.lean` | Conformance.Subclass.SubclassMain |
| `TypeSoundness/Conformance/Module/ModuleCore.lean` | Conformance.Module.ModuleConstants |
| `TypeSoundness/Conformance/Module/ModuleMain.lean` | Conformance.Module.ModuleConstants |
| `TypeSoundness/Conformance/Module/ModuleSites.lean` | Conformance.Module.ModuleConstants |
| `TypeSoundness/Conformance/Module/ModuleState.lean` | Conformance.Module.ModuleGlobals |
| `TypeSoundness/Conformance/Module/ModuleTables.lean` | Conformance.Module.ModuleConstants |
| `TypeSoundness/Conformance/Subclass/SubclassCore.lean` | Conformance.Subclass.SubclassConstants |
| `TypeSoundness/Conformance/Subclass/SubclassHeader.lean` | Conformance.Subclass.SubclassAllocator |
| `TypeSoundness/Conformance/Subclass/SubclassMain.lean` | Conformance.Subclass.SubclassConstants |
| `TypeSoundness/Conformance/Subclass/SubclassSites.lean` | Conformance.Subclass.SubclassConstants |
| `TypeSoundness/Conformance/Subclass/SubclassState.lean` | Conformance.Subclass.SubclassGlobals |
| `TypeSoundness/Conformance/Subclass/SubclassTables.lean` | Conformance.Subclass.SubclassConstants |
| `TypeSoundness/Controls/BoundBodyControls.lean` | Controls.CallbackAliasControls |
| `TypeSoundness/Controls/CallbackAliasControls.lean` | Controls.BoundCallbackControls |
| `TypeSoundness/Controls/ClassAliasControls.lean` | Rules.Class.ClassRun |
| `TypeSoundness/Controls/ClassCoreControls.lean` | Conformance.Class.ClassCore |
| `TypeSoundness/Controls/ClassCtorControls.lean` | Conformance.Class.ClassNewEntry |
| `TypeSoundness/Controls/ClassDeclaredControls.lean` | Conformance.Class.ClassDeclared |
| `TypeSoundness/Controls/ClassFrameControls.lean` | Conformance.Class.ClassConstants |
| `TypeSoundness/Controls/ClassFreshnessControls.lean` | Controls.ClassStateControls |
| `TypeSoundness/Controls/ClassHeaderControls.lean` | Conformance.Class.ClassHeader |
| `TypeSoundness/Controls/ClassReturnControls.lean` | Rules.Class.ClassRun |
| `TypeSoundness/Controls/ClassRootControls.lean` | Rules.Class.ClassRun |
| `TypeSoundness/Controls/ClassRootNameControls.lean` | Rules.Class.ClassRun |
| `TypeSoundness/Controls/ClassRuleControls.lean` | Rules.Class.ClassRules |
| `TypeSoundness/Controls/ClassScopeControls.lean` | Controls.ClassStateControls |
| `TypeSoundness/Controls/ClassSitesControls.lean` | Conformance.Instance.InstanceSiteClass |
| `TypeSoundness/Controls/ClassStateControls.lean` | Conformance.Class.ClassState |
| `TypeSoundness/Controls/ClosureCallControls.lean` | Rules.Closure.StorePrefix |
| `TypeSoundness/Controls/ClosureReturnStateControls.lean` | Rules.Closure.Write |
| `TypeSoundness/Controls/ClosureStoredReturnControls.lean` | Controls.ClosureStoredControls |
| `TypeSoundness/Controls/ClosureTrackingControls.lean` | Controls.ClosureStoredReturnControls |
| `TypeSoundness/Controls/ConstructorGeneralControls.lean` | Rules.Class.ClassHeaderRun |
| `TypeSoundness/Controls/DefaultConstructorControls.lean` | Rules.Constructor.DefaultConstructor |
| `TypeSoundness/Controls/FactoryConstructorControls.lean` | Examples.PointClass |
| `TypeSoundness/Controls/InheritedCallControls.lean` | Controls.ClassHeaderControls |
| `TypeSoundness/Controls/InheritedConstructorControls.lean` | Rules.Subclass.SubclassRule (no such module) |
| `TypeSoundness/Controls/InstanceReturnControls.lean` | Controls.ClassStateControls |
| `TypeSoundness/Controls/InstanceSiteWriteControls.lean` | Rules.Instance.InstanceSitePublish |
| `TypeSoundness/Controls/InstanceStateControls.lean` | Conformance.Instance.InstanceSiteEntry |
| `TypeSoundness/Controls/MainSiteControls.lean` | Controls.ClassStateControls |
| `TypeSoundness/Controls/MemberDefineControls.lean` | Controls.ClassHeaderControls |
| `TypeSoundness/Controls/MethodTypingControls.lean` | Examples.YieldBody |
| `TypeSoundness/Controls/ModuleCoreControls.lean` | Rules.Module.ModuleEntry |
| `TypeSoundness/Controls/ModuleDataControls.lean` | Rules.Module.ModuleEntry |
| `TypeSoundness/Controls/ModuleHeaderControls.lean` | Rules.Module.ModuleEntry |
| `TypeSoundness/Controls/ModuleRuleControls.lean` | Rules.Module.ModuleRule |
| `TypeSoundness/Controls/ModuleStateControls.lean` | Rules.Module.ModuleStateEntry |
| `TypeSoundness/Controls/PointClassControls.lean` | Examples.PointClass |
| `TypeSoundness/Controls/PointConstructorControls.lean` | Examples.PointConstructor |
| `TypeSoundness/Controls/PointConstructorExprControls.lean` | Examples.PointConstructorExpr |
| `TypeSoundness/Controls/PointProgramControls.lean` | Examples.PointProgram |
| `TypeSoundness/Controls/ReceiverCacheControls.lean` | Rules.Subclass.SubclassRule (no such module) |
| `TypeSoundness/Controls/RootInitControls.lean` | Controls.DefaultConstructorControls |
| `TypeSoundness/Controls/SingletonInstallControls.lean` | Controls.ClassStateControls |
| `TypeSoundness/Controls/SingletonScopeControls.lean` | Controls.SingletonInstallControls |
| `TypeSoundness/Controls/SingletonStateControls.lean` | Controls.ClassHeaderControls |
| `TypeSoundness/Controls/SingletonTableControls.lean` | Controls.ClassHeaderControls |
| `TypeSoundness/Controls/SubclassCoreControls.lean` | Rules.Subclass.SubclassEntry |
| `TypeSoundness/Controls/SubclassDataControls.lean` | Rules.Subclass.SubclassEntry |
| `TypeSoundness/Controls/SubclassDispatchControls.lean` | Rules.Subclass.SubclassEntry |
| `TypeSoundness/Controls/SubclassEntryControls.lean` | Rules.Subclass.SubclassEntry |
| `TypeSoundness/Controls/SubclassHeaderControls.lean` | Rules.Subclass.SubclassHeaderEntry |
| `TypeSoundness/Controls/SubclassNameControls.lean` | Rules.Subclass.SubclassEntry |
| `TypeSoundness/Controls/SubclassRunControls.lean` | Rules.Subclass.SubclassRule (no such module) |
| `TypeSoundness/Controls/SubclassScopeControls.lean` | Rules.Subclass.SubclassEntry |
| `TypeSoundness/Controls/SubclassStateControls.lean` | Rules.Subclass.SubclassStateEntry |
| `TypeSoundness/Controls/SubclassTableControls.lean` | Rules.Subclass.SubclassEntry |
| `TypeSoundness/Controls/SymbolClosureControls.lean` | Rules.Closure.SymbolBody |
| `TypeSoundness/Controls/YieldMethodControls.lean` | Examples.YieldCall |
| `TypeSoundness/Examples/ClassDerivations.lean` | Examples.PointProgram |
| `TypeSoundness/Examples/CorpusSafety.lean` | Examples.Derivations |
| `TypeSoundness/Examples/FactoryDerivations.lean` | Controls.FactoryConstructorControls |
| `TypeSoundness/Examples/PointClass.lean` | Rules.Class.ClassHeaderRun |
| `TypeSoundness/Examples/PointConstructor.lean` | Examples.PointClass |
| `TypeSoundness/Examples/PointConstructorExpr.lean` | Examples.PointConstructor |
| `TypeSoundness/Examples/PointProgram.lean` | Examples.PointConstructorExpr |
| `TypeSoundness/Examples/YieldBody.lean` | Rules.Method.YieldInt |
| `TypeSoundness/Examples/YieldCall.lean` | Examples.YieldBody |
| `TypeSoundness/Registry/FullProofs.lean` | Rules.Class.ClassRules |
| `TypeSoundness/RuleAudit.lean` | RuleCoverage |
| `TypeSoundness/RuleCoverage.lean` | Examples.CorpusSafety |
| `TypeSoundness/Rules/Class/ClassHeaderRun.lean` | Conformance.Class.ClassHeader |
| `TypeSoundness/Rules/Class/ClassRules.lean` | Rules.Class.ClassHeaderRun |
| `TypeSoundness/Rules/Class/ClassRun.lean` | Conformance.Class.ClassState |
| `TypeSoundness/Rules/Closure/SymbolBody.lean` | Rules.Closure.Symbol |
| `TypeSoundness/Rules/Constructor/DefaultConstructor.lean` | Rules.Constructor.DefaultAllocation |
| `TypeSoundness/Rules/Module/ModuleEntry.lean` | Conformance.Module.ModuleCore |
| `TypeSoundness/Rules/Module/ModuleRule.lean` | Rules.Module.ModuleRun |
| `TypeSoundness/Rules/Module/ModuleRun.lean` | Rules.Module.ModuleStateEntry |
| `TypeSoundness/Rules/Module/ModuleStateEntry.lean` | Conformance.Module.ModuleState |
| `TypeSoundness/Rules/Subclass/SubclassEntry.lean` | Conformance.Subclass.SubclassCore |
| `TypeSoundness/Rules/Subclass/SubclassExpr.lean` | Rules.Subclass.SubclassRun |
| `TypeSoundness/Rules/Subclass/SubclassHeaderEntry.lean` | Conformance.Subclass.SubclassHeader |
| `TypeSoundness/Rules/Subclass/SubclassRun.lean` | Rules.Subclass.SubclassHeaderEntry |
| `TypeSoundness/Rules/Subclass/SubclassStateEntry.lean` | Conformance.Subclass.SubclassState |
