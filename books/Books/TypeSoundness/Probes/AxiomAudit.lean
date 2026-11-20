import Books.TypeSoundness.Soundness
import Books.TypeSoundness.Registry.GateStatus
import Books.TypeSoundness.Controls.MethodAliasControls
import Books.TypeSoundness.Controls.MethodCodeControls
import Books.TypeSoundness.Controls.FrozenDefinitionControls
import Books.TypeSoundness.Controls.MethodDefinitionControls
import Books.TypeSoundness.Controls.MethodOriginControls
import Books.TypeSoundness.Controls.MethodPrefixControls
import Books.TypeSoundness.Controls.MethodDefineeControls
import Books.TypeSoundness.Controls.ClassHookControls
import Books.TypeSoundness.Controls.AllocationReadyControls
import Books.TypeSoundness.Controls.ConstantReachControls
import Books.TypeSoundness.Conformance.Class.ClassRegistration
import Books.TypeSoundness.Conformance.Instance.MainSiteWrite
import Books.TypeSoundness.Rules.Class.ClassCallbacks
import Books.TypeSoundness.Rules.Class.ClassEntry
import Books.TypeSoundness.Conformance.Class.ClassNameEntryActual
import Books.TypeSoundness.Conformance.Class.ClassTablesActual
import Books.TypeSoundness.Conformance.Class.ClassMainActual
import Books.TypeSoundness.Conformance.Class.ClassChainsActual
import Books.TypeSoundness.Conformance.Class.ClassSitesActual
import Books.TypeSoundness.Conformance.Class.ClassStateActual
import Books.TypeSoundness.Conformance.Class.ClassHeaderStateActual
import Books.TypeSoundness.Rules.Class.ClassRunActual
import Books.TypeSoundness.Conformance.Class.ClassPayloadActual
import Books.TypeSoundness.Examples.RecursiveDerivations

namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

#print axioms freshClassRegistered_named
#print axioms freshClassNamed_ready
#print axioms stepFn_class_registered
#print axioms MainSite.ivarOnly
#print axioms invoke_native_class_hook
#print axioms stepFn_class_hook
#print axioms class_callbacks_runSpec
#print axioms FreshClassActual.chainsIn
#print axioms FreshClassActual.saturated
#print axioms FreshClassActual.classHooksQuietB_eq
#print axioms FreshClassActual.allocator_ready
#print axioms stepFn_class_fresh
#print axioms FreshClassActual.namesOk
#print axioms FreshClassActual.className_old
#print axioms FreshClassActual.className_eigen
#print axioms FreshClassActual.constRefsLive
#print axioms FreshClassActual.rootNames
#print axioms FreshClassActual.fallback_old
#print axioms FreshClassActual.classReady
#print axioms FreshClassActual.dataPres
#print axioms FreshClassActual.framed
#print axioms FreshClassActual.core
#print axioms FreshClassActual.method_source
#print axioms FreshClassActual.shadow_before_source
#print axioms FreshClassActual.singleton_query_free
#print axioms FreshClassActual.primitiveDispatch
#print axioms FreshClassActual.primitiveErrors
#print axioms FreshClassActual.query
#print axioms FreshClassActual.clsQuery
#print axioms FreshClassActual.nilQuery
#print axioms FreshClassActual.stringPayload
#print axioms FreshClassActual.arrayPayload
#print axioms FreshClassActual.hashPayload
#print axioms FreshClassActual.machine_callback
#print axioms FreshClassActual.env_empty
#print axioms FreshClassActual.spine_empty
#print axioms FreshClassActual.self_type
#print axioms FreshClassActual.saved_frame
#print axioms FreshClassActual.own_code
#print axioms FreshClassActual.classes
#print axioms FreshClassActual.defs
#print axioms FreshClassActual.methodsExact
#print axioms FreshClassActual.scope_ready
#print axioms FreshClassActual.nameFree
#print axioms FreshClassActual.main_constants
#print axioms FreshClassActual.instance_constants_fresh
#print axioms FreshClassActual.const_scope
#print axioms FreshClassActual.fallback_fresh_meta
#print axioms FreshClassActual.constants
#print axioms FreshClassActual.paths
#print axioms FreshClassActual.nested
#print axioms FreshClassActual.metadata_old
#print axioms FreshClassActual.plain_ready_old
#print axioms FreshClassActual.mainSite
#print axioms FreshClassActual.declared
#print axioms FreshClassActual.ownNames
#print axioms FreshClassActual.classChains
#print axioms FreshClassActual.allocators
#print axioms FreshClassActual.globalConsts
#print axioms FreshClassActual.plain
#print axioms FreshClassActual.ordered_chain
#print axioms FreshClassActual.ownNames_header
#print axioms FreshClassActual.classChains_header
#print axioms ConstantReachControls.old_site_not_preserved
#print axioms FreshClassActual.const_from_old_fresh
#print axioms FreshClassActual.instance_constants_old
#print axioms FreshClassActual.instance_object_reach
#print axioms FreshClassActual.moduleBase
#print axioms FreshClassActual.meta_old
#print axioms FreshClassActual.meta_fresh
#print axioms FreshClassActual.instanceSite_old
#print axioms FreshClassActual.instanceSite

#eval IO.println s!"CLINK REBUILD: {dRegisteredRules.length} certified, {dGatedRules.length} gated, {dAllRules.length} total"
#eval IO.println s!"  enabled: {String.intercalate ", " dRegisteredRules}"

-- These controls follow the active profile rather than pinning every literal on.
-- Disabling an optional literal must remove its acceptance and its clink reference.
#guard validateD (.int 7) (.intLit 7) == clinkEnabled "intLit"
#guard validateD (.flt 0) (.fltLit 0) == clinkEnabled "fltLit"
#guard validateD (.str "ok") (.strLit "ok") == clinkEnabled "strLit"
#guard validateD (.sym "ok") (.symLit "ok") == clinkEnabled "symLit"
#guard validateD .tru .truLit == clinkEnabled "truLit"
#guard validateD .fls .flsLit == clinkEnabled "flsLit"
#guard validateD .nil .nilLit == clinkEnabled "nilLit"
#guard !validateD (.int 7) (.intLit 8)
#guard validateD (.int 7) (.flow (.intLit 7)) ==
  ["flow", "DFlow.intLit"].all clinkEnabled
#guard validateD (.seq [.int 7]) (.seq [.intLit 7]) ==
  ["seq", "DJudgeSeq.last", "intLit"].all clinkEnabled

-- A real model-safety witness, alongside the fixture-only registration controls.
theorem rebuilt_int_safe {m : Machine} (hm : StateOk ctx0 [] .ivar0 m) :
    StuckFree m (.int 0) := validateD_safe (by decide :
      validateD (.int 0) (.intLit 0) = true) hm
#print axioms rebuilt_int_safe

-- The subset bridge reaches the exact executable runner used by the full gate.
theorem rebuilt_int_safe_run (hb : bootOkB = true) (fuel : Nat) :
    Semantics.typeStuck (Semantics.run fuel (toRuby (.int 0))) = false :=
  validateD_safe_run (by decide :
    validateD (.int 0) (.intLit 0) = true) hb fuel
#print axioms rebuilt_int_safe_run
-- This same production theorem covers compounds as soon as their trace is enabled.
theorem rebuilt_sequence_safe_run
    (he : ["seq", "DJudgeSeq.last", "intLit"].all clinkEnabled = true)
    (hb : bootOkB = true) (fuel : Nat) :
    Semantics.typeStuck (Semantics.run fuel (toRuby (.seq [.int 7]))) = false :=
  validateD_safe_run (p := .seq [.int 7]) (d := .seq [.intLit 7]) he hb fuel
#print axioms rebuilt_sequence_safe_run
theorem rebuilt_sequence_pair_safe_run (hb : bootOkB = true) (fuel : Nat) :
    Semantics.typeStuck (Semantics.run fuel (toRuby (.seq [.int 7, .str "ok"]))) = false :=
  validateD_safe_run (by decide :
    validateD (.seq [.int 7, .str "ok"]) (.seq [.intLit 7, .strLit "ok"]) = true) hb fuel
#print axioms rebuilt_sequence_pair_safe_run
theorem rebuilt_local_retype_safe_run (hb : bootOkB = true) (fuel : Nat) :
    Semantics.typeStuck (Semantics.run fuel (toRuby
      (.seq [.vasgn .lvar "x" (.int 1), .vasgn .lvar "x" .nil, .var .lvar "x"]))) = false :=
  validateD_safe_run (by decide : validateD
    (.seq [.vasgn .lvar "x" (.int 1), .vasgn .lvar "x" .nil, .var .lvar "x"])
    (.seq [.vasgn .lvar "x" (.intLit 1), .vasgn .lvar "x" .nilLit, .var .lvar "x"]) = true) hb fuel
#print axioms rebuilt_local_retype_safe_run
-- Division by zero is an escaping non-type error, still safe for this contract.
theorem rebuilt_primitive_escape_safe_run (hb : bootOkB = true) (fuel : Nat) :
    Semantics.typeStuck (Semantics.run fuel (toRuby
      (.send (some (.int 1)) "/" [.int 0] none))) = false :=
  validateD_safe_run (by decide : validateD
    (.send (some (.int 1)) "/" [.int 0] none)
    (.prim (.intLit 1) "/" [.intLit 0] .int .int) = true) hb fuel
#print axioms rebuilt_primitive_escape_safe_run
theorem rebuilt_missing_else_safe_run (hb : bootOkB = true) (fuel : Nat) :
    Semantics.typeStuck (Semantics.run fuel (toRuby (.if' .fls (.int 1) none))) = false :=
  validateD_safe_run (by decide : validateD (.if' .fls (.int 1) none)
    (.ifD .flsLit (.intLit 1) none (.nilable .int)) = true) hb fuel
#print axioms rebuilt_missing_else_safe_run
theorem rebuilt_bare_name_safe_run (hb : bootOkB = true) (fuel : Nat) :
    Semantics.typeStuck (Semantics.run fuel (toRuby (.vcall "x"))) = false :=
  validateD_safe_run (by decide : validateD (.vcall "x") (.bareName "x") = true) hb fuel
#print axioms rebuilt_bare_name_safe_run
theorem rebuilt_array_bounds_safe_run (hb : bootOkB = true) (fuel : Nat) :
    Semantics.typeStuck (Semantics.run fuel (toRuby
      (.send (some (.array [.int 1])) "[]" [.int 2] none))) = false :=
  validateD_safe_run (by decide : validateD
    (.send (some (.array [.int 1])) "[]" [.int 2] none)
    (.prim (.arrayLit [.intLit 1] .int) "[]" [.intLit 2] (.arrayOf .int) (.nilable .int)) = true) hb fuel
#print axioms rebuilt_array_bounds_safe_run
theorem rebuilt_duplicate_hash_safe_run (hb : bootOkB = true) (fuel : Nat) :
    Semantics.typeStuck (Semantics.run fuel (toRuby
      (.hash [(.sym "k", .int 1), (.sym "k", .int 2)]))) = false :=
  validateD_safe_run (by decide : validateD
    (.hash [(.sym "k", .int 1), (.sym "k", .int 2)])
    (.hashLit [.symLit "k", .symLit "k"] [.intLit 1, .intLit 2] .sym .int) = true) hb fuel
#print axioms rebuilt_duplicate_hash_safe_run
theorem rebuilt_identity_call_safe_run (hb : bootOkB = true) (fuel : Nat) :
    Semantics.typeStuck (Semantics.run fuel (toRuby
      (.seq [.def' "identity" [.req "x"] (.var .lvar "x"),
        .send none "identity" [.int 7] none]))) = false :=
  validateD_safe_run (by decide : validateD
    (.seq [.def' "identity" [.req "x"] (.var .lvar "x"),
      .send none "identity" [.int 7] none])
    (.seq [.defDecl "identity" [("x", .int)] .int (.var .lvar "x"),
      .callSig "identity" [.intLit 7] .int]) = true) hb fuel
#print axioms rebuilt_identity_call_safe_run
#print axioms validateD_safe_run
end Checker.Soundness.Typed
#print axioms Checker.Soundness.FreshClassActual.state
#print axioms Checker.Soundness.FreshClassActual.header
#print axioms Checker.Soundness.classNativeQuietB_singleton
#print axioms Checker.Soundness.Typed.class_actual_runSpec
