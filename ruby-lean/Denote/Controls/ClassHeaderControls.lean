import Denote.Sem.Class.ClassHeader
import Denote.Controls.ClassStateControls
import Denote.Rules.Method.MethodDefine

/-! Real class entry publishes metadata only. Inherited initialization remains a separate
call obligation; future body statements have not installed or certified any method. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem class_entry_header {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {name : String} {body : Ratchet.Expr} (hm : StateOk κ Γ I m)
    (hr : κ.scope.runtimeMain = true) (hw : κ.pos.mainWorld = true)
    (hf : κ.frame = none) (ha : κ.asms = [])
    (ht : ClassTablesFrame κ name m) (hq : FreshClass.nativeFrameB κ name = true)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false)
    (hnew : nameFreeN κ "new" = true) (hquiet : FreshClass.NativeQuiet name "new")
    (hplain : unqualifiedClassB name = true) (hframe : headerTableFrameB κ.classes name = true) :
    ∃ n, Interp.stepFn (evalFrom m (.class' name none body)) = .next n ∧
      StateOk (classHeaderCtx (classBodyCtx κ name) name) [] .ivar0 n := by
  obtain ⟨e, he, hstep⟩ := stepFn_class_fresh hm hr hn hne
  refine ⟨_, hstep, ?_⟩
  have hs := FreshClass.state (body := toRuby body)
    (StateOk_reCtl hm (.eval (toRuby (.class' name none body))) []) hr hf ha (ht.heap rfl)
    (FreshClass.nativeFrameB_sound hq) hn hne he
  apply StateOk_publish_header hs rfl hplain
  · exact FreshClass.declared_header hm.core.classReady hm.sat hm.core.rootNames
      (hm.runtime hr).classLive hn hne he hquiet ((hm.mainSite hw).newDispatch hnew) rfl
      hm.classes hm.declCls (headerTableFrameB_sound hframe)
  · exact ⟨m.heap.objs.size, classNamed_freshClass (hm.runtime hr).classLive
      hm.core.classReady.chains.boot.2.2.2.2, FreshClass.plain hm.core hm.sat⟩
  · exact FreshClass.ownNames_header hm.core.classReady.chains.boot.2.2.2.2
      (hm.runtime hr).classLive hn hm.classes hm.ownNames
  · exact FreshClass.classChains_header hm.core.classReady hm.sat hm.core.rootNames
      (hm.runtime hr).classLive hn hm.classes hm.classChains (headerTableFrameB_sound hframe)

theorem boot_point_header (hb : bootOkB = true)
    (hn : constOwn bootMachine.heap Boot.objectId "Point" = none) (body : Ratchet.Expr) :
    ∃ n, Interp.stepFn (evalFrom bootMachine (.class' "Point" none body)) = .next n ∧
      StateOk (classHeaderCtx (classBodyCtx ctx0 "Point") "Point") [] .ivar0 n := by
  exact class_entry_header (stateOk_boot hb) rfl rfl rfl rfl
    (ClassTablesFrame.empty rfl rfl) (by decide) hn (by decide)
    rfl (by constructor <;> decide) (by decide) (by decide)

-- Header publication cannot grant a callable signature, even if the upcoming body is a def.
#guard ctorGet? (classHeaderCtx ctx0 "Point").classes "Point" |>.isNone
#guard (mroGet? (classHeaderCtx ctx0 "Point").classes "Point" "getX").isNone
#guard unqualifiedClassB "Point"
#guard !unqualifiedClassB "Outer::Point"
#guard (constOwn bootMachine.heap Boot.objectId "Point").isNone

private def inheritedDecl : Defn := ⟨"initialize", [.req "x"], .var .lvar "x"⟩
private def inheritedCtx : Ctx := topDeclCtx ctx0 inheritedDecl
private def inheritedBoot : Machine :=
  installMethod bootMachine "initialize" [.req "x"] (.var .lvar "x")

-- Full conformance with a real Object#initialize. This is heap/code publication, not
-- admission of an unchecked method: the identity body is independently annotation-safe.
private theorem inherited_state (hb : bootOkB = true) :
    StateOk inheritedCtx [] .ivar0 inheritedBoot := by
  have hm := stateOk_boot hb
  have ready := hm.runtime rfl
  have h := StateOk_defineTopMethod (d := inheritedDecl)
    (md := definedMethod bootMachine "initialize" [.req "x"] (.var .lvar "x"))
    (StateOk_reserveName hm "initialize") (ReframeFO.empty rfl rfl rfl rfl)
    (by simp) rfl rfl (by decide) (by decide) (by decide) ready.classLive
    (by simp [ctx0, Ctx.defs]) rfl rfl rfl
    (definedMethod_code ready.owner ready.cref ready.phase)
  simpa only [inheritedBoot, installMethod, ready.owner, inheritedCtx, inheritedDecl,
    topDeclCtx, reserveNameCtx] using h

example : SemSafeCtxA (topBodyCtx ctx0 inheritedDecl) [("x", .int)] .ivar0
    inheritedDecl.body .int (topBodyCtx ctx0 inheritedDecl) [("x", .int)] .ivar0 :=
  SemSafeCtxA.var rfl rfl

theorem inherited_point_header (hb : bootOkB = true)
    (hn : constOwn bootMachine.heap Boot.objectId "Point" = none) :
    ∃ n, Interp.stepFn (evalFrom inheritedBoot (.class' "Point" none .nil)) = .next n ∧
      StateOk (classHeaderCtx (classBodyCtx inheritedCtx "Point") "Point") [] .ivar0 n := by
  apply class_entry_header (inherited_state hb) rfl rfl rfl rfl
    (ClassTablesFrame.empty rfl rfl) (by decide) _ (by decide)
    (by decide) (by constructor <;> decide) (by decide) (by decide)
  simpa only [inheritedBoot, installMethod, Proof.constOwn_defineMethod] using hn

#guard match Interp.enterClassBody inheritedBoot "Point" false none .nil with
  | .next n =>
      (n.heap.classPayload? n.currentFrame.defmod).any (·.methods.isEmpty) &&
      (Interp.userInit? n.heap n.currentFrame.defmod).any
        (fun md => md.owner == Boot.objectId && md.params.length == 1) &&
      match Interp.run 100 n with
      | .value _ m => match Interp.run 100
          (evalFrom m (.send (some (.const "Point")) "new" [] none)) with
        | .uncaught exc result => isAName result.heap exc "ArgumentError"
        | _ => false
      | _ => false
  | _ => false

#print axioms class_entry_header
#print axioms boot_point_header
#print axioms inherited_point_header
end Ratchet.Denote.Typed
