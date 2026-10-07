import Books.TypeSoundness.Rules.Super.SuperRun
import Books.TypeSoundness.Rules.Constructor.ConstructorState
import Books.TypeSoundness.Rules.Constructor.ConstructorLookup
import Books.TypeSoundness.Rules.Init.InitWrite
import Books.TypeSoundness.Soundness.Full
import Books.TypeSoundness.Denotation.DenB

/-! Checked declarations establish a real child initializer entry. A body-local super
pilot then consumes the parent's complete Integer domain, retaining a distinct child local.
The child's installed body is already supported; no super checker admission is claimed. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.SuperInitControls
open RubyCore Checker Checker.Soundness

def parentInit : Defn := ⟨"initialize", [.req "sides"], .vasgn .ivar "@sides" (.var .lvar "sides")⟩
def childInit : Defn := ⟨"initialize", [.req "saved"], .var .lvar "saved"⟩
def child : Cls := classWithMethod (subclassHeader "Wedge" "Polygon") childInit
def definitions : Checker.Expr := .seq [
  .class' "Polygon" none (.def' parentInit.name parentInit.params parentInit.body),
  .class' "Wedge" (some (.const "Polygon")) (.def' childInit.name childInit.params childInit.body)]
def hint : Deriv := .seq [
  .classDecl "Polygon" none (.defDecl "initialize" [("sides", .int)] .any
    (.ivarAsgn "@sides" (.var .lvar "sides"))),
  .classDecl "Wedge" (some "Polygon") (.defDecl "initialize" [("saved", .int)] .any (.var .lvar "saved"))]
def checked : Certified [] definitions := (check fuelD [] definitions hint).get (by decide +kernel)
@[irreducible] def baseCtx : Ctx := checked.ctx
theorem base_consts : baseCtx.consts = [] := by decide +kernel
theorem base_asms : baseCtx.asms = [] := List.eq_nil_of_length_eq_zero (by decide +kernel)
def caller : Ctx := initializerBodyCtxAt baseCtx "Wedge" "Wedge"
def callee : Ctx := initializerBodyCtxAt caller "Wedge" "Polygon"
def fields : Ty := .ivarCons "@sides" .int .ivar0
def route : SuperRoute caller.classes "Wedge" "Wedge" "Polygon" parentInit :=
  (superRoute? caller.classes "Wedge" "Wedge" "Polygon" parentInit).get (by decide +kernel)

theorem child_mem : child ∈ baseCtx.classes := by
  let f := (findClass "Wedge" baseCtx.classes).get (by decide +kernel)
  have he : f.cls = child := clsEqB_sound _ _ (by decide +kernel)
  exact he ▸ f.member

theorem parent_body : SemInitA callee [("sides", .int)] .ivar0 parentInit.body .any
    callee [("sides", .int)] fields :=
  (SemInitA.ivarAsgnChecked (SemInitA.var rfl rfl) (by decide +kernel)).ignoreResult

/-- Any Integer argument; the parent's proof is at its annotation, independently of it. -/
theorem nested_run {anchor : Heap} {m : Machine}
    (hm : InitState anchor caller [("saved", .int)] .ivar0 m) (v : Int) (hk : m.kont = []) :
    ∃ n, Interp.doSuper m [.int v] none = .next n ∧
      InitRunSpec anchor m n [("saved", .int)] .any caller fields := by
  exact declared_super_initializer_runSpec (receiver := child) (ps := [("sides", .int)])
    (κb := callee) (Γb := [("sides", .int)])
    hm (reframeTypesB_sound (by decide +kernel)) base_asms (reframeTypesB_sound (by decide +kernel))
    child_mem rfl rfl rfl rfl rfl rfl rfl rfl route rfl rfl
    (by simp [DenAll, denM, isIntV]) (by simp [FirstOrder, isAliasTy])
    (fun x => (constGet?_empty (κ := callee) base_consts x).trans (constGet?_empty (κ := caller) base_consts x).symm)
    rfl (by decide +kernel) (by decide +kernel)
    (fun x => (constGet?_empty (κ := callee) base_consts x).trans (constGet?_empty (κ := caller) base_consts x).symm)
    (by simp [IvarStable, stripAlias]) rfl hk parent_body

/-- The start is built from checked class execution, allocation and actual required-frame
entry. No code/heap lookup or initializer-state hypothesis is supplied by the control. -/
theorem after_definitions (hb : bootOkB = true) {fuel rest : Nat} {result : Value} {m : Machine}
    (hr : runA fuel (evalFrom bootMachine definitions) = .ans (.val result) m rest) (saved v : Int) :
    ∃ entry next, InitState m.heap caller [("saved", .int)] .ivar0 entry ∧
      Interp.doSuper entry [.int v] none = .next next ∧
      InitRunSpec m.heap entry next [("saved", .int)] .any caller fields := by
  have hs := certified_context checked
  have ho : checked.out = [] ∧ checked.spine = .ivar0 := by decide +kernel
  rw [ho.1, ho.2] at hs
  have hm : StateOk baseCtx [] .ivar0 m := by
    unfold baseCtx
    exact ((hs bootMachine (stateOk_boot hb)).2 fuel (.val result) m rest hr).2.2 result rfl
  obtain ⟨k, md, site, _, _, _, code, _⟩ := declared_constructor_code hm child_mem
    (d := childInit) (by change childInit ∈ [childInit]; simp) rfl (by decide +kernel) rfl
  obtain ⟨j, hj, alloc⟩ := hm.allocators "Wedge" (by decide +kernel)
  have he : j = k := Option.some.inj (hj.symm.trans site.named)
  subst j
  have hentry := constructor_frame_state_at (ps := [("saved", .int)]) (args := [.int saved])
    hm (reframeTypesB_sound (by decide +kernel)) base_asms alloc site site (hm.runtime (by decide +kernel)).phase code
    rfl (by simp [DenAll, denM, isIntV]) (by simp [FirstOrder, isAliasTy])
    (fun x => (constGet?_empty (κ := caller) base_consts x).trans (constGet?_empty base_consts x).symm)
  let entry := reCtl (constructorFrame m k md [("saved", .int)] [.int saved]) (.eval .nil) []
  have hi : InitState m.heap caller [("saved", .int)] .ivar0 entry := hentry.reCtl _ _
  obtain ⟨next, hd, hn⟩ := nested_run hi v rfl
  exact ⟨entry, next, hi, hd, hn⟩

-- Actual parent return keeps the object and the child's saved local, updating @sides.
#guard match Interp.run 120 (evalFrom bootMachine definitions) with
  | .value _ m => match Interp.run 60 (evalFrom m (.send (some (.const "Wedge")) "new" [.int 11] none)) with
    | .value recv n => match lookup n.heap recv "initialize" with
      | some (_, md) => match Interp.enterUserMethod n recv "initialize" md [.int 11] none with
        | .next entry => match Interp.doSuper (reCtl entry (.eval .nil) []) [.int 3] none with
          | .next next => match Interp.run 40 next with
            | .value _ last => last.currentFrame.self.identEq recv &&
                (last.getLocal "saved").identEq (.int 11) &&
                (ivarOf last.heap recv "@sides").identEq (.int 3) &&
                last.heap.objs.size == entry.heap.objs.size &&
                denB (.inst "Wedge" (.ivarCons "@sides" .nilT .ivar0)) entry.heap recv &&
                !denB (.inst "Wedge" (.ivarCons "@sides" .nilT .ivar0)) last.heap recv &&
                denB (.inst "Wedge" fields) last.heap recv
            | _ => false
          | _ => false
        | _ => false
      | none => false
    | _ => false
  | _ => false

#print axioms parent_body
#print axioms nested_run
#print axioms after_definitions
end Checker.Soundness.Typed.SuperInitControls
