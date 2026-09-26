import Denote.Rules.Method.Yield
import Denote.Rules.Expr.Send

/-! A typed captured write crosses a real ordinary-method activation. The method's
same-named local stays intact, and ordinary Framed at that method is provably false. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.TypedYieldControls
open RubyCore Ratchet Ratchet.Denote

private def body : Ratchet.Expr := .vasgn .lvar "total"
  (.send (some (.var .lvar "total")) "+" [.var .lvar "x"] none)
private def closure (m : Machine) : Closure :=
  { params := [.req "x"], locals := [], body := toRuby body,
    captured := some ((popMethodFrame m).stack.headD 0), home := 0, lam := false }
private def Γ : Env := [("total", .int)]
private def Γb : Env := [("x", .int), ("total", .int)]

private theorem body_typed : SemSafeCtxA (closureBodyCtx ctx0) Γb .ivar0 body .int
    (closureBodyCtx ctx0) Γb .ivar0 :=
  ((SemSafeCtxA.var rfl rfl).prim (.cons (SemSafeCtxA.var rfl rfl) .nil rfl)
    .intAdd rfl (by intro h; cases h)).vasgn rfl rfl rfl

/-- Checked block code, real doYield and both return markers. The block argument is
Integer, its write preserves the captured type, and no body or return-state premise remains. -/
theorem captured_write_yield {m : Machine} {o : ObjId} (fid : FrameId) (arg : Int)
    (hs : StateOk ctx0 Γ .ivar0 (popMethodFrame m))
    (hm : FrameInRange m) (hne : m.stack.headD 0 ≠ (popMethodFrame m).stack.headD 0)
    (hslots : CaptureSlots ["total"] Γ (popMethodFrame m))
    (hk : m.kont = [.frameK fid]) (hblk : m.currentFrame.blk = some (.ref o))
    (hproc : (m.heap.get o).payload = .proc (closure m)) :
    StepSpec (popMethodFrame m) Γ .int (Interp.doYield m [.int arg]) ctx0 .ivar0 := by
  apply typed_yield_continue (cl := closure m) (ps := [("x", .int)]) (names := ["total"])
    (args := [.int arg])
    (Γb := Γb) (body := body) ⟨hs, rfl, hslots⟩ hm hne hk
    (by intro k hmem tag; simp only [List.mem_singleton] at hmem; subst k; simp)
    hblk hproc rfl rfl rfl ⟨by simp [denM, isIntV], trivial⟩
    rfl rfl rfl rfl rfl body_typed
  intro a n hret
  exact hret.methodReturn rfl fid

/-- The source-level yield evaluates its argument before entering the checked block. -/
theorem captured_write_source {m : Machine} {o : ObjId} (fid : FrameId) (arg : Int)
    (hs : StateOk ctx0 Γ .ivar0 (popMethodFrame m))
    (hm : FrameInRange m) (hne : m.stack.headD 0 ≠ (popMethodFrame m).stack.headD 0)
    (hslots : CaptureSlots ["total"] Γ (popMethodFrame m))
    (hblk : m.currentFrame.blk = some (.ref o))
    (hproc : (m.heap.get o).payload = .proc (closure m)) :
    RunSpec (popMethodFrame m)
      (pushK [.frameK fid] (evalFrom m (.yield' [.int arg]))) Γ .int ctx0 .ivar0 := by
  apply RunSpec.step (by rfl) (show Interp.stepFn _ = .next
    (pushK [.yieldArgK [] [], .frameK fid] (evalFrom m (.int arg))) from rfl)
  apply RunSpec.step (by rfl) (show Interp.stepFn _ = .next
    (deliverA (.val (.int arg)) m [.yieldArgK [] [], .frameK fid]) from rfl)
  apply RunSpec.of_stepSpec (by rfl)
  exact (captured_write_yield (m := deliverA (.val (.int arg)) m [.frameK fid])
    fid arg (by simpa only [popMethodFrame, deliverA] using
      (StateOk_deliverA (a := .val (.int arg)) (K := [.frameK fid]) hs))
    hm hne hslots rfl hblk hproc).rebase (Framed_reCtl _ _ _)

private def outer : RubyCore.Frame :=
  { self := .nil, defmod := 0, kind := .toplevel, locals := [("total", .int 1)] }
private def method : RubyCore.Frame :=
  { self := .nil, defmod := 0, kind := .method, meth := "twice", locals := [("total", .int 99)] }
private def blockFrame : RubyCore.Frame :=
  { self := .nil, defmod := 0, kind := .block, captured := some 0 }
private def active (m : Machine) : Machine := { m with frames := #[outer, method], stack := [1, 0] }
private def entry (m : Machine) : Machine := pushMethodFrame (active m) blockFrame
private def written (m : Machine) : Machine := (entry m).setLocal "total" (.int 7)

theorem callback_framed (m : Machine) : CallbackFramed (active m) (popMethodFrame (written m)) :=
  callback_pop_framed
    ⟨by change [1, 0] ≠ []; decide, by change 1 < 2; decide⟩
    ⟨by change [0] ≠ []; decide, by change 0 < 2; decide⟩
    (by change 1 ≠ 0; decide) rfl rfl (Framed_setLocal (entry m) "total" (.int 7))

example (m : Machine) : (popMethodFrame (written m)).currentFrame = method :=
  (callback_framed m).active

example (m : Machine) :
    (popMethodFrame (popMethodFrame (written m))).getLocal "total" = .int 7 := rfl

theorem method_isolation_false (m : Machine) :
    ¬ Framed (active m) (popMethodFrame (written m)) := by
  intro h
  have he := h.frames.isolated rfl 0 (by change 0 < 2; decide) (by change 0 ≠ 1; decide)
  have hl := congrArg RubyCore.Frame.locals he
  change [("total", Value.int 7)] = [("total", Value.int 1)] at hl
  cases hl

/-- The return contract also rejects corruption of the suspended method. -/
theorem method_damage_rejected (m : Machine) :
    ¬ CallbackFramed (active m) ((active m).setLocal "total" .nil) := by
  intro h
  have hl := congrArg RubyCore.Frame.locals h.active
  change [("total", Value.nil)] = [("total", Value.int 99)] at hl
  cases hl

#print axioms captured_write_yield
#print axioms captured_write_source
#print axioms callback_framed
#print axioms method_isolation_false
#print axioms method_damage_rejected
end Ratchet.Denote.Typed.TypedYieldControls
