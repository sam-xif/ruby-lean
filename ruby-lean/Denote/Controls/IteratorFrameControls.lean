import Denote.Rules.Iterator.ReadReturn

/-! A block writes past the iterator activation into its caller. The caller projection
retains certified framing; imposing ordinary isolation on the iterator is false. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.IteratorFrameControls
open RubyCore Ratchet Ratchet.Denote

private def outer : RubyCore.Frame :=
  { self := .int 0, defmod := 0, kind := .toplevel, locals := [("x", .int 1)] }
private def iter : RubyCore.Frame :=
  { self := .nil, defmod := 0, kind := .method, meth := "each" }
private def blockFrame : RubyCore.Frame :=
  { self := .int 0, defmod := 0, kind := .block, captured := some 0 }
private def active (m : Machine) : Machine := { m with frames := #[outer, iter], stack := [1, 0] }
private def body (m : Machine) : Machine := pushMethodFrame (active m) blockFrame
private def written (m : Machine) : Machine := (body m).setLocal "x" (.int 7)

theorem caller_framed (m : Machine) :
    Framed (popMethodFrame (active m)) (popMethodFrame (popMethodFrame (written m))) :=
  iterator_pop_framed (by change 0 < 2; decide) rfl rfl
    (Framed_setLocal (body m) "x" (.int 7))

example (m : Machine) :
    (popMethodFrame (popMethodFrame (written m))).getLocal "x" = .int 7 := rfl

theorem iterator_isolation_false (m : Machine) :
    ¬ FramePres (active m) (popMethodFrame (written m)) := by
  intro h
  have he := h.isolated rfl 0 (by change 0 < 2; decide) (by change 0 ≠ 1; decide)
  have hl := congrArg RubyCore.Frame.locals he
  change [("x", Value.int 7)] = [("x", Value.int 1)] at hl
  cases hl

private def shadowFrame : RubyCore.Frame := { blockFrame with locals := [("x", .nil)] }
private def shadowBody (m : Machine) : Machine := pushMethodFrame (active m) shadowFrame

/-- Writing the parameter leaves the saved caller's same-named value alone. -/
theorem hidden_caller_retained (m : Machine) :
    (popMethodFrame (popMethodFrame ((shadowBody m).setLocal "x" (.int 9)))).getLocal "x" =
      (popMethodFrame (active m)).getLocal "x" :=
  iterator_shadowed_read (m := active m) (f := shadowFrame)
    ⟨by change [0] ≠ []; decide, by change 0 < 2; decide⟩ rfl rfl
    (Framed_setLocal (shadowBody m) "x" (.int 9)) "x" rfl

theorem capture_write_retained (m : Machine) :
    (popMethodFrame (popMethodFrame (written m))).getLocal "x" = (written m).getLocal "x" :=
  iterator_bound_read (m := active m) (f := blockFrame)
    ⟨by change [0] ≠ []; decide, by change 0 < 2; decide⟩ rfl rfl
    (Framed_setLocal (body m) "x" (.int 7)) "x" rfl rfl

theorem parameter_type_not_caller_value (m : Machine) :
    (popMethodFrame (popMethodFrame ((shadowBody m).setLocal "x" (.int 9)))).getLocal "x" ≠
      ((shadowBody m).setLocal "x" (.int 9)).getLocal "x" := by
  rw [hidden_caller_retained]
  change Value.int 1 ≠ Value.int 9
  intro h
  cases h

#print axioms caller_framed
#print axioms iterator_isolation_false
#print axioms hidden_caller_retained
#print axioms capture_write_retained
#print axioms parameter_type_not_caller_value
end Ratchet.Denote.Typed.IteratorFrameControls
