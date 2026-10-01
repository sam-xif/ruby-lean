import Denote.Rules.Method.BodyRun

/-! Real writes in both frames belong to one method effect trace. Neither ordinary
method isolation nor a frozen suspended method describes the whole trace. Anchoring
the return before method allocation is necessary, not just a proof convenience. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.MethodEffectsControls
open RubyCore Ratchet Ratchet.Denote

private def outer : RubyCore.Frame :=
  { self := .nil, defmod := 0, kind := .toplevel, locals := [("total", .int 1)] }
private def method : RubyCore.Frame :=
  { self := .nil, defmod := 0, kind := .method, meth := "twice", locals := [("total", .int 99)] }
private def blockFrame : RubyCore.Frame :=
  { self := .nil, defmod := 0, kind := .block, captured := some 0 }
private def caller (m : Machine) : Machine := { m with frames := #[outer], stack := [0] }
private def entry (m : Machine) : Machine := pushMethodFrame (caller m) method
private def first (m : Machine) : Machine := (entry m).setLocal "total" (.int 2)
private def blockEntry (m : Machine) : Machine := pushMethodFrame (first m) blockFrame
private def blockWritten (m : Machine) : Machine := (blockEntry m).setLocal "total" (.int 7)
private def afterBlock (m : Machine) : Machine := popMethodFrame (blockWritten m)
private def done (m : Machine) : Machine := (afterBlock m).setLocal "fresh" .nil

private theorem first_eq (m : Machine) : first m =
    { m with frames := #[outer, { method with locals := [("total", .int 2)] }], stack := [1, 0] } := rfl

private theorem afterBlock_eq (m : Machine) : afterBlock m =
    { m with frames := #[{ outer with locals := [("total", .int 7)] },
      { method with locals := [("total", .int 2)] }, blockFrame], stack := [1, 0] } := by
  simp only [afterBlock, blockWritten, blockEntry, first_eq]
  rfl

private theorem done_eq (m : Machine) : done m =
    { m with frames := #[{ outer with locals := [("total", .int 7)] },
      { method with locals := [("fresh", .nil), ("total", .int 2)] }, blockFrame], stack := [1, 0] } := by
  simp only [done, afterBlock_eq]
  rfl

private theorem callback (m : Machine) : CallbackFramed (first m) (afterBlock m) :=
  callback_pop_framed
    ⟨by change [1, 0] ≠ []; decide, by change 1 < 2; decide⟩
    ⟨by change [0] ≠ []; decide, by change 0 < 2; decide⟩
    (by change 1 ≠ 0; decide) rfl rfl (Framed_setLocal (blockEntry m) "total" (.int 7))

theorem mixed (m : Machine) : MethodEffects (entry m) (done m) :=
  (MethodEffects.ordinary (Framed_setLocal (entry m) "total" (.int 2))).trans
    ((MethodEffects.callback (callback m)).trans (.ordinary (Framed_setLocal (afterBlock m) "fresh" .nil)))

theorem caller_return (m : Machine) : Framed (caller m) (popMethodFrame (done m)) :=
  (mixed m).project
    ⟨by change [0] ≠ []; decide, by change 0 < 1; decide⟩ rfl
    ⟨by change [1, 0] ≠ []; decide, by change 1 < 2; decide⟩ rfl (Nat.le_refl _)
    (method_pop_framed (by change 0 < 1; decide) rfl (Framed.refl (entry m)))

example (m : Machine) : (done m).getLocal "total" = .int 2 := by rw [done_eq]; rfl
example (m : Machine) : (popMethodFrame (done m)).getLocal "total" = .int 7 := by rw [done_eq]; rfl
example (m : Machine) : frameBinds (done m) 1 "fresh" = true := by rw [done_eq]; rfl
example (m : Machine) : frameBinds (done m) 0 "fresh" = false := by rw [done_eq]; rfl

theorem ordinary_contract_false (m : Machine) : ¬ Framed (entry m) (done m) := by
  intro h
  have hf := h.frames.isolated rfl 0 (by change 0 < 2; decide) (by change 0 ≠ 1; decide)
  rw [done_eq] at hf
  have he := congrArg RubyCore.Frame.locals hf
  change [("total", Value.int 7)] = [("total", Value.int 1)] at he
  cases he

theorem callback_contract_false (m : Machine) : ¬ CallbackFramed (entry m) (done m) := by
  intro h
  have he := congrArg RubyCore.Frame.locals h.active
  rw [done_eq] at he
  change [("fresh", Value.nil), ("total", Value.int 2)] = [("total", Value.int 99)] at he
  have hlen : (2 : Nat) = 1 := congrArg List.length he
  cases hlen

/-- If the origin already contains the method, Framed freezes its saved locals.
That later origin cannot replace the true caller entry used by MethodEffects.project. -/
theorem late_anchor_false (m : Machine) :
    ¬ Framed (popMethodFrame (entry m)) (popMethodFrame (done m)) := by
  intro h
  have hf := h.frames.isolated rfl 1 (by change 1 < 2; decide) (by change 1 ≠ 0; decide)
  rw [done_eq] at hf
  have he := congrArg RubyCore.Frame.locals hf
  change [("fresh", Value.nil), ("total", Value.int 2)] = [("total", Value.int 99)] at he
  have hlen : (2 : Nat) = 1 := congrArg List.length he
  cases hlen

#print axioms mixed
#print axioms caller_return
#print axioms ordinary_contract_false
#print axioms callback_contract_false
#print axioms late_anchor_false
end Ratchet.Denote.Typed.MethodEffectsControls
