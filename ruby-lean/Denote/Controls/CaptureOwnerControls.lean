import Denote.Rules.Closure.ReadReturn

/-! Existing domains alone permit active shadowing. Owner preservation excludes it,
while allowing captured writes through several frames and creation of fresh locals. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.CaptureOwnerControls
open RubyCore Ratchet Ratchet.Denote

private def outer : RubyCore.Frame :=
  { self := .nil, defmod := 0, kind := .toplevel, locals := [("x", .int 1)] }
private def inner (p : FrameId) : RubyCore.Frame :=
  { self := .nil, defmod := 0, kind := .block, captured := some p }
private def chain (m : Machine) : Machine :=
  { m with frames := #[outer, inner 0, inner 1], stack := [2] }
private def shadowed (m : Machine) : Machine := setAt (chain m) "x" .nil 2

theorem bindings_allow_shadow (m : Machine) : BindingsPres (chain m) (shadowed m) := by
  refine ⟨fun i _ x hx => frameBinds_setAt_mono (chain m) "x" .nil 2 i x hx, ?_⟩
  intro i _ hn x
  change i ≠ 2 at hn
  simp only [shadowed, frameBinds, setAt, framesD_set!_ne _ _ _ _ hn]

theorem owners_reject_shadow (m : Machine) : ¬ OwnersPres (chain m) (shadowed m) := by
  intro h
  have hl : CaptureLive (chain m) (some 2) :=
    .frame (by change 2 < 3; decide) (.frame (by change 1 < 3; decide)
      (.frame (by change 0 < 3; decide) .none))
  have he := h hl "x" 3 (by change 3 ≤ 4; decide)
  change 2 = 0 at he
  cases he

theorem nested_write (m : Machine) :
    OwnersPres (chain m) ((chain m).setLocal "x" (.int 7)) ∧
    ((chain m).setLocal "x" (.int 7)).getLocal "x" = .int 7 ∧
    frameBinds ((chain m).setLocal "x" (.int 7)) 2 "x" = false :=
  ⟨.setLocal _ _ _, rfl, rfl⟩

theorem fresh_local (m : Machine) :
    OwnersPres (chain m) ((chain m).setLocal "y" (.int 7)) ∧
    frameBinds ((chain m).setLocal "y" (.int 7)) 2 "y" = true ∧
    frameBinds ((chain m).setLocal "y" (.int 7)) 0 "y" = false :=
  ⟨.setLocal _ _ _, rfl, rfl⟩

private def caller (m : Machine) : Machine := { m with frames := #[outer], stack := [0] }
private def body (m : Machine) : Machine := pushMethodFrame (caller m) (inner 0)

theorem captured_write_read (m : Machine) :
    (popMethodFrame ((body m).setLocal "x" (.int 7))).getLocal "x" =
      ((body m).setLocal "x" (.int 7)).getLocal "x" :=
  closure_bound_read (m := caller m) (f := inner 0)
    ⟨by change ([0] : List FrameId) ≠ []; decide, by change 0 < 1; decide⟩ rfl rfl
    (Framed_setLocal (body m) "x" (.int 7)) "x" rfl rfl

#print axioms bindings_allow_shadow
#print axioms owners_reject_shadow
#print axioms nested_write
#print axioms fresh_local
#print axioms captured_write_read
end Ratchet.Denote.Typed.CaptureOwnerControls
