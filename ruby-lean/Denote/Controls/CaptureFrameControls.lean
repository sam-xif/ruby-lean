import Denote.Rules.Closure.Return

/-! Captured writes are legal; damage to saved metadata or an unrelated frame is not.
The old frame contract admitted both kinds of damage at a captured activation. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.CaptureFrameControls
open RubyCore Ratchet Ratchet.Denote

private def outer : RubyCore.Frame :=
  { self := .int 0, defmod := 0, kind := .toplevel, locals := [("x", .int 1)] }
private def inner : RubyCore.Frame :=
  { self := .int 0, defmod := 0, kind := .block, captured := some 0 }
private def caller (m : Machine) : Machine := { m with frames := #[outer, outer], stack := [0] }
private def body (m : Machine) : Machine := pushMethodFrame (caller m) inner
private def badSelf (m : Machine) : Machine :=
  { body m with frames := (body m).frames.set! 0 { outer with self := .nil } }
private def badOther (m : Machine) : Machine :=
  { body m with frames := (body m).frames.set! 1 { outer with locals := [("x", .nil)] } }

private def LegacyFramePres (m n : Machine) : Prop :=
  m.frames.size ≤ n.frames.size ∧
  frameScope (n.frames.getD (n.stack.headD 0) default) =
    frameScope (m.frames.getD (m.stack.headD 0) default) ∧
  (RootUncaptured m → ∀ i, i < m.frames.size → i ≠ m.stack.headD 0 →
    n.frames.getD i default = m.frames.getD i default)

theorem legacy_allows_damage (m : Machine) :
    LegacyFramePres (body m) (badSelf m) ∧ LegacyFramePres (body m) (badOther m) := by
  constructor <;> refine ⟨by change 3 ≤ 3; decide, rfl, ?_⟩ <;>
    intro h <;> simp [RootUncaptured, body, caller, pushMethodFrame, inner, Array.getD] at h

theorem saved_self_damage_rejected (m : Machine) : ¬ FramePres (body m) (badSelf m) := by
  intro h
  have hs := congrArg RubyCore.Frame.self
    (h.saved 0 (by change 0 < 3; decide) (by change 0 ≠ 2; decide))
  change Value.nil = Value.int 0 at hs
  cases hs

theorem unrelated_local_damage_rejected (m : Machine) : ¬ FramePres (body m) (badOther m) := by
  intro h
  have hl : CaptureLive (body m) (some ((body m).stack.headD 0)) :=
    .frame (by change 2 < 3; decide) (.frame (by change 0 < 3; decide) .none)
  have hn : ¬ CapturePath (body m) (some ((body m).stack.headD 0)) 1 := by
    intro hp
    cases hp with
    | next hp =>
      have he := hp.uncaptured (by rfl)
      contradiction
  have hf := congrArg RubyCore.Frame.locals (h.outside hl 1 (by change 1 < 3; decide) hn)
  change [("x", Value.nil)] = [("x", Value.int 1)] at hf
  cases hf

theorem captured_write_returns_framed (m : Machine) :
    Framed (caller m) (popMethodFrame ((body m).setLocal "x" (.int 7))) :=
  closure_pop_framed (by change 0 < 2; decide) rfl rfl (Framed_setLocal (body m) "x" (.int 7))

theorem captured_write_changes_caller (m : Machine) :
    (caller m).getLocal "x" = .int 1 ∧
    (popMethodFrame ((body m).setLocal "x" (.int 7))).getLocal "x" = .int 7 := by
  exact ⟨rfl, rfl⟩

#print axioms legacy_allows_damage
#print axioms saved_self_damage_rejected
#print axioms unrelated_local_damage_rejected
#print axioms captured_write_returns_framed
#print axioms captured_write_changes_caller
end Ratchet.Denote.Typed.CaptureFrameControls
