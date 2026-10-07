import Books.TypeSoundness.Rules.Closure.ShadowReturn

/-! Slot and lookup-owner preservation do not protect shadowed values. A parameter
may change its own value and a different capture, while the hidden caller value survives. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.ClosureShadowControls
open RubyCore Checker Checker.Soundness

private def outer : RubyCore.Frame :=
  { self := .int 0, defmod := 0, kind := .toplevel,
    locals := [("x", .nil), ("y", .int 1)], captured := none }
private def inner : RubyCore.Frame :=
  { self := .int 0, defmod := 0, kind := .block,
    locals := [("x", .int 2)], captured := some 0 }
private def caller (m : Machine) : Machine := { m with frames := #[outer], stack := [0] }
private def body (m : Machine) : Machine := pushMethodFrame (caller m) inner
private def bad (m : Machine) : Machine := setAt (body m) "x" (.int 9) 0

theorem bad_keeps_domains (m : Machine) (i : FrameId) (x : String) :
    frameBinds (bad m) i x = frameBinds (body m) i x := by
  by_cases hx : x = "x"
  · subst x
    by_cases hi : i = 0
    · subst i
      exact (frameBinds_setAt_mono (body m) "x" (.int 9) 0 0 "x" rfl).trans rfl
    · simp only [bad, frameBinds, setAt, framesD_set!_ne _ _ _ _ hi]
  · exact frameBinds_setAt_ne (body m) "x" (.int 9) 0 i hx

theorem bad_keeps_owners (m : Machine) : OwnersPres (body m) (bad m) := by
  intro hl x fuel _
  exact setLocal_owner_congr x _ (fun i _ => bad_keeps_domains m i x)
    (fun i _ => setAt_captured (body m) "x" (.int 9) 0 i) fuel _ hl

theorem bad_shadow_rejected (m : Machine) : ¬ ShadowPres (body m) (bad m) := by
  intro h
  have he := h "x" rfl 0 (by change 0 < 2; decide) (by change 0 ≠ 1; decide)
  change some ("x", Value.int 9) = some ("x", Value.nil) at he
  cases he

theorem parameter_write_preserves_caller (m : Machine) :
    (popMethodFrame (((body m).setLocal "x" (.int 9)).setLocal "y" (.int 7))).getLocal "x" =
      (caller m).getLocal "x" :=
  closure_shadowed_read (m := caller m) (f := inner)
    ⟨by change [0] ≠ []; decide, by change 0 < 1; decide⟩ rfl rfl
    ((Framed_setLocal (body m) "x" (.int 9)).trans
      (Framed_setLocal ((body m).setLocal "x" (.int 9)) "y" (.int 7))) "x" rfl

-- The other captured binding may still change; shadow preservation is per name.
example (m : Machine) :
    (popMethodFrame (((body m).setLocal "x" (.int 9)).setLocal "y" (.int 7))).getLocal "y" =
      .int 7 := rfl

#print axioms bad_keeps_owners
#print axioms bad_shadow_rejected
#print axioms parameter_write_preserves_caller
end Checker.Soundness.Typed.ClosureShadowControls
