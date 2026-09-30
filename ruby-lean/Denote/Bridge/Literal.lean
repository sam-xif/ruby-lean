import Denote.Bridge

/-! Compatibility API for the earlier literal-only bridge. The original
validateD and Bridge.lean now enforce and prove the active clink boundary. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

abbrev validateActiveLiteralD := validateD

theorem validateActiveLiteralD_certified {p : Ratchet.Expr} {d : Deriv}
    (h : validateActiveLiteralD p d = true) :
    ∃ τ, (DJudgeC dclinks).judge [] p τ [] ctx0 .ivar0 := validateD_certified h

theorem validateActiveLiteralD_safe {p : Ratchet.Expr} {d : Deriv}
    (h : validateActiveLiteralD p d = true)
    {m : Machine} (hm : StateOk ctx0 [] .ivar0 m) : StuckFree m p := validateD_safe h hm

theorem validateActiveLiteralD_safe_boot {p : Ratchet.Expr} {d : Deriv}
    (h : validateActiveLiteralD p d = true) (hb : bootOkB = true) :
    StuckFree bootMachine p := validateD_safe_boot h hb

theorem validateActiveLiteralD_safe_run {p : Ratchet.Expr} {d : Deriv}
    (h : validateActiveLiteralD p d = true) (hb : bootOkB = true) (fuel : Nat) :
    Semantics.typeStuck (Semantics.run fuel (toRuby p)) = false := validateD_safe_run h hb fuel
end Ratchet.Denote.Typed
