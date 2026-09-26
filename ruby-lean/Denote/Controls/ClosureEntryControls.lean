import Denote.Rules.Closure.Entry
import Denote.Rules.Closure.Literal
import Denote.Rules.Method.MethodReturn

/-! Real lambda activation, shadowing and metadata. The existing answer contract does
not yet justify the block continuation: next/break may become untyped return values. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.ClosureEntryControls
open RubyCore Ratchet Ratchet.Denote

private def caller : Machine := (bootMachine.setLocal "x" (.int 7)).setLocal "z" (.int 9)
private def closure : Closure :=
  reifiedClosure caller [.req "x", .req "y"] ["z"] (.var .lvar "x") true
private def entered : Machine :=
  match Interp.callClosure caller closure [.int 2, .int 3] none with
  | .next n => n
  | _ => caller

#guard (entered.getLocal "x").identEq (.int 2)
#guard (entered.getLocal "y").identEq (.int 3)
#guard (entered.getLocal "z").identEq .nil
#guard (entered.getLocal "missing").identEq .nil
#guard entered.currentFrame.captured == some (caller.stack.headD 0)
#guard entered.currentFrame.home == closure.home
#guard entered.currentFrame.cref == caller.currentFrame.cref
#guard entered.currentFrame.kind == .block
#guard entered.currentFrame.lam
#guard entered.stack == caller.frames.size :: caller.stack

-- Removing the block-local declaration exposes the current captured value.
#guard match Interp.callClosure caller { closure with locals := [] } [.int 2, .int 3] none with
  | .next n => (n.getLocal "z").identEq (.int 9)
  | _ => false
-- Parameters win even if an untrusted descriptor repeats one as a block-local.
#guard match Interp.callClosure caller { closure with locals := ["x"] } [.int 2, .int 3] none with
  | .next n => (n.getLocal "x").identEq (.int 2)
  | _ => false
-- A lambda keeps an Array as one argument; it does not use proc auto-splatting.
#guard let (v, m) := Builtins.allocArr caller #[.int 2, .int 3]
  match Interp.callClosure m closure [v] none with
  | .next n => Semantics.typeStuck (Interp.run 20 n)
  | _ => false
#guard match Interp.callClosure caller closure [.int 2, .int 3] none
    (some (.int 42)) (some Boot.integerId) with
  | .next n => n.currentFrame.self.identEq (.int 42) &&
      n.currentFrame.defmod == Boot.integerId && n.currentFrame.cref == caller.currentFrame.cref
  | _ => false

theorem reified_live {m : Machine} (hr : FrameInRange m)
    (hu : m.currentFrame.captured = none) (ps : List RubyCore.Param)
    (ls : List String) (body : RubyCore.Expr) (lam : Bool) :
    CaptureLive (reifiedMachine m ps ls body lam)
      (reifiedClosure m ps ls body lam).captured :=
  reified_captureLive hr (hu ▸ CaptureLive.none) ps ls body lam

/-- A next escape meets today's complete ResultOk contract at any promised type. -/
theorem next_result {m : Machine} {Γ : Env} {τ I : Ty} {κ : Ctx} (v : Value) :
    ResultOk m Γ τ (.esc (.nxtJ v)) m κ I :=
  ⟨Framed.refl m, trivial, fun _ h => by cases h⟩

/-- F50: the real block continuation converts that escape into an ordinary result.
The Integer promise supplies neither its value type nor outgoing StateOk. -/
theorem next_returns_nil (m : Machine) (fid : FrameId) (lam : Bool)
    (brk : Option FrameId) (cl : Closure) (args : List Value) :
    Interp.stepFn (deliverA (.esc (.nxtJ .nil)) m [.blkFrameK fid lam brk cl args]) =
      .next (deliverA (.val .nil) (popMethodFrame m) []) ∧
    ¬ denM .int (popMethodFrame m) .nil := ⟨rfl, by simp [denM, isIntV]⟩

#print axioms reified_live
#print axioms next_result
#print axioms next_returns_nil
end Ratchet.Denote.Typed.ClosureEntryControls
