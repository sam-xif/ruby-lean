import Denote.Sem.Core.Alloc
import Denote.Sem.Core.Transport
import Denote.Sem.Closure.Capture

/-! Literal block allocation preserves full conformance and records every field the
call engine reads. No callable typing rule is admitted by this allocation lemma. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

/-- The code, capture and return metadata installed by the real block allocator. -/
def reifiedClosure (m : Machine) (ps : List RubyCore.Param) (ls : List String)
    (body : RubyCore.Expr) (lam : Bool) : Closure :=
  { params := ps, locals := ls, body, captured := some (m.stack.headD 0),
    home := Interp.returnTarget m, lam }

def reifiedMachine (m : Machine) (ps : List RubyCore.Param) (ls : List String)
    (body : RubyCore.Expr) (lam : Bool) : Machine :=
  let obj : Object := { klass := Boot.procId, payload := .proc (reifiedClosure m ps ls body lam) }
  { m with heap := pushHeap m.heap obj }

theorem reifyBlock_eq (m : Machine) (ps : List RubyCore.Param) (ls : List String)
    (body : RubyCore.Expr) (lam : Bool) :
    Interp.reifyBlock m ps ls body lam =
      (.ref m.heap.objs.size, reifiedMachine m ps ls body lam) := rfl

theorem reified_payload (m : Machine) (ps : List RubyCore.Param) (ls : List String)
    (body : RubyCore.Expr) (lam : Bool) :
    procClosure? (reifiedMachine m ps ls body lam).heap (.ref m.heap.objs.size) =
      some (reifiedClosure m ps ls body lam) := by
  simp [reifiedMachine, procClosure?, pushHeap_get_self]

theorem reified_ext {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) (ps : List RubyCore.Param) (ls : List String)
    (body : RubyCore.Expr) (lam : Bool) : Ext m (reifiedMachine m ps ls body lam) :=
  ext_push _ hm.sat hm.core.basicSelf (by intro c h; cases h) rfl rfl hm.core.procBasic

theorem reified_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) (ps : List RubyCore.Param) (ls : List String)
    (body : RubyCore.Expr) (lam : Bool) : StateOk κ Γ I (reifiedMachine m ps ls body lam) :=
  StateOk_ext hm (reified_ext hm ps ls body lam)
    (stringPayloadOk_push hm.stringPayload (by simp [Boot.procId, Boot.stringId]))
    (arrayPayloadOk_push hm.arrayPayload (by intro xs h; cases h))
    (hashPayloadOk_push hm.hashPayload (by intro xs h; cases h)) rfl

/-- Captures retain a reference to the current frame, not a copy of its local values. -/
theorem reified_locals (m : Machine) (ps : List RubyCore.Param) (ls : List String)
    (body : RubyCore.Expr) (lam : Bool) :
    closLocal (reifiedMachine m ps ls body lam) (reifiedClosure m ps ls body lam) =
      m.getLocal := by
  funext x
  suffices h : ∀ fuel fid,
      frameLocal.go (reifiedMachine m ps ls body lam) x fid fuel =
        Machine.getLocal.go m x fid fuel from h _ _
  intro fuel
  induction fuel with
  | zero => intro fid; rfl
  | succ fuel ih =>
    intro fid
    simp only [frameLocal.go, Machine.getLocal.go, reifiedMachine]
    cases hf : (m.frames.getD fid default).locals.find? (·.1 == x) with
    | some p => simp only [hf]
    | none =>
      simp only [hf]
      cases hc : (m.frames.getD fid default).captured with
      | none => rfl
      | some p => exact ih p

theorem reified_self {m : Machine} (hr : FrameInRange m) (ps : List RubyCore.Param)
    (ls : List String) (body : RubyCore.Expr) (lam : Bool) :
    closSelf (reifiedMachine m ps ls body lam) (reifiedClosure m ps ls body lam) =
      m.currentFrame.self := by
  exact congrArg RubyCore.Frame.self (currentFrame_headD hr.1).symm

/-- Allocation extends an already live capture chain by the current frame. StateOk's
current-frame bound alone does not assert that its captured parents are live. -/
theorem reified_captureLive {m : Machine} (hr : FrameInRange m)
    (hc : CaptureLive m m.currentFrame.captured) (ps : List RubyCore.Param)
    (ls : List String) (body : RubyCore.Expr) (lam : Bool) :
    CaptureLive (reifiedMachine m ps ls body lam)
      (reifiedClosure m ps ls body lam).captured := by
  apply CaptureLive.frames_preserved (m := m) (n := reifiedMachine m ps ls body lam)
    (Nat.le_refl _) (fun _ _ => rfl)
  apply CaptureLive.frame hr.2
  simpa only [currentFrame_headD hr.1] using hc

#print axioms reified_state
#print axioms reified_locals
#print axioms reified_captureLive
end Ratchet.Denote
