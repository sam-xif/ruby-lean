import Books.TypeSoundness.Rules.Closure.Current
import Books.TypeSoundness.Conformance.Closure.Value
import Books.TypeSoundness.Conformance.Closure.Transport
import Books.TypeSoundness.Denotation.DenB

/-! A stored literal's complete captured environment includes its own binding. These
entry controls retain that exact closure type, without claiming the body or call is safe. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.ClosureStoredControls
open RubyCore Checker Checker.Soundness

def stored (m : Machine) (code : ClosureCode) (name : String) : Machine :=
  (reifiedMachine m (toRubyParams code.params) code.locals (toRuby code.body) code.lam).setLocal
    name (.ref m.heap.objs.size)

def payload (m : Machine) (code : ClosureCode) : Closure :=
  reifiedClosure m (toRubyParams code.params) code.locals (toRuby code.body) code.lam

theorem stored_state {m : Machine} (hm : StateOk ctx0 [] .ivar0 m)
    (code : ClosureCode) (name : String) :
    StateOk ctx0 [(name, .clos code .ivar0 .never)] .ivar0 (stored m code name) := by
  exact StateOk_setLocal (x := name) (ρ := .clos code .ivar0 .never)
    (reified_state hm _ _ _ _) (reified_den hm code) rfl rfl rfl
    (by intro y σ h; cases h)

theorem stored_payload {m : Machine} (hm : StateOk ctx0 [] .ivar0 m)
    (code : ClosureCode) (name : String) :
    procClosure? (stored m code name).heap ((stored m code name).getLocal name) =
      some (payload m code) := by
  rw [stored, getLocal_setLocal_self
    (reifiedMachine m (toRubyParams code.params) code.locals (toRuby code.body) code.lam)
    _ _ hm.frameInRange.2, setLocal_heap]
  exact reified_payload m _ _ _ _

/-- Any supported zero-argument lambda body enters with the stored binding present.
No body result is assumed or proved by this activation theorem. -/
theorem stored_entry {m : Machine} (hm : StateOk ctx0 [] .ivar0 m)
    (code : ClosureCode) (name : String) (hp : code.params = [])
    (hls : code.locals = []) (hl : code.lam = true) :
    ∃ n, Interp.callClosure (stored m code name) (payload m code) [] none = .next n ∧
      StateOk (ctx0.withoutRuntimeScope.withFrame none)
        [(name, .clos code .ivar0 .never)] .ivar0 n := by
  have hs := stored_state hm code name
  have he := callClosure_current_state (cl := payload m code) (ps := []) (args := [])
    hs (ReframeFO.empty rfl rfl rfl rfl) rfl (hs.runtime rfl).captured rfl trivial
    (by simp [payload, reifiedClosure, hls, blockLocals, isAliasTy])
    (by
      intro p hmem v hv
      simp only [List.nil_append, payload, reifiedClosure, hls, blockLocals,
        List.mem_singleton] at hmem
      subst p
      exact ProcPres.empty_capture_den (m := stored m code name)
        (n := pushMethodFrame (stored m code name)
          (requiredClosureFrame (stored m code name) (payload m code) [] [])) (.refl _) hv)
    (fun _ => rfl) (by simp [payload, reifiedClosure, hp, toRubyParams])
    (by simpa [payload, reifiedClosure] using hl) rfl none
  simpa [payload, reifiedClosure, hls, blockLocals] using he

theorem boot_stored_entry (hb : bootOkB = true) (value : Int) :
    let code : ClosureCode := ⟨[], [], .int value, true, by simp [paramEqAll, exprEq]⟩
    ∃ n, Interp.callClosure (stored bootMachine code "f") (payload bootMachine code) [] none =
      .next n ∧ StateOk (ctx0.withoutRuntimeScope.withFrame none)
        [("f", .clos code .ivar0 .never)] .ivar0 n :=
  stored_entry (stateOk_boot hb) _ "f" rfl rfl rfl

private def one : ClosureCode := ⟨[], [], .int 1, true, rfl⟩
private def nilCapture : Ty := .clos one (.ivarCons "x" .nilT .ivar0) .never
private def dangling : Machine :=
  let n := reifiedMachine { bootMachine with stack := [bootMachine.frames.size] }
    [] [] (.int 1) true
  { n with stack := bootMachine.stack }
private def filled : Machine :=
  pushMethodFrame dangling { (default : RubyCore.Frame) with locals := [("x", .int 7)] }

-- Equal heaps and exact Proc code do not suffice for arbitrary capture-type transport:
-- a previously dangling capture can start reading the frame that was just allocated.
#guard closB nilCapture dangling (.ref bootMachine.heap.objs.size)
#guard !closB nilCapture filled (.ref bootMachine.heap.objs.size)

#print axioms stored_state
#print axioms stored_payload
#print axioms stored_entry
#print axioms boot_stored_entry
end Checker.Soundness.Typed.ClosureStoredControls
