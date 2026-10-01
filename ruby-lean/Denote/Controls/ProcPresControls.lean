import Denote.Sem.Closure.Transport
import Denote.Sem.Closure.Reify
import Denote.Sem.Closure.LocalFacts
import Denote.Sem.Core.Boot
import Denote.Ty.DenB

/-! Exact Proc preservation rejects code/dispatch replacement but permits captured writes.
The latter still invalidate incompatible captured-local type claims. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.ProcPresControls
open RubyCore Ratchet Ratchet.Denote

private def first : ClosureCode := ⟨[], [], .int 1, true, rfl⟩
private def second : ClosureCode := ⟨[], [], .int 2, true, rfl⟩

theorem changed_code_not_framed (m : Machine) :
    ¬ Framed (reifiedMachine m [] [] (.int 1) true)
      (reifiedMachine m [] [] (.int 2) true) := by
  intro h
  have hp := h.procs.payload _ _ (reified_payload m [] [] (.int 1) true)
  rw [reified_payload] at hp
  have hb := congrArg Closure.body (Option.some.inj hp)
  cases hb

private def readX : ClosureCode := ⟨[], [], .var .lvar "x", true, rfl⟩
private def captured : Machine := reifiedMachine (bootMachine.setLocal "x" (.int 1))
  [] [] (.var .lvar "x") true
private def changed : Machine := captured.setLocal "x" .nil
private def capTy : Ty := .clos readX (.ivarCons "x" .int .ivar0) .never

theorem write_preserves_descriptor : ProcPres captured.heap changed.heap :=
  by
  simpa only [changed, setLocal_heap] using (ProcPres.refl captured.heap)

theorem saved_receiver_survives_overwrite (m : Machine) (code : ClosureCode) :
    CurrentProc
      ((reifiedMachine m (toRubyParams code.params) code.locals (toRuby code.body) code.lam).setLocal
        "f" .nil) (.ref m.heap.objs.size) :=
by
  simpa only [CurrentProc, setLocal_heap, setLocal_stack] using currentProc_reified m code

private def dispatchHeap (e : Option ObjId) : Heap :=
  { objs := #[{ klass := Boot.procId, eigen := e, payload := .proc default }] }

theorem changed_dispatch_keeps_payload (o : ObjId) :
    ((dispatchHeap (some 0)).get o).payload = ((dispatchHeap none).get o).payload := by
  cases o with
  | zero => rfl
  | succ o => simp [dispatchHeap, Heap.get, Array.getD]

theorem changed_dispatch_rejected : ¬ ProcPres (dispatchHeap none) (dispatchHeap (some 0)) := by
  intro h
  have he : (0 : Nat) = Boot.procId := h.dispatch (.ref 0) default rfl
  exact (by decide : (0 : Nat) ≠ Boot.procId) he

#guard closB capTy captured (.ref bootMachine.heap.objs.size)
#guard !closB capTy changed (.ref bootMachine.heap.objs.size)
#guard closB (.clos readX .ivar0 .never) changed (.ref bootMachine.heap.objs.size)

-- Same object id and class do not justify a changed body at the old exact code type.
#guard closB (.clos first .ivar0 .never)
  (reifiedMachine bootMachine [] [] (.int 1) true) (.ref bootMachine.heap.objs.size)
#guard !closB (.clos first .ivar0 .never)
  (reifiedMachine bootMachine [] [] (.int 2) true) (.ref bootMachine.heap.objs.size)
#guard closB (.clos second .ivar0 .never)
  (reifiedMachine bootMachine [] [] (.int 2) true) (.ref bootMachine.heap.objs.size)

#print axioms changed_code_not_framed
#print axioms write_preserves_descriptor
#print axioms saved_receiver_survives_overwrite
#print axioms changed_dispatch_rejected
end Ratchet.Denote.Typed.ProcPresControls
