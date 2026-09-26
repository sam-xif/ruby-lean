import Denote.Sem.Closure.Transport
import Denote.Sem.Closure.Reify
import Denote.Sem.Core.Boot
import Denote.Ty.DenB

/-! Exact descriptor preservation rejects code replacement but permits captured writes.
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
  have hp := h.procs _ _ (reified_payload m [] [] (.int 1) true)
  rw [reified_payload] at hp
  have hb := congrArg Closure.body (Option.some.inj hp)
  cases hb

private def readX : ClosureCode := ⟨[], [], .var .lvar "x", true, rfl⟩
private def captured : Machine := reifiedMachine (bootMachine.setLocal "x" (.int 1))
  [] [] (.var .lvar "x") true
private def changed : Machine := captured.setLocal "x" .nil
private def capTy : Ty := .clos readX (.ivarCons "x" .int .ivar0) .never

theorem write_preserves_descriptor : ProcPres captured.heap changed.heap :=
  (Framed_setLocal captured "x" .nil).procs

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
end Ratchet.Denote.Typed.ProcPresControls
