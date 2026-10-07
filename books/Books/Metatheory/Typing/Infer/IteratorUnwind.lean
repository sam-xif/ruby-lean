import RubyCore.Interp

/-! Hash iterator unwind releases shared state and is not machine-transparent. -/
namespace RubyCore.Proof.Static

def IterUnwindInert : IterKind → Prop
  | .hashEach .. => False
  | _ => True

@[simp] theorem leaveHashIteration_inert {m : Machine} {kind : IterKind}
    (h : IterUnwindInert kind) : m.leaveHashIteration kind = m := by
  cases kind <;> simp_all [IterUnwindInert, Machine.leaveHashIteration]

private def lockedIterator : Machine :=
  { (Machine.init .nil) with
    hashIterationLocks := [0]
    kont := [.iterK default 0 [] (.hashEach 0 [] 0 0) [] .nil .nil] }

-- The old RetTransparent/NxtTransparent admitted this marker unconditionally.
theorem hash_unwind_not_transparent :
    Interp.unwind lockedIterator (.raiseJ .nil) ≠
      .next (Interp.withCtl { lockedIterator with kont := [] } (.jump (.raiseJ .nil))) := by
  intro h
  have locks := congrArg (fun s => match s with
    | .next m => m.hashIterationLocks
    | _ => []) h
  change ([] : List ObjId) = [0] at locks
  cases locks

#print axioms hash_unwind_not_transparent
end RubyCore.Proof.Static
