import Books.Metatheory.Heap.HeapReads
import RubyCore.Interp

/-! Counterexamples to pre-L276 heap-growth lemmas. The repaired statements
must account for recursive names and the lookup fuel bound. -/
namespace RubyCore.Proof.DriftControls

def cyclicName : Heap :=
  { objs := #[{ klass := 0, payload := .cls { superclass := none, name := "A", attached := some 0 } }] }

example : className (cyclicName.alloc { klass := 0 }).2 0 ≠ className cyclicName 0 := by
  decide

def methodHeap : Heap :=
  { objs := #[{ klass := 0, payload := .cls { superclass := none, name := "A", methods := [("m", { params := [], owner := 0, body := .nil })] } }] }

-- Repeated ids can consume the old fuel even though allocation changes no
-- class payload. Real ancestor chains are duplicate-free and need a bound.
example : lookupInChain (methodHeap.alloc { klass := 0 }).2 [1, 1, 1, 1, 0] "m" ≠
    lookupInChain methodHeap [1, 1, 1, 1, 0] "m" := by
  intro he
  have := congrArg Option.isSome he
  contradiction

def aliasedLocals : Machine :=
  { (default : Machine) with
    stack := [0]
    frames := #[{ (default : Frame) with locals := [("x", .int 1)], localAlias := some 1 },
      { (default : Frame) with locals := [("x", .int 2)] }] }

/-- No captured parent does not imply that reads use the current frame. -/
example : aliasedLocals.currentFrame.captured = none ∧
    aliasedLocals.getLocal "x" = .int 2 ∧
    aliasedLocals.currentFrame.locals = [("x", .int 1)] := ⟨rfl, rfl, rfl⟩

def suspendedEnumerator : Machine :=
  { (default : Machine) with enumerators := [(0, { suspended := some default })] }

private def nextKontLength : StepResult → Nat
  | .next m => m.kont.length
  | _ => 0

/-- Resumption saves the caller's continuation, then switches to the fiber's
continuation. Appending a tail only to the active stack is not a frame action. -/
example :
    nextKontLength (Interp.enumNext
      { suspendedEnumerator with kont := [.seqK []] } 0 false false) = 0 ∧
    nextKontLength (match Interp.enumNext suspendedEnumerator 0 false false with
      | .next m => .next { m with kont := m.kont ++ [.seqK []] }
      | result => result) = 1 := by decide

end RubyCore.Proof.DriftControls
