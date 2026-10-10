import Books.Lib.Exec
import Books.Metatheory.Heap.BootedHeap

/-!
# Where a program starts

`rubycore` does not run a program on the bare boot heap. It first boots the
prelude — the part of Ruby's core library that the model writes in Ruby — and
runs the program on the heap that leaves. `start p` is that machine, and
`boot_ok` says so. Proofs in this library are about `start p`, so they are
about what `rubycore` executes.

`start p` is built from the booted heap as a literal (`Booted.heap`), not by
running the boot. That the literal is the boot's result is proved once, in
`Books/Metatheory/Heap/BootedHeap.lean`; a proof here never pays for the boot.
-/
namespace Books
open RubyCore

set_option maxRecDepth 1000000

/-- The machine `rubycore` starts a program on: the prelude-booted heap, one
    toplevel frame, `self = main`. -/
def start (program : Expr) : Machine :=
  match Prelude.initOnBooted program with
  | .ok m => m
  | .error _ => default

/-- `start program` is what booting the prelude and placing `program` on the
    resulting heap gives, whatever the program. -/
theorem boot_ok (program : Expr) : Prelude.initWithPrelude program = .ok (start program) := by
  rw [Proof.initWithPrelude_eq_initOnBooted]
  kernel_rfl

end Books

namespace Books
open RubyCore RubyCore.Interp

/-- `program`, run the way `rubycore` runs it, terminates normally with value
    `v`, leaving the machine in state `m'`. -/
def Runs (program : Expr) (v : Value) (m' : Machine) : Prop :=
  ∃ m₀, Prelude.initWithPrelude program = .ok m₀ ∧ Returns m₀ v m'

/-- `v` is an Array in heap `h` holding exactly `xs`. -/
def IsArray (h : Heap) (v : Value) (xs : List Value) : Prop :=
  ∃ o, v = .ref o ∧ (h.get o).payload = .arr xs.toArray

end Books
