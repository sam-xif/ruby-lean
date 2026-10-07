import Books.Lib.Exec
import RubyCore.Boot

/-!
# Where a program starts

`rubycore` does not run a program on the bare boot heap. It first boots the
prelude — the part of Ruby's core library that the model writes in Ruby — and
runs the program on the heap that leaves. `start p` is that machine, and
`boot_ok` is the kernel's check that booting succeeds and produces it. Proofs in
this library are about `start p`, so they are about what `rubycore` executes.
-/
namespace Books
open RubyCore

set_option maxRecDepth 1000000

/-- The machine `rubycore` starts a program on: the prelude-booted heap, one
    toplevel frame, `self = main`. -/
def start (program : Expr) : Machine :=
  match Prelude.initWithPrelude program with
  | .ok m => m
  | .error _ => default

/-- Booting the prelude succeeds, whatever the program. The kernel runs the
    boot: about a thousand transitions that define the prelude's classes. -/
theorem boot_ok (program : Expr) : Prelude.initWithPrelude program = .ok (start program) := by
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
