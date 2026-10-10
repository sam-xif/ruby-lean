import RubyCore.Booted
import Books.Lib.Exec

/-!
# The booted heap is the literal

`RubyCore/Generated/BootedHeap.lean` holds the state the prelude boot leaves
behind — the heap, the globals, the shared numeric literals — written out as
terms by a program that ran the boot. `boot_eq_booted` is the proof that those
terms are what `Prelude.boot` computes: the kernel runs the boot, about a
thousand transitions, and compares the result with the literal field by field.

`initWithPrelude_eq_initOnBooted` is the form to use. It replaces "boot the
prelude, then start the program" by "start the program on the literal", for any
program. A proof about a program rewrites with it once and never runs the boot
again.

The literal is a build artifact that `make` rewrites when the model changes. If
it is ever stale — the prelude, a builtin table or the boot itself has changed
since it was written — this file stops compiling.
-/
namespace RubyCore.Proof

open RubyCore Books

set_option maxRecDepth 1000000

/-- The prelude boot succeeds, and leaves exactly the generated literal. -/
theorem boot_eq_booted :
    (Prelude.boot.map fun m => (m.heap, m.globals, m.numericLiterals))
      = .ok (Booted.heap, Booted.globals, Booted.numericLiterals) := by
  kernel_rfl

/-- Starting a program after booting the prelude is starting it on the literal. -/
theorem initWithPrelude_eq_initOnBooted (prog : Expr) :
    Prelude.initWithPrelude prog = Prelude.initOnBooted prog := by
  have h := boot_eq_booted
  unfold Prelude.initWithPrelude Prelude.initOnBooted
  generalize Prelude.boot = booted at h ⊢
  cases booted with
  | error e => exact absurd h (by simp [Except.map])
  | ok m =>
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hh, hg, hn⟩ := h
    simp only [bind, Except.bind, hh, hg, hn]

end RubyCore.Proof
